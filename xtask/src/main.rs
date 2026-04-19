use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::Write,
    net::TcpListener,
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    str::FromStr,
    thread,
    time::{Duration, Instant},
};

mod phase2;
mod phase2_real;

use anyhow::{anyhow, bail, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use chrono::Utc;
use csv::Writer;
use phase1_probe::{
    build_parse_instruction, build_synthetic_instruction, build_upload_instruction, id,
    FieldKernel, MerkleBatchMode, ProbeInstruction, ProofParseFormat, SyntheticVerifierProfile,
};
use reqwest::blocking::Client as HttpClient;
use serde::Serialize;
use serde_json::{json, Value};
use solana_program::instruction::Instruction;
use solana_sdk::{
    compute_budget::ComputeBudgetInstruction,
    hash::hashv,
    instruction::AccountMeta,
    native_token::LAMPORTS_PER_SOL,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    system_instruction,
    transaction::Transaction,
};
use svm_cost_model::{
    assess_query_soundness, bootstrap_coefficients, fit_additive_model,
    fit_additive_model_for_features, load_summary, render_markdown_report,
    score_profile_with_components, BenchmarkKind, CoefficientEstimate, CostFeatures,
    FailureObservation, FeatureOrigin, FittedCostModel, HistoricalBaseline, MeasurementRecord,
    MeasurementStatus, ModelComparison, Phase1Summary, ProfileParameterChoice, ProfileScoreInput,
    ProfileScoreOutput, ProfileSweepRecord, QuerySoundnessAssessment, QuerySoundnessModel,
    RepoBaselineSummary, SvmLimits, TransportCostFeatures,
};
use winterfell::{
    crypto::{hashers::Sha2_256, MerkleTree},
    math::{fields::f128::BaseElement, FieldElement, ToElements},
    Air, AirContext, Assertion, EvaluationFrame, FieldExtension, Proof, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

const VERIFICATION_CORE_CANDIDATES: &[&str] = &[
    "sha_calls",
    "sha_bytes",
    "merkle_levels",
    "proof_bytes",
    "heap_pages_32k",
    "ro_account_count",
    "rw_account_count",
    "account_data_bytes_read",
    "account_data_bytes_written",
    "field_add_sub_ops",
    "field_mul_ops",
    "field_inv_ops",
    "extension_mul_ops",
];

const TRANSPORT_CANDIDATES: &[&str] = &["sha_calls", "sha_bytes"];

struct BenchHarness {
    client: LocalRpcClient,
    payer: Keypair,
    program_id: Pubkey,
    limits: SvmLimits,
}

struct ValidatorGuard {
    child: Child,
    rpc_url: String,
    _log_path: PathBuf,
}

impl Drop for ValidatorGuard {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[derive(Clone)]
struct TxPlan {
    instructions: Vec<Instruction>,
    compute_unit_limit: Option<u32>,
    heap_frame_bytes: Option<u32>,
}

#[derive(Clone)]
struct SimulatedTx {
    units_consumed: Option<u64>,
    transaction_bytes: u64,
    error: Option<String>,
    logs: Vec<String>,
}

struct LocalRpcClient {
    url: String,
    http: HttpClient,
}

struct RpcSimulation {
    units_consumed: Option<u64>,
    error: Option<String>,
    logs: Vec<String>,
}

type PqzkHasher = Sha2_256<BaseElement>;
type PqzkMerkle = MerkleTree<PqzkHasher>;

#[derive(Serialize)]
struct CsvRecord<'a> {
    measurement_id: &'a str,
    benchmark: String,
    label: &'a str,
    repetition: u32,
    timestamp_utc: &'a str,
    status: String,
    actual_cu: Option<u64>,
    transaction_bytes: Option<u64>,
    error: Option<&'a str>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_paths: u64,
    merkle_levels: u64,
    proof_bytes: u64,
    proof_segments: u64,
    upload_bytes: u64,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    ro_account_count: u64,
    rw_account_count: u64,
    account_data_bytes_read: u64,
    account_data_bytes_written: u64,
    field_add_sub_ops: u64,
    field_mul_ops: u64,
    field_inv_ops: u64,
    extension_mul_ops: u64,
}

#[derive(Clone, Copy)]
struct PqzkPublicInputs {
    seed: BaseElement,
    inc: BaseElement,
}

impl ToElements<BaseElement> for PqzkPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.seed, self.inc]
    }
}

struct PqzkMessageAir {
    context: AirContext<BaseElement>,
    public_inputs: PqzkPublicInputs,
}

impl PqzkMessageAir {
    fn new_internal(info: TraceInfo, public_inputs: PqzkPublicInputs, opts: ProofOptions) -> Self {
        let degrees = vec![TransitionConstraintDegree::new(1)];
        Self {
            context: AirContext::new(info, degrees, 2, opts),
            public_inputs,
        }
    }
}

impl Air for PqzkMessageAir {
    type BaseField = BaseElement;
    type PublicInputs = PqzkPublicInputs;

    fn new(info: TraceInfo, public_inputs: Self::PublicInputs, opts: ProofOptions) -> Self {
        Self::new_internal(info, public_inputs, opts)
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic: &[E],
        result: &mut [E],
    ) {
        let inc = E::from(self.public_inputs.inc);
        result[0] = frame.next()[0] - frame.current()[0] - inc;
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let last = self.trace_length() - 1;
        vec![
            Assertion::single(0, 0, self.public_inputs.seed),
            Assertion::single(
                0,
                last,
                self.public_inputs.seed + (self.public_inputs.inc * BaseElement::from(last as u64)),
            ),
        ]
    }
}

#[derive(Clone, Debug, Serialize)]
struct VersionCommandResult {
    command: String,
    output: String,
}

#[derive(Clone, Debug, Serialize)]
struct VersionManifest {
    generated_at_utc: String,
    executed: Vec<VersionCommandResult>,
    not_executed: Vec<String>,
}

#[derive(Serialize)]
struct ExternalCuSummary {
    run_count: usize,
    mean_cu: f64,
    median_cu: f64,
    min_cu: u64,
    max_cu: u64,
}

#[derive(Serialize)]
struct PqzkProofStructure {
    proof_path: String,
    proof_sha256: String,
    proof_bytes: u64,
    trace_width: u64,
    trace_length: u64,
    num_trace_segments: u64,
    num_unique_queries: u64,
    configured_queries: u64,
    blowup_factor: u64,
    grinding_factor: u64,
    field_extension: String,
    folding_factor: u64,
    fri_layers: u64,
    fri_remainder_elements: u64,
    lde_domain_size: u64,
    trace_query_depths: Vec<u64>,
    constraint_query_depth: u64,
    fri_layer_depths: Vec<u64>,
    merkle_query_families: u64,
    total_merkle_levels_unbatched: u64,
    total_batched_merkle_nodes: u64,
    cipher_bytes: u64,
    kem_ciphertext_bytes: u64,
    body_bytes: u64,
    chat_msg_account_bytes: u64,
    heap_frame_bytes_requested: u64,
    notes: Vec<String>,
}

#[derive(Serialize)]
struct RealVerifierFieldInvDiagnostic {
    prior_query_scaled_proxy: u64,
    ood_transition_divisions: u64,
    boundary_constraint_group_divisions: u64,
    deep_composer_batch_inversions: u64,
    fri_layer_batch_inversions: u64,
    estimated_total: u64,
    notes: Vec<String>,
}

#[derive(Clone, Serialize)]
struct RealVerifierFieldMulDiagnostic {
    prior_proxy: u64,
    remainder_horner_mul_ops: u64,
    query_coordinate_lift_mul_ops: u64,
    estimated_total: u64,
    notes: Vec<String>,
}

#[derive(Clone, Serialize)]
struct RealVerifierExtensionMulDiagnostic {
    estimated_total: u64,
    notes: Vec<String>,
}

#[derive(Serialize)]
struct RealVerifierComparison {
    generated_at_utc: String,
    source_repo: String,
    source_paper: String,
    verify_stark_baseline: ExternalCuSummary,
    finalize_sig_baseline: ExternalCuSummary,
    structure: PqzkProofStructure,
    scored_profile_path: String,
    scored_profile: ProfileScoreInput,
    score: ProfileScoreOutput,
    measured_minus_predicted_cu: f64,
    absolute_error_cu: f64,
    relative_error_fraction: f64,
    field_inv_diagnostic: RealVerifierFieldInvDiagnostic,
    field_mul_diagnostic: RealVerifierFieldMulDiagnostic,
    extension_mul_diagnostic: RealVerifierExtensionMulDiagnostic,
    field_mul_ops_backsolved_for_mean: Option<f64>,
    notes: Vec<String>,
}

#[derive(Serialize)]
struct OrthogonalSweepSummary {
    generated_at_utc: String,
    record_count: usize,
    upload_model: Option<ModelComparison>,
    account_io_model: Option<ModelComparison>,
    field_inv_model: Option<ModelComparison>,
    field_inv_failed_runs: usize,
    notes: Vec<String>,
}

#[derive(Clone, Copy)]
enum SpendProtocol {
    Circle,
    Whir,
}

#[derive(Clone, Serialize)]
struct SpendStatementShape {
    spends: u64,
    outputs: u64,
    note_tree_depth: u64,
    note_openings_per_spend: u64,
    nullifier_hashes_per_spend: u64,
    note_commitments_per_output: u64,
    amount_range_checks_64: u64,
    ownership_checks: u64,
    balance_constraints: u64,
    lookup_arguments: u64,
}

#[derive(Clone, Serialize)]
struct SpendArithmetizationAssumptions {
    merkle_rows_per_level: u64,
    nullifier_hash_rows: u64,
    note_commitment_rows: u64,
    range_check_rows: u64,
    ownership_rows: u64,
    balance_rows: u64,
    lookup_rows: u64,
    misc_rows: u64,
    transition_constraint_divisions: u64,
    boundary_constraint_groups: u64,
}

#[derive(Clone, Serialize)]
struct SpendVerifierAssumptions {
    protocol_family: String,
    query_count: u64,
    proof_query_semantics: String,
    security_interpretation: String,
    proof_merkle_depth: u64,
    base_proof_bytes: u64,
    proof_bytes_per_log2_rows: u64,
    proof_bytes_per_query: u64,
    proof_bytes_per_lookup_argument: u64,
    proof_bytes_per_hash_gadget: u64,
    proof_segment_bytes: u64,
    sha_calls_base: u64,
    sha_bytes_base: u64,
    ro_account_count: u64,
    rw_account_count: u64,
    account_read_base_bytes: u64,
    account_read_per_merkle_path_bytes: u64,
    account_read_per_output_bytes: u64,
    account_write_bytes: u64,
    field_add_base: u64,
    field_add_per_hash_gadget: u64,
    field_add_per_lookup_argument: u64,
    field_add_per_log2_rows: u64,
    field_mul_base: u64,
    field_mul_per_query: u64,
    field_mul_per_hash_gadget: u64,
    field_mul_per_lookup_argument: u64,
    field_mul_per_log2_rows: u64,
    field_inv_base: u64,
    field_inv_per_lookup_argument: u64,
    field_inv_per_query: u64,
    deep_batch_inversions: u64,
    low_degree_batch_inversions: u64,
    extension_mul_base: u64,
    extension_mul_per_query: u64,
    extension_mul_per_lookup_argument: u64,
    extension_mul_per_log2_rows: u64,
    heap_small_bytes: u64,
    heap_large_bytes: u64,
    heap_large_log2_rows_threshold: u32,
}

#[derive(Clone, Serialize)]
struct SpendFieldInvStructuralBreakdown {
    prior_query_scaled_proxy: u64,
    transition_constraint_divisions: u64,
    boundary_constraint_group_divisions: u64,
    deep_batch_inversions: u64,
    low_degree_batch_inversions: u64,
    estimated_total: u64,
    notes: Vec<String>,
}

#[derive(Clone, Serialize)]
struct SpendBoundaryLayout {
    main_trace_initial_groups: u64,
    main_trace_terminal_groups: u64,
    lookup_accumulator_initial_groups: u64,
    lookup_accumulator_terminal_groups: u64,
    total_groups: u64,
    notes: Vec<String>,
}

#[derive(Clone, Serialize)]
struct SpendVerifierInversionLayout {
    deep_batch_inversions: u64,
    low_degree_batch_components: BTreeMap<String, u64>,
    low_degree_batch_inversions: u64,
    notes: Vec<String>,
}

#[derive(Clone, Serialize)]
struct StructuredSpendProjection {
    profile_name: String,
    protocol_family: String,
    statement: SpendStatementShape,
    arithmetization: SpendArithmetizationAssumptions,
    verifier: SpendVerifierAssumptions,
    boundary_layout: SpendBoundaryLayout,
    verifier_inversion_layout: SpendVerifierInversionLayout,
    field_inv_breakdown: SpendFieldInvStructuralBreakdown,
    row_breakdown: BTreeMap<String, u64>,
    total_rows: u64,
    evaluation_domain_log2: u32,
    application_merkle_paths: u64,
    application_merkle_levels: u64,
    application_hash_gadgets: u64,
    derived_profile: ProfileScoreInput,
    notes: Vec<String>,
}

struct StructuredSpendProfile {
    profile: ProfileScoreInput,
    projection: StructuredSpendProjection,
}

#[derive(Serialize)]
struct QueryCountSweepSummary {
    query_count: u64,
    min_predicted_cu: f64,
    max_predicted_cu: f64,
    feasible_count: usize,
}

#[derive(Serialize)]
struct RefinedSpendSummary {
    generated_at_utc: String,
    constrained_model_path: String,
    constrained_core_model_path: String,
    structured_projection_path: String,
    baseline_scores: Vec<ProfileScoreOutput>,
    refined_scores: Vec<ProfileScoreOutput>,
    best_by_protocol: Vec<ProfileSweepRecord>,
    protocol_feasible_counts: BTreeMap<String, usize>,
    query_count_summary: Vec<QueryCountSweepSummary>,
    security_qualified_sweep_path: String,
    security_qualified_summary_path: String,
    security_qualified_best_by_protocol_assumption: Vec<SecurityQualifiedSweepRecord>,
    security_qualified_feasible_counts: BTreeMap<String, usize>,
    sweep_artifacts: Vec<String>,
    notes: Vec<String>,
}

#[derive(Clone, Copy)]
enum SecurityQualifiedAssumption {
    Conservative,
    Optimistic,
}

#[derive(Clone, Serialize)]
struct SecurityQualifiedSweepRecord {
    scenario_name: String,
    protocol_family: String,
    soundness_assumption: String,
    security_target_bits: f64,
    cost_scenario_name: String,
    rate_parameter_name: String,
    log_rate: u32,
    reciprocal_rate: u64,
    grinding_bits: u32,
    minimum_secure_query_count: u64,
    total_explicit_query_count: u64,
    chunk_size: u64,
    proof_bytes: u64,
    predicted_cu: f64,
    lower_cu: Option<f64>,
    upper_cu: Option<f64>,
    verification_core_cu: Option<f64>,
    transport_overhead_cu: Option<f64>,
    cu_budget_fraction: f64,
    proof_transport_pressure: f64,
    assumption_qualified_feasible: bool,
    assumption_feasibility_reasons: Vec<String>,
    lower_bound_model_feasible: bool,
    lower_bound_model_feasibility_reasons: Vec<String>,
    query_soundness: QuerySoundnessAssessment,
    notes: Vec<String>,
}

#[derive(Serialize)]
struct SecurityQualifiedSweepSummary {
    generated_at_utc: String,
    sweep_path: String,
    best_by_protocol_assumption_target: Vec<SecurityQualifiedSweepRecord>,
    feasible_counts: BTreeMap<String, usize>,
    notes: Vec<String>,
}

#[derive(Clone)]
struct CostScenario {
    name: &'static str,
    whir_core_multiplier: f64,
    field_mul_multiplier: f64,
    extension_mul_multiplier: f64,
    notes: Vec<String>,
}

#[derive(Clone, Copy)]
enum WhirSecurityAssumption {
    Johnson,
    Capacity,
}

#[derive(Clone, Serialize)]
struct FullWhirRoundDerivation {
    round_index: usize,
    current_log_inv_rate: u32,
    next_log_inv_rate: u32,
    num_variables: u32,
    num_queries: u64,
    ood_samples: u64,
    query_security_bits: f64,
    combination_security_bits: f64,
    query_pow_bits_required: u32,
    folding_security_bits: f64,
    folding_pow_bits_required: u32,
}

#[derive(Clone, Serialize)]
struct FullWhirSecurityDerivation {
    soundness_assumption: String,
    target_bits: f64,
    field_size_bits: u32,
    max_pow_bits: u32,
    starting_log_inv_rate: u32,
    num_variables: u32,
    first_round_folding_factor: u32,
    later_round_folding_factor: u32,
    rs_domain_initial_reduction_factor: u32,
    commitment_ood_samples: u64,
    commitment_ood_security_bits: f64,
    starting_folding_security_bits: f64,
    starting_folding_pow_bits_required: u32,
    rounds: Vec<FullWhirRoundDerivation>,
    final_log_inv_rate: u32,
    final_queries: u64,
    final_query_security_bits: f64,
    final_query_pow_bits_required: u32,
    final_folding_security_bits: f64,
    final_folding_pow_bits_required: u32,
    total_explicit_query_count: u64,
    total_ood_samples: u64,
    max_required_pow_bits: u32,
    pow_cap_satisfied: bool,
    overall_security_bits: f64,
}

#[derive(Serialize)]
struct Phase1NextSummary {
    generated_at_utc: String,
    command: String,
    raw_artifacts: Vec<String>,
    real_verifier_comparison_path: String,
    spend_profile_scores_path: String,
    refined_spend_summary_path: String,
    refined_spend_sweep_path: String,
    constrained_spend_model_path: String,
    orthogonal_measurements_path: String,
    orthogonal_summary_path: String,
    version_manifest_path: String,
    notes: Vec<String>,
}

impl LocalRpcClient {
    fn new(url: String) -> Self {
        Self {
            url,
            http: HttpClient::builder()
                .timeout(Duration::from_secs(30))
                .build()
                .expect("http client"),
        }
    }

    fn rpc(&self, method: &str, params: Value) -> Result<Value> {
        let response = self
            .http
            .post(&self.url)
            .json(&json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": method,
                "params": params,
            }))
            .send()
            .with_context(|| format!("rpc {method} request failed"))?;
        let value: Value = response
            .json()
            .with_context(|| format!("rpc {method} response decode failed"))?;
        if let Some(error) = value.get("error") {
            bail!("rpc {method} error: {error}");
        }
        value
            .get("result")
            .cloned()
            .ok_or_else(|| anyhow!("rpc {method} missing result"))
    }

    fn get_latest_blockhash(&self) -> Result<solana_sdk::hash::Hash> {
        let result = self.rpc("getLatestBlockhash", json!([{ "commitment": "processed" }]))?;
        let blockhash = result
            .get("value")
            .and_then(|value| value.get("blockhash"))
            .and_then(Value::as_str)
            .ok_or_else(|| anyhow!("missing blockhash in RPC response"))?;
        Ok(solana_sdk::hash::Hash::from_str(blockhash)?)
    }

    fn request_airdrop(&self, pubkey: &Pubkey, lamports: u64) -> Result<String> {
        let result = self.rpc(
            "requestAirdrop",
            json!([pubkey.to_string(), lamports, { "commitment": "processed" }]),
        )?;
        result
            .as_str()
            .map(str::to_owned)
            .ok_or_else(|| anyhow!("requestAirdrop missing signature"))
    }

    fn get_balance(&self, pubkey: &Pubkey) -> Result<u64> {
        let result = self.rpc(
            "getBalance",
            json!([pubkey.to_string(), { "commitment": "processed" }]),
        )?;
        result
            .get("value")
            .and_then(Value::as_u64)
            .ok_or_else(|| anyhow!("getBalance missing value"))
    }

    fn get_minimum_balance_for_rent_exemption(&self, size: usize) -> Result<u64> {
        let result = self.rpc("getMinimumBalanceForRentExemption", json!([size]))?;
        result
            .as_u64()
            .ok_or_else(|| anyhow!("getMinimumBalanceForRentExemption missing value"))
    }

    fn get_account_data_len(&self, pubkey: &Pubkey) -> Result<Option<usize>> {
        let result = self.rpc(
            "getAccountInfo",
            json!([pubkey.to_string(), { "encoding": "base64", "commitment": "processed" }]),
        )?;
        let value = result.get("value").cloned().unwrap_or(Value::Null);
        if value.is_null() {
            return Ok(None);
        }
        Ok(value
            .get("space")
            .and_then(Value::as_u64)
            .map(|space| space as usize))
    }

    fn simulate_transaction(&self, tx: &Transaction) -> Result<RpcSimulation> {
        let encoded = BASE64_STANDARD.encode(bincode::serialize(tx)?);
        let result = self.rpc(
            "simulateTransaction",
            json!([
                encoded,
                {
                    "encoding": "base64",
                    "sigVerify": false,
                    "replaceRecentBlockhash": true,
                    "commitment": "processed"
                }
            ]),
        )?;
        let logs = result
            .get("value")
            .and_then(|value| value.get("logs"))
            .and_then(Value::as_array)
            .map(|logs| {
                logs.iter()
                    .filter_map(|line| line.as_str().map(str::to_owned))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let error = result
            .get("value")
            .and_then(|value| value.get("err"))
            .filter(|value| !value.is_null())
            .map(ToString::to_string);
        let units_consumed = result
            .get("value")
            .and_then(|value| value.get("unitsConsumed"))
            .and_then(Value::as_u64);
        Ok(RpcSimulation {
            units_consumed,
            error,
            logs,
        })
    }

    fn send_and_confirm_transaction(&self, tx: &Transaction) -> Result<()> {
        let encoded = BASE64_STANDARD.encode(bincode::serialize(tx)?);
        let signature = self.rpc(
            "sendTransaction",
            json!([
                encoded,
                {
                    "encoding": "base64",
                    "preflightCommitment": "processed"
                }
            ]),
        )?;
        let signature = signature
            .as_str()
            .ok_or_else(|| anyhow!("sendTransaction missing signature"))?;
        let started = Instant::now();
        loop {
            let statuses = self.rpc(
                "getSignatureStatuses",
                json!([[signature], { "searchTransactionHistory": false }]),
            )?;
            let value = statuses
                .get("value")
                .and_then(Value::as_array)
                .and_then(|items| items.first())
                .cloned()
                .unwrap_or(Value::Null);
            if !value.is_null() {
                if let Some(err) = value.get("err").filter(|err| !err.is_null()) {
                    bail!("transaction {signature} failed: {err}");
                }
                if value
                    .get("confirmationStatus")
                    .and_then(Value::as_str)
                    .map(|status| matches!(status, "processed" | "confirmed" | "finalized"))
                    .unwrap_or(false)
                {
                    break;
                }
            }
            if started.elapsed() > Duration::from_secs(10) {
                bail!("timed out waiting for transaction {signature} to confirm");
            }
            thread::sleep(Duration::from_millis(100));
        }
        Ok(())
    }
}

fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("phase1") => run_phase1(),
        Some("phase1-next") => run_phase1_next(),
        Some("phase2-experiments") => phase2::run_phase2_experiments(),
        Some("phase2-real-experiments") => phase2_real::run_phase2_real_experiments(),
        Some(other) => bail!("unknown xtask subcommand: {other}"),
        None => bail!("usage: cargo xtask phase1 | cargo xtask phase1-next | cargo xtask phase2-experiments | cargo xtask phase2-real-experiments"),
    }
}

fn run_phase1() -> Result<()> {
    let root = workspace_root()?;
    let results_dir = root.join("phase1_results");
    let docs_dir = root.join("docs");
    let examples_dir = root.join("examples/phase1");
    fs::create_dir_all(&results_dir)?;
    fs::create_dir_all(&docs_dir)?;
    fs::create_dir_all(&examples_dir)?;

    let limits = SvmLimits::default();
    let program_so = build_sbf_program(&root)?;
    let validator = start_validator(&root, &results_dir, &program_so)?;
    let harness = BenchHarness {
        client: LocalRpcClient::new(validator.rpc_url.clone()),
        payer: Keypair::new(),
        program_id: id(),
        limits: limits.clone(),
    };

    fund_payer(&harness)?;
    eprintln!("phase1: funded payer");

    let mut records = Vec::new();
    let mut failures = Vec::new();

    records.extend(run_noop_benchmarks(&harness)?);
    eprintln!("phase1: noop");
    records.extend(run_hash_benchmarks(&harness)?);
    eprintln!("phase1: hash");
    records.extend(run_merkle_benchmarks(&harness)?);
    eprintln!("phase1: merkle");
    records.extend(run_field_benchmarks(&harness)?);
    eprintln!("phase1: field");
    records.extend(run_heap_benchmarks(&harness, &mut failures)?);
    eprintln!("phase1: heap");
    records.extend(run_account_io_benchmarks(&harness)?);
    eprintln!("phase1: account-io");
    records.extend(run_upload_path_benchmarks(&harness, &mut failures)?);
    eprintln!("phase1: upload");
    records.extend(run_proof_parsing_benchmarks(&harness)?);
    eprintln!("phase1: parse");
    records.extend(run_synthetic_verifier_benchmarks(&harness, &mut failures)?);
    eprintln!("phase1: synthetic");
    failures.extend(run_failure_boundaries(&harness)?);
    eprintln!("phase1: failures");

    let comparison = fit_additive_model(&records)?;
    eprintln!("phase1: model");
    let verification_core_records = records
        .iter()
        .filter(|record| record.benchmark != BenchmarkKind::UploadPath)
        .cloned()
        .collect::<Vec<_>>();
    let verification_core_model =
        fit_additive_model_for_features(&verification_core_records, VERIFICATION_CORE_CANDIDATES)?;
    eprintln!("phase1: core-model");
    let transport_records = records
        .iter()
        .filter(|record| {
            matches!(
                record.benchmark,
                BenchmarkKind::Noop | BenchmarkKind::HashSyscall | BenchmarkKind::UploadPath
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let transport_model =
        fit_additive_model_for_features(&transport_records, TRANSPORT_CANDIDATES)?;
    eprintln!("phase1: transport-model");
    let bootstrap = bootstrap_coefficients(
        &records,
        &comparison
            .chosen
            .selected_features
            .iter()
            .map(|value| value.as_str())
            .collect::<Vec<_>>(),
        256,
        0x5EED_1234,
    )?;
    eprintln!("phase1: bootstrap");

    let sample_profiles = write_sample_profiles(&examples_dir)?;
    let sample_scores = sample_profiles
        .iter()
        .map(|path| {
            let input = svm_cost_model::load_profile_input(path)?;
            score_profile_with_components(
                &comparison.chosen,
                Some(&verification_core_model.chosen),
                Some(&transport_model.chosen),
                &limits,
                &input,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    write_json(&results_dir.join("profile_scores.json"), &sample_scores)?;
    eprintln!("phase1: sample-scores");
    let circle_sweep = write_circle_sweep(
        &results_dir,
        &comparison.chosen,
        &verification_core_model.chosen,
        &transport_model.chosen,
        &limits,
    )?;
    eprintln!("phase1: circle-sweep");
    write_json(&results_dir.join("coefficient_bootstrap.json"), &bootstrap)?;
    eprintln!("phase1: bootstrap-artifacts");

    let summary = Phase1Summary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask phase1".to_string(),
        repo_baseline: RepoBaselineSummary {
            discovery_summary: "Workspace was empty at `/Users/dominic/ZK`. Phase 1 is a from-scratch scaffold: no pre-existing on-chain program, verifier entrypoint, benchmark harness, upload path, allocator tuning, or vendored proof-system dependency was present to reuse.".to_string(),
            existing_onchain_programs: Vec::new(),
            existing_verifier_entrypoints: Vec::new(),
            existing_benchmark_scripts: Vec::new(),
            existing_upload_path: None,
            existing_heap_handling: None,
            existing_patched_dependencies: Vec::new(),
        },
        historical_baseline: HistoricalBaseline {
            name: "verify_stark".to_string(),
            mean_cu: 1_104_510,
            max_cu: 1_190_982,
            run_count: 100,
            notes: vec![
                "Preserved from prompt context; not reproduced in this empty workspace.".to_string(),
                "Likely included chunked uploads, SHA-256 via Solana hash syscall path, explicit heap tuning, and end-to-end benchmark scripts.".to_string(),
            ],
        },
        measurement_count: records.len(),
        raw_artifacts: vec![
            "phase1_results/measurements.jsonl".to_string(),
            "phase1_results/measurements.csv".to_string(),
            "phase1_results/profile_scores.json".to_string(),
            "phase1_results/circle_sweep.json".to_string(),
            "phase1_results/circle_sweep.csv".to_string(),
            "phase1_results/coefficient_bootstrap.json".to_string(),
            "phase1_results/summary.json".to_string(),
            "docs/phase1-cost-model.md".to_string(),
        ],
        measured_variables: vec![
            "transaction CU from local simulation".to_string(),
            "transaction byte size".to_string(),
            "hash call count per benchmark definition".to_string(),
            "hashed bytes per benchmark definition".to_string(),
            "proof bytes uploaded and parsed".to_string(),
            "upload chunk count".to_string(),
            "heap frame request bytes".to_string(),
            "readonly and writable account counts".to_string(),
            "account data bytes read/written by benchmark construction".to_string(),
        ],
        inferred_variables: vec![
            "total merkle levels = path_count * path_depth".to_string(),
            "heap_pages_32k from requested heap frame".to_string(),
            "proof transport pressure from upload bytes vs 1232-byte transaction cap".to_string(),
            "dominant contributor ordering from additive fitted coefficients".to_string(),
            "verification-core vs transport decomposition from secondary additive fits".to_string(),
            "coefficient uncertainty bands from deterministic bootstrap resampling".to_string(),
        ],
        unknowns: vec![
            "real verifier semantic op mix, because no verifier implementation was present".to_string(),
            "stack pressure under production verifier recursion or inlined frames".to_string(),
            "validator-version drift beyond local Agave 2.3.0".to_string(),
            "cache warmth effects across distributed validators".to_string(),
        ],
        model: comparison,
        verification_core_model: Some(verification_core_model),
        transport_model: Some(transport_model),
        coefficient_bootstrap: bootstrap,
        sample_scores,
        circle_sweep,
        failure_modes: failures,
        notes: vec![
            "All field-operation counts are proxy microkernel counts, not dynamic counters from a live verifier.".to_string(),
            "Synthetic verifier measurements aggregate upload cost and verify cost into one record for scoring purposes.".to_string(),
            "Verification-core and transport component models are secondary fits used for decomposition, not replacements for the monolithic scorer.".to_string(),
        ],
    };

    write_jsonl(&results_dir.join("measurements.jsonl"), &records)?;
    write_csv(&results_dir.join("measurements.csv"), &records)?;
    write_json(&results_dir.join("summary.json"), &summary)?;
    fs::write(
        docs_dir.join("phase1-cost-model.md"),
        render_markdown_report(&summary),
    )?;
    eprintln!("phase1: done");

    Ok(())
}

fn run_phase1_next() -> Result<()> {
    let root = workspace_root()?;
    let results_dir = root.join("phase1_results");
    let docs_dir = root.join("docs");
    let examples_dir = root.join("examples/phase1");
    fs::create_dir_all(&results_dir)?;
    fs::create_dir_all(&docs_dir)?;
    fs::create_dir_all(&examples_dir)?;

    let summary_path = results_dir.join("summary.json");
    if !summary_path.exists() {
        eprintln!("phase1-next: phase1 summary missing, running base pipeline");
        run_phase1()?;
    }
    let summary = load_summary(&summary_path)?;
    let limits = SvmLimits::default();

    eprintln!("phase1-next: real-verifier");
    let real_verifier = build_real_verifier_comparison(&root, &examples_dir, &summary, &limits)?;
    write_json(
        &results_dir.join("real_verifier_comparison.json"),
        &real_verifier,
    )?;

    eprintln!("phase1-next: spend-profiles");
    let spend_profile_scores =
        write_spend_profiles(&examples_dir, &results_dir, &summary, &limits)?;

    let version_manifest = capture_version_manifest()?;
    write_json(
        &results_dir.join("version_manifest.json"),
        &version_manifest,
    )?;
    eprintln!("phase1-next: version-manifest");

    let program_so = build_sbf_program(&root)?;
    let validator = start_validator(&root, &results_dir, &program_so)?;
    let harness = BenchHarness {
        client: LocalRpcClient::new(validator.rpc_url.clone()),
        payer: Keypair::new(),
        program_id: id(),
        limits: limits.clone(),
    };
    fund_payer(&harness)?;
    eprintln!("phase1-next: orthogonal-funded-payer");
    let (orthogonal_records, orthogonal_summary) = run_orthogonal_sweeps(&harness)?;
    write_jsonl(
        &results_dir.join("orthogonal_measurements.jsonl"),
        &orthogonal_records,
    )?;
    write_csv(
        &results_dir.join("orthogonal_measurements.csv"),
        &orthogonal_records,
    )?;
    write_json(
        &results_dir.join("orthogonal_sweep_summary.json"),
        &orthogonal_summary,
    )?;
    eprintln!("phase1-next: orthogonal-sweeps");
    let refined_spend = write_refined_spend_outputs(
        &examples_dir,
        &results_dir,
        &summary,
        &orthogonal_summary,
        &limits,
    )?;
    eprintln!("phase1-next: refined-spend");

    let next_summary = Phase1NextSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask phase1-next".to_string(),
        raw_artifacts: vec![
            "phase1_results/real_verifier_comparison.json".to_string(),
            "phase1_results/spend_profile_scores.json".to_string(),
            "phase1_results/refined_spend_model.json".to_string(),
            "phase1_results/refined_spend_core_model.json".to_string(),
            "phase1_results/refined_spend_scores.json".to_string(),
            "phase1_results/refined_spend_sweep.json".to_string(),
            "phase1_results/refined_spend_sweep.csv".to_string(),
            "phase1_results/structured_spend_projections.json".to_string(),
            "phase1_results/refined_spend_summary.json".to_string(),
            "phase1_results/security_qualified_spend_sweep.json".to_string(),
            "phase1_results/security_qualified_spend_sweep.csv".to_string(),
            "phase1_results/security_qualified_spend_summary.json".to_string(),
            "phase1_results/orthogonal_measurements.jsonl".to_string(),
            "phase1_results/orthogonal_measurements.csv".to_string(),
            "phase1_results/orthogonal_sweep_summary.json".to_string(),
            "phase1_results/version_manifest.json".to_string(),
            "phase1_results/phase1_next_summary.json".to_string(),
            "docs/phase1-next-experiments.md".to_string(),
        ],
        real_verifier_comparison_path: "phase1_results/real_verifier_comparison.json".to_string(),
        spend_profile_scores_path: "phase1_results/spend_profile_scores.json".to_string(),
        refined_spend_summary_path: "phase1_results/refined_spend_summary.json".to_string(),
        refined_spend_sweep_path: "phase1_results/refined_spend_sweep.json".to_string(),
        constrained_spend_model_path: "phase1_results/refined_spend_model.json".to_string(),
        orthogonal_measurements_path: "phase1_results/orthogonal_measurements.jsonl".to_string(),
        orthogonal_summary_path: "phase1_results/orthogonal_sweep_summary.json".to_string(),
        version_manifest_path: "phase1_results/version_manifest.json".to_string(),
        notes: vec![
            "Real-verifier comparison is scored from a locally generated proof and externally measured verify_stark CSV data from pqzk-labs/solana-pqzk-fullchain.".to_string(),
            "Spend profiles now carry protocol-backed query-soundness assessments, but they still stop short of a full production-verifier security proof."
                .to_string(),
            "In all spend outputs, q is a literal absolute verifier-query count in the current model rather than a query-round count or hidden effective-query estimate."
                .to_string(),
            "Security-qualified spend outputs now sweep rate and grinding jointly, then solve for the minimum q required under each soundness assumption before scoring verifier cost."
                .to_string(),
            "Orthogonal sweeps were executed locally on Agave/Solana 2.3.0 using the Phase 1 probe program."
                .to_string(),
            "Refined spend scoring constrains account-I/O coefficients from orthogonal sweeps without refitting the full additive model; inversion is used only if the Winterfell-aligned inversion sweep completes without failures."
                .to_string(),
        ],
    };
    write_json(&results_dir.join("phase1_next_summary.json"), &next_summary)?;
    fs::write(
        docs_dir.join("phase1-next-experiments.md"),
        render_phase1_next_report(
            &summary,
            &real_verifier,
            &spend_profile_scores,
            &refined_spend,
            &orthogonal_summary,
            &version_manifest,
        ),
    )?;
    eprintln!("phase1-next: done");

    Ok(())
}

fn workspace_root() -> Result<PathBuf> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .map(Path::to_path_buf)
        .ok_or_else(|| anyhow!("failed to determine workspace root"))
}

fn run_command_capture(program: &str, args: &[&str]) -> Result<String> {
    let output = Command::new(program)
        .args(args)
        .output()
        .with_context(|| format!("failed to run {program} {}", args.join(" ")))?;
    if !output.status.success() {
        bail!(
            "{program} {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

fn capture_version_manifest() -> Result<VersionManifest> {
    let commands = [
        ("solana-test-validator", vec!["--version"]),
        ("cargo-build-sbf", vec!["--version"]),
        ("rustc", vec!["--version"]),
        ("cargo", vec!["--version"]),
    ];
    let mut executed = Vec::new();
    for (program, args) in commands {
        executed.push(VersionCommandResult {
            command: format!("{program} {}", args.join(" ")),
            output: run_command_capture(program, &args)?,
        });
    }
    Ok(VersionManifest {
        generated_at_utc: Utc::now().to_rfc3339(),
        executed,
        not_executed: vec![
            "Cross-version validator drift was not executed here; set up alternate Agave/Solana binaries and rerun `cargo xtask phase1-next` under those toolchains.".to_string(),
        ],
    })
}

fn parse_csv_cu_values(path: &Path) -> Result<Vec<u64>> {
    let bytes =
        fs::read_to_string(path).with_context(|| format!("failed to read {}", path.display()))?;
    let mut values = Vec::new();
    for line in bytes.lines() {
        let mut parts = line.split(',');
        let _timestamp = parts.next();
        let _phase = parts.next();
        let cu = parts
            .next()
            .ok_or_else(|| anyhow!("missing CU column in {}", path.display()))?
            .parse::<u64>()
            .with_context(|| format!("failed to parse CU in {}", path.display()))?;
        values.push(cu);
    }
    if values.is_empty() {
        bail!("no CU samples found in {}", path.display());
    }
    Ok(values)
}

fn summarize_cu_values(values: &[u64]) -> ExternalCuSummary {
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let mean = sorted.iter().map(|value| *value as f64).sum::<f64>() / sorted.len() as f64;
    let median = if sorted.len() % 2 == 0 {
        let hi = sorted.len() / 2;
        (sorted[hi - 1] as f64 + sorted[hi] as f64) / 2.0
    } else {
        sorted[sorted.len() / 2] as f64
    };
    ExternalCuSummary {
        run_count: sorted.len(),
        mean_cu: mean,
        median_cu: median,
        min_cu: *sorted.first().unwrap_or(&0),
        max_cu: *sorted.last().unwrap_or(&0),
    }
}

fn field_extension_name(extension: FieldExtension) -> &'static str {
    match extension {
        FieldExtension::None => "none",
        FieldExtension::Quadratic => "quadratic",
        FieldExtension::Cubic => "cubic",
    }
}

fn total_nodes_in_batch_proof<H: winterfell::crypto::Hasher>(
    proof: &winterfell::crypto::BatchMerkleProof<H>,
) -> u64 {
    proof.nodes.iter().map(|layer| layer.len() as u64).sum()
}

fn derive_pqzk_public_inputs(cipher: &[u8]) -> PqzkPublicInputs {
    let digest = hashv(&[cipher]).to_bytes();
    let mut lo = [0u8; 8];
    let mut hi = [0u8; 8];
    lo.copy_from_slice(&digest[0..8]);
    hi.copy_from_slice(&digest[8..16]);
    PqzkPublicInputs {
        seed: BaseElement::from(u64::from_le_bytes(lo)),
        inc: BaseElement::from(u64::from_le_bytes(hi)),
    }
}

fn extract_pqzk_structure(root: &Path) -> Result<PqzkProofStructure> {
    let proof_path = root.join("third_party/solana-pqzk-fullchain/proof.bin");
    let proof_bytes = fs::read(&proof_path)
        .with_context(|| format!("failed to read {}", proof_path.display()))?;
    let proof = Proof::from_bytes(&proof_bytes)
        .with_context(|| format!("failed to parse {}", proof_path.display()))?;

    let cipher_bytes = 28_u64;
    let kem_ciphertext_bytes = 1_088_u64;
    let public_inputs = derive_pqzk_public_inputs(&vec![0u8; cipher_bytes as usize]);
    let air = PqzkMessageAir::new_internal(
        proof.trace_info().clone(),
        public_inputs,
        proof.options().clone(),
    );

    let fri_options = proof.options().to_fri_options();
    let folding_factor = fri_options.folding_factor();
    let lde_domain_size = proof.lde_domain_size();
    let num_unique_queries = proof.num_unique_queries as usize;

    let mut trace_query_depths = Vec::new();
    let mut total_batched_merkle_nodes = 0_u64;
    for trace_queries in proof.trace_queries.clone() {
        let (proof_nodes, _values) = trace_queries.parse::<BaseElement, PqzkHasher, PqzkMerkle>(
            lde_domain_size,
            num_unique_queries,
            air.trace_info().main_trace_width(),
        )?;
        trace_query_depths.push(proof_nodes.depth as u64);
        total_batched_merkle_nodes += total_nodes_in_batch_proof(&proof_nodes);
    }

    let (constraint_nodes, _constraint_values) = proof
        .constraint_queries
        .clone()
        .parse::<BaseElement, PqzkHasher, PqzkMerkle>(
            lde_domain_size,
            num_unique_queries,
            air.context().num_constraint_composition_columns(),
        )?;
    total_batched_merkle_nodes += total_nodes_in_batch_proof(&constraint_nodes);

    let (fri_layer_queries, fri_layer_proofs) = proof
        .fri_proof
        .clone()
        .parse_layers::<BaseElement, PqzkHasher, PqzkMerkle>(lde_domain_size, folding_factor)?;
    let mut fri_layer_depths = Vec::new();
    for proof_nodes in &fri_layer_proofs {
        fri_layer_depths.push(proof_nodes.depth as u64);
        total_batched_merkle_nodes += total_nodes_in_batch_proof(proof_nodes);
    }

    let merkle_depth_sum = trace_query_depths.iter().sum::<u64>()
        + constraint_nodes.depth as u64
        + fri_layer_depths.iter().sum::<u64>();
    let merkle_query_families = trace_query_depths.len() as u64 + 1 + fri_layer_depths.len() as u64;
    let total_merkle_levels_unbatched = merkle_depth_sum * num_unique_queries as u64;
    let body_bytes = cipher_bytes + kem_ciphertext_bytes + proof_bytes.len() as u64;
    let chat_msg_account_bytes = 8 + 164 + body_bytes;

    Ok(PqzkProofStructure {
        proof_path: proof_path.display().to_string(),
        proof_sha256: hex_bytes(&solana_sdk::hash::hash(&proof_bytes).to_bytes()),
        proof_bytes: proof_bytes.len() as u64,
        trace_width: proof.trace_info().width() as u64,
        trace_length: proof.trace_info().length() as u64,
        num_trace_segments: proof.trace_queries.len() as u64,
        num_unique_queries: proof.num_unique_queries as u64,
        configured_queries: proof.options().num_queries() as u64,
        blowup_factor: proof.options().blowup_factor() as u64,
        grinding_factor: proof.options().grinding_factor() as u64,
        field_extension: field_extension_name(proof.options().field_extension()).to_string(),
        folding_factor: folding_factor as u64,
        fri_layers: fri_layer_queries.len() as u64,
        fri_remainder_elements: proof.fri_proof.num_remainder_elements::<BaseElement>() as u64,
        lde_domain_size: lde_domain_size as u64,
        trace_query_depths,
        constraint_query_depth: constraint_nodes.depth as u64,
        fri_layer_depths,
        merkle_query_families,
        total_merkle_levels_unbatched,
        total_batched_merkle_nodes,
        cipher_bytes,
        kem_ciphertext_bytes,
        body_bytes,
        chat_msg_account_bytes,
        heap_frame_bytes_requested: 262_144,
        notes: vec![
            "Proof structure was parsed from a locally generated proof.bin emitted by the pqzk-labs prover.".to_string(),
            "Cipher bytes follow the external CLI demo's Hello world AES-256-GCM example: 12 plaintext bytes + 16-byte tag = 28 bytes.".to_string(),
            "ChatMsg account size uses 8 discriminator bytes + CHAT_HEAD(164) + body length from the external verifier state layout.".to_string(),
        ],
    })
}

fn pqzk_real_verifier_field_inv_diagnostic(
    structure: &PqzkProofStructure,
) -> RealVerifierFieldInvDiagnostic {
    let prior_query_scaled_proxy = structure.num_unique_queries.max(1);
    let ood_transition_divisions = 1_u64;
    let boundary_constraint_group_divisions = 2_u64;
    let deep_composer_batch_inversions = if structure.num_unique_queries > 0 {
        1
    } else {
        0
    };
    let fri_layer_batch_inversions = structure.fri_layers;
    let estimated_total = ood_transition_divisions
        + boundary_constraint_group_divisions
        + deep_composer_batch_inversions
        + fri_layer_batch_inversions;

    RealVerifierFieldInvDiagnostic {
        prior_query_scaled_proxy,
        ood_transition_divisions,
        boundary_constraint_group_divisions,
        deep_composer_batch_inversions,
        fri_layer_batch_inversions,
        estimated_total,
        notes: vec![
            "The previous proxy scaled field inversions with the number of unique queries, which treated the verifier like a per-query inversion kernel.".to_string(),
            "Code inspection of the Winterfell verifier path points to a small constant number of inversions for this AIR: one transition-divisor division in evaluator::combine_evaluations, two boundary-constraint-group divisions from the AIR's two assertions, one DEEP batch inversion in composer::compose_columns, and one interpolation batch inversion per recursive FRI layer.".to_string(),
            "For the current pqzk proof, fri_layers=0, so the defensible field_inv_ops proxy is 4 rather than 27.".to_string(),
        ],
    }
}

fn pqzk_real_verifier_field_mul_diagnostic(
    structure: &PqzkProofStructure,
) -> RealVerifierFieldMulDiagnostic {
    let prior_proxy = structure.num_unique_queries
        * (3 + structure.merkle_query_families * 2
            + structure.folding_factor.saturating_div(2).max(1));
    let remainder_horner_mul_ops =
        structure.num_unique_queries * structure.fri_remainder_elements.max(1);
    let query_coordinate_lift_mul_ops = structure.num_unique_queries;
    let estimated_total = remainder_horner_mul_ops + query_coordinate_lift_mul_ops;

    RealVerifierFieldMulDiagnostic {
        prior_proxy,
        remainder_horner_mul_ops,
        query_coordinate_lift_mul_ops,
        estimated_total,
        notes: vec![
            "The real-verifier field_mul_ops proxy is now tied to the two dominant query-scaled multiplication kernels visible in the Winterfell source: Horner evaluation of the FRI remainder polynomial and one base-field lift/multiply when materializing each queried x-coordinate.".to_string(),
            "For this proof, the FRI remainder has 8 coefficients and there are 27 unique queries, yielding 216 Horner multiplications plus 27 x-coordinate lifts for a total proxy of 243.".to_string(),
            "This remains a compressed proxy rather than a literal count of every multiplication in the verifier; mixed arithmetic inside DEEP composition and OOD reduction is intentionally left out so the proxy stays aligned with the fitted Phase 1 microkernel scale.".to_string(),
        ],
    }
}

fn pqzk_real_verifier_extension_mul_diagnostic(
    structure: &PqzkProofStructure,
) -> RealVerifierExtensionMulDiagnostic {
    let notes = if structure.field_extension == "none" {
        vec![
            "The pqzk verifier selects Winterfell's base-field verification path because proof.options().field_extension() is None.".to_string(),
            "Under this path, quadratic/cubic extension arithmetic is not instantiated, so extension_mul_ops is exactly zero for this proof family.".to_string(),
        ]
    } else {
        vec![
            "Non-base-field verification would instantiate Winterfell's extension-field verifier path, but this proof does not do so.".to_string(),
        ]
    };

    RealVerifierExtensionMulDiagnostic {
        estimated_total: 0,
        notes,
    }
}

fn pqzk_real_verifier_profile(structure: &PqzkProofStructure) -> ProfileScoreInput {
    let query_families = structure.merkle_query_families.max(1);
    let num_unique_queries = structure.num_unique_queries.max(1);
    let fixed_hash_calls = 1 + structure.fri_layers + 2;
    let sha_calls = fixed_hash_calls
        + structure.total_merkle_levels_unbatched
        + num_unique_queries * query_families;
    let sha_bytes = structure.cipher_bytes
        + structure.total_merkle_levels_unbatched * 64
        + num_unique_queries * query_families * 64
        + 32 * (query_families + 2);
    let field_add_sub_ops = num_unique_queries * (5 + query_families * 2 + structure.fri_layers);
    let field_mul_diagnostic = pqzk_real_verifier_field_mul_diagnostic(structure);
    let field_mul_ops = field_mul_diagnostic.estimated_total;
    let field_inv_diagnostic = pqzk_real_verifier_field_inv_diagnostic(structure);
    let field_inv_ops = field_inv_diagnostic.estimated_total;
    let extension_mul_diagnostic = pqzk_real_verifier_extension_mul_diagnostic(structure);
    let heap_frame_bytes_requested = structure.heap_frame_bytes_requested;

    ProfileScoreInput {
        name: "pqzk-real-verifier-profile".to_string(),
        protocol_family: Some("Winterfell-FRI".to_string()),
        features: CostFeatures {
            sha_calls,
            sha_bytes,
            merkle_paths: num_unique_queries * query_families,
            merkle_levels: structure.total_merkle_levels_unbatched,
            proof_bytes: structure.proof_bytes,
            proof_segments: 1,
            upload_bytes: 0,
            upload_chunks: 0,
            heap_frame_bytes_requested,
            heap_pages_32k: heap_frame_bytes_requested.div_ceil(32 * 1024),
            ro_account_count: 1,
            rw_account_count: 0,
            account_data_bytes_read: structure.chat_msg_account_bytes,
            account_data_bytes_written: 0,
            field_add_sub_ops,
            field_mul_ops,
            field_inv_ops,
            extension_mul_ops: extension_mul_diagnostic.estimated_total,
        },
        transport: TransportCostFeatures::default(),
        parameter_choices: vec![
            parameter_choice(
                "proof_bytes",
                structure.proof_bytes.to_string(),
                "Directly measured from the locally generated proof.bin emitted by the external pqzk-labs prover.",
                &["https://github.com/pqzk-labs/solana-pqzk-fullchain"],
            ),
            parameter_choice(
                "num_queries",
                structure.configured_queries.to_string(),
                "Taken directly from the prover's ProofOptions::new(30, 16, 8, FieldExtension::None, 4, 31, ...).",
                &[
                    "https://github.com/pqzk-labs/solana-pqzk-fullchain",
                    "https://eprint.iacr.org/2025/1741",
                ],
            ),
            parameter_choice(
                "heap_frame_bytes_requested",
                heap_frame_bytes_requested.to_string(),
                "Matches the external verifier's documented 256 KiB heap request for verify_stark.",
                &["https://github.com/pqzk-labs/solana-pqzk-fullchain"],
            ),
        ],
        references: vec![
            "https://github.com/pqzk-labs/solana-pqzk-fullchain".to_string(),
            "https://eprint.iacr.org/2025/1741".to_string(),
        ],
        query_soundness_model: Some(fri_query_soundness_model(
            structure.configured_queries,
            structure.blowup_factor.ilog2(),
            structure.grinding_factor as u32,
            128.0,
            &[
                "https://eprint.iacr.org/2020/654",
                "https://eprint.iacr.org/2021/582",
                "https://github.com/Plonky3/Plonky3/blob/main/fri/src/prover.rs",
            ],
            &[
                "Query soundness is attached here to make the real-verifier comparison explicit about its 30-query, blowup-16 configuration.",
            ],
        )),
        notes: vec![
            "Intended to approximate the external verify_stark phase only; upload transport is set to zero because the comparison target is the repo's verify-only benchmark.".to_string(),
            "Hash, Merkle, and account-byte features are structure-derived from the proof and verifier layout.".to_string(),
            "Field-operation counts are source-backed verifier-kernel proxies, not dynamic Winterfell counters.".to_string(),
            format!(
                "field_inv_ops uses an execution-structure proxy of {} rather than the earlier query-scaled proxy of {}.",
                field_inv_diagnostic.estimated_total, field_inv_diagnostic.prior_query_scaled_proxy
            ),
            format!(
                "field_mul_ops uses a source-backed proxy of {} built from remainder Horner multiplications ({}) plus queried x-coordinate lifts ({}).",
                field_mul_ops,
                field_mul_diagnostic.remainder_horner_mul_ops,
                field_mul_diagnostic.query_coordinate_lift_mul_ops
            ),
        ],
    }
}

fn build_real_verifier_comparison(
    root: &Path,
    examples_dir: &Path,
    summary: &Phase1Summary,
    limits: &SvmLimits,
) -> Result<RealVerifierComparison> {
    let repo_root = root.join("third_party/solana-pqzk-fullchain");
    let verify_only = summarize_cu_values(&parse_csv_cu_values(
        &repo_root.join("examples/benchmarks/results-verify-only.csv"),
    )?);
    let finalize_only = summarize_cu_values(&parse_csv_cu_values(
        &repo_root.join("examples/benchmarks/results-finalize-only.csv"),
    )?);
    let structure = extract_pqzk_structure(root)?;
    let field_inv_diagnostic = pqzk_real_verifier_field_inv_diagnostic(&structure);
    let field_mul_diagnostic = pqzk_real_verifier_field_mul_diagnostic(&structure);
    let extension_mul_diagnostic = pqzk_real_verifier_extension_mul_diagnostic(&structure);
    let profile = pqzk_real_verifier_profile(&structure);
    let profile_path = examples_dir.join("pqzk-real-verifier-profile.yaml");
    fs::write(&profile_path, serde_yaml::to_string(&profile)?)?;
    let score = score_profile_with_components(
        &summary.model.chosen,
        summary
            .verification_core_model
            .as_ref()
            .map(|value| &value.chosen),
        summary.transport_model.as_ref().map(|value| &value.chosen),
        limits,
        &profile,
    )?;
    let measured_minus_predicted_cu = verify_only.mean_cu - score.predicted_cu;
    let absolute_error_cu = measured_minus_predicted_cu.abs();
    let relative_error_fraction = if verify_only.mean_cu > 0.0 {
        absolute_error_cu / verify_only.mean_cu
    } else {
        0.0
    };

    let field_mul_ops_backsolved_for_mean = summary
        .model
        .chosen
        .coefficients
        .field_mul_ops
        .as_ref()
        .and_then(|coef| {
            if coef.estimate <= 0.0 {
                return None;
            }
            let mut zero_mul = profile.features.clone();
            zero_mul.field_mul_ops = 0;
            let predicted_without_field_mul = score_profile_with_components(
                &summary.model.chosen,
                None,
                None,
                limits,
                &ProfileScoreInput {
                    name: profile.name.clone(),
                    protocol_family: profile.protocol_family.clone(),
                    features: zero_mul,
                    transport: profile.transport.clone(),
                    parameter_choices: profile.parameter_choices.clone(),
                    references: profile.references.clone(),
                    query_soundness_model: profile.query_soundness_model.clone(),
                    notes: profile.notes.clone(),
                },
            )
            .ok()?
            .predicted_cu;
            Some(((verify_only.mean_cu - predicted_without_field_mul) / coef.estimate).max(0.0))
        });

    Ok(RealVerifierComparison {
        generated_at_utc: Utc::now().to_rfc3339(),
        source_repo: "https://github.com/pqzk-labs/solana-pqzk-fullchain".to_string(),
        source_paper: "https://eprint.iacr.org/2025/1741".to_string(),
        verify_stark_baseline: verify_only,
        finalize_sig_baseline: finalize_only,
        structure,
        scored_profile_path: profile_path.display().to_string(),
        scored_profile: profile,
        score,
        measured_minus_predicted_cu,
        absolute_error_cu,
        relative_error_fraction,
        field_inv_diagnostic,
        field_mul_diagnostic,
        extension_mul_diagnostic,
        field_mul_ops_backsolved_for_mean,
        notes: vec![
            "Measured baseline comes from the external repository's 100-run verify-only CSV, not from a rerun in this workspace.".to_string(),
            "The scored profile uses a locally generated proof.bin and structural feature extraction against the same verifier family.".to_string(),
            "The 23% miss in the prior pass was traced to an unsupported query-scaled field_inv_ops proxy; this artifact records the corrected execution-structure proxy.".to_string(),
            "Field multiplication and extension-field terms are now audited against the Winterfell source path used by this proof family, rather than left as unlabeled heuristics.".to_string(),
            "Backsolved field_mul_ops is diagnostic only; it is not an independently measured coefficient.".to_string(),
        ],
    })
}

fn build_sbf_program(root: &Path) -> Result<PathBuf> {
    let out_dir = root.join("target/phase1-sbf");
    fs::create_dir_all(&out_dir)?;
    let status = Command::new("cargo")
        .arg("build-sbf")
        .arg("--manifest-path")
        .arg(root.join("programs/phase1-probe/Cargo.toml"))
        .arg("--features")
        .arg("phase2-instrumentation")
        .arg("--sbf-out-dir")
        .arg(&out_dir)
        .status()
        .context("failed to run cargo build-sbf")?;
    if !status.success() {
        bail!("cargo build-sbf failed");
    }
    let so_path = out_dir.join("phase1_probe.so");
    if !so_path.exists() {
        bail!("expected SBF artifact missing at {}", so_path.display());
    }
    Ok(so_path)
}

fn reserve_port() -> Result<u16> {
    let listener = TcpListener::bind("127.0.0.1:0")?;
    Ok(listener.local_addr()?.port())
}

fn remove_generated_yaml_with_prefix(examples_dir: &Path, prefix: &str) -> Result<()> {
    if !examples_dir.exists() {
        return Ok(());
    }
    for entry in fs::read_dir(examples_dir)? {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let Some(file_name) = path.file_name().and_then(|value| value.to_str()) else {
            continue;
        };
        if file_name.starts_with(prefix) && file_name.ends_with(".yaml") {
            fs::remove_file(path)?;
        }
    }
    Ok(())
}

fn start_validator(root: &Path, results_dir: &Path, program_so: &Path) -> Result<ValidatorGuard> {
    start_validator_with_program(root, results_dir, id(), program_so)
}

fn start_validator_with_program(
    root: &Path,
    results_dir: &Path,
    program_id: Pubkey,
    program_so: &Path,
) -> Result<ValidatorGuard> {
    let rpc_port = reserve_port()?;
    let faucet_port = reserve_port()?;
    let gossip_port = reserve_port()?;
    let ledger_dir = root.join(".phase1-validator/ledger");
    if ledger_dir.exists() {
        fs::remove_dir_all(&ledger_dir)?;
    }
    fs::create_dir_all(ledger_dir.parent().unwrap())?;
    let log_path = results_dir.join("validator.log");
    let stdout = File::create(&log_path)?;
    let stderr = stdout.try_clone()?;

    let mut child = Command::new("solana-test-validator")
        .arg("--reset")
        .arg("--quiet")
        .arg("--ledger")
        .arg(&ledger_dir)
        .arg("--rpc-port")
        .arg(rpc_port.to_string())
        .arg("--faucet-port")
        .arg(faucet_port.to_string())
        .arg("--gossip-port")
        .arg(gossip_port.to_string())
        .arg("--bpf-program")
        .arg(program_id.to_string())
        .arg(program_so)
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .context("failed to start solana-test-validator")?;

    let rpc_url = format!("http://127.0.0.1:{rpc_port}");
    let client = LocalRpcClient::new(rpc_url.clone());
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        if let Ok(_) = client.get_latest_blockhash() {
            break;
        }
        if Instant::now() > deadline {
            let _ = child.kill();
            bail!("validator did not become ready within 60s");
        }
        thread::sleep(Duration::from_millis(500));
    }

    Ok(ValidatorGuard {
        child,
        rpc_url,
        _log_path: log_path,
    })
}

fn fund_payer(harness: &BenchHarness) -> Result<()> {
    harness
        .client
        .request_airdrop(&harness.payer.pubkey(), 10 * LAMPORTS_PER_SOL)
        .context("failed to request airdrop")?;
    let deadline = Instant::now() + Duration::from_secs(15);
    loop {
        let balance = harness.client.get_balance(&harness.payer.pubkey())?;
        if balance >= LAMPORTS_PER_SOL {
            return Ok(());
        }
        if Instant::now() > deadline {
            bail!("payer funding did not settle within 15s");
        }
        thread::sleep(Duration::from_millis(250));
    }
}

fn new_record(
    benchmark: BenchmarkKind,
    label: impl Into<String>,
    repetition: u32,
    limits: &SvmLimits,
    features: CostFeatures,
    feature_origins: BTreeMap<String, FeatureOrigin>,
    tx: SimulatedTx,
    notes: Vec<String>,
) -> MeasurementRecord {
    MeasurementRecord {
        measurement_id: format!(
            "{:?}-{}-r{}",
            benchmark,
            Utc::now().timestamp_millis(),
            repetition
        ),
        benchmark,
        label: label.into(),
        repetition,
        timestamp_utc: Utc::now().to_rfc3339(),
        svm_limits: limits.clone(),
        features,
        feature_origins,
        actual_cu: tx.units_consumed,
        transaction_bytes: Some(tx.transaction_bytes),
        status: if tx.error.is_none() {
            MeasurementStatus::Success
        } else {
            MeasurementStatus::Failed
        },
        error: tx.error,
        notes,
    }
}

fn default_origins() -> BTreeMap<String, FeatureOrigin> {
    BTreeMap::new()
}

fn simulate_plan(harness: &BenchHarness, plan: TxPlan) -> Result<SimulatedTx> {
    let mut instructions = Vec::new();
    instructions.push(ComputeBudgetInstruction::set_compute_unit_limit(
        plan.compute_unit_limit
            .unwrap_or(harness.limits.max_compute_units_per_tx as u32),
    ));
    if let Some(heap_frame_bytes) = plan.heap_frame_bytes {
        instructions.push(ComputeBudgetInstruction::request_heap_frame(
            heap_frame_bytes,
        ));
    }
    instructions.extend(plan.instructions);

    let recent_blockhash = harness.client.get_latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&harness.payer.pubkey()),
        &[&harness.payer],
        recent_blockhash,
    );
    let tx_size = bincode::serialized_size(&tx)? as u64;
    if tx_size > harness.limits.max_transaction_bytes {
        return Ok(SimulatedTx {
            units_consumed: None,
            transaction_bytes: tx_size,
            error: Some(format!(
                "serialized transaction {tx_size} exceeds limit {}",
                harness.limits.max_transaction_bytes
            )),
            logs: Vec::new(),
        });
    }

    let response = harness.client.simulate_transaction(&tx)?;
    Ok(SimulatedTx {
        units_consumed: response.units_consumed,
        transaction_bytes: tx_size,
        error: response.error,
        logs: response.logs,
    })
}

fn send_instructions(
    harness: &BenchHarness,
    instructions: Vec<Instruction>,
    additional_signers: &[&Keypair],
) -> Result<()> {
    let mut instructions = instructions;
    instructions.insert(
        0,
        ComputeBudgetInstruction::set_compute_unit_limit(
            harness.limits.max_compute_units_per_tx as u32,
        ),
    );
    let recent_blockhash = harness.client.get_latest_blockhash()?;
    let mut signer_refs = vec![&harness.payer];
    signer_refs.extend_from_slice(additional_signers);
    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&harness.payer.pubkey()),
        &signer_refs,
        recent_blockhash,
    );
    harness.client.send_and_confirm_transaction(&tx)?;
    Ok(())
}

fn create_program_account(harness: &BenchHarness, size: usize) -> Result<Keypair> {
    let account = Keypair::new();
    let lamports = harness
        .client
        .get_minimum_balance_for_rent_exemption(size)
        .context("failed to fetch rent exemption")?;
    let create = system_instruction::create_account(
        &harness.payer.pubkey(),
        &account.pubkey(),
        lamports,
        size as u64,
        &harness.program_id,
    );
    send_instructions(harness, vec![create], &[&account])?;
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if let Some(actual) = harness.client.get_account_data_len(&account.pubkey())? {
            if actual >= size {
                break;
            }
        }
        if Instant::now() > deadline {
            bail!(
                "account {} did not reach expected size {}",
                account.pubkey(),
                size
            );
        }
        thread::sleep(Duration::from_millis(100));
    }
    Ok(account)
}

fn populate_accounts(
    harness: &BenchHarness,
    accounts: &[Keypair],
    variable_layout: bool,
    seed: u8,
) -> Result<()> {
    let metas = accounts
        .iter()
        .map(|account| AccountMeta::new(account.pubkey(), false))
        .collect::<Vec<_>>();
    let instruction = ProbeInstruction::instruction(
        harness.program_id,
        metas,
        ProbeInstruction::PopulateAccounts {
            variable_layout,
            seed,
        },
    );
    send_instructions(harness, vec![instruction], &[])
}

fn build_fixed_proof(total_bytes: usize, segment_count: usize) -> Vec<u8> {
    let header_bytes = segment_count * 4;
    let payload_bytes = total_bytes.saturating_sub(header_bytes).max(segment_count);
    let mut remaining = payload_bytes;
    let mut out = Vec::with_capacity(header_bytes + payload_bytes);
    for segment in 0..segment_count {
        let segments_left = segment_count - segment;
        let segment_len = if segments_left == 1 {
            remaining
        } else {
            (remaining / segments_left).max(1)
        };
        out.extend_from_slice(&(segment_len as u32).to_le_bytes());
        for offset in 0..segment_len {
            out.push(((segment + offset) % 251) as u8);
        }
        remaining = remaining.saturating_sub(segment_len);
    }
    out
}

fn encode_leb128(mut value: usize, out: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn build_leb128_proof(total_bytes: usize, segment_count: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut remaining = total_bytes.max(segment_count);
    for segment in 0..segment_count {
        let segments_left = segment_count - segment;
        let segment_len = if segments_left == 1 {
            remaining.saturating_sub(out.len()).max(1)
        } else {
            (remaining / segments_left).max(1)
        };
        encode_leb128(segment_len, &mut out);
        for offset in 0..segment_len {
            out.push(((segment * 17 + offset) % 251) as u8);
        }
        remaining = remaining.saturating_sub(segment_len);
    }
    if out.len() > total_bytes {
        out.truncate(total_bytes);
    }
    out
}

fn upload_bytes(
    harness: &BenchHarness,
    data: &[u8],
    chunk_size: usize,
    rolling_hash: bool,
    label_prefix: &str,
    repetitions: u32,
) -> Result<(Keypair, Vec<MeasurementRecord>, u64)> {
    let upload_account = create_program_account(harness, data.len())?;
    let mut records = Vec::new();
    let mut total_cu = 0u64;
    let mut prior_digest = [0u8; 32];
    for (chunk_index, chunk) in data.chunks(chunk_size.max(1)).enumerate() {
        let instruction = build_upload_instruction(
            harness.program_id,
            upload_account.pubkey(),
            (chunk_index * chunk_size) as u32,
            rolling_hash,
            prior_digest,
            chunk.to_vec(),
        );

        for repetition in 0..repetitions {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            features.upload_bytes = chunk.len() as u64;
            features.upload_chunks = 1;
            if rolling_hash {
                features.sha_calls = 1;
                features.sha_bytes = (32 + chunk.len()) as u64;
            }
            let mut origins = default_origins();
            origins.insert("upload_bytes".to_string(), FeatureOrigin::DirectMeasurement);
            origins.insert(
                "upload_chunks".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            if rolling_hash {
                origins.insert("sha_calls".to_string(), FeatureOrigin::DerivedStructure);
                origins.insert("sha_bytes".to_string(), FeatureOrigin::DerivedStructure);
            }
            let record = new_record(
                BenchmarkKind::UploadPath,
                format!("{label_prefix}/chunk-{chunk_index}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx.clone(),
                if tx.logs.is_empty() {
                    Vec::new()
                } else {
                    vec![format!("logs: {}", tx.logs.join(" | "))]
                },
            );
            if repetition == 0 {
                total_cu += record.actual_cu.unwrap_or_default();
            }
            records.push(record);
        }

        send_instructions(harness, vec![instruction], &[])?;
        prior_digest = hashv(&[&prior_digest, chunk]).to_bytes();
    }
    Ok((upload_account, records, total_cu))
}

fn run_noop_benchmarks(harness: &BenchHarness) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let instruction =
        ProbeInstruction::instruction(harness.program_id, Vec::new(), ProbeInstruction::Noop);
    for repetition in 0..5 {
        let tx = simulate_plan(
            harness,
            TxPlan {
                instructions: vec![instruction.clone()],
                compute_unit_limit: None,
                heap_frame_bytes: None,
            },
        )?;
        records.push(new_record(
            BenchmarkKind::Noop,
            "noop",
            repetition,
            &harness.limits,
            CostFeatures::default(),
            default_origins(),
            tx,
            Vec::new(),
        ));
    }
    Ok(records)
}

fn run_hash_benchmarks(harness: &BenchHarness) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (1, 32),
        (4, 32),
        (8, 64),
        (16, 64),
        (16, 256),
        (32, 256),
        (32, 512),
    ];
    for (hash_calls, bytes_per_call) in scenarios {
        let instruction = ProbeInstruction::instruction(
            harness.program_id,
            Vec::new(),
            ProbeInstruction::Hash {
                hash_calls,
                bytes_per_call,
            },
        );
        for repetition in 0..3 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            features.sha_calls = hash_calls as u64;
            features.sha_bytes = hash_calls as u64 * (bytes_per_call as u64 + 33);
            let mut origins = default_origins();
            origins.insert("sha_calls".to_string(), FeatureOrigin::DirectMeasurement);
            origins.insert("sha_bytes".to_string(), FeatureOrigin::DirectMeasurement);
            records.push(new_record(
                BenchmarkKind::HashSyscall,
                format!("hash/{hash_calls}x{bytes_per_call}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                Vec::new(),
            ));
        }
    }
    Ok(records)
}

fn run_merkle_benchmarks(harness: &BenchHarness) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (4, 1, 32, MerkleBatchMode::Serial),
        (8, 2, 32, MerkleBatchMode::Serial),
        (12, 4, 32, MerkleBatchMode::Interleaved),
        (16, 4, 64, MerkleBatchMode::Serial),
        (20, 8, 32, MerkleBatchMode::Interleaved),
    ];
    for (depth, paths, sibling_size, batch_mode) in scenarios {
        let instruction = ProbeInstruction::instruction(
            harness.program_id,
            Vec::new(),
            ProbeInstruction::Merkle {
                path_depth: depth,
                path_count: paths,
                sibling_size,
                batch_mode,
            },
        );
        for repetition in 0..3 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            features.merkle_paths = paths as u64;
            features.merkle_levels = depth as u64 * paths as u64;
            features.sha_calls = features.merkle_levels + paths as u64;
            features.sha_bytes =
                features.merkle_levels * (32 + sibling_size as u64) + paths as u64 * 64;
            let mut origins = default_origins();
            origins.insert("merkle_paths".to_string(), FeatureOrigin::DirectMeasurement);
            origins.insert("merkle_levels".to_string(), FeatureOrigin::DerivedStructure);
            origins.insert("sha_calls".to_string(), FeatureOrigin::DerivedStructure);
            origins.insert("sha_bytes".to_string(), FeatureOrigin::DerivedStructure);
            records.push(new_record(
                BenchmarkKind::MerklePath,
                format!("merkle/{depth}d-{paths}p-{sibling_size}b-{batch_mode:?}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                Vec::new(),
            ));
        }
    }
    Ok(records)
}

fn run_field_benchmarks(harness: &BenchHarness) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (FieldKernel::AddSub, 512u32),
        (FieldKernel::AddSub, 4096u32),
        (FieldKernel::Mul, 256u32),
        (FieldKernel::Mul, 2048u32),
        (FieldKernel::Inv, 16u32),
        (FieldKernel::Inv, 64u32),
        (FieldKernel::ExtensionMul, 256u32),
        (FieldKernel::ExtensionMul, 1024u32),
    ];
    for (kernel, iterations) in scenarios {
        let instruction = ProbeInstruction::instruction(
            harness.program_id,
            Vec::new(),
            ProbeInstruction::FieldOps { kernel, iterations },
        );
        for repetition in 0..3 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            match kernel {
                FieldKernel::AddSub => features.field_add_sub_ops = (iterations as u64) * 3,
                FieldKernel::Mul => features.field_mul_ops = (iterations as u64) * 3,
                FieldKernel::Inv => features.field_inv_ops = (iterations as u64) * 2,
                FieldKernel::ExtensionMul => features.extension_mul_ops = iterations as u64,
            }
            let mut origins = default_origins();
            let key = match kernel {
                FieldKernel::AddSub => "field_add_sub_ops",
                FieldKernel::Mul => "field_mul_ops",
                FieldKernel::Inv => "field_inv_ops",
                FieldKernel::ExtensionMul => "extension_mul_ops",
            };
            origins.insert(key.to_string(), FeatureOrigin::EstimatedProxy);
            records.push(new_record(
                BenchmarkKind::FieldArithmetic,
                format!("field/{kernel:?}-{iterations}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                vec!["Proxy microkernel; not a live verifier op counter.".to_string()],
            ));
        }
    }
    Ok(records)
}

fn run_heap_benchmarks(
    harness: &BenchHarness,
    failures: &mut Vec<FailureObservation>,
) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (32_768u32, 8_192u32),
        (65_536u32, 16_384u32),
        (131_072u32, 65_536u32),
        (196_608u32, 131_072u32),
        (262_144u32, 196_608u32),
    ];
    for (heap_frame, scratch_bytes) in scenarios {
        let instruction = ProbeInstruction::instruction(
            harness.program_id,
            Vec::new(),
            ProbeInstruction::HeapProbe {
                scratch_bytes,
                touch_stride: 64,
            },
        );
        for repetition in 0..3 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: Some(heap_frame),
                },
            )?;
            let mut features = CostFeatures::default();
            features.heap_frame_bytes_requested = heap_frame as u64;
            features.heap_pages_32k = harness.limits.heap_pages_32k(heap_frame as u64);
            let mut origins = default_origins();
            origins.insert(
                "heap_frame_bytes_requested".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "heap_pages_32k".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            records.push(new_record(
                BenchmarkKind::HeapFrame,
                format!("heap/{heap_frame}-{scratch_bytes}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                Vec::new(),
            ));
        }
    }

    let over_limit = simulate_plan(
        harness,
        TxPlan {
            instructions: vec![ProbeInstruction::instruction(
                harness.program_id,
                Vec::new(),
                ProbeInstruction::HeapProbe {
                    scratch_bytes: 1,
                    touch_stride: 1,
                },
            )],
            compute_unit_limit: None,
            heap_frame_bytes: Some((harness.limits.max_heap_frame_bytes + 32_768) as u32),
        },
    )?;
    failures.push(FailureObservation {
        boundary: "heap_pressure".to_string(),
        status: if over_limit.error.is_some() {
            "observed".to_string()
        } else {
            "not_observed".to_string()
        },
        details: over_limit.error.unwrap_or_else(|| {
            "request above nominal heap limit unexpectedly simulated".to_string()
        }),
    });

    Ok(records)
}

fn run_account_io_benchmarks(harness: &BenchHarness) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (2usize, 1usize, 512usize, 128usize, true),
        (4usize, 2usize, 2048usize, 256usize, true),
        (4usize, 2usize, 4096usize, 512usize, false),
        (8usize, 2usize, 8192usize, 1024usize, false),
    ];
    for (ro_count, rw_count, read_bytes, write_bytes, fixed_layout) in scenarios {
        let total = ro_count + rw_count;
        let account_size = read_bytes.max(write_bytes).max(256);
        let mut accounts = Vec::new();
        for _ in 0..total {
            accounts.push(create_program_account(harness, account_size)?);
        }
        populate_accounts(harness, &accounts, !fixed_layout, 11)?;

        let mut metas = Vec::new();
        for account in accounts.iter().take(ro_count) {
            metas.push(AccountMeta::new_readonly(account.pubkey(), false));
        }
        for account in accounts.iter().skip(ro_count) {
            metas.push(AccountMeta::new(account.pubkey(), false));
        }
        let instruction = ProbeInstruction::instruction(
            harness.program_id,
            metas,
            ProbeInstruction::AccountIo {
                fixed_layout,
                read_bytes_per_account: read_bytes as u32,
                write_bytes_per_account: write_bytes as u32,
            },
        );
        for repetition in 0..3 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            features.ro_account_count = ro_count as u64;
            features.rw_account_count = rw_count as u64;
            features.account_data_bytes_read = ((ro_count + rw_count) * read_bytes) as u64;
            features.account_data_bytes_written = (rw_count * write_bytes) as u64;
            let mut origins = default_origins();
            origins.insert(
                "ro_account_count".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "rw_account_count".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "account_data_bytes_read".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            origins.insert(
                "account_data_bytes_written".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            records.push(new_record(
                BenchmarkKind::AccountIo,
                format!(
                    "account-io/{ro_count}-{rw_count}-{read_bytes}-{write_bytes}-{fixed_layout}"
                ),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                Vec::new(),
            ));
        }
    }
    Ok(records)
}

fn run_upload_path_benchmarks(
    harness: &BenchHarness,
    failures: &mut Vec<FailureObservation>,
) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (1024usize, 240usize, false),
        (4096usize, 480usize, false),
        (4096usize, 480usize, true),
        (8192usize, 640usize, true),
    ];
    for (total_bytes, chunk_size, rolling_hash) in scenarios {
        let data = (0..total_bytes)
            .map(|idx| (idx % 251) as u8)
            .collect::<Vec<_>>();
        let (_, mut upload_records, _) = upload_bytes(
            harness,
            &data,
            chunk_size,
            rolling_hash,
            &format!("upload/{total_bytes}-{chunk_size}-{rolling_hash}"),
            2,
        )?;
        records.append(&mut upload_records);
    }

    let too_large_chunk = vec![0u8; 1_050];
    let instruction = build_upload_instruction(
        harness.program_id,
        Pubkey::new_unique(),
        0,
        false,
        [0u8; 32],
        too_large_chunk,
    );
    let tx = simulate_plan(
        harness,
        TxPlan {
            instructions: vec![instruction],
            compute_unit_limit: None,
            heap_frame_bytes: None,
        },
    )?;
    failures.push(FailureObservation {
        boundary: "transaction_size_friction".to_string(),
        status: if tx.error.is_some() {
            "observed".to_string()
        } else {
            "not_observed".to_string()
        },
        details: tx.error.unwrap_or_else(|| {
            "oversized upload chunk unexpectedly stayed within transaction size budget".to_string()
        }),
    });

    Ok(records)
}

fn run_proof_parsing_benchmarks(harness: &BenchHarness) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (512usize, 4usize, ProofParseFormat::FixedWidth, 240usize),
        (2048usize, 8usize, ProofParseFormat::FixedWidth, 480usize),
        (2048usize, 8usize, ProofParseFormat::Leb128, 480usize),
        (8192usize, 16usize, ProofParseFormat::Leb128, 640usize),
    ];
    for (proof_bytes, segment_count, format, chunk_size) in scenarios {
        let data = match format {
            ProofParseFormat::FixedWidth => build_fixed_proof(proof_bytes, segment_count),
            ProofParseFormat::Leb128 => build_leb128_proof(proof_bytes, segment_count),
        };
        let (upload_account, _, _) =
            upload_bytes(harness, &data, chunk_size, false, "parse-setup", 1)?;
        let instruction = build_parse_instruction(
            harness.program_id,
            upload_account.pubkey(),
            segment_count as u32,
            format,
        );
        for repetition in 0..3 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            features.proof_bytes = data.len() as u64;
            features.proof_segments = segment_count as u64;
            let mut origins = default_origins();
            origins.insert("proof_bytes".to_string(), FeatureOrigin::DirectMeasurement);
            origins.insert(
                "proof_segments".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            records.push(new_record(
                BenchmarkKind::ProofParsing,
                format!("parse/{proof_bytes}-{segment_count}-{format:?}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                Vec::new(),
            ));
        }
    }
    Ok(records)
}

fn run_synthetic_verifier_benchmarks(
    harness: &BenchHarness,
    failures: &mut Vec<FailureObservation>,
) -> Result<Vec<MeasurementRecord>> {
    let mut records = Vec::new();
    let scenarios = [
        (
            "fri-like",
            4096usize,
            480usize,
            true,
            ProofParseFormat::FixedWidth,
            MerkleBatchMode::Serial,
            SyntheticVerifierProfile {
                hash_calls: 12,
                bytes_per_hash_call: 96,
                merkle_paths: 4,
                merkle_depth: 12,
                sibling_size: 32,
                proof_segments: 8,
                field_add_sub_ops: 2_048,
                field_mul_ops: 768,
                field_inv_ops: 48,
                extension_mul_ops: 96,
                fixed_layout: true,
                read_bytes_per_account: 512,
                write_bytes_per_account: 64,
            },
            3usize,
            1usize,
            Some(131_072u32),
        ),
        (
            "deep-merkle",
            8192usize,
            640usize,
            true,
            ProofParseFormat::Leb128,
            MerkleBatchMode::Interleaved,
            SyntheticVerifierProfile {
                hash_calls: 16,
                bytes_per_hash_call: 128,
                merkle_paths: 8,
                merkle_depth: 18,
                sibling_size: 32,
                proof_segments: 16,
                field_add_sub_ops: 4096,
                field_mul_ops: 1024,
                field_inv_ops: 64,
                extension_mul_ops: 128,
                fixed_layout: false,
                read_bytes_per_account: 1024,
                write_bytes_per_account: 128,
            },
            4usize,
            2usize,
            Some(196_608u32),
        ),
        (
            "field-heavy",
            6144usize,
            640usize,
            false,
            ProofParseFormat::Leb128,
            MerkleBatchMode::Serial,
            SyntheticVerifierProfile {
                hash_calls: 10,
                bytes_per_hash_call: 160,
                merkle_paths: 4,
                merkle_depth: 10,
                sibling_size: 64,
                proof_segments: 12,
                field_add_sub_ops: 8192,
                field_mul_ops: 2048,
                field_inv_ops: 96,
                extension_mul_ops: 192,
                fixed_layout: true,
                read_bytes_per_account: 768,
                write_bytes_per_account: 96,
            },
            2usize,
            2usize,
            Some(131_072u32),
        ),
    ];

    for (
        label,
        proof_size,
        chunk_size,
        rolling_hash,
        format,
        batch_mode,
        profile,
        ro_count,
        rw_count,
        heap_frame,
    ) in scenarios
    {
        let proof = match format {
            ProofParseFormat::FixedWidth => {
                build_fixed_proof(proof_size, profile.proof_segments as usize)
            }
            ProofParseFormat::Leb128 => {
                build_leb128_proof(proof_size, profile.proof_segments as usize)
            }
        };
        let (upload_account, mut upload_records, upload_cu) = upload_bytes(
            harness,
            &proof,
            chunk_size,
            rolling_hash,
            &format!("synthetic-upload/{label}"),
            1,
        )?;
        records.append(&mut upload_records);

        let total_accounts = ro_count + rw_count;
        let account_size = profile
            .read_bytes_per_account
            .max(profile.write_bytes_per_account) as usize
            + 256;
        let mut io_accounts = Vec::new();
        for _ in 0..total_accounts {
            io_accounts.push(create_program_account(harness, account_size)?);
        }
        populate_accounts(harness, &io_accounts, !profile.fixed_layout, 27)?;

        let mut metas = Vec::new();
        for account in io_accounts.iter().take(ro_count) {
            metas.push(AccountMeta::new_readonly(account.pubkey(), false));
        }
        for account in io_accounts.iter().skip(ro_count) {
            metas.push(AccountMeta::new(account.pubkey(), false));
        }

        let instruction = build_synthetic_instruction(
            harness.program_id,
            upload_account.pubkey(),
            profile.clone(),
            metas,
            format,
            batch_mode,
        );
        for repetition in 0..4 {
            let verify_tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: heap_frame,
                },
            )?;
            let actual_total_cu = verify_tx.units_consumed.map(|value| value + upload_cu);
            let mut features = CostFeatures::default();
            features.proof_bytes = proof.len() as u64;
            features.proof_segments = profile.proof_segments as u64;
            features.upload_bytes = proof.len() as u64;
            features.upload_chunks = proof.len().div_ceil(chunk_size) as u64;
            features.heap_frame_bytes_requested = heap_frame.unwrap_or_default() as u64;
            features.heap_pages_32k = harness
                .limits
                .heap_pages_32k(features.heap_frame_bytes_requested);
            features.sha_calls = profile.hash_calls as u64
                + profile.merkle_paths as u64 * profile.merkle_depth as u64
                + if rolling_hash {
                    features.upload_chunks
                } else {
                    0
                };
            features.sha_bytes = profile.hash_calls as u64
                * (profile.bytes_per_hash_call as u64 + 33)
                + (profile.merkle_paths as u64 * profile.merkle_depth as u64)
                    * (32 + profile.sibling_size as u64)
                + if rolling_hash {
                    features.upload_bytes + 32 * features.upload_chunks
                } else {
                    0
                };
            features.merkle_paths = profile.merkle_paths as u64;
            features.merkle_levels = profile.merkle_paths as u64 * profile.merkle_depth as u64;
            features.ro_account_count = (ro_count + 1) as u64;
            features.rw_account_count = rw_count as u64;
            features.account_data_bytes_read =
                ((ro_count + rw_count) as u64) * profile.read_bytes_per_account as u64;
            features.account_data_bytes_written =
                (rw_count as u64) * profile.write_bytes_per_account as u64;
            features.field_add_sub_ops = profile.field_add_sub_ops as u64;
            features.field_mul_ops = profile.field_mul_ops as u64;
            features.field_inv_ops = profile.field_inv_ops as u64;
            features.extension_mul_ops = profile.extension_mul_ops as u64;

            let mut origins = default_origins();
            origins.insert("proof_bytes".to_string(), FeatureOrigin::DirectMeasurement);
            origins.insert(
                "proof_segments".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            origins.insert("upload_bytes".to_string(), FeatureOrigin::DirectMeasurement);
            origins.insert(
                "upload_chunks".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "heap_frame_bytes_requested".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "heap_pages_32k".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            origins.insert("sha_calls".to_string(), FeatureOrigin::DerivedStructure);
            origins.insert("sha_bytes".to_string(), FeatureOrigin::DerivedStructure);
            origins.insert("merkle_paths".to_string(), FeatureOrigin::DirectMeasurement);
            origins.insert("merkle_levels".to_string(), FeatureOrigin::DerivedStructure);
            origins.insert(
                "ro_account_count".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "rw_account_count".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "account_data_bytes_read".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            origins.insert(
                "account_data_bytes_written".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            origins.insert(
                "field_add_sub_ops".to_string(),
                FeatureOrigin::EstimatedProxy,
            );
            origins.insert("field_mul_ops".to_string(), FeatureOrigin::EstimatedProxy);
            origins.insert("field_inv_ops".to_string(), FeatureOrigin::EstimatedProxy);
            origins.insert(
                "extension_mul_ops".to_string(),
                FeatureOrigin::EstimatedProxy,
            );

            let tx = SimulatedTx {
                units_consumed: actual_total_cu,
                transaction_bytes: verify_tx.transaction_bytes,
                error: verify_tx.error.clone(),
                logs: verify_tx.logs.clone(),
            };
            records.push(new_record(
                BenchmarkKind::SyntheticVerifier,
                format!("synthetic/{label}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                vec!["Aggregate upload + verify cost.".to_string()],
            ));
        }
    }

    let overflow_instruction = build_synthetic_instruction(
        harness.program_id,
        create_program_account(harness, 256)?.pubkey(),
        SyntheticVerifierProfile {
            hash_calls: 256,
            bytes_per_hash_call: 512,
            merkle_paths: 32,
            merkle_depth: 32,
            sibling_size: 64,
            proof_segments: 8,
            field_add_sub_ops: 65_536,
            field_mul_ops: 16_384,
            field_inv_ops: 1_024,
            extension_mul_ops: 4_096,
            fixed_layout: true,
            read_bytes_per_account: 64,
            write_bytes_per_account: 0,
        },
        Vec::new(),
        ProofParseFormat::FixedWidth,
        MerkleBatchMode::Serial,
    );
    let overflow_tx = simulate_plan(
        harness,
        TxPlan {
            instructions: vec![overflow_instruction],
            compute_unit_limit: Some(100_000),
            heap_frame_bytes: Some(131_072),
        },
    )?;
    failures.push(FailureObservation {
        boundary: "compute_unit_exhaustion".to_string(),
        status: if overflow_tx.error.is_some() {
            "observed".to_string()
        } else {
            "not_observed".to_string()
        },
        details: overflow_tx
            .error
            .unwrap_or_else(|| "expected low compute-unit cap to fail, but it did not".to_string()),
    });

    Ok(records)
}

fn run_failure_boundaries(harness: &BenchHarness) -> Result<Vec<FailureObservation>> {
    Ok(vec![FailureObservation {
        boundary: "stack_pressure".to_string(),
        status: "unknown".to_string(),
        details: format!(
            "No production verifier or recursive stack-heavy probe was present. The scaffold keeps stack pressure explicit via the documented {}-byte frame limit, but does not force a stack overflow probe yet.",
            harness.limits.stack_frame_bytes
        ),
    }])
}

fn write_jsonl(path: &Path, records: &[MeasurementRecord]) -> Result<()> {
    let mut file = File::create(path)?;
    for record in records {
        serde_json::to_writer(&mut file, record)?;
        file.write_all(b"\n")?;
    }
    Ok(())
}

fn write_csv(path: &Path, records: &[MeasurementRecord]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(CsvRecord {
            measurement_id: &record.measurement_id,
            benchmark: format!("{:?}", record.benchmark),
            label: &record.label,
            repetition: record.repetition,
            timestamp_utc: &record.timestamp_utc,
            status: format!("{:?}", record.status),
            actual_cu: record.actual_cu,
            transaction_bytes: record.transaction_bytes,
            error: record.error.as_deref(),
            sha_calls: record.features.sha_calls,
            sha_bytes: record.features.sha_bytes,
            merkle_paths: record.features.merkle_paths,
            merkle_levels: record.features.merkle_levels,
            proof_bytes: record.features.proof_bytes,
            proof_segments: record.features.proof_segments,
            upload_bytes: record.features.upload_bytes,
            upload_chunks: record.features.upload_chunks,
            heap_frame_bytes_requested: record.features.heap_frame_bytes_requested,
            heap_pages_32k: record.features.heap_pages_32k,
            ro_account_count: record.features.ro_account_count,
            rw_account_count: record.features.rw_account_count,
            account_data_bytes_read: record.features.account_data_bytes_read,
            account_data_bytes_written: record.features.account_data_bytes_written,
            field_add_sub_ops: record.features.field_add_sub_ops,
            field_mul_ops: record.features.field_mul_ops,
            field_inv_ops: record.features.field_inv_ops,
            extension_mul_ops: record.features.extension_mul_ops,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_json<T: Serialize>(path: &Path, value: &T) -> Result<()> {
    fs::write(path, serde_json::to_vec_pretty(value)?)?;
    Ok(())
}

fn write_circle_sweep(
    results_dir: &Path,
    monolithic_model: &svm_cost_model::FittedCostModel,
    verification_core_model: &svm_cost_model::FittedCostModel,
    transport_model: &svm_cost_model::FittedCostModel,
    limits: &SvmLimits,
) -> Result<Vec<ProfileSweepRecord>> {
    let mut records = Vec::new();
    for proof_bytes in [4_608_u64, 5_120, 5_632, 6_144] {
        for chunk_size in [448_u64, 512, 640] {
            for query_count in [3_u64, 4, 5, 6] {
                let scenario_name =
                    format!("circle-p{}-c{}-q{}", proof_bytes, chunk_size, query_count);
                let profile = hypothetical_circle_profile(
                    &scenario_name,
                    proof_bytes,
                    chunk_size,
                    query_count,
                );
                let score = score_profile_with_components(
                    monolithic_model,
                    Some(verification_core_model),
                    Some(transport_model),
                    limits,
                    &profile,
                )?;
                records.push(ProfileSweepRecord {
                    scenario_name,
                    protocol_family: "Circle".to_string(),
                    proof_bytes,
                    chunk_size,
                    query_count,
                    predicted_cu: score.predicted_cu,
                    lower_cu: score.lower_cu,
                    upper_cu: score.upper_cu,
                    verification_core_cu: score.verification_core_cu,
                    transport_overhead_cu: score.transport_overhead_cu,
                    component_predicted_cu: score.component_predicted_cu,
                    component_gap_vs_monolithic_cu: score.component_gap_vs_monolithic_cu,
                    cu_budget_fraction: score.cu_budget_fraction,
                    proof_transport_pressure: score.proof_transport_pressure,
                    feasible: score.feasible,
                    feasibility_reasons: score.feasibility_reasons,
                    query_soundness: score.query_soundness,
                    notes: profile.notes,
                });
            }
        }
    }

    write_json(&results_dir.join("circle_sweep.json"), &records)?;
    write_profile_sweep_csv(&results_dir.join("circle_sweep.csv"), &records)?;
    Ok(records)
}

fn write_profile_sweep_csv(path: &Path, records: &[ProfileSweepRecord]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    writer.write_record([
        "scenario_name",
        "protocol_family",
        "proof_bytes",
        "chunk_size",
        "query_count",
        "predicted_cu",
        "lower_cu",
        "upper_cu",
        "verification_core_cu",
        "transport_overhead_cu",
        "component_predicted_cu",
        "component_gap_vs_monolithic_cu",
        "cu_budget_fraction",
        "proof_transport_pressure",
        "feasible",
        "feasibility_reasons",
        "notes",
    ])?;
    for record in records {
        writer.write_record([
            record.scenario_name.clone(),
            record.protocol_family.clone(),
            record.proof_bytes.to_string(),
            record.chunk_size.to_string(),
            record.query_count.to_string(),
            format!("{:.6}", record.predicted_cu),
            record
                .lower_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .upper_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .verification_core_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .transport_overhead_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .component_predicted_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .component_gap_vs_monolithic_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            format!("{:.6}", record.cu_budget_fraction),
            format!("{:.6}", record.proof_transport_pressure),
            record.feasible.to_string(),
            record.feasibility_reasons.join(" | "),
            record.notes.join(" | "),
        ])?;
    }
    writer.flush()?;
    Ok(())
}

fn transport_features(upload_bytes: u64, chunk_size: u64) -> TransportCostFeatures {
    let upload_chunks = upload_bytes.div_ceil(chunk_size.max(1));
    TransportCostFeatures {
        sha_calls: upload_chunks,
        sha_bytes: upload_bytes + 32 * upload_chunks,
        upload_bytes,
        upload_chunks,
    }
}

fn parameter_choice(
    name: &str,
    value: impl Into<String>,
    rationale: &str,
    sources: &[&str],
) -> ProfileParameterChoice {
    ProfileParameterChoice {
        name: name.to_string(),
        value: value.into(),
        rationale: rationale.to_string(),
        sources: sources.iter().map(|value| (*value).to_string()).collect(),
    }
}

fn fri_query_soundness_model(
    query_count: u64,
    log_blowup: u32,
    query_proof_of_work_bits: u32,
    target_bits: f64,
    sources: &[&str],
    notes: &[&str],
) -> QuerySoundnessModel {
    QuerySoundnessModel::Fri {
        query_count,
        log_blowup,
        query_proof_of_work_bits,
        target_bits,
        sources: sources.iter().map(|value| (*value).to_string()).collect(),
        notes: notes.iter().map(|value| (*value).to_string()).collect(),
    }
}

fn whir_query_soundness_model(
    query_count: u64,
    log_inv_rate: u32,
    pow_bits: u32,
    target_bits: f64,
    sources: &[&str],
    notes: &[&str],
) -> QuerySoundnessModel {
    QuerySoundnessModel::Whir {
        query_count,
        log_inv_rate,
        pow_bits,
        target_bits,
        sources: sources.iter().map(|value| (*value).to_string()).collect(),
        notes: notes.iter().map(|value| (*value).to_string()).collect(),
    }
}

fn default_protocol_log_rate(protocol: SpendProtocol) -> u32 {
    match protocol {
        SpendProtocol::Circle | SpendProtocol::Whir => 4,
    }
}

fn adjust_u64_by_rate(
    base: u64,
    log_rate: u32,
    default_log_rate: u32,
    step: u64,
    floor: u64,
) -> u64 {
    if log_rate >= default_log_rate {
        base + step * (log_rate - default_log_rate) as u64
    } else {
        base.saturating_sub(step * (default_log_rate - log_rate) as u64)
            .max(floor)
    }
}

fn grinding_witness_checks(protocol: SpendProtocol, grinding_bits: u32) -> u64 {
    if grinding_bits == 0 {
        return 0;
    }
    match protocol {
        SpendProtocol::Circle => 1,
        SpendProtocol::Whir => 3,
    }
}

fn ceil_log2(value: u64) -> u32 {
    if value <= 1 {
        0
    } else {
        u64::BITS - (value - 1).leading_zeros()
    }
}

fn default_spend_statement() -> SpendStatementShape {
    SpendStatementShape {
        spends: 2,
        outputs: 2,
        note_tree_depth: 32,
        note_openings_per_spend: 1,
        nullifier_hashes_per_spend: 1,
        note_commitments_per_output: 1,
        amount_range_checks_64: 4,
        ownership_checks: 2,
        balance_constraints: 8,
        lookup_arguments: 3,
    }
}

fn default_spend_arithmetization() -> SpendArithmetizationAssumptions {
    SpendArithmetizationAssumptions {
        merkle_rows_per_level: 12,
        nullifier_hash_rows: 512,
        note_commitment_rows: 512,
        range_check_rows: 256,
        ownership_rows: 384,
        balance_rows: 48,
        lookup_rows: 320,
        misc_rows: 768,
        transition_constraint_divisions: 1,
        boundary_constraint_groups: 0,
    }
}

fn spend_boundary_layout(statement: &SpendStatementShape) -> SpendBoundaryLayout {
    let lookup_groups = u64::from(statement.lookup_arguments > 0);
    let total_groups = 1 + 1 + lookup_groups + lookup_groups;
    SpendBoundaryLayout {
        main_trace_initial_groups: 1,
        main_trace_terminal_groups: 1,
        lookup_accumulator_initial_groups: lookup_groups,
        lookup_accumulator_terminal_groups: lookup_groups,
        total_groups,
        notes: vec![
            "The concrete spend AIR layout assumes one shared initial boundary group for public-input state and one shared terminal boundary group for public-output state.".to_string(),
            "Lookup arguments are modeled with accumulator columns that share a common initial step and a common terminal step, so lookup boundary groups scale with presence of lookup arguments rather than one-for-one with argument count.".to_string(),
        ],
    }
}

fn spend_verifier_inversion_layout(protocol: SpendProtocol) -> SpendVerifierInversionLayout {
    match protocol {
        SpendProtocol::Circle => {
            let mut low_degree_batch_components = BTreeMap::new();
            low_degree_batch_components.insert("opening_denominator_batches".to_string(), 1);
            low_degree_batch_components.insert("selector_denominator_batches".to_string(), 1);
            let low_degree_batch_inversions = low_degree_batch_components.values().sum();
            SpendVerifierInversionLayout {
                deep_batch_inversions: 1,
                low_degree_batch_components,
                low_degree_batch_inversions,
                notes: vec![
                    "Circle's DEEP quotient construction uses one batched denominator inversion in the official Plonky3 implementation.".to_string(),
                    "The low-degree side keeps one batched opening-denominator inversion plus one selector-denominator batch, derived from the official Circle/FRI verifier-support code rather than a generic per-round placeholder.".to_string(),
                ],
            }
        }
        SpendProtocol::Whir => SpendVerifierInversionLayout {
            deep_batch_inversions: 0,
            low_degree_batch_components: BTreeMap::new(),
            low_degree_batch_inversions: 0,
            notes: vec![
                "The current spend-screen WHIR inversion layout is grounded in the official WHIR/Plonky3 code paths inspected here, which do not expose a DEEP-style or low-degree batched inversion stage analogous to the Winterfell verifier.".to_string(),
                "This remains a protocol-layout assumption for screening, but it is no longer a generic 'one round equals one inversion batch' placeholder.".to_string(),
            ],
        },
    }
}

fn spend_verifier_assumptions(
    protocol: SpendProtocol,
    query_count: u64,
    log_rate: u32,
    grinding_bits: u32,
) -> SpendVerifierAssumptions {
    let default_log_rate = default_protocol_log_rate(protocol);
    let pow_checks = grinding_witness_checks(protocol, grinding_bits);
    match protocol {
        SpendProtocol::Circle => {
            let reciprocal_rate = 1_u64 << log_rate;
            SpendVerifierAssumptions {
                protocol_family: "Circle".to_string(),
                query_count,
                proof_query_semantics: "Literal absolute proof-oracle queries in the screening model. Each unit of q contributes one proof-side Merkle authentication path; q is not a round count and not multiplied by hidden batching.".to_string(),
                security_interpretation: format!(
                    "Query soundness is assessed with FRI-style lower and upper bounds at blowup {reciprocal_rate}: a proven rate^(q/2) lower bound and a conjectured ethSTARK-style rate^q upper bound, plus {grinding_bits} query-grinding bits."
                ),
                proof_merkle_depth: adjust_u64_by_rate(10, log_rate, default_log_rate, 1, 6),
                base_proof_bytes: adjust_u64_by_rate(2_752, log_rate, default_log_rate, 96, 2_176)
                    + 8 * pow_checks,
                proof_bytes_per_log2_rows: 128,
                proof_bytes_per_query: adjust_u64_by_rate(288, log_rate, default_log_rate, 32, 160),
                proof_bytes_per_lookup_argument: 72,
                proof_bytes_per_hash_gadget: 88,
                proof_segment_bytes: 512,
                sha_calls_base: 18 + pow_checks,
                sha_bytes_base: 2_048 + 64 * pow_checks,
                ro_account_count: 6,
                rw_account_count: 1,
                account_read_base_bytes: 4_608,
                account_read_per_merkle_path_bytes: 1_024,
                account_read_per_output_bytes: 512,
                account_write_bytes: 256,
                field_add_base: 1_536,
                field_add_per_hash_gadget: 128,
                field_add_per_lookup_argument: 192,
                field_add_per_log2_rows: 16,
                field_mul_base: 224,
                field_mul_per_query: 96,
                field_mul_per_hash_gadget: 24,
                field_mul_per_lookup_argument: 40,
                field_mul_per_log2_rows: 24,
                field_inv_base: 4,
                field_inv_per_lookup_argument: 2,
                field_inv_per_query: 1,
                deep_batch_inversions: 1,
                low_degree_batch_inversions: 2,
                extension_mul_base: 16,
                extension_mul_per_query: 20,
                extension_mul_per_lookup_argument: 12,
                extension_mul_per_log2_rows: 4,
                heap_small_bytes: 98_304,
                heap_large_bytes: 131_072,
                heap_large_log2_rows_threshold: 13,
            }
        }
        SpendProtocol::Whir => {
            let reciprocal_rate = 1_u64 << log_rate;
            SpendVerifierAssumptions {
                protocol_family: "WHIR".to_string(),
                query_count,
                proof_query_semantics: "Literal absolute proof queries in the screening model. q is an explicit verifier-query counter, not a query-round counter and not an effective-query estimate after hidden batching.".to_string(),
                security_interpretation: format!(
                    "Query soundness is assessed with the official WHIR query-term models at inverse rate {reciprocal_rate}: Johnson-bound as the lower bound and capacity-bound as the upper bound, plus {grinding_bits} PoW bits."
                ),
                proof_merkle_depth: adjust_u64_by_rate(8, log_rate, default_log_rate, 1, 4),
                base_proof_bytes: adjust_u64_by_rate(2_432, log_rate, default_log_rate, 80, 1_920)
                    + 8 * pow_checks,
                proof_bytes_per_log2_rows: 112,
                proof_bytes_per_query: adjust_u64_by_rate(248, log_rate, default_log_rate, 32, 136),
                proof_bytes_per_lookup_argument: 56,
                proof_bytes_per_hash_gadget: 72,
                proof_segment_bytes: 512,
                sha_calls_base: 14 + pow_checks,
                sha_bytes_base: 1_536 + 64 * pow_checks,
                ro_account_count: 6,
                rw_account_count: 1,
                account_read_base_bytes: 4_096,
                account_read_per_merkle_path_bytes: 1_024,
                account_read_per_output_bytes: 512,
                account_write_bytes: 256,
                field_add_base: 1_344,
                field_add_per_hash_gadget: 112,
                field_add_per_lookup_argument: 160,
                field_add_per_log2_rows: 16,
                field_mul_base: 160,
                field_mul_per_query: 88,
                field_mul_per_hash_gadget: 20,
                field_mul_per_lookup_argument: 32,
                field_mul_per_log2_rows: 20,
                field_inv_base: 4,
                field_inv_per_lookup_argument: 2,
                field_inv_per_query: 1,
                deep_batch_inversions: 1,
                low_degree_batch_inversions: 1,
                extension_mul_base: 24,
                extension_mul_per_query: 16,
                extension_mul_per_lookup_argument: 8,
                extension_mul_per_log2_rows: 2,
                heap_small_bytes: 98_304,
                heap_large_bytes: 131_072,
                heap_large_log2_rows_threshold: 13,
            }
        }
    }
}

fn structured_spend_profile_with_tuning(
    protocol: SpendProtocol,
    name: &str,
    query_count: u64,
    chunk_size: u64,
    proof_bytes_override: Option<u64>,
    log_rate: u32,
    grinding_bits: u32,
) -> StructuredSpendProfile {
    let statement = default_spend_statement();
    let boundary_layout = spend_boundary_layout(&statement);
    let verifier_inversion_layout = spend_verifier_inversion_layout(protocol);
    let mut arithmetization = default_spend_arithmetization();
    arithmetization.boundary_constraint_groups = boundary_layout.total_groups;
    let mut verifier = spend_verifier_assumptions(protocol, query_count, log_rate, grinding_bits);
    verifier.deep_batch_inversions = verifier_inversion_layout.deep_batch_inversions;
    verifier.low_degree_batch_inversions = verifier_inversion_layout.low_degree_batch_inversions;

    let application_merkle_paths = statement.spends * statement.note_openings_per_spend;
    let application_merkle_levels = application_merkle_paths * statement.note_tree_depth;
    let application_hash_gadgets = statement.spends * statement.nullifier_hashes_per_spend
        + statement.outputs * statement.note_commitments_per_output;

    let mut row_breakdown = BTreeMap::new();
    row_breakdown.insert(
        "application_merkle_rows".to_string(),
        application_merkle_levels * arithmetization.merkle_rows_per_level,
    );
    row_breakdown.insert(
        "nullifier_hash_rows".to_string(),
        statement.spends
            * statement.nullifier_hashes_per_spend
            * arithmetization.nullifier_hash_rows,
    );
    row_breakdown.insert(
        "note_commitment_rows".to_string(),
        statement.outputs
            * statement.note_commitments_per_output
            * arithmetization.note_commitment_rows,
    );
    row_breakdown.insert(
        "range_check_rows".to_string(),
        statement.amount_range_checks_64 * arithmetization.range_check_rows,
    );
    row_breakdown.insert(
        "ownership_rows".to_string(),
        statement.ownership_checks * arithmetization.ownership_rows,
    );
    row_breakdown.insert(
        "balance_rows".to_string(),
        statement.balance_constraints * arithmetization.balance_rows,
    );
    row_breakdown.insert(
        "lookup_rows".to_string(),
        statement.lookup_arguments * arithmetization.lookup_rows,
    );
    row_breakdown.insert("misc_rows".to_string(), arithmetization.misc_rows);
    let total_rows = row_breakdown.values().copied().sum::<u64>();
    let evaluation_domain_log2 = ceil_log2(total_rows.max(1));

    let derived_proof_bytes = verifier.base_proof_bytes
        + verifier.proof_bytes_per_log2_rows * evaluation_domain_log2 as u64
        + verifier.proof_bytes_per_query * query_count
        + verifier.proof_bytes_per_lookup_argument * statement.lookup_arguments
        + verifier.proof_bytes_per_hash_gadget * application_hash_gadgets;
    let proof_bytes = proof_bytes_override.unwrap_or(derived_proof_bytes);
    let transport = transport_features(proof_bytes, chunk_size);

    let proof_merkle_levels = query_count * verifier.proof_merkle_depth;
    let total_merkle_levels = proof_merkle_levels + application_merkle_levels;
    let heap_frame_bytes_requested =
        if evaluation_domain_log2 > verifier.heap_large_log2_rows_threshold {
            verifier.heap_large_bytes
        } else {
            verifier.heap_small_bytes
        };

    let field_add_sub_ops = verifier.field_add_base
        + verifier.field_add_per_hash_gadget * application_hash_gadgets
        + verifier.field_add_per_lookup_argument * statement.lookup_arguments
        + verifier.field_add_per_log2_rows * evaluation_domain_log2 as u64
        + 32 * statement.amount_range_checks_64
        + 48 * statement.ownership_checks
        + 16 * statement.balance_constraints;
    let field_mul_ops = verifier.field_mul_base
        + verifier.field_mul_per_query * query_count
        + verifier.field_mul_per_hash_gadget * application_hash_gadgets
        + verifier.field_mul_per_lookup_argument * statement.lookup_arguments
        + verifier.field_mul_per_log2_rows * evaluation_domain_log2 as u64
        + 24 * statement.amount_range_checks_64
        + 48 * statement.ownership_checks;
    let prior_query_scaled_field_inv_ops = verifier.field_inv_base
        + verifier.field_inv_per_lookup_argument * statement.lookup_arguments
        + verifier.field_inv_per_query * query_count;
    let field_inv_breakdown = SpendFieldInvStructuralBreakdown {
        prior_query_scaled_proxy: prior_query_scaled_field_inv_ops,
        transition_constraint_divisions: arithmetization.transition_constraint_divisions,
        boundary_constraint_group_divisions: arithmetization.boundary_constraint_groups,
        deep_batch_inversions: verifier.deep_batch_inversions,
        low_degree_batch_inversions: verifier.low_degree_batch_inversions,
        estimated_total: arithmetization.transition_constraint_divisions
            + arithmetization.boundary_constraint_groups
            + verifier.deep_batch_inversions
            + verifier.low_degree_batch_inversions,
        notes: vec![
            "Spend-screen inversion counts now follow verifier structure rather than query scaling: AIR-side divisor divisions plus protocol-side batch inversions.".to_string(),
            "Boundary constraint groups are now derived from an explicit spend AIR layout: shared initial/terminal main-trace groups plus shared lookup-accumulator start/end groups.".to_string(),
            "Low-degree batch inversion counts now come from named protocol stages in the inspected Circle and WHIR codepaths rather than a generic per-round placeholder.".to_string(),
        ],
    };
    let field_inv_ops = field_inv_breakdown.estimated_total;
    let extension_mul_ops = verifier.extension_mul_base
        + verifier.extension_mul_per_query * query_count
        + verifier.extension_mul_per_lookup_argument * statement.lookup_arguments
        + verifier.extension_mul_per_log2_rows * evaluation_domain_log2 as u64;

    let profile = ProfileScoreInput {
        name: name.to_string(),
        protocol_family: Some(verifier.protocol_family.clone()),
        features: CostFeatures {
            sha_calls: total_merkle_levels + verifier.sha_calls_base + transport.sha_calls,
            sha_bytes: total_merkle_levels * 64 + proof_bytes + verifier.sha_bytes_base + transport.sha_bytes,
            merkle_paths: query_count + application_merkle_paths,
            merkle_levels: total_merkle_levels,
            proof_bytes,
            proof_segments: proof_bytes.div_ceil(verifier.proof_segment_bytes).max(9),
            upload_bytes: proof_bytes,
            upload_chunks: transport.upload_chunks,
            heap_frame_bytes_requested,
            heap_pages_32k: heap_frame_bytes_requested.div_ceil(32 * 1024),
            ro_account_count: verifier.ro_account_count,
            rw_account_count: verifier.rw_account_count,
            account_data_bytes_read: verifier.account_read_base_bytes
                + application_merkle_paths * verifier.account_read_per_merkle_path_bytes
                + statement.outputs * verifier.account_read_per_output_bytes,
            account_data_bytes_written: verifier.account_write_bytes,
            field_add_sub_ops,
            field_mul_ops,
            field_inv_ops,
            extension_mul_ops,
        },
        transport,
        parameter_choices: vec![
            parameter_choice(
                "query_count",
                query_count.to_string(),
                &verifier.proof_query_semantics,
                match protocol {
                    SpendProtocol::Circle => &["https://eprint.iacr.org/2024/278", "https://eprint.iacr.org/2024/1161"],
                    SpendProtocol::Whir => &["https://eprint.iacr.org/2024/1586"],
                },
            ),
            parameter_choice(
                "query_security_status",
                "query_soundness_assessed",
                &verifier.security_interpretation,
                match protocol {
                    SpendProtocol::Circle => &["https://eprint.iacr.org/2024/278", "https://eprint.iacr.org/2024/1161"],
                    SpendProtocol::Whir => &["https://eprint.iacr.org/2024/1586"],
                },
            ),
            parameter_choice(
                match protocol {
                    SpendProtocol::Circle => "log_blowup",
                    SpendProtocol::Whir => "log_inv_rate",
                },
                log_rate.to_string(),
                match protocol {
                    SpendProtocol::Circle => {
                        "Sweeps the Circle/FRI blowup factor jointly with q and grinding; higher values improve soundness but deepen proof authentication paths."
                    }
                    SpendProtocol::Whir => {
                        "Sweeps the WHIR starting inverse code rate jointly with q and PoW; higher values improve query soundness but enlarge proof paths."
                    }
                },
                match protocol {
                    SpendProtocol::Circle => &[
                        "https://eprint.iacr.org/2020/654",
                        "https://eprint.iacr.org/2021/582",
                    ],
                    SpendProtocol::Whir => &[
                        "https://eprint.iacr.org/2024/1586",
                        "https://eprint.iacr.org/2025/2055",
                    ],
                },
            ),
            parameter_choice(
                match protocol {
                    SpendProtocol::Circle => "query_proof_of_work_bits",
                    SpendProtocol::Whir => "pow_bits",
                },
                grinding_bits.to_string(),
                "Verifier-side grinding is modeled as a fixed-size witness check when enabled; difficulty bits mainly move security, not verifier work.",
                match protocol {
                    SpendProtocol::Circle => &[
                        "https://github.com/Plonky3/Plonky3/blob/main/fri/src/config.rs",
                        "https://github.com/Plonky3/Plonky3/blob/main/fri/src/verifier.rs",
                    ],
                    SpendProtocol::Whir => &[
                        "https://github.com/Plonky3/Plonky3/blob/main/whir/src/parameters/whir.rs",
                        "https://github.com/Plonky3/Plonky3/blob/main/whir/src/sumcheck/data.rs",
                    ],
                },
            ),
            parameter_choice(
                "chunk_size_bytes",
                chunk_size.to_string(),
                "Upload chunking remains an explicit transport lever under the Solana transaction byte cap.",
                &[],
            ),
            parameter_choice(
                "proof_bytes",
                proof_bytes.to_string(),
                if proof_bytes_override.is_some() {
                    "Proof bytes were overridden after structured arithmetization to sweep transport sensitivity around the derived baseline."
                } else {
                    "Proof bytes were derived from the structured spend arithmetization, query count, and protocol-specific transcript assumptions."
                },
                match protocol {
                    SpendProtocol::Circle => &["https://eprint.iacr.org/2024/278"],
                    SpendProtocol::Whir => &["https://eprint.iacr.org/2024/1586"],
                },
            ),
            parameter_choice(
                "evaluation_domain_log2",
                evaluation_domain_log2.to_string(),
                "Derived from the explicit spend arithmetization row budget rather than a hand-picked verifier proxy count.",
                &[],
            ),
        ],
        references: match protocol {
            SpendProtocol::Circle => vec![
                "https://eprint.iacr.org/2024/278".to_string(),
                "https://eprint.iacr.org/2024/1161".to_string(),
                "https://eprint.iacr.org/2024/1810".to_string(),
                "https://eprint.iacr.org/2020/654".to_string(),
                "https://eprint.iacr.org/2021/582".to_string(),
            ],
            SpendProtocol::Whir => vec![
                "https://eprint.iacr.org/2024/1586".to_string(),
                "https://eprint.iacr.org/2024/1810".to_string(),
                "https://eprint.iacr.org/2025/2055".to_string(),
            ],
        },
        query_soundness_model: Some(match protocol {
            SpendProtocol::Circle => fri_query_soundness_model(
                query_count,
                log_rate,
                grinding_bits,
                128.0,
                &[
                    "https://eprint.iacr.org/2020/654",
                    "https://eprint.iacr.org/2021/582",
                    "https://github.com/Plonky3/Plonky3/blob/main/fri/src/config.rs",
                    "https://github.com/Plonky3/Plonky3/blob/main/fri/src/prover.rs",
                ],
                &[
                    "Circle spend scoring treats q as the literal FRI query count.",
                ],
            ),
            SpendProtocol::Whir => whir_query_soundness_model(
                query_count,
                log_rate,
                grinding_bits,
                128.0,
                &[
                    "https://eprint.iacr.org/2024/1586",
                    "https://eprint.iacr.org/2025/2055",
                    "https://github.com/Plonky3/Plonky3/blob/main/whir/src/parameters/soundness.rs",
                ],
                &[
                    "WHIR spend scoring treats q as the explicit proximity-query count.",
                ],
            ),
        }),
        notes: {
            let mut notes = vec![
                format!(
                    "Structured spend-screen profile derived from explicit statement and arithmetization assumptions; total_rows={}, log2_rows={}.",
                    total_rows, evaluation_domain_log2
                ),
                verifier.proof_query_semantics.clone(),
                verifier.security_interpretation.clone(),
                format!(
                    "This tuned screen uses {}={} and grinding_bits={}.",
                    match protocol {
                        SpendProtocol::Circle => "log_blowup",
                        SpendProtocol::Whir => "log_inv_rate",
                    },
                    log_rate,
                    grinding_bits,
                ),
                format!(
                    "field_inv_ops uses a structural proxy of {} instead of the earlier query-scaled proxy of {}.",
                    field_inv_ops, prior_query_scaled_field_inv_ops
                ),
            ];
            if let Some(override_bytes) = proof_bytes_override {
                notes.push(format!(
                    "Derived proof_bytes baseline was {derived_proof_bytes}; this profile overrides it to {override_bytes} for transport sensitivity."
                ));
            }
            notes
        },
    };

    StructuredSpendProfile {
        projection: StructuredSpendProjection {
            profile_name: name.to_string(),
            protocol_family: verifier.protocol_family.clone(),
            statement,
            arithmetization,
            verifier,
            boundary_layout,
            verifier_inversion_layout,
            field_inv_breakdown,
            row_breakdown,
            total_rows,
            evaluation_domain_log2,
            application_merkle_paths,
            application_merkle_levels,
            application_hash_gadgets,
            derived_profile: profile.clone(),
            notes: vec![
                "This structured spend projection makes q semantics explicit: q is a literal absolute verifier-query count in the current model.".to_string(),
                "This projection now attaches a protocol-backed lower/upper query-soundness estimate to the same literal q parameter.".to_string(),
                format!(
                    "The spend-screen field_inv_ops proxy was corrected from the earlier query-scaled estimate of {} to the structural estimate of {}.",
                    prior_query_scaled_field_inv_ops, field_inv_ops
                ),
            ],
        },
        profile,
    }
}

fn structured_spend_profile(
    protocol: SpendProtocol,
    name: &str,
    query_count: u64,
    chunk_size: u64,
    proof_bytes_override: Option<u64>,
) -> StructuredSpendProfile {
    structured_spend_profile_with_tuning(
        protocol,
        name,
        query_count,
        chunk_size,
        proof_bytes_override,
        default_protocol_log_rate(protocol),
        0,
    )
}

fn hypothetical_fri_profile() -> ProfileScoreInput {
    let proof_bytes = 9_216_u64;
    let chunk_size = 576_u64;
    let query_count = 6_u64;
    let merkle_depth = 14_u64;
    let transport = transport_features(proof_bytes, chunk_size);
    let merkle_levels = query_count * merkle_depth;
    let heap_frame_bytes_requested = 131_072_u64;

    ProfileScoreInput {
        name: "hypothetical-fri-profile".to_string(),
        protocol_family: Some("FRI".to_string()),
        features: CostFeatures {
            sha_calls: merkle_levels + 18 + transport.sha_calls,
            sha_bytes: merkle_levels * 64 + proof_bytes + 1_536 + transport.sha_bytes,
            merkle_paths: query_count,
            merkle_levels,
            proof_bytes,
            proof_segments: 12,
            upload_bytes: proof_bytes,
            upload_chunks: transport.upload_chunks,
            heap_frame_bytes_requested,
            heap_pages_32k: heap_frame_bytes_requested.div_ceil(32 * 1024),
            ro_account_count: 5,
            rw_account_count: 2,
            account_data_bytes_read: 6_144,
            account_data_bytes_written: 256,
            field_add_sub_ops: 6_144,
            field_mul_ops: 1_536,
            field_inv_ops: 96,
            extension_mul_ops: 192,
        },
        transport,
        parameter_choices: vec![
            parameter_choice(
                "query_count",
                query_count.to_string(),
                "Keeps the profile in the conservative, high-query regime used for a first-pass infeasibility screen rather than tuning down soundness to fit budget.",
                &["https://eprint.iacr.org/2024/1810"],
            ),
            parameter_choice(
                "merkle_depth",
                merkle_depth.to_string(),
                "Represents a deep authentication surface consistent with FRI-style query pressure under transparent settings.",
                &["https://eprint.iacr.org/2024/1810"],
            ),
            parameter_choice(
                "chunk_size_bytes",
                chunk_size.to_string(),
                "Leaves headroom under Solana's transaction byte cap once instruction and account metadata are included.",
                &[],
            ),
        ],
        references: vec!["https://eprint.iacr.org/2024/1810".to_string()],
        query_soundness_model: Some(fri_query_soundness_model(
            query_count,
            4,
            0,
            128.0,
            &[
                "https://eprint.iacr.org/2020/654",
                "https://eprint.iacr.org/2021/582",
                "https://github.com/Plonky3/Plonky3/blob/main/fri/src/prover.rs",
            ],
            &[
                "The hypothetical FRI profile uses q as a literal query count at blowup 16.",
            ],
        )),
        notes: vec![
            "Exploratory FRI-shaped profile for Phase 1 scoring; not tied to a production verifier implementation.".to_string(),
            "Used as an upper-pressure comparison point, not a claim about an optimized FRI verifier.".to_string(),
        ],
    }
}

fn hypothetical_circle_profile(
    name: &str,
    proof_bytes: u64,
    chunk_size: u64,
    query_count: u64,
) -> ProfileScoreInput {
    let merkle_depth = 10_u64;
    let merkle_levels = query_count * merkle_depth;
    let transport = transport_features(proof_bytes, chunk_size);
    let heap_frame_bytes_requested = if proof_bytes >= 6_144 || query_count >= 6 {
        131_072_u64
    } else {
        98_304_u64
    };
    let proof_segments = proof_bytes.div_ceil(512).max(8);
    let extra_bytes = proof_bytes.saturating_sub(5_120);

    ProfileScoreInput {
        name: name.to_string(),
        protocol_family: Some("Circle".to_string()),
        features: CostFeatures {
            sha_calls: merkle_levels + 12 + transport.sha_calls,
            sha_bytes: merkle_levels * 64 + proof_bytes + 640 + transport.sha_bytes,
            merkle_paths: query_count,
            merkle_levels,
            proof_bytes,
            proof_segments,
            upload_bytes: proof_bytes,
            upload_chunks: transport.upload_chunks,
            heap_frame_bytes_requested,
            heap_pages_32k: heap_frame_bytes_requested.div_ceil(32 * 1024),
            ro_account_count: 4,
            rw_account_count: 1,
            account_data_bytes_read: 4_096 + query_count.saturating_sub(4) * 512,
            account_data_bytes_written: 128,
            field_add_sub_ops: 768 * query_count + extra_bytes / 8,
            field_mul_ops: 256 * query_count + extra_bytes / 16,
            field_inv_ops: 12 * query_count,
            extension_mul_ops: 24 * query_count + extra_bytes / 64,
        },
        transport,
        parameter_choices: vec![
            parameter_choice(
                "query_count",
                query_count.to_string(),
                "Treats query count as the primary soundness lever in the Circle family and exposes it directly in the sweep.",
                &["https://eprint.iacr.org/2024/278", "https://eprint.iacr.org/2024/1810"],
            ),
            parameter_choice(
                "chunk_size_bytes",
                chunk_size.to_string(),
                "Chosen to stay comfortably below the Solana transaction byte cap after non-payload overhead.",
                &[],
            ),
            parameter_choice(
                "proof_bytes",
                proof_bytes.to_string(),
                "Swept around the base 5,120-byte profile to test transport and parse sensitivity without changing the overall statement family.",
                &["https://eprint.iacr.org/2024/278"],
            ),
        ],
        references: vec![
            "https://eprint.iacr.org/2024/278".to_string(),
            "https://eprint.iacr.org/2024/1810".to_string(),
            "https://eprint.iacr.org/2024/1635".to_string(),
        ],
        query_soundness_model: Some(fri_query_soundness_model(
            query_count,
            4,
            0,
            128.0,
            &[
                "https://eprint.iacr.org/2020/654",
                "https://eprint.iacr.org/2021/582",
                "https://github.com/Plonky3/Plonky3/blob/main/fri/src/config.rs",
                "https://github.com/Plonky3/Plonky3/blob/main/fri/src/prover.rs",
            ],
            &[
                "The hypothetical Circle profile interprets q as the literal FRI query count behind the Circle PCS query phase.",
            ],
        )),
        notes: vec![
            format!(
                "Exploratory Circle profile with proof_bytes={}, chunk_size={}, query_count={}.",
                proof_bytes, chunk_size, query_count
            ),
            "Not security-certified; intended for relative SVM pressure comparison only.".to_string(),
        ],
    }
}

fn hypothetical_whir_profile() -> ProfileScoreInput {
    let proof_bytes = 4_096_u64;
    let chunk_size = 512_u64;
    let query_count = 3_u64;
    let merkle_depth = 8_u64;
    let merkle_levels = query_count * merkle_depth;
    let transport = transport_features(proof_bytes, chunk_size);
    let heap_frame_bytes_requested = 98_304_u64;

    ProfileScoreInput {
        name: "hypothetical-whir-profile".to_string(),
        protocol_family: Some("WHIR".to_string()),
        features: CostFeatures {
            sha_calls: merkle_levels + 10 + transport.sha_calls,
            sha_bytes: merkle_levels * 64 + proof_bytes + 768 + transport.sha_bytes,
            merkle_paths: query_count,
            merkle_levels,
            proof_bytes,
            proof_segments: 9,
            upload_bytes: proof_bytes,
            upload_chunks: transport.upload_chunks,
            heap_frame_bytes_requested,
            heap_pages_32k: heap_frame_bytes_requested.div_ceil(32 * 1024),
            ro_account_count: 4,
            rw_account_count: 1,
            account_data_bytes_read: 3_072,
            account_data_bytes_written: 128,
            field_add_sub_ops: 2_048,
            field_mul_ops: 896,
            field_inv_ops: 32,
            extension_mul_ops: 72,
        },
        transport,
        parameter_choices: vec![
            parameter_choice(
                "query_count",
                query_count.to_string(),
                "WHIR is modeled with fewer queries than the FRI baseline to reflect its intended verifier-side savings.",
                &["https://eprint.iacr.org/2024/1586", "https://eprint.iacr.org/2024/1810"],
            ),
            parameter_choice(
                "merkle_depth",
                merkle_depth.to_string(),
                "Keeps the Merkle surface shallower than the FRI baseline while preserving a transparent commitment shape.",
                &["https://eprint.iacr.org/2024/1586"],
            ),
            parameter_choice(
                "chunk_size_bytes",
                chunk_size.to_string(),
                "Matches the existing 512-byte upload-friendly shape used elsewhere in Phase 1.",
                &[],
            ),
        ],
        references: vec![
            "https://eprint.iacr.org/2024/1586".to_string(),
            "https://eprint.iacr.org/2024/1810".to_string(),
        ],
        query_soundness_model: Some(whir_query_soundness_model(
            query_count,
            4,
            0,
            128.0,
            &[
                "https://eprint.iacr.org/2024/1586",
                "https://eprint.iacr.org/2025/2055",
                "https://github.com/Plonky3/Plonky3/blob/main/whir/src/parameters/soundness.rs",
            ],
            &[
                "The hypothetical WHIR profile interprets q as the explicit proximity-query count at inverse rate 16.",
            ],
        )),
        notes: vec![
            "Exploratory WHIR-shaped profile for direct comparison against the Circle and FRI examples.".to_string(),
            "Parameter values are intended for SVM cost screening, not as a definitive WHIR parameterization.".to_string(),
        ],
    }
}

fn spend_circle_profile() -> ProfileScoreInput {
    structured_spend_profile(
        SpendProtocol::Circle,
        "spend-circle-profile",
        5,
        512,
        Some(6_656),
    )
    .profile
}

fn spend_whir_profile() -> ProfileScoreInput {
    structured_spend_profile(
        SpendProtocol::Whir,
        "spend-whir-profile",
        4,
        512,
        Some(5_632),
    )
    .profile
}

fn write_spend_profiles(
    examples_dir: &Path,
    results_dir: &Path,
    summary: &Phase1Summary,
    limits: &SvmLimits,
) -> Result<Vec<ProfileScoreOutput>> {
    let profiles = vec![spend_circle_profile(), spend_whir_profile()];
    let mut scores = Vec::new();
    for profile in profiles {
        let path = examples_dir.join(format!("{}.yaml", profile.name));
        fs::write(&path, serde_yaml::to_string(&profile)?)?;
        scores.push(score_profile_with_components(
            &summary.model.chosen,
            summary
                .verification_core_model
                .as_ref()
                .map(|value| &value.chosen),
            summary.transport_model.as_ref().map(|value| &value.chosen),
            limits,
            &profile,
        )?);
    }
    write_json(&results_dir.join("spend_profile_scores.json"), &scores)?;
    Ok(scores)
}

fn ensure_selected_feature(model: &mut FittedCostModel, feature: &str) {
    if !model.selected_features.iter().any(|name| name == feature) {
        model.selected_features.push(feature.to_string());
    }
    model.dropped_features.retain(|name| name != feature);
}

fn apply_override(
    model: &mut FittedCostModel,
    feature: &str,
    coefficient: &CoefficientEstimate,
    rationale: &str,
) -> Result<()> {
    let mut coefficient = coefficient.clone();
    coefficient.rationale = rationale.to_string();
    model.coefficients.set(feature, coefficient)?;
    ensure_selected_feature(model, feature);
    Ok(())
}

fn build_constrained_spend_model(
    base: &FittedCostModel,
    orthogonal: &OrthogonalSweepSummary,
    label: &str,
) -> Result<FittedCostModel> {
    let mut constrained = base.clone();
    constrained.method = format!("{}+orthogonal_spend_constraints/{label}", base.method);
    constrained.notes.push(format!(
        "Spend scoring for `{label}` reuses the base fitted model and overrides coefficients only where the orthogonal sweeps provide a clean enough calibration."
    ));
    constrained.notes.push(
        "Model-level error metrics and uncertainty are inherited from the base fit; they were not re-estimated after applying orthogonal coefficient overrides."
            .to_string(),
    );

    if let Some(account_model) = orthogonal
        .account_io_model
        .as_ref()
        .map(|value| &value.chosen)
    {
        for feature in [
            "ro_account_count",
            "rw_account_count",
            "account_data_bytes_read",
            "account_data_bytes_written",
        ] {
            match account_model.coefficients.get(feature) {
                Some(coefficient) if !coefficient.estimate.is_sign_negative() => {
                    apply_override(
                        &mut constrained,
                        feature,
                        coefficient,
                        &format!(
                            "orthogonal account-I/O sweep override from `{}` for spend scoring",
                            account_model.method
                        ),
                    )?;
                    constrained.notes.push(format!(
                        "Applied orthogonal override `{feature}` = {:.6}.",
                        coefficient.estimate
                    ));
                }
                Some(coefficient) => constrained.notes.push(format!(
                    "Skipped orthogonal override `{feature}` because the fitted coefficient was negative ({:.6}).",
                    coefficient.estimate
                )),
                None => constrained.notes.push(format!(
                    "Orthogonal account-I/O sweep did not expose `{feature}` in the chosen model; inherited base coefficient remains in place."
                )),
            }
        }
    } else {
        constrained.notes.push(
            "Orthogonal account-I/O fit was unavailable, so spend scoring kept the inherited account coefficients."
                .to_string(),
        );
    }

    if let Some(field_inv_model) = orthogonal
        .field_inv_model
        .as_ref()
        .map(|value| &value.chosen)
    {
        match field_inv_model.coefficients.get("field_inv_ops") {
            Some(coefficient)
                if !coefficient.estimate.is_sign_negative()
                    && orthogonal.field_inv_failed_runs == 0 =>
            {
                apply_override(
                    &mut constrained,
                    "field_inv_ops",
                    coefficient,
                    &format!(
                        "Winterfell-aligned orthogonal inversion sweep override from `{}` for spend scoring",
                        field_inv_model.method
                    ),
                )?;
                constrained.notes.push(format!(
                    "Applied orthogonal override `field_inv_ops` = {:.6} after a failure-free Winterfell-aligned inversion sweep.",
                    coefficient.estimate
                ));
            }
            Some(coefficient) if !coefficient.estimate.is_sign_negative() => constrained
                .notes
                .push(format!(
                    "Measured orthogonal `field_inv_ops` = {:.6}, but did not apply it to spend scoring because {} inversion sweep runs still failed.",
                    coefficient.estimate, orthogonal.field_inv_failed_runs
                )),
            Some(coefficient) => constrained.notes.push(format!(
                "Skipped orthogonal override `field_inv_ops` because the fitted coefficient was negative ({:.6}).",
                coefficient.estimate
            )),
            None => constrained.notes.push(
                "Orthogonal inversion sweep did not expose `field_inv_ops` in the chosen model."
                    .to_string(),
            ),
        }
    } else {
        constrained.notes.push(
            "Orthogonal inversion fit was unavailable, so spend scoring kept the inherited inversion term."
                .to_string(),
        );
    }

    Ok(constrained)
}

fn spend_circle_profile_variant(
    name: &str,
    proof_bytes: u64,
    chunk_size: u64,
    query_count: u64,
) -> ProfileScoreInput {
    structured_spend_profile(
        SpendProtocol::Circle,
        name,
        query_count,
        chunk_size,
        Some(proof_bytes),
    )
    .profile
}

fn spend_whir_profile_variant(
    name: &str,
    proof_bytes: u64,
    chunk_size: u64,
    query_count: u64,
) -> ProfileScoreInput {
    structured_spend_profile(
        SpendProtocol::Whir,
        name,
        query_count,
        chunk_size,
        Some(proof_bytes),
    )
    .profile
}

fn best_sweep_record(
    records: &[ProfileSweepRecord],
    protocol_family: &str,
) -> Option<ProfileSweepRecord> {
    let protocol_records = records
        .iter()
        .filter(|record| record.protocol_family == protocol_family)
        .cloned()
        .collect::<Vec<_>>();
    let mut feasible = protocol_records
        .iter()
        .filter(|record| record.feasible)
        .cloned()
        .collect::<Vec<_>>();
    feasible.sort_by(|lhs, rhs| lhs.predicted_cu.total_cmp(&rhs.predicted_cu));
    if let Some(best) = feasible.into_iter().next() {
        return Some(best);
    }
    let mut by_cost = protocol_records;
    by_cost.sort_by(|lhs, rhs| lhs.predicted_cu.total_cmp(&rhs.predicted_cu));
    by_cost.into_iter().next()
}

fn security_assumption_slug(
    protocol: SpendProtocol,
    assumption: SecurityQualifiedAssumption,
) -> &'static str {
    match (protocol, assumption) {
        (SpendProtocol::Circle, SecurityQualifiedAssumption::Conservative) => "fri_proven",
        (SpendProtocol::Circle, SecurityQualifiedAssumption::Optimistic) => "fri_conjectured",
        (SpendProtocol::Whir, SecurityQualifiedAssumption::Conservative) => "whir_johnson_full",
        (SpendProtocol::Whir, SecurityQualifiedAssumption::Optimistic) => "whir_capacity_full",
    }
}

fn security_assumption_bits(
    assessment: &QuerySoundnessAssessment,
    assumption: SecurityQualifiedAssumption,
) -> f64 {
    match assumption {
        SecurityQualifiedAssumption::Conservative => assessment.lower_bits,
        SecurityQualifiedAssumption::Optimistic => {
            assessment.upper_bits.unwrap_or(assessment.lower_bits)
        }
    }
}

fn minimum_secure_queries(
    protocol: SpendProtocol,
    log_rate: u32,
    grinding_bits: u32,
    target_bits: f64,
    assumption: SecurityQualifiedAssumption,
) -> Result<u64> {
    for query_count in 1_u64..=4096 {
        let model = match protocol {
            SpendProtocol::Circle => fri_query_soundness_model(
                query_count,
                log_rate,
                grinding_bits,
                target_bits,
                &[],
                &[],
            ),
            SpendProtocol::Whir => whir_query_soundness_model(
                query_count,
                log_rate,
                grinding_bits,
                target_bits,
                &[],
                &[],
            ),
        };
        let assessment = assess_query_soundness(&model);
        if security_assumption_bits(&assessment, assumption) >= target_bits {
            return Ok(query_count);
        }
    }
    bail!(
        "failed to find a security-qualified q for protocol={} log_rate={} grinding_bits={} within search bound",
        match protocol {
            SpendProtocol::Circle => "Circle",
            SpendProtocol::Whir => "WHIR",
        },
        log_rate,
        grinding_bits
    );
}

fn write_security_qualified_sweep_csv(
    path: &Path,
    records: &[SecurityQualifiedSweepRecord],
) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    writer.write_record([
        "scenario_name",
        "protocol_family",
        "soundness_assumption",
        "security_target_bits",
        "cost_scenario_name",
        "rate_parameter_name",
        "log_rate",
        "reciprocal_rate",
        "grinding_bits",
        "minimum_secure_query_count",
        "total_explicit_query_count",
        "chunk_size",
        "proof_bytes",
        "predicted_cu",
        "lower_cu",
        "upper_cu",
        "verification_core_cu",
        "transport_overhead_cu",
        "cu_budget_fraction",
        "proof_transport_pressure",
        "assumption_qualified_feasible",
        "assumption_feasibility_reasons",
        "lower_bound_model_feasible",
        "lower_bound_model_feasibility_reasons",
    ])?;
    for record in records {
        writer.write_record([
            record.scenario_name.clone(),
            record.protocol_family.clone(),
            record.soundness_assumption.clone(),
            format!("{:.1}", record.security_target_bits),
            record.cost_scenario_name.clone(),
            record.rate_parameter_name.clone(),
            record.log_rate.to_string(),
            record.reciprocal_rate.to_string(),
            record.grinding_bits.to_string(),
            record.minimum_secure_query_count.to_string(),
            record.total_explicit_query_count.to_string(),
            record.chunk_size.to_string(),
            record.proof_bytes.to_string(),
            format!("{:.6}", record.predicted_cu),
            record
                .lower_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .upper_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .verification_core_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            record
                .transport_overhead_cu
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            format!("{:.6}", record.cu_budget_fraction),
            format!("{:.6}", record.proof_transport_pressure),
            record.assumption_qualified_feasible.to_string(),
            record.assumption_feasibility_reasons.join("; "),
            record.lower_bound_model_feasible.to_string(),
            record.lower_bound_model_feasibility_reasons.join("; "),
        ])?;
    }
    writer.flush()?;
    Ok(())
}

fn best_security_sweep_record(
    records: &[SecurityQualifiedSweepRecord],
    protocol_family: &str,
    assumption_slug: &str,
    target_bits: f64,
) -> Option<SecurityQualifiedSweepRecord> {
    let protocol_records = records
        .iter()
        .filter(|record| {
            record.protocol_family == protocol_family
                && record.soundness_assumption == assumption_slug
                && (record.security_target_bits - target_bits).abs() < f64::EPSILON
        })
        .cloned()
        .collect::<Vec<_>>();
    let mut feasible = protocol_records
        .iter()
        .filter(|record| record.assumption_qualified_feasible)
        .cloned()
        .collect::<Vec<_>>();
    feasible.sort_by(|lhs, rhs| lhs.predicted_cu.total_cmp(&rhs.predicted_cu));
    if let Some(best) = feasible.into_iter().next() {
        return Some(best);
    }
    let mut by_cost = protocol_records;
    by_cost.sort_by(|lhs, rhs| lhs.predicted_cu.total_cmp(&rhs.predicted_cu));
    by_cost.into_iter().next()
}

fn cost_scenarios() -> Vec<CostScenario> {
    vec![
        CostScenario {
            name: "baseline",
            whir_core_multiplier: 1.0,
            field_mul_multiplier: 1.0,
            extension_mul_multiplier: 1.0,
            notes: vec!["No inferred optimization multiplier is applied.".to_string()],
        },
        CostScenario {
            name: "fenzi_whir_core_0p8",
            whir_core_multiplier: 0.8,
            field_mul_multiplier: 1.0,
            extension_mul_multiplier: 1.0,
            notes: vec![
                "Inferred scenario: applies a 20% reduction to WHIR verifier-core cost as a Fenzi-style fold-representation proxy.".to_string(),
                "This is a scenario multiplier, not a measured coefficient refit.".to_string(),
            ],
        },
        CostScenario {
            name: "m31_mul_0p75",
            whir_core_multiplier: 1.0,
            field_mul_multiplier: 0.75,
            extension_mul_multiplier: 0.75,
            notes: vec![
                "Inferred scenario: scales field_mul_ops and extension_mul_ops coefficients by 0.75 as an M31-native arithmetic calibration proxy.".to_string(),
                "This is not yet a measured re-fit against M31-native kernels.".to_string(),
            ],
        },
        CostScenario {
            name: "fenzi_whir_core_0p8_plus_m31_mul_0p75",
            whir_core_multiplier: 0.8,
            field_mul_multiplier: 0.75,
            extension_mul_multiplier: 0.75,
            notes: vec![
                "Inferred optimistic scenario: combines the Fenzi-style 20% WHIR core reduction with the 0.75 M31-native multiplication calibration.".to_string(),
                "This is a stacked scenario analysis, not a measured verifier implementation.".to_string(),
            ],
        },
    ]
}

fn whir_assumption_name(assumption: WhirSecurityAssumption) -> &'static str {
    match assumption {
        WhirSecurityAssumption::Johnson => "whir_johnson_full",
        WhirSecurityAssumption::Capacity => "whir_capacity_full",
    }
}

fn whir_assumption_rate_log_eta(log_inv_rate: u32, assumption: WhirSecurityAssumption) -> f64 {
    match assumption {
        WhirSecurityAssumption::Johnson => {
            -(0.5 * log_inv_rate as f64 + std::f64::consts::LOG2_10 + 1.0)
        }
        WhirSecurityAssumption::Capacity => {
            -(log_inv_rate as f64 + std::f64::consts::LOG2_10 + 1.0)
        }
    }
}

fn whir_assumption_list_size_bits(
    log_degree: u32,
    log_inv_rate: u32,
    assumption: WhirSecurityAssumption,
) -> f64 {
    let log_eta = whir_assumption_rate_log_eta(log_inv_rate, assumption);
    match assumption {
        WhirSecurityAssumption::Johnson => 0.5 * log_inv_rate as f64 - (1.0 + log_eta),
        WhirSecurityAssumption::Capacity => (log_degree + log_inv_rate) as f64 - log_eta,
    }
}

fn whir_full_log_1_delta(log_inv_rate: u32, assumption: WhirSecurityAssumption) -> f64 {
    let eta = 2_f64.powf(whir_assumption_rate_log_eta(log_inv_rate, assumption));
    let rate = 1.0 / ((1_u64 << log_inv_rate) as f64);
    let delta = match assumption {
        WhirSecurityAssumption::Johnson => 1.0 - rate.sqrt() - eta,
        WhirSecurityAssumption::Capacity => 1.0 - rate - eta,
    };
    (1.0 - delta).log2()
}

fn whir_queries_error(
    log_inv_rate: u32,
    num_queries: u64,
    assumption: WhirSecurityAssumption,
) -> f64 {
    -(num_queries as f64) * whir_full_log_1_delta(log_inv_rate, assumption)
}

fn whir_queries_needed(
    target_bits: f64,
    max_pow_bits: u32,
    log_inv_rate: u32,
    assumption: WhirSecurityAssumption,
) -> u64 {
    let protocol_bits = (target_bits - max_pow_bits as f64).max(0.0);
    (-protocol_bits / whir_full_log_1_delta(log_inv_rate, assumption)).ceil() as u64
}

fn whir_prox_gaps_error(
    log_degree: u32,
    log_inv_rate: u32,
    field_size_bits: u32,
    num_functions: u32,
    assumption: WhirSecurityAssumption,
) -> f64 {
    let error = match assumption {
        WhirSecurityAssumption::Johnson => {
            let log_n = (log_degree + log_inv_rate) as f64;
            let constant = (2.0 * 10.5_f64.powf(5.0) / 3.0).log2();
            let log_rho_neg_3_2 = 1.5 * log_inv_rate as f64;
            log_n + constant + log_rho_neg_3_2
        }
        WhirSecurityAssumption::Capacity => {
            let log_eta = whir_assumption_rate_log_eta(log_inv_rate, assumption);
            (log_degree + 2 * log_inv_rate) as f64 - log_eta
        }
    };
    let num_functions_log = (num_functions as f64 - 1.0).log2();
    field_size_bits as f64 - (error + num_functions_log)
}

fn whir_ood_error(
    log_degree: u32,
    log_inv_rate: u32,
    field_size_bits: u32,
    ood_samples: u32,
    assumption: WhirSecurityAssumption,
) -> f64 {
    let list_size_bits = whir_assumption_list_size_bits(log_degree, log_inv_rate, assumption);
    let error = 2.0 * list_size_bits + (log_degree * ood_samples) as f64;
    (ood_samples * field_size_bits) as f64 + 1.0 - error
}

fn whir_determine_ood_samples(
    target_bits: f64,
    log_degree: u32,
    log_inv_rate: u32,
    field_size_bits: u32,
    assumption: WhirSecurityAssumption,
) -> u32 {
    for ood_samples in 1_u32..64 {
        if whir_ood_error(
            log_degree,
            log_inv_rate,
            field_size_bits,
            ood_samples,
            assumption,
        ) >= target_bits
        {
            return ood_samples;
        }
    }
    63
}

fn whir_fold_sumcheck_error(
    field_size_bits: u32,
    num_variables: u32,
    log_inv_rate: u32,
    assumption: WhirSecurityAssumption,
) -> f64 {
    let list_size = whir_assumption_list_size_bits(num_variables, log_inv_rate, assumption);
    field_size_bits as f64 - (list_size + 1.0)
}

fn whir_queries_combination_error(
    field_size_bits: u32,
    num_variables: u32,
    log_inv_rate: u32,
    ood_samples: u32,
    num_queries: u64,
    assumption: WhirSecurityAssumption,
) -> f64 {
    let list_size = whir_assumption_list_size_bits(num_variables, log_inv_rate, assumption);
    let log_combination = ((ood_samples as f64) + (num_queries as f64)).log2();
    field_size_bits as f64 - (log_combination + list_size + 1.0)
}

fn whir_folding_pow_bits(
    target_bits: f64,
    field_size_bits: u32,
    num_variables: u32,
    log_inv_rate: u32,
    assumption: WhirSecurityAssumption,
) -> u32 {
    let prox_gaps_error =
        whir_prox_gaps_error(num_variables, log_inv_rate, field_size_bits, 2, assumption);
    let sumcheck_error =
        whir_fold_sumcheck_error(field_size_bits, num_variables, log_inv_rate, assumption);
    ((target_bits - prox_gaps_error.min(sumcheck_error)).max(0.0)).ceil() as u32
}

fn whir_round_structure(
    num_variables: u32,
    first_round_folding_factor: u32,
    later_round_folding_factor: u32,
) -> (usize, u32) {
    const MAX_NUM_VARIABLES_TO_SEND_COEFFS: u32 = 6;
    let nv_except_first_round = num_variables.saturating_sub(first_round_folding_factor);
    if nv_except_first_round < MAX_NUM_VARIABLES_TO_SEND_COEFFS {
        return (0, nv_except_first_round);
    }
    let num_rounds = (nv_except_first_round - MAX_NUM_VARIABLES_TO_SEND_COEFFS)
        .div_ceil(later_round_folding_factor);
    let final_sumcheck_rounds = nv_except_first_round - num_rounds * later_round_folding_factor;
    (num_rounds as usize, final_sumcheck_rounds)
}

fn derive_full_whir_security(
    target_bits: f64,
    starting_log_inv_rate: u32,
    max_pow_bits: u32,
    assumption: WhirSecurityAssumption,
    num_variables: u32,
    field_size_bits: u32,
    first_round_folding_factor: u32,
    later_round_folding_factor: u32,
    rs_domain_initial_reduction_factor: u32,
) -> FullWhirSecurityDerivation {
    let commitment_ood_samples = whir_determine_ood_samples(
        target_bits,
        num_variables,
        starting_log_inv_rate,
        field_size_bits,
        assumption,
    );
    let commitment_ood_security_bits = whir_ood_error(
        num_variables,
        starting_log_inv_rate,
        field_size_bits,
        commitment_ood_samples,
        assumption,
    );

    let starting_folding_base_bits = whir_prox_gaps_error(
        num_variables,
        starting_log_inv_rate,
        field_size_bits,
        2,
        assumption,
    )
    .min(whir_fold_sumcheck_error(
        field_size_bits,
        num_variables,
        starting_log_inv_rate,
        assumption,
    ));
    let starting_folding_pow_bits_required = whir_folding_pow_bits(
        target_bits,
        field_size_bits,
        num_variables,
        starting_log_inv_rate,
        assumption,
    );
    let starting_folding_security_bits =
        starting_folding_base_bits + starting_folding_pow_bits_required as f64;

    let (num_rounds, _final_sumcheck_rounds) = whir_round_structure(
        num_variables,
        first_round_folding_factor,
        later_round_folding_factor,
    );

    let mut rounds = Vec::new();
    let mut current_num_variables = num_variables.saturating_sub(first_round_folding_factor);
    let mut current_log_inv_rate = starting_log_inv_rate;
    let mut total_explicit_query_count = 0_u64;
    let mut total_ood_samples = commitment_ood_samples as u64;
    let mut max_required_pow_bits = starting_folding_pow_bits_required;
    let mut overall_security_bits =
        commitment_ood_security_bits.min(starting_folding_security_bits);

    for round_index in 0..num_rounds {
        let current_folding_factor = if round_index == 0 {
            first_round_folding_factor
        } else {
            later_round_folding_factor
        };
        let next_folding_factor = later_round_folding_factor;
        let rs_reduction_factor = if round_index == 0 {
            rs_domain_initial_reduction_factor
        } else {
            1
        };
        let next_log_inv_rate =
            current_log_inv_rate + (current_folding_factor - rs_reduction_factor);
        let num_queries =
            whir_queries_needed(target_bits, max_pow_bits, current_log_inv_rate, assumption);
        let ood_samples = whir_determine_ood_samples(
            target_bits,
            current_num_variables,
            next_log_inv_rate,
            field_size_bits,
            assumption,
        );
        let query_security_bits = whir_queries_error(current_log_inv_rate, num_queries, assumption);
        let combination_security_bits = whir_queries_combination_error(
            field_size_bits,
            current_num_variables,
            next_log_inv_rate,
            ood_samples,
            num_queries,
            assumption,
        );
        let query_pow_bits_required =
            ((target_bits - query_security_bits.min(combination_security_bits)).max(0.0)).ceil()
                as u32;
        let effective_query_security =
            query_security_bits.min(combination_security_bits) + query_pow_bits_required as f64;
        let folding_base_bits = whir_prox_gaps_error(
            current_num_variables,
            next_log_inv_rate,
            field_size_bits,
            2,
            assumption,
        )
        .min(whir_fold_sumcheck_error(
            field_size_bits,
            current_num_variables,
            next_log_inv_rate,
            assumption,
        ));
        let folding_pow_bits_required = whir_folding_pow_bits(
            target_bits,
            field_size_bits,
            current_num_variables,
            next_log_inv_rate,
            assumption,
        );
        let effective_folding_security = folding_base_bits + folding_pow_bits_required as f64;

        total_explicit_query_count += num_queries;
        total_ood_samples += ood_samples as u64;
        max_required_pow_bits = max_required_pow_bits
            .max(query_pow_bits_required)
            .max(folding_pow_bits_required);
        overall_security_bits = overall_security_bits
            .min(effective_query_security)
            .min(effective_folding_security);

        rounds.push(FullWhirRoundDerivation {
            round_index,
            current_log_inv_rate,
            next_log_inv_rate,
            num_variables: current_num_variables,
            num_queries,
            ood_samples: ood_samples as u64,
            query_security_bits,
            combination_security_bits,
            query_pow_bits_required,
            folding_security_bits: folding_base_bits,
            folding_pow_bits_required,
        });

        current_num_variables = current_num_variables.saturating_sub(next_folding_factor);
        current_log_inv_rate = next_log_inv_rate;
    }

    let final_queries =
        whir_queries_needed(target_bits, max_pow_bits, current_log_inv_rate, assumption);
    let final_query_base_bits = whir_queries_error(current_log_inv_rate, final_queries, assumption);
    let final_query_pow_bits_required =
        ((target_bits - final_query_base_bits).max(0.0)).ceil() as u32;
    let final_query_security_bits = final_query_base_bits + final_query_pow_bits_required as f64;
    let final_folding_base_bits = field_size_bits as f64 - 1.0;
    let final_folding_pow_bits_required =
        ((target_bits - final_folding_base_bits).max(0.0)).ceil() as u32;
    let final_folding_security_bits =
        final_folding_base_bits + final_folding_pow_bits_required as f64;

    total_explicit_query_count += final_queries;
    max_required_pow_bits = max_required_pow_bits
        .max(final_query_pow_bits_required)
        .max(final_folding_pow_bits_required);
    overall_security_bits = overall_security_bits
        .min(final_query_security_bits)
        .min(final_folding_security_bits);

    FullWhirSecurityDerivation {
        soundness_assumption: whir_assumption_name(assumption).to_string(),
        target_bits,
        field_size_bits,
        max_pow_bits,
        starting_log_inv_rate,
        num_variables,
        first_round_folding_factor,
        later_round_folding_factor,
        rs_domain_initial_reduction_factor,
        commitment_ood_samples: commitment_ood_samples as u64,
        commitment_ood_security_bits,
        starting_folding_security_bits,
        starting_folding_pow_bits_required,
        rounds,
        final_log_inv_rate: current_log_inv_rate,
        final_queries,
        final_query_security_bits,
        final_query_pow_bits_required,
        final_folding_security_bits,
        final_folding_pow_bits_required,
        total_explicit_query_count,
        total_ood_samples,
        max_required_pow_bits,
        pow_cap_satisfied: max_required_pow_bits <= max_pow_bits,
        overall_security_bits,
    }
}

fn apply_scaled_coefficient(
    model: &mut FittedCostModel,
    feature: &str,
    multiplier: f64,
    rationale: &str,
) -> Result<()> {
    if (multiplier - 1.0).abs() < f64::EPSILON {
        return Ok(());
    }
    if let Some(coefficient) = model.coefficients.get(feature).cloned() {
        let mut scaled = coefficient;
        scaled.estimate *= multiplier;
        if let Some(stderr) = scaled.stderr.as_mut() {
            *stderr *= multiplier.abs();
        }
        scaled.rationale = rationale.to_string();
        model.coefficients.set(feature, scaled)?;
    }
    Ok(())
}

fn apply_cost_scenario_to_core_model(
    base_core_model: &FittedCostModel,
    protocol: SpendProtocol,
    scenario: &CostScenario,
) -> Result<FittedCostModel> {
    let mut adjusted = base_core_model.clone();
    if (scenario.field_mul_multiplier - 1.0).abs() >= f64::EPSILON {
        apply_scaled_coefficient(
            &mut adjusted,
            "field_mul_ops",
            scenario.field_mul_multiplier,
            &format!(
                "scenario `{}` scales field_mul_ops for M31-native arithmetic sensitivity",
                scenario.name
            ),
        )?;
    }
    if (scenario.extension_mul_multiplier - 1.0).abs() >= f64::EPSILON {
        apply_scaled_coefficient(
            &mut adjusted,
            "extension_mul_ops",
            scenario.extension_mul_multiplier,
            &format!(
                "scenario `{}` scales extension_mul_ops for M31-native arithmetic sensitivity",
                scenario.name
            ),
        )?;
    }
    if matches!(protocol, SpendProtocol::Whir)
        && (scenario.whir_core_multiplier - 1.0).abs() >= f64::EPSILON
    {
        for feature in VERIFICATION_CORE_CANDIDATES {
            apply_scaled_coefficient(
                &mut adjusted,
                feature,
                scenario.whir_core_multiplier,
                &format!(
                    "scenario `{}` applies a WHIR verifier-core multiplier",
                    scenario.name
                ),
            )?;
        }
    }
    adjusted.notes.push(format!(
        "Applied cost scenario `{}` (WHIR core x{:.3}, field_mul x{:.3}, extension_mul x{:.3}).",
        scenario.name,
        scenario.whir_core_multiplier,
        scenario.field_mul_multiplier,
        scenario.extension_mul_multiplier
    ));
    Ok(adjusted)
}

fn full_whir_query_soundness_assessment(
    derivation: &FullWhirSecurityDerivation,
) -> QuerySoundnessAssessment {
    QuerySoundnessAssessment {
        model: "whir_full_derived".to_string(),
        query_count: derivation.total_explicit_query_count,
        target_bits: derivation.target_bits,
        lower_bits: derivation.overall_security_bits,
        lower_assumption: derivation.soundness_assumption.clone(),
        upper_bits: None,
        upper_assumption: None,
        meets_target: derivation.overall_security_bits >= derivation.target_bits
            && derivation.pow_cap_satisfied,
        notes: vec![
            format!(
                "Full WHIR-derived screen with starting rate 1/{} over {} variables and field size {} bits.",
                1_u64 << derivation.starting_log_inv_rate,
                derivation.num_variables,
                derivation.field_size_bits
            ),
            format!(
                "Commitment OOD samples: {}; total explicit proof queries across all rounds: {}.",
                derivation.commitment_ood_samples, derivation.total_explicit_query_count
            ),
            format!(
                "Maximum derived PoW requirement is {} bits against a configured cap of {} bits.",
                derivation.max_required_pow_bits, derivation.max_pow_bits
            ),
            "Overall security is taken as the minimum protected term across commitment OOD, folding, per-round query/combination, final query, and final folding steps.".to_string(),
        ],
        sources: vec![
            "https://github.com/Plonky3/Plonky3/blob/main/whir/src/parameters/soundness.rs"
                .to_string(),
            "https://github.com/Plonky3/Plonky3/blob/main/whir/src/parameters/whir.rs"
                .to_string(),
            "https://eprint.iacr.org/2024/1586".to_string(),
            "https://eprint.iacr.org/2025/2055".to_string(),
        ],
    }
}

fn build_security_qualified_profile(
    protocol: SpendProtocol,
    scenario_name: &str,
    log_rate: u32,
    grinding_bits: u32,
    target_bits: f64,
    assumption: SecurityQualifiedAssumption,
) -> Result<(
    ProfileScoreInput,
    QuerySoundnessAssessment,
    u64,
    Vec<String>,
)> {
    match protocol {
        SpendProtocol::Circle => {
            let minimum_query_count =
                minimum_secure_queries(protocol, log_rate, grinding_bits, target_bits, assumption)?;
            let bundle = structured_spend_profile_with_tuning(
                protocol,
                scenario_name,
                minimum_query_count,
                640,
                None,
                log_rate,
                grinding_bits,
            );
            let profile = bundle.profile;
            let assessment = profile
                .query_soundness_model
                .as_ref()
                .map(assess_query_soundness)
                .ok_or_else(|| anyhow!("missing query soundness model for {}", profile.name))?;
            Ok((profile, assessment, minimum_query_count, Vec::new()))
        }
        SpendProtocol::Whir => {
            let statement = default_spend_statement();
            let mut arithmetization = default_spend_arithmetization();
            let boundary_layout = spend_boundary_layout(&statement);
            arithmetization.boundary_constraint_groups = boundary_layout.total_groups;
            let application_merkle_paths = statement.spends * statement.note_openings_per_spend;
            let application_merkle_levels = application_merkle_paths * statement.note_tree_depth;
            let application_hash_gadgets = statement.spends * statement.nullifier_hashes_per_spend
                + statement.outputs * statement.note_commitments_per_output;
            let total_rows = application_merkle_levels * arithmetization.merkle_rows_per_level
                + statement.spends
                    * statement.nullifier_hashes_per_spend
                    * arithmetization.nullifier_hash_rows
                + statement.outputs
                    * statement.note_commitments_per_output
                    * arithmetization.note_commitment_rows
                + statement.amount_range_checks_64 * arithmetization.range_check_rows
                + statement.ownership_checks * arithmetization.ownership_rows
                + statement.balance_constraints * arithmetization.balance_rows
                + statement.lookup_arguments * arithmetization.lookup_rows
                + arithmetization.misc_rows;
            let evaluation_domain_log2 = ceil_log2(total_rows.max(1));
            let derivation = derive_full_whir_security(
                target_bits,
                log_rate,
                grinding_bits,
                match assumption {
                    SecurityQualifiedAssumption::Conservative => WhirSecurityAssumption::Johnson,
                    SecurityQualifiedAssumption::Optimistic => WhirSecurityAssumption::Capacity,
                },
                evaluation_domain_log2,
                155,
                4,
                4,
                1,
            );

            let total_query_count = derivation.total_explicit_query_count;
            let bundle = structured_spend_profile_with_tuning(
                protocol,
                scenario_name,
                total_query_count,
                640,
                None,
                log_rate,
                grinding_bits,
            );
            let mut profile = bundle.profile;
            let round_merkle_levels = derivation
                .rounds
                .iter()
                .map(|round| {
                    let verifier = spend_verifier_assumptions(
                        protocol,
                        round.num_queries,
                        round.current_log_inv_rate,
                        grinding_bits,
                    );
                    round.num_queries * verifier.proof_merkle_depth
                })
                .sum::<u64>();
            let final_merkle_levels = {
                let verifier = spend_verifier_assumptions(
                    protocol,
                    derivation.final_queries,
                    derivation.final_log_inv_rate,
                    grinding_bits,
                );
                derivation.final_queries * verifier.proof_merkle_depth
            };
            let total_proof_merkle_levels = round_merkle_levels + final_merkle_levels;

            let verifier =
                spend_verifier_assumptions(protocol, total_query_count, log_rate, grinding_bits);
            let base_proof_bytes = verifier.base_proof_bytes
                + verifier.proof_bytes_per_log2_rows * evaluation_domain_log2 as u64
                + verifier.proof_bytes_per_lookup_argument * statement.lookup_arguments
                + verifier.proof_bytes_per_hash_gadget * application_hash_gadgets;
            let round_query_bytes = derivation
                .rounds
                .iter()
                .map(|round| {
                    let round_verifier = spend_verifier_assumptions(
                        protocol,
                        round.num_queries,
                        round.current_log_inv_rate,
                        grinding_bits,
                    );
                    round_verifier.proof_bytes_per_query * round.num_queries
                })
                .sum::<u64>();
            let final_query_bytes = {
                let final_verifier = spend_verifier_assumptions(
                    protocol,
                    derivation.final_queries,
                    derivation.final_log_inv_rate,
                    grinding_bits,
                );
                final_verifier.proof_bytes_per_query * derivation.final_queries
            };
            let ood_sample_bytes = (155_u64 + 7).div_ceil(8);
            let proof_bytes = base_proof_bytes
                + round_query_bytes
                + final_query_bytes
                + derivation.total_ood_samples * ood_sample_bytes;
            let transport = transport_features(proof_bytes, 640);

            profile.features.merkle_paths = total_query_count + application_merkle_paths;
            profile.features.merkle_levels = total_proof_merkle_levels + application_merkle_levels;
            profile.features.proof_bytes = proof_bytes;
            profile.features.proof_segments =
                proof_bytes.div_ceil(verifier.proof_segment_bytes).max(9);
            profile.features.upload_bytes = proof_bytes;
            profile.features.upload_chunks = transport.upload_chunks;
            profile.features.sha_calls =
                profile.features.merkle_levels + verifier.sha_calls_base + transport.sha_calls;
            profile.features.sha_bytes = profile.features.merkle_levels * 64
                + proof_bytes
                + verifier.sha_bytes_base
                + transport.sha_bytes;
            profile.transport = transport;
            profile.parameter_choices.push(parameter_choice(
                "security_target_bits",
                format!("{target_bits:.0}"),
                "Explicit security target for the scorer-side sweep.",
                &[],
            ));
            profile.parameter_choices.push(parameter_choice(
                "total_explicit_query_count",
                total_query_count.to_string(),
                "Total explicit WHIR proof queries across intermediate and final phases, derived from the official round-by-round parameter generation.",
                &[
                    "https://github.com/Plonky3/Plonky3/blob/main/whir/src/parameters/whir.rs",
                ],
            ));
            profile.parameter_choices.push(parameter_choice(
                "field_size_bits",
                "155",
                "Inferred M31-style screening assumption: degree-5 extension field for the full-WHIR security model.",
                &[
                    "https://eprint.iacr.org/2025/2055",
                ],
            ));
            profile.parameter_choices.push(parameter_choice(
                "folding_factor",
                "4/4",
                "Inferred WHIR screening assumption: first-round folding factor 4 and later-round folding factor 4, matching the reference CLI defaults.",
                &[
                    "https://github.com/GalArnon/whir/blob/main/src/bin/main.rs",
                ],
            ));
            profile.query_soundness_model = None;
            profile.notes.push(format!(
                "Full WHIR-derived security replaces the earlier query-only screen; total explicit queries={}, total OOD samples={}, final rate=1/{}.",
                total_query_count,
                derivation.total_ood_samples,
                1_u64 << derivation.final_log_inv_rate
            ));
            let mut derivation_notes = Vec::new();
            if !derivation.pow_cap_satisfied {
                derivation_notes.push(format!(
                    "Derived WHIR configuration exceeds the configured max PoW cap: required {} bits, allowed {} bits.",
                    derivation.max_required_pow_bits, derivation.max_pow_bits
                ));
            }
            derivation_notes.push(format!(
                "Starting-round query count is {}; final-round query count is {}.",
                derivation
                    .rounds
                    .first()
                    .map(|round| round.num_queries)
                    .unwrap_or(derivation.final_queries),
                derivation.final_queries
            ));
            let starting_round_query_count = derivation
                .rounds
                .first()
                .map(|round| round.num_queries)
                .unwrap_or(derivation.final_queries);
            Ok((
                profile,
                full_whir_query_soundness_assessment(&derivation),
                starting_round_query_count,
                derivation_notes,
            ))
        }
    }
}

fn write_security_qualified_spend_sweep(
    examples_dir: &Path,
    results_dir: &Path,
    constrained_model: &FittedCostModel,
    constrained_core_model: &FittedCostModel,
    transport_model: Option<&FittedCostModel>,
    limits: &SvmLimits,
) -> Result<SecurityQualifiedSweepSummary> {
    remove_generated_yaml_with_prefix(examples_dir, "qualified-")?;
    let mut records = Vec::new();
    let chunk_size = 640_u64;
    let target_bits_sweep = [100.0_f64, 120.0, 128.0];
    let cost_scenarios = cost_scenarios();
    for (protocol, log_rates, grinding_values) in [
        (
            SpendProtocol::Circle,
            vec![1_u32, 2, 3, 4, 5],
            vec![0_u32, 8, 16, 24, 32],
        ),
        (
            SpendProtocol::Whir,
            vec![1_u32, 2, 3, 4],
            vec![0_u32, 8, 16, 20, 24, 32],
        ),
    ] {
        for target_bits in target_bits_sweep {
            for log_rate in log_rates.clone() {
                for grinding_bits in grinding_values.clone() {
                    for assumption in [
                        SecurityQualifiedAssumption::Conservative,
                        SecurityQualifiedAssumption::Optimistic,
                    ] {
                        let assumption_slug = security_assumption_slug(protocol, assumption);
                        let protocol_slug = match protocol {
                            SpendProtocol::Circle => "circle",
                            SpendProtocol::Whir => "whir",
                        };
                        let base_scenario_name = format!(
                            "qualified-{protocol_slug}-t{:.0}-r{}-g{}-{}",
                            target_bits,
                            1_u64 << log_rate,
                            grinding_bits,
                            assumption_slug,
                        );
                        let (profile, assessment, minimum_query_count, derivation_notes) =
                            build_security_qualified_profile(
                                protocol,
                                &base_scenario_name,
                                log_rate,
                                grinding_bits,
                                target_bits,
                                assumption,
                            )?;
                        let path = examples_dir.join(format!("{}.yaml", profile.name));
                        fs::write(&path, serde_yaml::to_string(&profile)?)?;
                        for cost_scenario in &cost_scenarios {
                            let scenario_name =
                                format!("{base_scenario_name}-{}", cost_scenario.name);
                            let scenario_core_model = apply_cost_scenario_to_core_model(
                                constrained_core_model,
                                protocol,
                                cost_scenario,
                            )?;
                            let score = score_profile_with_components(
                                constrained_model,
                                Some(&scenario_core_model),
                                transport_model,
                                limits,
                                &profile,
                            )?;
                            let scenario_predicted_cu =
                                score.component_predicted_cu.unwrap_or(score.predicted_cu);
                            let mut lower_bound_model_feasibility_reasons = Vec::new();
                            if scenario_predicted_cu > limits.max_compute_units_per_tx as f64 {
                                lower_bound_model_feasibility_reasons.push(
                                    "predicted CU exceeds the transaction compute budget"
                                        .to_string(),
                                );
                            }
                            if profile.features.heap_frame_bytes_requested
                                > limits.max_heap_frame_bytes
                            {
                                lower_bound_model_feasibility_reasons.push(
                                    "requested heap frame exceeds current SVM limit".to_string(),
                                );
                            }
                            if profile.features.upload_chunks == 0
                                && profile.transport.upload_bytes > limits.max_transaction_bytes
                            {
                                lower_bound_model_feasibility_reasons.push(
                                    "upload bytes imply chunking but upload_chunks is zero"
                                        .to_string(),
                                );
                            }

                            let bits = security_assumption_bits(&assessment, assumption);
                            let mut assumption_feasibility_reasons =
                                lower_bound_model_feasibility_reasons.clone();
                            if !assessment.meets_target {
                                assumption_feasibility_reasons.push(format!(
                                    "{} soundness term {:.1} bits is below the {:.1}-bit target",
                                    assumption_slug, bits, assessment.target_bits
                                ));
                            }

                            let mut notes = profile.notes.clone();
                            notes.extend(derivation_notes.clone());
                            notes.extend(cost_scenario.notes.clone());

                            records.push(SecurityQualifiedSweepRecord {
                                scenario_name,
                                protocol_family: match protocol {
                                    SpendProtocol::Circle => "Circle".to_string(),
                                    SpendProtocol::Whir => "WHIR".to_string(),
                                },
                                soundness_assumption: assumption_slug.to_string(),
                                security_target_bits: target_bits,
                                cost_scenario_name: cost_scenario.name.to_string(),
                                rate_parameter_name: match protocol {
                                    SpendProtocol::Circle => "log_blowup".to_string(),
                                    SpendProtocol::Whir => "log_inv_rate".to_string(),
                                },
                                log_rate,
                                reciprocal_rate: 1_u64 << log_rate,
                                grinding_bits,
                                minimum_secure_query_count: minimum_query_count,
                                total_explicit_query_count: assessment.query_count,
                                chunk_size,
                                proof_bytes: profile.features.proof_bytes,
                                predicted_cu: scenario_predicted_cu,
                                lower_cu: Some(
                                    (scenario_predicted_cu - constrained_model.uncertainty_rmse)
                                        .max(0.0),
                                ),
                                upper_cu: Some(
                                    scenario_predicted_cu + constrained_model.uncertainty_rmse,
                                ),
                                verification_core_cu: score.verification_core_cu,
                                transport_overhead_cu: score.transport_overhead_cu,
                                cu_budget_fraction: scenario_predicted_cu
                                    / limits.max_compute_units_per_tx as f64,
                                proof_transport_pressure: score.proof_transport_pressure,
                                assumption_qualified_feasible: assumption_feasibility_reasons
                                    .is_empty(),
                                assumption_feasibility_reasons,
                                lower_bound_model_feasible: lower_bound_model_feasibility_reasons
                                    .is_empty(),
                                lower_bound_model_feasibility_reasons,
                                query_soundness: assessment.clone(),
                                notes,
                            });
                        }
                    }
                }
            }
        }
    }

    let sweep_path = results_dir.join("security_qualified_spend_sweep.json");
    let summary_path = results_dir.join("security_qualified_spend_summary.json");
    write_json(&sweep_path, &records)?;
    write_security_qualified_sweep_csv(
        &results_dir.join("security_qualified_spend_sweep.csv"),
        &records,
    )?;

    let mut best_by_protocol_assumption_target = Vec::new();
    for target_bits in [100.0_f64, 120.0, 128.0] {
        for (protocol, assumption) in [
            ("Circle", "fri_proven"),
            ("Circle", "fri_conjectured"),
            ("WHIR", "whir_johnson_full"),
            ("WHIR", "whir_capacity_full"),
        ] {
            if let Some(record) =
                best_security_sweep_record(&records, protocol, assumption, target_bits)
            {
                best_by_protocol_assumption_target.push(record);
            }
        }
    }

    let mut feasible_counts = BTreeMap::new();
    for target_bits in [100.0_f64, 120.0, 128.0] {
        for (protocol, assumption) in [
            ("Circle", "fri_proven"),
            ("Circle", "fri_conjectured"),
            ("WHIR", "whir_johnson_full"),
            ("WHIR", "whir_capacity_full"),
        ] {
            feasible_counts.insert(
                format!("{protocol}/{assumption}/t{target_bits:.0}"),
                records
                    .iter()
                    .filter(|record| {
                        record.protocol_family == protocol
                            && record.soundness_assumption == assumption
                            && (record.security_target_bits - target_bits).abs() < f64::EPSILON
                            && record.assumption_qualified_feasible
                    })
                    .count(),
            );
        }
    }

    let summary = SecurityQualifiedSweepSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        sweep_path: "phase1_results/security_qualified_spend_sweep.json".to_string(),
        best_by_protocol_assumption_target,
        feasible_counts,
        notes: vec![
            "This sweep varies rate, grinding, security target (100/120/128 bits), and inferred cost scenario jointly before scoring verifier cost.".to_string(),
            "Circle still solves for the minimum literal FRI query count q that reaches the target under the proven or conjectured bound.".to_string(),
            "WHIR no longer uses the earlier query-only screen: it derives commitment OOD samples, per-round query counts, query/combination PoW requirements, folding checks, final queries, and final PoW from the official Plonky3 parameter-generation logic.".to_string(),
            "Grinding bits mostly move security, not verifier work. The current screen charges only a fixed-size witness check when grinding is enabled.".to_string(),
            "The Fenzi and M31 scenario multipliers are inference-only sensitivity cases layered on top of the measured model; they are not yet backed by a new probe fit.".to_string(),
        ],
    };
    write_json(&summary_path, &summary)?;
    Ok(summary)
}

fn write_refined_spend_outputs(
    examples_dir: &Path,
    results_dir: &Path,
    summary: &Phase1Summary,
    orthogonal: &OrthogonalSweepSummary,
    limits: &SvmLimits,
) -> Result<RefinedSpendSummary> {
    let constrained_model =
        build_constrained_spend_model(&summary.model.chosen, orthogonal, "full")?;
    let constrained_core_model = build_constrained_spend_model(
        &summary
            .verification_core_model
            .as_ref()
            .ok_or_else(|| anyhow!("verification-core model missing from base summary"))?
            .chosen,
        orthogonal,
        "verification_core",
    )?;
    write_json(
        &results_dir.join("refined_spend_model.json"),
        &constrained_model,
    )?;
    write_json(
        &results_dir.join("refined_spend_core_model.json"),
        &constrained_core_model,
    )?;
    let security_qualified_summary = write_security_qualified_spend_sweep(
        examples_dir,
        results_dir,
        &constrained_model,
        &constrained_core_model,
        summary.transport_model.as_ref().map(|value| &value.chosen),
        limits,
    )?;

    let baseline_bundles = vec![
        structured_spend_profile(
            SpendProtocol::Circle,
            "spend-circle-profile",
            5,
            512,
            Some(6_656),
        ),
        structured_spend_profile(
            SpendProtocol::Whir,
            "spend-whir-profile",
            4,
            512,
            Some(5_632),
        ),
    ];
    let baseline_profiles = baseline_bundles
        .iter()
        .map(|bundle| bundle.profile.clone())
        .collect::<Vec<_>>();
    let mut structured_projections = baseline_bundles
        .iter()
        .map(|bundle| bundle.projection.clone())
        .collect::<Vec<_>>();
    let baseline_scores = baseline_profiles
        .iter()
        .map(|profile| {
            score_profile_with_components(
                &summary.model.chosen,
                summary
                    .verification_core_model
                    .as_ref()
                    .map(|value| &value.chosen),
                summary.transport_model.as_ref().map(|value| &value.chosen),
                limits,
                profile,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    let refined_scores = baseline_profiles
        .iter()
        .map(|profile| {
            score_profile_with_components(
                &constrained_model,
                Some(&constrained_core_model),
                summary.transport_model.as_ref().map(|value| &value.chosen),
                limits,
                profile,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    write_json(
        &results_dir.join("refined_spend_scores.json"),
        &refined_scores,
    )?;

    let mut sweep_records = Vec::new();
    for proof_bytes in [5_632_u64, 6_144, 6_656, 7_168] {
        for chunk_size in [448_u64, 512, 640] {
            for query_count in [3_u64, 4, 5, 6] {
                let bundle = structured_spend_profile(
                    SpendProtocol::Circle,
                    &format!("spend-circle-p{proof_bytes}-c{chunk_size}-q{query_count}"),
                    query_count,
                    chunk_size,
                    Some(proof_bytes),
                );
                structured_projections.push(bundle.projection.clone());
                let profile = bundle.profile;
                let path = examples_dir.join(format!("{}.yaml", profile.name));
                fs::write(&path, serde_yaml::to_string(&profile)?)?;
                let score = score_profile_with_components(
                    &constrained_model,
                    Some(&constrained_core_model),
                    summary.transport_model.as_ref().map(|value| &value.chosen),
                    limits,
                    &profile,
                )?;
                sweep_records.push(ProfileSweepRecord {
                    scenario_name: profile.name.clone(),
                    protocol_family: "Circle".to_string(),
                    proof_bytes,
                    chunk_size,
                    query_count,
                    predicted_cu: score.predicted_cu,
                    lower_cu: score.lower_cu,
                    upper_cu: score.upper_cu,
                    verification_core_cu: score.verification_core_cu,
                    transport_overhead_cu: score.transport_overhead_cu,
                    component_predicted_cu: score.component_predicted_cu,
                    component_gap_vs_monolithic_cu: score.component_gap_vs_monolithic_cu,
                    cu_budget_fraction: score.cu_budget_fraction,
                    proof_transport_pressure: score.proof_transport_pressure,
                    feasible: score.feasible,
                    feasibility_reasons: score.feasibility_reasons,
                    query_soundness: score.query_soundness,
                    notes: profile.notes,
                });
            }
        }
    }
    for proof_bytes in [5_120_u64, 5_632, 6_144, 6_656] {
        for chunk_size in [448_u64, 512, 640] {
            for query_count in [3_u64, 4, 5] {
                let bundle = structured_spend_profile(
                    SpendProtocol::Whir,
                    &format!("spend-whir-p{proof_bytes}-c{chunk_size}-q{query_count}"),
                    query_count,
                    chunk_size,
                    Some(proof_bytes),
                );
                structured_projections.push(bundle.projection.clone());
                let profile = bundle.profile;
                let path = examples_dir.join(format!("{}.yaml", profile.name));
                fs::write(&path, serde_yaml::to_string(&profile)?)?;
                let score = score_profile_with_components(
                    &constrained_model,
                    Some(&constrained_core_model),
                    summary.transport_model.as_ref().map(|value| &value.chosen),
                    limits,
                    &profile,
                )?;
                sweep_records.push(ProfileSweepRecord {
                    scenario_name: profile.name.clone(),
                    protocol_family: "WHIR".to_string(),
                    proof_bytes,
                    chunk_size,
                    query_count,
                    predicted_cu: score.predicted_cu,
                    lower_cu: score.lower_cu,
                    upper_cu: score.upper_cu,
                    verification_core_cu: score.verification_core_cu,
                    transport_overhead_cu: score.transport_overhead_cu,
                    component_predicted_cu: score.component_predicted_cu,
                    component_gap_vs_monolithic_cu: score.component_gap_vs_monolithic_cu,
                    cu_budget_fraction: score.cu_budget_fraction,
                    proof_transport_pressure: score.proof_transport_pressure,
                    feasible: score.feasible,
                    feasibility_reasons: score.feasibility_reasons,
                    query_soundness: score.query_soundness,
                    notes: profile.notes,
                });
            }
        }
    }
    write_json(
        &results_dir.join("refined_spend_sweep.json"),
        &sweep_records,
    )?;
    write_profile_sweep_csv(&results_dir.join("refined_spend_sweep.csv"), &sweep_records)?;
    write_json(
        &results_dir.join("structured_spend_projections.json"),
        &structured_projections,
    )?;

    let mut protocol_feasible_counts = BTreeMap::new();
    for protocol_family in ["Circle", "WHIR"] {
        protocol_feasible_counts.insert(
            protocol_family.to_string(),
            sweep_records
                .iter()
                .filter(|record| record.protocol_family == protocol_family && record.feasible)
                .count(),
        );
    }
    let best_by_protocol = ["Circle", "WHIR"]
        .iter()
        .filter_map(|protocol| best_sweep_record(&sweep_records, protocol))
        .collect::<Vec<_>>();
    let query_count_summary = [3_u64, 4, 5, 6]
        .iter()
        .filter_map(|query_count| {
            let records = sweep_records
                .iter()
                .filter(|record| record.query_count == *query_count)
                .collect::<Vec<_>>();
            if records.is_empty() {
                None
            } else {
                Some(QueryCountSweepSummary {
                    query_count: *query_count,
                    min_predicted_cu: records
                        .iter()
                        .map(|record| record.predicted_cu)
                        .fold(f64::INFINITY, f64::min),
                    max_predicted_cu: records
                        .iter()
                        .map(|record| record.predicted_cu)
                        .fold(f64::NEG_INFINITY, f64::max),
                    feasible_count: records.iter().filter(|record| record.feasible).count(),
                })
            }
        })
        .collect::<Vec<_>>();

    let refined_summary = RefinedSpendSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        constrained_model_path: "phase1_results/refined_spend_model.json".to_string(),
        constrained_core_model_path: "phase1_results/refined_spend_core_model.json".to_string(),
        structured_projection_path: "phase1_results/structured_spend_projections.json".to_string(),
        baseline_scores,
        refined_scores,
        best_by_protocol,
        protocol_feasible_counts,
        query_count_summary,
        security_qualified_sweep_path: "phase1_results/security_qualified_spend_sweep.json"
            .to_string(),
        security_qualified_summary_path: "phase1_results/security_qualified_spend_summary.json"
            .to_string(),
        security_qualified_best_by_protocol_assumption: security_qualified_summary
            .best_by_protocol_assumption_target
            .clone(),
        security_qualified_feasible_counts: security_qualified_summary.feasible_counts.clone(),
        sweep_artifacts: vec![
            "phase1_results/refined_spend_scores.json".to_string(),
            "phase1_results/refined_spend_sweep.json".to_string(),
            "phase1_results/refined_spend_sweep.csv".to_string(),
            "phase1_results/structured_spend_projections.json".to_string(),
            "phase1_results/security_qualified_spend_sweep.json".to_string(),
            "phase1_results/security_qualified_spend_sweep.csv".to_string(),
            "phase1_results/security_qualified_spend_summary.json".to_string(),
        ],
        notes: vec![
            "Refined spend scores preserve the base additive model for global structure and constrain only the account-I/O terms from the orthogonal sweeps.".to_string(),
            "Spend profiles and sweeps are now derived from an explicit spend-statement arithmetization rather than hand-entered verifier proxy counts.".to_string(),
            "The q parameter is a literal absolute verifier-query count in the current model, not query rounds or an internally batched effective count.".to_string(),
            "Circle and WHIR spend profiles now attach protocol-backed lower/upper query-soundness estimates rather than leaving q as an unlabeled screening knob.".to_string(),
            "The recovered inversion coefficient is folded into spend scoring only if the Winterfell-aligned inversion sweep succeeds without failures.".to_string(),
            "Spend field_inv_ops now uses structural divisor and batch-inversion counts rather than the earlier query-scaled proxy; boundary groups are derived from an explicit AIR layout and low-degree batches are tied to named protocol stages.".to_string(),
            "A second spend sweep now varies rate, grinding, security target (100/120/128 bits), and inferred optimization scenarios jointly before scoring cost.".to_string(),
        ],
    };
    write_json(
        &results_dir.join("refined_spend_summary.json"),
        &refined_summary,
    )?;
    Ok(refined_summary)
}

fn write_sample_profiles(examples_dir: &Path) -> Result<Vec<PathBuf>> {
    let fri_like = hypothetical_fri_profile();
    let circle_like = hypothetical_circle_profile("hypothetical-circle-profile", 5_120, 512, 4);
    let whir_like = hypothetical_whir_profile();

    let fri_path = examples_dir.join("hypothetical-fri-profile.yaml");
    let circle_path = examples_dir.join("hypothetical-circle-profile.yaml");
    let whir_path = examples_dir.join("hypothetical-whir-profile.yaml");
    fs::write(&fri_path, serde_yaml::to_string(&fri_like)?)?;
    fs::write(&circle_path, serde_yaml::to_string(&circle_like)?)?;
    fs::write(&whir_path, serde_yaml::to_string(&whir_like)?)?;
    Ok(vec![fri_path, circle_path, whir_path])
}

fn aggregate_upload_record(
    limits: &SvmLimits,
    label: impl Into<String>,
    repetition: u32,
    upload_bytes: u64,
    upload_chunks: u64,
    actual_cu: u64,
    rolling_hash: bool,
) -> MeasurementRecord {
    let mut features = CostFeatures::default();
    features.upload_bytes = upload_bytes;
    features.upload_chunks = upload_chunks;
    if rolling_hash {
        features.sha_calls = upload_chunks;
        features.sha_bytes = upload_bytes + 32 * upload_chunks;
    }
    let mut origins = default_origins();
    origins.insert("upload_bytes".to_string(), FeatureOrigin::DirectMeasurement);
    origins.insert(
        "upload_chunks".to_string(),
        FeatureOrigin::DirectMeasurement,
    );
    if rolling_hash {
        origins.insert("sha_calls".to_string(), FeatureOrigin::DerivedStructure);
        origins.insert("sha_bytes".to_string(), FeatureOrigin::DerivedStructure);
    }
    MeasurementRecord {
        measurement_id: format!(
            "orthogonal-upload-{}-{repetition}",
            Utc::now().timestamp_millis()
        ),
        benchmark: BenchmarkKind::UploadPath,
        label: label.into(),
        repetition,
        timestamp_utc: Utc::now().to_rfc3339(),
        svm_limits: limits.clone(),
        features,
        feature_origins: origins,
        actual_cu: Some(actual_cu),
        transaction_bytes: None,
        status: MeasurementStatus::Success,
        error: None,
        notes: vec![
            "Aggregate upload-path record synthesized from a full chunked upload run.".to_string(),
        ],
    }
}

fn run_orthogonal_sweeps(
    harness: &BenchHarness,
) -> Result<(Vec<MeasurementRecord>, OrthogonalSweepSummary)> {
    let mut records = Vec::new();

    let upload_total_scenarios = [1_024usize, 2_048, 3_072, 4_096, 6_144];
    for (idx, total_bytes) in upload_total_scenarios.iter().enumerate() {
        let data = (0..*total_bytes)
            .map(|offset| (offset % 251) as u8)
            .collect::<Vec<_>>();
        let (_, mut chunk_records, total_cu) = upload_bytes(
            harness,
            &data,
            512,
            false,
            &format!("orthogonal/upload-bytes/{total_bytes}"),
            1,
        )?;
        records.append(&mut chunk_records);
        records.push(aggregate_upload_record(
            &harness.limits,
            format!("orthogonal/upload-aggregate/bytes-{total_bytes}"),
            idx as u32,
            *total_bytes as u64,
            (*total_bytes as u64).div_ceil(512),
            total_cu,
            false,
        ));
    }

    let upload_chunk_scenarios = [896usize, 768, 512, 384, 256];
    for (idx, chunk_size) in upload_chunk_scenarios.iter().enumerate() {
        let total_bytes = 4_096usize;
        let data = (0..total_bytes)
            .map(|offset| (offset % 251) as u8)
            .collect::<Vec<_>>();
        let (_, mut chunk_records, total_cu) = upload_bytes(
            harness,
            &data,
            *chunk_size,
            false,
            &format!("orthogonal/upload-chunks/{chunk_size}"),
            1,
        )?;
        records.append(&mut chunk_records);
        records.push(aggregate_upload_record(
            &harness.limits,
            format!("orthogonal/upload-aggregate/chunks-{chunk_size}"),
            idx as u32,
            total_bytes as u64,
            (total_bytes as u64).div_ceil(*chunk_size as u64),
            total_cu,
            false,
        ));
    }

    for (ro_count, rw_count, read_bytes, write_bytes, fixed_layout) in [
        (1usize, 0usize, 256usize, 0usize, true),
        (2, 0, 256, 0, true),
        (4, 0, 256, 0, true),
        (8, 0, 256, 0, true),
        (0, 1, 256, 64, true),
        (0, 2, 256, 64, true),
        (0, 4, 256, 64, true),
        (4, 0, 512, 0, true),
        (4, 0, 1_024, 0, true),
        (4, 0, 2_048, 0, true),
        (0, 2, 256, 128, true),
        (0, 2, 256, 256, true),
        (0, 2, 256, 512, true),
    ] {
        let total = ro_count + rw_count;
        let account_size = read_bytes.max(write_bytes).max(256);
        let mut accounts = Vec::new();
        for _ in 0..total {
            accounts.push(create_program_account(harness, account_size)?);
        }
        populate_accounts(harness, &accounts, !fixed_layout, 43)?;

        let mut metas = Vec::new();
        for account in accounts.iter().take(ro_count) {
            metas.push(AccountMeta::new_readonly(account.pubkey(), false));
        }
        for account in accounts.iter().skip(ro_count) {
            metas.push(AccountMeta::new(account.pubkey(), false));
        }

        let instruction = ProbeInstruction::instruction(
            harness.program_id,
            metas,
            ProbeInstruction::AccountIo {
                fixed_layout,
                read_bytes_per_account: read_bytes as u32,
                write_bytes_per_account: write_bytes as u32,
            },
        );
        for repetition in 0..2 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            features.ro_account_count = ro_count as u64;
            features.rw_account_count = rw_count as u64;
            features.account_data_bytes_read = ((ro_count + rw_count) * read_bytes) as u64;
            features.account_data_bytes_written = (rw_count * write_bytes) as u64;
            let mut origins = default_origins();
            origins.insert(
                "ro_account_count".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "rw_account_count".to_string(),
                FeatureOrigin::DirectMeasurement,
            );
            origins.insert(
                "account_data_bytes_read".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            origins.insert(
                "account_data_bytes_written".to_string(),
                FeatureOrigin::DerivedStructure,
            );
            records.push(new_record(
                BenchmarkKind::AccountIo,
                format!(
                    "orthogonal/account-io/{ro_count}-{rw_count}-{read_bytes}-{write_bytes}-{fixed_layout}"
                ),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                vec!["Orthogonal account-IO sweep record.".to_string()],
            ));
        }
    }

    for iterations in [4u32, 8, 16, 24, 32, 48, 64] {
        let instruction = ProbeInstruction::instruction(
            harness.program_id,
            Vec::new(),
            ProbeInstruction::FieldOps {
                kernel: FieldKernel::Inv,
                iterations,
            },
        );
        for repetition in 0..2 {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![instruction.clone()],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let mut features = CostFeatures::default();
            features.field_inv_ops = (iterations as u64) * 2;
            let mut origins = default_origins();
            origins.insert("field_inv_ops".to_string(), FeatureOrigin::EstimatedProxy);
            records.push(new_record(
                BenchmarkKind::FieldArithmetic,
                format!("orthogonal/field-inv/{iterations}"),
                repetition,
                &harness.limits,
                features,
                origins,
                tx,
                vec!["Orthogonal inversion microkernel proxy.".to_string()],
            ));
        }
    }

    let upload_fit_records = records
        .iter()
        .filter(|record| record.label.starts_with("orthogonal/upload-aggregate/"))
        .cloned()
        .collect::<Vec<_>>();
    let account_fit_records = records
        .iter()
        .filter(|record| record.label.starts_with("orthogonal/account-io/"))
        .cloned()
        .collect::<Vec<_>>();
    let field_inv_fit_records = records
        .iter()
        .filter(|record| record.label.starts_with("orthogonal/field-inv/"))
        .cloned()
        .collect::<Vec<_>>();
    let field_inv_failed_runs = field_inv_fit_records
        .iter()
        .filter(|record| record.status != MeasurementStatus::Success)
        .count();

    let upload_model =
        fit_additive_model_for_features(&upload_fit_records, &["upload_bytes", "upload_chunks"])
            .ok();
    let account_io_model = fit_additive_model_for_features(
        &account_fit_records,
        &[
            "ro_account_count",
            "rw_account_count",
            "account_data_bytes_read",
            "account_data_bytes_written",
        ],
    )
    .ok();
    let field_inv_model =
        fit_additive_model_for_features(&field_inv_fit_records, &["field_inv_ops"]).ok();
    let field_inv_model_present = field_inv_model.is_some();

    Ok((
        records.clone(),
        OrthogonalSweepSummary {
            generated_at_utc: Utc::now().to_rfc3339(),
            record_count: records.len(),
            upload_model,
            account_io_model,
            field_inv_model,
            field_inv_failed_runs,
            notes: {
                let mut notes = vec![
                    "Upload sweeps use aggregate records synthesized from full chunked uploads so upload_bytes and upload_chunks can be fit jointly.".to_string(),
                    "Account I/O sweeps were executed against real probe-owned accounts on the local validator.".to_string(),
                    "Field inversion now uses the Winterfell f128 field implementation rather than the earlier hand-rolled exponentiation kernel.".to_string(),
                ];
                let field_inv_total_runs = field_inv_fit_records.len();
                if field_inv_failed_runs == field_inv_total_runs && field_inv_total_runs > 0 {
                    notes.push(format!(
                        "All {field_inv_failed_runs} field inversion sweep runs failed with ProgramFailedToComplete at the current probe settings, so no inversion coefficient was fit in this pass."
                    ));
                } else if field_inv_failed_runs > 0 {
                    notes.push(format!(
                        "{field_inv_failed_runs} of {field_inv_total_runs} field inversion sweep runs still failed under the reduced settings; the fitted inversion coefficient is probe-specific and based only on successful runs."
                    ));
                } else if field_inv_model_present {
                    notes.push(
                        "Field inversion sweep completed without failures using the Winterfell-aligned field implementation, so the recovered coefficient is eligible for spend scoring."
                            .to_string(),
                    );
                }
                notes
            },
        },
    ))
}

fn render_phase1_next_report(
    summary: &Phase1Summary,
    real_verifier: &RealVerifierComparison,
    spend_scores: &[ProfileScoreOutput],
    refined_spend: &RefinedSpendSummary,
    orthogonal: &OrthogonalSweepSummary,
    version_manifest: &VersionManifest,
) -> String {
    let mut lines = Vec::new();
    lines.push("# Phase 1 Follow-on Experiments".to_string());
    lines.push(String::new());
    lines.push("## Goal".to_string());
    lines.push("Run the next serious Phase 1 experiments against the existing scaffold: compare the scorer to a real Winterfell verifier path, score spend-shaped Circle and WHIR profiles, and execute orthogonal sweeps for previously dropped coefficients.".to_string());
    lines.push(String::new());
    lines.push("## Real Verifier Path".to_string());
    lines.push(format!(
        "Measured external `verify_stark` baseline: mean {:.2} CU, median {:.2} CU, min {}, max {} over {} runs.",
        real_verifier.verify_stark_baseline.mean_cu,
        real_verifier.verify_stark_baseline.median_cu,
        real_verifier.verify_stark_baseline.min_cu,
        real_verifier.verify_stark_baseline.max_cu,
        real_verifier.verify_stark_baseline.run_count
    ));
    lines.push(format!(
        "Locally generated proof size: {} bytes; predicted verifier cost: {:.1} CU; measured minus predicted: {:.1} CU ({:.2}% abs error).",
        real_verifier.structure.proof_bytes,
        real_verifier.score.predicted_cu,
        real_verifier.measured_minus_predicted_cu,
        real_verifier.relative_error_fraction * 100.0
    ));
    if let Some(soundness) = &real_verifier.score.query_soundness {
        lines.push(format!(
            "Query soundness for the real verifier profile: {:.1}-{:.1} bits at q={} and blowup {}. The proven lower bound misses the {:.0}-bit target, while the conjectured upper bound lands on it.",
            soundness.lower_bits,
            soundness.upper_bits.unwrap_or(soundness.lower_bits),
            soundness.query_count,
            real_verifier.structure.blowup_factor,
            soundness.target_bits
        ));
    }
    lines.push(format!(
        "Field inversion proxy: prior query-scaled estimate {} -> corrected execution-structure estimate {} (transition divisions {}, boundary-group divisions {}, DEEP batch inversion {}, recursive FRI layer inversions {}).",
        real_verifier.field_inv_diagnostic.prior_query_scaled_proxy,
        real_verifier.field_inv_diagnostic.estimated_total,
        real_verifier.field_inv_diagnostic.ood_transition_divisions,
        real_verifier.field_inv_diagnostic.boundary_constraint_group_divisions,
        real_verifier.field_inv_diagnostic.deep_composer_batch_inversions,
        real_verifier.field_inv_diagnostic.fri_layer_batch_inversions
    ));
    lines.push(format!(
        "Field multiplication proxy audit: dominant remainder Horner multiplications {} + queried x-coordinate lifts {} -> proxy {}. Extension-field multiplications remain {} because this proof stays on Winterfell's base-field path.",
        real_verifier.field_mul_diagnostic.remainder_horner_mul_ops,
        real_verifier.field_mul_diagnostic.query_coordinate_lift_mul_ops,
        real_verifier.field_mul_diagnostic.estimated_total,
        real_verifier.extension_mul_diagnostic.estimated_total
    ));
    if let Some(backsolved) = real_verifier.field_mul_ops_backsolved_for_mean {
        lines.push(format!(
            "Diagnostic backsolve: matching the measured mean under the current additive model would require about {:.1} `field_mul_ops` proxy units.",
            backsolved
        ));
    }
    lines.push("Measured here: proof bytes from a local proof.bin and external verify-only/finalize-only CSV baselines. Inferred here: Merkle levels, account bytes, and verifier-kernel field proxies from proof structure and verifier layout.".to_string());
    lines.push(String::new());
    lines.push("## Base Spend-Screen Scores".to_string());
    for score in spend_scores {
        let contributors = score
            .dominant_contributors
            .iter()
            .map(|item| format!("{} {:.1} CU", item.feature, item.cu))
            .collect::<Vec<_>>()
            .join(", ");
        if let Some(soundness) = &score.query_soundness {
            lines.push(format!(
                "- `{}`: {:.1} CU ({:.3}x budget), feasible={}, query soundness {:.1}-{:.1} bits vs {:.0}-bit target, top contributors: {}.",
                score.name,
                score.predicted_cu,
                score.cu_budget_fraction,
                score.feasible,
                soundness.lower_bits,
                soundness.upper_bits.unwrap_or(soundness.lower_bits),
                soundness.target_bits,
                contributors
            ));
        } else {
            lines.push(format!(
                "- `{}`: {:.1} CU ({:.3}x budget), feasible={}, top contributors: {}.",
                score.name,
                score.predicted_cu,
                score.cu_budget_fraction,
                score.feasible,
                contributors
            ));
        }
    }
    lines.push("These are the raw structured-screen outputs from the base additive model before the orthogonal account-I/O replacement pass. They are derived from an explicit spend-statement arithmetization rather than hand-entered verifier proxy counts, but they remain screening inputs rather than a production circuit.".to_string());
    lines.push("Spend field inversion counts now follow verifier structure in the screening model: transition divisor divisions + boundary constraint groups + DEEP batch inversions + low-degree batch-inversion rounds, rather than scaling directly with q.".to_string());
    lines.push(String::new());
    lines.push("## Query Semantics".to_string());
    lines.push("In the spend sweeps, `q` is a literal absolute proof-query count in the current model. It is not a query-round count, not an internally batched effective-query estimate, and not a hidden security-normalized parameter.".to_string());
    lines.push("Circle now maps q to lower/upper query soundness using official FRI formulas: proven `rate^(q/2)` as the lower bound and conjectured ethSTARK-style `rate^q` as the upper bound, with query grinding bits added directly. WHIR now maps q to lower/upper query soundness using the official Plonky3 WHIR soundness model: Johnson-bound as the lower bound and capacity-bound as the upper bound, with configured PoW bits added directly to the query term.".to_string());
    lines.push("Interpretation: low-q points are no longer unlabeled cost screens; they now fail explicitly because their query-controlled soundness stays far below the 128-bit target.".to_string());
    for item in &refined_spend.query_count_summary {
        lines.push(format!(
            "- q{} sweep envelope: {:.1} to {:.1} CU across all spend-screen scenarios; feasible_points={}.",
            item.query_count, item.min_predicted_cu, item.max_predicted_cu, item.feasible_count
        ));
    }
    lines.push(String::new());
    lines.push("## Security-Qualified Joint Sweep".to_string());
    lines.push("This second sweep varies rate, grinding, security target (100/120/128 bits), and inferred cost scenarios jointly before scoring verifier cost. It is a security-qualified screen, not just a low-q cost sweep.".to_string());
    for record in &refined_spend.security_qualified_best_by_protocol_assumption {
        lines.push(format!(
            "- Best {} / {} / t{:.0} point: `{}` -> scenario `{}`, rate 1/{}, grinding {} bits, q_min {}, q_total {}, {:.1} CU ({:.3}x budget), assumption_feasible={}, lower-bound-feasible={}.",
            record.protocol_family,
            record.soundness_assumption,
            record.security_target_bits,
            record.scenario_name,
            record.cost_scenario_name,
            record.reciprocal_rate,
            record.grinding_bits,
            record.minimum_secure_query_count,
            record.total_explicit_query_count,
            record.predicted_cu,
            record.cu_budget_fraction,
            record.assumption_qualified_feasible,
            record.lower_bound_model_feasible
        ));
    }
    for (key, value) in &refined_spend.security_qualified_feasible_counts {
        lines.push(format!(
            "- Security-qualified feasible points for `{key}`: {value}."
        ));
    }
    lines.push(String::new());
    lines.push("## Refined Spend Scoring".to_string());
    lines.push("Spend rescoring keeps the base additive structure and replaces account-I/O coefficients with orthogonal sweep terms. The inversion coefficient is applied only if the Winterfell-aligned inversion sweep completes without failures.".to_string());
    if let Some(model) = &orthogonal.account_io_model {
        let chosen = &model.chosen;
        let ro = chosen
            .coefficients
            .get("ro_account_count")
            .map(|value| value.estimate)
            .unwrap_or_default();
        let rw = chosen
            .coefficients
            .get("rw_account_count")
            .map(|value| value.estimate)
            .unwrap_or_default();
        let read = chosen
            .coefficients
            .get("account_data_bytes_read")
            .map(|value| value.estimate)
            .unwrap_or_default();
        let written = chosen
            .coefficients
            .get("account_data_bytes_written")
            .map(|value| value.estimate)
            .unwrap_or_default();
        lines.push(format!(
            "Orthogonal account-I/O coefficients used for spend rescoring: ro_account_count {:.3}, rw_account_count {:.3}, account_data_bytes_read {:.6}, account_data_bytes_written {:.6}.",
            ro, rw, read, written
        ));
    }
    if let Some(model) = &orthogonal.field_inv_model {
        if let Some(coefficient) = model.chosen.coefficients.get("field_inv_ops") {
            if orthogonal.field_inv_failed_runs == 0 {
                lines.push(format!(
                    "Recovered inversion coefficient: field_inv_ops {:.3} CU/op from `{}`. It was applied to the refined spend scorer because the Winterfell-aligned inversion sweep completed without failures.",
                    coefficient.estimate, model.chosen.method
                ));
            } else {
                lines.push(format!(
                    "Recovered inversion coefficient: field_inv_ops {:.3} CU/op from `{}`. It was not applied to the refined spend scorer because {} inversion sweep runs still failed.",
                    coefficient.estimate, model.chosen.method, orthogonal.field_inv_failed_runs
                ));
            }
        }
    } else {
        lines.push("Inversion coefficient was not recoverable in the orthogonal pass, so the spend scorer still inherits the base inversion term.".to_string());
    }
    for score in &refined_spend.refined_scores {
        let contributors = score
            .dominant_contributors
            .iter()
            .map(|item| format!("{} {:.1} CU", item.feature, item.cu))
            .collect::<Vec<_>>()
            .join(", ");
        if let Some(soundness) = &score.query_soundness {
            lines.push(format!(
                "- Refined `{}`: {:.1} CU ({:.3}x budget), feasible={}, query soundness {:.1}-{:.1} bits vs {:.0}-bit target, top contributors: {}.",
                score.name,
                score.predicted_cu,
                score.cu_budget_fraction,
                score.feasible,
                soundness.lower_bits,
                soundness.upper_bits.unwrap_or(soundness.lower_bits),
                soundness.target_bits,
                contributors
            ));
        } else {
            lines.push(format!(
                "- Refined `{}`: {:.1} CU ({:.3}x budget), feasible={}, top contributors: {}.",
                score.name,
                score.predicted_cu,
                score.cu_budget_fraction,
                score.feasible,
                contributors
            ));
        }
    }
    for record in &refined_spend.best_by_protocol {
        let feasible_count = refined_spend
            .protocol_feasible_counts
            .get(&record.protocol_family)
            .copied()
            .unwrap_or_default();
        if let Some(soundness) = &record.query_soundness {
            lines.push(format!(
                "- Best {} sweep point: `{}` -> {:.1} CU ({:.3}x budget), feasible={}, feasible_points={}, query soundness {:.1}-{:.1} bits.",
                record.protocol_family,
                record.scenario_name,
                record.predicted_cu,
                record.cu_budget_fraction,
                record.feasible,
                feasible_count,
                soundness.lower_bits,
                soundness.upper_bits.unwrap_or(soundness.lower_bits)
            ));
        } else {
            lines.push(format!(
                "- Best {} sweep point: `{}` -> {:.1} CU ({:.3}x budget), feasible={}, feasible_points={}.",
                record.protocol_family,
                record.scenario_name,
                record.predicted_cu,
                record.cu_budget_fraction,
                record.feasible,
                feasible_count
            ));
        }
    }
    lines.push(String::new());
    lines.push("## Orthogonal Sweeps".to_string());
    lines.push(format!(
        "Executed {} local orthogonal records across aggregate uploads, account I/O, and inversion microkernels.",
        orthogonal.record_count
    ));
    if let Some(model) = &orthogonal.upload_model {
        lines.push(format!(
            "- Upload aggregate fit: `{}`; selected features: {}; RMSE {:.1} CU.",
            model.chosen.method,
            model.chosen.selected_features.join(", "),
            model.chosen.metrics.rmse
        ));
    }
    if let Some(model) = &orthogonal.account_io_model {
        lines.push(format!(
            "- Account I/O fit: `{}`; selected features: {}; RMSE {:.1} CU.",
            model.chosen.method,
            model.chosen.selected_features.join(", "),
            model.chosen.metrics.rmse
        ));
    }
    if let Some(model) = &orthogonal.field_inv_model {
        lines.push(format!(
            "- Field inversion fit: `{}`; selected features: {}; RMSE {:.1} CU.",
            model.chosen.method,
            model.chosen.selected_features.join(", "),
            model.chosen.metrics.rmse
        ));
        lines.push(format!(
            "  Failed inversion runs: {}.",
            orthogonal.field_inv_failed_runs
        ));
    } else {
        lines.push("- Field inversion fit: not recovered in this pass; every inversion microkernel sweep run failed under the current probe settings.".to_string());
    }
    lines.push(String::new());
    lines.push("## Version Manifest".to_string());
    for entry in &version_manifest.executed {
        lines.push(format!("- `{}` -> `{}`", entry.command, entry.output));
    }
    for item in &version_manifest.not_executed {
        lines.push(format!("- Not executed: {item}"));
    }
    lines.push(String::new());
    lines.push("## Baseline Context".to_string());
    lines.push(format!(
        "Base Phase 1 chosen model remains `{}` with RMSE {:.1} CU and p95 abs error {:.1} CU across {} successful records.",
        summary.model.chosen.method,
        summary.model.chosen.metrics.rmse,
        summary.model.chosen.metrics.p95_abs_error,
        summary.model.chosen.metrics.record_count
    ));
    lines.push(String::new());
    lines.push("## Unknowns".to_string());
    lines.push("- The real-verifier comparison still relies on source-backed field-op proxies rather than an instrumented Winterfell verifier kernel.".to_string());
    lines.push("- Cross-version validator drift is recorded but not yet measured across multiple Agave/Solana binaries.".to_string());
    lines.push("- Spend-shaped profiles remain hypothesis inputs until a concrete spend circuit is arithmetized and proved.".to_string());
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} UTC from `cargo xtask phase1-next`._",
        Utc::now().to_rfc3339()
    ));
    lines.join("\n")
}
