use super::*;
use serde::{Deserialize, Serialize};
use std::process::Output;

const WHIR_P3_REPO_URL: &str = "https://github.com/tcoratger/whir-p3";
const WHIR_P3_CHECKOUT: &str = "/tmp/whir-p3-ref";
const BUILDABLE_WHIR_P3_COMMIT: &str = "ade33e7f5900a0f6c763d2793d7e1a5068d0b338";
const BUILDABLE_WHIR_P3_CHECKOUT: &str = "/tmp/whir-p3-ade33e7";
const TRACE_HELPER_FIELD_PROFILE: &str = "babybear5-poseidon2";

#[derive(Clone, Debug, Deserialize)]
struct Phase2RunConfigDoc {
    proof_plan: Phase2ProofPlanSummary,
}

#[derive(Clone, Debug, Deserialize)]
struct Phase2ProofPlanSummary {
    fold_arity: u16,
}

#[derive(Clone, Debug, Deserialize)]
struct Phase2ScenarioOverview {
    name: String,
    log_inv_rate: u64,
    grinding_bits: u32,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    proof_bytes: u32,
    statement_shape: Phase2StatementShapeOverview,
}

#[derive(Clone, Debug, Deserialize)]
struct Phase2StatementShapeOverview {
    evaluation_domain_log2: u16,
}

#[derive(Clone, Debug, Deserialize)]
struct ScenarioDoc {
    name: String,
    config: ScenarioConfig,
    plan: ScenarioPlan,
}

#[derive(Clone, Debug, Deserialize)]
struct ScenarioConfig {
    arithmetic_kernel_id: String,
    extension_kernel_id: String,
    lift_policy: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
}

#[derive(Clone, Debug, Deserialize)]
struct ScenarioPlan {
    target_proof_bytes: u32,
    rounds: Vec<ScenarioRoundPlan>,
}

#[derive(Clone, Debug, Deserialize)]
struct ScenarioRoundPlan {
    merkle_depth: u16,
    ood_samples: u16,
    opening_count: u16,
    query_count: u16,
}

#[derive(Clone, Debug, Serialize)]
struct LocalScenarioSnapshot {
    name: String,
    security_target_bits: f64,
    soundness_assumption: String,
    soundness_assumption_whir_p3: String,
    field_tower: String,
    hash_backend: String,
    log_inv_rate: u64,
    nominal_rate: String,
    evaluation_domain_log2: u16,
    fold_arity: u16,
    grinding_bits: u32,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    merkle_depths: Vec<u16>,
    ood_samples_per_round: Vec<u16>,
    opening_counts_per_round: Vec<u16>,
    target_proof_bytes: u32,
    arithmetic_kernel_id: String,
    extension_kernel_id: String,
    lift_policy: String,
    fold_mode: String,
    merkle_proof_mode: String,
}

#[derive(Clone, Debug, Serialize)]
struct CurrentWhirP3Summary {
    repo_url: String,
    checkout_path: String,
    git_head: String,
    cargo_toml_has_p3_mersenne31: bool,
    cargo_toml_has_sha256_backend: bool,
    cli_field: String,
    cli_extension_field: String,
    cli_hash_backend: String,
    cli_challenger: String,
    cli_mmcs: String,
    cli_rate_flag: String,
    cli_fold_flag: String,
    cli_security_flag: String,
    cli_pow_flag: String,
    cli_initial_rs_reduction_flag: String,
    query_count_control: String,
    proof_serialization: String,
    additional_hash_variants: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct BuildableWhirP3Summary {
    checkout_path: String,
    whir_p3_commit: String,
    plonky3_commit: String,
    cargo_check: CommandCapture,
    api_findings: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct MappingRow {
    scenario: String,
    local_parameter: String,
    local_value: String,
    whir_p3_api: String,
    compatibility: String,
}

#[derive(Clone, Debug, Serialize)]
struct ComparisonSurfaceSummary {
    name: String,
    rationale: String,
    selected_field_profile: String,
    selected_field_profile_rationale: String,
    compared_fields: Vec<String>,
    intentionally_not_compared: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct CommandCapture {
    command: Vec<String>,
    status_code: Option<i32>,
    success: bool,
    stdout: String,
    stderr: String,
}

#[derive(Clone, Debug, Serialize)]
struct LocalStructuralTrace {
    scenario: String,
    field_profile: String,
    soundness_assumption: String,
    target_bits: u64,
    field_size_bits: u64,
    starting_log_inv_rate: u64,
    max_pow_bits: u64,
    num_variables: u64,
    first_round_folding_factor: u64,
    later_round_folding_factor: u64,
    rs_domain_initial_reduction_factor: u64,
    commitment_ood_samples: u64,
    starting_folding_pow_bits_required: u64,
    rounds: Vec<StructuralRoundTrace>,
    final_queries: u64,
    final_query_pow_bits_required: u64,
    final_sumcheck_rounds: u64,
    final_folding_pow_bits_required: u64,
    total_explicit_query_count: u64,
    max_required_pow_bits: u64,
    pow_cap_satisfied: bool,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct StructuralRoundTrace {
    round_index: usize,
    current_log_inv_rate: u64,
    next_log_inv_rate: u64,
    num_variables: u64,
    num_queries: u64,
    ood_samples: u64,
    query_pow_bits_required: u64,
    folding_pow_bits_required: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct WhirP3StructuralTrace {
    scenario: String,
    field_profile: String,
    base_field: String,
    extension_field: String,
    hash_backend: String,
    soundness_assumption: String,
    target_bits: u64,
    field_size_bits: u64,
    starting_log_inv_rate: u64,
    max_pow_bits: u64,
    num_variables: u64,
    first_round_folding_factor: u64,
    later_round_folding_factor: u64,
    rs_domain_initial_reduction_factor: u64,
    commitment_ood_samples: u64,
    starting_folding_pow_bits_required: u64,
    rounds: Vec<StructuralRoundTrace>,
    final_queries: u64,
    final_query_pow_bits_required: u64,
    final_sumcheck_rounds: u64,
    final_folding_pow_bits_required: u64,
    total_explicit_query_count: u64,
    max_required_pow_bits: u64,
    pow_cap_satisfied: bool,
}

#[derive(Clone, Debug, Serialize)]
struct StructuralComparisonRecord {
    scenario: String,
    field_profile: String,
    exact_match: bool,
    compared_field_count: usize,
    divergences: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct StructuralTraceRunSummary {
    field_profile: String,
    attempted: bool,
    helper_command: Vec<String>,
    helper_status_code: Option<i32>,
    helper_success: bool,
    helper_manifest_path: String,
    helper_input_path: String,
    helper_stdout_path: String,
    helper_stderr_path: String,
    helper_status_path: String,
    local_trace_path: String,
    whir_p3_trace_path: String,
    comparison_path: String,
    comparisons: Vec<StructuralComparisonRecord>,
    notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct CrossValidationSummary {
    generated_at_utc: String,
    command: String,
    current_whir_p3: CurrentWhirP3Summary,
    current_main_build_preflight: CommandCapture,
    buildable_pair: BuildableWhirP3Summary,
    local_scenarios: Vec<LocalScenarioSnapshot>,
    parameter_mapping: Vec<MappingRow>,
    comparison_surface: ComparisonSurfaceSummary,
    structural_trace_run: Option<StructuralTraceRunSummary>,
    proof_interop_possible: bool,
    proof_interop_block_reasons: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct TraceHelperInputDoc {
    scenarios: Vec<TraceHelperScenario>,
}

#[derive(Clone, Debug, Serialize)]
struct TraceHelperScenario {
    name: String,
    security_level: usize,
    pow_bits: usize,
    num_variables: usize,
    starting_log_inv_rate: usize,
    first_round_folding_factor: usize,
    later_round_folding_factor: usize,
    rs_domain_initial_reduction_factor: usize,
    soundness_assumption: String,
}

pub(super) fn run_whir_p3_cross_validate() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/whir-p3-compatibility.md");
    let results_root = root.join("results/whir-p3-cross-validation");
    let raw_root = results_root.join("raw");
    fs::create_dir_all(&raw_root)?;

    let main_checkout = ensure_whir_p3_checkout()?;
    let main_git_head = run_command_capture(
        "git",
        &["-C", main_checkout.to_str().unwrap(), "rev-parse", "HEAD"],
    )?;
    let current_whir_p3 = inspect_current_whir_p3(&main_checkout, &main_git_head)?;
    let current_main_build_preflight = run_command_capture_allow_failure(
        "cargo",
        &[
            "check",
            "--manifest-path",
            main_checkout.join("Cargo.toml").to_str().unwrap(),
            "--features",
            "cli",
        ],
        None,
    )?;
    write_command_capture(
        &raw_root,
        "whir-p3-current-main-cargo-check",
        &current_main_build_preflight,
    )?;
    fs::write(
        raw_root.join("whir-p3-current-main-git-head.txt"),
        format!("{main_git_head}\n"),
    )?;

    let buildable_checkout = ensure_buildable_whir_p3_checkout(&main_checkout)?;
    let buildable_git_head = run_command_capture(
        "git",
        &[
            "-C",
            buildable_checkout.to_str().unwrap(),
            "rev-parse",
            "HEAD",
        ],
    )?;
    let buildable_cargo_check = run_command_capture_allow_failure(
        "cargo",
        &[
            "check",
            "--manifest-path",
            buildable_checkout.join("Cargo.toml").to_str().unwrap(),
            "--features",
            "cli",
        ],
        None,
    )?;
    write_command_capture(
        &raw_root,
        "whir-p3-buildable-cargo-check",
        &buildable_cargo_check,
    )?;
    fs::write(
        raw_root.join("whir-p3-buildable-git-head.txt"),
        format!("{buildable_git_head}\n"),
    )?;
    let plonky3_commit = extract_plonky3_commit(
        &fs::read_to_string(buildable_checkout.join("Cargo.lock"))
            .context("failed to read buildable whir-p3 Cargo.lock")?,
    )
    .unwrap_or_else(|| "unknown".to_string());
    fs::write(
        raw_root.join("whir-p3-buildable-plonky3-commit.txt"),
        format!("{plonky3_commit}\n"),
    )?;
    let buildable_pair = BuildableWhirP3Summary {
        checkout_path: buildable_checkout.display().to_string(),
        whir_p3_commit: buildable_git_head,
        plonky3_commit,
        cargo_check: buildable_cargo_check.clone(),
        api_findings: vec![
            "Buildable pair API checked at `src/bin/main.rs`, `src/parameters/mod.rs`, `src/whir/parameters.rs`, and `src/whir/proof.rs`.".to_string(),
            "The checked-in CLI still hardcodes KoalaBear4 + Poseidon2, but the generic `WhirConfig`/`ProtocolParameters` surface is usable from an external helper crate.".to_string(),
            "Round structure is exposed through `WhirConfig::round_parameters`, `final_queries`, `final_pow_bits`, and `final_sumcheck_rounds`.".to_string(),
            "Proof serialization remains serde/bincode over `WhirProof`, so proof-byte interop with the local fixed-layout transcript is still unavailable.".to_string(),
        ],
    };

    let local_scenarios = load_local_scenarios(&root)?;
    write_json(
        &raw_root.join("local-phase2-scenarios.json"),
        &local_scenarios,
    )?;

    let parameter_mapping = build_mapping_rows(&local_scenarios);
    let comparison_surface = ComparisonSurfaceSummary {
        name: "Derived WHIR schedule trace from whir-p3 `WhirConfig`".to_string(),
        rationale: "The first honest overlap is the protocol schedule derivation: OOD sample counts, per-round query counts, per-round PoW requirements, and final-query/final-sumcheck structure. Exact proof bytes, transcript challenges, query indices, and Merkle roots are not compared because the local verifier is SHA-256 + fixed-layout `P2T1`, while whir-p3 is Poseidon/Keccak-capable + serde/bincode.".to_string(),
        selected_field_profile: TRACE_HELPER_FIELD_PROFILE.to_string(),
        selected_field_profile_rationale: "The Phase 2 scenarios in this workspace hard-code a 155-bit screening assumption. The closest buildable whir-p3 generic surface for that exact field-size input is `BinomialExtensionField<BabyBear, 5>`. This is a schedule-level comparison only; it is not an M31 proof-equivalence claim.".to_string(),
        compared_fields: vec![
            "soundness assumption".to_string(),
            "target security bits".to_string(),
            "field_size_bits".to_string(),
            "starting_log_inv_rate".to_string(),
            "max_pow_bits".to_string(),
            "num_variables".to_string(),
            "first/later folding factors".to_string(),
            "commitment OOD samples".to_string(),
            "starting folding PoW bits".to_string(),
            "per-round query counts".to_string(),
            "per-round OOD samples".to_string(),
            "per-round query/folding PoW bits".to_string(),
            "final queries".to_string(),
            "final query PoW bits".to_string(),
            "final sumcheck rounds".to_string(),
            "final folding PoW bits".to_string(),
            "total explicit query count".to_string(),
            "pow-cap satisfied".to_string(),
        ],
        intentionally_not_compared: vec![
            "proof bytes".to_string(),
            "proof object layout".to_string(),
            "Merkle roots".to_string(),
            "Fiat-Shamir challenge bytes".to_string(),
            "query indices".to_string(),
            "opened values".to_string(),
            "host-verifier accept/reject".to_string(),
            "SBF-verifier accept/reject".to_string(),
        ],
    };

    let structural_trace_run = if buildable_pair.cargo_check.success {
        Some(run_structural_trace_comparison(
            &root,
            &raw_root,
            &buildable_checkout,
            &buildable_pair.plonky3_commit,
            &local_scenarios,
        )?)
    } else {
        None
    };

    let mut proof_interop_block_reasons = Vec::new();
    if !current_main_build_preflight.success {
        proof_interop_block_reasons.push(
            "The current whir-p3 main checkout does not build against its declared Plonky3 main dependency set, so there is no stable current-main prover/verifier binary to compare against yet.".to_string(),
        );
    }
    proof_interop_block_reasons.push(
        "The local implementation uses SHA-256 through Solana's syscall path, while the checked-in whir-p3 surfaces are Poseidon-based and tests add Keccak only; transcript bytes and Merkle roots are therefore expected to diverge.".to_string(),
    );
    proof_interop_block_reasons.push(
        "The local proof is a fixed-layout `P2T1` envelope parsed by deterministic offsets, while whir-p3 serializes `WhirProof` via serde/bincode with nested vectors, enums, and options.".to_string(),
    );
    proof_interop_block_reasons.push(
        "The first trace comparison had to target the derived schedule rather than the proof bytes. Matching the local 155-bit Phase 2 screen required a generic `BabyBear` degree-5 helper, not the public M31 path advertised by the reference repository.".to_string(),
    );

    let summary = CrossValidationSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask whir-p3-cross-validate".to_string(),
        current_whir_p3,
        current_main_build_preflight,
        buildable_pair,
        local_scenarios,
        parameter_mapping,
        comparison_surface,
        structural_trace_run,
        proof_interop_possible: false,
        proof_interop_block_reasons,
    };

    write_json(&results_root.join("summary.json"), &summary)?;
    write_json(&raw_root.join("summary.json"), &summary)?;
    fs::write(&docs_path, render_compatibility_doc(&summary))?;
    fs::write(
        results_root.join("first-run.md"),
        render_first_run(&summary),
    )?;
    Ok(())
}

fn inspect_current_whir_p3(checkout: &Path, git_head: &str) -> Result<CurrentWhirP3Summary> {
    let cargo_toml = fs::read_to_string(checkout.join("Cargo.toml"))
        .context("failed to read whir-p3 Cargo.toml")?;
    Ok(CurrentWhirP3Summary {
        repo_url: WHIR_P3_REPO_URL.to_string(),
        checkout_path: checkout.display().to_string(),
        git_head: git_head.to_string(),
        cargo_toml_has_p3_mersenne31: cargo_toml.contains("p3-mersenne"),
        cargo_toml_has_sha256_backend: cargo_toml.to_ascii_lowercase().contains("sha256"),
        cli_field: "KoalaBear".to_string(),
        cli_extension_field: "BinomialExtensionField<KoalaBear, 4>".to_string(),
        cli_hash_backend: "Poseidon2KoalaBear sponge + truncated Poseidon permutation for MMCS"
            .to_string(),
        cli_challenger: "DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>".to_string(),
        cli_mmcs: "MerkleTreeMmcs<PackedF, PackedF, PaddingFreeSponge<Poseidon24>, TruncatedPermutation<Poseidon16>, 2, 8>".to_string(),
        cli_rate_flag: "-r / --rate -> starting_log_inv_rate".to_string(),
        cli_fold_flag: "-k / --fold -> FoldingFactor::Constant(args.folding_factor)".to_string(),
        cli_security_flag: "--sec -> SecurityAssumption::{CapacityBound, JohnsonBound, ...}"
            .to_string(),
        cli_pow_flag: "-p / --pow-bits -> ProtocolParameters::pow_bits".to_string(),
        cli_initial_rs_reduction_flag:
            "--initial-rs-reduction -> rs_domain_initial_reduction_factor".to_string(),
        query_count_control:
            "No direct CLI query-count flag; `WhirProof::from_protocol_parameters` derives capacity from `soundness_type.queries(protocol_security_level, starting_log_inv_rate)`."
                .to_string(),
        proof_serialization:
            "`bincode::serialize(&proof)` over a serde `WhirProof` object".to_string(),
        additional_hash_variants: vec![
            "Keccak test-only path over KoalaBear in `src/whir/mod.rs`.".to_string(),
            "No checked-in SHA-256 MMCS/challenger path found at this commit.".to_string(),
        ],
    })
}

fn ensure_whir_p3_checkout() -> Result<PathBuf> {
    let checkout = PathBuf::from(WHIR_P3_CHECKOUT);
    if checkout.join("Cargo.toml").exists() {
        return Ok(checkout);
    }
    let status = Command::new("git")
        .args(["clone", WHIR_P3_REPO_URL, WHIR_P3_CHECKOUT])
        .status()
        .context("failed to clone whir-p3")?;
    if !status.success() {
        bail!("git clone {} {} failed", WHIR_P3_REPO_URL, WHIR_P3_CHECKOUT);
    }
    Ok(checkout)
}

fn ensure_buildable_whir_p3_checkout(main_checkout: &Path) -> Result<PathBuf> {
    let checkout = PathBuf::from(BUILDABLE_WHIR_P3_CHECKOUT);
    if checkout.join("Cargo.toml").exists() {
        let current = run_command_capture(
            "git",
            &["-C", checkout.to_str().unwrap(), "rev-parse", "HEAD"],
        )?;
        if current != BUILDABLE_WHIR_P3_COMMIT {
            let status = Command::new("git")
                .args([
                    "-C",
                    checkout.to_str().unwrap(),
                    "checkout",
                    BUILDABLE_WHIR_P3_COMMIT,
                ])
                .status()
                .context("failed to checkout pinned buildable whir-p3 commit")?;
            if !status.success() {
                bail!(
                    "failed to checkout pinned buildable commit {} in {}",
                    BUILDABLE_WHIR_P3_COMMIT,
                    checkout.display()
                );
            }
        }
        return Ok(checkout);
    }

    let worktree_status = Command::new("git")
        .args([
            "-C",
            main_checkout.to_str().unwrap(),
            "worktree",
            "add",
            BUILDABLE_WHIR_P3_CHECKOUT,
            BUILDABLE_WHIR_P3_COMMIT,
        ])
        .status();
    if let Ok(status) = worktree_status {
        if status.success() && checkout.join("Cargo.toml").exists() {
            return Ok(checkout);
        }
    }

    let clone_status = Command::new("git")
        .args(["clone", WHIR_P3_REPO_URL, BUILDABLE_WHIR_P3_CHECKOUT])
        .status()
        .context("failed to clone buildable whir-p3 checkout")?;
    if !clone_status.success() {
        bail!(
            "git clone {} {} failed",
            WHIR_P3_REPO_URL,
            BUILDABLE_WHIR_P3_CHECKOUT
        );
    }
    let checkout_status = Command::new("git")
        .args([
            "-C",
            BUILDABLE_WHIR_P3_CHECKOUT,
            "checkout",
            BUILDABLE_WHIR_P3_COMMIT,
        ])
        .status()
        .context("failed to checkout buildable whir-p3 revision")?;
    if !checkout_status.success() {
        bail!(
            "git checkout {} failed in {}",
            BUILDABLE_WHIR_P3_COMMIT,
            BUILDABLE_WHIR_P3_CHECKOUT
        );
    }
    Ok(checkout)
}

fn load_local_scenarios(root: &Path) -> Result<Vec<LocalScenarioSnapshot>> {
    let run_config: Phase2RunConfigDoc = serde_json::from_slice(
        &fs::read(root.join("results/phase2/run_config.json"))
            .context("failed to read results/phase2/run_config.json")?,
    )
    .context("failed to decode results/phase2/run_config.json")?;
    let scenario_overviews: Vec<Phase2ScenarioOverview> = serde_json::from_slice(
        &fs::read(root.join("results/phase2/whir-query/scenarios.json"))
            .context("failed to read results/phase2/whir-query/scenarios.json")?,
    )
    .context("failed to decode results/phase2/whir-query/scenarios.json")?;
    let scenario_map: std::collections::BTreeMap<_, _> = scenario_overviews
        .into_iter()
        .map(|scenario| (scenario.name.clone(), scenario))
        .collect();

    let scenario_files = [
        "results/phase2/whir-query/whir_t100_capacity_full_reference_karatsuba_late.json",
        "results/phase2/whir-query/whir_t128_capacity_full_reference_karatsuba_late.json",
        "results/phase2/whir-query/whir_t128_johnson_full_reference_karatsuba_late.json",
    ];

    let mut snapshots = Vec::with_capacity(scenario_files.len());
    for relative in scenario_files {
        let doc: ScenarioDoc = serde_json::from_slice(
            &fs::read(root.join(relative)).with_context(|| format!("failed to read {relative}"))?,
        )
        .with_context(|| format!("failed to decode {relative}"))?;
        let scenario_name = base_scenario_name(doc.name());
        let overview = scenario_map
            .get(scenario_name)
            .with_context(|| format!("missing scenario overview for {scenario_name}"))?;
        let plan_round_query_counts: Vec<u64> = doc
            .plan
            .rounds
            .iter()
            .filter(|round| round.query_count > 0)
            .map(|round| u64::from(round.query_count))
            .collect();
        if plan_round_query_counts != overview.round_query_counts {
            bail!(
                "round-query mismatch in {relative}: plan has {:?}, overview has {:?}",
                plan_round_query_counts,
                overview.round_query_counts
            );
        }
        if doc.plan.target_proof_bytes != overview.proof_bytes {
            bail!(
                "proof-byte mismatch in {relative}: plan has {}, overview has {}",
                doc.plan.target_proof_bytes,
                overview.proof_bytes
            );
        }
        snapshots.push(LocalScenarioSnapshot {
            name: scenario_name.to_string(),
            security_target_bits: overview.security_target_bits,
            soundness_assumption: overview.soundness_assumption.clone(),
            soundness_assumption_whir_p3: phase2_assumption_whir_p3_name(
                &overview.soundness_assumption,
            )?
            .to_string(),
            field_tower:
                "M31 base field with CM31/QM31 extension arithmetic in the Solana verifier path"
                    .to_string(),
            hash_backend:
                "Solana SHA-256 via `solana_program::hash::hashv` / `sol_sha256` syscall path"
                    .to_string(),
            log_inv_rate: overview.log_inv_rate,
            nominal_rate: format!("1/{}", 1_u64 << overview.log_inv_rate),
            evaluation_domain_log2: overview.statement_shape.evaluation_domain_log2,
            fold_arity: run_config.proof_plan.fold_arity,
            grinding_bits: overview.grinding_bits,
            total_explicit_query_count: overview.total_explicit_query_count,
            round_query_counts: overview.round_query_counts.clone(),
            merkle_depths: doc
                .plan
                .rounds
                .iter()
                .map(|round| round.merkle_depth)
                .collect(),
            ood_samples_per_round: doc
                .plan
                .rounds
                .iter()
                .map(|round| round.ood_samples)
                .collect(),
            opening_counts_per_round: doc
                .plan
                .rounds
                .iter()
                .map(|round| round.opening_count)
                .collect(),
            target_proof_bytes: doc.plan.target_proof_bytes,
            arithmetic_kernel_id: doc.config.arithmetic_kernel_id.clone(),
            extension_kernel_id: doc.config.extension_kernel_id.clone(),
            lift_policy: doc.config.lift_policy.clone(),
            fold_mode: doc.config.whir_fold_mode.clone(),
            merkle_proof_mode: doc.config.merkle_proof_mode.clone(),
        });
    }
    Ok(snapshots)
}

fn base_scenario_name(name: &str) -> &str {
    name.split("_reference_").next().unwrap_or(name)
}

impl ScenarioDoc {
    fn name(&self) -> &str {
        &self.name
    }
}

fn phase2_assumption_whir_p3_name(value: &str) -> Result<&'static str> {
    match value {
        "whir_capacity_full" => Ok("CapacityBound"),
        "whir_johnson_full" => Ok("JohnsonBound"),
        other => bail!("unsupported Phase 2 soundness assumption `{other}`"),
    }
}

fn build_mapping_rows(scenarios: &[LocalScenarioSnapshot]) -> Vec<MappingRow> {
    let mut rows = Vec::new();
    for scenario in scenarios {
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "field tower".to_string(),
            local_value: scenario.field_tower.clone(),
            whir_p3_api: "Current checked-in CLI/examples use `KoalaBear` + `BinomialExtensionField<KoalaBear, 4>`; generic `WhirConfig` can be instantiated from an external helper crate.".to_string(),
            compatibility: "proof-level blocked; schedule-level comparison required a helper crate and a field-size-matched `BinomialExtensionField<BabyBear, 5>` surface because the local Phase 2 screen hard-codes 155 field bits".to_string(),
        });
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "hash / transcript / MMCS".to_string(),
            local_value: scenario.hash_backend.clone(),
            whir_p3_api: "Checked-in surfaces are Poseidon-based; tests add Keccak only."
                .to_string(),
            compatibility: "blocked for proof bytes and transcript data".to_string(),
        });
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "starting rate".to_string(),
            local_value: format!(
                "log_inv_rate={} (nominal rate {})",
                scenario.log_inv_rate, scenario.nominal_rate
            ),
            whir_p3_api: "`ProtocolParameters { starting_log_inv_rate, .. }` or CLI `-r/--rate`"
                .to_string(),
            compatibility: "maps directly".to_string(),
        });
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "folding factor".to_string(),
            local_value: format!(
                "first={}, later={}",
                scenario.fold_arity, scenario.fold_arity
            ),
            whir_p3_api: "`FoldingFactor::ConstantFromSecondRound(first, later)`".to_string(),
            compatibility: "maps for the schedule derivation".to_string(),
        });
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "query schedule".to_string(),
            local_value: format!(
                "total={} with round_query_counts={:?}",
                scenario.total_explicit_query_count, scenario.round_query_counts
            ),
            whir_p3_api: "`WhirConfig::round_parameters[..].num_queries` plus `final_queries` after parameter derivation".to_string(),
            compatibility: "derivable and compared structurally; not a direct CLI input".to_string(),
        });
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "grinding / PoW bits".to_string(),
            local_value: scenario.grinding_bits.to_string(),
            whir_p3_api: "`ProtocolParameters { pow_bits, .. }` or CLI `-p/--pow-bits`".to_string(),
            compatibility: "maps for the schedule derivation".to_string(),
        });
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "soundness assumption".to_string(),
            local_value: scenario.soundness_assumption.clone(),
            whir_p3_api: "`SecurityAssumption::{CapacityBound, JohnsonBound}`".to_string(),
            compatibility: "maps directly".to_string(),
        });
        rows.push(MappingRow {
            scenario: scenario.name.clone(),
            local_parameter: "proof serialization".to_string(),
            local_value: format!(
                "fixed-layout phase2 transcript proof, target_proof_bytes={}",
                scenario.target_proof_bytes
            ),
            whir_p3_api:
                "`bincode::serialize(&proof)` over the serde `WhirProof<F, EF, MT>` object".to_string(),
            compatibility:
                "blocked: byte layout and parser model differ completely, so direct proof interchange is not available".to_string(),
        });
    }
    rows
}

fn run_structural_trace_comparison(
    root: &Path,
    raw_root: &Path,
    buildable_checkout: &Path,
    plonky3_commit: &str,
    local_scenarios: &[LocalScenarioSnapshot],
) -> Result<StructuralTraceRunSummary> {
    let helper_dir = root.join("target/whir-p3-cross-validation/trace-helper");
    write_trace_helper_project(&helper_dir, buildable_checkout, plonky3_commit)?;

    let helper_input = TraceHelperInputDoc {
        scenarios: local_scenarios
            .iter()
            .map(|scenario| TraceHelperScenario {
                name: scenario.name.clone(),
                security_level: scenario.security_target_bits.round() as usize,
                pow_bits: scenario.grinding_bits as usize,
                num_variables: scenario.evaluation_domain_log2 as usize,
                starting_log_inv_rate: scenario.log_inv_rate as usize,
                first_round_folding_factor: scenario.fold_arity as usize,
                later_round_folding_factor: scenario.fold_arity as usize,
                rs_domain_initial_reduction_factor: 1,
                soundness_assumption: scenario.soundness_assumption_whir_p3.clone(),
            })
            .collect(),
    };
    let helper_input_path = raw_root.join("trace-helper.input.json");
    write_json(&helper_input_path, &helper_input)?;

    let helper_manifest_path = helper_dir.join("Cargo.toml");
    let helper_capture = run_command_capture_allow_failure(
        "cargo",
        &[
            "run",
            "--manifest-path",
            helper_manifest_path.to_str().unwrap(),
            "--quiet",
            "--",
            TRACE_HELPER_FIELD_PROFILE,
            helper_input_path.to_str().unwrap(),
        ],
        None,
    )?;
    let helper_stdout_path = raw_root.join("trace-helper.babybear5.stdout.json");
    let helper_stderr_path = raw_root.join("trace-helper.babybear5.stderr.txt");
    let helper_status_path = raw_root.join("trace-helper.babybear5.status.txt");
    fs::write(&helper_stdout_path, &helper_capture.stdout)?;
    fs::write(&helper_stderr_path, &helper_capture.stderr)?;
    fs::write(
        &helper_status_path,
        format!(
            "success={}\nstatus_code={:?}\ncommand={}\n",
            helper_capture.success,
            helper_capture.status_code,
            helper_capture.command.join(" ")
        ),
    )?;

    let local_traces: Vec<LocalStructuralTrace> = local_scenarios
        .iter()
        .map(derive_local_structural_trace)
        .collect::<Result<_>>()?;
    let local_trace_path = raw_root.join("local-structural-traces.json");
    write_json(&local_trace_path, &local_traces)?;

    let mut whir_p3_traces = Vec::new();
    let mut comparisons = Vec::new();
    let mut notes = vec![
        "The selected surface is the derived WHIR schedule, not proof bytes.".to_string(),
        "The helper uses `BinomialExtensionField<BabyBear, 5>` because the local Phase 2 sweep hard-codes a 155-bit field-size assumption.".to_string(),
        "Any exact match reported here is only a formula-level schedule agreement on this surface.".to_string(),
    ];
    if helper_capture.success {
        whir_p3_traces = serde_json::from_str(&helper_capture.stdout)
            .context("failed to decode whir-p3 structural trace helper output")?;
        comparisons = compare_structural_traces(&local_traces, &whir_p3_traces)?;
    } else {
        notes.push(
            "The helper crate did not run successfully, so no structural comparison was produced."
                .to_string(),
        );
    }
    let whir_p3_trace_path = raw_root.join("whir-p3-structural-traces.json");
    write_json(&whir_p3_trace_path, &whir_p3_traces)?;
    let comparison_path = raw_root.join("structural-comparison.json");
    write_json(&comparison_path, &comparisons)?;

    Ok(StructuralTraceRunSummary {
        field_profile: TRACE_HELPER_FIELD_PROFILE.to_string(),
        attempted: true,
        helper_command: helper_capture.command,
        helper_status_code: helper_capture.status_code,
        helper_success: helper_capture.success,
        helper_manifest_path: helper_manifest_path.display().to_string(),
        helper_input_path: helper_input_path.display().to_string(),
        helper_stdout_path: helper_stdout_path.display().to_string(),
        helper_stderr_path: helper_stderr_path.display().to_string(),
        helper_status_path: helper_status_path.display().to_string(),
        local_trace_path: local_trace_path.display().to_string(),
        whir_p3_trace_path: whir_p3_trace_path.display().to_string(),
        comparison_path: comparison_path.display().to_string(),
        comparisons,
        notes,
    })
}

fn derive_local_structural_trace(scenario: &LocalScenarioSnapshot) -> Result<LocalStructuralTrace> {
    let assumption = match scenario.soundness_assumption.as_str() {
        "whir_capacity_full" => WhirSecurityAssumption::Capacity,
        "whir_johnson_full" => WhirSecurityAssumption::Johnson,
        other => bail!("unsupported Phase 2 assumption `{other}`"),
    };
    let derivation = derive_full_whir_security(
        scenario.security_target_bits,
        scenario.log_inv_rate as u32,
        scenario.grinding_bits,
        assumption,
        scenario.evaluation_domain_log2 as u32,
        155,
        scenario.fold_arity as u32,
        scenario.fold_arity as u32,
        1,
    );
    let (_, final_sumcheck_rounds) = whir_round_structure(
        scenario.evaluation_domain_log2 as u32,
        scenario.fold_arity as u32,
        scenario.fold_arity as u32,
    );
    Ok(LocalStructuralTrace {
        scenario: scenario.name.clone(),
        field_profile: "phase2-screen-155bit".to_string(),
        soundness_assumption: scenario.soundness_assumption_whir_p3.clone(),
        target_bits: scenario.security_target_bits.round() as u64,
        field_size_bits: 155,
        starting_log_inv_rate: scenario.log_inv_rate,
        max_pow_bits: scenario.grinding_bits as u64,
        num_variables: scenario.evaluation_domain_log2 as u64,
        first_round_folding_factor: scenario.fold_arity as u64,
        later_round_folding_factor: scenario.fold_arity as u64,
        rs_domain_initial_reduction_factor: 1,
        commitment_ood_samples: derivation.commitment_ood_samples,
        starting_folding_pow_bits_required: derivation.starting_folding_pow_bits_required as u64,
        rounds: derivation
            .rounds
            .iter()
            .map(|round| StructuralRoundTrace {
                round_index: round.round_index,
                current_log_inv_rate: round.current_log_inv_rate as u64,
                next_log_inv_rate: round.next_log_inv_rate as u64,
                num_variables: round.num_variables as u64,
                num_queries: round.num_queries,
                ood_samples: round.ood_samples,
                query_pow_bits_required: round.query_pow_bits_required as u64,
                folding_pow_bits_required: round.folding_pow_bits_required as u64,
            })
            .collect(),
        final_queries: derivation.final_queries,
        final_query_pow_bits_required: derivation.final_query_pow_bits_required as u64,
        final_sumcheck_rounds: final_sumcheck_rounds as u64,
        final_folding_pow_bits_required: derivation.final_folding_pow_bits_required as u64,
        total_explicit_query_count: derivation.total_explicit_query_count,
        max_required_pow_bits: derivation.max_required_pow_bits as u64,
        pow_cap_satisfied: derivation.pow_cap_satisfied,
    })
}

fn compare_structural_traces(
    local_traces: &[LocalStructuralTrace],
    whir_p3_traces: &[WhirP3StructuralTrace],
) -> Result<Vec<StructuralComparisonRecord>> {
    let mut remote_map = std::collections::BTreeMap::new();
    for trace in whir_p3_traces {
        remote_map.insert(trace.scenario.clone(), trace);
    }

    let mut comparisons = Vec::with_capacity(local_traces.len());
    for local in local_traces {
        let mut divergences = Vec::new();
        let Some(remote) = remote_map.get(&local.scenario) else {
            comparisons.push(StructuralComparisonRecord {
                scenario: local.scenario.clone(),
                field_profile: TRACE_HELPER_FIELD_PROFILE.to_string(),
                exact_match: false,
                compared_field_count: 0,
                divergences: vec!["missing whir-p3 structural trace".to_string()],
            });
            continue;
        };

        compare_eq(
            &mut divergences,
            "soundness_assumption",
            &local.soundness_assumption,
            &remote.soundness_assumption,
        );
        compare_eq_u64(
            &mut divergences,
            "target_bits",
            local.target_bits,
            remote.target_bits,
        );
        compare_eq_u64(
            &mut divergences,
            "field_size_bits",
            local.field_size_bits,
            remote.field_size_bits,
        );
        compare_eq_u64(
            &mut divergences,
            "starting_log_inv_rate",
            local.starting_log_inv_rate,
            remote.starting_log_inv_rate,
        );
        compare_eq_u64(
            &mut divergences,
            "max_pow_bits",
            local.max_pow_bits,
            remote.max_pow_bits,
        );
        compare_eq_u64(
            &mut divergences,
            "num_variables",
            local.num_variables,
            remote.num_variables,
        );
        compare_eq_u64(
            &mut divergences,
            "first_round_folding_factor",
            local.first_round_folding_factor,
            remote.first_round_folding_factor,
        );
        compare_eq_u64(
            &mut divergences,
            "later_round_folding_factor",
            local.later_round_folding_factor,
            remote.later_round_folding_factor,
        );
        compare_eq_u64(
            &mut divergences,
            "rs_domain_initial_reduction_factor",
            local.rs_domain_initial_reduction_factor,
            remote.rs_domain_initial_reduction_factor,
        );
        compare_eq_u64(
            &mut divergences,
            "commitment_ood_samples",
            local.commitment_ood_samples,
            remote.commitment_ood_samples,
        );
        compare_eq_u64(
            &mut divergences,
            "starting_folding_pow_bits_required",
            local.starting_folding_pow_bits_required,
            remote.starting_folding_pow_bits_required,
        );
        compare_eq_u64(
            &mut divergences,
            "final_queries",
            local.final_queries,
            remote.final_queries,
        );
        compare_eq_u64(
            &mut divergences,
            "final_query_pow_bits_required",
            local.final_query_pow_bits_required,
            remote.final_query_pow_bits_required,
        );
        compare_eq_u64(
            &mut divergences,
            "final_sumcheck_rounds",
            local.final_sumcheck_rounds,
            remote.final_sumcheck_rounds,
        );
        compare_eq_u64(
            &mut divergences,
            "final_folding_pow_bits_required",
            local.final_folding_pow_bits_required,
            remote.final_folding_pow_bits_required,
        );
        compare_eq_u64(
            &mut divergences,
            "total_explicit_query_count",
            local.total_explicit_query_count,
            remote.total_explicit_query_count,
        );
        compare_eq_u64(
            &mut divergences,
            "max_required_pow_bits",
            local.max_required_pow_bits,
            remote.max_required_pow_bits,
        );
        compare_eq(
            &mut divergences,
            "pow_cap_satisfied",
            &local.pow_cap_satisfied.to_string(),
            &remote.pow_cap_satisfied.to_string(),
        );

        if local.rounds.len() != remote.rounds.len() {
            divergences.push(format!(
                "round_count differs: local={} whir-p3={}",
                local.rounds.len(),
                remote.rounds.len()
            ));
        }
        for (index, (local_round, remote_round)) in
            local.rounds.iter().zip(remote.rounds.iter()).enumerate()
        {
            compare_eq_u64(
                &mut divergences,
                &format!("round[{index}].current_log_inv_rate"),
                local_round.current_log_inv_rate,
                remote_round.current_log_inv_rate,
            );
            compare_eq_u64(
                &mut divergences,
                &format!("round[{index}].next_log_inv_rate"),
                local_round.next_log_inv_rate,
                remote_round.next_log_inv_rate,
            );
            compare_eq_u64(
                &mut divergences,
                &format!("round[{index}].num_variables"),
                local_round.num_variables,
                remote_round.num_variables,
            );
            compare_eq_u64(
                &mut divergences,
                &format!("round[{index}].num_queries"),
                local_round.num_queries,
                remote_round.num_queries,
            );
            compare_eq_u64(
                &mut divergences,
                &format!("round[{index}].ood_samples"),
                local_round.ood_samples,
                remote_round.ood_samples,
            );
            compare_eq_u64(
                &mut divergences,
                &format!("round[{index}].query_pow_bits_required"),
                local_round.query_pow_bits_required,
                remote_round.query_pow_bits_required,
            );
            compare_eq_u64(
                &mut divergences,
                &format!("round[{index}].folding_pow_bits_required"),
                local_round.folding_pow_bits_required,
                remote_round.folding_pow_bits_required,
            );
        }

        comparisons.push(StructuralComparisonRecord {
            scenario: local.scenario.clone(),
            field_profile: remote.field_profile.clone(),
            exact_match: divergences.is_empty(),
            compared_field_count: 17 + local.rounds.len() * 7,
            divergences,
        });
    }
    Ok(comparisons)
}

fn compare_eq(divergences: &mut Vec<String>, label: &str, local: &str, remote: &str) {
    if local != remote {
        divergences.push(format!(
            "{label} differs: local=`{local}` whir-p3=`{remote}`"
        ));
    }
}

fn compare_eq_u64(divergences: &mut Vec<String>, label: &str, local: u64, remote: u64) {
    if local != remote {
        divergences.push(format!("{label} differs: local={local} whir-p3={remote}"));
    }
}

fn write_trace_helper_project(
    helper_dir: &Path,
    buildable_checkout: &Path,
    plonky3_commit: &str,
) -> Result<()> {
    let src_dir = helper_dir.join("src");
    fs::create_dir_all(&src_dir)?;
    let plonky3_rev = short_git_rev(plonky3_commit);
    let cargo_toml = format!(
        r#"[package]
name = "whir-p3-trace-helper"
version = "0.1.0"
edition = "2024"

[workspace]

[dependencies]
anyhow = "1"
serde = {{ version = "1", features = ["derive"] }}
serde_json = "1"
rand = {{ version = "0.9", features = ["small_rng"] }}
whir-p3 = {{ path = "{}" }}
p3-baby-bear = {{ git = "https://github.com/Plonky3/Plonky3.git", rev = "{}" }}
p3-challenger = {{ git = "https://github.com/Plonky3/Plonky3.git", rev = "{}" }}
p3-field = {{ git = "https://github.com/Plonky3/Plonky3.git", rev = "{}" }}
p3-symmetric = {{ git = "https://github.com/Plonky3/Plonky3.git", rev = "{}" }}
"#,
        buildable_checkout.display(),
        plonky3_rev,
        plonky3_rev,
        plonky3_rev,
        plonky3_rev
    );
    fs::write(helper_dir.join("Cargo.toml"), cargo_toml)?;
    fs::write(src_dir.join("main.rs"), trace_helper_source())?;
    Ok(())
}

fn trace_helper_source() -> &'static str {
    r#"use anyhow::{bail, Context, Result};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_field::{extension::BinomialExtensionField, Field};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::{rngs::SmallRng, SeedableRng};
use serde::{Deserialize, Serialize};
use whir_p3::{
    parameters::{errors::SecurityAssumption, FoldingFactor, ProtocolParameters},
    whir::parameters::{InitialPhaseConfig, WhirConfig},
};

type F = BabyBear;
type EF = BinomialExtensionField<F, 5>;
type Poseidon16 = Poseidon2BabyBear<16>;
type Poseidon24 = Poseidon2BabyBear<24>;
type MerkleHash = PaddingFreeSponge<Poseidon24, 24, 16, 8>;
type MerkleCompress = TruncatedPermutation<Poseidon16, 2, 8, 16>;
type MyChallenger = DuplexChallenger<F, Poseidon16, 16, 8>;

#[derive(Clone, Debug, Deserialize)]
struct TraceHelperInputDoc {
    scenarios: Vec<TraceHelperScenario>,
}

#[derive(Clone, Debug, Deserialize)]
struct TraceHelperScenario {
    name: String,
    security_level: usize,
    pow_bits: usize,
    num_variables: usize,
    starting_log_inv_rate: usize,
    first_round_folding_factor: usize,
    later_round_folding_factor: usize,
    rs_domain_initial_reduction_factor: usize,
    soundness_assumption: String,
}

#[derive(Clone, Debug, Serialize)]
struct StructuralRoundTrace {
    round_index: usize,
    current_log_inv_rate: u64,
    next_log_inv_rate: u64,
    num_variables: u64,
    num_queries: u64,
    ood_samples: u64,
    query_pow_bits_required: u64,
    folding_pow_bits_required: u64,
}

#[derive(Clone, Debug, Serialize)]
struct WhirP3StructuralTrace {
    scenario: String,
    field_profile: String,
    base_field: String,
    extension_field: String,
    hash_backend: String,
    soundness_assumption: String,
    target_bits: u64,
    field_size_bits: u64,
    starting_log_inv_rate: u64,
    max_pow_bits: u64,
    num_variables: u64,
    first_round_folding_factor: u64,
    later_round_folding_factor: u64,
    rs_domain_initial_reduction_factor: u64,
    commitment_ood_samples: u64,
    starting_folding_pow_bits_required: u64,
    rounds: Vec<StructuralRoundTrace>,
    final_queries: u64,
    final_query_pow_bits_required: u64,
    final_sumcheck_rounds: u64,
    final_folding_pow_bits_required: u64,
    total_explicit_query_count: u64,
    max_required_pow_bits: u64,
    pow_cap_satisfied: bool,
}

fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let field_profile = args.next().context("missing field profile")?;
    let input_path = args.next().context("missing input path")?;
    if field_profile != "babybear5-poseidon2" {
        bail!("unsupported field profile `{field_profile}`");
    }
    let input: TraceHelperInputDoc = serde_json::from_slice(
        &std::fs::read(&input_path).with_context(|| format!("failed to read {input_path}"))?,
    )
    .with_context(|| format!("failed to decode {input_path}"))?;

    let traces: Vec<WhirP3StructuralTrace> = input
        .scenarios
        .iter()
        .map(build_trace)
        .collect::<Result<_>>()?;
    println!("{}", serde_json::to_string_pretty(&traces)?);
    Ok(())
}

fn build_trace(scenario: &TraceHelperScenario) -> Result<WhirP3StructuralTrace> {
    let assumption = scenario
        .soundness_assumption
        .parse::<SecurityAssumption>()
        .map_err(anyhow::Error::msg)
        .with_context(|| {
            format!(
                "invalid soundness assumption `{}`",
                scenario.soundness_assumption
            )
        })?;
    let mut rng = SmallRng::seed_from_u64(1);
    let poseidon16 = Poseidon16::new_from_rng_128(&mut rng);
    let poseidon24 = Poseidon24::new_from_rng_128(&mut rng);
    let params = WhirConfig::<EF, F, MerkleHash, MerkleCompress, MyChallenger>::new(
        scenario.num_variables,
        ProtocolParameters {
            initial_phase_config: InitialPhaseConfig::WithStatementClassic,
            starting_log_inv_rate: scenario.starting_log_inv_rate,
            rs_domain_initial_reduction_factor: scenario.rs_domain_initial_reduction_factor,
            folding_factor: FoldingFactor::ConstantFromSecondRound(
                scenario.first_round_folding_factor,
                scenario.later_round_folding_factor,
            ),
            soundness_type: assumption,
            security_level: scenario.security_level,
            pow_bits: scenario.pow_bits,
            merkle_hash: MerkleHash::new(poseidon24),
            merkle_compress: MerkleCompress::new(poseidon16),
        },
    );

    let mut current_log_inv_rate = scenario.starting_log_inv_rate;
    let rounds: Vec<StructuralRoundTrace> = params
        .round_parameters
        .iter()
        .enumerate()
        .map(|(round_index, round)| {
            let next_log_inv_rate = current_log_inv_rate
                + (params.folding_factor.at_round(round_index) - params.rs_reduction_factor(round_index));
            let trace = StructuralRoundTrace {
                round_index,
                current_log_inv_rate: current_log_inv_rate as u64,
                next_log_inv_rate: next_log_inv_rate as u64,
                num_variables: round.num_variables as u64,
                num_queries: round.num_queries as u64,
                ood_samples: round.ood_samples as u64,
                query_pow_bits_required: round.pow_bits as u64,
                folding_pow_bits_required: round.folding_pow_bits as u64,
            };
            current_log_inv_rate = next_log_inv_rate;
            trace
        })
        .collect();

    let max_required_pow_bits = std::iter::once(params.starting_folding_pow_bits)
        .chain(
            params
                .round_parameters
                .iter()
                .flat_map(|round| [round.pow_bits, round.folding_pow_bits]),
        )
        .chain([params.final_pow_bits, params.final_folding_pow_bits])
        .max()
        .unwrap_or(0) as u64;

    Ok(WhirP3StructuralTrace {
        scenario: scenario.name.clone(),
        field_profile: "babybear5-poseidon2".to_string(),
        base_field: "BabyBear".to_string(),
        extension_field: "BinomialExtensionField<BabyBear, 5>".to_string(),
        hash_backend: "Poseidon2BabyBear sponge + truncated Poseidon permutation".to_string(),
        soundness_assumption: scenario.soundness_assumption.clone(),
        target_bits: scenario.security_level as u64,
        field_size_bits: EF::bits() as u64,
        starting_log_inv_rate: scenario.starting_log_inv_rate as u64,
        max_pow_bits: scenario.pow_bits as u64,
        num_variables: scenario.num_variables as u64,
        first_round_folding_factor: scenario.first_round_folding_factor as u64,
        later_round_folding_factor: scenario.later_round_folding_factor as u64,
        rs_domain_initial_reduction_factor: scenario.rs_domain_initial_reduction_factor as u64,
        commitment_ood_samples: params.commitment_ood_samples as u64,
        starting_folding_pow_bits_required: params.starting_folding_pow_bits as u64,
        rounds: rounds.clone(),
        final_queries: params.final_queries as u64,
        final_query_pow_bits_required: params.final_pow_bits as u64,
        final_sumcheck_rounds: params.final_sumcheck_rounds as u64,
        final_folding_pow_bits_required: params.final_folding_pow_bits as u64,
        total_explicit_query_count: rounds.iter().map(|round| round.num_queries).sum::<u64>()
            + params.final_queries as u64,
        max_required_pow_bits,
        pow_cap_satisfied: params.check_pow_bits(),
    })
}
"#
}

fn extract_plonky3_commit(cargo_lock: &str) -> Option<String> {
    for line in cargo_lock.lines() {
        let trimmed = line.trim();
        if let Some(rest) =
            trimmed.strip_prefix("source = \"git+https://github.com/Plonky3/Plonky3.git?rev=")
        {
            let (_, suffix) = rest.split_once('#')?;
            return Some(suffix.trim_end_matches('"').to_string());
        }
    }
    None
}

fn short_git_rev(commit: &str) -> &str {
    commit.get(..7).unwrap_or(commit)
}

fn run_command_capture_allow_failure(
    program: &str,
    args: &[&str],
    current_dir: Option<&Path>,
) -> Result<CommandCapture> {
    let mut command = Command::new(program);
    command.args(args);
    if let Some(dir) = current_dir {
        command.current_dir(dir);
    }
    let output: Output = command
        .output()
        .with_context(|| format!("failed to run {program} {}", args.join(" ")))?;
    Ok(CommandCapture {
        command: std::iter::once(program.to_string())
            .chain(args.iter().map(|arg| (*arg).to_string()))
            .collect(),
        status_code: output.status.code(),
        success: output.status.success(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

fn write_command_capture(raw_root: &Path, stem: &str, capture: &CommandCapture) -> Result<()> {
    fs::write(raw_root.join(format!("{stem}.stdout.txt")), &capture.stdout)?;
    fs::write(raw_root.join(format!("{stem}.stderr.txt")), &capture.stderr)?;
    fs::write(
        raw_root.join(format!("{stem}.status.txt")),
        format!(
            "success={}\nstatus_code={:?}\ncommand={}\n",
            capture.success,
            capture.status_code,
            capture.command.join(" ")
        ),
    )?;
    Ok(())
}

fn render_compatibility_doc(summary: &CrossValidationSummary) -> String {
    let mut lines = Vec::new();
    lines.push("# WHIR-p3 Compatibility Analysis".to_string());
    lines.push(String::new());
    lines.push("## Scope".to_string());
    lines.push("This document characterizes whether the current Solana WHIR measurement path in this workspace can be cross-checked against `whir-p3` without modifying either implementation to force agreement.".to_string());
    lines.push(format!(
        "- Reference repository: `{}`.",
        summary.current_whir_p3.repo_url
    ));
    lines.push(format!(
        "- Current-main checkout: `{}` @ `{}`.",
        summary.current_whir_p3.checkout_path, summary.current_whir_p3.git_head
    ));
    lines.push(format!(
        "- Buildable pinned pair: `{}` @ `{}` with Plonky3 `{}`.",
        summary.buildable_pair.checkout_path,
        summary.buildable_pair.whir_p3_commit,
        summary.buildable_pair.plonky3_commit
    ));
    lines.push(String::new());
    lines.push("## Current-main API Findings".to_string());
    lines.push("- Current `whir-p3` main was inspected at `src/lib.rs`, `src/bin/main.rs`, and `src/whir/proof.rs` in the checkout above.".to_string());
    lines.push("- The checked-in CLI surface is KoalaBear4 + Poseidon2. It exposes `security_level`, `pow_bits`, `num_variables`, `rate`, `folding_factor`, `soundness_type`, and `rs_domain_initial_reduction_factor`.".to_string());
    lines.push("- Query count is not a direct CLI input; the proof constructor derives it from the soundness model and rate.".to_string());
    lines.push(
        "- Proof bytes come from serde/bincode over `WhirProof`, not from a fixed-layout envelope."
            .to_string(),
    );
    if !summary.current_whir_p3.cargo_toml_has_p3_mersenne31 {
        lines.push("- The current main `Cargo.toml` does not declare `p3-mersenne-31`, and the public examples are not M31-based.".to_string());
    }
    lines.push(String::new());
    lines.push("## Buildability".to_string());
    lines.push(format!(
        "- Current-main preflight: success=`{}` status_code=`{:?}` via `{}`.",
        summary.current_main_build_preflight.success,
        summary.current_main_build_preflight.status_code,
        summary.current_main_build_preflight.command.join(" ")
    ));
    if !summary
        .current_main_build_preflight
        .stderr
        .trim()
        .is_empty()
    {
        lines.push("- Current-main stderr excerpt:".to_string());
        lines.push("```text".to_string());
        lines.push(
            summary
                .current_main_build_preflight
                .stderr
                .trim()
                .to_string(),
        );
        lines.push("```".to_string());
    }
    lines.push(format!(
        "- Buildable pinned pair preflight: success=`{}` status_code=`{:?}`.",
        summary.buildable_pair.cargo_check.success, summary.buildable_pair.cargo_check.status_code
    ));
    lines.push(String::new());
    lines.push("## Buildable-pair API Findings".to_string());
    for finding in &summary.buildable_pair.api_findings {
        lines.push(format!("- {finding}"));
    }
    lines.push(String::new());
    lines.push("## Local Phase 2 Targets".to_string());
    lines.push("| Scenario | Security bits | Assumption | eval_domain_log2 | log_inv_rate | Grinding bits | Round query counts | Total explicit queries | Target proof bytes |".to_string());
    lines.push("| --- | ---: | --- | ---: | ---: | ---: | --- | ---: | ---: |".to_string());
    for scenario in &summary.local_scenarios {
        lines.push(format!(
            "| {} | {:.0} | {} | {} | {} | {} | {:?} | {} | {} |",
            scenario.name,
            scenario.security_target_bits,
            scenario.soundness_assumption,
            scenario.evaluation_domain_log2,
            scenario.log_inv_rate,
            scenario.grinding_bits,
            scenario.round_query_counts,
            scenario.total_explicit_query_count,
            scenario.target_proof_bytes
        ));
    }
    lines.push(String::new());
    lines.push("## Parameter Mapping Table".to_string());
    lines.push("| Scenario | Local parameter | Local value | whir-p3 API / config | Observed compatibility |".to_string());
    lines.push("| --- | --- | --- | --- | --- |".to_string());
    for row in &summary.parameter_mapping {
        lines.push(format!(
            "| {} | {} | {} | {} | {} |",
            row.scenario, row.local_parameter, row.local_value, row.whir_p3_api, row.compatibility
        ));
    }
    lines.push(String::new());
    lines.push("## Selected Comparison Surface".to_string());
    lines.push(format!("- Surface: {}.", summary.comparison_surface.name));
    lines.push(format!(
        "- Rationale: {}",
        summary.comparison_surface.rationale
    ));
    lines.push(format!(
        "- Selected field profile: `{}`. {}",
        summary.comparison_surface.selected_field_profile,
        summary.comparison_surface.selected_field_profile_rationale
    ));
    lines.push("- Compared fields:".to_string());
    for field in &summary.comparison_surface.compared_fields {
        lines.push(format!("  - {field}"));
    }
    lines.push("- Intentionally not compared:".to_string());
    for field in &summary.comparison_surface.intentionally_not_compared {
        lines.push(format!("  - {field}"));
    }
    lines.push(String::new());
    lines.push("## Structural Trace Run".to_string());
    match &summary.structural_trace_run {
        Some(run) => {
            lines.push(format!(
                "- Helper run success=`{}` status_code=`{:?}` via `{}`.",
                run.helper_success,
                run.helper_status_code,
                run.helper_command.join(" ")
            ));
            for note in &run.notes {
                lines.push(format!("- {note}"));
            }
            if run.helper_success {
                lines.push(String::new());
                lines.push("| Scenario | Exact structural match | Divergence count |".to_string());
                lines.push("| --- | --- | ---: |".to_string());
                for comparison in &run.comparisons {
                    lines.push(format!(
                        "| {} | {} | {} |",
                        comparison.scenario,
                        comparison.exact_match,
                        comparison.divergences.len()
                    ));
                }
                for comparison in &run.comparisons {
                    if !comparison.divergences.is_empty() {
                        lines.push(String::new());
                        lines.push(format!("### {}", comparison.scenario));
                        for divergence in &comparison.divergences {
                            lines.push(format!("- {divergence}"));
                        }
                    }
                }
            }
        }
        None => {
            lines.push("- Structural trace run was not attempted because the pinned buildable pair did not pass preflight.".to_string());
        }
    }
    lines.push(String::new());
    lines.push("## Proof Format Analysis".to_string());
    lines.push("- Local Phase 2 transcript proofs are fixed-layout byte envelopes. The builder writes a `P2T1` header and then packs round plans, roots, query records, Merkle witnesses, and final records at deterministic offsets.".to_string());
    lines.push("- The on-chain parser mirrors that layout exactly, which is good for SBF parsing cost but tightly binds the verifier to the byte format.".to_string());
    lines.push("- `whir-p3` proof bytes are serde/bincode over the `WhirProof` Rust structure, which contains nested vectors, enums, and optional sections.".to_string());
    lines.push("- Even if the same semantics were proven, those byte layouts are not directly interchangeable.".to_string());
    lines.push(String::new());
    lines.push("## Current Status".to_string());
    lines.push("Comparison infrastructure exists at the schedule-trace level. Proof-level interop is still blocked by buildability drift on current main plus field/hash/proof-format differences. No validation claim should be inferred from the structural trace output.".to_string());
    lines.join("\n")
}

fn render_first_run(summary: &CrossValidationSummary) -> String {
    let mut lines = Vec::new();
    lines.push("# First Diagnostic Run".to_string());
    lines.push(String::new());
    lines.push("## What Was Attempted".to_string());
    lines.push(format!(
        "1. Reuse or clone `whir-p3` into `{}` and record current-main commit `{}`.",
        summary.current_whir_p3.checkout_path, summary.current_whir_p3.git_head
    ));
    lines.push(format!(
        "2. Run current-main preflight: `{}`.",
        summary.current_main_build_preflight.command.join(" ")
    ));
    lines.push(format!(
        "3. Pin a buildable `whir-p3` checkout at `{}` with Plonky3 `{}`.",
        summary.buildable_pair.whir_p3_commit, summary.buildable_pair.plonky3_commit
    ));
    lines.push(format!(
        "4. Run buildable-pair preflight: `{}`.",
        summary.buildable_pair.cargo_check.command.join(" ")
    ));
    lines.push("5. Select the first honest shared surface: the derived WHIR schedule trace from `WhirConfig`.".to_string());
    if let Some(run) = &summary.structural_trace_run {
        lines.push(format!(
            "6. Run the trace helper: `{}`.",
            run.helper_command.join(" ")
        ));
    }
    lines.push(String::new());
    lines.push("## Directional Results".to_string());
    lines.push("- `whir-p3 proof -> local SBF verifier`: not attempted. Proof-byte interop is still blocked by hash and envelope mismatches.".to_string());
    lines.push("- `local proof -> whir-p3 verifier`: not attempted. The proof objects are not serialized the same way, and the current comparison stayed at the schedule-trace layer.".to_string());
    match &summary.structural_trace_run {
        Some(run) if run.helper_success => {
            lines.push(
                "- `local schedule derivation -> whir-p3 schedule derivation`: attempted."
                    .to_string(),
            );
            for comparison in &run.comparisons {
                if comparison.exact_match {
                    lines.push(format!(
                        "  - `{}`: no differences in the compared structural fields.",
                        comparison.scenario
                    ));
                } else {
                    lines.push(format!(
                        "  - `{}`: {} structural differences observed.",
                        comparison.scenario,
                        comparison.divergences.len()
                    ));
                }
            }
        }
        Some(run) => {
            lines.push(format!(
                "- `local schedule derivation -> whir-p3 schedule derivation`: attempted, but helper failed with status `{:?}`.",
                run.helper_status_code
            ));
        }
        None => {
            lines.push("- `local schedule derivation -> whir-p3 schedule derivation`: not attempted because the pinned buildable pair did not pass preflight.".to_string());
        }
    }
    lines.push(String::new());
    lines.push("## Exact Observations".to_string());
    lines.push(format!(
        "- Current-main preflight success: `{}` with status code `{:?}`.",
        summary.current_main_build_preflight.success,
        summary.current_main_build_preflight.status_code
    ));
    if !summary
        .current_main_build_preflight
        .stderr
        .trim()
        .is_empty()
    {
        lines.push("- Current-main stderr:".to_string());
        lines.push("```text".to_string());
        lines.push(
            summary
                .current_main_build_preflight
                .stderr
                .trim()
                .to_string(),
        );
        lines.push("```".to_string());
    }
    lines.push(format!(
        "- Buildable-pair preflight success: `{}` with status code `{:?}`.",
        summary.buildable_pair.cargo_check.success, summary.buildable_pair.cargo_check.status_code
    ));
    if let Some(run) = &summary.structural_trace_run {
        lines.push(format!(
            "- Structural helper success: `{}` with status code `{:?}`.",
            run.helper_success, run.helper_status_code
        ));
        if !run.comparisons.is_empty() {
            for comparison in &run.comparisons {
                lines.push(format!(
                    "- `{}` divergences: {}.",
                    comparison.scenario,
                    if comparison.divergences.is_empty() {
                        "none".to_string()
                    } else {
                        comparison.divergences.join("; ")
                    }
                ));
            }
        }
    }
    lines.push(String::new());
    lines.push("## Compatibility Diagnosis".to_string());
    for reason in &summary.proof_interop_block_reasons {
        lines.push(format!("- {reason}"));
    }
    lines.push(String::new());
    lines.push("## Raw Artifacts".to_string());
    lines.push(
        "- `results/whir-p3-cross-validation/raw/whir-p3-current-main-git-head.txt`".to_string(),
    );
    lines.push(
        "- `results/whir-p3-cross-validation/raw/whir-p3-current-main-cargo-check.stdout.txt`"
            .to_string(),
    );
    lines.push(
        "- `results/whir-p3-cross-validation/raw/whir-p3-current-main-cargo-check.stderr.txt`"
            .to_string(),
    );
    lines.push(
        "- `results/whir-p3-cross-validation/raw/whir-p3-buildable-git-head.txt`".to_string(),
    );
    lines.push(
        "- `results/whir-p3-cross-validation/raw/whir-p3-buildable-plonky3-commit.txt`".to_string(),
    );
    lines.push(
        "- `results/whir-p3-cross-validation/raw/whir-p3-buildable-cargo-check.stdout.txt`"
            .to_string(),
    );
    lines.push(
        "- `results/whir-p3-cross-validation/raw/whir-p3-buildable-cargo-check.stderr.txt`"
            .to_string(),
    );
    lines.push("- `results/whir-p3-cross-validation/raw/local-phase2-scenarios.json`".to_string());
    if summary.structural_trace_run.is_some() {
        lines.push("- `results/whir-p3-cross-validation/raw/trace-helper.input.json`".to_string());
        lines.push(
            "- `results/whir-p3-cross-validation/raw/trace-helper.babybear5.stdout.json`"
                .to_string(),
        );
        lines.push(
            "- `results/whir-p3-cross-validation/raw/trace-helper.babybear5.stderr.txt`"
                .to_string(),
        );
        lines.push(
            "- `results/whir-p3-cross-validation/raw/local-structural-traces.json`".to_string(),
        );
        lines.push(
            "- `results/whir-p3-cross-validation/raw/whir-p3-structural-traces.json`".to_string(),
        );
        lines.push(
            "- `results/whir-p3-cross-validation/raw/structural-comparison.json`".to_string(),
        );
    }
    lines.push("- `results/whir-p3-cross-validation/raw/summary.json`".to_string());
    lines.push(String::new());
    lines.push(
        "This is one comparison at one set of parameters. It does not constitute validation."
            .to_string(),
    );
    lines.join("\n")
}
