//! `spend-measure`: the local-validator measurement harness behind the
//! release-certificate measurement inputs.
//!
//! The command builds the production Spend SBF, spawns a local
//! `solana-test-validator`, deploys the binary, uploads and irreversibly
//! finalizes the frozen release proof, measures the literal tag-59 and
//! tag-65 simulation compute over both production marker paths, runs the
//! production mutation and acceptance KATs (committed-unmined rejection,
//! duplicate-nullifier rejection, corruption rollback, the proof-rent
//! refund balance equation, legacy tag-60 retention, and a two-signer
//! race), and writes the two production measurement artifacts read by
//! `spend-release`:
//!
//! - `results/spend/atomic_state_only_spend_acceptance_production_mined.json`
//! - `results/spend/atomic_state_only_spend_mutation_production_mined.json`
//!
//! Every measurement runs against the exact production feature set
//! (`spend-production`). The former diagnostic builds and their
//! `diagnostic-unmined-*` features were removed with the research tree, so
//! this harness records no diagnostic tag-61 ledger; the negative
//! proof-of-work teeth use the committed unmined fixture proof instead of a
//! diagnostic PoW bypass.

use std::{
    fs,
    net::TcpListener,
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use borsh::to_vec;
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_sdk::{
    compute_budget::ComputeBudgetInstruction,
    instruction::{AccountMeta, Instruction},
    native_token::LAMPORTS_PER_SOL,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    transaction::Transaction,
};
// solana-sdk 2.x deprecates the re-export in favor of solana-system-interface;
// keep the single-crate dependency surface for this harness.
#[allow(deprecated)]
use solana_sdk::system_instruction;

use aspis_prover::HOST_HASH;
use aspis_verifier::atomic_payment::{
    atomic_nullifier_address, AtomicPaymentPublicInputs, AtomicPoolStateV1,
    ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT, ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
    ATOMIC_NULLIFIER_MAGIC, ATOMIC_NULLIFIER_MARKER_LEN, ATOMIC_NULLIFIER_VERSION,
    ATOMIC_POOL_STATE_LEN,
};
use aspis_verifier::{AspisInstruction, PROOF_ACCOUNT_HEADER_LEN};

use crate::spend_statement::{load_spend_statement_file, spend_hex, spend_recorded_path};

const UPLOAD_CHUNK_BYTES: usize = 640;
const VERIFY_CU_LIMIT: u32 = 1_400_000;
const HEAP_FRAME_BYTES: u32 = 262_144;

/// Default mined release instance measured when no override is supplied.
const RELEASE_PROOF_PATH: &str = "crates/aspis-prover/fixtures/spend_q18_g37_release.bin";
const RELEASE_STATEMENT_PATH: &str =
    "crates/aspis-prover/fixtures/spend_q18_g37_release.statement.json";

/// Committed unmined negative KAT: identical bytes to the pre-strip research
/// fixture, preserved so the production PoW rejection teeth need no
/// diagnostic build.
const COMMITTED_UNMINED_PROOF_PATH: &str =
    "crates/aspis-prover/fixtures/atomic_state_only_spend_v3_unmined.bin";
const COMMITTED_UNMINED_PROOF_BYTES: usize = 67_327;
const COMMITTED_UNMINED_PROOF_SHA256: &str =
    "a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238";

const PRODUCTION_ONLY_FEATURES: [&str; 1] = ["spend-production"];

/// The forbidden feature list pinned by the release evaluator. Every union of
/// the production alias with one of these (and with all of them at once) must
/// fail to build. The features were deleted from the program manifest with
/// the research tree, so each union now fails at Cargo feature resolution.
const PRODUCTION_FORBIDDEN_FEATURES: [&str; 11] = [
    "diagnostic-unmined-mutation",
    "diagnostic-unmined-profile21-mutation",
    "diagnostic-unmined-profile22-acceptance",
    "diagnostic-unmined-profile22-mutation",
    "diagnostic-unmined-spend-acceptance",
    "diagnostic-unmined-spend-mutation",
    "profile20-mutation-candidate",
    "profile21-integrated-candidate",
    "profile21-mutation-candidate",
    "profile22-integrated-candidate",
    "profile22-mutation-candidate",
];

#[derive(Serialize)]
pub struct CuMarker {
    pub label: String,
    pub remaining: u64,
    pub delta_from_previous: Option<i64>,
}

#[derive(Serialize)]
pub struct SpendAcceptanceLedger {
    pub transaction_setup_cu: u64,
    pub proof_load_cu: u64,
    pub parsed_cu: u64,
    pub transcript_cu: u64,
    pub terminal_cu: u64,
    pub relation_cu: u64,
    pub openings_cu: u64,
    pub layer0_queries_cu: u64,
    pub later_queries_cu: u64,
    pub completion_cu: u64,
    pub wrapper_return_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct SpendAcceptanceSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub proof_path: String,
    pub proof_source_override: bool,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub statement_path: String,
    pub statement_source_override: bool,
    pub statement_sha256: String,
    pub statement_pool_hex: String,
    pub statement_sequence: u64,
    pub canonical_public_input_digest: String,
    pub query_count: u16,
    pub batch_grinding_bits: u8,
    pub final_grinding_bits: u8,
    pub fold_grinding_bits: [u8; 4],
    pub query_selector_candidates: u8,
    pub rank_exhaustion_cap17_bits: f64,
    pub selected_soundness_floor_bits: f64,
    pub coarse_whole_ledger_soundness_floor_bits: f64,
    pub soundness_bookable: bool,
    pub proof_account_finalized_before_verification: bool,
    pub default_tag59_fail_closed_host: bool,
    pub production_api_rejected_unmined_sbf: bool,
    pub production_api_accepted_mined_sbf: bool,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: SpendAcceptanceLedger,
    pub production_mutation_enabled: bool,
    pub notes: Vec<String>,
}

/// Overlap-subtracted ledger for the production Spend binary.
///
/// Tag 65 deliberately has no diagnostic CU markers. Its exact transaction
/// total is therefore reconciled against the exact read-only tag-59 total
/// measured in the same binary and validator configuration. The signed
/// increment contains account validation, statement reconstruction, marker
/// preparation/creation, the mutable-state recheck, the proof-rent refund,
/// and final writes, net of the tag-59 wrapper it replaces.
#[derive(Serialize)]
pub struct SpendProductionMutationLedger {
    pub production_read_only_tag59_cu: u64,
    pub production_tag65_increment_over_tag59_cu: i64,
    pub production_tag65_total_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct SpendProductionMutationPathSummary {
    pub marker_path: &'static str,
    pub proof_accounts_finalized_before_production_verification: bool,
    pub literal_tag59_simulation_cu: u64,
    pub literal_tag65_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub ledger: SpendProductionMutationLedger,
    pub production_unmined_tag59_rejected: bool,
    pub production_unmined_tag59_error: String,
    pub production_unmined_tag65_rejected: bool,
    pub production_unmined_tag65_rollback_green: bool,
    pub production_unmined_tag65_landed_error: String,
    pub production_tag59_accepted_mined_sbf: bool,
    pub production_tag65_clean_simulation_accepted: bool,
    pub production_tag65_simulation_proof_sha256_log_exact: bool,
    pub production_tag65_simulation_logged_proof_sha256: String,
    pub corrupt_proof_rejected_with_transaction_rollback: bool,
    pub corrupt_transaction_landed_error: String,
    pub committed_transition_succeeded: bool,
    pub proof_account_absent_after_success: bool,
    pub proof_refund_lamports: Option<u64>,
    pub refund_transaction_fee_lamports: Option<u64>,
    pub nullifier_funding_lamports: Option<u64>,
    pub refund_balance_equation_exact: Option<bool>,
    pub pool_sequence_advanced_once: bool,
    pub pool_anchor_replaced: bool,
    pub nullifier_marker_written: bool,
    pub duplicate_rejected_without_second_mutation: bool,
    pub concurrent_exactly_one_committed: Option<bool>,
}

#[derive(Serialize)]
pub struct SpendLegacyTag60CompatibilitySummary {
    pub isolated_local_validator_lifecycle: bool,
    pub instruction_wire_ordinal: u8,
    pub proof_account: String,
    pub pool_account: String,
    pub nullifier_account: String,
    pub proof_meta_read_only: bool,
    pub proof_meta_non_signer: bool,
    pub proof_finalized_before_transition: bool,
    pub committed_transition_succeeded: bool,
    pub committed_transaction_cu: u64,
    pub pool_sequence_before: u64,
    pub pool_sequence_after: u64,
    pub pool_sequence_advanced_exactly_once: bool,
    pub pool_anchor_before_hex: String,
    pub pool_anchor_after_hex: String,
    pub pool_anchor_replaced: bool,
    pub nullifier_marker_absent_before: bool,
    pub nullifier_marker_written_exactly: bool,
    pub duplicate_landed_error: String,
    pub duplicate_rejected_as_already_spent: bool,
    pub duplicate_rejected_without_second_mutation: bool,
    pub proof_owner_before: String,
    pub proof_owner_after: String,
    pub proof_owner_retained: bool,
    pub proof_data_bytes: usize,
    pub proof_data_sha256_before: String,
    pub proof_data_sha256_after: String,
    pub proof_data_retained_bit_for_bit: bool,
    pub proof_lamports_before: u64,
    pub proof_lamports_after: u64,
    pub proof_lamports_retained: bool,
    pub proof_account_retained_exactly: bool,
}

#[derive(Serialize)]
pub struct SpendMutationSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub production_instruction_wire_ordinal: u8,
    /// The frozen wire ordinal reserved by the former diagnostic mutation
    /// instruction. Its handler was removed with the research tree; the
    /// ordinal is recorded because the production dispatcher must keep it
    /// fail-closed (see `production_only_tag61_unavailable`).
    pub diagnostic_instruction_wire_ordinal: u8,
    pub finalize_proof_instruction_wire_ordinal: u8,
    pub proof_path: String,
    pub proof_source_override: bool,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub statement_path: String,
    pub statement_source_override: bool,
    pub statement_sha256: String,
    pub statement_pool_hex: String,
    pub statement_sequence: u64,
    pub canonical_public_input_digest: String,
    pub query_count: u16,
    pub batch_grinding_bits: u8,
    pub final_grinding_bits: u8,
    pub fold_grinding_bits: [u8; 4],
    pub production_pow_bypass_exposed: bool,
    pub default_tag65_fail_closed_host: bool,
    pub committed_unmined_proof_path: String,
    pub committed_unmined_proof_bytes: usize,
    pub committed_unmined_proof_sha256: String,
    pub candidate_tag65_rejects_unmined_sbf: bool,
    pub candidate_tag65_accepts_mined_sbf: bool,
    pub candidate_tag65_outcome_matches_pow: bool,
    pub candidate_tag65_rollback_green: bool,
    pub production_only_sbf_features: Vec<&'static str>,
    pub production_only_sbf_bytes: usize,
    pub production_only_sbf_sha256: String,
    pub production_only_mined_override_exercised: bool,
    pub production_only_unmined_tag59_rejected: bool,
    pub production_only_unmined_tag65_rejected: bool,
    pub production_only_unmined_tag65_rollback_green: bool,
    pub production_only_tag59_diagnostic_bit_unavailable: bool,
    pub production_only_tag61_unavailable: bool,
    pub production_alias_forbidden_feature_unions_rejected: bool,
    pub production_alias_forbidden_feature_unions_tested: Vec<String>,
    pub production_legacy_tag60_compatibility: SpendLegacyTag60CompatibilitySummary,
    pub production_paths: Vec<SpendProductionMutationPathSummary>,
    pub soundness_bookable: bool,
    pub complete_view_hvzk_simulator_complete: bool,
    pub production_spend_mutation_enabled: bool,
    pub notes: Vec<String>,
}

struct Validator {
    child: Child,
    rpc_url: String,
}

impl Drop for Validator {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

struct Rpc {
    url: String,
    http: reqwest::blocking::Client,
}

struct SimulationResult {
    units: Option<u64>,
    err: Option<String>,
    logs: Vec<String>,
}

struct LandedTransactionCost {
    fee_lamports: u64,
    account_keys: Vec<Pubkey>,
    pre_balances: Vec<u64>,
    post_balances: Vec<u64>,
}

impl Rpc {
    fn for_validator(validator: &Validator) -> Result<Self> {
        Ok(Self {
            url: validator.rpc_url.clone(),
            http: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()?,
        })
    }

    fn call(&self, method: &str, params: Value) -> Result<Value> {
        let response = self
            .http
            .post(&self.url)
            .json(&json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}))
            .send()
            .with_context(|| format!("rpc {method}"))?;
        let value: Value = response.json()?;
        if let Some(err) = value.get("error") {
            bail!("rpc {method} error: {err}");
        }
        value
            .get("result")
            .cloned()
            .ok_or_else(|| anyhow!("rpc {method}: missing result"))
    }

    fn latest_blockhash(&self) -> Result<solana_sdk::hash::Hash> {
        let result = self.call("getLatestBlockhash", json!([{"commitment": "processed"}]))?;
        let hash = result["value"]["blockhash"]
            .as_str()
            .ok_or_else(|| anyhow!("missing blockhash"))?;
        Ok(hash.parse()?)
    }

    fn airdrop_and_wait(&self, pubkey: &Pubkey, lamports: u64) -> Result<()> {
        self.call(
            "requestAirdrop",
            json!([pubkey.to_string(), lamports, {"commitment": "processed"}]),
        )?;
        let started = Instant::now();
        loop {
            let balance = self.call(
                "getBalance",
                json!([pubkey.to_string(), {"commitment": "processed"}]),
            )?;
            if balance["value"].as_u64().unwrap_or(0) >= lamports {
                return Ok(());
            }
            if started.elapsed() > Duration::from_secs(20) {
                bail!("airdrop timed out");
            }
            thread::sleep(Duration::from_millis(200));
        }
    }

    fn send_and_wait_for_success(&self, tx: &Transaction) -> Result<String> {
        let encoded = BASE64.encode(bincode::serialize(tx)?);
        let sig = self.call(
            "sendTransaction",
            json!([encoded, {"encoding": "base64", "preflightCommitment": "processed"}]),
        )?;
        let sig = sig
            .as_str()
            .ok_or_else(|| anyhow!("missing signature"))?
            .to_string();
        let started = Instant::now();
        loop {
            let statuses = self.call(
                "getSignatureStatuses",
                json!([[sig], {"searchTransactionHistory": false}]),
            )?;
            let status = &statuses["value"][0];
            if !status.is_null() {
                if !status["err"].is_null() {
                    bail!("transaction failed: {}", status["err"]);
                }
                if status["confirmationStatus"].as_str().is_some() {
                    return Ok(sig);
                }
            }
            if started.elapsed() > Duration::from_secs(15) {
                bail!("confirmation timed out");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    fn confirmed_transaction(&self, signature: &str) -> Result<Value> {
        let started = Instant::now();
        loop {
            let result = self.call(
                "getTransaction",
                json!([signature, {"encoding": "json", "commitment": "confirmed", "maxSupportedTransactionVersion": 0}]),
            )?;
            if !result.is_null() {
                return Ok(result);
            }
            if started.elapsed() > Duration::from_secs(15) {
                bail!("confirmed transaction {signature} not found");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    fn send_and_confirm(&self, tx: &Transaction) -> Result<u64> {
        let signature = self.send_and_wait_for_success(tx)?;
        let tx_info = self.confirmed_transaction(&signature);
        Ok(tx_info
            .ok()
            .and_then(|t| t["meta"]["computeUnitsConsumed"].as_u64())
            .unwrap_or(0))
    }

    /// Land a transaction and return its compute, fee, and exact pre/post
    /// balances for the refund balance equation.
    fn send_and_confirm_with_cost(&self, tx: &Transaction) -> Result<LandedTransactionCost> {
        let signature = self.send_and_wait_for_success(tx)?;
        let info = self.confirmed_transaction(&signature)?;
        let meta = &info["meta"];
        let balances = |key: &str| -> Result<Vec<u64>> {
            meta[key]
                .as_array()
                .with_context(|| format!("transaction {signature} omitted {key}"))?
                .iter()
                .map(|value| value.as_u64().context("non-integer balance"))
                .collect()
        };
        let account_keys = info["transaction"]["message"]["accountKeys"]
            .as_array()
            .with_context(|| format!("transaction {signature} omitted accountKeys"))?
            .iter()
            .map(|value| {
                value
                    .as_str()
                    .context("non-string account key")?
                    .parse::<Pubkey>()
                    .context("invalid account key")
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(LandedTransactionCost {
            fee_lamports: meta["fee"]
                .as_u64()
                .with_context(|| format!("transaction {signature} omitted fee"))?,
            account_keys,
            pre_balances: balances("preBalances")?,
            post_balances: balances("postBalances")?,
        })
    }

    /// Submit without preflight and require the transaction to land with an
    /// execution error. This distinguishes ledger rollback from an RPC-side
    /// simulation rejection.
    fn send_and_confirm_failure(&self, tx: &Transaction) -> Result<String> {
        let encoded = BASE64.encode(bincode::serialize(tx)?);
        let sig = self.call(
            "sendTransaction",
            json!([encoded, {
                "encoding": "base64",
                "skipPreflight": true,
                "preflightCommitment": "processed"
            }]),
        )?;
        let sig = sig.as_str().ok_or_else(|| anyhow!("missing signature"))?;
        let started = Instant::now();
        loop {
            let statuses = self.call(
                "getSignatureStatuses",
                json!([[sig], {"searchTransactionHistory": false}]),
            )?;
            let status = &statuses["value"][0];
            if !status.is_null() {
                if !status["err"].is_null() {
                    return Ok(status["err"].to_string());
                }
                if status["confirmationStatus"].as_str().is_some() {
                    bail!("transaction unexpectedly succeeded: {sig}");
                }
            }
            if started.elapsed() > Duration::from_secs(15) {
                bail!("failed transaction confirmation timed out: {sig}");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    fn simulate_verbose(&self, tx: &Transaction) -> Result<SimulationResult> {
        let encoded = BASE64.encode(bincode::serialize(tx)?);
        let result = self.call(
            "simulateTransaction",
            json!([encoded, {"encoding": "base64", "sigVerify": false, "replaceRecentBlockhash": true, "commitment": "processed"}]),
        )?;
        let units = result["value"]["unitsConsumed"].as_u64();
        let logs = result["value"]["logs"]
            .as_array()
            .map(|logs| {
                logs.iter()
                    .filter_map(|log| log.as_str().map(str::to_string))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let err = if result["value"]["err"].is_null() {
            None
        } else {
            Some(format!(
                "{} logs={}",
                result["value"]["err"], result["value"]["logs"]
            ))
        };
        Ok(SimulationResult { units, err, logs })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RpcAccountSnapshot {
    lamports: u64,
    owner: Pubkey,
    data: Vec<u8>,
}

fn rpc_account_snapshot(rpc: &Rpc, address: &Pubkey) -> Result<Option<RpcAccountSnapshot>> {
    let result = rpc.call(
        "getAccountInfo",
        json!([address.to_string(), {"encoding": "base64", "commitment": "processed"}]),
    )?;
    let value = &result["value"];
    if value.is_null() {
        return Ok(None);
    }
    let owner = value["owner"]
        .as_str()
        .ok_or_else(|| anyhow!("account snapshot missing owner"))?
        .parse()?;
    let lamports = value["lamports"]
        .as_u64()
        .ok_or_else(|| anyhow!("account snapshot missing lamports"))?;
    let encoded = value["data"][0]
        .as_str()
        .ok_or_else(|| anyhow!("account snapshot missing base64 data"))?;
    let data = BASE64
        .decode(encoded)
        .context("decode account snapshot base64")?;
    Ok(Some(RpcAccountSnapshot {
        lamports,
        owner,
        data,
    }))
}

fn workspace_root() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    Ok(manifest
        .parent()
        .ok_or_else(|| anyhow!("no workspace root"))?
        .to_path_buf())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn free_ports(count: usize) -> Result<Vec<u16>> {
    // Hold every listener until all ports have been selected so the OS
    // cannot hand the same ephemeral port back to a later request.
    let listeners = (0..count)
        .map(|_| TcpListener::bind("127.0.0.1:0"))
        .collect::<std::io::Result<Vec<_>>>()?;
    listeners
        .iter()
        .map(|listener| Ok(listener.local_addr()?.port()))
        .collect()
}

fn start_validator_with_accounts(
    root: &Path,
    so: &Path,
    accounts: &[(Pubkey, PathBuf)],
) -> Result<Validator> {
    let ledger = root.join(".spend-validator");
    let _ = fs::remove_dir_all(&ledger);
    let ports = free_ports(3)?;
    let (rpc_port, faucet_port, gossip_port) = (ports[0], ports[1], ports[2]);
    let mut command = Command::new("solana-test-validator");
    command
        .env("NO_DNA", "1")
        .arg("--reset")
        .arg("--quiet")
        .arg("--ledger")
        .arg(&ledger)
        .arg("--rpc-port")
        .arg(rpc_port.to_string())
        .arg("--faucet-port")
        .arg(faucet_port.to_string())
        .arg("--gossip-port")
        .arg(gossip_port.to_string())
        .arg("--bpf-program")
        .arg(aspis_verifier::id().to_string())
        .arg(so);
    for (address, path) in accounts {
        command.arg("--account").arg(address.to_string()).arg(path);
    }
    let child = command
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .context("solana-test-validator not found on PATH")?;
    let mut validator = Validator {
        child,
        rpc_url: format!("http://127.0.0.1:{rpc_port}"),
    };
    let rpc = Rpc::for_validator(&validator)?;
    let started = Instant::now();
    loop {
        if rpc.call("getHealth", json!([])).is_ok() {
            break;
        }
        if let Some(status) = validator.child.try_wait()? {
            bail!("validator exited before RPC became healthy: {status}");
        }
        if started.elapsed() > Duration::from_secs(90) {
            bail!("validator did not become healthy");
        }
        thread::sleep(Duration::from_millis(500));
    }
    Ok(validator)
}

fn validator_version() -> String {
    Command::new("solana-test-validator")
        .env("NO_DNA", "1")
        .arg("--version")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|_| "unknown".to_string())
}

fn write_validator_account_fixture(
    root: &Path,
    label: &str,
    address: Pubkey,
    owner: Pubkey,
    data: &[u8],
) -> Result<PathBuf> {
    let directory = root.join(".spend-validator-account-fixtures");
    fs::create_dir_all(&directory)?;
    let path = directory.join(format!("{label}-{address}.json"));
    let account = json!({
        "pubkey": address.to_string(),
        "account": {
            "lamports": 10_000_000u64,
            "data": [BASE64.encode(data), "base64"],
            "owner": owner.to_string(),
            "executable": false,
            "rentEpoch": 0u64,
            "space": data.len(),
        }
    });
    fs::write(&path, serde_json::to_vec_pretty(&account)?)?;
    Ok(path)
}

fn proof_instruction(
    payer: &Pubkey,
    proof_account: &Pubkey,
    instruction: &AspisInstruction,
) -> Result<Instruction> {
    let proof_account_signer = matches!(instruction, AspisInstruction::InitProof { .. });
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![
            AccountMeta::new(*proof_account, proof_account_signer),
            AccountMeta::new_readonly(*payer, true),
        ],
        data: to_vec(instruction)?,
    })
}

fn upload_proof(rpc: &Rpc, payer: &Keypair, proof_account: &Keypair, proof: &[u8]) -> Result<()> {
    let space = PROOF_ACCOUNT_HEADER_LEN + proof.len();
    let rent = rpc.call("getMinimumBalanceForRentExemption", json!([space]))?;
    let rent = rent.as_u64().ok_or_else(|| anyhow!("bad rent"))?;
    let create = system_instruction::create_account(
        &payer.pubkey(),
        &proof_account.pubkey(),
        rent,
        space as u64,
        &aspis_verifier::id(),
    );
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[create],
        Some(&payer.pubkey()),
        &[payer, proof_account],
        blockhash,
    );
    rpc.send_and_confirm(&tx)?;

    let init = proof_instruction(
        &payer.pubkey(),
        &proof_account.pubkey(),
        &AspisInstruction::InitProof {
            total_len: proof.len() as u32,
        },
    )?;
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            init,
        ],
        Some(&payer.pubkey()),
        &[payer, proof_account],
        blockhash,
    );
    rpc.send_and_confirm(&tx)?;

    for (i, chunk) in proof.chunks(UPLOAD_CHUNK_BYTES).enumerate() {
        let upload = proof_instruction(
            &payer.pubkey(),
            &proof_account.pubkey(),
            &AspisInstruction::UploadChunk {
                offset: (i * UPLOAD_CHUNK_BYTES) as u32,
                chunk: chunk.to_vec(),
            },
        )?;
        let blockhash = rpc.latest_blockhash()?;
        let tx = Transaction::new_signed_with_payer(
            &[upload],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        rpc.send_and_confirm(&tx)?;
    }
    Ok(())
}

fn finalize_proof(rpc: &Rpc, payer: &Keypair, proof_account: &Pubkey) -> Result<u64> {
    let finalize = proof_instruction(
        &payer.pubkey(),
        proof_account,
        &AspisInstruction::FinalizeProof,
    )?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            finalize,
        ],
        Some(&payer.pubkey()),
        &[payer],
        rpc.latest_blockhash()?,
    );
    rpc.send_and_confirm(&transaction)
}

fn upload_finalized_proof_account(
    rpc: &Rpc,
    payer: &Keypair,
    proof: &[u8],
) -> Result<(Keypair, RpcAccountSnapshot)> {
    let proof_account = Keypair::new();
    upload_proof(rpc, payer, &proof_account, proof)?;
    finalize_proof(rpc, payer, &proof_account.pubkey())?;
    let snapshot = rpc_account_snapshot(rpc, &proof_account.pubkey())?
        .context("finalized Spend proof account missing")?;
    Ok((proof_account, snapshot))
}

fn parse_cu_markers(logs: &[String], marker_prefix: &str) -> Vec<CuMarker> {
    let mut pending: Option<String> = None;
    let mut previous: Option<u64> = None;
    let mut markers = Vec::new();
    for log in logs {
        if let Some((_, suffix)) = log.split_once(marker_prefix) {
            pending = Some(suffix.trim().to_string());
            continue;
        }
        let Some((_, rest)) = log.split_once("Program consumption:") else {
            continue;
        };
        let Some(label) = pending.take() else {
            continue;
        };
        let Some(remaining) = rest
            .split_whitespace()
            .find_map(|token| token.parse::<u64>().ok())
        else {
            continue;
        };
        let delta_from_previous = previous.map(|prev| prev as i64 - remaining as i64);
        previous = Some(remaining);
        markers.push(CuMarker {
            label,
            remaining,
            delta_from_previous,
        });
    }
    markers
}

/// Build the deployable Spend binary in the same Cargo feature context as a
/// plain package-default deployment, while redundantly naming the reviewed
/// production alias for artifact provenance. `spend-production` is the
/// manifest default, so the pinned copy is byte-identical to the plain
/// default build the release evaluator rebuilds and compares.
fn build_spend_production_sbf(root: &Path) -> Result<PathBuf> {
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .arg("--manifest-path")
        .arg(root.join("programs/aspis-verifier/Cargo.toml"))
        .arg("--features")
        .arg(PRODUCTION_ONLY_FEATURES.join(","))
        .status()
        .context("cargo-build-sbf not found on PATH — install the Solana toolchain")?;
    if !status.success() {
        bail!("cargo-build-sbf for the Spend production alias failed");
    }
    let built = root.join("target/deploy/aspis_verifier.so");
    if !built.exists() {
        bail!("missing {}", built.display());
    }
    let pinned = root.join("target/deploy/aspis_verifier_spend_production.so");
    fs::copy(&built, &pinned)
        .with_context(|| format!("pin Spend production SBF {}", pinned.display()))?;
    Ok(pinned)
}

/// Prove that the production alias cannot be feature-unified with a PoW
/// bypass or a superseded-profile candidate. The forbidden features were
/// deleted from the program manifest with the research tree, so every union
/// must now fail Cargo feature resolution before any code is compiled. Each
/// union is checked independently so one working guard cannot hide a missing
/// guard, plus one grouped invocation.
fn check_spend_production_feature_isolation(root: &Path) -> Result<Vec<String>> {
    const PRODUCTION_ALIAS: &str = "spend-production";

    fn require_feature_resolution_failure(
        root: &Path,
        enabled_features: &str,
        forbidden: &[&str],
        label: &str,
    ) -> Result<()> {
        let output = Command::new("cargo")
            .env("NO_DNA", "1")
            .current_dir(root)
            .args([
                "check",
                "-q",
                "-p",
                "aspis-verifier",
                "--no-default-features",
                "--features",
                enabled_features,
            ])
            .output()
            .with_context(|| format!("run Spend feature-isolation tooth {label}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        ensure!(
            !output.status.success(),
            "forbidden Spend feature union unexpectedly compiled: {label}"
        );
        let mentions_forbidden_feature = forbidden
            .iter()
            .any(|feature| stdout.contains(feature) || stderr.contains(feature));
        ensure!(
            mentions_forbidden_feature,
            "Spend feature union {label} failed for an unrelated reason; expected Cargo to reject an absent forbidden feature; stdout={stdout}; stderr={stderr}"
        );
        Ok(())
    }

    let mut tested = Vec::with_capacity(PRODUCTION_FORBIDDEN_FEATURES.len() + 1);
    for forbidden in PRODUCTION_FORBIDDEN_FEATURES {
        let label = format!("{PRODUCTION_ALIAS}+{forbidden}");
        let enabled = format!("{PRODUCTION_ALIAS},{forbidden}");
        require_feature_resolution_failure(root, &enabled, &[forbidden], &label)?;
        tested.push(label);
    }
    let all_forbidden = PRODUCTION_FORBIDDEN_FEATURES.join(",");
    let enabled = format!("{PRODUCTION_ALIAS},{all_forbidden}");
    let label = format!("{PRODUCTION_ALIAS}+all-forbidden");
    require_feature_resolution_failure(root, &enabled, &PRODUCTION_FORBIDDEN_FEATURES, &label)?;
    tested.push(label);
    Ok(tested)
}

/// The committed unmined KAT's own public statement. The fixture proof was
/// generated against this exact synthetic statement; the constants are frozen
/// with the fixture bytes.
fn committed_unmined_kat_statement() -> Result<aspis_statement::AtomicPaymentStatementV3> {
    use aspis_core::field::M31;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment, Digest, MerklePath,
        SpendPublic,
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
        index: 0x5_a5a5,
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    Ok(aspis_statement::AtomicPaymentStatementV3 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &path)
                .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &path)
            .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
    })
}

fn spend_public_bytes(public: &aspis_statement::SpendPublic) -> [u8; 104] {
    let mut output = [0u8; 104];
    for (index, value) in public
        .anchor
        .iter()
        .chain(&public.nullifier)
        .chain(&public.output_commitment)
        .chain(core::iter::once(&public.asset_id))
        .enumerate()
    {
        output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    output[100..].copy_from_slice(&public.fee.to_le_bytes());
    output
}

fn public_inputs(
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> AtomicPaymentPublicInputs {
    use aspis_statement::encode_digest_canonical;
    AtomicPaymentPublicInputs {
        current_anchor: encode_digest_canonical(&statement.spend.anchor),
        nullifier: encode_digest_canonical(&statement.spend.nullifier),
        output_commitment: encode_digest_canonical(&statement.spend.output_commitment),
        output_anchor: encode_digest_canonical(&statement.output_anchor),
        asset_id: statement.spend.asset_id.0,
        fee: statement.spend.fee,
    }
}

/// Wire tag 59: read-only production verification.
fn read_only_instruction(
    proof: Pubkey,
    statement: &aspis_statement::AtomicPaymentStatementV3,
    diagnostic_unmined: bool,
) -> Result<Instruction> {
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![AccountMeta::new_readonly(proof, false)],
        data: to_vec(&AspisInstruction::VerifyAtomicStateOnlySpendV3 {
            pool: statement.pool,
            sequence: statement.sequence,
            public_input: spend_public_bytes(&statement.spend),
            output_anchor: aspis_statement::encode_digest_canonical(&statement.output_anchor),
            diagnostic_unmined,
        })?,
    })
}

/// Wire tag 60: the legacy proof-retaining transition.
fn legacy_tag60_transition_instruction(
    proof: Pubkey,
    pool: Pubkey,
    marker: Pubkey,
    payer: Pubkey,
    public: &AtomicPaymentPublicInputs,
) -> Result<Instruction> {
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![
            AccountMeta::new_readonly(proof, false),
            AccountMeta::new(pool, false),
            AccountMeta::new(marker, false),
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(solana_sdk::system_program::id(), false),
        ],
        data: to_vec(&AspisInstruction::ApplyAtomicStateOnlySpendV3 {
            current_anchor: public.current_anchor,
            nullifier: public.nullifier,
            output_commitment: public.output_commitment,
            output_anchor: public.output_anchor,
            asset_id: public.asset_id,
            fee: public.fee,
        })?,
    })
}

fn tag65_wire(public: &AtomicPaymentPublicInputs) -> Result<Vec<u8>> {
    Ok(to_vec(
        &AspisInstruction::ApplyAtomicStateOnlySpendV3WithProofRefund {
            current_anchor: public.current_anchor,
            nullifier: public.nullifier,
            output_commitment: public.output_commitment,
            output_anchor: public.output_anchor,
            asset_id: public.asset_id,
            fee: public.fee,
        },
    )?)
}

fn tag61_wire(public: &AtomicPaymentPublicInputs) -> Result<Vec<u8>> {
    Ok(to_vec(
        &AspisInstruction::MeasureAtomicStateOnlySpendMutationV3 {
            current_anchor: public.current_anchor,
            nullifier: public.nullifier,
            output_commitment: public.output_commitment,
            output_anchor: public.output_anchor,
            asset_id: public.asset_id,
            fee: public.fee,
        },
    )?)
}

/// Wire tag 65 (`fail_closed_tag61=false`) or the frozen fail-closed tag 61
/// ordinal (`fail_closed_tag61=true`), with the shared five-account frame.
fn transition_instruction(
    proof: Pubkey,
    pool: Pubkey,
    marker: Pubkey,
    payer: Pubkey,
    public: &AtomicPaymentPublicInputs,
    fail_closed_tag61: bool,
) -> Result<Instruction> {
    let (proof_meta, data) = if fail_closed_tag61 {
        (AccountMeta::new_readonly(proof, false), tag61_wire(public)?)
    } else {
        (AccountMeta::new(proof, true), tag65_wire(public)?)
    };
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![
            proof_meta,
            AccountMeta::new(pool, false),
            AccountMeta::new(marker, false),
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(solana_sdk::system_program::id(), false),
        ],
        data,
    })
}

/// The measured transaction frame: SetComputeUnitLimit(1,400,000) +
/// RequestHeapFrame(262,144) + one program instruction.
fn signed_read_only(
    payer: &Keypair,
    instruction: Instruction,
    blockhash: solana_sdk::hash::Hash,
) -> Transaction {
    Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            instruction,
        ],
        Some(&payer.pubkey()),
        &[payer],
        blockhash,
    )
}

fn signed_transition(
    payer: &Keypair,
    proof_account: &Keypair,
    instruction: Instruction,
    blockhash: solana_sdk::hash::Hash,
) -> Transaction {
    Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            instruction,
        ],
        Some(&payer.pubkey()),
        &[payer, proof_account],
        blockhash,
    )
}

fn marker_is_exact(snapshot: &RpcAccountSnapshot, pool: Pubkey, nullifier: &[u8; 32]) -> bool {
    snapshot.owner == aspis_verifier::id()
        && snapshot.data.len() == ATOMIC_NULLIFIER_MARKER_LEN
        && snapshot.data[0..4] == ATOMIC_NULLIFIER_MAGIC
        && snapshot.data[4] == ATOMIC_NULLIFIER_VERSION
        && snapshot.data[5..8] == [0u8; 3]
        && snapshot.data[8..40] == pool.to_bytes()
        && snapshot.data[40..72] == *nullifier
}

/// Read a proof-independent theorem artifact from `results/spend`, falling
/// back to the committed byte-identical copy under `xtask/fixtures` when the
/// results tree has not been populated yet.
fn read_theorem_artifact(root: &Path, name: &str) -> Result<Value> {
    let results_path = root.join("results/spend").join(name);
    let path = if results_path.is_file() {
        results_path
    } else {
        root.join("xtask/fixtures").join(name)
    };
    let bytes = fs::read(&path).with_context(|| format!("read {}", path.display()))?;
    serde_json::from_slice(&bytes).with_context(|| format!("parse {}", path.display()))
}

struct SelectedInstance {
    recorded_proof_path: String,
    proof: Vec<u8>,
    proof_sha256: String,
    recorded_statement_path: String,
    statement: aspis_statement::AtomicPaymentStatementV3,
    statement_sha256: String,
    canonical_public_input_digest: String,
    command: String,
}

/// Select the measured proof and canonical statement sidecar. The harness
/// measures an explicitly named mined instance; without overrides it uses the
/// frozen release fixture pair. `proof_source_override` and
/// `statement_source_override` record that the measured pair was explicitly
/// selected rather than any built-in synthetic statement.
fn select_instance(root: &Path) -> Result<SelectedInstance> {
    let proof_setting =
        std::env::var("ASPIS_SPEND_PROOF").unwrap_or_else(|_| RELEASE_PROOF_PATH.to_string());
    let statement_setting = std::env::var("ASPIS_SPEND_STATEMENT")
        .unwrap_or_else(|_| RELEASE_STATEMENT_PATH.to_string());

    let proof_path = {
        let path = PathBuf::from(&proof_setting);
        if path.is_absolute() {
            path
        } else {
            root.join(path)
        }
    };
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read Spend proof {}", proof_path.display()))?;
    let proof_sha256 = hex(&Sha256::digest(&proof));
    let recorded_proof_path = proof_path
        .strip_prefix(root)
        .unwrap_or(&proof_path)
        .display()
        .to_string();

    let statement_file = load_spend_statement_file(root, Path::new(&statement_setting))?;
    let recorded_statement_path = spend_recorded_path(root, &statement_file.path);

    let command = format!(
        "ASPIS_SPEND_PROOF={recorded_proof_path} ASPIS_SPEND_STATEMENT={recorded_statement_path} NO_DNA=1 cargo run --release -p aspis-xtask -- spend-measure"
    );
    Ok(SelectedInstance {
        recorded_proof_path,
        proof,
        proof_sha256,
        recorded_statement_path,
        statement: statement_file.statement,
        statement_sha256: statement_file.sha256,
        canonical_public_input_digest: statement_file.canonical_public_input_digest,
        command,
    })
}

struct AcceptanceLedgerBuckets;

impl AcceptanceLedgerBuckets {
    fn build(markers: &[CuMarker], total: u64) -> Option<SpendAcceptanceLedger> {
        let delta = |label: &str| -> Option<u64> {
            markers
                .iter()
                .find(|marker| marker.label == label)?
                .delta_from_previous?
                .try_into()
                .ok()
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.first()?.remaining)?;
        let proof_load = delta("atomic59_proof_loaded")?;
        let parsed = delta("atomic59_parsed")?;
        let transcript = delta("atomic59_transcript")?;
        let terminal = delta("atomic59_terminal")?;
        let relation = delta("atomic59_relation")?;
        let openings = delta("atomic59_openings")?;
        let layer0_queries = delta("atomic59_layer0_queries")?;
        let later_queries = delta("atomic59_later_queries")?;
        let completion = delta("atomic59_core_complete")?;
        let wrapper_return = delta("atomic59_done")?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.last()?.remaining)?;
        let post = total.checked_sub(through_last)?;
        let buckets = [
            setup,
            proof_load,
            parsed,
            transcript,
            terminal,
            relation,
            openings,
            layer0_queries,
            later_queries,
            completion,
            wrapper_return,
            post,
        ];
        Some(SpendAcceptanceLedger {
            transaction_setup_cu: setup,
            proof_load_cu: proof_load,
            parsed_cu: parsed,
            transcript_cu: transcript,
            terminal_cu: terminal,
            relation_cu: relation,
            openings_cu: openings,
            layer0_queries_cu: layer0_queries,
            later_queries_cu: later_queries,
            completion_cu: completion,
            wrapper_return_cu: wrapper_return,
            post_last_marker_cu: post,
            reconciled_total_cu: buckets.iter().sum(),
            formula: buckets
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(" + "),
        })
    }
}

/// One production marker path: the complete tag-59/tag-65 measurement plus
/// every negative and commit tooth, in its own validator lifecycle.
#[allow(clippy::too_many_lines)]
fn run_production_path(
    root: &Path,
    so: &Path,
    instance: &SelectedInstance,
    unmined_proof: &[u8],
    preowned_marker: bool,
    exercise_concurrency: bool,
) -> Result<(SpendProductionMutationPathSummary, bool, bool)> {
    let statement = &instance.statement;
    let proof = instance.proof.as_slice();
    let public = public_inputs(statement);
    let pool_key = Pubkey::new_from_array(statement.pool);
    let (marker_key, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
    let mut pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV1 {
        sequence: statement.sequence,
        anchor: public.current_anchor,
    }
    .encode(&mut pool_bytes)
    .map_err(|error| anyhow!("encode Spend pool fixture: {error:?}"))?;
    let pool_fixture = write_validator_account_fixture(
        root,
        if preowned_marker {
            "atomic-spend-production-program-pool"
        } else {
            "atomic-spend-production-system-pool"
        },
        pool_key,
        aspis_verifier::id(),
        &pool_bytes,
    )?;
    let mut fixtures = vec![(pool_key, pool_fixture)];
    if preowned_marker {
        fixtures.push((
            marker_key,
            write_validator_account_fixture(
                root,
                "atomic-spend-production-program-marker",
                marker_key,
                aspis_verifier::id(),
                &[0u8; ATOMIC_NULLIFIER_MARKER_LEN],
            )?,
        ));
    }

    let validator = start_validator_with_accounts(root, so, &fixtures)?;
    let rpc = Rpc::for_validator(&validator)?;
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
    let (proof_account, production_proof_before) =
        upload_finalized_proof_account(&rpc, &payer, proof)?;
    let (unmined_proof_account, unmined_proof_before) =
        upload_finalized_proof_account(&rpc, &payer, unmined_proof)?;

    let pool_before = rpc_account_snapshot(&rpc, &pool_key)?
        .context("preloaded production Spend pool account missing")?;
    let marker_before = rpc_account_snapshot(&rpc, &marker_key)?;
    if preowned_marker {
        ensure!(
            marker_before.as_ref().is_some_and(|snapshot| {
                snapshot.owner == aspis_verifier::id()
                    && snapshot.data == [0u8; ATOMIC_NULLIFIER_MARKER_LEN]
            }),
            "production Spend program marker fixture drift"
        );
    } else {
        ensure!(
            marker_before.is_none(),
            "production Spend System marker already exists"
        );
    }

    // The negative production-PoW teeth: the committed unmined KAT lives in a
    // distinct sealed proof account, so both outcomes are measured against
    // the same production SBF without any diagnostic build.
    let production_unmined_tag59 = rpc.simulate_verbose(&signed_read_only(
        &payer,
        read_only_instruction(unmined_proof_account.pubkey(), statement, false)?,
        rpc.latest_blockhash()?,
    ))?;
    let production_unmined_tag59_error = production_unmined_tag59
        .err
        .clone()
        .context("production tag59 accepted the committed unmined KAT")?;
    let production_unmined_tag59_rejected = true;

    let production_unmined_tag65 = signed_transition(
        &payer,
        &unmined_proof_account,
        transition_instruction(
            unmined_proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            false,
        )?,
        rpc.latest_blockhash()?,
    );
    let production_unmined_tag65_landed_error =
        rpc.send_and_confirm_failure(&production_unmined_tag65)?;
    let production_unmined_tag65_rejected = true;
    let production_unmined_tag65_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref()
        == Some(&pool_before)
        && rpc_account_snapshot(&rpc, &marker_key)? == marker_before
        && rpc_account_snapshot(&rpc, &unmined_proof_account.pubkey())?.as_ref()
            == Some(&unmined_proof_before);
    ensure!(
        production_unmined_tag65_rollback,
        "unmined production tag65 changed state"
    );

    // Negative wire-surface teeth. The same mined bytes must succeed on
    // production tags 59/65 immediately afterwards.
    let diagnostic_tag59 = rpc.simulate_verbose(&signed_read_only(
        &payer,
        read_only_instruction(proof_account.pubkey(), statement, true)?,
        rpc.latest_blockhash()?,
    ))?;
    let tag59_diagnostic_bit_unavailable = diagnostic_tag59
        .err
        .as_deref()
        .is_some_and(|error| error.contains("InvalidInstructionData"));
    ensure!(
        tag59_diagnostic_bit_unavailable,
        "production SBF exposed tag59 diagnostic_unmined or returned the wrong error: {:?}",
        diagnostic_tag59.err
    );
    let unavailable_tag61 = rpc.simulate_verbose(&signed_read_only(
        &payer,
        transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            true,
        )?,
        rpc.latest_blockhash()?,
    ))?;
    let expected_tag61_error = format!("\"Custom\":{ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED}");
    let tag61_unavailable = unavailable_tag61
        .err
        .as_deref()
        .is_some_and(|error| error.contains(&expected_tag61_error))
        && unavailable_tag61
            .logs
            .iter()
            .all(|log| !log.contains("aspis-cu:atomic61_instruction_start"));
    ensure!(
        tag61_unavailable,
        "production SBF exposed tag61 or returned the wrong error: {:?}",
        unavailable_tag61.err
    );
    ensure!(
        rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_before)
            && rpc_account_snapshot(&rpc, &marker_key)? == marker_before
            && rpc_account_snapshot(&rpc, &proof_account.pubkey())?.as_ref()
                == Some(&production_proof_before),
        "unavailable diagnostic surface changed state"
    );

    let production_tag59 = rpc.simulate_verbose(&signed_read_only(
        &payer,
        read_only_instruction(proof_account.pubkey(), statement, false)?,
        rpc.latest_blockhash()?,
    ))?;
    ensure!(
        production_tag59.err.is_none(),
        "production tag59 rejected mined proof: {:?}",
        production_tag59.err
    );
    let tag59_total = production_tag59
        .units
        .context("production tag59 omitted CU")?;

    let clean_instruction = transition_instruction(
        proof_account.pubkey(),
        pool_key,
        marker_key,
        payer.pubkey(),
        &public,
        false,
    )?;
    let clean = rpc.simulate_verbose(&signed_transition(
        &payer,
        &proof_account,
        clean_instruction.clone(),
        rpc.latest_blockhash()?,
    ))?;
    ensure!(
        clean.err.is_none(),
        "production tag65 rejected mined proof on {} marker path: {:?}",
        if preowned_marker { "program" } else { "System" },
        clean.err
    );
    let expected_proof_sha256 = Sha256::digest(proof);
    let expected_proof_log = format!(
        "Program data: {} {}",
        BASE64.encode(b"aspis-proof-sha256-v1"),
        BASE64.encode(expected_proof_sha256)
    );
    let proof_log_count = clean
        .logs
        .iter()
        .filter(|line| line.as_str() == expected_proof_log)
        .count();
    let production_tag65_simulation_proof_sha256_log_exact = proof_log_count == 1;
    ensure!(
        production_tag65_simulation_proof_sha256_log_exact,
        "production tag65 simulation omitted or duplicated the exact proof SHA-256 log: count={proof_log_count}"
    );
    let production_tag65_simulation_logged_proof_sha256 = hex(&expected_proof_sha256);
    ensure!(
        rpc_account_snapshot(&rpc, &proof_account.pubkey())?.as_ref()
            == Some(&production_proof_before),
        "production tag65 simulation changed proof account"
    );
    let tag65_total = clean.units.context("production tag65 omitted CU")?;
    let increment = tag65_total as i64 - tag59_total as i64;
    let reconciled: u64 = (tag59_total as i128 + i128::from(increment))
        .try_into()
        .context("production Spend CU reconciliation overflow")?;
    ensure!(
        reconciled == tag65_total,
        "production tag65 ledger mismatch"
    );
    let ledger = SpendProductionMutationLedger {
        production_read_only_tag59_cu: tag59_total,
        production_tag65_increment_over_tag59_cu: increment,
        production_tag65_total_cu: tag65_total,
        reconciled_total_cu: reconciled,
        formula: format!("{tag59_total} + ({increment})"),
    };

    // Use a real failed transaction, not only simulation, for rollback. Any
    // single flipped proof byte must reject; the last byte sits inside the
    // final grinding-nonce/query tail of the wire.
    let corruption_offset = proof.len().checked_sub(1).context("empty Spend proof")?;
    let mut corrupt_proof = proof.to_vec();
    corrupt_proof[corruption_offset] ^= 1;
    let (corrupt_proof_account, corrupt_proof_before) =
        upload_finalized_proof_account(&rpc, &payer, &corrupt_proof)?;
    let corrupt = signed_transition(
        &payer,
        &corrupt_proof_account,
        transition_instruction(
            corrupt_proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            false,
        )?,
        rpc.latest_blockhash()?,
    );
    let corrupt_landed_error = rpc.send_and_confirm_failure(&corrupt)?;
    let corrupt_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_before)
        && rpc_account_snapshot(&rpc, &marker_key)? == marker_before
        && rpc_account_snapshot(&rpc, &corrupt_proof_account.pubkey())?.as_ref()
            == Some(&corrupt_proof_before);
    ensure!(corrupt_rollback, "corrupt production tag65 failed rollback");

    let mut proof_refund_lamports = None;
    let mut refund_transaction_fee_lamports = None;
    let mut nullifier_funding_lamports = None;
    let mut refund_balance_equation_exact = None;
    let concurrent_exactly_one = if exercise_concurrency {
        let second_payer = Keypair::new();
        rpc.airdrop_and_wait(&second_payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
        let first = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            false,
        )?;
        let second = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            second_payer.pubkey(),
            &public,
            false,
        )?;
        let blockhash = rpc.latest_blockhash()?;
        let first = signed_transition(&payer, &proof_account, first, blockhash);
        let second = signed_transition(&second_payer, &proof_account, second, blockhash);
        let rpc_a = Rpc::for_validator(&validator)?;
        let rpc_b = Rpc::for_validator(&validator)?;
        let (a, b) = thread::scope(|scope| {
            let a = scope.spawn(|| rpc_a.send_and_confirm(&first));
            let b = scope.spawn(|| rpc_b.send_and_confirm(&second));
            (a.join().unwrap(), b.join().unwrap())
        });
        let exactly_one = a.is_ok() ^ b.is_ok();
        ensure!(
            exactly_one,
            "production tag65 race did not commit exactly once"
        );
        ensure!(
            rpc_account_snapshot(&rpc, &proof_account.pubkey())?.is_none(),
            "successful production tag65 race did not close proof account"
        );
        Some(exactly_one)
    } else {
        // The exact proof-rent refund balance equation: the payer receives
        // every proof-account lamport, pays the transaction fee, and (on the
        // System marker path) funds the nullifier marker rent.
        let cost = rpc.send_and_confirm_with_cost(&signed_transition(
            &payer,
            &proof_account,
            clean_instruction,
            rpc.latest_blockhash()?,
        ))?;
        ensure!(
            rpc_account_snapshot(&rpc, &proof_account.pubkey())?.is_none(),
            "successful production tag65 did not close proof account"
        );
        let index_of = |key: Pubkey| -> Result<usize> {
            cost.account_keys
                .iter()
                .position(|candidate| *candidate == key)
                .with_context(|| format!("committed tag65 message omitted account {key}"))
        };
        let payer_index = index_of(payer.pubkey())?;
        let proof_index = index_of(proof_account.pubkey())?;
        let marker_index = index_of(marker_key)?;
        let payer_pre = cost.pre_balances[payer_index];
        let payer_post = cost.post_balances[payer_index];
        let proof_pre = cost.pre_balances[proof_index];
        let proof_post = cost.post_balances[proof_index];
        let marker_pre = cost.pre_balances[marker_index];
        let marker_post = cost.post_balances[marker_index];
        ensure!(proof_pre == production_proof_before.lamports && proof_post == 0);
        let refunded = proof_pre;
        let marker_funding = marker_post
            .checked_sub(marker_pre)
            .context("nullifier marker balance decreased during tag65")?;
        let equation_exact = i128::from(payer_post) - i128::from(payer_pre)
            + i128::from(cost.fee_lamports)
            + i128::from(marker_funding)
            == i128::from(refunded);
        ensure!(
            equation_exact,
            "committed tag65 payer/proof/marker balances do not reconcile: payer {payer_pre}->{payer_post}, fee {}, refund {refunded}, marker funding {marker_funding}",
            cost.fee_lamports
        );
        proof_refund_lamports = Some(refunded);
        refund_transaction_fee_lamports = Some(cost.fee_lamports);
        nullifier_funding_lamports = Some(marker_funding);
        refund_balance_equation_exact = Some(equation_exact);
        None
    };

    let pool_after = rpc_account_snapshot(&rpc, &pool_key)?
        .context("production Spend pool missing after tag65")?;
    let marker_after = rpc_account_snapshot(&rpc, &marker_key)?
        .context("production Spend marker missing after tag65")?;
    let decoded_pool = AtomicPoolStateV1::decode(&pool_after.data)
        .map_err(|error| anyhow!("decode Spend pool after tag65: {error:?}"))?;
    let sequence_advanced = decoded_pool.sequence == statement.sequence + 1;
    let anchor_replaced = decoded_pool.anchor == public.output_anchor;
    let marker_written = marker_is_exact(&marker_after, pool_key, &public.nullifier);
    ensure!(
        sequence_advanced && anchor_replaced && marker_written,
        "production tag65 did not commit the exact atomic transition"
    );

    // A distinct sealed replay probe keeps the duplicate tooth independent of
    // the proof-close assertion above.
    let (duplicate_proof_account, duplicate_proof_before) =
        upload_finalized_proof_account(&rpc, &payer, &[0u8])?;
    let mut duplicate_public = public;
    duplicate_public.current_anchor = duplicate_public.output_anchor;
    let duplicate = signed_transition(
        &payer,
        &duplicate_proof_account,
        transition_instruction(
            duplicate_proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &duplicate_public,
            false,
        )?,
        rpc.latest_blockhash()?,
    );
    let duplicate_error = rpc.send_and_confirm_failure(&duplicate)?;
    let expected_duplicate_error = format!("\"Custom\":{ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT}");
    let duplicate_no_mutation = duplicate_error.contains(&expected_duplicate_error)
        && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_after)
        && rpc_account_snapshot(&rpc, &marker_key)?.as_ref() == Some(&marker_after)
        && rpc_account_snapshot(&rpc, &duplicate_proof_account.pubkey())?.as_ref()
            == Some(&duplicate_proof_before);
    ensure!(
        duplicate_no_mutation,
        "duplicate production tag65 changed state"
    );

    drop(validator);
    Ok((
        SpendProductionMutationPathSummary {
            marker_path: if preowned_marker {
                "program_owned_zeroed"
            } else {
                "canonical_system_owned_create"
            },
            proof_accounts_finalized_before_production_verification: true,
            literal_tag59_simulation_cu: tag59_total,
            literal_tag65_simulation_cu: tag65_total,
            headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - tag65_total as i64,
            ledger,
            production_unmined_tag59_rejected,
            production_unmined_tag59_error,
            production_unmined_tag65_rejected,
            production_unmined_tag65_rollback_green: production_unmined_tag65_rollback,
            production_unmined_tag65_landed_error,
            production_tag59_accepted_mined_sbf: true,
            production_tag65_clean_simulation_accepted: true,
            production_tag65_simulation_proof_sha256_log_exact,
            production_tag65_simulation_logged_proof_sha256,
            corrupt_proof_rejected_with_transaction_rollback: corrupt_rollback,
            corrupt_transaction_landed_error: corrupt_landed_error,
            committed_transition_succeeded: true,
            proof_account_absent_after_success: true,
            proof_refund_lamports,
            refund_transaction_fee_lamports,
            nullifier_funding_lamports,
            refund_balance_equation_exact,
            pool_sequence_advanced_once: sequence_advanced,
            pool_anchor_replaced: anchor_replaced,
            nullifier_marker_written: marker_written,
            duplicate_rejected_without_second_mutation: duplicate_no_mutation,
            concurrent_exactly_one_committed: concurrent_exactly_one,
        },
        tag59_diagnostic_bit_unavailable,
        tag61_unavailable,
    ))
}

/// Pin the original tag-60 account ABI and proof-retention postcondition
/// against the exact production SBF. This intentionally owns a separate
/// validator lifecycle from every tag-65 path.
fn run_legacy_tag60_compatibility(
    root: &Path,
    so: &Path,
    instance: &SelectedInstance,
) -> Result<SpendLegacyTag60CompatibilitySummary> {
    let statement = &instance.statement;
    let public = public_inputs(statement);
    let pool_key = Pubkey::new_from_array(statement.pool);
    let (marker_key, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
    let mut pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV1 {
        sequence: statement.sequence,
        anchor: public.current_anchor,
    }
    .encode(&mut pool_bytes)
    .map_err(|error| anyhow!("encode legacy tag60 pool fixture: {error:?}"))?;
    let pool_fixture = write_validator_account_fixture(
        root,
        "atomic-spend-production-legacy-tag60-pool",
        pool_key,
        aspis_verifier::id(),
        &pool_bytes,
    )?;

    let validator = start_validator_with_accounts(root, so, &[(pool_key, pool_fixture)])?;
    let rpc = Rpc::for_validator(&validator)?;
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
    let (proof_account, proof_before) =
        upload_finalized_proof_account(&rpc, &payer, &instance.proof)?;
    let proof_finalized_before_transition = proof_before.data.len() >= PROOF_ACCOUNT_HEADER_LEN
        && proof_before.data[8..PROOF_ACCOUNT_HEADER_LEN]
            .iter()
            .all(|byte| *byte == 0);
    ensure!(
        proof_finalized_before_transition,
        "legacy tag60 compatibility proof was not sealed"
    );
    let pool_before =
        rpc_account_snapshot(&rpc, &pool_key)?.context("legacy tag60 pool fixture missing")?;
    let decoded_pool_before = AtomicPoolStateV1::decode(&pool_before.data)
        .map_err(|error| anyhow!("decode legacy tag60 pool: {error:?}"))?;
    let marker_before = rpc_account_snapshot(&rpc, &marker_key)?;
    let nullifier_marker_absent_before = marker_before.is_none();
    ensure!(
        nullifier_marker_absent_before,
        "legacy tag60 nullifier marker unexpectedly existed"
    );

    let legacy_instruction = legacy_tag60_transition_instruction(
        proof_account.pubkey(),
        pool_key,
        marker_key,
        payer.pubkey(),
        &public,
    )?;
    let proof_meta = legacy_instruction
        .accounts
        .first()
        .context("legacy tag60 instruction omitted proof meta")?;
    let proof_meta_read_only = !proof_meta.is_writable;
    let proof_meta_non_signer = !proof_meta.is_signer;
    ensure!(
        legacy_instruction.data.first() == Some(&60),
        "legacy Spend transition discriminator drifted from tag60"
    );
    ensure!(
        proof_meta_read_only && proof_meta_non_signer,
        "legacy tag60 proof meta must remain read-only and non-signer"
    );

    let committed_transaction_cu = rpc.send_and_confirm(&signed_read_only(
        &payer,
        legacy_instruction,
        rpc.latest_blockhash()?,
    ))?;
    let proof_after_commit = rpc_account_snapshot(&rpc, &proof_account.pubkey())?
        .context("legacy tag60 consumed its retained proof account")?;
    ensure!(
        proof_after_commit == proof_before,
        "legacy tag60 changed proof owner, data, or lamports"
    );
    let pool_after = rpc_account_snapshot(&rpc, &pool_key)?
        .context("legacy tag60 pool disappeared after commit")?;
    let marker_after = rpc_account_snapshot(&rpc, &marker_key)?
        .context("legacy tag60 nullifier marker missing after commit")?;
    let decoded_pool_after = AtomicPoolStateV1::decode(&pool_after.data)
        .map_err(|error| anyhow!("decode legacy tag60 pool after commit: {error:?}"))?;
    let expected_sequence = decoded_pool_before
        .sequence
        .checked_add(1)
        .context("legacy tag60 fixture sequence overflow")?;
    let pool_sequence_advanced_exactly_once = decoded_pool_after.sequence == expected_sequence;
    let pool_anchor_replaced = decoded_pool_after.anchor == public.output_anchor;
    let nullifier_marker_written_exactly =
        marker_is_exact(&marker_after, pool_key, &public.nullifier);
    ensure!(
        pool_sequence_advanced_exactly_once
            && pool_anchor_replaced
            && nullifier_marker_written_exactly,
        "legacy tag60 did not commit the exact atomic transition"
    );

    let mut duplicate_public = public;
    duplicate_public.current_anchor = duplicate_public.output_anchor;
    let duplicate_instruction = legacy_tag60_transition_instruction(
        proof_account.pubkey(),
        pool_key,
        marker_key,
        payer.pubkey(),
        &duplicate_public,
    )?;
    ensure!(
        duplicate_instruction
            .accounts
            .first()
            .is_some_and(|meta| !meta.is_writable && !meta.is_signer),
        "legacy tag60 duplicate changed the proof meta ABI"
    );
    let duplicate_landed_error = rpc.send_and_confirm_failure(&signed_read_only(
        &payer,
        duplicate_instruction,
        rpc.latest_blockhash()?,
    ))?;
    let expected_duplicate_error = format!("\"Custom\":{ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT}");
    let duplicate_rejected_as_already_spent =
        duplicate_landed_error.contains(&expected_duplicate_error);
    let proof_after = rpc_account_snapshot(&rpc, &proof_account.pubkey())?
        .context("legacy tag60 duplicate consumed its retained proof account")?;
    let pool_after_duplicate = rpc_account_snapshot(&rpc, &pool_key)?
        .context("legacy tag60 duplicate removed the pool")?;
    let marker_after_duplicate = rpc_account_snapshot(&rpc, &marker_key)?
        .context("legacy tag60 duplicate removed the marker")?;
    let duplicate_rejected_without_second_mutation = duplicate_rejected_as_already_spent
        && pool_after_duplicate == pool_after
        && marker_after_duplicate == marker_after
        && proof_after == proof_before;
    ensure!(
        duplicate_rejected_without_second_mutation,
        "legacy tag60 duplicate mutated state or its retained proof"
    );

    let proof_owner_retained = proof_after.owner == proof_before.owner;
    let proof_data_retained_bit_for_bit = proof_after.data == proof_before.data;
    let proof_lamports_retained = proof_after.lamports == proof_before.lamports;
    let proof_account_retained_exactly = proof_after == proof_before;
    let proof_data_sha256_before = hex(&Sha256::digest(&proof_before.data));
    let proof_data_sha256_after = hex(&Sha256::digest(&proof_after.data));

    drop(validator);
    Ok(SpendLegacyTag60CompatibilitySummary {
        isolated_local_validator_lifecycle: true,
        instruction_wire_ordinal: 60,
        proof_account: proof_account.pubkey().to_string(),
        pool_account: pool_key.to_string(),
        nullifier_account: marker_key.to_string(),
        proof_meta_read_only,
        proof_meta_non_signer,
        proof_finalized_before_transition,
        committed_transition_succeeded: true,
        committed_transaction_cu,
        pool_sequence_before: decoded_pool_before.sequence,
        pool_sequence_after: decoded_pool_after.sequence,
        pool_sequence_advanced_exactly_once,
        pool_anchor_before_hex: spend_hex(&decoded_pool_before.anchor),
        pool_anchor_after_hex: spend_hex(&decoded_pool_after.anchor),
        pool_anchor_replaced,
        nullifier_marker_absent_before,
        nullifier_marker_written_exactly,
        duplicate_landed_error,
        duplicate_rejected_as_already_spent,
        duplicate_rejected_without_second_mutation,
        proof_owner_before: proof_before.owner.to_string(),
        proof_owner_after: proof_after.owner.to_string(),
        proof_owner_retained,
        proof_data_bytes: proof_before.data.len(),
        proof_data_sha256_before,
        proof_data_sha256_after,
        proof_data_retained_bit_for_bit,
        proof_lamports_before: proof_before.lamports,
        proof_lamports_after: proof_after.lamports,
        proof_lamports_retained,
        proof_account_retained_exactly,
    })
}

fn run_spend_acceptance(
    root: &Path,
    so: &Path,
    instance: &SelectedInstance,
    validator_version: &str,
) -> Result<SpendAcceptanceSummary> {
    use aspis_core::state_only_prefix::{
        STATE_ONLY_SPEND_BATCH_GRINDING_BITS, STATE_ONLY_SPEND_FOLD_GRINDING_BITS,
        STATE_ONLY_SPEND_GRINDING_BITS, STATE_ONLY_SPEND_QUERY_COUNT,
    };
    use aspis_statement::state_only_spend::verify_atomic_state_only_spend_v3;

    let statement = &instance.statement;
    let proof = instance.proof.as_slice();

    let host_result = verify_atomic_state_only_spend_v3(proof, statement, HOST_HASH, None);
    let proof_unmined = host_result.is_err();
    ensure!(
        !proof_unmined,
        "spend-measure requires a mined release proof; production host verification failed: {:?}",
        host_result.err()
    );

    // The default (production) host dispatch must reject the tag-59
    // diagnostic selector before any account access.
    let diagnostic_bit_data = to_vec(&AspisInstruction::VerifyAtomicStateOnlySpendV3 {
        pool: statement.pool,
        sequence: statement.sequence,
        public_input: spend_public_bytes(&statement.spend),
        output_anchor: aspis_statement::encode_digest_canonical(&statement.output_anchor),
        diagnostic_unmined: true,
    })?;
    let default_tag59_fail_closed_host =
        aspis_verifier::process_spend_production_instruction(
            &aspis_verifier::id(),
            &[],
            &diagnostic_bit_data,
        ) == Err(solana_sdk::program_error::ProgramError::InvalidInstructionData);
    ensure!(
        default_tag59_fail_closed_host,
        "default tag59 diagnostic selector is not fail-closed"
    );

    let soundness = read_theorem_artifact(root, "spend_d_after_g_soundness_epro.json")?;
    let hvzk = read_theorem_artifact(root, "spend_computational_hvzk_closure.json")?;
    let selected_soundness_floor_bits = soundness["soundness"]["selected_floor_bits"]
        .as_f64()
        .context("soundness artifact omitted selected_floor_bits")?;
    let coarse_whole_ledger_soundness_floor_bits = soundness["soundness"]
        ["coarse_whole_ledger_times_three_bits"]
        .as_f64()
        .context("soundness artifact omitted coarse_whole_ledger_times_three_bits")?;
    let rank_exhaustion_cap17_bits = hvzk["q3_cap17_release"]["rank_exhaustion_abort_bits"]
        .as_f64()
        .context("HVZK artifact omitted rank_exhaustion_abort_bits")?;
    let soundness_bookable = soundness["bookable"].as_bool() == Some(true);

    let validator = start_validator_with_accounts(root, so, &[])?;
    let rpc = Rpc::for_validator(&validator)?;
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let (proof_account, _) = upload_finalized_proof_account(&rpc, &payer, proof)?;

    let transaction = signed_read_only(
        &payer,
        read_only_instruction(proof_account.pubkey(), statement, false)?,
        rpc.latest_blockhash()?,
    );
    let production = rpc.simulate_verbose(&transaction)?;
    ensure!(
        production.err.is_none(),
        "production tag59 rejected the mined proof: {:?}",
        production.err
    );
    let total = production.units.context("tag59 simulation omitted CU")?;
    let markers = parse_cu_markers(&production.logs, "aspis-cu:");
    let ledger = AcceptanceLedgerBuckets::build(&markers, total)
        .context("tag59 marker ledger incomplete")?;
    ensure!(ledger.reconciled_total_cu == total, "tag59 ledger mismatch");
    drop(validator);

    Ok(SpendAcceptanceSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: instance.command.clone(),
        validator_version: validator_version.to_string(),
        instruction_wire_ordinal: 59,
        proof_path: instance.recorded_proof_path.clone(),
        proof_source_override: true,
        proof_bytes: proof.len(),
        proof_sha256: instance.proof_sha256.clone(),
        proof_unmined,
        statement_path: instance.recorded_statement_path.clone(),
        statement_source_override: true,
        statement_sha256: instance.statement_sha256.clone(),
        statement_pool_hex: spend_hex(&statement.pool),
        statement_sequence: statement.sequence,
        canonical_public_input_digest: instance.canonical_public_input_digest.clone(),
        query_count: STATE_ONLY_SPEND_QUERY_COUNT,
        batch_grinding_bits: STATE_ONLY_SPEND_BATCH_GRINDING_BITS,
        final_grinding_bits: STATE_ONLY_SPEND_GRINDING_BITS,
        fold_grinding_bits: STATE_ONLY_SPEND_FOLD_GRINDING_BITS,
        query_selector_candidates: 3,
        rank_exhaustion_cap17_bits,
        selected_soundness_floor_bits,
        coarse_whole_ledger_soundness_floor_bits,
        soundness_bookable,
        proof_account_finalized_before_verification: true,
        default_tag59_fail_closed_host,
        production_api_rejected_unmined_sbf: false,
        production_api_accepted_mined_sbf: true,
        literal_simulation_cu: total,
        headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
        markers,
        ledger,
        production_mutation_enabled: false,
        notes: vec![
            "Tag59 is one integrated parse/transcript/terminal/relation/private-opening/q18 call. The phase ledger is overlap-free and reconciles exactly to the literal simulation total.".to_string(),
            "All five Merkle sections authenticate value||salt32 records. Salts are not transcript messages; their roots bind them before downstream challenges.".to_string(),
            "This total is measured on the exact production binary (spend-production with dynamic RATE512 query coordinates); the former diagnostic candidate build and its lower full-table tag59 total were removed with the research tree.".to_string(),
            "The measured proof is the explicitly selected mined release instance; production host and SBF tag59 both accepted it without any PoW bypass.".to_string(),
            "The canonical public-statement sidecar's path, byte SHA-256, pool, sequence, and transcript public-input digest are pinned in this artifact.".to_string(),
            "production_mutation_enabled records that this measurement artifact does not itself authorize the production mutation path; that authorization is the fail-closed spend-release certificate.".to_string(),
        ],
    })
}

#[allow(clippy::too_many_lines)]
fn run_spend_mutation(
    root: &Path,
    so: &Path,
    so_bytes: usize,
    so_sha256: &str,
    instance: &SelectedInstance,
    validator_version: &str,
) -> Result<SpendMutationSummary> {
    use aspis_core::state_only_prefix::{
        STATE_ONLY_SPEND_BATCH_GRINDING_BITS, STATE_ONLY_SPEND_FOLD_GRINDING_BITS,
        STATE_ONLY_SPEND_GRINDING_BITS, STATE_ONLY_SPEND_QUERY_COUNT,
    };
    use aspis_statement::state_only_spend::{
        verify_atomic_state_only_spend_unmined_for_diagnostics_v3,
        verify_atomic_state_only_spend_v3,
    };

    let statement = &instance.statement;

    // Committed unmined negative KAT: exact bytes, well-formed under the
    // diagnostics-only host replay, and rejected by the production host
    // verifier because its grinding nonces are unmined.
    let committed_unmined_path = root.join(COMMITTED_UNMINED_PROOF_PATH);
    let committed_unmined_proof = fs::read(&committed_unmined_path).with_context(|| {
        format!(
            "read committed unmined Spend proof {}",
            committed_unmined_path.display()
        )
    })?;
    let committed_unmined_sha256 = hex(&Sha256::digest(&committed_unmined_proof));
    ensure!(
        committed_unmined_proof.len() == COMMITTED_UNMINED_PROOF_BYTES,
        "committed unmined Spend proof geometry drift"
    );
    ensure!(
        committed_unmined_sha256 == COMMITTED_UNMINED_PROOF_SHA256,
        "committed unmined Spend proof KAT drift"
    );
    let committed_unmined_statement = committed_unmined_kat_statement()?;
    verify_atomic_state_only_spend_unmined_for_diagnostics_v3(
        &committed_unmined_proof,
        &committed_unmined_statement,
        HOST_HASH,
        None,
    )
    .map_err(|error| anyhow!("committed unmined Spend host replay: {error:?}"))?;
    ensure!(
        verify_atomic_state_only_spend_v3(
            &committed_unmined_proof,
            &committed_unmined_statement,
            HOST_HASH,
            None,
        )
        .is_err(),
        "committed unmined Spend KAT passed production host verification"
    );

    // The default host wire surface exposes no diagnostic mutation: the
    // frozen former-diagnostic ordinal 61 fails closed with the dedicated
    // error, and tag65's wire accepts no trailing diagnostic selector.
    let public = public_inputs(statement);
    let tag61_fail_closed = aspis_verifier::process_spend_production_instruction(
        &aspis_verifier::id(),
        &[],
        &tag61_wire(&public)?,
    ) == Err(solana_sdk::program_error::ProgramError::Custom(
        ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
    ));
    let mut tag65_with_trailing_selector = tag65_wire(&public)?;
    tag65_with_trailing_selector.push(1);
    let tag65_rejects_trailing_selector =
        aspis_verifier::process_spend_production_instruction(
            &aspis_verifier::id(),
            &[],
            &tag65_with_trailing_selector,
        ) == Err(solana_sdk::program_error::ProgramError::InvalidInstructionData);
    let default_tag65_fail_closed_host = tag61_fail_closed && tag65_rejects_trailing_selector;
    ensure!(
        default_tag65_fail_closed_host,
        "the default host mutation wire surface is not fail-closed: tag61={tag61_fail_closed}, tag65_trailing={tag65_rejects_trailing_selector}"
    );

    let production_alias_forbidden_feature_unions_tested =
        check_spend_production_feature_isolation(root)?;

    let (program, program_tag59_closed, program_tag61_closed) =
        run_production_path(root, so, instance, &committed_unmined_proof, true, false)?;
    let (system, system_tag59_closed, system_tag61_closed) =
        run_production_path(root, so, instance, &committed_unmined_proof, false, true)?;
    let production_legacy_tag60_compatibility = run_legacy_tag60_compatibility(root, so, instance)?;

    let production_only_unmined_tag59_rejected =
        program.production_unmined_tag59_rejected && system.production_unmined_tag59_rejected;
    let production_only_unmined_tag65_rejected =
        program.production_unmined_tag65_rejected && system.production_unmined_tag65_rejected;
    let production_only_unmined_tag65_rollback_green = program
        .production_unmined_tag65_rollback_green
        && system.production_unmined_tag65_rollback_green;
    let candidate_tag65_accepts_mined_sbf = program.production_tag65_clean_simulation_accepted
        && system.production_tag65_clean_simulation_accepted;

    let soundness = read_theorem_artifact(root, "spend_d_after_g_soundness_epro.json")?;
    let soundness_bookable = soundness["bookable"].as_bool() == Some(true);
    let hvzk = read_theorem_artifact(root, "spend_computational_hvzk_closure.json")?;
    let complete_view_hvzk_simulator_complete = hvzk["theorem_gates"]
        ["complete_view_computational_hvzk_in_declared_model"]
        .as_bool()
        .context("HVZK artifact omitted the complete-view theorem gate")?;

    Ok(SpendMutationSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: instance.command.clone(),
        validator_version: validator_version.to_string(),
        production_instruction_wire_ordinal: 65,
        diagnostic_instruction_wire_ordinal: 61,
        finalize_proof_instruction_wire_ordinal: 62,
        proof_path: instance.recorded_proof_path.clone(),
        proof_source_override: true,
        proof_bytes: instance.proof.len(),
        proof_sha256: instance.proof_sha256.clone(),
        proof_unmined: false,
        statement_path: instance.recorded_statement_path.clone(),
        statement_source_override: true,
        statement_sha256: instance.statement_sha256.clone(),
        statement_pool_hex: spend_hex(&statement.pool),
        statement_sequence: statement.sequence,
        canonical_public_input_digest: instance.canonical_public_input_digest.clone(),
        query_count: STATE_ONLY_SPEND_QUERY_COUNT,
        batch_grinding_bits: STATE_ONLY_SPEND_BATCH_GRINDING_BITS,
        final_grinding_bits: STATE_ONLY_SPEND_GRINDING_BITS,
        fold_grinding_bits: STATE_ONLY_SPEND_FOLD_GRINDING_BITS,
        production_pow_bypass_exposed: false,
        default_tag65_fail_closed_host,
        committed_unmined_proof_path: COMMITTED_UNMINED_PROOF_PATH.to_string(),
        committed_unmined_proof_bytes: committed_unmined_proof.len(),
        committed_unmined_proof_sha256: committed_unmined_sha256,
        candidate_tag65_rejects_unmined_sbf: false,
        candidate_tag65_accepts_mined_sbf,
        candidate_tag65_outcome_matches_pow: candidate_tag65_accepts_mined_sbf,
        candidate_tag65_rollback_green: true,
        production_only_sbf_features: PRODUCTION_ONLY_FEATURES.to_vec(),
        production_only_sbf_bytes: so_bytes,
        production_only_sbf_sha256: so_sha256.to_string(),
        production_only_mined_override_exercised: true,
        production_only_unmined_tag59_rejected,
        production_only_unmined_tag65_rejected,
        production_only_unmined_tag65_rollback_green,
        production_only_tag59_diagnostic_bit_unavailable: program_tag59_closed
            && system_tag59_closed,
        production_only_tag61_unavailable: program_tag61_closed && system_tag61_closed,
        production_alias_forbidden_feature_unions_rejected: true,
        production_alias_forbidden_feature_unions_tested,
        production_legacy_tag60_compatibility,
        production_paths: vec![program, system],
        soundness_bookable,
        complete_view_hvzk_simulator_complete,
        production_spend_mutation_enabled: false,
        notes: vec![
            "Tag65 has no diagnostic selector and calls the exact tag59 parser/verifier with production PoW before the first CPI or account write. Its simulated and landed outcomes are measured against the exact production binary.".to_string(),
            "The same production SBF is exercised in a separate local-validator lifecycle through legacy tag60 with a sealed read-only, non-signer proof. The landed transition advances the pool and writes the marker exactly once, a landed duplicate reaches the nullifier-already-spent error, and the proof owner, bytes, and lamports remain exactly unchanged.".to_string(),
            "The negative PoW teeth use the committed unmined fixture proof in a second sealed account: production tags 59/65 must reject it, with a landed failed tag65 transaction and exact rollback. The former diagnostic-unmined builds and the tag61 measurement handler were removed with the research tree, so no diagnostic ledger is recorded; the frozen ordinal 61 is instead required to fail closed on the deployed binary.".to_string(),
            "The candidate_tag65_* fields record the pre-commit tag65 simulation of the same production binary: acceptance of the mined proof and simulation-time rollback. The separate diagnostic candidate build they previously described no longer exists.".to_string(),
            "The committed non-race tag65 additionally reconciles the exact refund balance equation: payer_post - payer_pre + fee + nullifier_funding = proof_refund.".to_string(),
            "Every production-alias forbidden feature union fails Cargo feature resolution because the diagnostic and superseded-profile features were deleted from the program manifest; each union and the grouped all-forbidden union were rebuilt and rejected.".to_string(),
            "The mutation artifact records, but cannot override, the independent complete-Good/q3 soundness audit and complete-view HVZK release gate.".to_string(),
        ],
    })
}

pub struct SpendMeasureOutcome {
    pub acceptance_path: PathBuf,
    pub mutation_path: PathBuf,
    pub acceptance_tag59_cu: u64,
    pub max_production_tag65_cu: u64,
}

/// Run the complete production measurement and write both release-certificate
/// measurement inputs under `results/spend`.
pub fn run_spend_measure(results_dir: &Path) -> Result<SpendMeasureOutcome> {
    let root = workspace_root()?;
    let instance = select_instance(&root)?;
    let so = build_spend_production_sbf(&root)?;
    let so_bytes =
        fs::read(&so).with_context(|| format!("read production Spend SBF {}", so.display()))?;
    let so_sha256 = hex(&Sha256::digest(&so_bytes));
    let validator_version = validator_version();

    let acceptance = run_spend_acceptance(&root, &so, &instance, &validator_version)?;
    let mutation = run_spend_mutation(
        &root,
        &so,
        so_bytes.len(),
        &so_sha256,
        &instance,
        &validator_version,
    )?;

    // The two artifacts must describe one measurement context.
    ensure!(
        acceptance.proof_sha256 == mutation.proof_sha256
            && acceptance.statement_sha256 == mutation.statement_sha256
            && acceptance.validator_version == mutation.validator_version,
        "acceptance/mutation measurement context mismatch"
    );

    fs::create_dir_all(results_dir)?;
    let acceptance_path =
        results_dir.join("atomic_state_only_spend_acceptance_production_mined.json");
    let mutation_path = results_dir.join("atomic_state_only_spend_mutation_production_mined.json");
    fs::write(
        &acceptance_path,
        format!("{}\n", serde_json::to_string_pretty(&acceptance)?),
    )?;
    fs::write(
        &mutation_path,
        format!("{}\n", serde_json::to_string_pretty(&mutation)?),
    )?;

    let max_production_tag65_cu = mutation
        .production_paths
        .iter()
        .map(|path| path.literal_tag65_simulation_cu)
        .max()
        .unwrap_or_default();
    Ok(SpendMeasureOutcome {
        acceptance_path,
        mutation_path,
        acceptance_tag59_cu: acceptance.literal_simulation_cu,
        max_production_tag65_cu,
    })
}
