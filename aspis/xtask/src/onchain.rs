//! `stage0-onchain`: build the SBF program, spawn a local validator, run the
//! Stage 0 measurement matrix and corruption suite on-chain, and write
//! `results/stage0/onchain_summary.json`.
//!
//! Requires `cargo-build-sbf` and `solana-test-validator` on PATH (blocked in
//! some sandboxes; the gate note records where this has and hasn't run).

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
use solana_sdk::{
    compute_budget::ComputeBudgetInstruction,
    instruction::{AccountMeta, Instruction},
    native_token::LAMPORTS_PER_SOL,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    transaction::Transaction,
};
// solana-sdk 2.x deprecates the re-export in favor of solana-system-interface;
// keep the single-crate dependency surface for the Stage 0 harness.
#[allow(deprecated)]
use solana_sdk::system_instruction;

use aspis_core::params::{
    PROFILE_CAPACITY, PROFILE_CAPACITY_G32_Q32, PROFILE_CAPACITY_G32_Q36,
    PROFILE_CAPACITY_LR10_Q32_G16, PROFILE_CAPACITY_LR10_Q36_G16, PROFILE_CAPACITY_LR10_Q40_G16,
    PROFILE_CAPACITY_LR14, PROFILE_JOHNSON,
};
use aspis_core::{FoldPayload, MerkleMode, Profile};
use aspis_prover::{
    multilinear_eval, prove, prove_exact_wide_v4_scaffold_for_measurement, prove_with_claim,
    prove_with_claim_v4, prove_with_synthetic_second_phase, seeded_coeffs, ProveOptions, HOST_HASH,
};
use aspis_verifier::{
    AspisInstruction, ExactWideV4DiagnosticMode, M31CircleBasisDiagnosticMode, ZkKernelKind,
    M31_CIRCLE_BASIS_C1_COLUMNS, M31_CIRCLE_BASIS_C1_LEAF_BYTES, M31_CIRCLE_BASIS_C2_LEAF_BYTES,
    M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS, M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES,
    M31_CIRCLE_FOLD_FIXTURE_BYTES, PROOF_ACCOUNT_HEADER_LEN,
};

const UPLOAD_CHUNK_BYTES: usize = 640;
const VERIFY_CU_LIMIT: u32 = 1_400_000;
const HEAP_FRAME_BYTES: u32 = 262_144;
const VERIFY_REPETITIONS: usize = 5;

#[derive(Serialize)]
pub struct OnchainVariant {
    pub profile: &'static str,
    pub soundness_label: &'static str,
    pub fold_payload: &'static str,
    pub merkle_mode: &'static str,
    pub status: &'static str,
    pub verify_error: Option<String>,
    pub proof_bytes: usize,
    pub upload_chunks: usize,
    pub upload_cu_total: u64,
    pub verify_cu: Vec<u64>,
    pub verify_cu_mean: f64,
    pub verify_repetitions_requested: usize,
    pub corruption_rejected_onchain: Vec<(String, bool)>,
}

#[derive(Serialize)]
pub struct OnchainSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub verify_cu_limit: u32,
    pub heap_frame_bytes: u32,
    pub gate_matrix_only: bool,
    pub variants: Vec<OnchainVariant>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct CuMarker {
    pub label: String,
    pub remaining: u64,
    pub delta_from_previous: Option<i64>,
}

#[derive(Serialize)]
pub struct ProfileRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub fold_payload: &'static str,
    pub merkle_mode: &'static str,
    pub proof_bytes: usize,
    pub upload_chunks: usize,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub markers: Vec<CuMarker>,
    pub logs: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct LayoutPoint {
    pub log_rows: u8,
    pub columns: u16,
    pub query_count: u16,
    pub leaf_bytes: u16,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub markers: Vec<CuMarker>,
}

#[derive(Serialize)]
pub struct LayoutSweep {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub points: Vec<LayoutPoint>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Stage2LayoutVariant {
    pub columns: u16,
    pub leaf_bytes: u16,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub delta_vs_k64_cu: i64,
    pub diagnostic_markers: Vec<CuMarker>,
    pub wide_leaf_hash_cu: Option<i64>,
    pub synthetic_merkle_cu: Option<i64>,
    pub obsolete_same_gamma_rlc_cu: Option<i64>,
}

#[derive(Serialize)]
pub struct Stage2LayoutSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub log_rows: u8,
    pub query_count: u16,
    pub repetitions: usize,
    pub variants: Vec<Stage2LayoutVariant>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Poseidon2ProbeVariant {
    pub implementation: &'static str,
    pub permutations: u16,
    pub simulation_cu: Vec<Option<u64>>,
    pub simulation_errors: Vec<Option<String>>,
    pub accepted_all: bool,
    pub mean_cu_if_accepted: Option<f64>,
    pub incremental_cu_over_zero_if_accepted: Option<i64>,
}

#[derive(Serialize)]
pub struct Poseidon2ProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub variants: Vec<Poseidon2ProbeVariant>,
    pub measured_incremental_cu_per_permutation_from_8: Option<f64>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct ZkKernelProbeVariant {
    pub kernel: &'static str,
    pub iterations: u16,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub incremental_cu_over_zero: i64,
    pub incremental_cu_per_iteration: f64,
}

#[derive(Serialize)]
pub struct ZkKernelProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub variants: Vec<ZkKernelProbeVariant>,
    pub full_pcs_verifier: FullPcsVerifierComparison,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct WideRlcProbeVariant {
    pub kernel: &'static str,
    pub columns: u16,
    pub query_count: u16,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub baseline_cu_mean: f64,
    pub incremental_cu: i64,
}

#[derive(Serialize)]
pub struct WideRlcProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub variants: Vec<WideRlcProbeVariant>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct MerkleArityProbePoint {
    pub tree: &'static str,
    pub depth: u8,
    pub query_count: u16,
    pub binary_cu: Vec<u64>,
    pub binary_cu_mean: f64,
    pub radix4_cu: Vec<u64>,
    pub radix4_cu_mean: f64,
    pub radix4_savings_cu: i64,
}

#[derive(Serialize)]
pub struct MerkleArityProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub points: Vec<MerkleArityProbePoint>,
    pub modeled_binary_total_cu: i64,
    pub modeled_radix4_total_cu: i64,
    pub modeled_radix4_savings_cu: i64,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Radix4ProofVariant {
    pub merkle_mode: &'static str,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    /// Production `Verify` CU (the optimized path). Named `verify_cu`, not
    /// `verify_fast_cu`: `VerifyFast` survives only as a wire-compatible
    /// alias and the g32 runner has always measured `Verify` itself.
    pub verify_cu: Vec<u64>,
    pub verify_cu_mean: f64,
    pub host_corruption_cases: usize,
    pub host_corruption_all_rejected: bool,
}

#[derive(Serialize)]
pub struct Radix4G16Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub repetitions: usize,
    pub second_phase_enabled: bool,
    pub variants: Vec<Radix4ProofVariant>,
    pub radix4_savings_cu: i64,
    pub radix4_savings_percent: f64,
    pub radix4_proof_bytes_delta: i64,
    pub radix4_frontier_corruption_rejected_host: bool,
    pub radix4_frontier_corruption_rejected_sbf: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Radix4G32Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub repetitions: usize,
    pub binary_proof_source: String,
    pub radix4_proof_source: String,
    pub radix4_generation_seconds: Option<f64>,
    pub binary_first_root: String,
    pub radix4_first_root: String,
    pub root_changed: bool,
    pub transcript_kat_unchanged: bool,
    pub variants: Vec<Radix4ProofVariant>,
    pub radix4_savings_cu: i64,
    pub radix4_savings_percent: f64,
    pub radix4_proof_bytes_delta: i64,
    pub radix4_frontier_corruption_rejected_host: bool,
    pub radix4_frontier_corruption_rejected_sbf: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct VarianceSeedSample {
    pub seed: u64,
    pub binary_proof_bytes: usize,
    pub binary_verify_cu: u64,
    pub radix4_proof_bytes: usize,
    pub radix4_verify_cu: u64,
    pub radix4_saving_cu: i64,
}

#[derive(Serialize)]
pub struct VarianceModeStats {
    pub merkle_mode: &'static str,
    pub per_seed_cu: Vec<u64>,
    pub mean_cu: f64,
    pub population_std_dev_cu: f64,
    pub min_cu: u64,
    pub max_cu: u64,
    pub range_cu: u64,
    pub max_minus_mean_cu: f64,
    pub mean_plus_two_sigma_cu: f64,
}

#[derive(Serialize)]
pub struct VarianceG16Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub seeds: u64,
    pub repetitions_per_seed: usize,
    pub criterion: String,
    pub samples: Vec<VarianceSeedSample>,
    pub binary_stats: VarianceModeStats,
    pub radix4_stats: VarianceModeStats,
    pub strict_candidate_projection_cu: i64,
    pub ten_percent_slack_maximum_cu: i64,
    pub single_draw_headroom_cu: i64,
    pub criterion_penalty_range_cu: u64,
    pub criterion_adjusted_projection_cu: i64,
    pub criterion_passes: bool,
    pub secondary_two_sigma_penalty_cu: f64,
    pub secondary_adjusted_projection_cu: i64,
    pub notes: Vec<String>,
}

fn variance_stats(merkle_mode: &'static str, per_seed_cu: Vec<u64>) -> VarianceModeStats {
    let n = per_seed_cu.len() as f64;
    let mean = per_seed_cu.iter().sum::<u64>() as f64 / n;
    let variance = per_seed_cu
        .iter()
        .map(|&cu| {
            let d = cu as f64 - mean;
            d * d
        })
        .sum::<f64>()
        / n;
    let sigma = variance.sqrt();
    let min = *per_seed_cu.iter().min().expect("nonempty seed set");
    let max = *per_seed_cu.iter().max().expect("nonempty seed set");
    VarianceModeStats {
        merkle_mode,
        mean_cu: mean,
        population_std_dev_cu: sigma,
        min_cu: min,
        max_cu: max,
        range_cu: max - min,
        max_minus_mean_cu: max as f64 - mean,
        mean_plus_two_sigma_cu: mean + 2.0 * sigma,
        per_seed_cu,
    }
}

#[derive(Serialize)]
pub struct FullPcsVerifierComparison {
    pub profile: &'static str,
    pub proof_bytes: usize,
    pub software_inverse_cu: Vec<u64>,
    pub software_inverse_cu_mean: f64,
    pub syscall_inverse_cu: Vec<u64>,
    pub syscall_inverse_cu_mean: f64,
    pub syscall_savings_cu: i64,
    pub circle_conjugate_cu: Vec<u64>,
    pub circle_conjugate_cu_mean: f64,
    pub circle_conjugate_savings_vs_software_cu: i64,
    pub diagnostic_profile_cu: Option<u64>,
    pub diagnostic_profile_markers: Vec<CuMarker>,
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

impl Rpc {
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

    fn send_and_confirm(&self, tx: &Transaction) -> Result<u64> {
        let encoded = BASE64.encode(bincode::serialize(tx)?);
        let sig = self.call(
            "sendTransaction",
            json!([encoded, {"encoding": "base64", "preflightCommitment": "processed"}]),
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
                    bail!("transaction failed: {}", status["err"]);
                }
                if status["confirmationStatus"].as_str().is_some() {
                    break;
                }
            }
            if started.elapsed() > Duration::from_secs(15) {
                bail!("confirmation timed out");
            }
            thread::sleep(Duration::from_millis(100));
        }
        // fetch CU from simulation-free path is awkward; use getTransaction meta
        let tx_info = self.call(
            "getTransaction",
            json!([sig, {"encoding": "json", "commitment": "confirmed", "maxSupportedTransactionVersion": 0}]),
        );
        Ok(tx_info
            .ok()
            .and_then(|t| t["meta"]["computeUnitsConsumed"].as_u64())
            .unwrap_or(0))
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

    /// Simulate and return (units_consumed, error).
    fn simulate(&self, tx: &Transaction) -> Result<(Option<u64>, Option<String>)> {
        let result = self.simulate_verbose(tx)?;
        Ok((result.units, result.err))
    }
}

fn workspace_root() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    Ok(manifest
        .parent()
        .ok_or_else(|| anyhow!("no workspace root"))?
        .to_path_buf())
}

fn build_sbf(root: &Path) -> Result<PathBuf> {
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .arg("--manifest-path")
        .arg(root.join("programs/aspis-verifier/Cargo.toml"))
        .status()
        .context("cargo-build-sbf not found on PATH — install the Solana toolchain")?;
    if !status.success() {
        bail!("cargo-build-sbf failed");
    }
    let so = root.join("target/deploy/aspis_verifier.so");
    if !so.exists() {
        bail!("missing {}", so.display());
    }
    Ok(so)
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

fn start_validator(root: &Path, so: &Path) -> Result<Validator> {
    let ledger = root.join(".stage0-validator");
    let _ = fs::remove_dir_all(&ledger);
    let ports = free_ports(3)?;
    let (rpc_port, faucet_port, gossip_port) = (ports[0], ports[1], ports[2]);
    let child = Command::new("solana-test-validator")
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
        .arg(so)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .context("solana-test-validator not found on PATH")?;
    let mut validator = Validator {
        child,
        rpc_url: format!("http://127.0.0.1:{rpc_port}"),
    };
    // wait for RPC
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
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

fn create_program_account(
    rpc: &Rpc,
    payer: &Keypair,
    account: &Keypair,
    space: usize,
) -> Result<()> {
    let rent = rpc.call("getMinimumBalanceForRentExemption", json!([space]))?;
    let rent = rent.as_u64().ok_or_else(|| anyhow!("bad rent"))?;
    let create = system_instruction::create_account(
        &payer.pubkey(),
        &account.pubkey(),
        rent,
        space as u64,
        &aspis_verifier::id(),
    );
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[create],
        Some(&payer.pubkey()),
        &[payer, account],
        blockhash,
    );
    rpc.send_and_confirm(&tx)?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn upload_proof(
    rpc: &Rpc,
    payer: &Keypair,
    proof_account: &Keypair,
    proof: &[u8],
    fresh_account: bool,
) -> Result<(usize, u64)> {
    let space = PROOF_ACCOUNT_HEADER_LEN + proof.len();
    if fresh_account {
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
    }

    let mut total_cu = 0u64;
    let init = proof_instruction(
        &payer.pubkey(),
        &proof_account.pubkey(),
        &AspisInstruction::InitProof {
            total_len: proof.len() as u32,
        },
    )?;
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[init],
        Some(&payer.pubkey()),
        &[payer, proof_account],
        blockhash,
    );
    total_cu += rpc.send_and_confirm(&tx)?;

    let mut chunks = 0usize;
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
        total_cu += rpc.send_and_confirm(&tx)?;
        chunks += 1;
    }
    Ok((chunks, total_cu))
}

fn verify_tx(
    payer: &Keypair,
    proof_account: &Pubkey,
    digest: [u8; 32],
    blockhash: solana_sdk::hash::Hash,
    profile_cu: bool,
) -> Result<Transaction> {
    let instruction = if profile_cu {
        AspisInstruction::VerifyProfile {
            statement_digest: digest,
        }
    } else {
        AspisInstruction::Verify {
            statement_digest: digest,
        }
    };
    let ixs = vec![
        ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
        ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
        proof_instruction(&payer.pubkey(), proof_account, &instruction)?,
    ];
    Ok(Transaction::new_signed_with_payer(
        &ixs,
        Some(&payer.pubkey()),
        &[payer],
        blockhash,
    ))
}

fn validator_version() -> String {
    Command::new("solana-test-validator")
        .env("NO_DNA", "1")
        .arg("--version")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|_| "unknown".to_string())
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

pub fn run_stage0_onchain(gate_matrix_only: bool) -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let validator_version = validator_version();

    let mut variants = Vec::new();
    let modes: &[MerkleMode] = if gate_matrix_only {
        &[MerkleMode::MinimalSubtree]
    } else {
        &[MerkleMode::MinimalSubtree, MerkleMode::SinglePaths]
    };
    for profile in [&PROFILE_CAPACITY, &PROFILE_JOHNSON, &PROFILE_CAPACITY_LR14] {
        for payload in [FoldPayload::RawFibers, FoldPayload::ProofCarriedRoundLocal] {
            for &mode in modes {
                if gate_matrix_only
                    && profile.id == PROFILE_CAPACITY_LR14.id
                    && payload == FoldPayload::ProofCarriedRoundLocal
                {
                    continue;
                }
                variants.push(run_onchain_variant(&rpc, &payer, profile, payload, mode)?);
            }
        }
    }

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: if gate_matrix_only {
            "cargo run -p aspis-xtask -- stage0-onchain-gate".to_string()
        } else {
            "cargo run -p aspis-xtask -- stage0-onchain".to_string()
        },
        validator_version,
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only,
        variants,
        notes: vec![
            "verify_cu are simulateTransaction unitsConsumed for the full verify transaction (including compute-budget instructions) against a local test validator.".to_string(),
            "Variants with status=verify_failed exceeded budget or otherwise failed during simulation; their corruption suite is skipped because no accepting baseline exists.".to_string(),
            "Soundness labels remain heuristic pending the Stage 1 note; the capacity-vs-Johnson asymmetry must be restated wherever these CU numbers are quoted.".to_string(),
        ],
    })
}

pub fn run_stage0_onchain_g32() -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for profile in [&PROFILE_CAPACITY_G32_Q36, &PROFILE_CAPACITY_G32_Q32] {
        variants.push(run_onchain_variant(
            &rpc,
            &payer,
            profile,
            FoldPayload::RawFibers,
            MerkleMode::MinimalSubtree,
        )?);
    }

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-onchain-g32".to_string(),
        validator_version: validator_version(),
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only: true,
        variants,
        notes: vec![
            "Diagnostic g32 query/grinding trade; not a frozen profile until Stage 1 soundness accounting confirms the query count.".to_string(),
            "Only raw_fibers/minimal_subtree is measured because proof_carried_round_local lost on both bytes and CU in the gate artifact.".to_string(),
        ],
    })
}

pub fn run_stage0_onchain_layout_target() -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for profile in [
        // the literal ruled Stage 1 schedule first (soundness-note §4)
        &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32,
        &PROFILE_CAPACITY_LR10_Q40_G16,
        &PROFILE_CAPACITY_LR10_Q36_G16,
        &PROFILE_CAPACITY_LR10_Q32_G16,
    ] {
        variants.push(run_onchain_variant(
            &rpc,
            &payer,
            profile,
            FoldPayload::RawFibers,
            MerkleMode::MinimalSubtree,
        )?);
    }

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-onchain-layout-target".to_string(),
        validator_version: validator_version(),
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only: true,
        variants,
        notes: vec![
            "Lower-row diagnostic for the wide-row statement layout decision; not a frozen profile until Stage 1 soundness accounting and the Stage 2 direct evaluator exist.".to_string(),
            "Only raw_fibers/minimal_subtree is measured because proof_carried_round_local lost on both bytes and CU in the gate artifact.".to_string(),
            "The first row is the literal ruled q36/g32 Stage 1 profile and performs the real prover-side 32-bit nonce search; the remaining g16 rows are comparison diagnostics.".to_string(),
            "Although the verifier's grinding threshold check is constant-cost, changing g16 to g32 changes the transcript-bound header and therefore the sampled query collisions and minimal-subtree shape. Use the literal g32 row, not a g16 CU proxy, for the ruled profile.".to_string(),
            "Historical lower-row diagnostic emitted by the current v3 verifier without C2: one OOD value and its interleaved relation polynomial are enforced per round. Use stage1-onchain-hardening for the frozen C2 gate profile.".to_string(),
            "Combine these PCS verifier costs with layout_sweep RLC/wide-leaf deltas; do not add the full synthetic Merkle loop or path hashing is double-counted.".to_string(),
        ],
    })
}

/// Stage 1 hardened-profile measurement. The valid g32 proof is cached as a
/// pinned fixture after its expensive nonce search; every reuse first runs
/// the current host verifier, so a protocol change invalidates and replaces
/// it instead of silently measuring stale bytes.
pub fn run_stage1_onchain_hardening() -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let profile = &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32;
    let payload = FoldPayload::RawFibers;
    let mode = MerkleMode::MinimalSubtree;
    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let digest = crate::host_statement_digest(0);
    let options = ProveOptions {
        fold_payload: payload,
        merkle_mode: mode,
    };
    let proof_dir = root.join("results/stage1/proofs");
    fs::create_dir_all(&proof_dir)?;
    let proof_path = proof_dir.join("capacity_lr10_q36_g32_v3_c2.bin");

    let cached = fs::read(&proof_path)
        .ok()
        .filter(|proof| aspis_core::verify(proof, &digest, HOST_HASH).is_ok());
    let (proof, proof_source) = if let Some(proof) = cached {
        (proof, "reused host-verified cached g32 proof".to_string())
    } else {
        eprintln!("stage1-onchain: searching literal g32 nonce (cached after success)");
        let started = Instant::now();
        let proof =
            prove_with_synthetic_second_phase(profile, &coeffs, &digest, &options, HOST_HASH);
        fs::write(&proof_path, &proof)?;
        (
            proof,
            format!(
                "generated and cached literal g32 proof; prover search {:.3}s",
                started.elapsed().as_secs_f64()
            ),
        )
    };
    let proof_digest = HOST_HASH(&[&proof]);
    let proof_digest_hex = proof_digest
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();

    let variant =
        run_onchain_variant_with_proof(&rpc, &payer, profile, payload, mode, Some(proof))?;

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage1-onchain-hardening".to_string(),
        validator_version: validator_version(),
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only: true,
        variants: vec![variant],
        notes: vec![
            "Literal ruled Stage 1 q36/g32 profile with C1 -> (lambda, chi) -> C2 -> claims -> gamma and the interleaved OOD/evaluation-relation sumcheck enabled.".to_string(),
            "C2 uses a deterministic challenge-dependent Stage-1 helper to price and test the generic second-phase interface; it is not the Stage-2 LogUp helper and proves no payment relation.".to_string(),
            "All host-generated corruption cases are replayed against the SBF verifier; every entry must be true.".to_string(),
            format!("proof fixture: {}; {proof_source}", proof_path.display()),
            format!("proof SHA-256: {proof_digest_hex}"),
        ],
    })
}

pub fn run_stage0_onchain_profile() -> Result<ProfileRun> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY;
    let payload = FoldPayload::RawFibers;
    let mode = MerkleMode::MinimalSubtree;
    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let digest = crate::host_statement_digest(0);
    let proof = prove(
        profile,
        &coeffs,
        &digest,
        &ProveOptions {
            fold_payload: payload,
            merkle_mode: mode,
        },
        HOST_HASH,
    );
    let proof_account = Keypair::new();
    let (chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let blockhash = rpc.latest_blockhash()?;
    let tx = verify_tx(&payer, &proof_account.pubkey(), digest, blockhash, true)?;
    let sim = rpc.simulate_verbose(&tx)?;
    Ok(ProfileRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-onchain-profile".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        fold_payload: "raw_fibers",
        merkle_mode: "minimal_subtree",
        proof_bytes: proof.len(),
        upload_chunks: chunks,
        simulation_units: sim.units,
        simulation_error: sim.err,
        markers: parse_cu_markers(&sim.logs, "aspis-cu:"),
        logs: sim.logs,
        notes: vec![
            "Diagnostic only: msg!/sol_log_compute_units markers add CU and should not be quoted as the verifier cost.".to_string(),
            "Use marker deltas for stage attribution: header/transcript/query/layer Merkle+fold/final.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct TranscriptKatRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub expected_digest_hex: String,
    pub matched_on_sbf: bool,
    pub simulation_units: Option<u64>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct TranscriptKatV4S2PcsScaffoldRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub expected_digest_hex: String,
    pub host_digest_hex: String,
    pub host_matched: bool,
    pub matched_on_sbf: bool,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub v3_pin_unchanged: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct LogUpCompressionKatRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub expected_phi_hex: String,
    pub host_phi_hex: String,
    pub host_matched: bool,
    pub matched_on_sbf: bool,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub weakened_feature_forwarded_to_verifier: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct OodSampleRelationProbeVariant {
    pub samples_per_round: u8,
    pub expected_sink_hex: String,
    pub host_sink_hex: String,
    pub host_sink_matched: bool,
    pub sbf_sink_matched: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct OodSampleRelationProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub log_rows: u8,
    pub rounds: u8,
    pub terminal_coefficients: u8,
    pub existing_multilinear_claim_components: u8,
    pub variants: Vec<OodSampleRelationProbeVariant>,
    pub pcs_s2_second_ood_sample_transcript_relation_cu: i64,
    pub superseded_probe_local_generated_value_delta_cu: i64,
    pub probe_local_value_generation_contamination_removed_cu: i64,
    pub previous_estimate_bracket_cu: [i64; 2],
    pub delta_over_previous_bracket_max_cu: i64,
    pub structural_proof_record_delta_bytes: u64,
    pub extra_transcript_hash_calls_no_retry: u32,
    pub extra_geometric_fold_operations: u32,
    pub extra_terminal_component_evaluations: u32,
    pub production_transcript_kat_unchanged: bool,
    pub production_proof_format_unchanged: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct V4S2PcsScaffoldSeedMeasurement {
    pub seed: u64,
    pub v3_proof_bytes: usize,
    pub v4_proof_bytes: usize,
    pub proof_bytes_delta: i64,
    pub v3_proof_sha256: String,
    pub v4_proof_sha256: String,
    pub v3_layer0_unique_fibers: u16,
    pub v4_layer0_unique_fibers: u16,
    pub v3_verify_cu: u64,
    pub v4_verify_cu: u64,
    pub verify_cu_delta: i64,
}

#[derive(Serialize)]
pub struct V4S2PcsScaffoldCorruptionCase {
    pub seed: u64,
    pub target: String,
    pub layer: Option<u32>,
    pub sample_index: Option<u8>,
    pub helper_claim_index: Option<u8>,
    pub helper_leaf_half_index: Option<u8>,
    pub proof_byte_offset: usize,
    pub host_rejected: bool,
    pub host_error: String,
    pub sbf_rejected: bool,
    pub sbf_error: String,
}

#[derive(Serialize)]
pub struct V4S2PcsScaffoldSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub statement_kind: &'static str,
    pub is_payment_proof: bool,
    pub production_verify_instruction_wire_ordinal: u8,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub transaction_envelope: &'static str,
    pub merkle_mode: &'static str,
    pub seeds: u64,
    pub repetitions_per_proof: usize,
    pub v3_samples_per_round: u8,
    pub v4_samples_per_round: u8,
    pub v3_second_phase_helper_columns: u8,
    pub v4_second_phase_helper_columns: u8,
    pub v3_second_phase_leaf_bytes: u16,
    pub v4_second_phase_leaf_bytes: u16,
    pub v3_second_phase_claims: u8,
    pub v4_second_phase_claims: u8,
    pub transcript_kat_v4_s2_pcs_scaffold_wire_ordinal: u8,
    pub transcript_kat_v4_s2_pcs_scaffold_expected_hex: String,
    pub transcript_kat_v4_s2_pcs_scaffold_host_matched: bool,
    pub transcript_kat_v4_s2_pcs_scaffold_sbf_matched: bool,
    pub transcript_kat_v4_s2_pcs_scaffold_simulation_cu: u64,
    pub transcript_kat_v3_unchanged: bool,
    pub measurements: Vec<V4S2PcsScaffoldSeedMeasurement>,
    pub v3_layer0_unique_fibers_min: u16,
    pub v3_layer0_unique_fibers_max: u16,
    pub v4_layer0_unique_fibers_min: u16,
    pub v4_layer0_unique_fibers_max: u16,
    pub v3_verify_cu_mean: f64,
    pub v4_verify_cu_mean: f64,
    pub paired_verify_cu_delta_mean: f64,
    pub paired_verify_cu_delta_min: i64,
    pub paired_verify_cu_delta_max: i64,
    pub paired_verify_cu_delta_range: u64,
    pub proof_bytes_delta_min: i64,
    pub proof_bytes_delta_max: i64,
    pub second_ood_corruptions: Vec<V4S2PcsScaffoldCorruptionCase>,
    pub helper_claim_corruptions: Vec<V4S2PcsScaffoldCorruptionCase>,
    pub helper_leaf_half_corruptions: Vec<V4S2PcsScaffoldCorruptionCase>,
    pub every_second_ood_rejected_host: bool,
    pub every_second_ood_rejected_sbf: bool,
    pub every_helper_claim_rejected_host: bool,
    pub every_helper_claim_rejected_sbf: bool,
    pub every_helper_leaf_half_rejected_host: bool,
    pub every_helper_leaf_half_rejected_sbf: bool,
    pub normative_payment_v4_framing_complete: bool,
    pub missing_payment_v4_components: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct ReconciledExactWideSeedMeasurement {
    pub seed: u64,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub layer0_unique_fibers: u16,
    pub authenticated_c1_opening_bytes: usize,
    pub authenticated_c2_opening_bytes: usize,
    pub diagnostic_host_accepted: bool,
    pub production_host_rejected_bad_header: bool,
    pub observed_cu_or_cap: u64,
    pub simulation_error: Option<String>,
    pub accepted_at_1_400_000_limit: bool,
    pub compute_budget_exhausted: bool,
    pub exact_cu_if_accepted: Option<u64>,
    pub required_cu_lower_bound_if_exhausted: Option<u64>,
    pub signed_headroom_vs_1_190_000_if_accepted: Option<i64>,
    pub signed_headroom_vs_1_400_000_if_accepted: Option<i64>,
    pub minimum_breach_vs_1_190_000_if_exhausted: Option<u64>,
    pub minimum_breach_vs_1_400_000_if_exhausted: Option<u64>,
    pub outcome_vs_1_190_000: String,
    pub outcome_vs_1_400_000: String,
}

#[derive(Serialize)]
pub struct ReconciledExactWideCorruptionCase {
    pub target: &'static str,
    pub kind: &'static str,
    pub proof_byte_offset: usize,
    pub host_rejected: bool,
    pub host_error: String,
    pub sbf_error: String,
    pub sbf_compute_budget_exhausted: bool,
    pub sbf_rejection_conclusive: bool,
}

#[derive(Serialize)]
pub struct ReconciledExactWideSummary {
    pub generated_at_utc: String,
    pub command: &'static str,
    pub validator_version: String,
    pub profile: &'static str,
    pub statement_kind: &'static str,
    pub is_payment_proof: bool,
    pub diagnostic_verify_instruction_wire_ordinal: u8,
    pub production_verify_with_claim_wire_ordinal: u8,
    pub production_verify_with_claim_accepts_wide_flag: bool,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub strict_project_threshold_cu: u64,
    pub absolute_execution_cap_cu: u64,
    pub transaction_envelope: &'static str,
    pub merkle_mode: &'static str,
    pub seeds: u64,
    pub c1_columns: usize,
    pub c1_leaf_bytes: usize,
    pub c2_columns: usize,
    pub c2_leaf_bytes: usize,
    pub auxiliary_c1_columns: &'static str,
    pub measurements: Vec<ReconciledExactWideSeedMeasurement>,
    pub accepted_seed_count: usize,
    pub compute_budget_exhausted_seed_count: usize,
    pub all_seed_outcomes_classified: bool,
    pub observed_cu_or_cap_min: u64,
    pub observed_cu_or_cap_max: u64,
    pub exact_accepted_cu_mean: Option<f64>,
    pub threshold_1_190_000_observation: String,
    pub threshold_1_400_000_observation: String,
    pub production_tag6_seed1_sbf_rejected: bool,
    pub production_tag6_seed1_sbf_cu: u64,
    pub production_tag6_seed1_sbf_error: String,
    pub corruption_cases: Vec<ReconciledExactWideCorruptionCase>,
    pub canonical_mutations_rejected_host: bool,
    pub noncanonical_limbs_rejected_host_and_sbf_conclusively: bool,
    pub owner_ruling_made: bool,
    pub overlap_replacement: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct ExactWideV4DiagnosticVariant {
    pub mode: &'static str,
    pub expected_host_sink_hex: String,
    pub sbf_matched_host_sink: bool,
    pub accepted_all: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_errors: Vec<Option<String>>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct ExactWideV4CorruptionCase {
    pub target: &'static str,
    pub mode: &'static str,
    pub fixture_byte_offset: usize,
    pub host_corrupted_sink_differs: bool,
    pub host_rejected_malformed: bool,
    pub sbf_rejected_canonical_sink: bool,
    pub sbf_error: String,
}

#[derive(Serialize)]
pub struct ExactWideV4DiagnosticSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub final_payment_kat_reserved_wire_ordinal: u8,
    pub final_payment_kat_implemented: bool,
    pub repetitions: usize,
    pub fixture_seed: u64,
    pub fixture_payload_bytes: usize,
    pub fixture_upload_chunks: usize,
    pub fixture_upload_cu_excluded: u64,
    pub batch_fixture_payload_bytes: usize,
    pub batch_fixture_upload_chunks: usize,
    pub batch_fixture_upload_cu_excluded: u64,
    pub fixture_generation_in_measured_instruction: bool,
    pub c1_columns: usize,
    pub c2_columns: usize,
    pub total_gamma_powers: usize,
    pub c1_leaf_bytes: usize,
    pub c2_leaf_bytes: usize,
    pub c1_layout: &'static str,
    pub c2_layout: &'static str,
    pub host_baseline_equals_fused: bool,
    pub variants: Vec<ExactWideV4DiagnosticVariant>,
    pub fused_dot4_savings_cu: i64,
    pub fused_dot4_savings_percent: f64,
    pub c1_leaf_hash_incremental_over_empty_cu: i64,
    pub c2_leaf_hash_incremental_over_empty_cu: i64,
    pub gamma_powers_incremental_over_control_cu: i64,
    pub gate_q36_batch_unique_fibers: usize,
    pub gate_batch_count_provenance: String,
    pub frozen_q36_fixture_unique_fibers: [usize; 2],
    pub theoretical_q36_unique_fibers_max: usize,
    pub transaction_compute_limit_cu: u32,
    pub strict_transaction_target_cu: u32,
    pub heap_frame_bytes: u32,
    pub transaction_envelope: &'static str,
    pub batch_unprepared_accepted: bool,
    pub batch_unprepared_compute_budget_exhausted: bool,
    pub batch_prepared_accepted: bool,
    pub batch_unprepared_cu_mean_or_cap: f64,
    pub batch_prepared_cu_mean: f64,
    pub batch_prepared_headroom_vs_compute_cap_cu: i64,
    pub batch_prepared_headroom_vs_strict_target_cu: i64,
    pub batch_prepared_bytes_accepted: bool,
    pub batch_prepared_bytes_cu_mean: f64,
    pub batch_prepared_bytes_headroom_vs_compute_cap_cu: i64,
    pub batch_prepared_bytes_headroom_vs_strict_target_cu: i64,
    pub batch_prepared_bytes_savings_vs_structured_cu: i64,
    pub batch_prepared_bytes_savings_vs_structured_percent: f64,
    pub batch_prepared_savings_cu_if_exact: Option<i64>,
    pub batch_prepared_savings_lower_bound_cu: i64,
    pub batch_prepared_bytes_savings_lower_bound_cu: i64,
    pub corruption_cases: Vec<ExactWideV4CorruptionCase>,
    pub all_corruptions_rejected_sbf: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct M31CircleBasisVariant {
    pub mode: &'static str,
    pub expected_host_sink_hex: String,
    pub accepted_all: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub signed_headroom_vs_1_190_000_cu: i64,
    pub signed_headroom_vs_1_400_000_cu: i64,
}

#[derive(Serialize)]
pub struct M31CircleBasisCorruptionCase {
    pub target: &'static str,
    pub fixture: &'static str,
    pub fixture_byte_offset: usize,
    pub host_rejected: bool,
    pub sbf_rejected: bool,
    pub sbf_error: String,
}

#[derive(Serialize)]
pub struct M31CircleBasisSummary {
    pub generated_at_utc: String,
    pub command: &'static str,
    pub validator_version: String,
    pub status: &'static str,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub transaction_envelope: &'static str,
    pub structural_fibers: usize,
    pub c1_field: &'static str,
    pub c1_columns: usize,
    pub c1_leaf_bytes: usize,
    pub c2_field: &'static str,
    pub c2_columns: usize,
    pub c2_leaf_bytes: usize,
    pub gamma_powers: &'static str,
    pub rlc_fixture_bytes: usize,
    pub fold_fixture_bytes: usize,
    pub host_structured_equals_fused: bool,
    pub host_all_rlc_modes_equal: bool,
    pub host_normalized_fold_matches_cubic_reference: bool,
    pub variants: Vec<M31CircleBasisVariant>,
    pub fused_rlc_savings_cu: i64,
    pub fused_rlc_savings_percent: f64,
    pub decoded_fused_rlc_savings_vs_structured_cu: i64,
    pub decoded_fused_rlc_savings_vs_structured_percent: f64,
    pub streaming_rlc_savings_vs_structured_cu: i64,
    pub streaming_rlc_savings_vs_structured_percent: f64,
    pub winning_rlc_mode: &'static str,
    pub winning_rlc_cu_mean: f64,
    pub winning_rlc_savings_vs_structured_cu: i64,
    pub winning_rlc_savings_vs_structured_percent: f64,
    pub c1_leaf_hash_incremental_over_empty_cu: i64,
    pub fold_cached_coordinate_derivation_increment_cu: i64,
    pub fold_batch_inverse_syscall_increment_cu: i64,
    pub fold_coordinate_and_batch_inverse_increment_cu: i64,
    pub fold_batch_inverse_backend: &'static str,
    pub corruption_cases: Vec<M31CircleBasisCorruptionCase>,
    pub all_corruptions_rejected: bool,
    pub current_aspis_serialization: bool,
    pub genuine_circle_pcs_integration_implemented: bool,
    pub protocol_or_architecture_ruling_made: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

/// Host/SBF transcript known-answer check: send `TranscriptKat` with the
/// host-pinned digest; the program recomputes with the syscall backend and
/// errors on mismatch (soundness-note appendix, sampler step).
pub fn run_transcript_kat() -> Result<TranscriptKatRun> {
    // host-side assertion first, so a drifted pin fails before spawning a validator
    let host_digest = aspis_core::transcript::transcript_kat(HOST_HASH);
    anyhow::ensure!(
        host_digest == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED,
        "host transcript KAT does not match the pinned constant; re-pin only as a deliberate protocol change"
    );

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::TranscriptKat {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (units, err) = rpc.simulate(&tx)?;
    let mut hex = String::new();
    for b in aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED {
        hex.push_str(&format!("{b:02x}"));
    }
    Ok(TranscriptKatRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-transcript-kat".to_string(),
        validator_version: validator_version(),
        expected_digest_hex: hex,
        matched_on_sbf: err.is_none(),
        simulation_units: units,
        notes: vec![
            "matched_on_sbf=false means the SBF transcript diverged from the host — stop and diagnose before trusting any on-chain measurement.".to_string(),
        ],
    })
}

/// Host/SBF known-answer check for the explicit two-helper v4/s=2 PCS
/// scaffold. The legacy tag-5 KAT remains independently pinned. This is not
/// the final payment-v4 schedule KAT, which will use a later wire tag.
pub fn run_transcript_kat_v4_s2_pcs_scaffold() -> Result<TranscriptKatV4S2PcsScaffoldRun> {
    const INSTRUCTION_WIRE_ORDINAL: u8 = 19;
    let hex = |bytes: &[u8]| {
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };
    let host_digest = aspis_core::transcript::transcript_kat_v4_s2_pcs_scaffold(HOST_HASH);
    ensure!(
        host_digest == aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        "host v4/s=2 PCS-scaffold transcript KAT drifted"
    );
    let v3_pin_unchanged = aspis_core::transcript::transcript_kat(HOST_HASH)
        == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED;
    ensure!(v3_pin_unchanged, "legacy v3 transcript KAT drifted");

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::TranscriptKatV4S2PcsScaffold {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (simulation_units, simulation_error) = rpc.simulate(&transaction)?;
    Ok(TranscriptKatV4S2PcsScaffoldRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command:
            "cargo run --release -p aspis-xtask -- stage2-v4-s2-pcs-scaffold-kat".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        expected_digest_hex: hex(
            &aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        ),
        host_digest_hex: hex(&host_digest),
        host_matched: true,
        matched_on_sbf: simulation_error.is_none(),
        simulation_units,
        simulation_error,
        v3_pin_unchanged,
        notes: vec![
            "Wire tag 19 is append-only and permanently names the two-helper v4/s=2 PCS scaffold; frozen v3 remains tag 5 and final payment-v4 will use tag 20 or later.".to_string(),
            "The vector absorbs one C2 root and both helper evaluations before gamma, then exercises two complete sequential beta/y/mu triples per round.".to_string(),
            "This KAT is necessary but neither a payment-v4 KAT nor a proof measurement; scaffold proof CU is measured separately through production VerifyWithClaim tag 6.".to_string(),
        ],
    })
}

/// Host/SBF known-answer check for the canonical LogUp tagged-tuple encoding.
/// The program is built through the normal production feature set, which does
/// not forward `insecure-test-logup-compression` to `aspis-statement`.
pub fn run_logup_compression_kat() -> Result<LogUpCompressionKatRun> {
    let mut host_phi = [0u8; 16];
    aspis_statement::logup_compression_kat().write_le_bytes(&mut host_phi);
    let host_matched = host_phi == aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED;
    anyhow::ensure!(
        host_matched,
        "host LogUp compression KAT does not match the pinned phi; re-pin only as a deliberate statement-protocol change"
    );

    let root = workspace_root()?;
    let feature_tree = Command::new("cargo")
        .args([
            "tree",
            "-p",
            "aspis-verifier",
            "-e",
            "features",
            "--prefix",
            "none",
        ])
        .current_dir(&root)
        .output()
        .context("inspect verifier dependency features")?;
    ensure!(
        feature_tree.status.success(),
        "cargo tree failed while checking verifier feature isolation: {}",
        String::from_utf8_lossy(&feature_tree.stderr)
    );
    let weakened_feature_forwarded =
        String::from_utf8_lossy(&feature_tree.stdout).contains("insecure-test-logup-compression");
    ensure!(
        !weakened_feature_forwarded,
        "production verifier dependency graph enables insecure-test-logup-compression"
    );
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::LogUpCompressionKat {
            expected_phi: aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (simulation_units, simulation_error) = rpc.simulate(&tx)?;

    let to_hex = |bytes: &[u8]| {
        let mut hex = String::new();
        for byte in bytes {
            hex.push_str(&format!("{byte:02x}"));
        }
        hex
    };
    Ok(LogUpCompressionKatRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage2-logup-compression-kat".to_string(),
        validator_version: validator_version(),
        expected_phi_hex: to_hex(&aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED),
        host_phi_hex: to_hex(&host_phi),
        host_matched,
        matched_on_sbf: simulation_error.is_none(),
        simulation_units,
        simulation_error,
        weakened_feature_forwarded_to_verifier: weakened_feature_forwarded,
        notes: vec![
            "The runner mechanically checks `cargo tree -p aspis-verifier -e features` before the SBF build; the deliberately weakened lambda^0 compression feature must be absent.".to_string(),
            "matched_on_sbf=false means host and SBF disagree on the pinned tagged-tuple phi; stop before regenerating transcript-bound statement artifacts.".to_string(),
        ],
    })
}

/// Isolated SBF A/B for the second sequential per-round OOD relation sample.
/// Both rows run the same lr10/four-round claim-carrying kernel; subtracting
/// s=1 from s=2 removes instruction and common sumcheck overhead without
/// importing transcript-induced query/Merkle variance from a full proof.
pub fn run_stage2_s2_ood_probe() -> Result<OodSampleRelationProbeSummary> {
    const REPETITIONS: usize = 5;
    const INSTRUCTION_WIRE_ORDINAL: u8 = 18;
    let pinned = [
        (1u8, aspis_core::verify::OOD_SAMPLE_PROBE_S1_EXPECTED),
        (2u8, aspis_core::verify::OOD_SAMPLE_PROBE_S2_EXPECTED),
    ];
    let to_hex = |bytes: &[u8]| {
        let mut hex = String::new();
        for byte in bytes {
            hex.push_str(&format!("{byte:02x}"));
        }
        hex
    };

    let mut host_rows = Vec::with_capacity(pinned.len());
    for (samples_per_round, expected_sink) in pinned {
        let value = aspis_core::verify::ood_sample_relation_probe(HOST_HASH, samples_per_round)
            .map_err(|error| anyhow!("host OOD sample probe failed: {error:?}"))?;
        let mut host_sink = [0u8; 16];
        value.write_le_bytes(&mut host_sink);
        anyhow::ensure!(
            host_sink == expected_sink,
            "host s={samples_per_round} OOD probe sink drifted: expected {}, got {}; re-pin only for a deliberate probe-kernel change",
            to_hex(&expected_sink),
            to_hex(&host_sink)
        );
        host_rows.push((samples_per_round, expected_sink, host_sink));
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut variants = Vec::with_capacity(host_rows.len());
    for (samples_per_round, expected_sink, host_sink) in host_rows {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::OodSampleRelationProbe {
                samples_per_round,
                expected_sink,
            })?,
        };
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        variants.push(OodSampleRelationProbeVariant {
            samples_per_round,
            expected_sink_hex: to_hex(&expected_sink),
            host_sink_hex: to_hex(&host_sink),
            host_sink_matched: host_sink == expected_sink,
            sbf_sink_matched: true,
            simulation_cu,
            simulation_cu_mean,
        });
    }
    anyhow::ensure!(
        variants.len() == 2
            && variants[0].samples_per_round == 1
            && variants[1].samples_per_round == 2,
        "OOD probe A/B rows are not in canonical s=1, s=2 order"
    );
    let incremental =
        (variants[1].simulation_cu_mean - variants[0].simulation_cu_mean).round() as i64;

    Ok(OodSampleRelationProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-s2-ood-probe".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        repetitions: REPETITIONS,
        log_rows: 10,
        rounds: 4,
        terminal_coefficients: 4,
        existing_multilinear_claim_components: 1,
        variants,
        pcs_s2_second_ood_sample_transcript_relation_cu: incremental,
        superseded_probe_local_generated_value_delta_cu: 49_155,
        probe_local_value_generation_contamination_removed_cu: 49_155 - incremental,
        previous_estimate_bracket_cu: [5_000, 12_000],
        delta_over_previous_bracket_max_cu: incremental - 12_000,
        structural_proof_record_delta_bytes: 64,
        extra_transcript_hash_calls_no_retry: 20,
        extra_geometric_fold_operations: 10,
        extra_terminal_component_evaluations: 16,
        production_transcript_kat_unchanged: true,
        production_proof_format_unchanged: true,
        included_work: vec![
            "four second sequential beta/y/mu triples: exact-uniform OOD sampling, canonical QM31 decode, y absorption, and mu sampling".to_string(),
            "four relation-value mu*y updates and four geometric relation-weight insertions, including allocator behavior".to_string(),
            "every later WeightAccumulator fold of the four added components (10 geometric folds total)".to_string(),
            "terminal dot evaluation of the four added components across four final coefficients (16 component evaluations)".to_string(),
        ],
        excluded_work: vec![
            "proof commitments, roots, Merkle openings, query derivation, and transcript-induced query/frontier variance".to_string(),
            "proof-account upload CU and the eventual v4 C2 leaf/claim widening".to_string(),
            "statement constraint composition, masking, and prover-side OOD evaluation work".to_string(),
        ],
        notes: vec![
            "Book only pcs_s2_second_ood_sample_transcript_relation_cu as the isolated pre-v4 projection line; the integrated v4 eight-draw SBF measurement replaces it.".to_string(),
            "The s=1 and s=2 instructions have identical Borsh size and expected-sink comparison overhead; their deterministic mean difference isolates the added second samples and retained relation-weight work.".to_string(),
            "The probe reuses the production canonical OOD sample kernel but does not select a proof format. VERSION=3 and TRANSCRIPT_KAT_EXPECTED remain untouched.".to_string(),
            "The +64-byte figure is the structural four-round record delta only; eventual full-proof bytes can move further when the v4 transcript changes openings.".to_string(),
            format!("The measured {incremental}-CU delta refutes the old 5-12K bracket: that intuition priced transcript work but omitted the four retained components' later folds and terminal evaluations."),
            format!("SUPERSEDED measurement: a first probe version generated and encoded each synthetic y inside the sample loop and measured 49,155 CU. Replacing those probe-only operations with a fixed canonical byte table removed {} CU of contamination; the pinned transcript sinks did not move.", 49_155 - incremental),
        ],
    })
}

/// Integrated v3/v4 comparison for an honest public evaluation claim and the
/// synthetic-C2 PCS scaffold. V3 carries one helper claim; v4 carries two
/// helper claims and samples two OOD points per round. This is not a payment
/// proof and must not be described as one.
pub fn run_stage2_v4_s2_pcs_scaffold() -> Result<V4S2PcsScaffoldSummary> {
    const SEEDS: u64 = 8;
    const REPETITIONS_PER_PROOF: usize = 1;
    const PRODUCTION_VERIFY_WIRE_ORDINAL: u8 = 6;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn layer0_unique_fibers(proof: &[u8]) -> Result<u16> {
        let header = aspis_core::proof::Header::parse(proof).context("parse proof header")?;
        let transcript_len = aspis_core::proof::transcript_records_len_for_version(
            header.num_rounds as usize,
            header.flags,
            header.version,
        )
        .context("unsupported proof version")?;
        let final_values = 1usize
            .checked_shl(header.final_poly_log_len)
            .context("final polynomial length overflow")?;
        let offset = aspis_core::proof::HEADER_LEN
            .checked_add(transcript_len)
            .and_then(|value| value.checked_add(final_values * 16))
            .and_then(|value| value.checked_add(8))
            .context("layer-0 opening offset overflow")?;
        let bytes = proof
            .get(offset..offset + 2)
            .context("layer-0 unique count missing")?;
        Ok(u16::from_le_bytes(bytes.try_into().unwrap()))
    }

    fn simulate_verify_with_claim(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        digest: [u8; 32],
        claim: &aspis_core::EvaluationClaim,
    ) -> Result<(Option<u64>, Option<String>)> {
        let claim_z = claim
            .z
            .iter()
            .map(|coordinate| {
                let mut encoded = [0u8; 16];
                coordinate.write_le_bytes(&mut encoded);
                encoded
            })
            .collect();
        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);
        let instruction = AspisInstruction::VerifyWithClaim {
            statement_digest: digest,
            claim_z,
            claim_v,
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                proof_instruction(&payer.pubkey(), proof_account, &instruction)?,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        rpc.simulate(&transaction)
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 20 * LAMPORTS_PER_SOL)?;

    let transcript_kat_v4_s2_pcs_scaffold_host =
        aspis_core::transcript::transcript_kat_v4_s2_pcs_scaffold(HOST_HASH);
    ensure!(
        transcript_kat_v4_s2_pcs_scaffold_host
            == aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        "host v4/s=2 PCS-scaffold transcript KAT drifted"
    );
    let transcript_kat_v3_unchanged = aspis_core::transcript::transcript_kat(HOST_HASH)
        == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED;
    ensure!(
        transcript_kat_v3_unchanged,
        "legacy v3 transcript KAT drifted"
    );
    let kat_instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::TranscriptKatV4S2PcsScaffold {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let kat_transaction = Transaction::new_signed_with_payer(
        &[kat_instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (transcript_kat_v4_s2_pcs_scaffold_units, transcript_kat_v4_s2_pcs_scaffold_error) =
        rpc.simulate(&kat_transaction)?;
    ensure!(
        transcript_kat_v4_s2_pcs_scaffold_error.is_none(),
        "v4/s=2 PCS-scaffold KAT failed on SBF: {transcript_kat_v4_s2_pcs_scaffold_error:?}"
    );
    let transcript_kat_v4_s2_pcs_scaffold_simulation_cu =
        transcript_kat_v4_s2_pcs_scaffold_units
            .context("v4/s=2 PCS-scaffold KAT simulation did not report units")?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let options = ProveOptions {
        fold_payload: FoldPayload::RawFibers,
        merkle_mode: MerkleMode::Radix4MinimalSubtree,
    };
    let mut measurements = Vec::with_capacity(SEEDS as usize);
    let mut corruption_source = None;

    for seed in 1..=SEEDS {
        let digest = crate::host_statement_digest(seed);
        let coeffs = seeded_coeffs(profile.log_rows, seed);
        let claim_z = (0..profile.log_rows)
            .map(|coordinate| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(1_000 + (seed as u32).wrapping_mul(37) + coordinate),
                ))
            })
            .collect::<Vec<_>>();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &claim_z),
            z: claim_z,
        };
        let v3_proof = prove_with_claim(profile, &coeffs, &digest, &claim, &options, HOST_HASH);
        let v4_proof = prove_with_claim_v4(profile, &coeffs, &digest, &claim, &options, HOST_HASH);

        ensure!(
            aspis_core::verify_with_claim(&v3_proof, &digest, Some(&claim), HOST_HASH).is_ok(),
            "seed {seed} v3 claim-carrying synthetic-C2 proof failed host verification"
        );
        ensure!(
            aspis_core::verify_with_claim(&v4_proof, &digest, Some(&claim), HOST_HASH).is_ok(),
            "seed {seed} v4/s=2 claim-carrying synthetic-C2 proof failed host verification"
        );
        let v3_header = aspis_core::proof::Header::parse(&v3_proof)
            .context("parse generated v3 proof header")?;
        let v4_header = aspis_core::proof::Header::parse(&v4_proof)
            .context("parse generated v4 proof header")?;
        ensure!(
            v3_header.ood_samples_per_round() == 1,
            "seed {seed} v3 proof did not encode s=1"
        );
        ensure!(
            v4_header.ood_samples_per_round() == 2,
            "seed {seed} v4 proof did not encode s=2"
        );
        ensure!(
            v3_header.second_phase_helper_count() == 1
                && v3_header.second_phase_leaf_len() == 64
                && v3_header.second_phase_claims_len() == 16,
            "seed {seed} v3 helper framing drifted"
        );
        ensure!(
            v4_header.second_phase_helper_count() == 2
                && v4_header.second_phase_leaf_len() == 128
                && v4_header.second_phase_claims_len() == 32,
            "seed {seed} v4 two-helper framing drifted"
        );

        let v3_account = Keypair::new();
        let v4_account = Keypair::new();
        upload_proof(&rpc, &payer, &v3_account, &v3_proof, true)?;
        upload_proof(&rpc, &payer, &v4_account, &v4_proof, true)?;
        let (v3_units, v3_error) =
            simulate_verify_with_claim(&rpc, &payer, &v3_account.pubkey(), digest, &claim)?;
        ensure!(
            v3_error.is_none(),
            "seed {seed} v3 production VerifyWithClaim failed: {v3_error:?}"
        );
        let (v4_units, v4_error) =
            simulate_verify_with_claim(&rpc, &payer, &v4_account.pubkey(), digest, &claim)?;
        ensure!(
            v4_error.is_none(),
            "seed {seed} v4 production VerifyWithClaim failed: {v4_error:?}"
        );
        let v3_verify_cu = v3_units.context("v3 production Verify did not report units")?;
        let v4_verify_cu = v4_units.context("v4 production Verify did not report units")?;
        let v3_hash = HOST_HASH(&[&v3_proof]);
        let v4_hash = HOST_HASH(&[&v4_proof]);
        measurements.push(V4S2PcsScaffoldSeedMeasurement {
            seed,
            v3_proof_bytes: v3_proof.len(),
            v4_proof_bytes: v4_proof.len(),
            proof_bytes_delta: v4_proof.len() as i64 - v3_proof.len() as i64,
            v3_proof_sha256: hex(&v3_hash),
            v4_proof_sha256: hex(&v4_hash),
            v3_layer0_unique_fibers: layer0_unique_fibers(&v3_proof)?,
            v4_layer0_unique_fibers: layer0_unique_fibers(&v4_proof)?,
            v3_verify_cu,
            v4_verify_cu,
            verify_cu_delta: v4_verify_cu as i64 - v3_verify_cu as i64,
        });
        if seed == 1 {
            corruption_source = Some((digest, claim, v4_proof));
        }
        eprintln!(
            "stage2-v4-s2-pcs-scaffold: seed {seed}/{SEEDS} v3={v3_verify_cu} v4={v4_verify_cu} delta={}",
            v4_verify_cu as i64 - v3_verify_cu as i64
        );
    }

    let (corruption_digest, corruption_claim, v4_proof) =
        corruption_source.context("seed-1 v4 proof missing")?;
    let header = aspis_core::proof::Header::parse(&v4_proof)
        .context("parse seed-1 v4 proof for corruption suite")?;
    ensure!(
        header.ood_samples_per_round() == 2,
        "corruption proof is not s=2"
    );
    let mut second_ood_corruptions = Vec::with_capacity(header.num_rounds as usize);
    for layer in 0..header.num_rounds {
        let offset = aspis_core::proof::ood_value_offset(&header, layer as usize, 1)
            .with_context(|| format!("locate layer-{layer} second OOD value"))?;
        let mut corrupted = v4_proof.clone();
        corrupted[offset] ^= 1;
        let host_error = aspis_core::verify_with_claim(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("second-OOD corruption unexpectedly passed host verification");
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
        let (_, sbf_error) = simulate_verify_with_claim(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            corruption_digest,
            &corruption_claim,
        )?;
        ensure!(
            sbf_error.is_some(),
            "layer {layer} second-OOD corruption unexpectedly passed VerifyWithClaim on SBF"
        );
        second_ood_corruptions.push(V4S2PcsScaffoldCorruptionCase {
            seed: 1,
            target: format!("layer_{layer}_second_ood_value"),
            layer: Some(layer),
            sample_index: Some(1),
            helper_claim_index: None,
            helper_leaf_half_index: None,
            proof_byte_offset: offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_rejected: true,
            sbf_error: sbf_error.unwrap(),
        });
    }

    let mut helper_claim_corruptions = Vec::with_capacity(header.second_phase_claim_count());
    for helper in 0..header.second_phase_claim_count() {
        let offset = aspis_core::proof::second_phase_claim_offset(&header, helper)
            .with_context(|| format!("locate helper claim {helper}"))?;
        let mut corrupted = v4_proof.clone();
        corrupted[offset] ^= 1;
        let host_error = aspis_core::verify_with_claim(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("helper-claim corruption unexpectedly passed host verification");
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
        let (_, sbf_error) = simulate_verify_with_claim(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            corruption_digest,
            &corruption_claim,
        )?;
        ensure!(
            sbf_error.is_some(),
            "helper claim {helper} corruption unexpectedly passed VerifyWithClaim on SBF"
        );
        helper_claim_corruptions.push(V4S2PcsScaffoldCorruptionCase {
            seed: 1,
            target: format!("second_phase_helper_claim_{helper}"),
            layer: None,
            sample_index: None,
            helper_claim_index: Some(helper as u8),
            helper_leaf_half_index: None,
            proof_byte_offset: offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_rejected: true,
            sbf_error: sbf_error.unwrap(),
        });
    }

    let mut helper_leaf_half_corruptions = Vec::with_capacity(header.second_phase_helper_count());
    for helper in 0..header.second_phase_helper_count() {
        let offset = aspis_core::proof::first_layer_second_phase_helper_offset(&v4_proof, helper)
            .with_context(|| format!("locate first C2 leaf helper half {helper}"))?;
        ensure!(
            offset + 64 <= v4_proof.len(),
            "helper half {helper} is out of proof bounds"
        );
        let mut corrupted = v4_proof.clone();
        let value = u32::from_le_bytes(corrupted[offset..offset + 4].try_into().unwrap());
        let changed = if value + 1 == aspis_core::field::P {
            0
        } else {
            value + 1
        };
        corrupted[offset..offset + 4].copy_from_slice(&changed.to_le_bytes());
        let host_error = aspis_core::verify_with_claim(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("C2 helper-half corruption unexpectedly passed host verification");
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
        let (_, sbf_error) = simulate_verify_with_claim(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            corruption_digest,
            &corruption_claim,
        )?;
        ensure!(
            sbf_error.is_some(),
            "C2 helper half {helper} corruption unexpectedly passed VerifyWithClaim on SBF"
        );
        helper_leaf_half_corruptions.push(V4S2PcsScaffoldCorruptionCase {
            seed: 1,
            target: format!("first_c2_leaf_helper_half_{helper}"),
            layer: Some(0),
            sample_index: None,
            helper_claim_index: None,
            helper_leaf_half_index: Some(helper as u8),
            proof_byte_offset: offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_rejected: true,
            sbf_error: sbf_error.unwrap(),
        });
    }

    let v3_verify_cu_mean = measurements.iter().map(|row| row.v3_verify_cu).sum::<u64>() as f64
        / measurements.len() as f64;
    let v4_verify_cu_mean = measurements.iter().map(|row| row.v4_verify_cu).sum::<u64>() as f64
        / measurements.len() as f64;
    let v3_layer0_unique_fibers_min = measurements
        .iter()
        .map(|row| row.v3_layer0_unique_fibers)
        .min()
        .context("empty v3 unique-fiber set")?;
    let v3_layer0_unique_fibers_max = measurements
        .iter()
        .map(|row| row.v3_layer0_unique_fibers)
        .max()
        .context("empty v3 unique-fiber set")?;
    let v4_layer0_unique_fibers_min = measurements
        .iter()
        .map(|row| row.v4_layer0_unique_fibers)
        .min()
        .context("empty v4 unique-fiber set")?;
    let v4_layer0_unique_fibers_max = measurements
        .iter()
        .map(|row| row.v4_layer0_unique_fibers)
        .max()
        .context("empty v4 unique-fiber set")?;
    let verify_deltas = measurements
        .iter()
        .map(|row| row.verify_cu_delta)
        .collect::<Vec<_>>();
    let paired_verify_cu_delta_mean =
        verify_deltas.iter().sum::<i64>() as f64 / verify_deltas.len() as f64;
    let paired_verify_cu_delta_min = *verify_deltas.iter().min().context("empty delta set")?;
    let paired_verify_cu_delta_max = *verify_deltas.iter().max().context("empty delta set")?;
    let proof_deltas = measurements
        .iter()
        .map(|row| row.proof_bytes_delta)
        .collect::<Vec<_>>();
    let proof_bytes_delta_min = *proof_deltas.iter().min().context("empty byte-delta set")?;
    let proof_bytes_delta_max = *proof_deltas.iter().max().context("empty byte-delta set")?;
    let every_second_ood_rejected_host =
        second_ood_corruptions.iter().all(|case| case.host_rejected);
    let every_second_ood_rejected_sbf = second_ood_corruptions.iter().all(|case| case.sbf_rejected);
    let every_helper_claim_rejected_host = helper_claim_corruptions
        .iter()
        .all(|case| case.host_rejected);
    let every_helper_claim_rejected_sbf = helper_claim_corruptions
        .iter()
        .all(|case| case.sbf_rejected);
    let every_helper_leaf_half_rejected_host = helper_leaf_half_corruptions
        .iter()
        .all(|case| case.host_rejected);
    let every_helper_leaf_half_rejected_sbf = helper_leaf_half_corruptions
        .iter()
        .all(|case| case.sbf_rejected);

    Ok(V4S2PcsScaffoldSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-v4-s2-pcs-scaffold".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        statement_kind: "honest public evaluation claim with synthetic-C2 PCS scaffold",
        is_payment_proof: false,
        production_verify_instruction_wire_ordinal: PRODUCTION_VERIFY_WIRE_ORDINAL,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + VerifyWithClaim",
        merkle_mode: "radix4_minimal_subtree",
        seeds: SEEDS,
        repetitions_per_proof: REPETITIONS_PER_PROOF,
        v3_samples_per_round: 1,
        v4_samples_per_round: 2,
        v3_second_phase_helper_columns: 1,
        v4_second_phase_helper_columns: 2,
        v3_second_phase_leaf_bytes: 64,
        v4_second_phase_leaf_bytes: 128,
        v3_second_phase_claims: 1,
        v4_second_phase_claims: 2,
        transcript_kat_v4_s2_pcs_scaffold_wire_ordinal: 19,
        transcript_kat_v4_s2_pcs_scaffold_expected_hex: hex(
            &aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        ),
        transcript_kat_v4_s2_pcs_scaffold_host_matched: true,
        transcript_kat_v4_s2_pcs_scaffold_sbf_matched: true,
        transcript_kat_v4_s2_pcs_scaffold_simulation_cu,
        transcript_kat_v3_unchanged,
        measurements,
        v3_layer0_unique_fibers_min,
        v3_layer0_unique_fibers_max,
        v4_layer0_unique_fibers_min,
        v4_layer0_unique_fibers_max,
        v3_verify_cu_mean,
        v4_verify_cu_mean,
        paired_verify_cu_delta_mean,
        paired_verify_cu_delta_min,
        paired_verify_cu_delta_max,
        paired_verify_cu_delta_range: (paired_verify_cu_delta_max
            - paired_verify_cu_delta_min) as u64,
        proof_bytes_delta_min,
        proof_bytes_delta_max,
        second_ood_corruptions,
        helper_claim_corruptions,
        helper_leaf_half_corruptions,
        every_second_ood_rejected_host,
        every_second_ood_rejected_sbf,
        every_helper_claim_rejected_host,
        every_helper_claim_rejected_sbf,
        every_helper_leaf_half_rejected_host,
        every_helper_leaf_half_rejected_sbf,
        normative_payment_v4_framing_complete: false,
        missing_payment_v4_components: vec![
            "authenticated wide C1: 49 CM31 columns and 1,568-byte layer-0 fibers".to_string(),
            "the exact k'=51 query recombination: 49 QM31-by-CM31 terms plus two QM31 helper terms at gamma^49 and gamma^50".to_string(),
            "the 102 pre-gamma statement values: 49 C1 plus 2 C2 evaluations at each of z and low-bit-XOR-11(z), with their transcript framing".to_string(),
            "ConstraintId-bound statement framing, LogUp payment relation, constraint composition, and economic-attack corpus".to_string(),
            "masking/hiding and the final q36/g32 measurement".to_string(),
        ],
        notes: vec![
            "Every row is a real v3/s=1/one-helper-claim versus v4/s=2/two-helper-claim pair over identical profile, coefficients, honest public main claim, statement digest, synthetic C2 rule, and radix-4 mode. The changed transcript deliberately produces fresh roots, nonce, queries, and frontiers.".to_string(),
            "The measured transaction invokes production AspisInstruction::VerifyWithClaim (Borsh tag 6); no measurement-only proof verifier or new proof-verification wire tag is involved.".to_string(),
            "This proves and measures only the repository's public evaluation claim with synthetic-C2 PCS scaffold. It is not LogUp, does not prove a payment, and is not hiding.".to_string(),
            "One simulation per proof is enough within a seed because Solana simulation CU is deterministic for fixed account data; the eight independently generated transcripts are the variance population.".to_string(),
            "The seed-1 corruption suite changes every second OOD value, both v4 helper claims, and each committed 64-byte half of the first authenticated C2 leaf, requiring rejection by host and production VerifyWithClaim on SBF.".to_string(),
            "Every paired and corruption simulation uses the standard 1,400,000-CU limit plus 262,144-byte heap-frame request; absolute v3/v4 CU is comparable to the production measurement envelope.".to_string(),
            "The paired CU delta prices s=2 plus the second 128-byte-leaf helper within the scalar-C1 PCS scaffold. It does not price the normative 49-column authenticated C1 representation or its k'=51 recombination.".to_string(),
            "The tag-21 exact-wide diagnostic is a separate replacement seam, not an additive line item: its 36-fiber prepared-byte CU must not be added wholesale to this scalar-C1 verifier total.".to_string(),
            "This g16 result is a PCS-scaffold delta checkpoint, not the final q36/g32 strict-gate measurement or the final payment-v4 KAT.".to_string(),
        ],
    })
}

/// Reconciled exact-wide v4 PCS-scaffold measurement. The diagnostic-only
/// tag invokes the real proof parser, Merkle authentication, folds and final
/// checks, but replaces scalar layer-zero C1/C2 processing in place. No
/// isolated artifact totals are added together.
pub fn run_stage2_reconciled_exact_wide_v4_scaffold() -> Result<ReconciledExactWideSummary> {
    const SEEDS: u64 = 8;
    const DIAGNOSTIC_WIRE_ORDINAL: u8 = 22;
    const PRODUCTION_WIRE_ORDINAL: u8 = 6;
    const STRICT_PROJECT_THRESHOLD_CU: u64 = 1_190_000;
    const ABSOLUTE_EXECUTION_CAP_CU: u64 = VERIFY_CU_LIMIT as u64;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn layer0_unique_fibers(proof: &[u8]) -> Result<u16> {
        let c1_start = aspis_core::proof::first_layer_first_phase_opening_offset(proof)
            .context("locate exact-wide layer-zero C1 section")?;
        let count_start = c1_start
            .checked_sub(2)
            .context("layer-zero unique-count underflow")?;
        Ok(u16::from_le_bytes(
            proof[count_start..c1_start].try_into().unwrap(),
        ))
    }

    fn encoded_claim(claim: &aspis_core::EvaluationClaim) -> (Vec<[u8; 16]>, [u8; 16]) {
        let claim_z = claim
            .z
            .iter()
            .map(|coordinate| {
                let mut bytes = [0u8; 16];
                coordinate.write_le_bytes(&mut bytes);
                bytes
            })
            .collect();
        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);
        (claim_z, claim_v)
    }

    fn simulate_claim(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        statement_digest: [u8; 32],
        claim: &aspis_core::EvaluationClaim,
        diagnostic: bool,
    ) -> Result<(u64, Option<String>)> {
        let (claim_z, claim_v) = encoded_claim(claim);
        let instruction = if diagnostic {
            AspisInstruction::VerifyExactWideV4Scaffold {
                statement_digest,
                claim_z,
                claim_v,
            }
        } else {
            AspisInstruction::VerifyWithClaim {
                statement_digest,
                claim_z,
                claim_v,
            }
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                proof_instruction(&payer.pubkey(), proof_account, &instruction)?,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        let (units, error) = rpc.simulate(&transaction)?;
        Ok((
            units.context("simulation did not report compute units")?,
            error,
        ))
    }

    fn compute_budget_exhausted(error: &str) -> bool {
        error.contains("ProgramFailedToComplete") && error.contains("exceeded CUs meter")
    }

    fn accepted_threshold_outcome(units: u64, threshold: u64) -> String {
        if units <= threshold {
            format!(
                "accepted at {units} CU; {} CU below the {threshold}-CU threshold",
                threshold - units
            )
        } else {
            format!(
                "accepted at {units} CU; {} CU above the {threshold}-CU threshold",
                units - threshold
            )
        }
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 40 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let options = ProveOptions {
        fold_payload: FoldPayload::RawFibers,
        merkle_mode: MerkleMode::Radix4MinimalSubtree,
    };
    let mut measurements = Vec::with_capacity(SEEDS as usize);
    let mut seed1 = None;
    let mut production_tag6_seed1_sbf = None;

    for seed in 1..=SEEDS {
        let statement_digest = crate::host_statement_digest(seed.wrapping_add(22_000));
        let coeffs = seeded_coeffs(profile.log_rows, seed.wrapping_add(22_000));
        let claim_z = (0..profile.log_rows)
            .map(|coordinate| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(22_000 + (seed as u32).wrapping_mul(53) + coordinate),
                ))
            })
            .collect::<Vec<_>>();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &claim_z),
            z: claim_z,
        };
        let proof = prove_exact_wide_v4_scaffold_for_measurement(
            profile,
            &coeffs,
            &statement_digest,
            &claim,
            &options,
            HOST_HASH,
        );
        let header = aspis_core::proof::Header::parse(&proof)
            .with_context(|| format!("seed {seed} exact-wide header"))?;
        ensure!(
            header.has_exact_wide_c1()
                && header.version == aspis_core::proof::VERSION_V4_S2
                && header.second_phase_helper_count() == 2,
            "seed {seed} did not produce the exact-wide v4/two-helper shape"
        );
        ensure!(
            aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
                &proof,
                &statement_digest,
                Some(&claim),
                HOST_HASH,
            )
            .is_ok(),
            "seed {seed} failed diagnostic host verification"
        );
        let production_host_error =
            aspis_core::verify_with_claim(&proof, &statement_digest, Some(&claim), HOST_HASH)
                .expect_err("production host verifier accepted exact-wide scaffold flag");
        ensure!(
            production_host_error == aspis_core::VerifyError::BadHeader,
            "seed {seed} production host rejection drifted: {production_host_error:?}"
        );

        let unique = layer0_unique_fibers(&proof)?;
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
        let (observed_cu_or_cap, simulation_error) = simulate_claim(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            statement_digest,
            &claim,
            true,
        )?;
        let accepted = simulation_error.is_none();
        let exhausted = simulation_error
            .as_deref()
            .map(compute_budget_exhausted)
            .unwrap_or(false);
        ensure!(
            accepted || exhausted,
            "seed {seed} failed for a non-budget reason: {simulation_error:?}"
        );
        if exhausted {
            ensure!(
                observed_cu_or_cap == ABSOLUTE_EXECUTION_CAP_CU,
                "seed {seed} budget failure reported {observed_cu_or_cap}, expected cap {ABSOLUTE_EXECUTION_CAP_CU}"
            );
        }
        let required_lower_bound = exhausted.then_some(ABSOLUTE_EXECUTION_CAP_CU + 1);
        let outcome_vs_1_190_000 = if accepted {
            accepted_threshold_outcome(observed_cu_or_cap, STRICT_PROJECT_THRESHOLD_CU)
        } else {
            format!(
                "compute meter exhausted at {ABSOLUTE_EXECUTION_CAP_CU} CU; requires at least {} CU, at least {} CU above the {STRICT_PROJECT_THRESHOLD_CU}-CU threshold",
                ABSOLUTE_EXECUTION_CAP_CU + 1,
                ABSOLUTE_EXECUTION_CAP_CU + 1 - STRICT_PROJECT_THRESHOLD_CU
            )
        };
        let outcome_vs_1_400_000 = if accepted {
            accepted_threshold_outcome(observed_cu_or_cap, ABSOLUTE_EXECUTION_CAP_CU)
        } else {
            format!(
                "compute meter exhausted at {ABSOLUTE_EXECUTION_CAP_CU} CU; requires more than the execution cap (lower bound {} CU)",
                ABSOLUTE_EXECUTION_CAP_CU + 1
            )
        };

        measurements.push(ReconciledExactWideSeedMeasurement {
            seed,
            proof_bytes: proof.len(),
            proof_sha256: hex(&HOST_HASH(&[&proof])),
            layer0_unique_fibers: unique,
            authenticated_c1_opening_bytes: usize::from(unique)
                * aspis_core::proof::EXACT_WIDE_C1_FIBER_LEN,
            authenticated_c2_opening_bytes: usize::from(unique)
                * aspis_core::proof::SECOND_PHASE_LEAF_LEN_V4_S2,
            diagnostic_host_accepted: true,
            production_host_rejected_bad_header: true,
            observed_cu_or_cap,
            simulation_error: simulation_error.clone(),
            accepted_at_1_400_000_limit: accepted,
            compute_budget_exhausted: exhausted,
            exact_cu_if_accepted: accepted.then_some(observed_cu_or_cap),
            required_cu_lower_bound_if_exhausted: required_lower_bound,
            signed_headroom_vs_1_190_000_if_accepted: accepted
                .then_some(STRICT_PROJECT_THRESHOLD_CU as i64 - observed_cu_or_cap as i64),
            signed_headroom_vs_1_400_000_if_accepted: accepted
                .then_some(ABSOLUTE_EXECUTION_CAP_CU as i64 - observed_cu_or_cap as i64),
            minimum_breach_vs_1_190_000_if_exhausted: required_lower_bound
                .map(|lower| lower - STRICT_PROJECT_THRESHOLD_CU),
            minimum_breach_vs_1_400_000_if_exhausted: required_lower_bound
                .map(|lower| lower - ABSOLUTE_EXECUTION_CAP_CU),
            outcome_vs_1_190_000,
            outcome_vs_1_400_000,
        });

        if seed == 1 {
            let (units, error) = simulate_claim(
                &rpc,
                &payer,
                &proof_account.pubkey(),
                statement_digest,
                &claim,
                false,
            )?;
            let error = error.context("production tag 6 unexpectedly accepted wide flag on SBF")?;
            ensure!(
                !compute_budget_exhausted(&error),
                "production tag 6 reached the wide work instead of rejecting the flag"
            );
            production_tag6_seed1_sbf = Some((units, error));
            seed1 = Some((statement_digest, claim, proof));
        }

        eprintln!(
            "stage2-v4-exact-wide-reconciled: seed {seed}/{SEEDS} unique={unique} cu_or_cap={observed_cu_or_cap} accepted={accepted} exhausted={exhausted}"
        );
    }

    let (corruption_digest, corruption_claim, proof) =
        seed1.context("seed-1 exact-wide corruption source missing")?;
    let c1_start = aspis_core::proof::first_layer_first_phase_opening_offset(&proof)
        .context("locate seed-1 C1 opening")?;
    let c2_start = aspis_core::proof::first_layer_second_phase_opening_offset(&proof)
        .context("locate seed-1 C2 opening")?;
    let mut corrupted_proofs = Vec::with_capacity(4);

    let mut canonical_c1 = proof.clone();
    let limb = u32::from_le_bytes(canonical_c1[c1_start..c1_start + 4].try_into().unwrap());
    let changed = if limb + 1 == aspis_core::field::P {
        0
    } else {
        limb + 1
    };
    canonical_c1[c1_start..c1_start + 4].copy_from_slice(&changed.to_le_bytes());
    corrupted_proofs.push((
        "first_c1_leaf",
        "canonical_committed_mutation",
        c1_start,
        canonical_c1,
    ));

    let mut canonical_c2 = proof.clone();
    let limb = u32::from_le_bytes(canonical_c2[c2_start..c2_start + 4].try_into().unwrap());
    let changed = if limb + 1 == aspis_core::field::P {
        0
    } else {
        limb + 1
    };
    canonical_c2[c2_start..c2_start + 4].copy_from_slice(&changed.to_le_bytes());
    corrupted_proofs.push((
        "first_c2_leaf",
        "canonical_committed_mutation",
        c2_start,
        canonical_c2,
    ));

    let mut noncanonical_c1 = proof.clone();
    noncanonical_c1[c1_start..c1_start + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
    corrupted_proofs.push((
        "first_c1_limb",
        "noncanonical_field_limb",
        c1_start,
        noncanonical_c1,
    ));

    let mut noncanonical_c2 = proof.clone();
    noncanonical_c2[c2_start..c2_start + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
    corrupted_proofs.push((
        "first_c2_limb",
        "noncanonical_field_limb",
        c2_start,
        noncanonical_c2,
    ));

    let mut corruption_cases = Vec::with_capacity(corrupted_proofs.len());
    for (target, kind, proof_byte_offset, corrupted) in corrupted_proofs {
        let host_error = aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("exact-wide corruption unexpectedly passed host verification");
        if kind == "noncanonical_field_limb" {
            ensure!(
                host_error == aspis_core::VerifyError::NonCanonicalValue,
                "{target} host rejection was not NonCanonicalValue: {host_error:?}"
            );
        }
        let account = Keypair::new();
        upload_proof(&rpc, &payer, &account, &corrupted, true)?;
        let (_, sbf_error) = simulate_claim(
            &rpc,
            &payer,
            &account.pubkey(),
            corruption_digest,
            &corruption_claim,
            true,
        )?;
        let sbf_error = sbf_error.context("corruption unexpectedly passed on SBF")?;
        let sbf_compute_budget_exhausted = compute_budget_exhausted(&sbf_error);
        let sbf_rejection_conclusive = !sbf_compute_budget_exhausted;
        if kind == "noncanonical_field_limb" {
            ensure!(
                sbf_rejection_conclusive,
                "{target} hit the compute cap before its noncanonical check"
            );
        }
        corruption_cases.push(ReconciledExactWideCorruptionCase {
            target,
            kind,
            proof_byte_offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_error,
            sbf_compute_budget_exhausted,
            sbf_rejection_conclusive,
        });
    }

    let accepted_seed_count = measurements
        .iter()
        .filter(|row| row.accepted_at_1_400_000_limit)
        .count();
    let compute_budget_exhausted_seed_count = measurements
        .iter()
        .filter(|row| row.compute_budget_exhausted)
        .count();
    let accepted_units = measurements
        .iter()
        .filter_map(|row| row.exact_cu_if_accepted)
        .collect::<Vec<_>>();
    let exact_accepted_cu_mean = (!accepted_units.is_empty())
        .then(|| accepted_units.iter().sum::<u64>() as f64 / accepted_units.len() as f64);
    let threshold_1_190_000_observation = if compute_budget_exhausted_seed_count > 0 {
        format!(
            "{compute_budget_exhausted_seed_count}/{SEEDS} seeds exhausted the 1,400,000-CU meter; each therefore requires at least 1,400,001 CU, at least 210,001 CU above 1,190,000"
        )
    } else {
        format!(
            "all {SEEDS} seeds returned exact CU under the execution cap; see per-seed signed headroom versus 1,190,000"
        )
    };
    let threshold_1_400_000_observation = if compute_budget_exhausted_seed_count > 0 {
        format!(
            "{compute_budget_exhausted_seed_count}/{SEEDS} seeds exhausted the 1,400,000-CU meter and have a per-seed required-CU lower bound of 1,400,001"
        )
    } else {
        format!("all {SEEDS} seeds accepted at the 1,400,000-CU limit")
    };
    let (production_tag6_seed1_sbf_cu, production_tag6_seed1_sbf_error) =
        production_tag6_seed1_sbf.context("seed-1 production tag-6 check missing")?;

    Ok(ReconciledExactWideSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-v4-exact-wide-reconciled",
        validator_version: validator_version(),
        profile: profile.name,
        statement_kind: "diagnostic exact-wide PCS scaffold: honest column 0, authenticated zero columns 1..48, two synthetic nonzero C2 helpers",
        is_payment_proof: false,
        diagnostic_verify_instruction_wire_ordinal: DIAGNOSTIC_WIRE_ORDINAL,
        production_verify_with_claim_wire_ordinal: PRODUCTION_WIRE_ORDINAL,
        production_verify_with_claim_accepts_wide_flag: false,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        strict_project_threshold_cu: STRICT_PROJECT_THRESHOLD_CU,
        absolute_execution_cap_cu: ABSOLUTE_EXECUTION_CAP_CU,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + diagnostic tag 22 exact-wide scaffold verifier",
        merkle_mode: "radix4_minimal_subtree",
        seeds: SEEDS,
        c1_columns: aspis_core::proof::EXACT_WIDE_C1_COLUMNS,
        c1_leaf_bytes: aspis_core::proof::EXACT_WIDE_C1_FIBER_LEN,
        c2_columns: 2,
        c2_leaf_bytes: aspis_core::proof::SECOND_PHASE_LEAF_LEN_V4_S2,
        auxiliary_c1_columns: "columns 1..48 are committed zero columns; every canonical byte is authenticated, parsed and processed by the 49-lane kernel",
        observed_cu_or_cap_min: measurements
            .iter()
            .map(|row| row.observed_cu_or_cap)
            .min()
            .context("empty exact-wide measurements")?,
        observed_cu_or_cap_max: measurements
            .iter()
            .map(|row| row.observed_cu_or_cap)
            .max()
            .context("empty exact-wide measurements")?,
        measurements,
        accepted_seed_count,
        compute_budget_exhausted_seed_count,
        all_seed_outcomes_classified: accepted_seed_count + compute_budget_exhausted_seed_count
            == SEEDS as usize,
        exact_accepted_cu_mean,
        threshold_1_190_000_observation,
        threshold_1_400_000_observation,
        production_tag6_seed1_sbf_rejected: true,
        production_tag6_seed1_sbf_cu,
        production_tag6_seed1_sbf_error,
        canonical_mutations_rejected_host: corruption_cases
            .iter()
            .filter(|case| case.kind == "canonical_committed_mutation")
            .all(|case| case.host_rejected),
        noncanonical_limbs_rejected_host_and_sbf_conclusively: corruption_cases
            .iter()
            .filter(|case| case.kind == "noncanonical_field_limb")
            .all(|case| case.host_rejected && case.sbf_rejection_conclusive),
        corruption_cases,
        owner_ruling_made: false,
        overlap_replacement: vec![
            "retained: v4/s2 transcript, relation sumchecks, query derivation, C2 authentication, deeper-layer Merkle/folds, final polynomial, and grinding".to_string(),
            "removed in the flagged branch: scalar 32-byte C1 parse/hash plus C1 + gamma*C2[0] + gamma^2*C2[1] materialization".to_string(),
            "inserted at the same layer-zero seam: 1,568-byte C1 authentication and once-prepared canonical-byte 49-CM31 + 2-QM31 combination at gamma powers 0..50".to_string(),
            "no CU total from v4_s2_pcs_scaffold_g16.json or exact_wide_v4_diagnostic.json is arithmetically added to this measurement".to_string(),
        ],
        excluded_work: vec![
            "the second statement point and all 102 pre-gamma C1/C2 evaluation values".to_string(),
            "randomized ConstraintId registry, payment constraint composition, and LogUp payment semantics".to_string(),
            "masking/hiding, pool/nullifier/output transition, and proof-account sealing".to_string(),
            "final q36/g32 grinding profile; this uses the registered q36/g16 variance population".to_string(),
            "the pending M31-column alternative; this artifact measures only the reviewed 49-CM31 basis".to_string(),
        ],
        notes: vec![
            "This is a reconciled in-place PCS-scaffold measurement, not a full payment integration and not a product/architecture ruling.".to_string(),
            "Production VerifyWithClaim tag 6 rejects FLAG_EXACT_WIDE_C1 with BadHeader. Append-only diagnostic tag 22 is the only SBF dispatch that enables the scaffold until final 102-value semantics land.".to_string(),
            "Proof generation and proof-account upload occur outside the measured transaction. Every measured simulation uses the same 1,400,000-CU limit and 262,144-byte heap request.".to_string(),
            "A compute-budget failure reports the exact 1,400,000-CU meter observation and a required-CU lower bound of 1,400,001; it does not invent an exact total above the cap.".to_string(),
            "Canonical committed-leaf mutations are conclusive on host; when SBF reaches the cap before Merkle rejection, the case is labeled non-conclusive rather than credited. Noncanonical C1/C2 limbs must reject conclusively on both host and SBF.".to_string(),
        ],
    })
}

/// Decision-packet-only arithmetic and first-fold controls for the alternative
/// M31-valued circle-polynomial basis. This does not reinterpret an Aspis
/// proof or select a protocol architecture.
pub fn run_stage2_m31_circle_basis_probe() -> Result<M31CircleBasisSummary> {
    use aspis_core::field::{
        m31_batch_inverse, qm31_circle_to_line_fold4, qm31_m31_dot, qm31_m31_dot4,
        qm31_m31_dot4_prepared_bytes, qm31_power_table, CM31, M31, P, QM31,
    };
    use aspis_core::verify::{domain_point, layer_geometry};

    const REPETITIONS: usize = 5;
    const STRICT_TARGET: i64 = 1_190_000;
    const ABSOLUTE_CAP: i64 = 1_400_000;
    const GAMMA_BYTES: usize = 16;
    const RLC_FIBER_BYTES: usize = M31_CIRCLE_BASIS_C1_LEAF_BYTES + M31_CIRCLE_BASIS_C2_LEAF_BYTES;
    const FOLD_RECORD_BYTES: usize = 2 + 4 * 4 + 4 * 16;
    const SEED: u64 = 0x4d33_3143_4952_434c;

    fn next_m31(state: &mut u64) -> M31 {
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: aspis_core::field::CM31::new(next_m31(state), next_m31(state)),
            c1: aspis_core::field::CM31::new(next_m31(state), next_m31(state)),
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn build_rlc_fixture(mut state: u64) -> Vec<u8> {
        let gamma = next_qm31(&mut state);
        let mut fixture = vec![0u8; M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES];
        gamma.write_le_bytes(&mut fixture[..GAMMA_BYTES]);
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let start = GAMMA_BYTES + fiber * RLC_FIBER_BYTES;
            for value in fixture[start..start + M31_CIRCLE_BASIS_C1_LEAF_BYTES].chunks_exact_mut(4)
            {
                value.copy_from_slice(&next_m31(&mut state).to_le_bytes());
            }
            let c2_start = start + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
            for value in
                fixture[c2_start..c2_start + M31_CIRCLE_BASIS_C2_LEAF_BYTES].chunks_exact_mut(16)
            {
                next_qm31(&mut state).write_le_bytes(value);
            }
        }
        fixture
    }

    fn host_rlc_sink(fixture: &[u8], mode: M31CircleBasisDiagnosticMode) -> Result<[u8; 32]> {
        ensure!(
            fixture.len() == M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES,
            "bad M31 RLC fixture length"
        );
        let gamma = QM31::from_le_bytes(&fixture[..GAMMA_BYTES]).context("M31 gamma")?;
        let powers = qm31_power_table::<51>(gamma);
        let weights: &[QM31; M31_CIRCLE_BASIS_C1_COLUMNS] =
            powers[..M31_CIRCLE_BASIS_C1_COLUMNS].try_into().unwrap();
        let mut decoded = vec![M31::ZERO; 4 * M31_CIRCLE_BASIS_C1_COLUMNS];
        let mut streaming = [M31::ZERO; M31_CIRCLE_BASIS_C1_COLUMNS];
        let mut accumulator = [QM31::ZERO; 4];
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let start = GAMMA_BYTES + fiber * RLC_FIBER_BYTES;
            let c2_start = start + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
            let c1 = &fixture[start..c2_start];
            for (index, bytes) in c1.chunks_exact(4).enumerate() {
                decoded[index] =
                    M31::from_le_bytes(bytes.try_into().unwrap()).context("noncanonical M31 C1")?;
            }
            let typed = [
                &decoded[0..49],
                &decoded[49..98],
                &decoded[98..147],
                &decoded[147..196],
            ];
            let reference = core::array::from_fn(|slot| qm31_m31_dot(weights, typed[slot]));
            let four_slot = qm31_m31_dot4(weights, typed);
            ensure!(reference == four_slot, "typed M31 dot4 differential failed");
            let mut combined = match mode {
                M31CircleBasisDiagnosticMode::RlcStructuredFourDots => reference,
                M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes => {
                    qm31_m31_dot4_prepared_bytes(weights, c1).context("canonical-byte M31 dot4")?
                }
                M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4 => four_slot,
                M31CircleBasisDiagnosticMode::RlcStreamingFourDots => {
                    let mut result = [QM31::ZERO; 4];
                    let slot_bytes = M31_CIRCLE_BASIS_C1_COLUMNS * 4;
                    for (slot, result_slot) in result.iter_mut().enumerate() {
                        for (index, bytes) in c1[slot * slot_bytes..(slot + 1) * slot_bytes]
                            .chunks_exact(4)
                            .enumerate()
                        {
                            streaming[index] = M31::from_le_bytes(bytes.try_into().unwrap())
                                .context("noncanonical streaming M31 C1")?;
                        }
                        *result_slot = qm31_m31_dot(weights, &streaming);
                    }
                    result
                }
                _ => bail!("non-RLC mode passed to host M31 RLC sink"),
            };
            ensure!(combined == reference, "M31 RLC mode differential failed");
            let c2 = &fixture[c2_start..c2_start + M31_CIRCLE_BASIS_C2_LEAF_BYTES];
            for helper in 0..2 {
                for (slot, combined_slot) in combined.iter_mut().enumerate() {
                    let offset = (helper * 4 + slot) * 16;
                    let helper_value = QM31::from_le_bytes(&c2[offset..offset + 16])
                        .context("noncanonical QM31 C2")?;
                    *combined_slot = combined_slot.add(powers[49 + helper].mul(helper_value));
                }
            }
            for slot in 0..4 {
                accumulator[slot] = accumulator[slot].add(combined[slot]);
            }
        }
        let mut encoded = [0u8; 64];
        for (slot, value) in accumulator.iter().enumerate() {
            value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
        }
        Ok(HOST_HASH(&[
            b"aspis-m31-circle-basis-rlc-shape-v1",
            &encoded,
        ]))
    }

    fn build_fold_fixture(mut state: u64) -> Result<(Vec<u8>, [u8; 32])> {
        let alpha = next_qm31(&mut state);
        let geometry = layer_geometry(&PROFILE_CAPACITY_LR10_Q36_G16, 0);
        let mut fixture = vec![0u8; M31_CIRCLE_FOLD_FIXTURE_BYTES];
        alpha.write_le_bytes(&mut fixture[..16]);
        let mut reference = QM31::ZERO;
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let index = fiber as u16;
            let point = domain_point(&geometry, u32::from(index));
            ensure!(point.a != M31::ZERO && point.b != M31::ZERO);
            let coefficients = core::array::from_fn::<_, 4, _>(|_| next_qm31(&mut state));
            let evaluate = |x: M31, y: M31| {
                coefficients[0]
                    .add(coefficients[1].mul_m31(y))
                    .add(coefficients[2].mul_m31(x))
                    .add(coefficients[3].mul_m31(x.mul(y)))
            };
            let minus_x = M31::ZERO.sub(point.a);
            let minus_y = M31::ZERO.sub(point.b);
            let values = [
                evaluate(point.a, point.b),
                evaluate(point.a, minus_y),
                evaluate(minus_x, minus_y),
                evaluate(minus_x, point.b),
            ];
            let expected = coefficients[0]
                .add(alpha.mul(coefficients[1]))
                .add(alpha.square().mul(coefficients[2]))
                .add(alpha.square().mul(alpha).mul(coefficients[3]));
            ensure!(
                qm31_circle_to_line_fold4(
                    values,
                    alpha,
                    point.a.double().inv(),
                    point.b.double().inv(),
                ) == expected,
                "circle-fold cubic differential failed"
            );
            reference = reference.add(expected);
            let start = 16 + fiber * FOLD_RECORD_BYTES;
            fixture[start..start + 2].copy_from_slice(&index.to_le_bytes());
            fixture[start + 2..start + 6].copy_from_slice(&point.a.to_le_bytes());
            fixture[start + 6..start + 10].copy_from_slice(&point.b.to_le_bytes());
            fixture[start + 10..start + 14].copy_from_slice(&point.a.inv().to_le_bytes());
            fixture[start + 14..start + 18].copy_from_slice(&point.b.inv().to_le_bytes());
            for (slot, value) in values.iter().enumerate() {
                value.write_le_bytes(&mut fixture[start + 18 + slot * 16..][..16]);
            }
        }
        let mut encoded = [0u8; 16];
        reference.write_le_bytes(&mut encoded);
        Ok((
            fixture,
            HOST_HASH(&[b"aspis-m31-circle-basis-fold-control-v1", &encoded]),
        ))
    }

    fn host_fold_sink(
        fixture: &[u8],
        derive_coordinates: bool,
        batch_invert: bool,
    ) -> Result<[u8; 32]> {
        ensure!(fixture.len() == M31_CIRCLE_FOLD_FIXTURE_BYTES);
        let alpha = QM31::from_le_bytes(&fixture[..16]).context("fold alpha")?;
        let geometry = layer_geometry(&PROFILE_CAPACITY_LR10_Q36_G16, 0);
        let mut omega_powers = [CM31::ONE; aspis_core::params::CIRCLE_LOG_ORDER as usize];
        omega_powers[0] = geometry.omega;
        for bit in 1..omega_powers.len() {
            omega_powers[bit] = omega_powers[bit - 1].square();
        }
        let cached_point = |mut index: u32| {
            let mut point = geometry.offset;
            let mut bit = 0usize;
            while index != 0 {
                if index & 1 != 0 {
                    point = point.mul(omega_powers[bit]);
                }
                index >>= 1;
                bit += 1;
            }
            point
        };
        let mut coords = vec![M31::ZERO; 2 * M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
        let mut inverses = vec![M31::ZERO; 2 * M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
        let mut all_values = vec![[QM31::ZERO; 4]; M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
        let mut previous = None;
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let start = 16 + fiber * FOLD_RECORD_BYTES;
            let index = u16::from_le_bytes(fixture[start..start + 2].try_into().unwrap());
            ensure!(previous.is_none_or(|value| index > value));
            previous = Some(index);
            let x = M31::from_le_bytes(fixture[start + 2..start + 6].try_into().unwrap())
                .context("fold x")?;
            let y = M31::from_le_bytes(fixture[start + 6..start + 10].try_into().unwrap())
                .context("fold y")?;
            if derive_coordinates {
                let point = cached_point(u32::from(index));
                ensure!(point.a == x && point.b == y && x != M31::ZERO && y != M31::ZERO);
                coords[2 * fiber] = x;
                coords[2 * fiber + 1] = y;
            }
            if !batch_invert {
                let inv_x = M31::from_le_bytes(fixture[start + 10..start + 14].try_into().unwrap())
                    .context("fold inv x")?;
                let inv_y = M31::from_le_bytes(fixture[start + 14..start + 18].try_into().unwrap())
                    .context("fold inv y")?;
                inverses[2 * fiber] = inv_x;
                inverses[2 * fiber + 1] = inv_y;
            }
            for slot in 0..4 {
                all_values[fiber][slot] = QM31::from_le_bytes(
                    &fixture[start + 18 + slot * 16..start + 18 + (slot + 1) * 16],
                )
                .context("fold value")?;
            }
        }
        if batch_invert {
            m31_batch_inverse(&coords, &mut inverses);
        }
        let mut accumulator = QM31::ZERO;
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            accumulator = accumulator.add(qm31_circle_to_line_fold4(
                all_values[fiber],
                alpha,
                inverses[2 * fiber].half(),
                inverses[2 * fiber + 1].half(),
            ));
        }
        let mut encoded = [0u8; 16];
        accumulator.write_le_bytes(&mut encoded);
        Ok(HOST_HASH(&[
            b"aspis-m31-circle-basis-fold-control-v1",
            &encoded,
        ]))
    }

    fn mean(values: &[u64]) -> f64 {
        values.iter().sum::<u64>() as f64 / values.len() as f64
    }

    let rlc_fixture = build_rlc_fixture(SEED);
    let structured_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcStructuredFourDots,
    )?;
    let fused_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
    )?;
    let decoded_fused_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4,
    )?;
    let streaming_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcStreamingFourDots,
    )?;
    ensure!(structured_sink == fused_sink);
    ensure!(structured_sink == decoded_fused_sink);
    ensure!(structured_sink == streaming_sink);
    let empty_leaf_sink = aspis_core::merkle::leaf_hash(HOST_HASH, 0, &[]);
    let c1_leaf_sink = aspis_core::merkle::leaf_hash(
        HOST_HASH,
        0,
        &rlc_fixture[GAMMA_BYTES..GAMMA_BYTES + M31_CIRCLE_BASIS_C1_LEAF_BYTES],
    );
    let (fold_fixture, fold_reference_sink) = build_fold_fixture(SEED ^ 0x464f_4c44)?;
    let fold_prevalidated_sink = host_fold_sink(&fold_fixture, false, false)?;
    let fold_cached_sink = host_fold_sink(&fold_fixture, true, false)?;
    let fold_derived_sink = host_fold_sink(&fold_fixture, true, true)?;
    ensure!(fold_reference_sink == fold_prevalidated_sink);
    ensure!(fold_prevalidated_sink == fold_cached_sink);
    ensure!(fold_prevalidated_sink == fold_derived_sink);

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 30 * LAMPORTS_PER_SOL)?;
    let rlc_account = Keypair::new();
    upload_proof(&rpc, &payer, &rlc_account, &rlc_fixture, true)?;
    let fold_account = Keypair::new();
    upload_proof(&rpc, &payer, &fold_account, &fold_fixture, true)?;

    let run_mode = |account: &Pubkey,
                    mode: M31CircleBasisDiagnosticMode,
                    sink: [u8; 32]|
     -> Result<(Vec<u64>, Vec<Option<String>>)> {
        let mut units = Vec::with_capacity(REPETITIONS);
        let mut errors = Vec::with_capacity(REPETITIONS);
        for _ in 0..REPETITIONS {
            let instruction = proof_instruction(
                &payer.pubkey(),
                account,
                &AspisInstruction::M31CircleBasisDiagnostic {
                    mode,
                    expected_sink: sink,
                },
            )?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                    instruction,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                rpc.latest_blockhash()?,
            );
            let (observed, error) = rpc.simulate(&transaction)?;
            units.push(observed.context("M31 diagnostic did not report CU")?);
            errors.push(error);
        }
        Ok((units, errors))
    };

    let mode_specs = [
        (
            "rlc_structured_four_independent_qm31_m31_dot",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcStructuredFourDots,
            structured_sink,
        ),
        (
            "rlc_fused_canonical_bytes_qm31_m31_dot4",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
            fused_sink,
        ),
        (
            "empty_leaf_hash_control",
            &rlc_account,
            M31CircleBasisDiagnosticMode::EmptyLeafHashControl,
            empty_leaf_sink,
        ),
        (
            "c1_leaf_hash_784_bytes",
            &rlc_account,
            M31CircleBasisDiagnosticMode::C1LeafHash784,
            c1_leaf_sink,
        ),
        (
            "fold_prevalidated_coordinates_control",
            &fold_account,
            M31CircleBasisDiagnosticMode::FoldPrevalidatedCoordinates,
            fold_prevalidated_sink,
        ),
        (
            "fold_cached_coordinates_prevalidated_inverses_control",
            &fold_account,
            M31CircleBasisDiagnosticMode::FoldCachedCoordinatesPrevalidatedInverses,
            fold_cached_sink,
        ),
        (
            "fold_cached_coordinates_batch_inverse_syscall",
            &fold_account,
            M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse,
            fold_derived_sink,
        ),
        (
            "rlc_decoded_then_typed_fused_qm31_m31_dot4",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4,
            decoded_fused_sink,
        ),
        (
            "rlc_streaming_one_slot_four_independent_qm31_m31_dot",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcStreamingFourDots,
            streaming_sink,
        ),
    ];
    let mut variants = Vec::with_capacity(mode_specs.len());
    for (name, account, mode, sink) in mode_specs {
        let (simulation_cu, errors) = run_mode(&account.pubkey(), mode, sink)?;
        ensure!(
            errors.iter().all(Option::is_none),
            "{name} failed: {errors:?}"
        );
        let simulation_cu_mean = mean(&simulation_cu);
        variants.push(M31CircleBasisVariant {
            mode: name,
            expected_host_sink_hex: hex(&sink),
            accepted_all: true,
            simulation_cu,
            simulation_cu_mean,
            signed_headroom_vs_1_190_000_cu: STRICT_TARGET - simulation_cu_mean.round() as i64,
            signed_headroom_vs_1_400_000_cu: ABSOLUTE_CAP - simulation_cu_mean.round() as i64,
        });
    }

    let mut corruptions = Vec::new();
    let mut noncanonical_c1 = rlc_fixture.clone();
    noncanonical_c1[GAMMA_BYTES..GAMMA_BYTES + 4].copy_from_slice(&P.to_le_bytes());
    let noncanonical_c1_decoded_fused = noncanonical_c1.clone();
    let noncanonical_c1_streaming = noncanonical_c1.clone();
    let mut noncanonical_c2 = rlc_fixture.clone();
    let c2_offset = GAMMA_BYTES + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
    noncanonical_c2[c2_offset..c2_offset + 4].copy_from_slice(&P.to_le_bytes());
    let mut wrong_coordinate = fold_fixture.clone();
    let coordinate_offset = 16 + 2;
    let coordinate = u32::from_le_bytes(
        wrong_coordinate[coordinate_offset..coordinate_offset + 4]
            .try_into()
            .unwrap(),
    );
    wrong_coordinate[coordinate_offset..coordinate_offset + 4]
        .copy_from_slice(&((coordinate + 1) % P).to_le_bytes());
    let mut wrong_slot_order = fold_fixture.clone();
    let slot_start = 16 + 18;
    for byte in 0..16 {
        wrong_slot_order.swap(slot_start + byte, slot_start + 16 + byte);
    }

    let corruption_specs = [
        (
            "noncanonical_c1_m31",
            "rlc",
            GAMMA_BYTES,
            noncanonical_c1,
            M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
            fused_sink,
        ),
        (
            "noncanonical_c2_qm31",
            "rlc",
            c2_offset,
            noncanonical_c2,
            M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
            fused_sink,
        ),
        (
            "mutated_domain_coordinate",
            "fold",
            coordinate_offset,
            wrong_coordinate,
            M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse,
            fold_derived_sink,
        ),
        (
            "wrong_four_slot_order",
            "fold",
            slot_start,
            wrong_slot_order,
            M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse,
            fold_derived_sink,
        ),
        (
            "noncanonical_c1_m31_decoded_fused",
            "rlc",
            GAMMA_BYTES,
            noncanonical_c1_decoded_fused,
            M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4,
            decoded_fused_sink,
        ),
        (
            "noncanonical_c1_m31_streaming",
            "rlc",
            GAMMA_BYTES,
            noncanonical_c1_streaming,
            M31CircleBasisDiagnosticMode::RlcStreamingFourDots,
            streaming_sink,
        ),
    ];
    for (target, fixture_name, offset, corrupted, mode, expected) in corruption_specs {
        let host_rejected = match fixture_name {
            "rlc" => host_rlc_sink(&corrupted, mode).map_or(true, |sink| sink != expected),
            "fold" => host_fold_sink(&corrupted, true, true).map_or(true, |sink| sink != expected),
            _ => unreachable!(),
        };
        ensure!(host_rejected, "{target} lacked host teeth");
        let account = Keypair::new();
        upload_proof(&rpc, &payer, &account, &corrupted, true)?;
        let (_, errors) = run_mode(&account.pubkey(), mode, expected)?;
        let sbf_rejected = errors.iter().all(Option::is_some);
        ensure!(sbf_rejected, "{target} accepted on SBF");
        corruptions.push(M31CircleBasisCorruptionCase {
            target,
            fixture: fixture_name,
            fixture_byte_offset: offset,
            host_rejected,
            sbf_rejected,
            sbf_error: errors.into_iter().flatten().next().unwrap(),
        });
    }

    let structured = variants[0].simulation_cu_mean;
    let fused = variants[1].simulation_cu_mean;
    let empty_leaf = variants[2].simulation_cu_mean;
    let c1_leaf = variants[3].simulation_cu_mean;
    let fold_control = variants[4].simulation_cu_mean;
    let fold_cached = variants[5].simulation_cu_mean;
    let fold_derived = variants[6].simulation_cu_mean;
    let decoded_fused = variants[7].simulation_cu_mean;
    let streaming = variants[8].simulation_cu_mean;
    let winning_rlc_variant = variants
        .iter()
        .filter(|variant| variant.mode.starts_with("rlc_"))
        .min_by(|left, right| left.simulation_cu_mean.total_cmp(&right.simulation_cu_mean))
        .context("missing M31 RLC variant")?;
    let winning_rlc_mode = winning_rlc_variant.mode;
    let winning_rlc_cu_mean = winning_rlc_variant.simulation_cu_mean;
    Ok(M31CircleBasisSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-m31-circle-basis-probe",
        validator_version: validator_version(),
        status: "decision_packet_only_provisional_shape_probe",
        diagnostic_instruction_wire_ordinal: 23,
        repetitions: REPETITIONS,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + diagnostic tag 23",
        structural_fibers: M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS,
        c1_field: "M31 candidate circle-polynomial code symbols",
        c1_columns: M31_CIRCLE_BASIS_C1_COLUMNS,
        c1_leaf_bytes: M31_CIRCLE_BASIS_C1_LEAF_BYTES,
        c2_field: "QM31 helpers, unchanged shape",
        c2_columns: 2,
        c2_leaf_bytes: M31_CIRCLE_BASIS_C2_LEAF_BYTES,
        gamma_powers: "0..50 prepared exactly once per measured instruction; helpers use 49 and 50",
        rlc_fixture_bytes: M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES,
        fold_fixture_bytes: M31_CIRCLE_FOLD_FIXTURE_BYTES,
        host_structured_equals_fused: true,
        host_all_rlc_modes_equal: true,
        host_normalized_fold_matches_cubic_reference: true,
        variants,
        fused_rlc_savings_cu: (structured - fused).round() as i64,
        fused_rlc_savings_percent: (structured - fused) / structured * 100.0,
        decoded_fused_rlc_savings_vs_structured_cu: (structured - decoded_fused).round() as i64,
        decoded_fused_rlc_savings_vs_structured_percent: (structured - decoded_fused) / structured
            * 100.0,
        streaming_rlc_savings_vs_structured_cu: (structured - streaming).round() as i64,
        streaming_rlc_savings_vs_structured_percent: (structured - streaming) / structured * 100.0,
        winning_rlc_mode,
        winning_rlc_cu_mean,
        winning_rlc_savings_vs_structured_cu: (structured - winning_rlc_cu_mean).round() as i64,
        winning_rlc_savings_vs_structured_percent: (structured - winning_rlc_cu_mean) / structured
            * 100.0,
        c1_leaf_hash_incremental_over_empty_cu: (c1_leaf - empty_leaf).round() as i64,
        fold_cached_coordinate_derivation_increment_cu: (fold_cached - fold_control).round() as i64,
        fold_batch_inverse_syscall_increment_cu: (fold_derived - fold_cached).round() as i64,
        fold_coordinate_and_batch_inverse_increment_cu: (fold_derived - fold_control).round() as i64,
        fold_batch_inverse_backend: "one sol_big_mod_exp M31 inverse for 72 denominators, with Montgomery prefix/suffix products; host differential uses software M31::inv",
        all_corruptions_rejected: corruptions
            .iter()
            .all(|case| case.host_rejected && case.sbf_rejected),
        corruption_cases: corruptions,
        current_aspis_serialization: false,
        genuine_circle_pcs_integration_implemented: false,
        protocol_or_architecture_ruling_made: false,
        included_work: vec![
            "RLC control: 36 structural fibers, 4x49 canonical M31 C1 values, 2x4 canonical QM31 C2 helpers, and gamma powers 0..50 prepared once".to_string(),
            "fold control: normalized circle-to-line then line fold over 36 already-combined four-QM31 fibers".to_string(),
            "bookable fold row includes public-domain coordinate derivation and one 72-element M31 batch inversion; the prevalidated row is a separately labeled control".to_string(),
            "append-only RLC separation rows isolate canonical decode plus typed dot4 from a one-slot fixed-buffer streaming decode plus four independent dots".to_string(),
        ],
        excluded_work: vec![
            "no current Aspis proof parsing, serialization, root, Merkle frontier, or authentication".to_string(),
            "no circle FFT encoder, bit-reversed trace-to-codeword conformance, query sampling, or later line-FRI layers".to_string(),
            "no OOD relation, statement sumcheck, final polynomial, payment constraints, hiding, pool transition, or proof-account sealing".to_string(),
            "RLC and fold rows are disjoint controls and must not be added as an integrated-v4 total".to_string(),
        ],
        notes: vec![
            "M31 C1 is valid only under a genuine circle-polynomial PCS; dropping the imaginary CM31 limb from the current ordinary-univariate Aspis PCS would be unsound".to_string(),
            "The fold slot order is (x,y),(x,-y),(-x,-y),(-x,y); normalization is mechanically checked against c0+alpha*c1+alpha^2*c2+alpha^3*c3".to_string(),
            "This artifact supplies costs and headrooms to a decision packet. It adopts neither a one-transaction M31 architecture nor a split architecture and changes no production verifier".to_string(),
            "The legacy fused_rlc_savings fields compare the original canonical-byte fused row with the original structured row; the explicitly named decoded-fused, streaming, and winner fields carry the reopened separation result".to_string(),
        ],
    })
}

/// Account-backed measurement of the exact candidate v4 layer-zero width.
/// Fixture generation and upload happen before every measured simulation.
pub fn run_stage2_exact_wide_v4_diagnostic() -> Result<ExactWideV4DiagnosticSummary> {
    use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
    use aspis_statement::wide_v4::{
        ExactWideFiber, C1_COLUMNS, C1_FIBER_BYTES, C2_COLUMNS, C2_FIBER_BYTES, FIBER_SLOTS,
        TOTAL_COLUMNS,
    };

    const REPETITIONS: usize = 5;
    const FIXTURE_SEED: u64 = 0x4558_4143_5457_5634;
    const GAMMA_BYTES: usize = 16;
    const FIXTURE_BYTES: usize = GAMMA_BYTES + C1_FIBER_BYTES + C2_FIBER_BYTES;

    fn next_m31(state: &mut u64) -> M31 {
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
    }

    fn next_cm31(state: &mut u64) -> CM31 {
        CM31::new(next_m31(state), next_m31(state))
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: next_cm31(state),
            c1: next_cm31(state),
        }
    }

    fn build_fixture(seed: u64) -> (Vec<u8>, QM31, ExactWideFiber) {
        let mut state = seed;
        let gamma = next_qm31(&mut state);
        let fiber = ExactWideFiber {
            c1: core::array::from_fn(|_| core::array::from_fn(|_| next_cm31(&mut state))),
            c2: core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state))),
        };
        let mut encoded = vec![0u8; FIXTURE_BYTES];
        gamma.write_le_bytes(&mut encoded[..GAMMA_BYTES]);
        let c1_start = GAMMA_BYTES;
        for slot in 0..FIBER_SLOTS {
            for column in 0..C1_COLUMNS {
                let offset = c1_start + (slot * C1_COLUMNS + column) * 8;
                fiber.c1[slot][column].write_le_bytes(&mut encoded[offset..offset + 8]);
            }
        }
        // Canonical v4 C2 wire order is helper-major, while the arithmetic
        // seam is slot-major.
        let c2_start = c1_start + C1_FIBER_BYTES;
        for helper in 0..C2_COLUMNS {
            for slot in 0..FIBER_SLOTS {
                let offset = c2_start + (helper * FIBER_SLOTS + slot) * 16;
                fiber.c2[slot][helper].write_le_bytes(&mut encoded[offset..offset + 16]);
            }
        }
        (encoded, gamma, fiber)
    }

    fn build_batch_fixture(seed: u64, fibers: usize) -> (Vec<u8>, QM31, Vec<ExactWideFiber>) {
        let mut state = seed;
        let gamma = next_qm31(&mut state);
        let values = (0..fibers)
            .map(|_| ExactWideFiber {
                c1: core::array::from_fn(|_| core::array::from_fn(|_| next_cm31(&mut state))),
                c2: core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state))),
            })
            .collect::<Vec<_>>();
        let fiber_bytes = C1_FIBER_BYTES + C2_FIBER_BYTES;
        let mut encoded = vec![0u8; GAMMA_BYTES + fibers * fiber_bytes];
        gamma.write_le_bytes(&mut encoded[..GAMMA_BYTES]);
        for (index, fiber) in values.iter().enumerate() {
            let base = GAMMA_BYTES + index * fiber_bytes;
            for slot in 0..FIBER_SLOTS {
                for column in 0..C1_COLUMNS {
                    let offset = base + (slot * C1_COLUMNS + column) * 8;
                    fiber.c1[slot][column].write_le_bytes(&mut encoded[offset..offset + 8]);
                }
            }
            let c2_start = base + C1_FIBER_BYTES;
            for helper in 0..C2_COLUMNS {
                for slot in 0..FIBER_SLOTS {
                    let offset = c2_start + (helper * FIBER_SLOTS + slot) * 16;
                    fiber.c2[slot][helper].write_le_bytes(&mut encoded[offset..offset + 16]);
                }
            }
        }
        (encoded, gamma, values)
    }

    fn decode_fixture(bytes: &[u8]) -> Result<(QM31, ExactWideFiber)> {
        ensure!(
            bytes.len() == FIXTURE_BYTES,
            "bad exact-wide fixture length"
        );
        let gamma =
            QM31::from_le_bytes(&bytes[..GAMMA_BYTES]).context("decode exact-wide gamma")?;
        let mut fiber = ExactWideFiber {
            c1: [[CM31::ZERO; C1_COLUMNS]; FIBER_SLOTS],
            c2: [[QM31::ZERO; C2_COLUMNS]; FIBER_SLOTS],
        };
        let c1_start = GAMMA_BYTES;
        let c2_start = c1_start + C1_FIBER_BYTES;
        for slot in 0..FIBER_SLOTS {
            for column in 0..C1_COLUMNS {
                let offset = c1_start + (slot * C1_COLUMNS + column) * 8;
                fiber.c1[slot][column] = CM31::from_le_bytes(&bytes[offset..offset + 8])
                    .context("decode exact-wide C1 value")?;
            }
        }
        for helper in 0..C2_COLUMNS {
            for slot in 0..FIBER_SLOTS {
                let offset = c2_start + (helper * FIBER_SLOTS + slot) * 16;
                fiber.c2[slot][helper] = QM31::from_le_bytes(&bytes[offset..offset + 16])
                    .context("decode exact-wide C2 value")?;
            }
        }
        Ok((gamma, fiber))
    }

    fn host_sink(mode: ExactWideV4DiagnosticMode, fixture: &[u8]) -> Result<[u8; 32]> {
        let c1_start = GAMMA_BYTES;
        let c2_start = c1_start + C1_FIBER_BYTES;
        Ok(match mode {
            ExactWideV4DiagnosticMode::BaselineFourDots | ExactWideV4DiagnosticMode::FusedDot4 => {
                let (gamma, fiber) = decode_fixture(fixture)?;
                let combined = match mode {
                    ExactWideV4DiagnosticMode::BaselineFourDots => {
                        aspis_statement::wide_v4::combine_exact_wide_fiber_baseline(&fiber, gamma)
                    }
                    ExactWideV4DiagnosticMode::FusedDot4 => {
                        aspis_statement::wide_v4::combine_exact_wide_fiber(&fiber, gamma)
                    }
                    _ => unreachable!(),
                };
                let mut encoded = [0u8; FIBER_SLOTS * 16];
                for (slot, value) in combined.iter().enumerate() {
                    value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
                }
                HOST_HASH(&[b"aspis-exact-wide-v4-combined", &encoded])
            }
            ExactWideV4DiagnosticMode::EmptyLeafHashControl => {
                aspis_core::merkle::leaf_hash(HOST_HASH, 0, &[])
            }
            ExactWideV4DiagnosticMode::C1LeafHash => {
                aspis_core::merkle::leaf_hash(HOST_HASH, 0, &fixture[c1_start..c2_start])
            }
            ExactWideV4DiagnosticMode::C2LeafHash => aspis_core::merkle::leaf_hash(
                HOST_HASH,
                aspis_core::proof::SECOND_PHASE_LAYER_TAG,
                &fixture[c2_start..],
            ),
            ExactWideV4DiagnosticMode::GammaPowersControl
            | ExactWideV4DiagnosticMode::GammaPowers0To50 => {
                let gamma = QM31::from_le_bytes(&fixture[..GAMMA_BYTES])
                    .context("decode gamma for host power sink")?;
                let mut encoded = [0u8; TOTAL_COLUMNS * 16];
                match mode {
                    ExactWideV4DiagnosticMode::GammaPowersControl => {
                        for chunk in encoded.chunks_exact_mut(16) {
                            QM31::ONE.write_le_bytes(chunk);
                        }
                    }
                    ExactWideV4DiagnosticMode::GammaPowers0To50 => {
                        let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
                        for (power, chunk) in powers.iter().zip(encoded.chunks_exact_mut(16)) {
                            power.write_le_bytes(chunk);
                        }
                    }
                    _ => unreachable!(),
                }
                HOST_HASH(&[b"aspis-exact-wide-v4-powers", &encoded])
            }
            ExactWideV4DiagnosticMode::FusedBatch36Unprepared
            | ExactWideV4DiagnosticMode::FusedBatch36Prepared
            | ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes => {
                let fiber_bytes = C1_FIBER_BYTES + C2_FIBER_BYTES;
                ensure!(
                    fixture.len()
                        == GAMMA_BYTES
                            + aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS * fiber_bytes,
                    "bad exact-wide batch fixture length"
                );
                let gamma = QM31::from_le_bytes(&fixture[..GAMMA_BYTES])
                    .context("decode exact-wide batch gamma")?;
                let prepared = if matches!(
                    mode,
                    ExactWideV4DiagnosticMode::FusedBatch36Prepared
                        | ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes
                ) {
                    Some(aspis_statement::wide_v4::prepare_exact_wide_weights(gamma))
                } else {
                    None
                };
                let bytes_mode =
                    matches!(mode, ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes);
                let mut accumulator = [QM31::ZERO; FIBER_SLOTS];
                for index in 0..aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS {
                    let start = GAMMA_BYTES + index * fiber_bytes;
                    let combined = if bytes_mode {
                        let c2_start = start + C1_FIBER_BYTES;
                        aspis_statement::wide_v4::combine_exact_wide_bytes_prepared(
                            &fixture[start..c2_start],
                            &fixture[c2_start..c2_start + C2_FIBER_BYTES],
                            prepared.as_ref().unwrap(),
                        )
                        .context("decode exact-wide prepared byte fiber")?
                    } else {
                        let mut single = Vec::with_capacity(FIXTURE_BYTES);
                        single.extend_from_slice(&fixture[..GAMMA_BYTES]);
                        single.extend_from_slice(&fixture[start..start + fiber_bytes]);
                        let (_, fiber) = decode_fixture(&single)?;
                        if let Some(weights) = prepared.as_ref() {
                            aspis_statement::wide_v4::combine_exact_wide_fiber_prepared(
                                &fiber, weights,
                            )
                        } else {
                            aspis_statement::wide_v4::combine_exact_wide_fiber(&fiber, gamma)
                        }
                    };
                    for slot in 0..FIBER_SLOTS {
                        accumulator[slot] = accumulator[slot].add(combined[slot]);
                    }
                }
                let mut encoded = [0u8; FIBER_SLOTS * 16];
                for (slot, value) in accumulator.iter().enumerate() {
                    value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
                }
                HOST_HASH(&[b"aspis-exact-wide-v4-batch36", &encoded])
            }
        })
    }

    fn mode_name(mode: ExactWideV4DiagnosticMode) -> &'static str {
        match mode {
            ExactWideV4DiagnosticMode::BaselineFourDots => "baseline_four_qm31_cm31_dot_49",
            ExactWideV4DiagnosticMode::FusedDot4 => "optimized_fused_qm31_cm31_dot4_49",
            ExactWideV4DiagnosticMode::EmptyLeafHashControl => "empty_leaf_hash_control",
            ExactWideV4DiagnosticMode::C1LeafHash => "c1_leaf_hash_1568_bytes",
            ExactWideV4DiagnosticMode::C2LeafHash => "c2_leaf_hash_128_bytes",
            ExactWideV4DiagnosticMode::GammaPowersControl => {
                "gamma_power_serialization_hash_control"
            }
            ExactWideV4DiagnosticMode::GammaPowers0To50 => "gamma_powers_0_through_50",
            ExactWideV4DiagnosticMode::FusedBatch36Unprepared => {
                "q36_structural_max_36_fibers_fused_unprepared"
            }
            ExactWideV4DiagnosticMode::FusedBatch36Prepared => {
                "q36_structural_max_36_fibers_fused_prepared_once"
            }
            ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes => {
                "q36_structural_max_36_fibers_prepared_bytes"
            }
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn simulate_diagnostic(
        rpc: &Rpc,
        payer: &Keypair,
        fixture_account: &Pubkey,
        mode: ExactWideV4DiagnosticMode,
        expected_sink: [u8; 32],
    ) -> Result<(Option<u64>, Option<String>)> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(*fixture_account, false)],
            data: to_vec(&AspisInstruction::ExactWideV4Diagnostic {
                mode,
                expected_sink,
            })?,
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        rpc.simulate(&transaction)
    }

    let (fixture, gamma, fiber) = build_fixture(FIXTURE_SEED);
    ensure!(
        fixture.len() == FIXTURE_BYTES,
        "fixture encoder length drifted"
    );
    let host_baseline = aspis_statement::wide_v4::combine_exact_wide_fiber_baseline(&fiber, gamma);
    let host_fused = aspis_statement::wide_v4::combine_exact_wide_fiber(&fiber, gamma);
    ensure!(
        host_baseline == host_fused,
        "host exact-wide baseline/fused differential failed"
    );
    let (batch_fixture, batch_gamma, batch_fibers) = build_batch_fixture(
        FIXTURE_SEED,
        aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS,
    );
    ensure!(
        batch_gamma == gamma && batch_fibers.first() == Some(&fiber),
        "single and batch fixture prefixes diverged"
    );
    let host_batch_unprepared = host_sink(
        ExactWideV4DiagnosticMode::FusedBatch36Unprepared,
        &batch_fixture,
    )?;
    let host_batch_prepared = host_sink(
        ExactWideV4DiagnosticMode::FusedBatch36Prepared,
        &batch_fixture,
    )?;
    let host_batch_prepared_bytes = host_sink(
        ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
        &batch_fixture,
    )?;
    ensure!(
        host_batch_unprepared == host_batch_prepared
            && host_batch_prepared == host_batch_prepared_bytes,
        "host unprepared/structured-prepared/byte-prepared batch differential failed"
    );

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 5 * LAMPORTS_PER_SOL)?;
    let fixture_account = Keypair::new();
    let (fixture_upload_chunks, fixture_upload_cu_excluded) =
        upload_proof(&rpc, &payer, &fixture_account, &fixture, true)?;
    let batch_fixture_account = Keypair::new();
    let (batch_fixture_upload_chunks, batch_fixture_upload_cu_excluded) =
        upload_proof(&rpc, &payer, &batch_fixture_account, &batch_fixture, true)?;

    let modes = [
        ExactWideV4DiagnosticMode::BaselineFourDots,
        ExactWideV4DiagnosticMode::FusedDot4,
        ExactWideV4DiagnosticMode::EmptyLeafHashControl,
        ExactWideV4DiagnosticMode::C1LeafHash,
        ExactWideV4DiagnosticMode::C2LeafHash,
        ExactWideV4DiagnosticMode::GammaPowersControl,
        ExactWideV4DiagnosticMode::GammaPowers0To50,
        ExactWideV4DiagnosticMode::FusedBatch36Unprepared,
        ExactWideV4DiagnosticMode::FusedBatch36Prepared,
        ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
    ];
    let mut variants = Vec::with_capacity(modes.len());
    for mode in modes {
        let batch_mode = matches!(
            mode,
            ExactWideV4DiagnosticMode::FusedBatch36Unprepared
                | ExactWideV4DiagnosticMode::FusedBatch36Prepared
                | ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes
        );
        let selected_fixture = if batch_mode { &batch_fixture } else { &fixture };
        let selected_account = if batch_mode {
            batch_fixture_account.pubkey()
        } else {
            fixture_account.pubkey()
        };
        let expected_sink = host_sink(mode, selected_fixture)?;
        let mut simulation_cu = Vec::with_capacity(REPETITIONS);
        let mut simulation_errors = Vec::with_capacity(REPETITIONS);
        for _ in 0..REPETITIONS {
            let (units, error) =
                simulate_diagnostic(&rpc, &payer, &selected_account, mode, expected_sink)?;
            simulation_cu.push(units.context("exact-wide diagnostic did not report CU")?);
            simulation_errors.push(error);
        }
        ensure!(
            simulation_cu.windows(2).all(|pair| pair[0] == pair[1]),
            "{} was not deterministic: {simulation_cu:?}",
            mode_name(mode)
        );
        ensure!(
            simulation_errors.windows(2).all(|pair| pair[0] == pair[1]),
            "{} error result was not deterministic: {simulation_errors:?}",
            mode_name(mode)
        );
        let accepted_all = simulation_errors.iter().all(Option::is_none);
        if !matches!(mode, ExactWideV4DiagnosticMode::FusedBatch36Unprepared) {
            ensure!(
                accepted_all,
                "{} failed on SBF: {simulation_errors:?}",
                mode_name(mode)
            );
        }
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        variants.push(ExactWideV4DiagnosticVariant {
            mode: mode_name(mode),
            expected_host_sink_hex: hex(&expected_sink),
            sbf_matched_host_sink: accepted_all,
            accepted_all,
            simulation_cu,
            simulation_errors,
            simulation_cu_mean,
        });
    }

    fn mutate_canonical_m31(bytes: &mut [u8], offset: usize) {
        let value = u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap());
        let changed = if value + 1 == P { 0 } else { value + 1 };
        bytes[offset..offset + 4].copy_from_slice(&changed.to_le_bytes());
    }

    let c1_offset = GAMMA_BYTES;
    let c2_offset = GAMMA_BYTES + C1_FIBER_BYTES;
    let mut corrupted_c1 = fixture.clone();
    mutate_canonical_m31(&mut corrupted_c1, c1_offset);
    let mut corrupted_c2 = fixture.clone();
    mutate_canonical_m31(&mut corrupted_c2, c2_offset);
    let corrupted_inputs = [
        (
            "c1_first_cm31_limb",
            c1_offset,
            &corrupted_c1,
            ExactWideV4DiagnosticMode::BaselineFourDots,
        ),
        (
            "c1_first_cm31_limb",
            c1_offset,
            &corrupted_c1,
            ExactWideV4DiagnosticMode::FusedDot4,
        ),
        (
            "c1_first_cm31_limb",
            c1_offset,
            &corrupted_c1,
            ExactWideV4DiagnosticMode::C1LeafHash,
        ),
        (
            "c2_first_qm31_limb",
            c2_offset,
            &corrupted_c2,
            ExactWideV4DiagnosticMode::FusedDot4,
        ),
        (
            "c2_first_qm31_limb",
            c2_offset,
            &corrupted_c2,
            ExactWideV4DiagnosticMode::C2LeafHash,
        ),
    ];
    let mut corruption_cases = Vec::with_capacity(corrupted_inputs.len());
    for (target, offset, corrupted, mode) in corrupted_inputs {
        let canonical_sink = host_sink(mode, &fixture)?;
        let corrupted_sink = host_sink(mode, corrupted)?;
        ensure!(
            canonical_sink != corrupted_sink,
            "{target} did not change {} host sink",
            mode_name(mode)
        );
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, corrupted, true)?;
        let (_, error) = simulate_diagnostic(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            mode,
            canonical_sink,
        )?;
        ensure!(
            error.is_some(),
            "{target} unexpectedly matched canonical {} sink on SBF",
            mode_name(mode)
        );
        corruption_cases.push(ExactWideV4CorruptionCase {
            target,
            mode: mode_name(mode),
            fixture_byte_offset: offset,
            host_corrupted_sink_differs: true,
            host_rejected_malformed: false,
            sbf_rejected_canonical_sink: true,
            sbf_error: error.unwrap(),
        });
    }

    let malformed_batch_inputs = [
        ("noncanonical_c1_m31_limb", GAMMA_BYTES, {
            let mut bytes = batch_fixture.clone();
            bytes[GAMMA_BYTES..GAMMA_BYTES + 4].copy_from_slice(&P.to_le_bytes());
            bytes
        }),
        ("noncanonical_c2_m31_limb", GAMMA_BYTES + C1_FIBER_BYTES, {
            let mut bytes = batch_fixture.clone();
            let offset = GAMMA_BYTES + C1_FIBER_BYTES;
            bytes[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            bytes
        }),
    ];
    for (target, offset, malformed) in malformed_batch_inputs {
        ensure!(
            host_sink(
                ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
                &malformed,
            )
            .is_err(),
            "{target} unexpectedly decoded on host"
        );
        let malformed_account = Keypair::new();
        upload_proof(&rpc, &payer, &malformed_account, &malformed, true)?;
        let (_, error) = simulate_diagnostic(
            &rpc,
            &payer,
            &malformed_account.pubkey(),
            ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
            host_batch_prepared_bytes,
        )?;
        let sbf_error = error.context(format!("{target} unexpectedly accepted on SBF"))?;
        ensure!(
            sbf_error.contains("InvalidAccountData"),
            "{target} rejected for the wrong SBF reason: {sbf_error}"
        );
        corruption_cases.push(ExactWideV4CorruptionCase {
            target,
            mode: mode_name(ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes),
            fixture_byte_offset: offset,
            host_corrupted_sink_differs: false,
            host_rejected_malformed: true,
            sbf_rejected_canonical_sink: true,
            sbf_error,
        });
    }

    let baseline_mean = variants[0].simulation_cu_mean;
    let fused_mean = variants[1].simulation_cu_mean;
    let empty_hash_mean = variants[2].simulation_cu_mean;
    let fused_dot4_savings_cu = (baseline_mean - fused_mean).round() as i64;
    let batch_unprepared_accepted = variants[7].accepted_all;
    let batch_unprepared_compute_budget_exhausted = !batch_unprepared_accepted
        && variants[7].simulation_errors.iter().all(|error| {
            error.as_ref().is_some_and(|text| {
                text.contains("ComputationalBudgetExceeded")
                    || (text.contains("ProgramFailedToComplete")
                        && text.contains("exceeded CUs meter"))
            })
        });
    ensure!(
        batch_unprepared_accepted || batch_unprepared_compute_budget_exhausted,
        "unprepared q36 batch failed for a reason other than compute-budget exhaustion: {:?}",
        variants[7].simulation_errors
    );
    let batch_prepared_accepted = variants[8].accepted_all;
    let batch_unprepared_cu_mean_or_cap = variants[7].simulation_cu_mean;
    let batch_prepared_cu_mean = variants[8].simulation_cu_mean;
    let batch_prepared_bytes_accepted = variants[9].accepted_all;
    let batch_prepared_bytes_cu_mean = variants[9].simulation_cu_mean;
    let batch_prepared_savings_cu_if_exact = batch_unprepared_accepted
        .then_some((batch_unprepared_cu_mean_or_cap - batch_prepared_cu_mean).round() as i64);
    Ok(ExactWideV4DiagnosticSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-exact-wide-v4-diagnostic"
            .to_string(),
        validator_version: validator_version(),
        diagnostic_instruction_wire_ordinal: 21,
        final_payment_kat_reserved_wire_ordinal: 20,
        final_payment_kat_implemented: false,
        repetitions: REPETITIONS,
        fixture_seed: FIXTURE_SEED,
        fixture_payload_bytes: FIXTURE_BYTES,
        fixture_upload_chunks,
        fixture_upload_cu_excluded,
        batch_fixture_payload_bytes: batch_fixture.len(),
        batch_fixture_upload_chunks,
        batch_fixture_upload_cu_excluded,
        fixture_generation_in_measured_instruction: false,
        c1_columns: C1_COLUMNS,
        c2_columns: C2_COLUMNS,
        total_gamma_powers: TOTAL_COLUMNS,
        c1_leaf_bytes: C1_FIBER_BYTES,
        c2_leaf_bytes: C2_FIBER_BYTES,
        c1_layout: "slot-major: 4 slots x 49 CM31 x 8 bytes",
        c2_layout: "helper-major wire order: 2 helpers x 4 slots x 16 bytes",
        host_baseline_equals_fused: true,
        fused_dot4_savings_cu,
        fused_dot4_savings_percent: fused_dot4_savings_cu as f64 / baseline_mean * 100.0,
        c1_leaf_hash_incremental_over_empty_cu: (variants[3].simulation_cu_mean
            - empty_hash_mean)
            .round() as i64,
        c2_leaf_hash_incremental_over_empty_cu: (variants[4].simulation_cu_mean
            - empty_hash_mean)
            .round() as i64,
        gamma_powers_incremental_over_control_cu: (variants[6].simulation_cu_mean
            - variants[5].simulation_cu_mean)
            .round() as i64,
        gate_q36_batch_unique_fibers:
            aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS,
        gate_batch_count_provenance: "structural collision-free q36 maximum; verifier cost cannot rely on transcript collisions".to_string(),
        frozen_q36_fixture_unique_fibers: [35, 35],
        theoretical_q36_unique_fibers_max: 36,
        transaction_compute_limit_cu: VERIFY_CU_LIMIT,
        strict_transaction_target_cu: 1_190_000,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + ExactWideV4Diagnostic",
        batch_unprepared_accepted,
        batch_unprepared_compute_budget_exhausted,
        batch_prepared_accepted,
        batch_unprepared_cu_mean_or_cap,
        batch_prepared_cu_mean,
        batch_prepared_headroom_vs_compute_cap_cu: VERIFY_CU_LIMIT as i64
            - batch_prepared_cu_mean.round() as i64,
        batch_prepared_headroom_vs_strict_target_cu: 1_190_000
            - batch_prepared_cu_mean.round() as i64,
        batch_prepared_bytes_accepted,
        batch_prepared_bytes_cu_mean,
        batch_prepared_bytes_headroom_vs_compute_cap_cu: VERIFY_CU_LIMIT as i64
            - batch_prepared_bytes_cu_mean.round() as i64,
        batch_prepared_bytes_headroom_vs_strict_target_cu: 1_190_000
            - batch_prepared_bytes_cu_mean.round() as i64,
        batch_prepared_bytes_savings_vs_structured_cu: (batch_prepared_cu_mean
            - batch_prepared_bytes_cu_mean)
            .round() as i64,
        batch_prepared_bytes_savings_vs_structured_percent: (batch_prepared_cu_mean
            - batch_prepared_bytes_cu_mean)
            / batch_prepared_cu_mean
            * 100.0,
        batch_prepared_savings_cu_if_exact,
        batch_prepared_savings_lower_bound_cu: (batch_unprepared_cu_mean_or_cap
            - batch_prepared_cu_mean)
            .round() as i64,
        batch_prepared_bytes_savings_lower_bound_cu: (batch_unprepared_cu_mean_or_cap
            - batch_prepared_bytes_cu_mean)
            .round() as i64,
        variants,
        all_corruptions_rejected_sbf: corruption_cases
            .iter()
            .all(|case| case.sbf_rejected_canonical_sink),
        corruption_cases,
        included_work: vec![
            "account borrow, canonical field decoding, gamma powers 0..50, four independent 49-term QM31-by-CM31 dots, gamma^49/gamma^50 helper products, result serialization, and observable sink hash in baseline mode".to_string(),
            "the identical path with fused qm31_cm31_dot4 in optimized mode; the paired delta isolates the arithmetic-kernel change".to_string(),
            "Merkle leaf_hash domain framing plus SHA-256 syscall over exactly 1,568 C1 bytes or 128 C2 bytes; empty-leaf control is reported".to_string(),
            "standalone gamma power-table construction with matched 816-byte serialization/hash control".to_string(),
            "gate-relevant q36 structural maximum of 36 distinct account-backed fibers: unprepared fused setup per fiber versus one prepared gamma/weight table reused across all fibers".to_string(),
            "prepared-byte batch over the same 36 fibers: canonical CM31/QM31 parsing is fused into the dot kernel without materializing a 1,696-byte ExactWideFiber matrix".to_string(),
        ],
        excluded_work: vec![
            "fixture generation, account creation, upload transactions, rent, and upload CU".to_string(),
            "Merkle frontier/node hashing, query derivation, proof parsing beyond the fixture account envelope, and full PCS verification".to_string(),
            "102-value two-point statement framing (49 C1 + 2 C2 at z and XOR-11(z)), LogUp/payment constraints, composition, masking/hiding, and g32 grinding".to_string(),
        ],
        notes: vec![
            "This is an exact-width SBF diagnostic, not a proof and not the final payment-v4 KAT. ABI tag 20 remains reserved/inactive; this diagnostic is append-only tag 21.".to_string(),
            "All five simulations per mode are asserted bit-for-bit deterministic. Acceptance means the SBF sink equals the independently computed host sink.".to_string(),
            "C1 arithmetic is 49 CM31 values per slot because this diagnostic prices Aspis's current custom CM31-coset PCS; the two C2 helpers are QM31 terms weighted by gamma^49 and gamma^50. An M31 circle-polynomial PCS is a separate candidate protocol measured separately, not a reinterpretation of these bytes.".to_string(),
            "Absolute transaction CU includes compute-budget dispatch, program/account dispatch, fixture framing, and sink comparison. Use the paired/control deltas for kernel attribution.".to_string(),
            "Headroom fields name their denominator explicitly: the 1.4M execution cap and the separate 1.19M project target. They apply to this diagnostic transaction alone, not a composed payment proof.".to_string(),
            "The gate batch uses the collision-free q36 maximum of 36. Both checked-in q36/g32 v3 fixtures happen to encode 35 unique layer-0 fibers; sampling luck does not lower the fixed verifier requirement.".to_string(),
            "If the unprepared batch exhausts the transaction budget, its reported CU is a cap/failure observation and the prepared savings field is a lower bound, not an exact total delta.".to_string(),
            "The prepared-byte parser is differential-tested against the structured path and explicitly rejects noncanonical C1 and C2 M31 limbs on both host and SBF.".to_string(),
            "The corruption matrix changes canonical C1/C2 field bytes in uploaded accounts and proves both arithmetic implementations and exact leaf hashes consume those bytes.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct CompositionProbeVariant {
    pub name: &'static str,
    pub kernel: &'static str,
    pub parameters: CompositionProbeParameters,
    pub host_qm31_multiplications: u32,
    pub host_qm31_by_cm31_multiplications: u32,
    pub host_additions_or_subtractions: u32,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub matching_rlc_only_cu: Vec<u64>,
    pub matching_rlc_only_cu_mean: f64,
    pub composition_incremental_cu_over_matching_rlc: i64,
    pub rlc_delta_from_frozen_k64_cu: i64,
    pub projected_total_cu: i64,
    pub headroom_vs_1_19m_cu: i64,
    pub meets_10_percent_slack: bool,
}

#[derive(Clone, Copy, Serialize)]
pub struct CompositionProbeParameters {
    pub opened_values: u16,
    pub poseidon_sbox_terms: u16,
    pub poseidon_linear_terms: u16,
    pub logup_degree3_terms: u16,
    pub range_bit_terms: u16,
    pub eq_variables: u8,
}

impl From<aspis_statement::CompositionProbe> for CompositionProbeParameters {
    fn from(value: aspis_statement::CompositionProbe) -> Self {
        Self {
            opened_values: value.opened_values,
            poseidon_sbox_terms: value.poseidon_sbox_terms,
            poseidon_linear_terms: value.poseidon_linear_terms,
            logup_degree3_terms: value.logup_degree3_terms,
            range_bit_terms: value.range_bit_terms,
            eq_variables: value.eq_variables,
        }
    }
}

#[derive(Serialize)]
pub struct CompositionProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub baseline_cu: Vec<u64>,
    pub baseline_cu_mean: f64,
    pub frozen_k64_rlc_only_cu: Vec<u64>,
    pub frozen_k64_rlc_only_cu_mean: f64,
    pub pre_composition_projection_cu: i64,
    pub transaction_target_cu: i64,
    pub ten_percent_slack_maximum_cu: i64,
    pub variants: Vec<CompositionProbeVariant>,
    pub notes: Vec<String>,
}

fn composition_instruction(
    probe: aspis_statement::CompositionProbe,
    optimized: bool,
) -> Result<Instruction> {
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::ConstraintCompositionProbe {
            opened_values: probe.opened_values,
            poseidon_sbox_terms: probe.poseidon_sbox_terms,
            poseidon_linear_terms: probe.poseidon_linear_terms,
            logup_degree3_terms: probe.logup_degree3_terms,
            range_bit_terms: probe.range_bit_terms,
            eq_variables: probe.eq_variables,
            optimized,
        })?,
    })
}

fn simulate_pure_instruction(
    rpc: &Rpc,
    payer: &Keypair,
    instruction: Instruction,
    repetitions: usize,
) -> Result<Vec<u64>> {
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            instruction,
        ],
        Some(&payer.pubkey()),
        &[payer],
        blockhash,
    );
    let mut units = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        let (run_units, error) = rpc.simulate(&transaction)?;
        anyhow::ensure!(
            error.is_none(),
            "composition probe simulation failed: {error:?}"
        );
        units.push(run_units.context("composition probe did not report units")?);
    }
    Ok(units)
}

/// Freehand plus evaluator-confirmed extension-field composition bracket.
pub fn run_stage2_composition_probe() -> Result<CompositionProbeSummary> {
    const REPETITIONS: usize = 5;
    const PRE_COMPOSITION_PROJECTION: i64 = 1_175_086;
    const TARGET: i64 = 1_190_000;
    const TEN_PERCENT_SLACK_MAXIMUM: i64 = 1_071_000;

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let baseline_probe = aspis_statement::CompositionProbe {
        opened_values: 1,
        poseidon_sbox_terms: 0,
        poseidon_linear_terms: 0,
        logup_degree3_terms: 0,
        range_bit_terms: 0,
        eq_variables: 0,
    };
    let baseline_cu = simulate_pure_instruction(
        &rpc,
        &payer,
        composition_instruction(baseline_probe, false)?,
        REPETITIONS,
    )?;
    let baseline_mean = baseline_cu.iter().sum::<u64>() as f64 / baseline_cu.len() as f64;
    let k64_rlc_probe = aspis_statement::CompositionProbe {
        opened_values: 64,
        ..baseline_probe
    };
    let frozen_k64_rlc_only_cu = simulate_pure_instruction(
        &rpc,
        &payer,
        composition_instruction(k64_rlc_probe, false)?,
        REPETITIONS,
    )?;
    let frozen_k64_rlc_mean =
        frozen_k64_rlc_only_cu.iter().sum::<u64>() as f64 / frozen_k64_rlc_only_cu.len() as f64;

    let profiles = [
        (
            "freehand_optimistic",
            aspis_statement::CompositionProbe::OPTIMISTIC,
            false,
        ),
        (
            "evaluator_confirmed_low",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                poseidon_linear_terms: 64,
                logup_degree3_terms: 1,
                range_bit_terms: 64,
                eq_variables: 10,
            },
            false,
        ),
        (
            "evaluator_confirmed_low_optimized",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                poseidon_linear_terms: 64,
                logup_degree3_terms: 1,
                range_bit_terms: 64,
                eq_variables: 10,
            },
            true,
        ),
        (
            "evaluator_low_lookup_range_optimized",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                // Six 10-bit limbs reconstruct the two bounded values.
                poseidon_linear_terms: 70,
                // Wiring LogUp plus a 10-bit fixed-table range LogUp.
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "evaluator_lookup_range_stress_linear128",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                // Stress row: the lookup candidate at the top of the
                // evaluator's per-row linear bracket [64, 128], instead of
                // the 70 terms the shared-output layout assumes.
                poseidon_linear_terms: 128,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r3_lookup_range_optimized",
            aspis_statement::CompositionProbe {
                // 3 Poseidon2 rounds per row: 48 S-box outputs, 48 + 6
                // reconstruction linear terms, 67 opened columns
                // (64 main + multiplicity + two helpers open at the row,
                // matching the r=3 layout candidate's k').
                opened_values: 67,
                poseidon_sbox_terms: 48,
                poseidon_linear_terms: 54,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r3_lookup_range_stress_linear102",
            aspis_statement::CompositionProbe {
                // r=3 bracket top: 3/4 of the r=4 [64,128] bracket plus the
                // six reconstruction terms.
                opened_values: 67,
                poseidon_sbox_terms: 48,
                poseidon_linear_terms: 102,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r2_lookup_range_optimized",
            aspis_statement::CompositionProbe {
                // 2 Poseidon2 rounds per row (the sweep floor: r=1 exceeds
                // the 2^10 row cap): 32 S-box outputs, 32 + 6 linear terms,
                // k' = 51 opened columns.
                opened_values: 51,
                poseidon_sbox_terms: 32,
                poseidon_linear_terms: 38,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r2_lookup_range_stress_linear70",
            aspis_statement::CompositionProbe {
                // r=2 bracket top: 2/4 of the r=4 [64,128] bracket plus the
                // six reconstruction terms.
                opened_values: 51,
                poseidon_sbox_terms: 32,
                poseidon_linear_terms: 70,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "realistic",
            aspis_statement::CompositionProbe::REALISTIC,
            false,
        ),
        (
            "realistic_optimized",
            aspis_statement::CompositionProbe::REALISTIC,
            true,
        ),
        (
            "pessimistic",
            aspis_statement::CompositionProbe::PESSIMISTIC,
            false,
        ),
    ];
    let mut variants = Vec::new();
    for (name, probe, optimized) in profiles {
        let host = if optimized {
            aspis_statement::evaluate_composition_probe_optimized(probe)
        } else {
            aspis_statement::evaluate_composition_probe(probe)
        };
        let simulation_cu = simulate_pure_instruction(
            &rpc,
            &payer,
            composition_instruction(probe, optimized)?,
            REPETITIONS,
        )?;
        let mean = simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        let matching_rlc_probe = aspis_statement::CompositionProbe {
            opened_values: probe.opened_values,
            ..baseline_probe
        };
        let matching_rlc_only_cu = simulate_pure_instruction(
            &rpc,
            &payer,
            composition_instruction(matching_rlc_probe, optimized)?,
            REPETITIONS,
        )?;
        let matching_rlc_mean =
            matching_rlc_only_cu.iter().sum::<u64>() as f64 / matching_rlc_only_cu.len() as f64;
        let composition_incremental = (mean - matching_rlc_mean).round() as i64;
        let rlc_delta = (matching_rlc_mean - frozen_k64_rlc_mean).round() as i64;
        let projected = PRE_COMPOSITION_PROJECTION + rlc_delta + composition_incremental;
        variants.push(CompositionProbeVariant {
            name,
            kernel: if optimized {
                "structured_horner"
            } else {
                "naive"
            },
            parameters: probe.into(),
            host_qm31_multiplications: host.qm31_multiplications,
            host_qm31_by_cm31_multiplications: host.qm31_by_cm31_multiplications,
            host_additions_or_subtractions: host.additions_or_subtractions,
            simulation_cu,
            simulation_cu_mean: mean,
            matching_rlc_only_cu,
            matching_rlc_only_cu_mean: matching_rlc_mean,
            composition_incremental_cu_over_matching_rlc: composition_incremental,
            rlc_delta_from_frozen_k64_cu: rlc_delta,
            projected_total_cu: projected,
            headroom_vs_1_19m_cu: TARGET - projected,
            meets_10_percent_slack: projected <= TEN_PERCENT_SLACK_MAXIMUM,
        });
    }

    Ok(CompositionProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-composition-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        baseline_cu,
        baseline_cu_mean: baseline_mean,
        frozen_k64_rlc_only_cu,
        frozen_k64_rlc_only_cu_mean: frozen_k64_rlc_mean,
        pre_composition_projection_cu: PRE_COMPOSITION_PROJECTION,
        transaction_target_cu: TARGET,
        ten_percent_slack_maximum_cu: TEN_PERCENT_SLACK_MAXIMUM,
        variants,
        notes: vec![
            "Synthetic bracket only: runtime term counts are explicit and must be replaced/confirmed by the evaluator-derived layout.".to_string(),
            "Composition deltas subtract a matching RLC-only run so the gamma RLC already represented in the frozen 201,114-CU layout allowance is not double-counted. Projected totals add the measured k64-to-k' RLC delta and composition-only delta to 1,175,086 CU.".to_string(),
            "Wide-leaf hashing for k'=80 is not updated by this arithmetic-only probe; it is measured separately before a final product decision.".to_string(),
            "The lookup-range candidate replaces 64 Boolean terms with six 10-bit limbs, one additional LogUp relation, and six reconstruction terms. It is an isolated cost candidate, not yet a frozen statement rule.".to_string(),
            "The stress row prices the lookup candidate at linear_terms=128, the top of the evaluator's per-row bracket. If only the 70-term reading fits the slack ceiling, candidate-green is bracket-conditional and the gate note must say so.".to_string(),
            "The 10% slack maximum is 1,071,000 CU. The frozen pre-composition projection already exceeds it by 104,086 CU, so no positive composition result can pass that gate without a named reclaim or rule change.".to_string(),
        ],
    })
}

/// Re-probe the frozen synthetic wide-leaf + gamma-RLC loop at the
/// evaluator's real candidate k'=80, with k64 retained as the exact baseline.
pub fn run_stage2_layout_probe() -> Result<Stage2LayoutSummary> {
    const LOG_ROWS: u8 = 10;
    const QUERY_COUNT: u16 = 36;
    const REPETITIONS: usize = 5;

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 10 * LAMPORTS_PER_SOL)?;
    let probe_account = Keypair::new();
    create_program_account(&rpc, &payer, &probe_account, PROOF_ACCOUNT_HEADER_LEN)?;

    let mut raw = Vec::new();
    // 51/67 = r=2 and r=3 layout candidate widths, 84 = the k' <= 84 pin.
    for columns in [51u16, 64, 67, 80, 82, 84] {
        let leaf_bytes = columns * 4;
        let instruction = AspisInstruction::LayoutProbe {
            log_rows: LOG_ROWS,
            columns,
            query_count: QUERY_COUNT,
            leaf_bytes,
        };
        let ix = proof_instruction(&payer.pubkey(), &probe_account.pubkey(), &instruction)?;
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ix,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let mut units = Vec::with_capacity(REPETITIONS);
        for _ in 0..REPETITIONS {
            let (run_units, error) = rpc.simulate(&transaction)?;
            anyhow::ensure!(error.is_none(), "stage2 layout probe failed: {error:?}");
            units.push(run_units.context("stage2 layout probe did not report units")?);
        }
        let mean = units.iter().sum::<u64>() as f64 / units.len() as f64;
        let diagnostic = rpc.simulate_verbose(&transaction)?;
        anyhow::ensure!(
            diagnostic.err.is_none(),
            "stage2 layout diagnostic failed: {:?}",
            diagnostic.err
        );
        let markers = parse_cu_markers(&diagnostic.logs, "aspis-layout:");
        raw.push((columns, leaf_bytes, units, mean, markers));
    }
    let baseline = raw[0].3;
    let variants = raw
        .into_iter()
        .map(
            |(columns, leaf_bytes, simulation_cu, simulation_cu_mean, diagnostic_markers)| {
                let marker_delta = |label: &str| {
                    diagnostic_markers
                        .iter()
                        .find(|marker| marker.label == label)
                        .and_then(|marker| marker.delta_from_previous)
                };
                Stage2LayoutVariant {
                    columns,
                    leaf_bytes,
                    simulation_cu,
                    simulation_cu_mean,
                    delta_vs_k64_cu: (simulation_cu_mean - baseline).round() as i64,
                    wide_leaf_hash_cu: marker_delta("leaf_hash_done"),
                    synthetic_merkle_cu: marker_delta("merkle_done"),
                    obsolete_same_gamma_rlc_cu: marker_delta("rlc_done"),
                    diagnostic_markers,
                }
            },
        )
        .collect();

    Ok(Stage2LayoutSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-layout-probe".to_string(),
        validator_version: validator_version(),
        log_rows: LOG_ROWS,
        query_count: QUERY_COUNT,
        repetitions: REPETITIONS,
        variants,
        notes: vec![
            "The leaf-hash and synthetic path markers remain useful for k80/q36 geometry. The historical RLC marker is explicitly obsolete because that loop multiplies every column by the same gamma rather than gamma powers.".to_string(),
            "Use results/stage2/wide_rlc_probe.json for the correct q-by-k RLC; lazy_dot4 is the measured winner. Do not quote the old k80-minus-k64 total as an RLC projection.".to_string(),
            "This is still not an integrated wide-row PCS measurement.".to_string(),
        ],
    })
}

/// Measure the pinned software Poseidon2-M31 permutation directly on SBF.
pub fn run_stage2_poseidon2_probe() -> Result<Poseidon2ProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for (implementation, optimized) in [("canonical", false), ("lazy_m31", true)] {
        for permutations in [0u16, 1, 8, 49, 73] {
            let probe = if optimized {
                AspisInstruction::Poseidon2OptimizedProbe { permutations }
            } else {
                AspisInstruction::Poseidon2Probe { permutations }
            };
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&probe)?,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    instruction,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let mut simulation_cu = Vec::new();
            let mut simulation_errors = Vec::new();
            for _ in 0..REPETITIONS {
                let (units, error) = rpc.simulate(&transaction)?;
                simulation_cu.push(units);
                simulation_errors.push(error);
            }
            let accepted_all = simulation_errors.iter().all(Option::is_none);
            let mean = if accepted_all {
                Some(
                    simulation_cu.iter().flatten().sum::<u64>() as f64 / simulation_cu.len() as f64,
                )
            } else {
                None
            };
            variants.push(Poseidon2ProbeVariant {
                implementation,
                permutations,
                simulation_cu,
                simulation_errors,
                accepted_all,
                mean_cu_if_accepted: mean,
                incremental_cu_over_zero_if_accepted: None,
            });
        }
    }
    for implementation in ["canonical", "lazy_m31"] {
        let zero = variants
            .iter()
            .find(|variant| variant.implementation == implementation && variant.permutations == 0)
            .and_then(|variant| variant.mean_cu_if_accepted);
        for variant in variants
            .iter_mut()
            .filter(|variant| variant.implementation == implementation)
        {
            variant.incremental_cu_over_zero_if_accepted = match (variant.mean_cu_if_accepted, zero)
            {
                (Some(mean), Some(zero)) => Some((mean - zero).round() as i64),
                _ => None,
            };
        }
    }
    let per_permutation = variants
        .iter()
        .find(|variant| variant.implementation == "lazy_m31" && variant.permutations == 8)
        .and_then(|variant| variant.incremental_cu_over_zero_if_accepted)
        .map(|delta| delta as f64 / 8.0);

    Ok(Poseidon2ProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-poseidon2-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        variants,
        measured_incremental_cu_per_permutation_from_8: per_permutation,
        notes: vec![
            "Canonical and lazy-M31 software Poseidon2 width-16 permutations use the exact p3-mersenne-31 0.6.1 constants; differential tests require identical outputs.".to_string(),
            "The lazy-M31 candidate reduces each linear-layer output once and replaces partial-round power-of-two multiplications with shifts. It is the first measured solmath-zk kernel candidate.".to_string(),
            "49 permutations is the depth-20 SpendV0 evaluator schedule; 73 is the depth-32 sensitivity. A capped run is recorded as a failure, not extrapolated into an accepted measurement.".to_string(),
            "This is deposit/direct-evaluator cost evidence, not proof-verifier constraint-composition cost.".to_string(),
        ],
    })
}

/// Measure small reusable field kernels before they become a standalone
/// `solmath-zk` API. Every point subtracts a zero-iteration instruction with
/// the same enum variant and dispatch path.
pub fn run_stage2_zk_kernel_probe() -> Result<ZkKernelProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let kernels = [
        ("m31_inverse_software", ZkKernelKind::M31InverseSoftware, 32),
        ("m31_inverse_syscall", ZkKernelKind::M31InverseSyscall, 32),
        ("qm31_square_generic", ZkKernelKind::Qm31SquareGeneric, 512),
        (
            "qm31_square_specialized",
            ZkKernelKind::Qm31SquareSpecialized,
            512,
        ),
        ("m31_pow2_generic", ZkKernelKind::M31Pow2Generic, 4_096),
        ("m31_pow2_shift", ZkKernelKind::M31Pow2Shift, 4_096),
    ];
    let mut variants = Vec::new();
    for (kernel, kind, iterations) in kernels {
        let mut means = Vec::new();
        let mut samples_by_count = Vec::new();
        for count in [0, iterations] {
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&AspisInstruction::ZkKernelProbe {
                    kind,
                    iterations: count,
                })?,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    instruction,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let mut samples = Vec::new();
            for _ in 0..REPETITIONS {
                let (units, error) = rpc.simulate(&transaction)?;
                anyhow::ensure!(error.is_none(), "{kernel} probe failed: {error:?}");
                samples.push(units.ok_or_else(|| anyhow!("no unitsConsumed for {kernel}"))?);
            }
            means.push(samples.iter().sum::<u64>() as f64 / samples.len() as f64);
            samples_by_count.push(samples);
        }
        let delta = (means[1] - means[0]).round() as i64;
        variants.push(ZkKernelProbeVariant {
            kernel,
            iterations,
            simulation_cu: samples_by_count.pop().unwrap(),
            simulation_cu_mean: means[1],
            incremental_cu_over_zero: delta,
            incremental_cu_per_iteration: delta as f64 / iterations as f64,
        });
    }

    let profile = &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32;
    let digest = crate::host_statement_digest(0);
    let proof_path = root.join("results/stage1/proofs/capacity_lr10_q36_g32_v3_c2.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read frozen proof {}", proof_path.display()))?;
    anyhow::ensure!(
        aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
        "frozen Stage 1 proof no longer verifies on host"
    );
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let measure_verifier = |mode: u8| -> Result<Vec<u64>> {
        let instruction = if mode == 2 {
            AspisInstruction::VerifySyscallInverse {
                statement_digest: digest,
            }
        } else if mode == 1 {
            AspisInstruction::VerifyFast {
                statement_digest: digest,
            }
        } else {
            AspisInstruction::VerifyLegacySoftware {
                statement_digest: digest,
            }
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let mut samples = Vec::new();
        for _ in 0..REPETITIONS {
            let (units, error) = rpc.simulate(&transaction)?;
            anyhow::ensure!(error.is_none(), "full verifier probe failed: {error:?}");
            samples.push(units.context("full verifier probe did not report units")?);
        }
        Ok(samples)
    };
    let software_inverse_cu = measure_verifier(0)?;
    let syscall_inverse_cu = measure_verifier(2)?;
    let circle_conjugate_cu = measure_verifier(1)?;
    let software_inverse_cu_mean =
        software_inverse_cu.iter().sum::<u64>() as f64 / software_inverse_cu.len() as f64;
    let syscall_inverse_cu_mean =
        syscall_inverse_cu.iter().sum::<u64>() as f64 / syscall_inverse_cu.len() as f64;
    let circle_conjugate_cu_mean =
        circle_conjugate_cu.iter().sum::<u64>() as f64 / circle_conjugate_cu.len() as f64;

    let profile_instruction = AspisInstruction::VerifyProfile {
        statement_digest: digest,
    };
    let blockhash = rpc.latest_blockhash()?;
    let profile_transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            proof_instruction(
                &payer.pubkey(),
                &proof_account.pubkey(),
                &profile_instruction,
            )?,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let diagnostic_profile = rpc.simulate_verbose(&profile_transaction)?;
    anyhow::ensure!(
        diagnostic_profile.err.is_none(),
        "diagnostic full verifier probe failed: {:?}",
        diagnostic_profile.err
    );
    let full_pcs_verifier = FullPcsVerifierComparison {
        profile: profile.name,
        proof_bytes: proof.len(),
        software_inverse_cu,
        software_inverse_cu_mean,
        syscall_inverse_cu,
        syscall_inverse_cu_mean,
        syscall_savings_cu: (software_inverse_cu_mean - syscall_inverse_cu_mean).round() as i64,
        circle_conjugate_cu,
        circle_conjugate_cu_mean,
        circle_conjugate_savings_vs_software_cu: (software_inverse_cu_mean
            - circle_conjugate_cu_mean)
            .round() as i64,
        diagnostic_profile_cu: diagnostic_profile.units,
        diagnostic_profile_markers: parse_cu_markers(&diagnostic_profile.logs, "aspis-cu:"),
    };

    Ok(ZkKernelProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-zk-kernel-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        variants,
        full_pcs_verifier,
        notes: vec![
            "Candidate reusable solmath-zk kernels measured on Agave SBF; these are instruction-level deltas, not host timings.".to_string(),
            "The M31 syscall inversion uses sol_big_mod_exp with stack-backed four-byte base/exponent/modulus/output and no Vec allocation on SBF.".to_string(),
            "Specialized QM31 squaring uses seven M31 products versus nine for generic multiplication; power-of-two multiplication uses a shift plus Mersenne reduction.".to_string(),
        ],
    })
}

/// Measure the actual q-by-k gamma RLC shape for wide base-field columns.
pub fn run_stage2_wide_rlc_probe() -> Result<WideRlcProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let kernels = [
        ("precomputed_powers", 0u8),
        ("lazy_dot4", 1u8),
        ("per_query_horner", 2u8),
        ("packed4_lazy_dot", 3u8),
        ("packed4_naive", 4u8),
        ("packed2_lazy_dot", 5u8),
        ("raw_u128_dot", 6u8),
        ("lazy_dot4_outer_lazy", 7u8),
        ("fixed80_outer_lazy", 8u8),
        ("fixed84_outer_lazy", 9u8),
        ("fixed67_outer_lazy", 10u8),
        ("fixed65_outer_lazy", 11u8),
        ("fixed51_outer_lazy", 12u8),
        ("fixed49_outer_lazy", 13u8),
    ];
    // Fixed-width kernels run only at their own width; k84 is the k' <= 84
    // pin, k67/k51 the r=3 and r=2 layout candidates, k65/k49 those layouts
    // under LogUp-GKR (helper-free).
    let shapes = [(64u16, 32u16), (80u16, 36u16)];
    let fixed_width: [(u8, u16); 6] = [(8, 80), (9, 84), (10, 67), (11, 65), (12, 51), (13, 49)];
    let mut variants = Vec::new();
    for (kernel, kernel_id) in kernels {
        for (columns, query_count) in shapes {
            if let Some(&(_, width)) = fixed_width.iter().find(|(id, _)| *id == kernel_id) {
                if query_count != 36 {
                    continue;
                }
                let columns = width;
                let mut means = Vec::new();
                let mut full_samples = Vec::new();
                for measured_queries in [0, query_count] {
                    let instruction = Instruction {
                        program_id: aspis_verifier::id(),
                        accounts: vec![],
                        data: to_vec(&AspisInstruction::WideRlcProbe {
                            columns,
                            query_count: measured_queries,
                            kernel: kernel_id,
                        })?,
                    };
                    let samples =
                        simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
                    means.push(samples.iter().sum::<u64>() as f64 / samples.len() as f64);
                    full_samples = samples;
                }
                variants.push(WideRlcProbeVariant {
                    kernel,
                    columns,
                    query_count,
                    simulation_cu: full_samples,
                    simulation_cu_mean: means[1],
                    baseline_cu_mean: means[0],
                    incremental_cu: (means[1] - means[0]).round() as i64,
                });
                continue;
            }
            let mut means = Vec::new();
            let mut full_samples = Vec::new();
            for measured_queries in [0, query_count] {
                let instruction = Instruction {
                    program_id: aspis_verifier::id(),
                    accounts: vec![],
                    data: to_vec(&AspisInstruction::WideRlcProbe {
                        columns,
                        query_count: measured_queries,
                        kernel: kernel_id,
                    })?,
                };
                let samples = simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
                means.push(samples.iter().sum::<u64>() as f64 / samples.len() as f64);
                full_samples = samples;
            }
            variants.push(WideRlcProbeVariant {
                kernel,
                columns,
                query_count,
                simulation_cu: full_samples,
                simulation_cu_mean: means[1],
                baseline_cu_mean: means[0],
                incremental_cu: (means[1] - means[0]).round() as i64,
            });
        }
    }
    Ok(WideRlcProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-wide-rlc-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        variants,
        notes: vec![
            "Unlike the historical layout loop, this probe uses gamma powers and measures all q*k base-column contributions required at the wide PCS seam.".to_string(),
            "lazy_dot4 fuses four raw-M31 scalar products per reduction. lazy_dot4_outer_lazy then accumulates those canonical block results in u64 and performs one final reduction per QM31 limb; both are differential-tested against the eager reference.".to_string(),
            "fixed80_outer_lazy uses qm31_power_table::<80> and stack-backed fixed arrays for the ruled k=80 shape; it is the selected 201,990-CU kernel. The generic outer-lazy slice API remains available for other widths.".to_string(),
            "packed4_lazy_dot injectively maps four raw M31 columns into one QM31 coefficient before batching; the k=80 shape therefore has degree 19 in gamma rather than 79 and no column information is discarded.".to_string(),
            "This still excludes wide-leaf hashing and must be integrated with real proof parsing before a gate closes.".to_string(),
        ],
    })
}

pub fn run_stage2_merkle_arity_probe() -> Result<MerkleArityProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let shapes = [
        ("c1_layer_0", 10u8, 36u16),
        ("c2_layer_0", 10, 36),
        ("c1_layer_1", 8, 36),
        ("c1_layer_2", 6, 36),
        ("c1_layer_3", 4, 36),
    ];
    let mut points = Vec::new();
    for (tree, depth, query_count) in shapes {
        let mut runs = Vec::new();
        for arity in [2u8, 4u8] {
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&AspisInstruction::MerkleArityProbe {
                    depth,
                    query_count,
                    arity,
                })?,
            };
            runs.push(simulate_pure_instruction(
                &rpc,
                &payer,
                instruction,
                REPETITIONS,
            )?);
        }
        let binary_mean = runs[0].iter().sum::<u64>() as f64 / runs[0].len() as f64;
        let radix4_mean = runs[1].iter().sum::<u64>() as f64 / runs[1].len() as f64;
        points.push(MerkleArityProbePoint {
            tree,
            depth,
            query_count,
            binary_cu: runs.remove(0),
            binary_cu_mean: binary_mean,
            radix4_cu: runs.remove(0),
            radix4_cu_mean: radix4_mean,
            radix4_savings_cu: (binary_mean - radix4_mean).round() as i64,
        });
    }
    let binary_total = points
        .iter()
        .map(|point| point.binary_cu_mean.round() as i64)
        .sum();
    let radix4_total = points
        .iter()
        .map(|point| point.radix4_cu_mean.round() as i64)
        .sum();
    Ok(MerkleArityProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-merkle-arity-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        points,
        modeled_binary_total_cu: binary_total,
        modeled_radix4_total_cu: radix4_total,
        modeled_radix4_savings_cu: binary_total - radix4_total,
        notes: vec![
            "Pure minimal-subtree traversal/hash model over deterministic query indices; leaf hashing and proof-byte parsing are excluded equally.".to_string(),
            "Radix-4 is tailored to the arity-4 fold: all frozen depths are even, and one 129-byte SHA call replaces up to three 65-byte binary-node calls.".to_string(),
            "A positive model is not authorization to re-pin roots or the transcript; a real g16 proof comparison must precede any g32 fixture change.".to_string(),
        ],
    })
}

/// Real two-phase proof comparison at g16. The transcript header and every
/// Merkle root are genuinely changed for the radix-4 variant; this is the
/// teeth-first checkpoint before regenerating the expensive frozen g32 KAT.
pub fn run_stage2_radix4_g16() -> Result<Radix4G16Summary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let digest = crate::host_statement_digest(0);
    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let mut variants = Vec::new();
    let mut radix4_proof = None;

    for mode in [MerkleMode::MinimalSubtree, MerkleMode::Radix4MinimalSubtree] {
        let proof = prove_with_synthetic_second_phase(
            profile,
            &coeffs,
            &digest,
            &ProveOptions {
                fold_payload: FoldPayload::RawFibers,
                merkle_mode: mode,
            },
            HOST_HASH,
        );
        ensure!(
            aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
            "generated {mode:?} proof failed host verification"
        );
        let corruption = crate::host::corruption_suite(profile, &proof, &digest);
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, &proof, true)?;

        let mut samples = Vec::new();
        for _ in 0..REPETITIONS {
            let instruction = AspisInstruction::Verify {
                statement_digest: digest,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let (units, error) = rpc.simulate(&transaction)?;
            ensure!(
                error.is_none(),
                "{mode:?} production Verify failed: {error:?}"
            );
            samples.push(units.context("production Verify did not report units")?);
        }
        let mean = samples.iter().sum::<u64>() as f64 / samples.len() as f64;
        let proof_hash = HOST_HASH(&[&proof]);
        let proof_sha256 = proof_hash
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        variants.push(Radix4ProofVariant {
            merkle_mode: match mode {
                MerkleMode::MinimalSubtree => "binary_minimal_subtree",
                MerkleMode::Radix4MinimalSubtree => "radix4_minimal_subtree",
                MerkleMode::SinglePaths => unreachable!(),
            },
            proof_bytes: proof.len(),
            proof_sha256,
            verify_cu: samples,
            verify_cu_mean: mean,
            host_corruption_cases: corruption.len(),
            host_corruption_all_rejected: corruption.iter().all(|case| case.rejected),
        });
        if mode == MerkleMode::Radix4MinimalSubtree {
            radix4_proof = Some(proof);
        }
    }

    let mut corrupted = radix4_proof.context("radix-4 proof missing")?;
    let header = aspis_core::proof::Header::parse(&corrupted).context("radix-4 header")?;
    let body_offset = aspis_core::proof::HEADER_LEN
        + aspis_core::proof::transcript_records_len(profile.num_rounds() as usize, header.flags)
        + profile.final_poly_len() as usize * 16
        + 8;
    let unique_count =
        u16::from_le_bytes(corrupted[body_offset..body_offset + 2].try_into().unwrap()) as usize;
    let main_node_count_offset = body_offset + 2 + unique_count * (32 + 64);
    let node_count = u32::from_le_bytes(
        corrupted[main_node_count_offset..main_node_count_offset + 4]
            .try_into()
            .unwrap(),
    );
    ensure!(
        node_count > 0,
        "radix-4 layer-0 frontier unexpectedly empty"
    );
    corrupted[main_node_count_offset + 4] ^= 1;
    let host_corruption = matches!(
        aspis_core::verify(&corrupted, &digest, HOST_HASH),
        Err(aspis_core::VerifyError::MerkleMismatch { layer: 0 })
    );

    let corrupted_account = Keypair::new();
    upload_proof(&rpc, &payer, &corrupted_account, &corrupted, true)?;
    let instruction = AspisInstruction::Verify {
        statement_digest: digest,
    };
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            proof_instruction(&payer.pubkey(), &corrupted_account.pubkey(), &instruction)?,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (_, sbf_corruption_error) = rpc.simulate(&transaction)?;

    let binary_mean = variants[0].verify_cu_mean;
    let radix4_mean = variants[1].verify_cu_mean;
    let savings = (binary_mean - radix4_mean).round() as i64;
    let proof_bytes_delta = variants[1].proof_bytes as i64 - variants[0].proof_bytes as i64;
    Ok(Radix4G16Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-radix4-g16".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        repetitions: REPETITIONS,
        second_phase_enabled: true,
        variants,
        radix4_savings_cu: savings,
        radix4_savings_percent: savings as f64 / binary_mean * 100.0,
        radix4_proof_bytes_delta: proof_bytes_delta,
        radix4_frontier_corruption_rejected_host: host_corruption,
        radix4_frontier_corruption_rejected_sbf: sbf_corruption_error.is_some(),
        notes: vec![
            "Both rows are real claim-free Stage-1 synthetic-C2 proofs over identical coefficients and statement bytes; only the transcript-bound Merkle mode differs.".to_string(),
            "Production Verify uses the cached-domain and unit-circle-conjugate verifier kernels selected by the Stage-2 kernel probe; VerifyFast remains a wire-compatible alias of the same path.".to_string(),
            "The radix-4 root uses domain byte 0x12 and one SHA-256 input containing four ordered child hashes. It is not a reinterpretation of a binary root.".to_string(),
            "A layer-0 radix-4 frontier hash is deliberately corrupted after proof construction and must reject both on host and SBF.".to_string(),
            "This g16 checkpoint does not re-pin the frozen g32 proof or transcript KAT; that happens only after this comparison is accepted.".to_string(),
        ],
    })
}

pub fn run_stage2_radix4_g32() -> Result<Radix4G32Summary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let profile = &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32;
    let digest = crate::host_statement_digest(0);
    let coeffs = seeded_coeffs(profile.log_rows, 1);

    let binary_path = root.join("results/stage1/proofs/capacity_lr10_q36_g32_v3_c2.bin");
    let binary_proof = fs::read(&binary_path)
        .with_context(|| format!("read frozen binary proof {}", binary_path.display()))?;
    ensure!(
        aspis_core::verify(&binary_proof, &digest, HOST_HASH).is_ok(),
        "frozen binary g32 proof failed current host verification"
    );

    let proof_dir = root.join("results/stage2/proofs");
    fs::create_dir_all(&proof_dir)?;
    let radix4_path = proof_dir.join("capacity_lr10_q36_g32_v3_c2_radix4.bin");
    let cached_radix4 = fs::read(&radix4_path).ok().filter(|proof| {
        let correct_mode = aspis_core::proof::Header::parse(proof)
            .map(|header| header.merkle_mode == MerkleMode::Radix4MinimalSubtree as u8)
            .unwrap_or(false);
        correct_mode && aspis_core::verify(proof, &digest, HOST_HASH).is_ok()
    });
    let (radix4_proof, radix4_source, generation_seconds) = if let Some(proof) = cached_radix4 {
        (
            proof,
            format!("reused host-verified cache {}", radix4_path.display()),
            None,
        )
    } else {
        eprintln!("stage2-radix4-g32: searching a fresh 32-bit grinding nonce");
        let started = Instant::now();
        let proof = prove_with_synthetic_second_phase(
            profile,
            &coeffs,
            &digest,
            &ProveOptions {
                fold_payload: FoldPayload::RawFibers,
                merkle_mode: MerkleMode::Radix4MinimalSubtree,
            },
            HOST_HASH,
        );
        let elapsed = started.elapsed().as_secs_f64();
        ensure!(
            aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
            "fresh radix-4 g32 proof failed host verification"
        );
        fs::write(&radix4_path, &proof)?;
        (
            proof,
            format!("generated and cached {}", radix4_path.display()),
            Some(elapsed),
        )
    };

    let hex = |bytes: &[u8]| {
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };
    let root_start = aspis_core::proof::HEADER_LEN;
    let binary_first_root = hex(&binary_proof[root_start..root_start + 32]);
    let radix4_first_root = hex(&radix4_proof[root_start..root_start + 32]);
    ensure!(
        binary_first_root != radix4_first_root,
        "radix-4 and binary C1 roots unexpectedly match"
    );
    let transcript_kat_unchanged = aspis_core::transcript::transcript_kat(HOST_HASH)
        == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED;
    ensure!(
        transcript_kat_unchanged,
        "schedule-level transcript KAT drifted"
    );

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 3 * LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for (mode_name, proof) in [
        ("binary_minimal_subtree", &binary_proof),
        ("radix4_minimal_subtree", &radix4_proof),
    ] {
        let corruption = crate::host::corruption_suite(profile, proof, &digest);
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, proof, true)?;
        let mut samples = Vec::new();
        for _ in 0..REPETITIONS {
            let instruction = AspisInstruction::Verify {
                statement_digest: digest,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let (units, error) = rpc.simulate(&transaction)?;
            ensure!(
                error.is_none(),
                "{mode_name} production Verify failed: {error:?}"
            );
            samples.push(units.context("production Verify did not report units")?);
        }
        let proof_hash = HOST_HASH(&[proof]);
        variants.push(Radix4ProofVariant {
            merkle_mode: mode_name,
            proof_bytes: proof.len(),
            proof_sha256: hex(&proof_hash),
            verify_cu_mean: samples.iter().sum::<u64>() as f64 / samples.len() as f64,
            verify_cu: samples,
            host_corruption_cases: corruption.len(),
            host_corruption_all_rejected: corruption.iter().all(|case| case.rejected),
        });
    }

    let mut corrupted = radix4_proof.clone();
    let header = aspis_core::proof::Header::parse(&corrupted).context("radix-4 header")?;
    let body_offset = aspis_core::proof::HEADER_LEN
        + aspis_core::proof::transcript_records_len(profile.num_rounds() as usize, header.flags)
        + profile.final_poly_len() as usize * 16
        + 8;
    let unique_count =
        u16::from_le_bytes(corrupted[body_offset..body_offset + 2].try_into().unwrap()) as usize;
    let main_node_count_offset = body_offset + 2 + unique_count * (32 + 64);
    let node_count = u32::from_le_bytes(
        corrupted[main_node_count_offset..main_node_count_offset + 4]
            .try_into()
            .unwrap(),
    );
    ensure!(node_count > 0, "radix-4 g32 frontier unexpectedly empty");
    corrupted[main_node_count_offset + 4] ^= 1;
    let host_corruption = matches!(
        aspis_core::verify(&corrupted, &digest, HOST_HASH),
        Err(aspis_core::VerifyError::MerkleMismatch { layer: 0 })
    );
    let corrupted_account = Keypair::new();
    upload_proof(&rpc, &payer, &corrupted_account, &corrupted, true)?;
    let instruction = AspisInstruction::Verify {
        statement_digest: digest,
    };
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            proof_instruction(&payer.pubkey(), &corrupted_account.pubkey(), &instruction)?,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (_, sbf_corruption_error) = rpc.simulate(&transaction)?;

    let binary_mean = variants[0].verify_cu_mean;
    let radix4_mean = variants[1].verify_cu_mean;
    let savings = (binary_mean - radix4_mean).round() as i64;
    let proof_bytes_delta = variants[1].proof_bytes as i64 - variants[0].proof_bytes as i64;
    Ok(Radix4G32Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-radix4-g32".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        repetitions: REPETITIONS,
        binary_proof_source: binary_path.display().to_string(),
        radix4_proof_source: radix4_source,
        radix4_generation_seconds: generation_seconds,
        binary_first_root,
        radix4_first_root,
        root_changed: true,
        transcript_kat_unchanged,
        variants,
        radix4_savings_cu: savings,
        radix4_savings_percent: savings as f64 / binary_mean * 100.0,
        radix4_proof_bytes_delta: proof_bytes_delta,
        radix4_frontier_corruption_rejected_host: host_corruption,
        radix4_frontier_corruption_rejected_sbf: sbf_corruption_error.is_some(),
        notes: vec![
            "Both proofs use the literal q36/g32 profile, synthetic C2, identical coefficients, and identical statement bytes. Production Verify selects the optimized denominator/domain path.".to_string(),
            "The Merkle-mode header byte is transcript-absorbed, so roots, challenges, grinding nonce, query positions, proof digest, and proof bytes are all freshly generated for radix-4.".to_string(),
            "TRANSCRIPT_KAT_EXPECTED intentionally does not move: radix-4 changes a transcript input, not the schedule or sampler that the standalone KAT pins.".to_string(),
            "A real radix-4 layer-0 frontier node is corrupted and must reject on both host and SBF.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct SumcheckProbeVariant {
    pub name: &'static str,
    pub rounds: u8,
    pub coefficients: u8,
    pub claims: u8,
    pub selector_terms: u16,
    pub selector_exceptions: u8,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub incremental_cu_over_baseline: i64,
}

#[derive(Serialize)]
pub struct SumcheckProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub baseline_cu_mean: f64,
    pub synthetic_allowance_cu: i64,
    pub variants: Vec<SumcheckProbeVariant>,
    pub central_replaces_allowance_cu: i64,
    pub allowance_error_cu: i64,
    pub notes: Vec<String>,
}

/// Measure the fused statement-sumcheck verifier work that the synthetic
/// 30,000-CU allowance stands in for. Risk retirement: every registered
/// gate statistic silently assumes the allowance.
pub fn run_stage2_sumcheck_probe() -> Result<SumcheckProbeSummary> {
    const REPETITIONS: usize = 5;
    const ALLOWANCE: i64 = 30_000;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let probe_instruction = |rounds: u8,
                             coefficients: u8,
                             claims: u8,
                             selector_terms: u16,
                             selector_exceptions: u8|
     -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StatementSumcheckProbe {
                rounds,
                coefficients,
                claims,
                selector_terms,
                selector_exceptions,
            })?,
        })
    };

    let baseline =
        simulate_pure_instruction(&rpc, &payer, probe_instruction(0, 1, 0, 0, 0)?, REPETITIONS)?;
    let baseline_mean = baseline.iter().sum::<u64>() as f64 / baseline.len() as f64;

    // (rounds, coefficients, claims, selector_terms, selector_exceptions):
    // optimistic assumes degree-6 messages and lean selectors; central is
    // the nu=10 / degree-7 / three-claim / b=4-5 block-periodic reading;
    // pessimistic is the T3 nu<=14 budget with heavier selectors.
    let shapes: [(&'static str, u8, u8, u8, u16, u8); 3] = [
        ("optimistic", 10, 7, 3, 16, 3),
        ("central", 10, 8, 3, 24, 5),
        ("pessimistic", 14, 8, 4, 48, 8),
    ];
    let mut variants = Vec::new();
    for (name, rounds, coefficients, claims, selector_terms, selector_exceptions) in shapes {
        let samples = simulate_pure_instruction(
            &rpc,
            &payer,
            probe_instruction(
                rounds,
                coefficients,
                claims,
                selector_terms,
                selector_exceptions,
            )?,
            REPETITIONS,
        )?;
        let mean = samples.iter().sum::<u64>() as f64 / samples.len() as f64;
        variants.push(SumcheckProbeVariant {
            name,
            rounds,
            coefficients,
            claims,
            selector_terms,
            selector_exceptions,
            simulation_cu: samples,
            simulation_cu_mean: mean,
            incremental_cu_over_baseline: (mean - baseline_mean).round() as i64,
        });
    }
    let central = variants[1].incremental_cu_over_baseline;
    Ok(SumcheckProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-sumcheck-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        baseline_cu_mean: baseline_mean,
        synthetic_allowance_cu: ALLOWANCE,
        variants,
        central_replaces_allowance_cu: central,
        allowance_error_cu: central - ALLOWANCE,
        notes: vec![
            "Prices mu-batched zero claims, transcript-absorbed round messages with boundary checks and Horner terminal evaluation, and block-periodic selector evaluation with enumerated exception rows.".to_string(),
            "eq(r,z) and the composition C(v_1..v_k) are deliberately excluded: the constraint-composition probe already prices them; adding them here would double-count the seam.".to_string(),
            "The central incremental value REPLACES the synthetic 30,000-CU statement-sumcheck allowance in every projection from this artifact onward.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct QueryTradeProfileStats {
    pub profile: &'static str,
    pub query_count: u16,
    pub per_seed_cu: Vec<u64>,
    pub mean_cu: f64,
    pub min_cu: u64,
    pub max_cu: u64,
    pub range_cu: u64,
}

#[derive(Serialize)]
pub struct QueryTradeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub seeds: u64,
    pub repetitions_per_seed: usize,
    pub profiles: Vec<QueryTradeProfileStats>,
    pub q36_to_q34_mean_saving_cu: f64,
    pub q36_to_q32_mean_saving_cu: f64,
    pub marginal_cu_per_query_q36_q32: f64,
    pub notes: Vec<String>,
}

/// Multi-seed q36/q34/q32 comparison at fixed g16 shape for the
/// query/grinding trade (production pairings q34/g36, q32/g40 hold
/// 2q + g = 104). Per the pre-registered evidence standard, generation-
/// changing candidates are evaluated on >= 8-seed means.
pub fn run_stage2_query_trade_g16() -> Result<QueryTradeSummary> {
    const REPETITIONS: usize = 5;
    const SEEDS: u64 = 8;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 40 * LAMPORTS_PER_SOL)?;

    let profiles = [
        &PROFILE_CAPACITY_LR10_Q36_G16,
        &aspis_core::params::PROFILE_CAPACITY_LR10_Q34_G16,
        &aspis_core::params::PROFILE_CAPACITY_LR10_Q32_G16,
    ];
    let mut stats = Vec::new();
    for profile in profiles {
        let mut per_seed = Vec::new();
        for seed in 1..=SEEDS {
            let digest = crate::host_statement_digest(seed);
            let coeffs = seeded_coeffs(profile.log_rows, seed);
            let proof = prove_with_synthetic_second_phase(
                profile,
                &coeffs,
                &digest,
                &ProveOptions {
                    fold_payload: FoldPayload::RawFibers,
                    merkle_mode: MerkleMode::Radix4MinimalSubtree,
                },
                HOST_HASH,
            );
            ensure!(
                aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
                "{} seed {seed} proof failed host verification",
                profile.name
            );
            let proof_account = Keypair::new();
            upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
            let mut reps = Vec::new();
            for _ in 0..REPETITIONS {
                let instruction = AspisInstruction::Verify {
                    statement_digest: digest,
                };
                let blockhash = rpc.latest_blockhash()?;
                let transaction = Transaction::new_signed_with_payer(
                    &[
                        ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                        proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                    ],
                    Some(&payer.pubkey()),
                    &[&payer],
                    blockhash,
                );
                let (units, error) = rpc.simulate(&transaction)?;
                ensure!(
                    error.is_none(),
                    "{} seed {seed} production Verify failed: {error:?}",
                    profile.name
                );
                reps.push(units.context("production Verify did not report units")?);
            }
            ensure!(
                reps.windows(2).all(|pair| pair[0] == pair[1]),
                "{} seed {seed} simulation was not deterministic: {reps:?}",
                profile.name
            );
            per_seed.push(reps[0]);
            eprintln!(
                "stage2-query-trade-g16: {} seed {seed}/{SEEDS} {}",
                profile.name, reps[0]
            );
        }
        let mean = per_seed.iter().sum::<u64>() as f64 / per_seed.len() as f64;
        let min = *per_seed.iter().min().expect("nonempty");
        let max = *per_seed.iter().max().expect("nonempty");
        stats.push(QueryTradeProfileStats {
            profile: profile.name,
            query_count: profile.query_count,
            per_seed_cu: per_seed,
            mean_cu: mean,
            min_cu: min,
            max_cu: max,
            range_cu: max - min,
        });
    }
    let q36_q34 = stats[0].mean_cu - stats[1].mean_cu;
    let q36_q32 = stats[0].mean_cu - stats[2].mean_cu;
    Ok(QueryTradeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-query-trade-g16".to_string(),
        validator_version: validator_version(),
        seeds: SEEDS,
        repetitions_per_seed: REPETITIONS,
        profiles: stats,
        q36_to_q34_mean_saving_cu: q36_q34,
        q36_to_q32_mean_saving_cu: q36_q32,
        marginal_cu_per_query_q36_q32: q36_q32 / 4.0,
        notes: vec![
            "Radix-4 synthetic-C2 g16 proofs, production Verify, 8 fresh draws per query count; means are the comparison statistic per the pre-registered evidence standard.".to_string(),
            "This measures the PCS-side query scaling only. The q-linear statement terms (wide RLC and leaf, ~ (k' RLC + leaf)/36 per query) add to the projected saving arithmetically and are called out in the hunt ledger.".to_string(),
            "Production pairings hold 2q + g = 104: q34/g36 and q32/g40. Each traded query improves the proven Johnson floor by ~1.07 bits net (0.93 proven query-bits out, 2 proven ROM work-bits in).".to_string(),
        ],
    })
}

/// Multi-seed transcript-draw variance study at fixed g16 shape.
///
/// This is the pre-registered decider for whether the strict candidate's
/// 29,056-CU single-draw headroom survives draw-to-draw spread. The
/// criterion string is committed before any multi-seed data exists; the
/// runner only evaluates it.
pub fn run_stage2_variance_g16() -> Result<VarianceG16Summary> {
    const REPETITIONS: usize = 5;
    const SEEDS: u64 = 16;
    const STRICT_CANDIDATE_PROJECTION: i64 = 1_041_944;
    const TEN_PERCENT_SLACK_MAXIMUM: i64 = 1_071_000;
    const CRITERION: &str = "Pre-registered before any multi-seed run: let R = max - min of \
        production Verify CU for the radix-4 minimal-subtree variant over 16 fresh transcript \
        draws (seed s in 1..=16; statement digest seed s, coefficient seed s) at fixed shape \
        capacity_lr10_q36_g16 with RawFibers and synthetic C2. The strict candidate stays green \
        only if 1,041,944 + R <= 1,071,000. Rationale: the single measured g32 radix-4 draw \
        (678,407 CU) may sit anywhere in its own draw distribution, including at its minimum, \
        so the full observed fixed-shape range bounds a worst-case redraw under the stated \
        g16-to-g32 spread-transfer assumption (the query-index and frontier-collision mechanism \
        is identical; grinding bits enter only as a header byte and a threshold). mean+2*sigma \
        and the binary-mode spread are reported as secondary diagnostics and are not binding. \
        On failure, projection_status downgrades to variance_conditional before any \
        integration nonce is ground.";

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 40 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let mut samples = Vec::new();
    let mut binary_cu = Vec::new();
    let mut radix4_cu = Vec::new();
    for seed in 1..=SEEDS {
        let digest = crate::host_statement_digest(seed);
        let coeffs = seeded_coeffs(profile.log_rows, seed);
        let mut per_mode = Vec::new();
        for mode in [MerkleMode::MinimalSubtree, MerkleMode::Radix4MinimalSubtree] {
            let proof = prove_with_synthetic_second_phase(
                profile,
                &coeffs,
                &digest,
                &ProveOptions {
                    fold_payload: FoldPayload::RawFibers,
                    merkle_mode: mode,
                },
                HOST_HASH,
            );
            ensure!(
                aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
                "seed {seed} {mode:?} proof failed host verification"
            );
            let proof_account = Keypair::new();
            upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
            let mut reps = Vec::new();
            for _ in 0..REPETITIONS {
                let instruction = AspisInstruction::Verify {
                    statement_digest: digest,
                };
                let blockhash = rpc.latest_blockhash()?;
                let transaction = Transaction::new_signed_with_payer(
                    &[
                        ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                        proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                    ],
                    Some(&payer.pubkey()),
                    &[&payer],
                    blockhash,
                );
                let (units, error) = rpc.simulate(&transaction)?;
                ensure!(
                    error.is_none(),
                    "seed {seed} {mode:?} production Verify failed: {error:?}"
                );
                reps.push(units.context("production Verify did not report units")?);
            }
            ensure!(
                reps.windows(2).all(|pair| pair[0] == pair[1]),
                "seed {seed} {mode:?} simulation was not deterministic: {reps:?}"
            );
            per_mode.push((proof.len(), reps[0]));
        }
        binary_cu.push(per_mode[0].1);
        radix4_cu.push(per_mode[1].1);
        samples.push(VarianceSeedSample {
            seed,
            binary_proof_bytes: per_mode[0].0,
            binary_verify_cu: per_mode[0].1,
            radix4_proof_bytes: per_mode[1].0,
            radix4_verify_cu: per_mode[1].1,
            radix4_saving_cu: per_mode[0].1 as i64 - per_mode[1].1 as i64,
        });
        eprintln!(
            "stage2-variance-g16: seed {seed}/{SEEDS} binary {} radix4 {}",
            per_mode[0].1, per_mode[1].1
        );
    }

    let binary_stats = variance_stats("binary_minimal_subtree", binary_cu);
    let radix4_stats = variance_stats("radix4_minimal_subtree", radix4_cu);
    let penalty = radix4_stats.range_cu;
    let adjusted = STRICT_CANDIDATE_PROJECTION + penalty as i64;
    let two_sigma = 2.0 * radix4_stats.population_std_dev_cu;
    let secondary_adjusted = STRICT_CANDIDATE_PROJECTION + two_sigma.round() as i64;
    Ok(VarianceG16Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-variance-g16".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        seeds: SEEDS,
        repetitions_per_seed: REPETITIONS,
        criterion: CRITERION.to_string(),
        samples,
        binary_stats,
        radix4_stats,
        strict_candidate_projection_cu: STRICT_CANDIDATE_PROJECTION,
        ten_percent_slack_maximum_cu: TEN_PERCENT_SLACK_MAXIMUM,
        single_draw_headroom_cu: TEN_PERCENT_SLACK_MAXIMUM - STRICT_CANDIDATE_PROJECTION,
        criterion_penalty_range_cu: penalty,
        criterion_adjusted_projection_cu: adjusted,
        criterion_passes: adjusted <= TEN_PERCENT_SLACK_MAXIMUM,
        secondary_two_sigma_penalty_cu: two_sigma,
        secondary_adjusted_projection_cu: secondary_adjusted,
        notes: vec![
            "Each row is a real claim-free synthetic-C2 g16 proof; g16 grinding makes 16 fresh draws affordable where 16 fresh 32-bit nonce searches are not.".to_string(),
            "Spread mechanism: the statement digest and coefficients move every absorbed root, so challenges, grinding nonce, query positions, unique-fiber counts, and minimal-subtree frontiers are fresh per seed; the verifier code path is fixed.".to_string(),
            "All five repetitions per seed are asserted identical; per-seed CU is a deterministic function of the draw, so the across-seed spread is exactly the transcript-draw variance.".to_string(),
            "The g16-to-g32 spread transfer is an assumption stated inside the criterion, not a measurement; the integrated g32 payment proof remains the final word.".to_string(),
        ],
    })
}

pub fn run_layout_sweep() -> Result<LayoutSweep> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 10 * LAMPORTS_PER_SOL)?;

    let probe_account = Keypair::new();
    create_program_account(&rpc, &payer, &probe_account, PROOF_ACCOUNT_HEADER_LEN)?;

    let sweep: [(u8, u16, u16); 6] = [
        (12, 16, 32),
        (11, 32, 32),
        (10, 64, 32),
        (9, 128, 32),
        (8, 256, 32),
        (6, 400, 32),
    ];
    let mut points = Vec::new();
    for (log_rows, columns, query_count) in sweep {
        let leaf_bytes = columns.saturating_mul(4);
        let instruction = AspisInstruction::LayoutProbe {
            log_rows,
            columns,
            query_count,
            leaf_bytes,
        };
        let ix = proof_instruction(&payer.pubkey(), &probe_account.pubkey(), &instruction)?;
        let blockhash = rpc.latest_blockhash()?;
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ix,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let sim = rpc.simulate_verbose(&tx)?;
        points.push(LayoutPoint {
            log_rows,
            columns,
            query_count,
            leaf_bytes,
            simulation_units: sim.units,
            simulation_error: sim.err,
            markers: parse_cu_markers(&sim.logs, "aspis-layout:"),
        });
    }

    Ok(LayoutSweep {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-layout-sweep".to_string(),
        validator_version: validator_version(),
        points,
        notes: vec![
            "Synthetic Stage 2 layout probe: SHA-256 leaf/path hashing plus QM31 RLC recombination over k columns.".to_string(),
            "This does not prove statement correctness; it pulls design item 13.8 forward so lr14 is not treated as a frozen target.".to_string(),
        ],
    })
}

fn run_onchain_variant(
    rpc: &Rpc,
    payer: &Keypair,
    profile: &'static Profile,
    payload: FoldPayload,
    mode: MerkleMode,
) -> Result<OnchainVariant> {
    run_onchain_variant_with_proof(rpc, payer, profile, payload, mode, None)
}

fn run_onchain_variant_with_proof(
    rpc: &Rpc,
    payer: &Keypair,
    profile: &'static Profile,
    payload: FoldPayload,
    mode: MerkleMode,
    proof_override: Option<Vec<u8>>,
) -> Result<OnchainVariant> {
    let payload_name = match payload {
        FoldPayload::RawFibers => "raw_fibers",
        FoldPayload::ProofCarriedRoundLocal => "proof_carried_round_local",
    };
    let mode_name = match mode {
        MerkleMode::SinglePaths => "single_paths",
        MerkleMode::MinimalSubtree => "minimal_subtree",
        MerkleMode::Radix4MinimalSubtree => "radix4_minimal_subtree",
    };
    eprintln!(
        "stage0-onchain: {} / {payload_name} / {mode_name}",
        profile.name
    );

    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let digest = crate::host_statement_digest(0);
    let options = ProveOptions {
        fold_payload: payload,
        merkle_mode: mode,
    };
    let proof =
        proof_override.unwrap_or_else(|| prove(profile, &coeffs, &digest, &options, HOST_HASH));
    anyhow::ensure!(
        aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
        "proof override failed current host verification"
    );

    let proof_account = Keypair::new();
    let (chunks, upload_cu) = upload_proof(rpc, payer, &proof_account, &proof, true)?;

    let mut verify_cu = Vec::new();
    let mut verify_error = None;
    for _ in 0..VERIFY_REPETITIONS {
        let blockhash = rpc.latest_blockhash()?;
        let tx = verify_tx(payer, &proof_account.pubkey(), digest, blockhash, false)?;
        let (units, err) = rpc.simulate(&tx)?;
        if let Some(err) = err {
            if let Some(units) = units {
                verify_cu.push(units);
            }
            verify_error = Some(err);
            break;
        }
        verify_cu.push(units.ok_or_else(|| anyhow!("no unitsConsumed"))?);
    }

    if verify_error.is_some() {
        let mean = if verify_cu.is_empty() {
            0.0
        } else {
            verify_cu.iter().sum::<u64>() as f64 / verify_cu.len() as f64
        };
        return Ok(OnchainVariant {
            profile: profile.name,
            soundness_label: profile.soundness_label,
            fold_payload: payload_name,
            merkle_mode: mode_name,
            status: "verify_failed",
            verify_error,
            proof_bytes: proof.len(),
            upload_chunks: chunks,
            upload_cu_total: upload_cu,
            verify_cu,
            verify_cu_mean: mean,
            verify_repetitions_requested: VERIFY_REPETITIONS,
            corruption_rejected_onchain: Vec::new(),
        });
    }

    // On-chain corruption suite: re-upload each corrupted proof, expect the
    // verify simulation to error.
    let mut corruption_rejected = Vec::new();
    let host_results = crate::host::corruption_suite(profile, &proof, &digest);
    for case in &host_results {
        let mut corrupted = proof.to_vec();
        match case.name {
            "trailing_byte" => corrupted.push(0),
            "truncation" => {
                corrupted.truncate(corrupted.len() - 1);
            }
            "statement_digest_mismatch" => {}
            _ => corrupted[case.byte_offset] ^= 0x01,
        }
        let corrupt_account = Keypair::new();
        upload_proof(rpc, payer, &corrupt_account, &corrupted, true)?;
        let check_digest = if case.name == "statement_digest_mismatch" {
            crate::host_statement_digest(0xDEAD_BEEF)
        } else {
            digest
        };
        let blockhash = rpc.latest_blockhash()?;
        let tx = verify_tx(
            payer,
            &corrupt_account.pubkey(),
            check_digest,
            blockhash,
            false,
        )?;
        let (_, err) = rpc.simulate(&tx)?;
        corruption_rejected.push((case.name.to_string(), err.is_some()));
    }

    let mean = verify_cu.iter().sum::<u64>() as f64 / verify_cu.len() as f64;
    Ok(OnchainVariant {
        profile: profile.name,
        soundness_label: profile.soundness_label,
        fold_payload: payload_name,
        merkle_mode: mode_name,
        status: "accepted",
        verify_error: None,
        proof_bytes: proof.len(),
        upload_chunks: chunks,
        upload_cu_total: upload_cu,
        verify_cu,
        verify_cu_mean: mean,
        verify_repetitions_requested: VERIFY_REPETITIONS,
        corruption_rejected_onchain: corruption_rejected,
    })
}
