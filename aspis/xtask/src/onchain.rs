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
    prove, prove_with_synthetic_second_phase, seeded_coeffs, ProveOptions, HOST_HASH,
};
use aspis_verifier::{AspisInstruction, ZkKernelKind, PROOF_ACCOUNT_HEADER_LEN};

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
