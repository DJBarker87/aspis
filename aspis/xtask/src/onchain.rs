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

use anyhow::{anyhow, bail, Context, Result};
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
use aspis_prover::{prove, seeded_coeffs, ProveOptions, HOST_HASH};
use aspis_verifier::{AspisInstruction, PROOF_ACCOUNT_HEADER_LEN};

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

fn free_port() -> Result<u16> {
    Ok(TcpListener::bind("127.0.0.1:0")?.local_addr()?.port())
}

fn start_validator(root: &Path, so: &Path) -> Result<Validator> {
    let ledger = root.join(".stage0-validator");
    let _ = fs::remove_dir_all(&ledger);
    let rpc_port = free_port()?;
    let faucet_port = free_port()?;
    let child = Command::new("solana-test-validator")
        .arg("--reset")
        .arg("--quiet")
        .arg("--ledger")
        .arg(&ledger)
        .arg("--rpc-port")
        .arg(rpc_port.to_string())
        .arg("--faucet-port")
        .arg(faucet_port.to_string())
        .arg("--bpf-program")
        .arg(aspis_verifier::id().to_string())
        .arg(so)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .context("solana-test-validator not found on PATH")?;
    let validator = Validator {
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
            "This runner measures the literal ruled schedule capacity_lr10_q36_g32 first (prover-side grinding for that row is a ~2^32-hash one-off); the remaining qNN/g16 rows are verifier-cost proxies for their g32 counterparts, sound because the verifier-side grinding check is one SHA-256 syscall independent of the difficulty bits (corroborated by onchain_g32_summary.json).".to_string(),
            "Combine these PCS verifier costs with layout_sweep RLC/wide-leaf deltas; do not add the full synthetic Merkle loop or path hashing is double-counted.".to_string(),
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

    let sweep = [
        (12, 16, 32),
        (11, 32, 32),
        (10, 64, 32),
        (9, 128, 32),
        (8, 256, 32),
        (6, 400, 32),
    ];
    let mut points = Vec::new();
    for (log_rows, columns, query_count) in sweep {
        let leaf_bytes = (columns as u16).saturating_mul(4);
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
    let payload_name = match payload {
        FoldPayload::RawFibers => "raw_fibers",
        FoldPayload::ProofCarriedRoundLocal => "proof_carried_round_local",
    };
    let mode_name = match mode {
        MerkleMode::SinglePaths => "single_paths",
        MerkleMode::MinimalSubtree => "minimal_subtree",
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
    let proof = prove(profile, &coeffs, &digest, &options, HOST_HASH);

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
