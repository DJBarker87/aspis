//! `stage0-host`: host-side Stage 0 measurement + corruption suite.
//!
//! Produces `results/stage0/host_summary.json`. Every number in the Stage 0
//! gate note traces back to this artifact (or the on-chain one).

use std::time::Instant;

use anyhow::Result;
use serde::Serialize;

use aspis_core::params::{PROFILE_CAPACITY, PROFILE_CAPACITY_LR14, PROFILE_JOHNSON};
use aspis_core::proof::HEADER_LEN;
use aspis_core::{verify, FoldPayload, MerkleMode, Profile, VerifyError};
use aspis_prover::{prove, seeded_coeffs, ProveOptions, HOST_HASH};

pub const PARITY_RUNS: u64 = 10;

#[derive(Serialize)]
pub struct CorruptionResult {
    pub name: &'static str,
    pub byte_offset: usize,
    pub rejected: bool,
    pub error: String,
}

#[derive(Serialize)]
pub struct VariantResult {
    pub profile: &'static str,
    pub soundness_label: &'static str,
    pub log_rows: u32,
    pub log_blowup: u32,
    pub query_count: u16,
    pub grinding_bits: u8,
    pub fold_payload: &'static str,
    pub merkle_mode: &'static str,
    pub runs: u64,
    pub accepted: u64,
    pub proof_bytes_min: usize,
    pub proof_bytes_max: usize,
    pub proof_bytes_mean: f64,
    pub prove_ms_mean: f64,
    pub verify_ms_mean: f64,
    pub corruption: Vec<CorruptionResult>,
}

#[derive(Serialize)]
pub struct HostSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub parity_runs_per_variant: u64,
    pub variants: Vec<VariantResult>,
    pub notes: Vec<String>,
}

use crate::host_statement_digest as statement_digest;

fn payload_name(p: FoldPayload) -> &'static str {
    match p {
        FoldPayload::RawFibers => "raw_fibers",
        FoldPayload::ProofCarriedRoundLocal => "proof_carried_round_local",
    }
}

fn mode_name(m: MerkleMode) -> &'static str {
    match m {
        MerkleMode::SinglePaths => "single_paths",
        MerkleMode::MinimalSubtree => "minimal_subtree",
    }
}

/// The four Stage 0 corruption classes (plus binding checks), applied to a
/// known-good proof. Every one must reject.
pub fn corruption_suite(
    profile: &Profile,
    proof: &[u8],
    digest: &[u8; 32],
) -> Vec<CorruptionResult> {
    let num_rounds = profile.num_rounds() as usize;
    let roots_off = HEADER_LEN;
    let final_off = roots_off + num_rounds * 32;
    let nonce_off = final_off + profile.final_poly_len() as usize * 16;
    let body_off = nonce_off + 8;

    let mut results = Vec::new();
    let mut run = |name: &'static str, offset: usize, digest: &[u8; 32]| {
        let mut corrupted = proof.to_vec();
        corrupted[offset] ^= 0x01;
        let outcome = verify(&corrupted, digest, HOST_HASH);
        results.push(CorruptionResult {
            name,
            byte_offset: offset,
            rejected: outcome.is_err(),
            error: format!("{:?}", outcome.err()),
        });
    };

    // 1. commitment root corruption
    run("root_corruption", roots_off + 5, digest);
    // 2. fold payload (opened fiber value) corruption
    run("payload_corruption", body_off + 2 + 3, digest);
    // 3. final polynomial corruption
    run("final_value_corruption", final_off + 1, digest);
    // 4. grinding witness corruption
    run("grinding_corruption", nonce_off, digest);

    // binding: same proof, wrong statement digest
    let wrong = statement_digest(0xDEAD_BEEF);
    let outcome = verify(proof, &wrong, HOST_HASH);
    results.push(CorruptionResult {
        name: "statement_digest_mismatch",
        byte_offset: 0,
        rejected: outcome.is_err(),
        error: format!("{:?}", outcome.err()),
    });
    // framing: trailing byte
    let mut extended = proof.to_vec();
    extended.push(0);
    let outcome = verify(&extended, digest, HOST_HASH);
    results.push(CorruptionResult {
        name: "trailing_byte",
        byte_offset: proof.len(),
        rejected: outcome.is_err(),
        error: format!("{:?}", outcome.err()),
    });
    // framing: truncation
    let outcome = verify(&proof[..proof.len() - 1], digest, HOST_HASH);
    results.push(CorruptionResult {
        name: "truncation",
        byte_offset: proof.len() - 1,
        rejected: outcome.is_err(),
        error: format!("{:?}", outcome.err()),
    });

    results
}

pub fn run_variant(
    profile: &'static Profile,
    fold_payload: FoldPayload,
    merkle_mode: MerkleMode,
) -> Result<VariantResult> {
    let options = ProveOptions {
        fold_payload,
        merkle_mode,
    };
    let mut sizes = Vec::new();
    let mut prove_ms = Vec::new();
    let mut verify_ms = Vec::new();
    let mut accepted = 0u64;
    let mut first_proof: Option<(Vec<u8>, [u8; 32])> = None;

    for seed in 0..PARITY_RUNS {
        let coeffs = seeded_coeffs(profile.log_rows, seed + 1);
        let digest = statement_digest(seed);
        let t0 = Instant::now();
        let proof = prove(profile, &coeffs, &digest, &options, HOST_HASH);
        prove_ms.push(t0.elapsed().as_secs_f64() * 1e3);
        sizes.push(proof.len());
        let t1 = Instant::now();
        let ok = verify(&proof, &digest, HOST_HASH);
        verify_ms.push(t1.elapsed().as_secs_f64() * 1e3);
        match ok {
            Ok(()) => accepted += 1,
            Err(err) => anyhow::bail!(
                "variant {}/{}/{} seed {} rejected: {:?}",
                profile.name,
                payload_name(fold_payload),
                mode_name(merkle_mode),
                seed,
                err
            ),
        }
        if first_proof.is_none() {
            first_proof = Some((proof, digest));
        }
    }

    let (proof, digest) = first_proof.unwrap();
    let corruption = corruption_suite(profile, &proof, &digest);

    let mean = |v: &[f64]| v.iter().sum::<f64>() / v.len() as f64;
    Ok(VariantResult {
        profile: profile.name,
        soundness_label: profile.soundness_label,
        log_rows: profile.log_rows,
        log_blowup: profile.log_blowup,
        query_count: profile.query_count,
        grinding_bits: profile.grinding_bits,
        fold_payload: payload_name(fold_payload),
        merkle_mode: mode_name(merkle_mode),
        runs: PARITY_RUNS,
        accepted,
        proof_bytes_min: *sizes.iter().min().unwrap(),
        proof_bytes_max: *sizes.iter().max().unwrap(),
        proof_bytes_mean: sizes.iter().sum::<usize>() as f64 / sizes.len() as f64,
        prove_ms_mean: mean(&prove_ms),
        verify_ms_mean: mean(&verify_ms),
        corruption,
    })
}

pub fn run_stage0_host() -> Result<HostSummary> {
    let mut variants = Vec::new();
    for profile in [&PROFILE_CAPACITY, &PROFILE_JOHNSON, &PROFILE_CAPACITY_LR14] {
        for payload in [FoldPayload::RawFibers, FoldPayload::ProofCarriedRoundLocal] {
            for mode in [MerkleMode::MinimalSubtree, MerkleMode::SinglePaths] {
                eprintln!(
                    "stage0-host: {} / {} / {}",
                    profile.name,
                    payload_name(payload),
                    mode_name(mode)
                );
                variants.push(run_variant(profile, payload, mode)?);
            }
        }
    }

    let all_rejected = variants
        .iter()
        .all(|v| v.corruption.iter().all(|c| c.rejected));
    anyhow::ensure!(all_rejected, "corruption suite had an accepted corruption");

    Ok(HostSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-host".to_string(),
        parity_runs_per_variant: PARITY_RUNS,
        variants,
        notes: vec![
            "Host-side measurements only; CU numbers come from stage0-onchain on a machine with the Solana toolchain.".to_string(),
            "All soundness labels are heuristic until the Stage 1 soundness note exists; no security figure may be quoted from this artifact.".to_string(),
            "verify() here is the identical no_std code path the SBF program executes (hash backend swapped), so accept/reject parity is structural; on-chain re-execution is still required by the Stage 0 gate.".to_string(),
        ],
    })
}

/// Also used by the corruption suite's unused-variant lint.
#[allow(dead_code)]
fn error_name(err: VerifyError) -> u32 {
    err.code()
}
