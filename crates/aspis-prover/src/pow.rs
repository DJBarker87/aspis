//! Host grinding for production proofs.
//!
//! The verifier predicate is exactly
//! `SHA256(transcript_state || 0x03 || nonce.to_le_bytes())`, with the
//! requested number of leading zero bits.  The portable path searches on all
//! host cores.  On macOS, setting `ASPIS_POW_MINER` to the compiled
//! `tools/aspis-pow-metal.swift` runner delegates the same one-block SHA-256
//! search to Metal.  Every delegated answer is checked again through the
//! consensus [`Transcript::grinding_ok`] predicate before it is accepted.
//! The bundled CPU and Metal implementations additionally select the global
//! minimum valid nonce; a custom external command is part of the trusted
//! honest-prover implementation for that privacy-only rule.

use aspis_core::transcript::Transcript;
use std::process::Command;
use std::process::Stdio;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

const CPU_PROGRESS_POLL: Duration = Duration::from_millis(100);
const CPU_PROGRESS_INTERVAL: Duration = Duration::from_secs(5);

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 15) as usize] as char);
    }
    output
}

fn checkpoint_path(state: &[u8; 32], bits: u8) -> Option<String> {
    let directory = std::env::var("ASPIS_POW_CHECKPOINT_DIR").ok()?;
    let state_hex = hex(state);
    Some(format!("{directory}/pow-{bits}-{state_hex}.checkpoint"))
}

fn external_nonce(transcript: &Transcript, bits: u8) -> Option<u64> {
    let miner = std::env::var_os("ASPIS_POW_MINER")?;
    let state = transcript.diagnostic_state();
    let mut command = Command::new(miner);
    command
        .arg("--state")
        .arg(hex(&state))
        .arg("--bits")
        .arg(bits.to_string())
        .stderr(Stdio::inherit());
    if let Some(path) = checkpoint_path(&state, bits) {
        command.arg("--checkpoint").arg(path).arg("--resume");
    }
    let output = command.output().unwrap_or_else(|error| {
        panic!("failed to start ASPIS_POW_MINER: {error}");
    });
    assert!(
        output.status.success(),
        "ASPIS_POW_MINER failed with {}: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout)
    );
    let stdout = String::from_utf8(output.stdout).expect("ASPIS_POW_MINER stdout is not UTF-8");
    let nonce = stdout
        .lines()
        .find_map(|line| line.strip_prefix("nonce="))
        .expect("ASPIS_POW_MINER did not print nonce=<u64>")
        .parse::<u64>()
        .expect("ASPIS_POW_MINER printed an invalid nonce");
    assert!(
        transcript.grinding_ok(nonce, bits),
        "ASPIS_POW_MINER returned a nonce rejected by the canonical transcript"
    );
    Some(nonce)
}

/// Find the minimum valid nonce for the canonical transcript predicate.
///
/// Minimum-nonce selection is an honest-prover rule, not an extra verifier
/// predicate. It makes the prover's output independent of CPU/GPU scheduling
/// and gives the zero-knowledge simulator the exact first-success geometric
/// law. Every delegated answer is still checked by the consensus predicate.
pub fn find_grinding_nonce(transcript: &Transcript, bits: u8) -> u64 {
    assert!(
        bits <= 63,
        "grinding difficulty exceeds the u64 threshold implementation"
    );
    if bits == 0 {
        return 0;
    }
    if let Some(nonce) = external_nonce(transcript, bits) {
        return nonce;
    }
    find_grinding_nonce_cpu(transcript, bits)
}

/// Controlled failures from the unpublished-attempt PoW path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnpublishedPowError {
    Difficulty,
    Spawn,
    ProcessFailed,
    Utf8,
    MissingNonce,
    InvalidNonce,
    NonceRejected,
    Exhausted,
}

/// Unpublished-attempt companion used by the profile-22 first-good manager.
/// It emits no progress output, creates no checkpoint, and suppresses an
/// external miner's stderr. The bundled CPU implementation returns the global
/// minimum. A configured external miner is part of the trusted honest-prover
/// implementation and MUST satisfy the same global-minimum contract; the
/// consensus predicate can check validity but cannot prove minimality.
pub fn find_grinding_nonce_unpublished(
    transcript: &Transcript,
    bits: u8,
) -> Result<u64, UnpublishedPowError> {
    if bits > 63 {
        return Err(UnpublishedPowError::Difficulty);
    }
    if bits == 0 {
        return Ok(0);
    }
    if let Some(miner) = std::env::var_os("ASPIS_POW_MINER") {
        let state = transcript.diagnostic_state();
        let output = Command::new(miner)
            .arg("--state")
            .arg(hex(&state))
            .arg("--bits")
            .arg(bits.to_string())
            .stderr(Stdio::null())
            .output()
            .map_err(|_| UnpublishedPowError::Spawn)?;
        if !output.status.success() {
            return Err(UnpublishedPowError::ProcessFailed);
        }
        let stdout = String::from_utf8(output.stdout).map_err(|_| UnpublishedPowError::Utf8)?;
        let nonce = stdout
            .lines()
            .find_map(|line| line.strip_prefix("nonce="))
            .ok_or(UnpublishedPowError::MissingNonce)?
            .parse::<u64>()
            .map_err(|_| UnpublishedPowError::InvalidNonce)?;
        if !transcript.grinding_ok(nonce, bits) {
            return Err(UnpublishedPowError::NonceRejected);
        }
        return Ok(nonce);
    }
    if bits <= 20 {
        return (0u64..)
            .find(|nonce| transcript.grinding_ok(*nonce, bits))
            .ok_or(UnpublishedPowError::Exhausted);
    }
    find_grinding_nonce_cpu_parallel_quiet(transcript, bits)
}

fn find_grinding_nonce_cpu_parallel_quiet(
    transcript: &Transcript,
    bits: u8,
) -> Result<u64, UnpublishedPowError> {
    find_grinding_nonce_cpu_parallel_quiet_from(transcript, bits, 0)
}

fn find_grinding_nonce_cpu_parallel_quiet_from(
    transcript: &Transcript,
    bits: u8,
    start: u64,
) -> Result<u64, UnpublishedPowError> {
    let workers = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .max(1);
    let found = Arc::new(AtomicBool::new(false));
    let result = Arc::new(AtomicU64::new(u64::MAX));
    std::thread::scope(|scope| {
        for worker in 0..workers {
            let found = Arc::clone(&found);
            let result = Arc::clone(&result);
            let transcript = transcript.clone();
            scope.spawn(move || {
                let Some(mut nonce) = start.checked_add(worker as u64) else {
                    return;
                };
                let stride = workers as u64;
                loop {
                    if found.load(Ordering::Acquire) && nonce >= result.load(Ordering::Acquire) {
                        break;
                    }
                    if transcript.grinding_ok(nonce, bits) {
                        result.fetch_min(nonce, Ordering::AcqRel);
                        found.store(true, Ordering::Release);
                        break;
                    }
                    let Some(next) = nonce.checked_add(stride) else {
                        break;
                    };
                    nonce = next;
                }
            });
        }
    });
    let nonce = result.load(Ordering::Acquire);
    if !found.load(Ordering::Acquire) {
        return Err(UnpublishedPowError::Exhausted);
    }
    if !transcript.grinding_ok(nonce, bits) {
        return Err(UnpublishedPowError::NonceRejected);
    }
    Ok(nonce)
}

/// Measurement-only companion that returns the minimum valid work nonce at
/// or above `start`.  The consensus predicate is unchanged.  This exists only
/// for the default-off V7 final-nonce cutoff experiment, where an unpublished
/// valid nonce may be discarded after its public q16 schedule is inspected.
#[cfg(feature = "v7-final-nonce-cutoff-audit")]
pub(crate) fn find_grinding_nonce_unpublished_from(
    transcript: &Transcript,
    bits: u8,
    start: u64,
) -> Result<u64, UnpublishedPowError> {
    if bits > 63 {
        return Err(UnpublishedPowError::Difficulty);
    }
    if bits == 0 {
        return Ok(start);
    }
    if let Some(miner) = std::env::var_os("ASPIS_POW_MINER") {
        let state = transcript.diagnostic_state();
        let output = Command::new(miner)
            .arg("--state")
            .arg(hex(&state))
            .arg("--bits")
            .arg(bits.to_string())
            .arg("--start")
            .arg(start.to_string())
            .stderr(Stdio::null())
            .output()
            .map_err(|_| UnpublishedPowError::Spawn)?;
        if !output.status.success() {
            return Err(UnpublishedPowError::ProcessFailed);
        }
        let stdout = String::from_utf8(output.stdout).map_err(|_| UnpublishedPowError::Utf8)?;
        let nonce = stdout
            .lines()
            .find_map(|line| line.strip_prefix("nonce="))
            .ok_or(UnpublishedPowError::MissingNonce)?
            .parse::<u64>()
            .map_err(|_| UnpublishedPowError::InvalidNonce)?;
        if nonce < start {
            return Err(UnpublishedPowError::InvalidNonce);
        }
        if !transcript.grinding_ok(nonce, bits) {
            return Err(UnpublishedPowError::NonceRejected);
        }
        return Ok(nonce);
    }
    if bits <= 20 {
        return (start..)
            .find(|nonce| transcript.grinding_ok(*nonce, bits))
            .ok_or(UnpublishedPowError::Exhausted);
    }
    find_grinding_nonce_cpu_parallel_quiet_from(transcript, bits, start)
}

fn find_grinding_nonce_cpu(transcript: &Transcript, bits: u8) -> u64 {
    if bits <= 20 {
        return (0u64..)
            .find(|nonce| transcript.grinding_ok(*nonce, bits))
            .expect("u64 nonce space exhausted");
    }
    find_grinding_nonce_cpu_parallel(transcript, bits)
}

fn find_grinding_nonce_cpu_parallel(transcript: &Transcript, bits: u8) -> u64 {
    let report_progress = std::env::var("ASPIS_POW_PROGRESS").as_deref() == Ok("1");
    let workers = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .max(1);
    let found = Arc::new(AtomicBool::new(false));
    let result = Arc::new(AtomicU64::new(u64::MAX));
    let active = Arc::new(AtomicUsize::new(workers));
    let tested = Arc::new(AtomicU64::new(0));
    let started = Instant::now();

    std::thread::scope(|scope| {
        for worker in 0..workers {
            let found = Arc::clone(&found);
            let result = Arc::clone(&result);
            let active = Arc::clone(&active);
            let tested = Arc::clone(&tested);
            let transcript = transcript.clone();
            scope.spawn(move || {
                let mut nonce = worker as u64;
                let stride = workers as u64;
                let mut local_tested = 0u64;
                loop {
                    if found.load(Ordering::Acquire) && nonce >= result.load(Ordering::Acquire) {
                        break;
                    }
                    if transcript.grinding_ok(nonce, bits) {
                        result.fetch_min(nonce, Ordering::AcqRel);
                        found.store(true, Ordering::Release);
                        break;
                    }
                    local_tested += 1;
                    if local_tested & ((1 << 16) - 1) == 0 {
                        tested.fetch_add(1 << 16, Ordering::Relaxed);
                    }
                    let Some(next) = nonce.checked_add(stride) else {
                        break;
                    };
                    nonce = next;
                }
                tested.fetch_add(local_tested & ((1 << 16) - 1), Ordering::Relaxed);
                active.fetch_sub(1, Ordering::AcqRel);
            });
        }
        if report_progress {
            let active = Arc::clone(&active);
            let tested = Arc::clone(&tested);
            scope.spawn(move || {
                let mut last_report = Instant::now();
                while active.load(Ordering::Acquire) != 0 {
                    std::thread::sleep(CPU_PROGRESS_POLL);
                    if last_report.elapsed() >= CPU_PROGRESS_INTERVAL {
                        let count = tested.load(Ordering::Relaxed);
                        let seconds = started.elapsed().as_secs_f64();
                        eprintln!(
                            "aspis-pow cpu: bits={bits} tested={count} rate={:.2} MH/s elapsed={seconds:.1}s",
                            count as f64 / seconds / 1_000_000.0
                        );
                        last_report = Instant::now();
                    }
                }
            });
        }
    });

    let nonce = result.load(Ordering::Acquire);
    assert!(found.load(Ordering::Acquire), "u64 nonce space exhausted");
    assert!(transcript.grinding_ok(nonce, bits));
    nonce
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HOST_HASH;
    use aspis_core::transcript::label;

    #[test]
    fn cpu_miner_matches_canonical_predicate() {
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::PROFILE, b"aspis-pow-kat-v1");
        transcript.absorb(label::STATEMENT, &[0xa5; 32]);
        assert_eq!(
            find_grinding_nonce_unpublished(&transcript, 64),
            Err(UnpublishedPowError::Difficulty)
        );
        assert_eq!(find_grinding_nonce_unpublished(&transcript, 0), Ok(0));
        let nonce = find_grinding_nonce_cpu(&transcript, 16);
        assert_eq!(nonce, 100_214);
        assert!(transcript.grinding_ok(nonce, 16));
        assert!(!(0..nonce).any(|candidate| transcript.grinding_ok(candidate, 16)));

        // Exercise the scheduler-independent parallel path at a cheap test
        // difficulty and require the same global minimum.
        let parallel = find_grinding_nonce_cpu_parallel(&transcript, 16);
        assert_eq!(parallel, nonce);
        let unpublished = find_grinding_nonce_cpu_parallel_quiet(&transcript, 16).unwrap();
        assert_eq!(unpublished, nonce);
    }

    #[cfg(feature = "v7-final-nonce-cutoff-audit")]
    #[test]
    fn unpublished_range_miner_advances_between_valid_nonces() {
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::PROFILE, b"aspis-pow-kat-v1");
        transcript.absorb(label::STATEMENT, &[0xa5; 32]);

        let first = find_grinding_nonce_unpublished_from(&transcript, 16, 0).unwrap();
        assert_eq!(first, 100_214);
        let second = find_grinding_nonce_unpublished_from(&transcript, 16, first + 1).unwrap();
        assert!(second > first);
        assert!(transcript.grinding_ok(second, 16));
        assert!(!(first + 1..second).any(|candidate| transcript.grinding_ok(candidate, 16)));
    }

    /// Build `tools/aspis-pow-metal.swift`, set `ASPIS_POW_MINER` to the
    /// resulting executable, and run this ignored test on Apple hosts.  The
    /// delegated result is accepted only through the Rust verifier predicate.
    #[test]
    #[ignore = "requires an explicitly configured Apple Metal runner"]
    fn configured_metal_miner_matches_canonical_predicate() {
        assert!(std::env::var_os("ASPIS_POW_MINER").is_some());
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::PROFILE, b"aspis-pow-kat-v1");
        transcript.absorb(label::STATEMENT, &[0xa5; 32]);
        let nonce = find_grinding_nonce(&transcript, 16);
        assert_eq!(nonce, 100_214);
        assert!(transcript.grinding_ok(nonce, 16));
        assert!(!(0..nonce).any(|candidate| transcript.grinding_ok(candidate, 16)));
    }
}
