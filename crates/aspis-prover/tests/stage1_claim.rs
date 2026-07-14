//! Stage 1 queue item 2: (z, v) evaluation-claim binding + challenge-order
//! tests (soundness-note §2 and appendix).
//!
//! What these tests DO establish at this revision: the claim is a
//! transcript-absorbed public input, so claim mix-and-match, flag mismatch,
//! and absorption-order attacks all reject.
//!
//! The interleaved relation sumcheck now also enforces w(z) = v against the
//! explicit final polynomial; false claims reject at the first boundary.

use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
use aspis_core::{verify_with_claim, EvaluationClaim, VerifyError};
use aspis_prover::{
    multilinear_eval, prove, prove_with_claim, prove_with_gamma_before_claims_for_tests,
    seeded_coeffs,
};

fn digest(seed: u64) -> [u8; 32] {
    use sha2::Digest;
    let mut h = sha2::Sha256::new();
    h.update(b"aspis-stage1-claim-test");
    h.update(seed.to_le_bytes());
    h.finalize().into()
}

fn options() -> aspis_prover::ProveOptions {
    aspis_prover::ProveOptions {
        fold_payload: aspis_core::FoldPayload::RawFibers,
        merkle_mode: aspis_core::MerkleMode::MinimalSubtree,
    }
}

fn honest_claim(coeffs: &[aspis_core::field::M31], seed: u64) -> EvaluationClaim {
    // deterministic pseudo-random point
    let z: Vec<aspis_core::field::QM31> = (0..PROFILE.log_rows as u64)
        .map(|i| {
            let x = seed
                .wrapping_mul(31)
                .wrapping_add(i)
                .wrapping_mul(0x9E37_79B9) as u32;
            aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                aspis_core::field::M31(x & 0x7fff_fffe),
            ))
        })
        .collect();
    let v = multilinear_eval(coeffs, &z);
    EvaluationClaim { z, v }
}

#[test]
fn claim_roundtrip_accepts() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 42);
    let d = digest(0);
    let claim = honest_claim(&coeffs, 7);
    let proof = prove_with_claim(
        &PROFILE,
        &coeffs,
        &d,
        &claim,
        &options(),
        aspis_prover::HOST_HASH,
    );
    assert_eq!(
        verify_with_claim(&proof, &d, Some(&claim), aspis_prover::HOST_HASH),
        Ok(())
    );
}

#[test]
fn claim_mix_and_match_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 42);
    let d = digest(0);
    let claim = honest_claim(&coeffs, 7);
    let proof = prove_with_claim(
        &PROFILE,
        &coeffs,
        &d,
        &claim,
        &options(),
        aspis_prover::HOST_HASH,
    );

    // different point
    let other = honest_claim(&coeffs, 8);
    assert!(verify_with_claim(&proof, &d, Some(&other), aspis_prover::HOST_HASH).is_err());

    // same point, perturbed value
    let mut wrong_v = claim.clone();
    wrong_v.v = wrong_v.v.add(aspis_core::field::QM31::ONE);
    assert!(verify_with_claim(&proof, &d, Some(&wrong_v), aspis_prover::HOST_HASH).is_err());
}

#[test]
fn claim_flag_mismatch_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 42);
    let d = digest(0);
    let claim = honest_claim(&coeffs, 7);

    // claim-carrying proof verified without a claim
    let proof = prove_with_claim(
        &PROFILE,
        &coeffs,
        &d,
        &claim,
        &options(),
        aspis_prover::HOST_HASH,
    );
    assert_eq!(
        verify_with_claim(&proof, &d, None, aspis_prover::HOST_HASH),
        Err(VerifyError::ClaimMissing)
    );

    // claim-less proof verified with a claim
    let plain = prove(&PROFILE, &coeffs, &d, &options(), aspis_prover::HOST_HASH);
    assert_eq!(
        verify_with_claim(&plain, &d, Some(&claim), aspis_prover::HOST_HASH),
        Err(VerifyError::ClaimUnexpected)
    );
}

#[test]
fn claim_shape_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 42);
    let d = digest(0);
    let claim = honest_claim(&coeffs, 7);
    let proof = prove_with_claim(
        &PROFILE,
        &coeffs,
        &d,
        &claim,
        &options(),
        aspis_prover::HOST_HASH,
    );
    let mut short = claim.clone();
    short.z.pop();
    assert_eq!(
        verify_with_claim(&proof, &d, Some(&short), aspis_prover::HOST_HASH),
        Err(VerifyError::ClaimShape)
    );
}

#[test]
fn gamma_before_claims_attack_rejects() {
    // A prover that squeezes gamma after C2 but before absorbing the main and
    // helper evaluations derives a self-consistent broken transcript. The
    // canonical verifier must reject it; stage1_ordering additionally proves
    // this vector's teeth against the matching weakened verifier.
    let coeffs = seeded_coeffs(PROFILE.log_rows, 42);
    let d = digest(0);
    let claim = honest_claim(&coeffs, 7);
    let misordered = prove_with_gamma_before_claims_for_tests(
        &PROFILE,
        &coeffs,
        &d,
        &claim,
        &options(),
        aspis_prover::HOST_HASH,
    );
    assert!(verify_with_claim(&misordered, &d, Some(&claim), aspis_prover::HOST_HASH).is_err());
}

#[test]
fn false_claim_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 42);
    let d = digest(0);
    let mut lying_claim = honest_claim(&coeffs, 7);
    lying_claim.v = lying_claim.v.add(aspis_core::field::QM31::ONE);
    let proof = prove_with_claim(
        &PROFILE,
        &coeffs,
        &d,
        &lying_claim,
        &options(),
        aspis_prover::HOST_HASH,
    );
    assert_eq!(
        verify_with_claim(&proof, &d, Some(&lying_claim), aspis_prover::HOST_HASH),
        Err(VerifyError::SumcheckBoundaryMismatch { layer: 0 })
    );
}
