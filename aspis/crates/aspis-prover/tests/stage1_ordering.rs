//! Teeth-first Fiat-Shamir ordering vectors.
//!
//! Every adversarial proof is rejected by the production verifier. With the
//! explicit `insecure-test-ordering` feature, the same bytes are accepted by
//! a verifier that deliberately reproduces the corresponding old/broken
//! schedule. That second assertion proves the vector reaches the intended
//! class of bug instead of merely producing malformed bytes.

use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
use aspis_core::{verify, verify_with_claim, EvaluationClaim};
#[cfg(feature = "insecure-test-ordering")]
use aspis_core::{verify_with_insecure_ordering, InsecureOrdering};
use aspis_prover::{
    multilinear_eval, prove_with_chi_before_c1_for_tests, prove_with_gamma_before_claims_for_tests,
    prove_with_misordered_ood_for_tests, seeded_coeffs, ProveOptions, HOST_HASH,
};

fn digest(tag: u8) -> [u8; 32] {
    use sha2::Digest;
    let mut hasher = sha2::Sha256::new();
    hasher.update(b"aspis-stage1-ordering-teeth");
    hasher.update([tag]);
    hasher.finalize().into()
}

fn options() -> ProveOptions {
    ProveOptions {
        fold_payload: aspis_core::FoldPayload::RawFibers,
        merkle_mode: aspis_core::MerkleMode::MinimalSubtree,
    }
}

fn honest_claim(coeffs: &[aspis_core::field::M31]) -> EvaluationClaim {
    let z = (0..PROFILE.log_rows)
        .map(|index| {
            aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                aspis_core::field::M31(17 + 19 * index),
            ))
        })
        .collect::<Vec<_>>();
    let v = multilinear_eval(coeffs, &z);
    EvaluationClaim { z, v }
}

#[test]
fn chi_before_c1_rejects_canonically() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 101);
    let statement = digest(1);
    let proof =
        prove_with_chi_before_c1_for_tests(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    assert!(verify(&proof, &statement, HOST_HASH).is_err());

    #[cfg(feature = "insecure-test-ordering")]
    assert_eq!(
        verify_with_insecure_ordering(
            &proof,
            &statement,
            None,
            HOST_HASH,
            InsecureOrdering::ChiBeforeC1,
        ),
        Ok(())
    );
}

#[test]
fn gamma_before_claimed_evaluations_rejects_canonically() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 102);
    let statement = digest(2);
    let claim = honest_claim(&coeffs);
    let proof = prove_with_gamma_before_claims_for_tests(
        &PROFILE,
        &coeffs,
        &statement,
        &claim,
        &options(),
        HOST_HASH,
    );
    assert!(verify_with_claim(&proof, &statement, Some(&claim), HOST_HASH).is_err());

    #[cfg(feature = "insecure-test-ordering")]
    assert_eq!(
        verify_with_insecure_ordering(
            &proof,
            &statement,
            Some(&claim),
            HOST_HASH,
            InsecureOrdering::GammaBeforeClaims,
        ),
        Ok(())
    );
}

#[test]
fn ood_claim_after_fold_challenge_rejects_canonically() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 103);
    let statement = digest(3);
    let proof =
        prove_with_misordered_ood_for_tests(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    assert!(verify(&proof, &statement, HOST_HASH).is_err());

    #[cfg(feature = "insecure-test-ordering")]
    assert_eq!(
        verify_with_insecure_ordering(
            &proof,
            &statement,
            None,
            HOST_HASH,
            InsecureOrdering::OodAfterFoldChallenge,
        ),
        Ok(())
    );
}
