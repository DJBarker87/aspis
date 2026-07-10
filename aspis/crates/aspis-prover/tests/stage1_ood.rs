//! Stage 1 queue item 3: per-round out-of-domain point/value binding.
//!
//! These tests establish the version-2 envelope and canonical order
//! `root -> OOD point -> OOD value -> alpha`, including corruption and
//! order-attack rejection. The interleaved relation sumcheck enforces every
//! claimed OOD evaluation against the explicit final polynomial.

use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
use aspis_core::proof::{HEADER_LEN, OOD_VALUE_LEN, ROOT_LEN, VERSION};
use aspis_core::{verify, VerifyError};
use aspis_prover::{
    prove, prove_with_lying_ood_for_tests, prove_with_misordered_ood_for_tests, seeded_coeffs,
    ProveOptions, HOST_HASH,
};

fn digest(seed: u64) -> [u8; 32] {
    use sha2::Digest;
    let mut h = sha2::Sha256::new();
    h.update(b"aspis-stage1-ood-test");
    h.update(seed.to_le_bytes());
    h.finalize().into()
}

fn options() -> ProveOptions {
    ProveOptions {
        fold_payload: aspis_core::FoldPayload::RawFibers,
        merkle_mode: aspis_core::MerkleMode::MinimalSubtree,
    }
}

#[test]
fn ood_roundtrip_accepts() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 41);
    let statement = digest(1);
    let proof = prove(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    assert_eq!(proof[4], VERSION);
    assert_eq!(verify(&proof, &statement, HOST_HASH), Ok(()));
}

#[test]
fn ood_value_corruption_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 42);
    let statement = digest(2);
    let mut proof = prove(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    // First round record is root[32] || ood_value[16]. A canonical low-byte
    // perturbation changes every later challenge and must reject.
    proof[HEADER_LEN + ROOT_LEN] ^= 1;
    assert!(verify(&proof, &statement, HOST_HASH).is_err());
}

#[test]
fn sumcheck_polynomial_corruption_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 420);
    let statement = digest(20);
    let mut proof = prove(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    let sumcheck_offset = HEADER_LEN + ROOT_LEN + OOD_VALUE_LEN;
    proof[sumcheck_offset] ^= 1;
    assert!(matches!(
        verify(&proof, &statement, HOST_HASH),
        Err(VerifyError::SumcheckBoundaryMismatch { layer: 0 })
            | Err(VerifyError::EvaluationRelationMismatch)
    ));
}

#[test]
fn ood_challenge_order_attack_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 43);
    let statement = digest(3);
    let proof =
        prove_with_misordered_ood_for_tests(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    assert!(verify(&proof, &statement, HOST_HASH).is_err());
}

#[test]
fn pre_v3_envelope_version_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 44);
    let statement = digest(4);
    let mut proof = prove(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    proof[4] = 2;
    assert_eq!(
        verify(&proof, &statement, HOST_HASH),
        Err(VerifyError::BadHeader)
    );
}

#[test]
fn false_ood_evaluation_rejects() {
    // The dishonest prover supplies f_r(beta_r)+1 in round 1 and absorbs the
    // lie in the correct transcript position. The relation sumcheck catches
    // it at that round's boundary.
    let coeffs = seeded_coeffs(PROFILE.log_rows, 45);
    let statement = digest(5);
    let proof =
        prove_with_lying_ood_for_tests(&PROFILE, &coeffs, &statement, 1, &options(), HOST_HASH);
    assert_eq!(
        verify(&proof, &statement, HOST_HASH),
        Err(VerifyError::SumcheckBoundaryMismatch { layer: 1 })
    );
}
