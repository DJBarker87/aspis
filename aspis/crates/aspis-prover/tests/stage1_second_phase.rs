//! Stage 1 C2 envelope, authentication, and gamma-RLC checks.

use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
use aspis_core::proof::{
    Header, FLAG_EVALUATION_CLAIM, FLAG_SECOND_PHASE, HEADER_LEN, ROOT_LEN,
    SECOND_PHASE_LEAF_LEN_V3,
};
use aspis_core::{verify, verify_with_claim, EvaluationClaim};
use aspis_prover::{
    multilinear_eval, prove_with_claim, prove_with_second_phase_builder,
    prove_with_synthetic_second_phase, seeded_coeffs, ProveOptions, HOST_HASH,
};

fn digest(tag: u8) -> [u8; 32] {
    use sha2::Digest;
    let mut hasher = sha2::Sha256::new();
    hasher.update(b"aspis-stage1-second-phase");
    hasher.update([tag]);
    hasher.finalize().into()
}

#[test]
fn generic_second_phase_builder_roundtrip_accepts() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 204);
    let statement = digest(4);
    let proof = prove_with_second_phase_builder(
        &PROFILE,
        &coeffs,
        &statement,
        None,
        &options(),
        HOST_HASH,
        |main, lambda, chi| {
            main.iter()
                .map(|coefficient| {
                    let lifted = aspis_core::field::QM31::from_cm31(
                        aspis_core::field::CM31::from_m31(*coefficient),
                    );
                    lifted.mul(lambda).add(chi)
                })
                .collect()
        },
    );
    assert_eq!(verify(&proof, &statement, HOST_HASH), Ok(()));
}

fn options() -> ProveOptions {
    ProveOptions {
        fold_payload: aspis_core::FoldPayload::RawFibers,
        merkle_mode: aspis_core::MerkleMode::MinimalSubtree,
    }
}

fn claim(coeffs: &[aspis_core::field::M31]) -> EvaluationClaim {
    let z = (0..PROFILE.log_rows)
        .map(|index| {
            aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                aspis_core::field::M31(5 + 7 * index),
            ))
        })
        .collect::<Vec<_>>();
    EvaluationClaim {
        v: multilinear_eval(coeffs, &z),
        z,
    }
}

#[test]
fn second_phase_roundtrip_accepts() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 201);
    let statement = digest(1);
    let proof =
        prove_with_synthetic_second_phase(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    assert_eq!(proof[15], FLAG_SECOND_PHASE);
    let header = Header::parse(&proof).unwrap();
    assert_eq!(header.second_phase_helper_count(), 1);
    assert_eq!(header.second_phase_leaf_len(), SECOND_PHASE_LEAF_LEN_V3);
    assert_eq!(verify(&proof, &statement, HOST_HASH), Ok(()));
}

#[test]
fn second_phase_root_corruption_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 202);
    let statement = digest(2);
    let mut proof =
        prove_with_synthetic_second_phase(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    proof[HEADER_LEN + ROOT_LEN + 3] ^= 1;
    assert!(verify(&proof, &statement, HOST_HASH).is_err());
}

#[test]
fn second_phase_claim_corruption_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 203);
    let statement = digest(3);
    let claim = claim(&coeffs);
    let mut proof = prove_with_claim(&PROFILE, &coeffs, &statement, &claim, &options(), HOST_HASH);
    assert_eq!(proof[15], FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE);
    let header = Header::parse(&proof).unwrap();
    assert_eq!(header.second_phase_claim_count(), 1);
    assert_eq!(header.second_phase_claims_len(), 16);
    proof[HEADER_LEN + 2 * ROOT_LEN] ^= 1;
    assert!(verify_with_claim(&proof, &statement, Some(&claim), HOST_HASH).is_err());
}
