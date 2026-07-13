//! Backward-compatible v4/s=2 envelope and challenge-order coverage.

use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
use aspis_core::proof::{
    first_layer_first_phase_opening_offset, first_layer_second_phase_helper_offset,
    first_layer_second_phase_opening_offset, ood_value_offset, second_phase_claim_offset,
    transcript_records_len, transcript_records_len_for_version, Header, EXACT_WIDE_C1_FIBER_LEN,
    HEADER_LEN, OOD_VALUE_LEN, SECOND_PHASE_LEAF_LEN_V4_S2, VERSION, VERSION_V4_S2,
};
#[cfg(feature = "insecure-test-framing")]
use aspis_core::proof::{FLAG_M31_CIRCLE_C1_DIAGNOSTIC, M31_CIRCLE_C1_FIBER_LEN};
#[cfg(feature = "insecure-test-framing")]
use aspis_core::verify_with_insecure_m31_circle_as_legacy_for_tests;
use aspis_core::{verify, verify_with_claim, EvaluationClaim, VerifyError};
#[cfg(feature = "insecure-test-ordering")]
use aspis_core::{verify_with_insecure_ordering, InsecureOrdering};
#[cfg(feature = "insecure-test-framing")]
use aspis_prover::prove_with_claim_v4_m31_circle_flag_legacy_basis_for_tests;
use aspis_prover::{
    multilinear_eval, prove, prove_exact_wide_v4_scaffold_for_measurement, prove_v4,
    prove_v4_with_gamma_before_second_helper_claim_for_tests,
    prove_v4_with_misordered_second_ood_for_tests, prove_with_claim_v4,
    prove_with_second_phase_builder_v4, prove_with_synthetic_second_phase_v4, seeded_coeffs,
    ProveOptions, HOST_HASH,
};

fn digest(tag: u8) -> [u8; 32] {
    use sha2::Digest;
    let mut hasher = sha2::Sha256::new();
    hasher.update(b"aspis-stage1-v4-s2");
    hasher.update([tag]);
    hasher.finalize().into()
}

fn options() -> ProveOptions {
    ProveOptions {
        fold_payload: aspis_core::FoldPayload::RawFibers,
        // Exercise the simplest opening parser; record-size assertions below
        // isolate the transcript section because changed challenges may also
        // change the number of unique queried fibers.
        merkle_mode: aspis_core::MerkleMode::SinglePaths,
    }
}

fn claim(coeffs: &[aspis_core::field::M31]) -> EvaluationClaim {
    let z = (0..PROFILE.log_rows)
        .map(|index| {
            aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                aspis_core::field::M31(31 + 13 * index),
            ))
        })
        .collect::<Vec<_>>();
    EvaluationClaim {
        v: multilinear_eval(coeffs, &z),
        z,
    }
}

#[test]
fn v3_remains_valid_and_v4_adds_exactly_one_value_per_round() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 401);
    let statement = digest(1);
    let v3 = prove(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    let v4 = prove_v4(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);

    assert_eq!(v3[4], VERSION);
    assert_eq!(v4[4], VERSION_V4_S2);
    assert_eq!(verify(&v3, &statement, HOST_HASH), Ok(()));
    assert_eq!(verify(&v4, &statement, HOST_HASH), Ok(()));
    let v3_header = Header::parse(&v3).unwrap();
    let v4_header = Header::parse(&v4).unwrap();
    assert_eq!(v3_header.ood_samples_per_round(), 1);
    assert_eq!(v4_header.ood_samples_per_round(), 2);
    assert_eq!(v3_header.second_phase_helper_count(), 0);
    assert_eq!(v3_header.second_phase_leaf_len(), 0);
    assert_eq!(v4_header.second_phase_helper_count(), 0);
    assert_eq!(v4_header.second_phase_leaf_len(), 0);
    assert_eq!(
        transcript_records_len_for_version(
            PROFILE.num_rounds() as usize,
            v3_header.flags,
            v3_header.version,
        ),
        Some(transcript_records_len(
            PROFILE.num_rounds() as usize,
            v3_header.flags,
        ))
    );
    let v3_records = transcript_records_len_for_version(
        PROFILE.num_rounds() as usize,
        v3_header.flags,
        v3_header.version,
    )
    .unwrap();
    let v4_records = transcript_records_len_for_version(
        PROFILE.num_rounds() as usize,
        v4_header.flags,
        v4_header.version,
    )
    .unwrap();
    assert_eq!(
        v4_records - v3_records,
        PROFILE.num_rounds() as usize * OOD_VALUE_LEN
    );
}

#[test]
fn corrupting_either_v4_ood_value_rejects() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 402);
    let statement = digest(2);
    let proof = prove_v4(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    let header = Header::parse(&proof).unwrap();

    for layer in 0..header.num_rounds as usize {
        for sample in 0..header.ood_samples_per_round() {
            let mut corrupted = proof.clone();
            let offset = ood_value_offset(&header, layer, sample).unwrap();
            corrupted[offset] ^= 1;
            assert!(
                verify(&corrupted, &statement, HOST_HASH).is_err(),
                "round-{layer} OOD sample {sample} corruption accepted"
            );
        }
    }
}

#[test]
fn v4_two_phase_and_claim_apis_roundtrip() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 403);
    let statement = digest(3);

    let synthetic =
        prove_with_synthetic_second_phase_v4(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    assert_eq!(verify(&synthetic, &statement, HOST_HASH), Ok(()));
    let synthetic_header = Header::parse(&synthetic).unwrap();
    assert!(synthetic_header.has_second_phase());
    assert_eq!(synthetic_header.second_phase_helper_count(), 2);
    assert_eq!(
        synthetic_header.second_phase_leaf_len(),
        SECOND_PHASE_LEAF_LEN_V4_S2
    );
    assert!(ood_value_offset(&synthetic_header, 0, 1).is_some());
    for sample in 0..synthetic_header.ood_samples_per_round() {
        let mut corrupted = synthetic.clone();
        corrupted[ood_value_offset(&synthetic_header, 0, sample).unwrap()] ^= 1;
        assert!(verify(&corrupted, &statement, HOST_HASH).is_err());
    }
    for helper_half in 0..synthetic_header.second_phase_helper_count() {
        let mut corrupted = synthetic.clone();
        corrupted[first_layer_second_phase_helper_offset(&synthetic, helper_half).unwrap()] ^= 1;
        assert!(
            verify(&corrupted, &statement, HOST_HASH).is_err(),
            "C2 helper half {helper_half} corruption accepted"
        );
    }

    let claim = claim(&coeffs);
    let claimed = prove_with_claim_v4(&PROFILE, &coeffs, &statement, &claim, &options(), HOST_HASH);
    assert_eq!(
        verify_with_claim(&claimed, &statement, Some(&claim), HOST_HASH),
        Ok(())
    );
    let claimed_header = Header::parse(&claimed).unwrap();
    assert_eq!(claimed_header.second_phase_claim_count(), 2);
    assert_eq!(claimed_header.second_phase_claims_len(), 2 * OOD_VALUE_LEN);
    for helper_claim in 0..claimed_header.second_phase_claim_count() {
        let mut corrupted = claimed.clone();
        corrupted[second_phase_claim_offset(&claimed_header, helper_claim).unwrap()] ^= 1;
        assert!(
            verify_with_claim(&corrupted, &statement, Some(&claim), HOST_HASH).is_err(),
            "C2 helper claim {helper_claim} corruption accepted"
        );
    }

    let generic = prove_with_second_phase_builder_v4(
        &PROFILE,
        &coeffs,
        &statement,
        None,
        &options(),
        HOST_HASH,
        |main, lambda, chi| {
            let helper_1 = main
                .iter()
                .map(|coefficient| {
                    let lifted = aspis_core::field::QM31::from_cm31(
                        aspis_core::field::CM31::from_m31(*coefficient),
                    );
                    lifted.mul(lambda).add(chi)
                })
                .collect();
            let helper_2 = main
                .iter()
                .map(|coefficient| {
                    let lifted = aspis_core::field::QM31::from_cm31(
                        aspis_core::field::CM31::from_m31(*coefficient),
                    );
                    lifted.mul(chi).add(lambda)
                })
                .collect();
            (helper_1, helper_2)
        },
    );
    assert_eq!(verify(&generic, &statement, HOST_HASH), Ok(()));
}

#[test]
fn exact_wide_scaffold_is_diagnostic_only_and_has_c1_c2_teeth() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 407);
    let statement = digest(7);
    let claim = claim(&coeffs);
    let proof = prove_exact_wide_v4_scaffold_for_measurement(
        &PROFILE,
        &coeffs,
        &statement,
        &claim,
        &options(),
        HOST_HASH,
    );
    let header = Header::parse(&proof).expect("exact-wide header");
    assert!(header.has_exact_wide_c1());
    assert_eq!(header.first_phase_leaf_len(0), EXACT_WIDE_C1_FIBER_LEN);

    // This flag is intentionally unavailable through production verification
    // until the final two-point/102-value semantics exist.
    assert_eq!(
        verify_with_claim(&proof, &statement, Some(&claim), HOST_HASH),
        Err(VerifyError::BadHeader)
    );
    assert_eq!(
        aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            &proof,
            &statement,
            Some(&claim),
            HOST_HASH,
        ),
        Ok(())
    );

    let c1_start = first_layer_first_phase_opening_offset(&proof).expect("first C1 opening");
    let c2_start = first_layer_second_phase_opening_offset(&proof).expect("first C2 opening");

    let mut c1_changed = proof.clone();
    let limb = u32::from_le_bytes(c1_changed[c1_start..c1_start + 4].try_into().unwrap());
    c1_changed[c1_start..c1_start + 4].copy_from_slice(
        &if limb + 1 == aspis_core::field::P {
            0
        } else {
            limb + 1
        }
        .to_le_bytes(),
    );
    assert!(
        aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            &c1_changed,
            &statement,
            Some(&claim),
            HOST_HASH,
        )
        .is_err()
    );

    let mut c1_noncanonical = proof.clone();
    c1_noncanonical[c1_start..c1_start + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
    assert_eq!(
        aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            &c1_noncanonical,
            &statement,
            Some(&claim),
            HOST_HASH,
        ),
        Err(VerifyError::NonCanonicalValue)
    );

    let mut c2_changed = proof.clone();
    let limb = u32::from_le_bytes(c2_changed[c2_start..c2_start + 4].try_into().unwrap());
    c2_changed[c2_start..c2_start + 4].copy_from_slice(
        &if limb + 1 == aspis_core::field::P {
            0
        } else {
            limb + 1
        }
        .to_le_bytes(),
    );
    assert!(
        aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            &c2_changed,
            &statement,
            Some(&claim),
            HOST_HASH,
        )
        .is_err()
    );

    let mut c2_noncanonical = proof.clone();
    c2_noncanonical[c2_start..c2_start + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
    assert_eq!(
        aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            &c2_noncanonical,
            &statement,
            Some(&claim),
            HOST_HASH,
        ),
        Err(VerifyError::NonCanonicalValue)
    );
}

#[test]
fn v4_second_ood_ordering_vector_has_teeth() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 404);
    let statement = digest(4);
    let proof = prove_v4_with_misordered_second_ood_for_tests(
        &PROFILE,
        &coeffs,
        &statement,
        &options(),
        HOST_HASH,
    );
    assert!(verify(&proof, &statement, HOST_HASH).is_err());

    #[cfg(feature = "insecure-test-ordering")]
    assert_eq!(
        verify_with_insecure_ordering(
            &proof,
            &statement,
            None,
            HOST_HASH,
            InsecureOrdering::SecondOodAfterFoldChallenge,
        ),
        Ok(())
    );
}

#[test]
fn v4_second_helper_claim_must_precede_gamma_vector_has_teeth() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 406);
    let statement = digest(6);
    let claim = claim(&coeffs);
    let proof = prove_v4_with_gamma_before_second_helper_claim_for_tests(
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
            InsecureOrdering::GammaBeforeSecondHelperClaim,
        ),
        Ok(())
    );
}

#[test]
fn v4_version_framing_and_trailing_bytes_reject() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 405);
    let statement = digest(5);
    let proof = prove_v4(&PROFILE, &coeffs, &statement, &options(), HOST_HASH);
    let header = Header::parse(&proof).unwrap();

    let mut trailing = proof.clone();
    trailing.push(0);
    assert_eq!(
        verify(&trailing, &statement, HOST_HASH),
        Err(VerifyError::TrailingBytes)
    );

    let mut unsupported = proof.clone();
    unsupported[4] = VERSION_V4_S2 + 1;
    assert_eq!(
        verify(&unsupported, &statement, HOST_HASH),
        Err(VerifyError::BadHeader)
    );

    let mut relabeled_v3 = proof.clone();
    relabeled_v3[4] = VERSION;
    assert!(verify(&relabeled_v3, &statement, HOST_HASH).is_err());

    let second_offset = ood_value_offset(&header, 0, 1).unwrap();
    let mut missing_second = proof.clone();
    missing_second.drain(second_offset..second_offset + OOD_VALUE_LEN);
    assert!(verify(&missing_second, &statement, HOST_HASH).is_err());

    let mut truncated = proof;
    truncated.truncate(HEADER_LEN - 1);
    assert_eq!(
        verify(&truncated, &statement, HOST_HASH),
        Err(VerifyError::BadHeader)
    );
}

#[cfg(not(feature = "insecure-test-framing"))]
#[test]
fn m31_circle_flag_is_rejected_when_test_framing_feature_is_absent() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 409);
    let statement = digest(9);
    let claim = claim(&coeffs);
    let mut proof =
        prove_with_claim_v4(&PROFILE, &coeffs, &statement, &claim, &options(), HOST_HASH);
    proof[15] |= aspis_core::proof::FLAG_M31_CIRCLE_C1_DIAGNOSTIC;
    let header = Header::parse(&proof).expect("recognized diagnostic flag frame");
    assert!(header.has_m31_circle_c1_diagnostic());

    // This test is compiled and run in the ordinary feature-absent suite.
    // The proof's transcript is intentionally stale, but BadHeader proves
    // rejection occurs at the basis allow-list before transcript validation.
    assert_eq!(
        verify_with_claim(&proof, &statement, Some(&claim), HOST_HASH),
        Err(VerifyError::BadHeader)
    );
}

#[cfg(feature = "insecure-test-framing")]
#[test]
fn m31_circle_basis_flag_misclassification_vector_has_teeth() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 408);
    let statement = digest(8);
    let claim = claim(&coeffs);
    let proof = prove_with_claim_v4_m31_circle_flag_legacy_basis_for_tests(
        &PROFILE,
        &coeffs,
        &statement,
        &claim,
        &ProveOptions {
            fold_payload: aspis_core::FoldPayload::RawFibers,
            merkle_mode: aspis_core::MerkleMode::Radix4MinimalSubtree,
        },
        HOST_HASH,
    );
    let header = Header::parse(&proof).expect("recognized diagnostic framing");
    assert_eq!(header.version, VERSION_V4_S2);
    assert_eq!(
        header.flags & FLAG_M31_CIRCLE_C1_DIAGNOSTIC,
        FLAG_M31_CIRCLE_C1_DIAGNOSTIC
    );
    assert_eq!(header.first_phase_leaf_len(0), M31_CIRCLE_C1_FIBER_LEN);

    // Canonical production rejects before any basis-dependent work.
    assert_eq!(
        verify_with_claim(&proof, &statement, Some(&claim), HOST_HASH),
        Err(VerifyError::BadHeader)
    );

    // The deliberately weakened build interprets the very same flagged
    // bytes as the legacy scalar CM31 leaf shape and accepts. This is the
    // acceptance evidence that gives the production rejection test teeth.
    assert_eq!(
        verify_with_insecure_m31_circle_as_legacy_for_tests(
            &proof,
            &statement,
            Some(&claim),
            HOST_HASH,
        ),
        Ok(())
    );
}
