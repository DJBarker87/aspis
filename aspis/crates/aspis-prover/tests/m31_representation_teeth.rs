//! Host-only paired acceptance/rejection teeth for the M31 circle candidate.
//!
//! Each adversarial vector is accepted by one deliberately weakened test
//! validator and rejected by the canonical representation validator. These
//! helpers are integration-test modules only: no production or SBF feature is
//! introduced here.

#[path = "support/m31_representation_teeth_reference.rs"]
mod teeth;

use aspis_core::field::{M31, M31_QUARTER, QM31};
use aspis_prover::multilinear_eval;
use aspis_statement::{
    build_spend_trace_v4, derive_nullifier, derive_owner_key, merkle_root, note_commitment,
    output_commitment, Digest, MerklePath, SpendPublic, SpendTraceV4, SpendWitness,
};
use teeth::{circle, line_fri, q, Rng};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + index as u32 * 17))
}

fn spend_trace() -> SpendTraceV4 {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let fee = 1;
    let owner_key = derive_owner_key(&nullifier_key);
    let note = note_commitment(&owner_key, value, asset_id, &input_salt);
    let path = MerklePath {
        siblings: (0..20)
            .map(|level| digest(1_000 + level as u32 * 31))
            .collect(),
        index: 0x5a5a5,
    };
    let public = SpendPublic {
        anchor: merkle_root(note, &path).unwrap(),
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output_commitment(&output_owner_key, value_out, asset_id, &output_salt),
        asset_id,
        fee,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path: path,
    };
    build_spend_trace_v4(&public, &witness).unwrap()
}

fn bit_reversed<T: Copy>(values: &[T]) -> Vec<T> {
    let mut values = values.to_vec();
    line_fri::bit_reverse(&mut values);
    values
}

#[test]
fn air_ifft_reinterpretation_accepts_weakened_and_rejects_direct_message() {
    let trace = spend_trace();
    let message = &trace.c1[0];
    assert_eq!(message.len(), 1 << circle::TRACE_LOG_SIZE);

    let air_coefficients = teeth::inverse_circle_codeword(message, circle::TRACE_LOG_SIZE);
    assert_eq!(
        circle::encode_circle(&air_coefficients, circle::TRACE_LOG_SIZE),
        *message,
        "test-only AIR IFFT must invert the pinned encoder"
    );

    let adversarial = teeth::weakened_air_ifft_digest(message, circle::DOMAIN_LOG_SIZE);
    assert!(teeth::weakened_air_ifft_accepts(
        message,
        circle::DOMAIN_LOG_SIZE,
        adversarial,
    ));
    assert!(!teeth::canonical_direct_message_accepts(
        message,
        circle::DOMAIN_LOG_SIZE,
        adversarial,
    ));

    let point = (0..circle::TRACE_LOG_SIZE)
        .map(|coordinate| {
            q([
                11 + coordinate,
                37 + 3 * coordinate,
                71 + 5 * coordinate,
                109 + 7 * coordinate,
            ])
        })
        .collect::<Vec<_>>();
    assert_ne!(
        multilinear_eval(message, &point),
        multilinear_eval(&air_coefficients, &point),
        "the wrong AIR-IFFT root must also bind a different MLE message"
    );
}

#[test]
fn mle_endian_and_basis_reversal_one_hot_family_has_teeth() {
    let point = [
        q([3, 5, 7, 11]),
        q([13, 17, 19, 23]),
        q([29, 31, 37, 41]),
        q([43, 47, 53, 59]),
    ];
    let mut messages = Vec::new();
    for hot in [1usize, 2, 4, 7, 8, 13] {
        let mut one_hot = vec![M31::ZERO; 16];
        one_hot[hot] = M31((hot as u32) + 2);
        messages.push(one_hot);
    }
    messages.push(
        (0..16)
            .map(|index| M31((index * index * 19 + index * 7 + 3) as u32))
            .collect(),
    );

    for message in messages {
        let adversarial = multilinear_eval(&teeth::bit_reversed_message(&message), &point);
        assert!(teeth::weakened_reversed_mle_accepts(
            &message,
            &point,
            adversarial,
        ));
        assert!(!teeth::canonical_mle_accepts(&message, &point, adversarial,));
    }
}

#[test]
fn circle_consecutive_and_legacy_strided_slot_order_has_teeth() {
    let mut rng = Rng(0x4349_5243_4c45_534c);
    let coefficients = (0..1usize << circle::TRACE_LOG_SIZE)
        .map(|_| rng.m31())
        .collect::<Vec<_>>();
    let codeword = circle::encode_circle(&coefficients, circle::DOMAIN_LOG_SIZE);

    for fiber in [0usize, 1, 137, 511, 1_023] {
        let strided = teeth::weakened_strided_circle_slots(&codeword, fiber);
        assert!(teeth::weakened_strided_circle_slots_accepts(
            &codeword, fiber, strided,
        ));
        assert!(!teeth::canonical_circle_slots_accepts(
            &codeword, fiber, strided,
        ));

        let middle_swap = teeth::weakened_middle_slot_swap(&codeword, fiber);
        assert!(teeth::weakened_middle_slot_swap_accepts(
            &codeword,
            fiber,
            middle_swap,
        ));
        assert!(!teeth::canonical_circle_slots_accepts(
            &codeword,
            fiber,
            middle_swap,
        ));
    }
}

#[test]
fn alpha_squared_second_fold_has_circle_and_later_line_teeth() {
    let fixed_values = [
        q([2, 3, 5, 7]),
        q([11, 13, 17, 19]),
        q([23, 29, 31, 37]),
        q([41, 43, 47, 53]),
    ];
    let fixed_point = circle::bit_reversed_domain_point(548, circle::DOMAIN_LOG_SIZE);
    for boundary in [QM31::ZERO, QM31::ONE] {
        assert_eq!(
            circle::normalized_fold4(fixed_values, boundary, fixed_point.x, fixed_point.y),
            teeth::fold_circle_with_second_challenge(
                fixed_values,
                boundary,
                boundary,
                fixed_point.x,
                fixed_point.y,
            ),
            "alpha and alpha^2 coincide at boundary challenge {boundary:?}"
        );
    }

    let mut rng = Rng(0x414c_5048_4132_5445);
    let line_domain = line_fri::LineDomain::half_odds(4);
    for case in 0..24usize {
        let values = core::array::from_fn(|_| rng.qm31());
        let point = circle::bit_reversed_domain_point(
            (case * 4) % (1usize << circle::DOMAIN_LOG_SIZE),
            circle::DOMAIN_LOG_SIZE,
        );
        let mut alpha = rng.qm31();
        if alpha == QM31::ZERO || alpha == QM31::ONE {
            alpha = q([101, 307, 401, 809]);
        }
        let adversarial =
            teeth::fold_circle_with_second_challenge(values, alpha, alpha, point.x, point.y);
        assert!(teeth::weakened_circle_alpha_reuse_accepts(
            values,
            alpha,
            point.x,
            point.y,
            adversarial,
        ));
        assert!(!teeth::canonical_circle_alpha2_accepts(
            values,
            alpha,
            point.x,
            point.y,
            adversarial,
        ));

        let natural = (0..line_domain.size())
            .map(|_| rng.qm31())
            .collect::<Vec<_>>();
        let evaluations = line_fri::evaluate_on_domain(&bit_reversed(&natural), line_domain);
        let line_adversarial = teeth::weakened_line_alpha_reuse(&evaluations, line_domain, alpha).1;
        assert!(teeth::weakened_line_alpha_reuse_accepts(
            &evaluations,
            line_domain,
            alpha,
            &line_adversarial,
        ));
        assert!(!teeth::canonical_line_alpha2_accepts(
            &evaluations,
            line_domain,
            alpha,
            &line_adversarial,
        ));
    }
}

#[test]
fn raw_stwo_factor_four_is_rejected_by_normalized_validator() {
    let mut rng = Rng(0x4641_4354_4f52_3454);
    let domain = line_fri::LineDomain::half_odds(4);
    for case in 0..24usize {
        let natural = (0..domain.size()).map(|_| rng.qm31()).collect::<Vec<_>>();
        let evaluations = line_fri::evaluate_on_domain(&bit_reversed(&natural), domain);
        let alpha = match case {
            0 => QM31::ZERO,
            1 => QM31::ONE,
            _ => rng.qm31(),
        };
        let raw = line_fri::fold_line_arity4(&evaluations, domain, alpha).1;
        let normalized = teeth::normalized_line_fold(&evaluations, domain, alpha);
        assert_eq!(line_fri::scale(&normalized, M31(4)), raw);
        assert!(teeth::weakened_raw_line_accepts(
            &evaluations,
            domain,
            alpha,
            &raw,
        ));
        assert!(!teeth::canonical_normalized_line_accepts(
            &evaluations,
            domain,
            alpha,
            &raw,
        ));
        assert_eq!(
            line_fri::scale(&raw, M31_QUARTER),
            normalized,
            "normalization must divide both binary inverse butterflies"
        );
    }
}

#[test]
fn ood_factor_order_and_retained_y_have_two_sample_teeth() {
    let mut rng = Rng(0x4f4f_4446_4143_544f);
    for case in 0..16usize {
        let coefficients = (0..16).map(|_| rng.qm31()).collect::<Vec<_>>();
        for sample in 0..2usize {
            let parameter = rng.qm31().add(q([
                17 + case as u32,
                31 + sample as u32,
                47 + case as u32 * 3,
                71 + sample as u32 * 5,
            ]));
            let point = circle::secure_circle_point(parameter);

            let swapped = teeth::weakened_swapped_ood_factors(&coefficients, point);
            assert!(teeth::weakened_swapped_ood_accepts(
                &coefficients,
                point,
                swapped,
            ));
            assert!(!teeth::canonical_circle_ood_accepts(
                &coefficients,
                point,
                swapped,
            ));

            let retained_y = teeth::weakened_retained_y_ood(&coefficients, point);
            assert!(teeth::weakened_retained_y_ood_accepts(
                &coefficients,
                point,
                retained_y,
            ));
            assert!(!teeth::canonical_circle_ood_accepts(
                &coefficients,
                point,
                retained_y,
            ));
        }
    }
}

#[test]
fn later_folded_storage_requires_one_bitreverse_bridge() {
    let mut rng = Rng(0x4252_4944_4745_5445);
    let domain = line_fri::LineDomain::half_odds(4);
    for case in 0..24usize {
        let natural = (0..domain.size()).map(|_| rng.qm31()).collect::<Vec<_>>();
        let alpha = match case {
            0 => QM31::ZERO,
            1 => QM31::ONE,
            _ => rng.qm31(),
        };
        let adversarial = teeth::weakened_unbridged_next_codeword(&natural, domain, alpha);
        assert!(teeth::weakened_unbridged_storage_accepts(
            &natural,
            domain,
            alpha,
            &adversarial,
        ));
        assert!(!teeth::canonical_storage_bridge_accepts(
            &natural,
            domain,
            alpha,
            &adversarial,
        ));

        // Cross-check the canonical bridge against normalized official raw
        // line folds, so this is a storage-order tooth rather than an
        // unrelated encoder comparison.
        let source = line_fri::evaluate_on_domain(&bit_reversed(&natural), domain);
        let raw = line_fri::fold_line_arity4(&source, domain, alpha).1;
        assert_eq!(
            line_fri::scale(&raw, M31_QUARTER),
            teeth::canonical_next_storage_codeword(&natural, domain, alpha),
        );
    }
}

#[test]
fn final_natural_serialization_and_storage_copy_have_teeth() {
    let mut rng = Rng(0x4649_4e41_4c42_4153);
    for _ in 0..32 {
        let natural = (0..4).map(|_| rng.qm31()).collect::<Vec<_>>();
        let weights = (0..4).map(|_| rng.qm31()).collect::<Vec<_>>();
        let query_x = rng.qm31();
        let adversarial = teeth::weakened_storage_final_candidate(&natural, &weights, query_x);
        assert!(teeth::weakened_storage_final_accepts(
            &natural,
            &weights,
            query_x,
            &adversarial,
        ));
        assert!(!teeth::canonical_final_accepts(
            &natural,
            &weights,
            query_x,
            &adversarial,
        ));

        let canonical = teeth::canonical_final_candidate(&natural, &weights, query_x);
        assert!(teeth::canonical_final_accepts(
            &natural, &weights, query_x, &canonical,
        ));
        assert!(!teeth::weakened_storage_final_accepts(
            &natural, &weights, query_x, &canonical,
        ));
    }
}
