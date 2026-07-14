use aspis_core::circle::{double_x, secure_ood_circle_point_from_parameter, SecureCirclePoint};
use aspis_core::field::{CM31, M31, M31_QUARTER, QM31};
use aspis_prover::circle_relation::{
    build_circle_relation, build_circle_relation_with_zero_interval, validate_circle_relation,
    CircleRelationError, CircleRelationParameters, CircleRelationPointRule,
    CIRCLE_RELATION_FINAL_LEN, CIRCLE_RELATION_MESSAGE_LEN, CIRCLE_RELATION_ROUNDS,
};

fn q(seed: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(seed * 13 + 1), M31(seed * 17 + 3)),
        c1: CM31::new(M31(seed * 19 + 5), M31(seed * 23 + 7)),
    }
}

fn xor11(z: [QM31; 10]) -> [QM31; 10] {
    let mut second = z;
    for coordinate in &mut second[8..] {
        *coordinate = QM31::ONE.sub(*coordinate);
    }
    second
}

fn fixture_message() -> Vec<QM31> {
    (0..CIRCLE_RELATION_MESSAGE_LEN)
        .map(|index| q(100 + index as u32))
        .collect()
}

fn fixture_parameters(point_scales: [QM31; 2]) -> CircleRelationParameters {
    let z = core::array::from_fn(|coordinate| q(10 + coordinate as u32));
    let layer0_ood_points = [
        secure_ood_circle_point_from_parameter(q(41)).unwrap(),
        secure_ood_circle_point_from_parameter(q(43)).unwrap(),
    ];
    CircleRelationParameters {
        z,
        xor11_z: xor11(z),
        point_rule: CircleRelationPointRule::LegacyLowBits2,
        point_scales,
        layer0_ood_points,
        later_ood_x: [[q(51), q(53)], [q(61), q(67)], [q(71), q(73)]],
        ood_mixes: [
            [q(101), q(103)],
            [q(107), q(109)],
            [q(113), q(127)],
            [q(131), q(137)],
        ],
        alphas: [q(149), q(151), q(157), q(163)],
    }
}

fn multilinear_weights(point: &[QM31]) -> Vec<QM31> {
    (0..1usize << point.len())
        .map(|index| {
            point
                .iter()
                .enumerate()
                .fold(QM31::ONE, |weight, (coordinate, value)| {
                    let bit = (index >> (point.len() - 1 - coordinate)) & 1;
                    if bit == 0 {
                        weight.mul(QM31::ONE.sub(*value))
                    } else {
                        weight.mul(*value)
                    }
                })
        })
        .collect()
}

fn tensor_weights(factors: &[QM31]) -> Vec<QM31> {
    (0..1usize << factors.len())
        .map(|index| {
            factors
                .iter()
                .enumerate()
                .fold(QM31::ONE, |weight, (coordinate, factor)| {
                    let bit = (index >> (factors.len() - 1 - coordinate)) & 1;
                    if bit == 0 {
                        weight
                    } else {
                        weight.mul(*factor)
                    }
                })
        })
        .collect()
}

fn circle_tensor_weights(log_len: u32, point: SecureCirclePoint) -> Vec<QM31> {
    let mut factors = vec![point.y, point.x];
    let mut x = point.x;
    for _ in 2..log_len {
        x = double_x(x);
        factors.push(x);
    }
    factors.reverse();
    tensor_weights(&factors)
}

fn line_tensor_weights(log_len: u32, mut x: QM31) -> Vec<QM31> {
    let mut factors = Vec::with_capacity(log_len as usize);
    for _ in 0..log_len {
        factors.push(x);
        x = double_x(x);
    }
    factors.reverse();
    tensor_weights(&factors)
}

fn dot(values: &[QM31], weights: &[QM31]) -> QM31 {
    values
        .iter()
        .zip(weights)
        .fold(QM31::ZERO, |sum, (value, weight)| {
            sum.add(value.mul(*weight))
        })
}

fn manual_sumcheck(values: &[QM31], weights: &[QM31]) -> [QM31; 7] {
    let mut polynomial = [QM31::ZERO; 7];
    for (values, weights) in values.chunks_exact(4).zip(weights.chunks_exact(4)) {
        let dual = [weights[0], weights[3], weights[2], weights[1]];
        for (value_degree, value) in values.iter().enumerate() {
            for (weight_degree, weight) in dual.iter().enumerate() {
                polynomial[value_degree + weight_degree] = polynomial[value_degree + weight_degree]
                    .add(value.mul(*weight).mul_m31(M31_QUARTER));
            }
        }
    }
    polynomial
}

fn evaluate_polynomial(polynomial: &[QM31; 7], point: QM31) -> QM31 {
    polynomial
        .iter()
        .rev()
        .fold(QM31::ZERO, |value, coefficient| {
            value.mul(point).add(*coefficient)
        })
}

fn fold_coefficients(values: &[QM31], alpha: QM31) -> Vec<QM31> {
    let alpha_squared = alpha.square();
    let alpha_cubed = alpha_squared.mul(alpha);
    values
        .chunks_exact(4)
        .map(|chunk| {
            chunk[0]
                .add(alpha.mul(chunk[1]))
                .add(alpha_squared.mul(chunk[2]))
                .add(alpha_cubed.mul(chunk[3]))
        })
        .collect()
}

fn fold_weights(weights: &[QM31], alpha: QM31) -> Vec<QM31> {
    let alpha_squared = alpha.square();
    let alpha_cubed = alpha_squared.mul(alpha);
    weights
        .chunks_exact(4)
        .map(|chunk| {
            chunk[0]
                .add(alpha_cubed.mul(chunk[1]))
                .add(alpha_squared.mul(chunk[2]))
                .add(alpha.mul(chunk[3]))
                .mul_m31(M31_QUARTER)
        })
        .collect()
}

fn add_scaled(target: &mut [QM31], scale: QM31, source: &[QM31]) {
    for (target, source) in target.iter_mut().zip(source) {
        *target = target.add(scale.mul(*source));
    }
}

#[test]
fn two_explicit_scale_pairs_match_independent_materialization_through_terminal() {
    let message = fixture_message();
    let scale_pairs = [[q(181), q(191)], [QM31::ONE, q(193).pow(51)]];

    for point_scales in scale_pairs {
        let parameters = fixture_parameters(point_scales);
        let trace = build_circle_relation(&message, &parameters).unwrap();
        validate_circle_relation(&message, &parameters, &trace).unwrap();

        let point_weights = [
            multilinear_weights(&parameters.z),
            multilinear_weights(&parameters.xor11_z),
        ];
        let point_claims = [
            dot(&message, &point_weights[0]),
            dot(&message, &point_weights[1]),
        ];
        assert_eq!(trace.point_claims, point_claims);

        let mut weights = vec![QM31::ZERO; CIRCLE_RELATION_MESSAGE_LEN];
        add_scaled(&mut weights, point_scales[0], &point_weights[0]);
        add_scaled(&mut weights, point_scales[1], &point_weights[1]);
        let mut coefficients = message.clone();
        assert_eq!(trace.running_claims[0], dot(&coefficients, &weights));

        for round in 0..CIRCLE_RELATION_ROUNDS {
            let log_len = 10 - 2 * round as u32;
            for sample in 0..2 {
                let ood_weights = if round == 0 {
                    circle_tensor_weights(log_len, parameters.layer0_ood_points[sample])
                } else {
                    line_tensor_weights(log_len, parameters.later_ood_x[round - 1][sample])
                };
                assert_eq!(
                    trace.ood_values[round][sample],
                    dot(&coefficients, &ood_weights)
                );
                add_scaled(
                    &mut weights,
                    parameters.ood_mixes[round][sample],
                    &ood_weights,
                );
            }

            assert_eq!(trace.boundary_claims[round], dot(&coefficients, &weights));
            let polynomial = manual_sumcheck(&coefficients, &weights);
            assert_eq!(trace.sumchecks[round], polynomial);
            assert_eq!(
                trace.running_claims[round + 1],
                evaluate_polynomial(&polynomial, parameters.alphas[round])
            );

            coefficients = fold_coefficients(&coefficients, parameters.alphas[round]);
            weights = fold_weights(&weights, parameters.alphas[round]);
            assert_eq!(
                trace.running_claims[round + 1],
                dot(&coefficients, &weights)
            );
        }

        assert_eq!(coefficients.len(), CIRCLE_RELATION_FINAL_LEN);
        assert_eq!(trace.final_coefficients.as_slice(), coefficients);
        assert_eq!(trace.terminal_claim, dot(&coefficients, &weights));
        assert_eq!(
            trace.terminal_claim,
            trace.running_claims[CIRCLE_RELATION_ROUNDS]
        );
    }
}

#[test]
fn malformed_points_claims_ood_values_and_boundaries_are_rejected() {
    let message = fixture_message();
    let parameters = fixture_parameters([q(211), q(223)]);
    let trace = build_circle_relation(&message, &parameters).unwrap();

    let mut changed_point = parameters;
    changed_point.z[3] = changed_point.z[3].add(QM31::ONE);
    changed_point.xor11_z = xor11(changed_point.z);
    assert_eq!(
        validate_circle_relation(&message, &changed_point, &trace),
        Err(CircleRelationError::PointClaimMismatch { point: 0 })
    );

    let mut inconsistent_xor = parameters;
    inconsistent_xor.xor11_z[9] = inconsistent_xor.xor11_z[9].add(QM31::ONE);
    assert_eq!(
        build_circle_relation(&message, &inconsistent_xor),
        Err(CircleRelationError::Xor11PointMismatch { coordinate: 9 })
    );

    let mut false_ood = trace;
    false_ood.ood_values[2][1] = false_ood.ood_values[2][1].add(QM31::ONE);
    assert_eq!(
        validate_circle_relation(&message, &parameters, &false_ood),
        Err(CircleRelationError::OodValueMismatch {
            round: 2,
            sample: 1
        })
    );

    let mut false_boundary = trace;
    false_boundary.sumchecks[1][0] = false_boundary.sumchecks[1][0].add(QM31::ONE);
    assert_eq!(
        validate_circle_relation(&message, &parameters, &false_boundary),
        Err(CircleRelationError::BoundaryMismatch { round: 1 })
    );

    let mut off_curve = parameters;
    off_curve.layer0_ood_points[0] = SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    };
    assert_eq!(
        build_circle_relation(&message, &off_curve),
        Err(CircleRelationError::CirclePointNotOnCurve { sample: 0 })
    );

    let mut in_subfield = parameters;
    in_subfield.layer0_ood_points[1] = SecureCirclePoint {
        x: QM31::ONE,
        y: QM31::ZERO,
    };
    assert_eq!(
        build_circle_relation(&message, &in_subfield),
        Err(CircleRelationError::CirclePointNotOod { sample: 1 })
    );

    let mut line_in_subfield = parameters;
    line_in_subfield.later_ood_x[1][0] = QM31::from_cm31(CM31::new(M31(7), M31(11)));
    assert_eq!(
        build_circle_relation(&message, &line_in_subfield),
        Err(CircleRelationError::LinePointNotOod {
            round: 2,
            sample: 0
        })
    );
}

#[test]
fn zero_interval_claim_accepts_zero_sum_padding_and_rejects_a_nonzero_sum() {
    let mut message = fixture_message();
    let parameters = fixture_parameters([q(227), q(229)]);
    let padding_sum = message[870..CIRCLE_RELATION_MESSAGE_LEN - 1]
        .iter()
        .copied()
        .fold(QM31::ZERO, QM31::add);
    message[CIRCLE_RELATION_MESSAGE_LEN - 1] = QM31::ZERO.sub(padding_sum);
    build_circle_relation_with_zero_interval(
        &message,
        &parameters,
        870,
        CIRCLE_RELATION_MESSAGE_LEN,
    )
    .unwrap();

    message[901] = message[901].add(QM31::ONE);
    assert!(matches!(
        build_circle_relation_with_zero_interval(
            &message,
            &parameters,
            870,
            CIRCLE_RELATION_MESSAGE_LEN
        ),
        Err(CircleRelationError::BoundaryMismatch { round: 0 })
    ));
}
