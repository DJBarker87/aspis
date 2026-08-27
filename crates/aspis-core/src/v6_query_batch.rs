//! Algebraic batching for the sixteen V6 final-polynomial query checks.
//!
//! At the degree-<256 stage, each authenticated folded layer-zero value must
//! equal the disclosed final polynomial at one transcript-derived line point.
//! This module turns those sixteen equalities into one random linear claim
//! that can share the three remaining relation folds.

use crate::field::{qm31_dot, PreparedQm31Multiplier, M31, QM31};
use crate::sumcheck::WeightAccumulator;

pub const V6_QUERY_BATCH_COUNT: usize = 16;
pub const V6_QUERY_BATCH_MAX_DEGREE: usize = V6_QUERY_BATCH_COUNT - 1;
pub const V7_QUERY_BATCH_JOINT_MAX_DEGREE: usize = V6_QUERY_BATCH_COUNT;
pub const V6_QUERY_BATCH_CIRCLE_DOMAIN_LOG: u32 = 20;
pub const V6_QUERY_BATCH_LINE_LAYER: u8 = 1;
pub const V6_QUERY_BATCH_TREE_DEPTH: u8 = 18;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6QueryBatchError {
    InvalidQuerySchedule,
    WeightShape,
}

/// Authenticated results returned by the single circle-fold callback.  The
/// line coordinates are derived alongside the fold denominators from the
/// same selected circle points, so the relation tail never recomputes them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V6AuthenticatedQueryBatch {
    pub values: [QM31; V6_QUERY_BATCH_COUNT],
    pub line_x: [M31; V6_QUERY_BATCH_COUNT],
}

/// Install sixteen structured line-evaluation covectors into an existing
/// degree-<256 relation accumulator and add the matching authenticated-value
/// claim to `running_claim`.
///
/// Query ordinal `i` receives scale `rho^i`, beginning with one. The caller
/// must invoke this exactly when `weights` has log length eight. The query
/// indices may be in transcript order; this function rejects duplicates and
/// indices outside the V6 layer-one line domain.
///
/// The returned value is the claim increment
/// `sum_i rho^i * authenticated_values[i]`.
pub fn add_v6_final256_query_batch(
    weights: &mut WeightAccumulator,
    running_claim: &mut QM31,
    queries: [u32; V6_QUERY_BATCH_COUNT],
    authenticated: V6AuthenticatedQueryBatch,
    rho: QM31,
) -> Result<QM31, V6QueryBatchError> {
    add_final256_query_batch_with_initial_scale(
        weights,
        running_claim,
        queries,
        authenticated,
        rho,
        QM31::ONE,
    )
}

/// Tag-73 joint query/relation batching. Query ordinal `i` receives scale
/// `rho^(i+1)`, so the complete post-round-zero discrepancy has the untouched
/// prior scalar as its constant coefficient. This prevents an ordinal-zero
/// query error from cancelling that prior scalar for every `rho`.
///
/// The wire format and number of field multiplications are unchanged from
/// V6: seeding with `rho` rather than one still needs exactly fifteen prepared
/// multiplications to produce all sixteen scales.
pub fn add_v7_final256_query_batch_shifted(
    weights: &mut WeightAccumulator,
    running_claim: &mut QM31,
    queries: [u32; V6_QUERY_BATCH_COUNT],
    authenticated: V6AuthenticatedQueryBatch,
    rho: QM31,
) -> Result<QM31, V6QueryBatchError> {
    add_final256_query_batch_with_initial_scale(
        weights,
        running_claim,
        queries,
        authenticated,
        rho,
        rho,
    )
}

fn add_final256_query_batch_with_initial_scale(
    weights: &mut WeightAccumulator,
    running_claim: &mut QM31,
    queries: [u32; V6_QUERY_BATCH_COUNT],
    authenticated: V6AuthenticatedQueryBatch,
    rho: QM31,
    initial_scale: QM31,
) -> Result<QM31, V6QueryBatchError> {
    let mut sorted = queries;
    sorted.sort_unstable();
    if sorted[V6_QUERY_BATCH_COUNT - 1] >= 1u32 << V6_QUERY_BATCH_TREE_DEPTH
        || sorted.windows(2).any(|pair| pair[0] == pair[1])
    {
        return Err(V6QueryBatchError::InvalidQuerySchedule);
    }

    let mut scales = [QM31::ZERO; V6_QUERY_BATCH_COUNT];
    scales[0] = initial_scale;
    let prepared_rho = PreparedQm31Multiplier::new(rho);
    for ordinal in 1..V6_QUERY_BATCH_COUNT {
        scales[ordinal] = prepared_rho.mul(scales[ordinal - 1]);
    }
    weights
        .add_line_m31_batch(&scales, &authenticated.line_x)
        .map_err(|_| V6QueryBatchError::WeightShape)?;
    let claim_increment = qm31_dot(&scales, &authenticated.values);
    *running_claim = running_claim.add(claim_increment);
    Ok(claim_increment)
}

/// Evaluate the Tag-73 shifted residual. Its degree is at most sixteen and it
/// is exactly `rho` times the frozen V6 residual.
pub fn v7_final256_query_batch_shifted_residual(
    expected_values: [QM31; V6_QUERY_BATCH_COUNT],
    authenticated_values: [QM31; V6_QUERY_BATCH_COUNT],
    rho: QM31,
) -> QM31 {
    rho.mul(v6_final256_query_batch_residual(
        expected_values,
        authenticated_values,
        rho,
    ))
}

/// Evaluate the degree-at-most-fifteen error polynomial associated with one
/// batched query check. Zero means that this particular `rho` is either an
/// accepting all-equalities point or a root of a nonzero error polynomial.
pub fn v6_final256_query_batch_residual(
    expected_values: [QM31; V6_QUERY_BATCH_COUNT],
    authenticated_values: [QM31; V6_QUERY_BATCH_COUNT],
    rho: QM31,
) -> QM31 {
    let mut scale = QM31::ONE;
    let mut residual = QM31::ZERO;
    for ordinal in 0..V6_QUERY_BATCH_COUNT {
        residual =
            residual.add(scale.mul(expected_values[ordinal].sub(authenticated_values[ordinal])));
        scale = scale.mul(rho);
    }
    residual
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circle_fri::line_domain_x_for_circle;
    use crate::field::{CM31, M31, P};
    use crate::sumcheck::{boundary_sum, evaluate, polynomial_for_extension};
    use crate::v6_onefold::evaluate_final256_coefficients;
    use alloc::vec::Vec;

    #[derive(Clone, Copy)]
    struct Deterministic(u64);

    impl Deterministic {
        fn word(&mut self) -> u32 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            ((self.0 >> 17) as u32) % P
        }

        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(M31(self.word()), M31(self.word())),
                c1: CM31::new(M31(self.word()), M31(self.word())),
            }
        }

        fn nonzero_qm31(&mut self) -> QM31 {
            loop {
                let value = self.qm31();
                if !value.is_zero() {
                    return value;
                }
            }
        }
    }

    fn query_schedule(random: &mut Deterministic) -> [u32; V6_QUERY_BATCH_COUNT] {
        let mut queries = [0u32; V6_QUERY_BATCH_COUNT];
        for ordinal in 0..V6_QUERY_BATCH_COUNT {
            loop {
                let candidate = random.word() & ((1 << V6_QUERY_BATCH_TREE_DEPTH) - 1);
                if !queries[..ordinal].contains(&candidate) {
                    queries[ordinal] = candidate;
                    break;
                }
            }
        }
        queries
    }

    fn direct_values(
        coefficients: &[QM31],
        queries: [u32; V6_QUERY_BATCH_COUNT],
    ) -> [QM31; V6_QUERY_BATCH_COUNT] {
        core::array::from_fn(|ordinal| {
            let point = line_domain_x_for_circle(
                V6_QUERY_BATCH_CIRCLE_DOMAIN_LOG,
                V6_QUERY_BATCH_LINE_LAYER,
                queries[ordinal] as usize,
            )
            .unwrap();
            evaluate_final256_coefficients(coefficients, point).unwrap()
        })
    }

    fn authenticated_batch(
        queries: [u32; V6_QUERY_BATCH_COUNT],
        values: [QM31; V6_QUERY_BATCH_COUNT],
    ) -> V6AuthenticatedQueryBatch {
        V6AuthenticatedQueryBatch {
            values,
            line_x: core::array::from_fn(|ordinal| {
                line_domain_x_for_circle(
                    V6_QUERY_BATCH_CIRCLE_DOMAIN_LOG,
                    V6_QUERY_BATCH_LINE_LAYER,
                    queries[ordinal] as usize,
                )
                .unwrap()
            }),
        }
    }

    fn fold_arity4(values: &[QM31], alpha: QM31) -> Vec<QM31> {
        let alpha2 = alpha.square();
        let alpha3 = alpha2.mul(alpha);
        values
            .chunks_exact(4)
            .map(|chunk| {
                chunk[0]
                    .add(alpha.mul(chunk[1]))
                    .add(alpha2.mul(chunk[2]))
                    .add(alpha3.mul(chunk[3]))
            })
            .collect()
    }

    fn rho_sum(values: &[QM31; V6_QUERY_BATCH_COUNT], rho: QM31) -> QM31 {
        let mut scale = QM31::ONE;
        let mut result = QM31::ZERO;
        for value in values {
            result = result.add(scale.mul(*value));
            scale = scale.mul(rho);
        }
        result
    }

    fn shifted_rho_sum(values: &[QM31; V6_QUERY_BATCH_COUNT], rho: QM31) -> QM31 {
        rho.mul(rho_sum(values, rho))
    }

    #[test]
    fn randomized_direct_checks_equal_one_claim_through_all_three_folds() {
        for seed in 1..=24u64 {
            let mut random = Deterministic(0x9e37_79b9_7f4a_7c15 ^ seed);
            let queries = query_schedule(&mut random);
            let mut coefficients = (0..256).map(|_| random.qm31()).collect::<Vec<_>>();
            let expected = direct_values(&coefficients, queries);
            let rho = random.nonzero_qm31();

            // Exercise composition with an already-live structured relation,
            // rather than testing the query components in an empty wrapper.
            let mut weights = WeightAccumulator::empty(8);
            let base_scale = random.qm31();
            let base_point = (0..8).map(|_| random.qm31()).collect::<Vec<_>>();
            weights.add_multilinear(base_scale, base_point).unwrap();
            let base_claim = weights.dot(&coefficients);
            let mut running_claim = base_claim;
            let increment = add_v6_final256_query_batch(
                &mut weights,
                &mut running_claim,
                queries,
                authenticated_batch(queries, expected),
                rho,
            )
            .unwrap();

            assert_eq!(increment, rho_sum(&expected, rho));
            assert_eq!(running_claim, base_claim.add(rho_sum(&expected, rho)));
            assert_eq!(weights.dot(&coefficients), running_claim);

            for _ in 0..3 {
                let polynomial = polynomial_for_extension(&coefficients, &weights);
                assert_eq!(boundary_sum(&polynomial), running_claim);
                let alpha = random.qm31();
                running_claim = evaluate(&polynomial, alpha);
                weights.fold_deferred_relation_arity4(alpha);
                coefficients = fold_arity4(&coefficients, alpha);
                assert_eq!(weights.dot(&coefficients), running_claim);
            }
            assert_eq!(coefficients.len(), 4);
            assert_eq!(weights.dot(&coefficients), running_claim);
        }
    }

    #[test]
    fn v7_shifted_batch_composes_through_all_three_folds() {
        for seed in 1..=8u64 {
            let mut random = Deterministic(0xa076_1d64_78bd_642f ^ seed);
            let queries = query_schedule(&mut random);
            let mut coefficients = (0..256).map(|_| random.qm31()).collect::<Vec<_>>();
            let expected = direct_values(&coefficients, queries);
            let rho = random.nonzero_qm31();

            let mut weights = WeightAccumulator::empty(8);
            let base_scale = random.qm31();
            let base_point = (0..8).map(|_| random.qm31()).collect::<Vec<_>>();
            weights.add_multilinear(base_scale, base_point).unwrap();
            let base_claim = weights.dot(&coefficients);
            let mut running_claim = base_claim;
            let increment = add_v7_final256_query_batch_shifted(
                &mut weights,
                &mut running_claim,
                queries,
                authenticated_batch(queries, expected),
                rho,
            )
            .unwrap();

            assert_eq!(increment, shifted_rho_sum(&expected, rho));
            assert_eq!(running_claim, base_claim.add(increment));
            assert_eq!(weights.dot(&coefficients), running_claim);

            for _ in 0..3 {
                let polynomial = polynomial_for_extension(&coefficients, &weights);
                assert_eq!(boundary_sum(&polynomial), running_claim);
                let alpha = random.qm31();
                running_claim = evaluate(&polynomial, alpha);
                weights.fold_deferred_relation_arity4(alpha);
                coefficients = fold_arity4(&coefficients, alpha);
                assert_eq!(weights.dot(&coefficients), running_claim);
            }
        }
    }

    #[test]
    fn each_single_corruption_is_a_nonzero_monomial_of_degree_at_most_fifteen() {
        let expected = [QM31::ZERO; V6_QUERY_BATCH_COUNT];
        let delta = QM31::from_cm31(CM31::from_m31(M31(17)));
        let nonzero_rhos = [
            QM31::ONE,
            QM31::from_cm31(CM31::from_m31(M31(2))),
            QM31 {
                c0: CM31::new(M31(3), M31(5)),
                c1: CM31::new(M31(7), M31(11)),
            },
        ];

        for corrupted_ordinal in 0..V6_QUERY_BATCH_COUNT {
            let mut authenticated = expected;
            authenticated[corrupted_ordinal] = delta;
            assert!(corrupted_ordinal <= V6_QUERY_BATCH_MAX_DEGREE);
            for rho in nonzero_rhos {
                let residual = v6_final256_query_batch_residual(expected, authenticated, rho);
                assert_eq!(residual, delta.neg().mul(rho.pow(corrupted_ordinal as u64)));
                assert!(!residual.is_zero());
            }

            let at_zero = v6_final256_query_batch_residual(expected, authenticated, QM31::ZERO);
            assert_eq!(at_zero.is_zero(), corrupted_ordinal != 0);
        }
    }

    #[test]
    fn v7_shift_moves_ordinal_zero_error_out_of_the_constant_coefficient() {
        let expected = [QM31::ZERO; V6_QUERY_BATCH_COUNT];
        let delta = QM31::from_cm31(CM31::from_m31(M31(17)));
        let mut authenticated = expected;
        authenticated[0] = delta;
        let rho = QM31::from_cm31(CM31::from_m31(M31(2)));

        let legacy = v6_final256_query_batch_residual(expected, authenticated, rho);
        let shifted = v7_final256_query_batch_shifted_residual(expected, authenticated, rho);
        assert_eq!(legacy, delta.neg());
        assert_eq!(shifted, rho.mul(delta.neg()));
        assert_ne!(legacy, shifted);
        assert_eq!(V7_QUERY_BATCH_JOINT_MAX_DEGREE, 16);
    }

    #[test]
    fn randomized_error_polynomials_have_at_most_their_degree_many_sampled_roots() {
        for seed in 1..=64u64 {
            let mut random = Deterministic(0xd1b5_4a32_d192_ed03 ^ seed);
            let degree = (random.word() as usize) % V6_QUERY_BATCH_COUNT;
            let expected = [QM31::ZERO; V6_QUERY_BATCH_COUNT];
            let mut authenticated = [QM31::ZERO; V6_QUERY_BATCH_COUNT];
            for value in &mut authenticated[..degree] {
                *value = random.qm31();
            }
            authenticated[degree] = random.nonzero_qm31();

            let roots = (0..64u32)
                .filter(|candidate| {
                    let rho = QM31::from_cm31(CM31::from_m31(M31(*candidate)));
                    v6_final256_query_batch_residual(expected, authenticated, rho).is_zero()
                })
                .count();
            assert!(roots <= degree);
        }
    }

    #[test]
    fn duplicate_and_out_of_range_queries_are_rejected_before_mutation() {
        let values = [QM31::ZERO; V6_QUERY_BATCH_COUNT];
        let mut duplicate = core::array::from_fn(|index| index as u32);
        duplicate[15] = duplicate[14];
        let mut weights = WeightAccumulator::empty(8);
        let mut claim = QM31::ZERO;
        assert_eq!(
            add_v6_final256_query_batch(
                &mut weights,
                &mut claim,
                duplicate,
                V6AuthenticatedQueryBatch {
                    values,
                    line_x: [M31::ZERO; V6_QUERY_BATCH_COUNT],
                },
                QM31::ONE,
            ),
            Err(V6QueryBatchError::InvalidQuerySchedule)
        );
        assert_eq!(claim, QM31::ZERO);

        let mut out_of_range = core::array::from_fn(|index| index as u32);
        out_of_range[15] = 1 << V6_QUERY_BATCH_TREE_DEPTH;
        assert_eq!(
            add_v6_final256_query_batch(
                &mut weights,
                &mut claim,
                out_of_range,
                V6AuthenticatedQueryBatch {
                    values,
                    line_x: [M31::ZERO; V6_QUERY_BATCH_COUNT],
                },
                QM31::ONE,
            ),
            Err(V6QueryBatchError::InvalidQuerySchedule)
        );
        assert_eq!(claim, QM31::ZERO);
    }
}
