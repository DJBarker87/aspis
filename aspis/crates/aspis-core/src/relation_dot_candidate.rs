//! Fused relation-dot kernel for the fixed profile-15 shape.
//!
//! The accepted proof currently carries two rows of 51 canonical QM31
//! statement evaluations.  Both rows use the same geometric gamma weights,
//! and the resulting power table is then converted into the prepared layer-0
//! query representation.  This candidate performs those three operations in
//! one traversal:
//!
//! 1. generate each gamma power once;
//! 2. canonically decode both row values and accumulate both dots while
//!    sharing the power's Karatsuba decomposition; and
//! 3. retain exactly the limbs/prepared helpers needed by the query verifier.
//!
//! The profile parser deliberately defers validation of this exact byte block
//! so canonical decoding is not still paid twice. Delaying that check is
//! acceptance-equivalent: the transcript absorbs the unchanged raw bytes
//! before gamma, and this kernel rejects every noncanonical limb before the
//! relation can accept.

use crate::circle_hiding_prefix::{
    PAYMENT_HIDING_STATEMENT_EVALUATIONS_LEN, PAYMENT_HIDING_VALUES_PER_POINT,
};
use crate::circle_hiding_query::{PaymentHidingQueryPowers, PAYMENT_HIDING_OUTER_COLUMNS};
use crate::field::{PreparedQm31Multiplier, CM31, M31, P, QM31};
use crate::proof::M31_CIRCLE_C1_COLUMNS;

const KARATSUBA_COMPONENTS: usize = 3;
const KARATSUBA_CHANNELS: usize = 3;
const PRODUCT_CHANNELS: usize = KARATSUBA_COMPONENTS * KARATSUBA_CHANNELS;
const PRODUCTS_PER_REDUCTION: usize = 4;

/// Exact arithmetic schedule of [`payment_hiding_relation_dot_candidate`].
///
/// The two dots contain `2 * 51 * 9` M31 products.  Generating powers one
/// through fifty contains another `50 * 9`.  Thirteen four-product blocks per
/// row reduce nine channels, followed by nine outer reductions per row; power
/// generation uses the ordinary nine-reduction QM31 multiplication.
const PAYMENT_HIDING_RELATION_DOT_M31_PRODUCTS: usize =
    (2 * PAYMENT_HIDING_OUTER_COLUMNS + (PAYMENT_HIDING_OUTER_COLUMNS - 1)) * 9;
const PAYMENT_HIDING_RELATION_DOT_M31_REDUCTIONS: usize =
    2 * (PAYMENT_HIDING_OUTER_COLUMNS.div_ceil(PRODUCTS_PER_REDUCTION) + 1) * 9
        + (PAYMENT_HIDING_OUTER_COLUMNS - 1) * 9;
const PAYMENT_HIDING_RELATION_DOT_QM31_DECODES: usize = 2 * PAYMENT_HIDING_OUTER_COLUMNS;
const PAYMENT_HIDING_RELATION_DOT_M31_LIMB_DECODES: usize =
    4 * PAYMENT_HIDING_RELATION_DOT_QM31_DECODES;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PaymentHidingRelationDotCandidate {
    pub claims: [QM31; 2],
    pub query_powers: PaymentHidingQueryPowers,
}

#[inline(always)]
fn prepared_components(value: QM31) -> [[M31; KARATSUBA_CHANNELS]; KARATSUBA_COMPONENTS] {
    let prepare = |component: CM31| [component.a, component.b, component.a.add(component.b)];
    [
        prepare(value.c0),
        prepare(value.c1),
        prepare(value.c0.add(value.c1)),
    ]
}

#[inline(always)]
fn value_components(value: QM31) -> [[M31; KARATSUBA_CHANNELS]; KARATSUBA_COMPONENTS] {
    prepared_components(value)
}

#[inline(always)]
fn mul_by_r(value: CM31) -> CM31 {
    CM31 {
        a: value.a.double().sub(value.b),
        b: value.a.add(value.b.double()),
    }
}

#[inline(always)]
fn finish_dot(channels: [u64; PRODUCT_CHANNELS]) -> QM31 {
    let component = |offset: usize| {
        let m0 = M31::reduce_u64(channels[offset]);
        let m1 = M31::reduce_u64(channels[offset + 1]);
        let m2 = M31::reduce_u64(channels[offset + 2]);
        CM31 {
            a: m0.sub(m1),
            b: m2.sub(m0).sub(m1),
        }
    };
    let m0 = component(0);
    let m1 = component(3);
    let m2 = component(6);
    QM31 {
        c0: m0.add(mul_by_r(m1)),
        c1: m2.sub(m0).sub(m1),
    }
}

#[inline(always)]
fn decode_qm31_masked(bytes: &[u8], invalid: &mut u32) -> QM31 {
    debug_assert_eq!(bytes.len(), 16);
    let mut limbs = [M31::ZERO; 4];
    for (limb, output) in limbs.iter_mut().enumerate() {
        let start = limb * 4;
        let raw = u32::from_le_bytes(bytes[start..start + 4].try_into().unwrap());
        *invalid |= u32::from(raw >= P);
        // The result is discarded when `raw` is noncanonical.  Masking keeps
        // rejected-input arithmetic bounded and matches the existing fused
        // byte kernels' single-final-branch discipline.
        *output = M31(raw & P);
    }
    QM31 {
        c0: CM31::new(limbs[0], limbs[1]),
        c1: CM31::new(limbs[2], limbs[3]),
    }
}

/// Canonically decode and gamma-combine both profile-15 statement rows.
///
/// Input order is the proof's row-major layout: 51 QM31 values at `z`, then
/// 51 at `xor11(z)`.  A successful result is byte-for-byte equivalent to two
/// `qm31_dot(qm31_power_table(gamma), row)` calls, and its query powers equal
/// `PaymentHidingQueryPowers::from_full_table` for the same gamma.
///
/// This primitive has one input-length branch and one final canonicality
/// branch.  Every one of the 408 encoded M31 limbs is checked.
pub(crate) fn payment_hiding_relation_dot_candidate(
    gamma: QM31,
    bytes: &[u8],
) -> Option<PaymentHidingRelationDotCandidate> {
    if bytes.len() != PAYMENT_HIDING_STATEMENT_EVALUATIONS_LEN {
        return None;
    }

    let mut invalid = 0u32;
    let mut outer = [[0u64; PRODUCT_CHANNELS]; 2];
    let mut c1_limbs = [[0u32; 4]; M31_CIRCLE_C1_COLUMNS];
    let mut helpers = [PreparedQm31Multiplier::new(QM31::ZERO); 2];
    let mut power = QM31::ONE;

    for block_start in (0..PAYMENT_HIDING_OUTER_COLUMNS).step_by(PRODUCTS_PER_REDUCTION) {
        let block_end = core::cmp::min(
            block_start + PRODUCTS_PER_REDUCTION,
            PAYMENT_HIDING_OUTER_COLUMNS,
        );
        let mut raw = [[0u64; PRODUCT_CHANNELS]; 2];

        for column in block_start..block_end {
            let weight = prepared_components(power);
            if column < M31_CIRCLE_C1_COLUMNS {
                c1_limbs[column] = [power.c0.a.0, power.c0.b.0, power.c1.a.0, power.c1.b.0];
            } else {
                helpers[column - M31_CIRCLE_C1_COLUMNS] = PreparedQm31Multiplier::new(power);
            }

            for (point, raw_point) in raw.iter_mut().enumerate() {
                let value_index = point * PAYMENT_HIDING_VALUES_PER_POINT + column;
                let offset = value_index * 16;
                let value = decode_qm31_masked(&bytes[offset..offset + 16], &mut invalid);
                let value = value_components(value);
                for component in 0..KARATSUBA_COMPONENTS {
                    for channel in 0..KARATSUBA_CHANNELS {
                        raw_point[component * KARATSUBA_CHANNELS + channel] +=
                            u64::from(weight[component][channel].0)
                                * u64::from(value[component][channel].0);
                    }
                }
            }

            if column + 1 != PAYMENT_HIDING_OUTER_COLUMNS {
                power = power.mul(gamma);
            }
        }

        for point in 0..2 {
            for channel in 0..PRODUCT_CHANNELS {
                outer[point][channel] += u64::from(M31::reduce_u64(raw[point][channel]).0);
            }
        }
    }

    if invalid != 0 {
        return None;
    }

    Some(PaymentHidingRelationDotCandidate {
        claims: [finish_dot(outer[0]), finish_dot(outer[1])],
        query_powers: PaymentHidingQueryPowers { c1_limbs, helpers },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{qm31_dot, qm31_power_table};

    fn next_m31(state: &mut u64) -> M31 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31((*state % u64::from(P)) as u32)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(next_m31(state), next_m31(state)),
            c1: CM31::new(next_m31(state), next_m31(state)),
        }
    }

    fn encode(values: &[[QM31; PAYMENT_HIDING_OUTER_COLUMNS]; 2]) -> [u8; 1632] {
        let mut bytes = [0u8; PAYMENT_HIDING_STATEMENT_EVALUATIONS_LEN];
        for (point, row) in values.iter().enumerate() {
            for (column, value) in row.iter().enumerate() {
                let index = point * PAYMENT_HIDING_OUTER_COLUMNS + column;
                value.write_le_bytes(&mut bytes[index * 16..][..16]);
            }
        }
        bytes
    }

    fn reference(
        gamma: QM31,
        values: &[[QM31; PAYMENT_HIDING_OUTER_COLUMNS]; 2],
    ) -> PaymentHidingRelationDotCandidate {
        let powers = qm31_power_table::<PAYMENT_HIDING_OUTER_COLUMNS>(gamma);
        PaymentHidingRelationDotCandidate {
            claims: [qm31_dot(&powers, &values[0]), qm31_dot(&powers, &values[1])],
            query_powers: PaymentHidingQueryPowers::from_full_table(&powers),
        }
    }

    #[test]
    fn schedule_counts_are_pinned() {
        assert_eq!(PAYMENT_HIDING_RELATION_DOT_M31_PRODUCTS, 1_368);
        assert_eq!(PAYMENT_HIDING_RELATION_DOT_M31_REDUCTIONS, 702);
        assert_eq!(PAYMENT_HIDING_RELATION_DOT_QM31_DECODES, 102);
        assert_eq!(PAYMENT_HIDING_RELATION_DOT_M31_LIMB_DECODES, 408);
    }

    #[test]
    fn candidate_matches_reference_at_random_inputs() {
        let mut state = 0x51_02_fa5e_d07c_5eed;
        for _ in 0..128 {
            let gamma = next_qm31(&mut state);
            let values = core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state)));
            assert_eq!(
                payment_hiding_relation_dot_candidate(gamma, &encode(&values)),
                Some(reference(gamma, &values)),
            );
        }
    }

    #[test]
    fn candidate_matches_reference_at_edge_challenges_and_dense_values() {
        let maximal = QM31 {
            c0: CM31::new(M31(P - 1), M31(P - 1)),
            c1: CM31::new(M31(P - 1), M31(P - 1)),
        };
        let values = [[maximal; PAYMENT_HIDING_OUTER_COLUMNS]; 2];
        let minus_one = QM31 {
            c0: CM31::new(M31(P - 1), M31::ZERO),
            c1: CM31::ZERO,
        };
        for gamma in [QM31::ZERO, QM31::ONE, minus_one, maximal] {
            assert_eq!(
                payment_hiding_relation_dot_candidate(gamma, &encode(&values)),
                Some(reference(gamma, &values)),
            );
        }
    }

    #[test]
    fn every_row_and_column_one_hot_matches_reference() {
        let gamma = QM31 {
            c0: CM31::new(M31(0x1234_567), M31(0x4567_123)),
            c1: CM31::new(M31(0x1111_111), M31(0x2222_222)),
        };
        let marker = QM31 {
            c0: CM31::new(M31(P - 1), M31(17)),
            c1: CM31::new(M31(23), M31(P - 2)),
        };
        for point in 0..2 {
            for column in 0..PAYMENT_HIDING_OUTER_COLUMNS {
                let mut values = [[QM31::ZERO; PAYMENT_HIDING_OUTER_COLUMNS]; 2];
                values[point][column] = marker;
                assert_eq!(
                    payment_hiding_relation_dot_candidate(gamma, &encode(&values)),
                    Some(reference(gamma, &values)),
                    "point={point}, column={column}",
                );
            }
        }
    }

    #[test]
    fn every_encoded_limb_is_checked_for_canonicality() {
        let values = [[QM31::ZERO; PAYMENT_HIDING_OUTER_COLUMNS]; 2];
        let canonical = encode(&values);
        for limb in 0..PAYMENT_HIDING_RELATION_DOT_M31_LIMB_DECODES {
            let mut bytes = canonical;
            bytes[limb * 4..limb * 4 + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                payment_hiding_relation_dot_candidate(QM31::ONE, &bytes),
                None,
                "accepted noncanonical limb {limb}",
            );
        }
    }

    #[test]
    fn wrong_lengths_are_rejected() {
        let bytes = [0u8; PAYMENT_HIDING_STATEMENT_EVALUATIONS_LEN];
        assert_eq!(
            payment_hiding_relation_dot_candidate(QM31::ONE, &bytes[..bytes.len() - 1]),
            None,
        );
        let mut oversized = [0u8; PAYMENT_HIDING_STATEMENT_EVALUATIONS_LEN + 1];
        oversized[..bytes.len()].copy_from_slice(&bytes);
        assert_eq!(
            payment_hiding_relation_dot_candidate(QM31::ONE, &oversized),
            None,
        );
    }
}
