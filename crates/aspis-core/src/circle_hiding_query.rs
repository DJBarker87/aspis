//! Layer-zero arithmetic for the one-mask+C1-padding hiding profile.
//!
//! C2 is the ordinary two-column `(h1,G)` leaf. The PCS therefore uses the
//! unchanged 51-column powers generator.

use crate::circle_query::{
    c2_symbol_offset, check_layer0_transition_prepared_for_fiber_count,
    gamma_combine_fixed_layer0_prepared, CircleQueryError, CircleQueryGammaPowers,
    CIRCLE_QUERY_C2_LEAF_BYTES,
};
use crate::field::{PreparedQm31Multiplier, M31, QM31};
use crate::proof::M31_CIRCLE_C1_COLUMNS;

pub const PAYMENT_HIDING_C2_COLUMNS: usize = 2;
pub const PAYMENT_HIDING_C2_LEAF_BYTES: usize = CIRCLE_QUERY_C2_LEAF_BYTES;
pub const PAYMENT_HIDING_OUTER_COLUMNS: usize = M31_CIRCLE_C1_COLUMNS + 2;

pub type PaymentHidingQueryPowers = CircleQueryGammaPowers;

pub const fn payment_hiding_c2_symbol_offset(column: usize, slot: usize) -> Option<usize> {
    c2_symbol_offset(column, slot)
}

pub fn gamma_combine_payment_hiding_layer0_prepared(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    powers: &PaymentHidingQueryPowers,
) -> Result<[QM31; 4], CircleQueryError> {
    gamma_combine_fixed_layer0_prepared(c1_leaf, c2_leaf, powers)
}

pub fn check_payment_hiding_layer0_transition_prepared_for_fiber_count(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    layer1_leaf: &[u8],
    query: usize,
    fiber_count: usize,
    powers: &PaymentHidingQueryPowers,
    inverses: [M31; 2],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    check_layer0_transition_prepared_for_fiber_count(
        c1_leaf,
        c2_leaf,
        layer1_leaf,
        query,
        fiber_count,
        powers,
        inverses,
        alpha,
        alpha_squared,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        circle_query::{CircleQueryLeaf, CIRCLE_QUERY_C1_LEAF_BYTES, CIRCLE_QUERY_QM31_BYTES},
        field::{qm31_power_table, CM31, P},
    };

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed), M31(seed + 1)),
            c1: CM31::new(M31(seed + 2), M31(seed + 3)),
        }
    }

    fn next_q(state: &mut u64) -> QM31 {
        let mut limb = || {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            M31((*state % u64::from(P)) as u32)
        };
        QM31 {
            c0: CM31::new(limb(), limb()),
            c1: CM31::new(limb(), limb()),
        }
    }

    #[test]
    fn reused_full_power_table_matches_direct_query_preparation() {
        let mut state = 0x51_00_15_7a_b1e5_5eed;
        for _ in 0..64 {
            let gamma = next_q(&mut state);
            let full = qm31_power_table::<PAYMENT_HIDING_OUTER_COLUMNS>(gamma);
            assert_eq!(
                PaymentHidingQueryPowers::from_full_table(&full),
                PaymentHidingQueryPowers::new(gamma),
            );
        }
    }

    #[test]
    fn one_mask_layer0_combiner_matches_the_standard_51_term_polynomial() {
        let gamma = q(101);
        let powers = PaymentHidingQueryPowers::new(gamma);
        let outer = qm31_power_table::<PAYMENT_HIDING_OUTER_COLUMNS>(gamma);
        let mut c1 = [0u8; CIRCLE_QUERY_C1_LEAF_BYTES];
        let mut c2 = [0u8; PAYMENT_HIDING_C2_LEAF_BYTES];
        let mut expected = [QM31::ZERO; 4];
        for slot in 0..4 {
            for column in 0..M31_CIRCLE_C1_COLUMNS {
                let symbol = M31(17 + slot as u32 * 1_003 + column as u32 * 19);
                let offset = (slot * M31_CIRCLE_C1_COLUMNS + column) * 4;
                c1[offset..offset + 4].copy_from_slice(&symbol.to_le_bytes());
                expected[slot] = expected[slot].add(outer[column].mul_m31(symbol));
            }
            for helper in 0..PAYMENT_HIDING_C2_COLUMNS {
                let value = q(10_001 + helper as u32 * 1_009 + slot as u32 * 103);
                let offset = payment_hiding_c2_symbol_offset(helper, slot).unwrap();
                value.write_le_bytes(&mut c2[offset..offset + CIRCLE_QUERY_QM31_BYTES]);
                expected[slot] =
                    expected[slot].add(outer[M31_CIRCLE_C1_COLUMNS + helper].mul(value));
            }
        }
        assert_eq!(
            gamma_combine_payment_hiding_layer0_prepared(&c1, &c2, &powers).unwrap(),
            expected,
        );
    }

    #[test]
    fn one_mask_layer0_combiner_rejects_width_and_noncanonical_symbols() {
        let powers = PaymentHidingQueryPowers::new(q(101));
        let c1 = [0u8; CIRCLE_QUERY_C1_LEAF_BYTES];
        let mut c2 = [0u8; PAYMENT_HIDING_C2_LEAF_BYTES];
        assert!(matches!(
            gamma_combine_payment_hiding_layer0_prepared(&c1, &c2[..c2.len() - 1], &powers),
            Err(CircleQueryError::LeafLength {
                leaf: CircleQueryLeaf::C2,
                expected: PAYMENT_HIDING_C2_LEAF_BYTES,
                actual
            }) if actual == PAYMENT_HIDING_C2_LEAF_BYTES - 1
        ));
        let offset = payment_hiding_c2_symbol_offset(1, 3).unwrap();
        c2[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            gamma_combine_payment_hiding_layer0_prepared(&c1, &c2, &powers),
            Err(CircleQueryError::NonCanonicalQm31 {
                leaf: CircleQueryLeaf::C2,
                offset,
            }),
        );
    }
}
