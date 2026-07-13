//! Layer-zero arithmetic for the production 28-column state-only profile.
//!
//! This module changes no production parser, transcript, commitment, or proof
//! format.  It gives the candidate an exact no-std arithmetic seam using the
//! same scalar powers generator as profile 15:
//!
//! `C_0 + ... + gamma^15*C_15 + gamma^16*M_0 + ... + gamma^25*M_9
//!  + gamma^26*h1 + gamma^27*G`.

use crate::circle_query::{canonical_m31_leaf_error, CircleQueryError, CircleQueryLeaf};
use crate::field::{
    qm31_m31_dot4_prepared_limbs_4b2_bytes, qm31_power_table, qm31_sum_products2_prepared,
    PreparedQm31Multiplier, M31, QM31,
};

pub const STATE_ONLY_C1_COLUMNS: usize =
    crate::state_only_hiding::STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS;
pub const STATE_ONLY_C2_COLUMNS: usize = crate::state_only_hiding::STATE_ONLY_HIDING_C2_COLUMNS;
pub const STATE_ONLY_TOTAL_COLUMNS: usize = STATE_ONLY_C1_COLUMNS + STATE_ONLY_C2_COLUMNS;
pub const STATE_ONLY_FIBER_SLOTS: usize = 4;
pub const STATE_ONLY_QM31_BYTES: usize = 16;
pub const STATE_ONLY_C1_LEAF_BYTES: usize = STATE_ONLY_FIBER_SLOTS * STATE_ONLY_C1_COLUMNS * 4;
pub const STATE_ONLY_C2_LEAF_BYTES: usize =
    STATE_ONLY_C2_COLUMNS * STATE_ONLY_FIBER_SLOTS * STATE_ONLY_QM31_BYTES;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyQueryPowers {
    pub c1_limbs: [[u32; 4]; STATE_ONLY_C1_COLUMNS],
    pub helpers: [PreparedQm31Multiplier; STATE_ONLY_C2_COLUMNS],
}

impl StateOnlyQueryPowers {
    pub fn new(gamma: QM31) -> Self {
        let powers = qm31_power_table::<STATE_ONLY_TOTAL_COLUMNS>(gamma);
        Self::from_full_table(&powers)
    }

    pub fn from_full_table(powers: &[QM31; STATE_ONLY_TOTAL_COLUMNS]) -> Self {
        let c1: [QM31; STATE_ONLY_C1_COLUMNS] = core::array::from_fn(|index| powers[index]);
        Self {
            c1_limbs: c1.map(|weight| [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]),
            helpers: [
                PreparedQm31Multiplier::new(powers[STATE_ONLY_C1_COLUMNS]),
                PreparedQm31Multiplier::new(powers[STATE_ONLY_C1_COLUMNS + 1]),
            ],
        }
    }
}

/// Byte offset of one M31 symbol in the slot-major C1 state leaf.
pub const fn state_only_c1_symbol_offset(slot: usize, column: usize) -> Option<usize> {
    if slot < STATE_ONLY_FIBER_SLOTS && column < STATE_ONLY_C1_COLUMNS {
        Some((slot * STATE_ONLY_C1_COLUMNS + column) * 4)
    } else {
        None
    }
}

/// Byte offset of one QM31 symbol in the helper-major C2 leaf.
pub const fn state_only_c2_symbol_offset(helper: usize, slot: usize) -> Option<usize> {
    if helper < STATE_ONLY_C2_COLUMNS && slot < STATE_ONLY_FIBER_SLOTS {
        Some((helper * STATE_ONLY_FIBER_SLOTS + slot) * STATE_ONLY_QM31_BYTES)
    } else {
        None
    }
}

/// Canonically decode and combine one authenticated state-only layer-zero
/// C1/C2 leaf pair.  The four returned values retain the arity-four circle
/// fiber ordering expected by the unchanged fold.
pub fn gamma_combine_state_only_layer0_prepared(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    powers: &StateOnlyQueryPowers,
) -> Result<[QM31; STATE_ONLY_FIBER_SLOTS], CircleQueryError> {
    gamma_combine_state_only_layer0_helpers_dot2_candidate(c1_leaf, c2_leaf, powers)
}

/// Literal pre-fusion helper evaluator retained as an independent
/// differential reference. Production callers use the lazy two-product
/// accumulator in [`gamma_combine_state_only_layer0_prepared`].
#[doc(hidden)]
pub fn gamma_combine_state_only_layer0_legacy_reference(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    powers: &StateOnlyQueryPowers,
) -> Result<[QM31; STATE_ONLY_FIBER_SLOTS], CircleQueryError> {
    if c1_leaf.len() != STATE_ONLY_C1_LEAF_BYTES {
        return Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C1,
            expected: STATE_ONLY_C1_LEAF_BYTES,
            actual: c1_leaf.len(),
        });
    }
    if c2_leaf.len() != STATE_ONLY_C2_LEAF_BYTES {
        return Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C2,
            expected: STATE_ONLY_C2_LEAF_BYTES,
            actual: c2_leaf.len(),
        });
    }

    let mut combined = qm31_m31_dot4_prepared_limbs_4b2_bytes(&powers.c1_limbs, c1_leaf)
        .ok_or_else(|| canonical_m31_leaf_error(c1_leaf))?;
    for (helper, power) in powers.helpers.into_iter().enumerate() {
        for (slot, value) in combined.iter_mut().enumerate() {
            let offset = state_only_c2_symbol_offset(helper, slot).unwrap();
            let symbol = QM31::from_le_bytes(&c2_leaf[offset..offset + STATE_ONLY_QM31_BYTES])
                .ok_or(CircleQueryError::NonCanonicalQm31 {
                    leaf: CircleQueryLeaf::C2,
                    offset,
                })?;
            *value = value.add(power.mul(symbol));
        }
    }
    Ok(combined)
}

/// Exact lazy kernel for the two QM31 helper lanes.
///
/// The C1 byte dot is unchanged. Both helper symbols are decoded in the same
/// helper-major order as [`gamma_combine_state_only_layer0_prepared`], then
/// each slot uses one lazy two-product accumulator. This preserves all field
/// products and canonicality checks while reducing the helper block from 18
/// to 9 M31 reductions per slot.
pub fn gamma_combine_state_only_layer0_helpers_dot2_candidate(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    powers: &StateOnlyQueryPowers,
) -> Result<[QM31; STATE_ONLY_FIBER_SLOTS], CircleQueryError> {
    if c1_leaf.len() != STATE_ONLY_C1_LEAF_BYTES {
        return Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C1,
            expected: STATE_ONLY_C1_LEAF_BYTES,
            actual: c1_leaf.len(),
        });
    }
    if c2_leaf.len() != STATE_ONLY_C2_LEAF_BYTES {
        return Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C2,
            expected: STATE_ONLY_C2_LEAF_BYTES,
            actual: c2_leaf.len(),
        });
    }

    let mut combined = qm31_m31_dot4_prepared_limbs_4b2_bytes(&powers.c1_limbs, c1_leaf)
        .ok_or_else(|| canonical_m31_leaf_error(c1_leaf))?;
    let mut helpers = [[QM31::ZERO; STATE_ONLY_FIBER_SLOTS]; STATE_ONLY_C2_COLUMNS];
    for (helper, symbols) in helpers.iter_mut().enumerate() {
        for (slot, symbol) in symbols.iter_mut().enumerate() {
            let offset = state_only_c2_symbol_offset(helper, slot).unwrap();
            *symbol = QM31::from_le_bytes(&c2_leaf[offset..offset + STATE_ONLY_QM31_BYTES]).ok_or(
                CircleQueryError::NonCanonicalQm31 {
                    leaf: CircleQueryLeaf::C2,
                    offset,
                },
            )?;
        }
    }
    for (slot, value) in combined.iter_mut().enumerate() {
        *value = value.add(qm31_sum_products2_prepared(
            &powers.helpers,
            &[helpers[0][slot], helpers[1][slot]],
        ));
    }
    Ok(combined)
}

pub fn gamma_combine_state_only_layer0(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    gamma: QM31,
) -> Result<[QM31; STATE_ONLY_FIBER_SLOTS], CircleQueryError> {
    gamma_combine_state_only_layer0_prepared(c1_leaf, c2_leaf, &StateOnlyQueryPowers::new(gamma))
}

/// Decode the width-28 state-only fiber and check its first normalized fold
/// against an authenticated layer-one leaf. The remaining fold layers are
/// width-independent and use the existing circle query checker.
pub fn check_state_only_layer0_transition_prepared_for_fiber_count(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    layer1_leaf: &[u8],
    query: usize,
    fiber_count: usize,
    powers: &StateOnlyQueryPowers,
    inverses: [M31; 2],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    let combined = gamma_combine_state_only_layer0_prepared(c1_leaf, c2_leaf, powers)?;
    crate::circle_query::check_combined_layer0_transition_prepared_for_fiber_count(
        combined,
        layer1_leaf,
        query,
        fiber_count,
        inverses,
        alpha,
        alpha_squared,
    )
}

/// Production polynomial-basis form of the same authenticated layer-zero
/// transition. It changes only the reduction schedule for the identical
/// cubic fold polynomial.
pub fn check_state_only_layer0_transition_prepared_polynomial_for_fiber_count(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    layer1_leaf: &[u8],
    query: usize,
    fiber_count: usize,
    powers: &StateOnlyQueryPowers,
    inverses: [M31; 2],
    alpha: PreparedQm31Multiplier,
    alpha_squared: PreparedQm31Multiplier,
    alpha_cubed: PreparedQm31Multiplier,
) -> Result<(), CircleQueryError> {
    let combined = gamma_combine_state_only_layer0_prepared(c1_leaf, c2_leaf, powers)?;
    crate::circle_query::check_combined_layer0_transition_prepared_polynomial_for_fiber_count(
        combined,
        layer1_leaf,
        query,
        fiber_count,
        inverses,
        alpha,
        alpha_squared,
        alpha_cubed,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, M31, P};

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

    #[test]
    fn state_only_layer0_matches_the_literal_twenty_eight_term_generator() {
        let mut state = 0x16c1_0012_5eed_0042u64;
        for _ in 0..48 {
            let gamma = next_qm31(&mut state);
            let powers = qm31_power_table::<STATE_ONLY_TOTAL_COLUMNS>(gamma);
            let mut c1 = [0u8; STATE_ONLY_C1_LEAF_BYTES];
            let mut c2 = [0u8; STATE_ONLY_C2_LEAF_BYTES];
            let mut expected = [QM31::ZERO; STATE_ONLY_FIBER_SLOTS];
            for (slot, expected_slot) in expected.iter_mut().enumerate() {
                for column in 0..STATE_ONLY_C1_COLUMNS {
                    let value = next_m31(&mut state);
                    let offset = state_only_c1_symbol_offset(slot, column).unwrap();
                    c1[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
                    *expected_slot = expected_slot.add(powers[column].mul_m31(value));
                }
            }
            for helper in 0..STATE_ONLY_C2_COLUMNS {
                for (slot, expected_slot) in expected.iter_mut().enumerate() {
                    let value = next_qm31(&mut state);
                    let offset = state_only_c2_symbol_offset(helper, slot).unwrap();
                    value.write_le_bytes(&mut c2[offset..offset + STATE_ONLY_QM31_BYTES]);
                    *expected_slot =
                        expected_slot.add(powers[STATE_ONLY_C1_COLUMNS + helper].mul(value));
                }
            }
            assert_eq!(
                gamma_combine_state_only_layer0(&c1, &c2, gamma),
                Ok(expected)
            );
            let prepared = StateOnlyQueryPowers::new(gamma);
            assert_eq!(
                gamma_combine_state_only_layer0_prepared(&c1, &c2, &prepared),
                gamma_combine_state_only_layer0_legacy_reference(&c1, &c2, &prepared)
            );
        }
    }

    #[test]
    fn state_only_layer0_rejects_lengths_and_every_noncanonical_field_kind() {
        let powers = StateOnlyQueryPowers::new(QM31::ONE);
        let mut c1 = [0u8; STATE_ONLY_C1_LEAF_BYTES];
        let mut c2 = [0u8; STATE_ONLY_C2_LEAF_BYTES];
        assert!(matches!(
            gamma_combine_state_only_layer0_prepared(&c1[..c1.len() - 1], &c2, &powers),
            Err(CircleQueryError::LeafLength {
                leaf: CircleQueryLeaf::C1,
                ..
            })
        ));
        assert_eq!(
            gamma_combine_state_only_layer0_legacy_reference(&c1[..c1.len() - 1], &c2, &powers,),
            gamma_combine_state_only_layer0_prepared(&c1[..c1.len() - 1], &c2, &powers),
        );
        let c1_tail = c1.len() - 4;
        c1[c1_tail..].copy_from_slice(&P.to_le_bytes());
        assert!(matches!(
            gamma_combine_state_only_layer0_prepared(&c1, &c2, &powers),
            Err(CircleQueryError::NonCanonicalM31 { .. })
        ));
        assert_eq!(
            gamma_combine_state_only_layer0_legacy_reference(&c1, &c2, &powers),
            gamma_combine_state_only_layer0_prepared(&c1, &c2, &powers),
        );
        c1[c1_tail..].copy_from_slice(&0u32.to_le_bytes());
        let offset = state_only_c2_symbol_offset(1, 3).unwrap();
        c2[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            gamma_combine_state_only_layer0_prepared(&c1, &c2, &powers),
            Err(CircleQueryError::NonCanonicalQm31 {
                leaf: CircleQueryLeaf::C2,
                offset,
            })
        );
        assert_eq!(
            gamma_combine_state_only_layer0_legacy_reference(&c1, &c2, &powers),
            gamma_combine_state_only_layer0_prepared(&c1, &c2, &powers),
        );
    }
}
