//! Layer-zero recombination for quarantined spend.
//!
//! C1 and H/G retain their frozen indices.  One QM31 D lane is appended at
//! generator 28, so the C2 leaf is `H[4] || G[4] || D[4]` (192 bytes).

use crate::circle_query::{CircleQueryError, CircleQueryLeaf};
use crate::field::{qm31_power_table, PreparedQm31Multiplier, QM31};
use crate::state_only_query::{
    gamma_combine_state_only_layer0_prepared, StateOnlyQueryPowers, STATE_ONLY_C1_LEAF_BYTES,
    STATE_ONLY_C2_LEAF_BYTES, STATE_ONLY_FIBER_SLOTS, STATE_ONLY_TOTAL_COLUMNS,
};

pub const SPEND_C2_COLUMNS: usize = 3;
pub const SPEND_TOTAL_COLUMNS: usize = STATE_ONLY_TOTAL_COLUMNS + 1;
pub const SPEND_C2_LEAF_BYTES: usize = SPEND_C2_COLUMNS * STATE_ONLY_FIBER_SLOTS * 16;
pub const SPEND_D_GENERATOR_INDEX: usize = SPEND_TOTAL_COLUMNS - 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlySpendQueryPowers {
    pub base: StateOnlyQueryPowers,
    pub d: PreparedQm31Multiplier,
}

impl StateOnlySpendQueryPowers {
    pub fn new(gamma: QM31) -> Self {
        let powers = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma);
        let base_powers: [QM31; STATE_ONLY_TOTAL_COLUMNS] =
            core::array::from_fn(|index| powers[index]);
        Self {
            base: StateOnlyQueryPowers::from_full_table(&base_powers),
            d: PreparedQm31Multiplier::new(powers[SPEND_D_GENERATOR_INDEX]),
        }
    }

    pub fn from_base_and_d(base: StateOnlyQueryPowers, d_power: QM31) -> Self {
        Self {
            base,
            d: PreparedQm31Multiplier::new(d_power),
        }
    }
}

pub const fn spend_d_symbol_offset(slot: usize) -> Option<usize> {
    if slot < STATE_ONLY_FIBER_SLOTS {
        Some(STATE_ONLY_C2_LEAF_BYTES + slot * 16)
    } else {
        None
    }
}

pub fn gamma_combine_state_only_spend_layer0_prepared(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    powers: &StateOnlySpendQueryPowers,
) -> Result<[QM31; STATE_ONLY_FIBER_SLOTS], CircleQueryError> {
    if c1_leaf.len() != STATE_ONLY_C1_LEAF_BYTES {
        return Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C1,
            expected: STATE_ONLY_C1_LEAF_BYTES,
            actual: c1_leaf.len(),
        });
    }
    if c2_leaf.len() != SPEND_C2_LEAF_BYTES {
        return Err(CircleQueryError::LeafLength {
            leaf: CircleQueryLeaf::C2,
            expected: SPEND_C2_LEAF_BYTES,
            actual: c2_leaf.len(),
        });
    }
    let mut combined = gamma_combine_state_only_layer0_prepared(
        c1_leaf,
        &c2_leaf[..STATE_ONLY_C2_LEAF_BYTES],
        &powers.base,
    )?;
    for (slot, output) in combined.iter_mut().enumerate() {
        let offset = spend_d_symbol_offset(slot).unwrap();
        let value = QM31::from_le_bytes(&c2_leaf[offset..offset + 16]).ok_or(
            CircleQueryError::NonCanonicalQm31 {
                leaf: CircleQueryLeaf::C2,
                offset,
            },
        )?;
        *output = output.add(powers.d.mul(value));
    }
    Ok(combined)
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
    fn appended_d_matches_literal_twenty_ninth_term() {
        let mut state = 0x2300_d00d_5100_1ee7;
        for _ in 0..32 {
            let gamma = next_qm31(&mut state);
            let powers = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma);
            let mut c1 = [0u8; STATE_ONLY_C1_LEAF_BYTES];
            let mut c2 = [0u8; SPEND_C2_LEAF_BYTES];
            let mut expected = [QM31::ZERO; STATE_ONLY_FIBER_SLOTS];
            for slot in 0..STATE_ONLY_FIBER_SLOTS {
                for column in 0..crate::state_only_query::STATE_ONLY_C1_COLUMNS {
                    let value = next_m31(&mut state);
                    let offset =
                        (slot * crate::state_only_query::STATE_ONLY_C1_COLUMNS + column) * 4;
                    c1[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
                    expected[slot] = expected[slot].add(powers[column].mul_m31(value));
                }
                for helper in 0..SPEND_C2_COLUMNS {
                    let value = next_qm31(&mut state);
                    let offset = (helper * STATE_ONLY_FIBER_SLOTS + slot) * 16;
                    value.write_le_bytes(&mut c2[offset..offset + 16]);
                    expected[slot] = expected[slot].add(
                        powers[crate::state_only_query::STATE_ONLY_C1_COLUMNS + helper].mul(value),
                    );
                }
            }
            assert_eq!(
                gamma_combine_state_only_spend_layer0_prepared(
                    &c1,
                    &c2,
                    &StateOnlySpendQueryPowers::new(gamma),
                ),
                Ok(expected)
            );
        }
    }

    // Teeth vector for the D-lane discharge (paper: fact (S2) of def:d-coupling,
    // used by lem:d-lane-rbr). The D word enters the layer-zero recombination
    // ONLY through the gamma^28 addend: changing only the D symbols shifts each
    // slot by exactly powers[28] * delta_D and touches nothing else. This is the
    // "zero coupling" the soundness proof of the zero-factor D lane rests on.
    #[test]
    fn d_lane_couples_only_through_gamma_28_addend() {
        let mut state = 0xd1a1_c0de_0000_d00d;
        for _ in 0..16 {
            let gamma = next_qm31(&mut state);
            let powers = StateOnlySpendQueryPowers::new(gamma);
            let gamma_28 = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma)[SPEND_D_GENERATOR_INDEX];

            let mut c1 = [0u8; STATE_ONLY_C1_LEAF_BYTES];
            for slot in 0..STATE_ONLY_FIBER_SLOTS {
                for column in 0..crate::state_only_query::STATE_ONLY_C1_COLUMNS {
                    let offset =
                        (slot * crate::state_only_query::STATE_ONLY_C1_COLUMNS + column) * 4;
                    c1[offset..offset + 4].copy_from_slice(&next_m31(&mut state).to_le_bytes());
                }
            }
            // Two C2 leaves identical except in the D symbols.
            let mut c2_a = [0u8; SPEND_C2_LEAF_BYTES];
            for helper in 0..SPEND_C2_COLUMNS {
                for slot in 0..STATE_ONLY_FIBER_SLOTS {
                    let offset = (helper * STATE_ONLY_FIBER_SLOTS + slot) * 16;
                    next_qm31(&mut state).write_le_bytes(&mut c2_a[offset..offset + 16]);
                }
            }
            let mut c2_b = c2_a;
            let mut delta_d = [QM31::ZERO; STATE_ONLY_FIBER_SLOTS];
            for slot in 0..STATE_ONLY_FIBER_SLOTS {
                let offset = spend_d_symbol_offset(slot).unwrap();
                let old = QM31::from_le_bytes(&c2_a[offset..offset + 16]).unwrap();
                let new = next_qm31(&mut state);
                new.write_le_bytes(&mut c2_b[offset..offset + 16]);
                delta_d[slot] = new.sub(old);
            }

            let out_a =
                gamma_combine_state_only_spend_layer0_prepared(&c1, &c2_a, &powers).unwrap();
            let out_b =
                gamma_combine_state_only_spend_layer0_prepared(&c1, &c2_b, &powers).unwrap();
            for slot in 0..STATE_ONLY_FIBER_SLOTS {
                assert_eq!(out_b[slot].sub(out_a[slot]), gamma_28.mul(delta_d[slot]));
            }
        }
    }
}
