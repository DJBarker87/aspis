//! Fused three-point relation preparation for the experimental state-only
//! profile.
//!
//! The proof carries 28 canonical QM31 values at each of `z`, `succ(z)`, and
//! `xor12(z)`. This kernel decodes all 84 values, computes the three ordinary
//! scalar-generator claims, and retains the same powers in the exact N16
//! query representation.

use crate::field::{CM31, M31, P, QM31};
use crate::state_only_query::{StateOnlyQueryPowers, STATE_ONLY_TOTAL_COLUMNS};

pub const STATE_ONLY_RELATION_POINTS: usize = 3;
pub const STATE_ONLY_STATEMENT_VALUES: usize =
    STATE_ONLY_RELATION_POINTS * STATE_ONLY_TOTAL_COLUMNS;
pub const STATE_ONLY_STATEMENT_BYTES: usize = STATE_ONLY_STATEMENT_VALUES * 16;

const COMPONENTS: usize = 3;
const CHANNELS: usize = 3;
const PRODUCT_CHANNELS: usize = COMPONENTS * CHANNELS;
const PRODUCTS_PER_REDUCTION: usize = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyRelationPrepared {
    pub claims: [QM31; STATE_ONLY_RELATION_POINTS],
    pub query_powers: StateOnlyQueryPowers,
}

#[inline(always)]
fn components(value: QM31) -> [[M31; CHANNELS]; COMPONENTS] {
    let prepare = |component: CM31| [component.a, component.b, component.a.add(component.b)];
    [
        prepare(value.c0),
        prepare(value.c1),
        prepare(value.c0.add(value.c1)),
    ]
}

#[inline(always)]
fn mul_by_r(value: CM31) -> CM31 {
    CM31 {
        a: value.a.double().sub(value.b),
        b: value.a.add(value.b.double()),
    }
}

#[inline(always)]
fn finish(channels: [u64; PRODUCT_CHANNELS]) -> QM31 {
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
        let offset = limb * 4;
        let raw = u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap());
        *invalid |= u32::from(raw >= P);
        *output = M31(raw & P);
    }
    QM31 {
        c0: CM31::new(limbs[0], limbs[1]),
        c1: CM31::new(limbs[2], limbs[3]),
    }
}

/// Decode and gamma-combine all state-only statement values in one traversal.
/// Input order is point-major, then column-major within each point.
pub fn prepare_state_only_relation(gamma: QM31, bytes: &[u8]) -> Option<StateOnlyRelationPrepared> {
    if bytes.len() != STATE_ONLY_STATEMENT_BYTES {
        return None;
    }

    let mut invalid = 0u32;
    let mut outer = [[0u64; PRODUCT_CHANNELS]; STATE_ONLY_RELATION_POINTS];
    let mut powers = [QM31::ZERO; STATE_ONLY_TOTAL_COLUMNS];
    let mut power = QM31::ONE;

    for block_start in (0..STATE_ONLY_TOTAL_COLUMNS).step_by(PRODUCTS_PER_REDUCTION) {
        let block_end = core::cmp::min(
            block_start + PRODUCTS_PER_REDUCTION,
            STATE_ONLY_TOTAL_COLUMNS,
        );
        let mut raw = [[0u64; PRODUCT_CHANNELS]; STATE_ONLY_RELATION_POINTS];
        for column in block_start..block_end {
            powers[column] = power;
            let weight = components(power);
            for (point, raw_point) in raw.iter_mut().enumerate() {
                let value_index = point * STATE_ONLY_TOTAL_COLUMNS + column;
                let offset = value_index * 16;
                let value = components(decode_qm31_masked(
                    &bytes[offset..offset + 16],
                    &mut invalid,
                ));
                for component in 0..COMPONENTS {
                    for channel in 0..CHANNELS {
                        raw_point[component * CHANNELS + channel] +=
                            u64::from(weight[component][channel].0)
                                * u64::from(value[component][channel].0);
                    }
                }
            }
            if column + 1 != STATE_ONLY_TOTAL_COLUMNS {
                power = power.mul(gamma);
            }
        }
        for point in 0..STATE_ONLY_RELATION_POINTS {
            for channel in 0..PRODUCT_CHANNELS {
                outer[point][channel] += u64::from(M31::reduce_u64(raw[point][channel]).0);
            }
        }
    }

    if invalid != 0 {
        return None;
    }
    Some(StateOnlyRelationPrepared {
        claims: outer.map(finish),
        query_powers: StateOnlyQueryPowers::from_full_table(&powers),
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

    fn encode(
        values: &[[QM31; STATE_ONLY_TOTAL_COLUMNS]; STATE_ONLY_RELATION_POINTS],
    ) -> [u8; STATE_ONLY_STATEMENT_BYTES] {
        let mut bytes = [0u8; STATE_ONLY_STATEMENT_BYTES];
        for (point, row) in values.iter().enumerate() {
            for (column, value) in row.iter().enumerate() {
                let index = point * STATE_ONLY_TOTAL_COLUMNS + column;
                value.write_le_bytes(&mut bytes[index * 16..][..16]);
            }
        }
        bytes
    }

    #[test]
    fn fused_three_point_relation_matches_three_literal_dots() {
        let mut state = 0x18c1_0003_f05e_5eedu64;
        for _ in 0..96 {
            let gamma = next_qm31(&mut state);
            let values: [[QM31; STATE_ONLY_TOTAL_COLUMNS]; STATE_ONLY_RELATION_POINTS] =
                core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state)));
            let powers = qm31_power_table::<STATE_ONLY_TOTAL_COLUMNS>(gamma);
            let prepared = prepare_state_only_relation(gamma, &encode(&values)).unwrap();
            assert_eq!(prepared.claims, values.map(|row| qm31_dot(&powers, &row)));
            assert_eq!(
                prepared.query_powers,
                StateOnlyQueryPowers::from_full_table(&powers)
            );
        }
    }

    #[test]
    fn fused_three_point_relation_rejects_every_noncanonical_limb_position() {
        let values = [[QM31::ZERO; STATE_ONLY_TOTAL_COLUMNS]; STATE_ONLY_RELATION_POINTS];
        let clean = encode(&values);
        assert!(prepare_state_only_relation(QM31::ONE, &clean).is_some());
        for limb in 0..STATE_ONLY_STATEMENT_VALUES * 4 {
            let mut corrupt = clean;
            corrupt[limb * 4..limb * 4 + 4].copy_from_slice(&P.to_le_bytes());
            assert!(
                prepare_state_only_relation(QM31::ONE, &corrupt).is_none(),
                "accepted noncanonical limb {limb}"
            );
        }
        assert!(prepare_state_only_relation(QM31::ONE, &clean[..clean.len() - 1]).is_none());
    }
}
