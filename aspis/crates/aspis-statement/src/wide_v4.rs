//! Exact-width arithmetic seam for the candidate v4 wide layer-zero fiber.
//!
//! This module only recombines already-decoded field elements. It does not
//! parse or authenticate a proof, hash a leaf, enforce a statement, or make
//! a soundness/payment claim.

use aspis_core::field::{
    qm31_cm31_dot, qm31_cm31_dot4, qm31_cm31_dot4_prepared, qm31_cm31_dot4_prepared_bytes,
    qm31_power_table, PreparedQm31Cm31Weights, CM31, QM31,
};

/// C1 columns in the frozen arithmetic shape, including the multiplicity
/// column as the final entry.
pub const C1_COLUMNS: usize = 49;
/// Challenge-dependent helper columns in the single C2 fiber.
pub const C2_COLUMNS: usize = 2;
/// Total gamma-RLC width.
pub const TOTAL_COLUMNS: usize = C1_COLUMNS + C2_COLUMNS;
pub const FIBER_SLOTS: usize = 4;
pub const C1_FIBER_BYTES: usize = C1_COLUMNS * FIBER_SLOTS * 8;
pub const C2_FIBER_BYTES: usize = C2_COLUMNS * FIBER_SLOTS * 16;

/// Four circle-code slots for 49 CM31 C1 columns and two QM31 C2 columns.
/// Arrays are slot-major so each slot is directly consumable by a dot kernel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactWideFiber {
    pub c1: [[CM31; C1_COLUMNS]; FIBER_SLOTS],
    pub c2: [[QM31; C2_COLUMNS]; FIBER_SLOTS],
}

/// Gamma powers and Karatsuba limbs prepared once, then reused by every
/// authenticated query fiber in the proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactWideWeights {
    c1: PreparedQm31Cm31Weights<C1_COLUMNS>,
    helpers: [QM31; C2_COLUMNS],
}

pub fn prepare_exact_wide_weights(gamma: QM31) -> ExactWideWeights {
    let (c1, gamma_49) = PreparedQm31Cm31Weights::geometric(gamma);
    let helpers = [gamma_49, gamma_49.mul(gamma)];
    ExactWideWeights { c1, helpers }
}

/// Reference composition using four independent CM31 dot-product calls.
pub fn combine_exact_wide_fiber_baseline(
    fiber: &ExactWideFiber,
    gamma: QM31,
) -> [QM31; FIBER_SLOTS] {
    let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
    core::array::from_fn(|slot| {
        qm31_cm31_dot(&powers[..C1_COLUMNS], &fiber.c1[slot])
            .add(powers[C1_COLUMNS].mul(fiber.c2[slot][0]))
            .add(powers[C1_COLUMNS + 1].mul(fiber.c2[slot][1]))
    })
}

/// Fused composition sharing the C1 gamma weights across all four slots.
pub fn combine_exact_wide_fiber(fiber: &ExactWideFiber, gamma: QM31) -> [QM31; FIBER_SLOTS] {
    let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
    let mut combined = qm31_cm31_dot4(
        &powers[..C1_COLUMNS],
        [&fiber.c1[0], &fiber.c1[1], &fiber.c1[2], &fiber.c1[3]],
    );
    for (slot, value) in combined.iter_mut().enumerate() {
        *value = value
            .add(powers[C1_COLUMNS].mul(fiber.c2[slot][0]))
            .add(powers[C1_COLUMNS + 1].mul(fiber.c2[slot][1]));
    }
    combined
}

/// Exact-wide composition with challenge-dependent factors prepared once per
/// proof. Callers should reuse `weights` across all unique opened fibers.
pub fn combine_exact_wide_fiber_prepared(
    fiber: &ExactWideFiber,
    weights: &ExactWideWeights,
) -> [QM31; FIBER_SLOTS] {
    let mut combined = qm31_cm31_dot4_prepared(
        &weights.c1,
        [&fiber.c1[0], &fiber.c1[1], &fiber.c1[2], &fiber.c1[3]],
    );
    for (slot, value) in combined.iter_mut().enumerate() {
        *value = value
            .add(weights.helpers[0].mul(fiber.c2[slot][0]))
            .add(weights.helpers[1].mul(fiber.c2[slot][1]));
    }
    combined
}

/// Parse and combine the exact wire fibers without materializing a 1,696-byte
/// matrix. C1 is slot-major CM31; C2 is helper-major QM31. Every field limb
/// must be canonical.
pub fn combine_exact_wide_bytes_prepared(
    c1_bytes: &[u8],
    c2_bytes: &[u8],
    weights: &ExactWideWeights,
) -> Option<[QM31; FIBER_SLOTS]> {
    if c1_bytes.len() != C1_FIBER_BYTES || c2_bytes.len() != C2_FIBER_BYTES {
        return None;
    }
    let mut combined = qm31_cm31_dot4_prepared_bytes(&weights.c1, c1_bytes)?;
    for helper in 0..C2_COLUMNS {
        for (slot, value) in combined.iter_mut().enumerate() {
            let offset = (helper * FIBER_SLOTS + slot) * 16;
            let helper_value = QM31::from_le_bytes(&c2_bytes[offset..offset + 16])?;
            *value = value.add(weights.helpers[helper].mul(helper_value));
        }
    }
    Some(combined)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{M31, P};

    fn next(state: &mut u64) -> M31 {
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
    }

    fn cm31(state: &mut u64) -> CM31 {
        CM31::new(next(state), next(state))
    }

    fn qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: cm31(state),
            c1: cm31(state),
        }
    }

    fn fiber(seed: u64) -> ExactWideFiber {
        let mut state = seed;
        ExactWideFiber {
            c1: core::array::from_fn(|_| core::array::from_fn(|_| cm31(&mut state))),
            c2: core::array::from_fn(|_| core::array::from_fn(|_| qm31(&mut state))),
        }
    }

    #[test]
    fn exact_shape_constants_are_pinned() {
        assert_eq!(C1_COLUMNS, 49);
        assert_eq!(C2_COLUMNS, 2);
        assert_eq!(TOTAL_COLUMNS, 51);
        assert_eq!(C1_FIBER_BYTES, 1_568);
        assert_eq!(C2_FIBER_BYTES, 128);
    }

    #[test]
    fn helper_columns_use_gamma_powers_49_and_50() {
        let mut exact = ExactWideFiber {
            c1: [[CM31::ZERO; C1_COLUMNS]; FIBER_SLOTS],
            c2: [[QM31::ZERO; C2_COLUMNS]; FIBER_SLOTS],
        };
        exact.c2[0] = [QM31::ONE, QM31::ONE];
        let gamma = qm31(&mut 17u64);
        let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
        let combined = combine_exact_wide_fiber(&exact, gamma);
        assert_eq!(combined[0], powers[49].add(powers[50]));
        assert_eq!(combined[1..], [QM31::ZERO; 3]);
    }

    #[test]
    fn fused_and_baseline_match_on_deterministic_vectors() {
        for seed in 1..=32u64 {
            let exact = fiber(seed.wrapping_mul(0x9e37_79b9));
            let gamma = qm31(&mut seed.wrapping_mul(0xd1b5_4a32));
            assert_eq!(
                combine_exact_wide_fiber(&exact, gamma),
                combine_exact_wide_fiber_baseline(&exact, gamma),
                "seed {seed}"
            );
        }
    }

    #[test]
    fn prepared_weights_match_fused_across_many_fibers() {
        for gamma_seed in 1..=8u64 {
            let gamma = qm31(&mut gamma_seed.wrapping_mul(0xd1b5_4a32));
            let weights = prepare_exact_wide_weights(gamma);
            for fiber_seed in 1..=16u64 {
                let exact = fiber(
                    gamma_seed
                        .wrapping_mul(0x9e37_79b9)
                        .wrapping_add(fiber_seed),
                );
                assert_eq!(
                    combine_exact_wide_fiber_prepared(&exact, &weights),
                    combine_exact_wide_fiber(&exact, gamma)
                );
            }
        }
    }

    #[test]
    fn prepared_byte_path_matches_structured_path_and_rejects_bad_limbs() {
        let gamma = qm31(&mut 0xd1b5_4a32_d192_ed03u64);
        let weights = prepare_exact_wide_weights(gamma);
        let exact = fiber(0x9e37_79b9_7f4a_7c15);
        let mut c1 = alloc::vec![0u8; C1_FIBER_BYTES];
        let mut c2 = alloc::vec![0u8; C2_FIBER_BYTES];
        for slot in 0..FIBER_SLOTS {
            for column in 0..C1_COLUMNS {
                exact.c1[slot][column]
                    .write_le_bytes(&mut c1[(slot * C1_COLUMNS + column) * 8..][..8]);
            }
        }
        for helper in 0..C2_COLUMNS {
            for slot in 0..FIBER_SLOTS {
                exact.c2[slot][helper]
                    .write_le_bytes(&mut c2[(helper * FIBER_SLOTS + slot) * 16..][..16]);
            }
        }
        assert_eq!(
            combine_exact_wide_bytes_prepared(&c1, &c2, &weights),
            Some(combine_exact_wide_fiber_prepared(&exact, &weights))
        );

        c1[0..4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
        assert_eq!(combine_exact_wide_bytes_prepared(&c1, &c2, &weights), None);
        exact.c1[0][0].write_le_bytes(&mut c1[..8]);
        c2[12..16].copy_from_slice(&aspis_core::field::P.to_le_bytes());
        assert_eq!(combine_exact_wide_bytes_prepared(&c1, &c2, &weights), None);
    }
}
