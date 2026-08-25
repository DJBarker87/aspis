//! V7 Phase-1 reference algebra for the split-tensor lane restriction.
//!
//! The committed lane tables contain Boolean subset-zeta values over M31.
//! Their multilinear extensions are evaluated in the deployed QM31 tower.
//! This module has no transcript, Merkle, PCS, or production-verifier surface;
//! it is the small executable oracle that must be proved before integration.

use crate::field::{CM31, M31, QM31};
use crate::v7_profile::{
    COMBINED_LANES, QM31_LIMBS, STAGE_A_LANE_VARIABLES, STAGE_A_PADDED_LANES, STAGE_A_SOURCE_LANES,
    STAGE_B_LANE_VARIABLES, STAGE_B_OUTER_GAMMA_POWER, STAGE_B_PADDED_LANES, STAGE_B_QM31_LANES,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZetaError {
    EmptyTable,
    LengthNotPowerOfTwo,
    DimensionMismatch,
}

pub const QM31_I: QM31 = QM31 {
    c0: CM31 {
        a: M31::ZERO,
        b: M31::ONE,
    },
    c1: CM31::ZERO,
};

pub const QM31_U: QM31 = QM31 {
    c0: CM31::ZERO,
    c1: CM31::ONE,
};

#[inline(always)]
pub const fn qm31_from_limbs(limbs: [M31; QM31_LIMBS]) -> QM31 {
    QM31 {
        c0: CM31 {
            a: limbs[0],
            b: limbs[1],
        },
        c1: CM31 {
            a: limbs[2],
            b: limbs[3],
        },
    }
}

#[inline(always)]
pub const fn qm31_limbs(value: QM31) -> [M31; QM31_LIMBS] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

#[inline(always)]
fn lift_m31(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

fn validate_power_of_two_length(length: usize) -> Result<(), ZetaError> {
    if length == 0 {
        Err(ZetaError::EmptyTable)
    } else if !length.is_power_of_two() {
        Err(ZetaError::LengthNotPowerOfTwo)
    } else {
        Ok(())
    }
}

/// In-place Boolean subset-zeta transform:
/// `table[B] = sum_{S subseteq B} coefficients[S]`.
pub fn zeta_in_place_m31(table: &mut [M31]) -> Result<(), ZetaError> {
    validate_power_of_two_length(table.len())?;
    let mut bit = 1usize;
    while bit < table.len() {
        let mut mask = 0usize;
        while mask < table.len() {
            if mask & bit != 0 {
                table[mask] = table[mask].add(table[mask ^ bit]);
            }
            mask += 1;
        }
        bit <<= 1;
    }
    Ok(())
}

/// Exact inverse of [`zeta_in_place_m31`].
pub fn mobius_in_place_m31(table: &mut [M31]) -> Result<(), ZetaError> {
    validate_power_of_two_length(table.len())?;
    let mut bit = 1usize;
    while bit < table.len() {
        let mut mask = 0usize;
        while mask < table.len() {
            if mask & bit != 0 {
                table[mask] = table[mask].sub(table[mask ^ bit]);
            }
            mask += 1;
        }
        bit <<= 1;
    }
    Ok(())
}

fn expected_table_length(dimension: usize) -> Result<usize, ZetaError> {
    1usize
        .checked_shl(dimension as u32)
        .ok_or(ZetaError::DimensionMismatch)
}

/// Evaluate the multilinear extension of a Boolean table over QM31.
pub fn evaluate_mle_zeta<const N: usize>(
    table: &[M31; N],
    point: &[QM31],
) -> Result<QM31, ZetaError> {
    validate_power_of_two_length(N)?;
    if expected_table_length(point.len())? != N {
        return Err(ZetaError::DimensionMismatch);
    }

    let mut scratch = [QM31::ZERO; N];
    let mut index = 0usize;
    while index < N {
        scratch[index] = lift_m31(table[index]);
        index += 1;
    }

    let mut active = N;
    for coordinate in point {
        let half = active / 2;
        let mut pair = 0usize;
        while pair < half {
            let low = scratch[2 * pair];
            let high = scratch[2 * pair + 1];
            scratch[pair] = low.add(coordinate.mul(high.sub(low)));
            pair += 1;
        }
        active = half;
    }
    Ok(scratch[0])
}

/// Literal monomial evaluation of pre-zeta coefficients.  This intentionally
/// uses a different loop shape from [`evaluate_mle_zeta`] for differential
/// checking.
pub fn evaluate_monomial_coefficients<const N: usize>(
    coefficients: &[M31; N],
    point: &[QM31],
) -> Result<QM31, ZetaError> {
    validate_power_of_two_length(N)?;
    if expected_table_length(point.len())? != N {
        return Err(ZetaError::DimensionMismatch);
    }

    let mut result = QM31::ZERO;
    let mut mask = 0usize;
    while mask < N {
        let mut term = lift_m31(coefficients[mask]);
        let mut bit = 0usize;
        while bit < point.len() {
            if mask & (1usize << bit) != 0 {
                term = term.mul(point[bit]);
            }
            bit += 1;
        }
        result = result.add(term);
        mask += 1;
    }
    Ok(result)
}

pub fn stage_a_coefficients(source: &[M31; STAGE_A_SOURCE_LANES]) -> [M31; STAGE_A_PADDED_LANES] {
    let mut coefficients = [M31::ZERO; STAGE_A_PADDED_LANES];
    coefficients[..STAGE_A_SOURCE_LANES].copy_from_slice(source);
    coefficients
}

pub fn stage_a_zeta_table(source: &[M31; STAGE_A_SOURCE_LANES]) -> [M31; STAGE_A_PADDED_LANES] {
    let mut table = stage_a_coefficients(source);
    zeta_in_place_m31(&mut table).expect("fixed Stage-A table is power-of-two");
    table
}

/// Flatten three QM31 lanes as `(c0.a,c0.b,c1.a,c1.b)` with basis index in
/// the low two bits and source-lane index in the high two bits.
pub fn stage_b_coefficients(source: &[QM31; STAGE_B_QM31_LANES]) -> [M31; STAGE_B_PADDED_LANES] {
    let mut coefficients = [M31::ZERO; STAGE_B_PADDED_LANES];
    let mut lane = 0usize;
    while lane < STAGE_B_QM31_LANES {
        let limbs = qm31_limbs(source[lane]);
        coefficients[lane * QM31_LIMBS..(lane + 1) * QM31_LIMBS].copy_from_slice(&limbs);
        lane += 1;
    }
    coefficients
}

pub fn stage_b_zeta_table(source: &[QM31; STAGE_B_QM31_LANES]) -> [M31; STAGE_B_PADDED_LANES] {
    let mut table = stage_b_coefficients(source);
    zeta_in_place_m31(&mut table).expect("fixed Stage-B table is power-of-two");
    table
}

pub fn stage_a_lane_point(gamma: QM31) -> [QM31; STAGE_A_LANE_VARIABLES] {
    let gamma2 = gamma.square();
    let gamma4 = gamma2.square();
    let gamma8 = gamma4.square();
    let gamma16 = gamma8.square();
    [gamma, gamma2, gamma4, gamma8, gamma16]
}

pub fn stage_b_lane_point(gamma: QM31) -> [QM31; STAGE_B_LANE_VARIABLES] {
    [QM31_I, QM31_U, gamma, gamma.square()]
}

pub fn stage_a_restriction(table: &[M31; STAGE_A_PADDED_LANES], gamma: QM31) -> QM31 {
    evaluate_mle_zeta(table, &stage_a_lane_point(gamma)).expect("fixed Stage-A dimensions agree")
}

pub fn stage_b_restriction(table: &[M31; STAGE_B_PADDED_LANES], gamma: QM31) -> QM31 {
    evaluate_mle_zeta(table, &stage_b_lane_point(gamma)).expect("fixed Stage-B dimensions agree")
}

pub fn split_tensor_restriction(
    stage_a_table: &[M31; STAGE_A_PADDED_LANES],
    stage_b_table: &[M31; STAGE_B_PADDED_LANES],
    gamma: QM31,
) -> QM31 {
    stage_a_restriction(stage_a_table, gamma).add(
        gamma
            .pow(STAGE_B_OUTER_GAMMA_POWER)
            .mul(stage_b_restriction(stage_b_table, gamma)),
    )
}

/// Literal V6 width-29 gamma batch in the selected lane order.
pub fn width29_batch(
    stage_a_source: &[M31; STAGE_A_SOURCE_LANES],
    stage_b_source: &[QM31; STAGE_B_QM31_LANES],
    gamma: QM31,
) -> QM31 {
    let mut result = QM31::ZERO;
    let mut power = QM31::ONE;
    let mut lane = 0usize;
    while lane < STAGE_A_SOURCE_LANES {
        result = result.add(power.mul_m31(stage_a_source[lane]));
        power = power.mul(gamma);
        lane += 1;
    }
    let mut extension_lane = 0usize;
    while extension_lane < STAGE_B_QM31_LANES {
        result = result.add(power.mul(stage_b_source[extension_lane]));
        power = power.mul(gamma);
        extension_lane += 1;
    }
    debug_assert_eq!(lane + extension_lane, COMBINED_LANES);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::P;

    fn basis(index: usize) -> QM31 {
        let mut limbs = [M31::ZERO; QM31_LIMBS];
        limbs[index] = M31::ONE;
        qm31_from_limbs(limbs)
    }

    fn next_m31(state: &mut u64) -> M31 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31((*state % u64::from(P)) as u32)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        qm31_from_limbs([
            next_m31(state),
            next_m31(state),
            next_m31(state),
            next_m31(state),
        ])
    }

    #[test]
    fn zeta_mobius_round_trip_and_mle_identity() {
        let coefficients = [
            M31(2),
            M31(3),
            M31(5),
            M31(7),
            M31(11),
            M31(13),
            M31(17),
            M31(19),
        ];
        let original = coefficients;
        let mut table = coefficients;
        zeta_in_place_m31(&mut table).unwrap();
        let point = [
            qm31_from_limbs([M31(23), M31(29), M31(31), M31(37)]),
            qm31_from_limbs([M31(41), M31(43), M31(47), M31(53)]),
            qm31_from_limbs([M31(59), M31(61), M31(67), M31(71)]),
        ];
        assert_eq!(
            evaluate_mle_zeta(&table, &point),
            evaluate_monomial_coefficients(&original, &point)
        );
        mobius_in_place_m31(&mut table).unwrap();
        assert_eq!(table, original);
    }

    #[test]
    fn malformed_zeta_shapes_are_rejected() {
        let mut empty: [M31; 0] = [];
        let mut three = [M31::ZERO; 3];
        assert_eq!(zeta_in_place_m31(&mut empty), Err(ZetaError::EmptyTable));
        assert_eq!(
            mobius_in_place_m31(&mut three),
            Err(ZetaError::LengthNotPowerOfTwo)
        );
        assert_eq!(
            evaluate_mle_zeta(&[M31::ZERO; 4], &[QM31::ZERO]),
            Err(ZetaError::DimensionMismatch)
        );
    }

    #[test]
    fn every_stage_a_lane_and_padding_position_is_exact() {
        let gamma = qm31_from_limbs([M31(7), M31(11), M31(13), M31(17)]);
        for lane in 0..STAGE_A_SOURCE_LANES {
            let mut source = [M31::ZERO; STAGE_A_SOURCE_LANES];
            source[lane] = M31::ONE;
            let table = stage_a_zeta_table(&source);
            assert_eq!(stage_a_restriction(&table, gamma), gamma.pow(lane as u64));

            let mut recovered = table;
            mobius_in_place_m31(&mut recovered).unwrap();
            assert_eq!(recovered, stage_a_coefficients(&source));
            assert!(recovered[STAGE_A_SOURCE_LANES..]
                .iter()
                .all(|value| value.is_zero()));
        }
    }

    #[test]
    fn every_stage_b_limb_and_padding_position_is_exact() {
        let gamma = qm31_from_limbs([M31(19), M31(23), M31(29), M31(31)]);
        for lane in 0..STAGE_B_QM31_LANES {
            for limb in 0..QM31_LIMBS {
                let mut source = [QM31::ZERO; STAGE_B_QM31_LANES];
                source[lane] = basis(limb);
                let table = stage_b_zeta_table(&source);
                assert_eq!(
                    stage_b_restriction(&table, gamma),
                    gamma.pow(lane as u64).mul(basis(limb))
                );

                let mut recovered = table;
                mobius_in_place_m31(&mut recovered).unwrap();
                assert_eq!(recovered, stage_b_coefficients(&source));
                assert!(recovered[STAGE_B_QM31_LANES * QM31_LIMBS..]
                    .iter()
                    .all(|value| value.is_zero()));
            }
        }
    }

    #[test]
    fn split_tensor_restriction_equals_literal_width29_batch() {
        let mut state = 0x7a11_ce55_5eed_u64;
        let mut stage_a = [M31::ZERO; STAGE_A_SOURCE_LANES];
        for value in &mut stage_a {
            *value = next_m31(&mut state);
        }
        let mut stage_b = [QM31::ZERO; STAGE_B_QM31_LANES];
        for value in &mut stage_b {
            *value = next_qm31(&mut state);
        }
        let stage_a_table = stage_a_zeta_table(&stage_a);
        let stage_b_table = stage_b_zeta_table(&stage_b);

        let minus_one = qm31_from_limbs([M31(P - 1), M31::ZERO, M31::ZERO, M31::ZERO]);
        let mut gammas = [QM31::ZERO; 10];
        gammas[0] = QM31::ONE;
        gammas[1] = minus_one;
        gammas[2] = QM31_I;
        gammas[3] = QM31_U;
        for gamma in &mut gammas[4..] {
            *gamma = next_qm31(&mut state);
        }

        for gamma in gammas {
            assert_eq!(
                split_tensor_restriction(&stage_a_table, &stage_b_table, gamma),
                width29_batch(&stage_a, &stage_b, gamma)
            );
            assert_eq!(
                evaluate_mle_zeta(&stage_a_table, &stage_a_lane_point(gamma)),
                evaluate_monomial_coefficients(
                    &stage_a_coefficients(&stage_a),
                    &stage_a_lane_point(gamma)
                )
            );
            assert_eq!(
                evaluate_mle_zeta(&stage_b_table, &stage_b_lane_point(gamma)),
                evaluate_monomial_coefficients(
                    &stage_b_coefficients(&stage_b),
                    &stage_b_lane_point(gamma)
                )
            );
        }
    }
}
