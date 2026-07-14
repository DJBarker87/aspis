//! Production-neutral oracle for the 16-column state-only Poseidon trace.
//!
//! The candidate layout stores the input of each two-round transition in
//! local rows `0..=10`, the final output in row 11, and the row-zero sponge
//! absorption in row 12.  The verifier binds the same sixteen multilinear
//! columns at `z`, at the binary-successor point, and at the low-bit-XOR-12
//! point.  This module defines only that algebra and its point maps; it is not
//! wired into the production v4 statement or profile-15 verifier.

use alloc::vec::Vec;

use aspis_core::field::{
    qm31_m31_dot, qm31_pack_base4, qm31_sum_products4, PreparedQm31Multiplier, CM31, M31, P, QM31,
};

use crate::poseidon2::{trace_round_constant, trace_round_descriptor, POSEIDON2_WIDTH, RATE};

pub const STATE_ONLY_POSEIDON_COLUMNS: usize = POSEIDON2_WIDTH;
pub const STATE_ONLY_POSEIDON_PACKED_LANES: usize = POSEIDON2_WIDTH / 4;
pub const STATE_ONLY_POSEIDON_ACTIVE_LOCAL_ROWS: usize = 11;
pub const STATE_ONLY_POSEIDON_FINAL_LOCAL_ROW: usize = 11;
pub const STATE_ONLY_POSEIDON_ABSORPTION_LOCAL_ROW: usize = 12;
pub const STATE_ONLY_POSEIDON_BLOCK_ROWS: usize = 16;
pub const STATE_ONLY_POSEIDON_BLOCKS: usize = 49;
pub const STATE_ONLY_POSEIDON_TRACE_ROWS: usize = 1 << 10;

/// The oracle has degree at most 26 in any one sumcheck variable: two
/// consecutive fifth-power rounds contribute 25 and the active-row selector
/// contributes one.  Multiplication by the outer zerocheck equality factor
/// gives the candidate statement's conservative degree-27 bound.
pub const STATE_ONLY_POSEIDON_ORACLE_INDIVIDUAL_DEGREE: usize = 26;
pub const STATE_ONLY_POSEIDON_ZEROCHECK_INDIVIDUAL_DEGREE: usize = 27;

const _: () = assert!(STATE_ONLY_POSEIDON_COLUMNS == 16);
const _: () = assert!(STATE_ONLY_POSEIDON_PACKED_LANES == 4);

/// The three independently PCS-bound evaluations consumed by the oracle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyPoseidonOpenings {
    pub z: [QM31; STATE_ONLY_POSEIDON_COLUMNS],
    pub succ_z: [QM31; STATE_ONLY_POSEIDON_COLUMNS],
    pub xor12_z: [QM31; STATE_ONLY_POSEIDON_COLUMNS],
}

/// Verifier-preprocessed row selectors for the state-only layout.
///
/// `block` is the MLE of high-index values `0..49`, while `local` contains
/// the sixteen low-nibble equality polynomials.  Poseidon constants are
/// interpolated with `local` before either round is evaluated, matching the
/// preprocessed-selector representative used by the current v4 statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyPoseidonSelectors {
    pub block: QM31,
    pub local: [QM31; STATE_ONLY_POSEIDON_BLOCK_ROWS],
}

impl StateOnlyPoseidonSelectors {
    fn expand<const N: usize>(coordinates: &[QM31]) -> [QM31; N] {
        debug_assert_eq!(N, 1usize << coordinates.len());
        let mut weights = [QM31::ZERO; N];
        weights[0] = QM31::ONE;
        let mut len = 1usize;
        for coordinate in coordinates {
            let prepared = PreparedQm31Multiplier::new(*coordinate);
            for index in (0..len).rev() {
                let parent = weights[index];
                let right = prepared.mul(parent);
                weights[2 * index] = parent.sub(right);
                weights[2 * index + 1] = right;
            }
            len *= 2;
        }
        weights
    }

    pub fn at_point(point: &[QM31; 10]) -> Self {
        let high = Self::expand::<64>(&point[..6]);
        let block = high[..STATE_ONLY_POSEIDON_BLOCKS]
            .iter()
            .copied()
            .fold(QM31::ZERO, QM31::add);
        Self {
            block,
            local: Self::expand(&point[6..]),
        }
    }
}

/// Polynomial binary increment, with overflow discarded modulo 1024.
/// Boolean row `r` maps to `(r + 1) mod 1024`.
pub fn successor_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut successor = *point;
    let mut carry = QM31::ONE;
    for coordinate in (0..point.len()).rev() {
        let bit = point[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    successor
}

/// Toggle low row-index bits two and three.  On Boolean points this maps a
/// block's local row zero to local row twelve, where its absorption lives.
pub fn xor12_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut shifted = *point;
    for bit in [2usize, 3] {
        let coordinate = point.len() - 1 - bit;
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    shifted
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[inline(always)]
fn pow5(value: QM31) -> QM31 {
    let square = value.square();
    square.square().mul(value)
}

#[inline(always)]
fn extension_limbs(value: QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

#[inline(always)]
fn extension_from_raw_limbs(limbs: [u64; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31::reduce_u62(limbs[0]), M31::reduce_u62(limbs[1])),
        c1: CM31::new(M31::reduce_u62(limbs[2]), M31::reduce_u62(limbs[3])),
    }
}

/// Addition-only Poseidon external layer with one reduction per output limb.
#[inline(never)]
fn external_linear_lazy(state: &mut [QM31; POSEIDON2_WIDTH]) {
    for values in state.chunks_exact_mut(4) {
        let input: [QM31; 4] = values.try_into().expect("four-lane chunk");
        let input = input.map(extension_limbs);
        for output in 0..4 {
            let raw = core::array::from_fn(|limb| {
                let a = u64::from(input[0][limb]);
                let b = u64::from(input[1][limb]);
                let c = u64::from(input[2][limb]);
                let d = u64::from(input[3][limb]);
                match output {
                    0 => 2 * a + 3 * b + c + d,
                    1 => a + 2 * b + 3 * c + d,
                    2 => a + b + 2 * c + 3 * d,
                    3 => 3 * a + b + c + 2 * d,
                    _ => unreachable!(),
                }
            });
            values[output] = extension_from_raw_limbs(raw);
        }
    }
    let sums: [[u64; 4]; 4] = core::array::from_fn(|column| {
        core::array::from_fn(|limb| {
            (0..4)
                .map(|row| u64::from(extension_limbs(state[row * 4 + column])[limb]))
                .sum()
        })
    });
    for (index, value) in state.iter_mut().enumerate() {
        let limbs = extension_limbs(*value);
        *value = extension_from_raw_limbs(core::array::from_fn(|limb| {
            u64::from(limbs[limb]) + sums[index & 3][limb]
        }));
    }
}

/// Apply the final external layer only through the four tower-packed output
/// functionals consumed by the terminal composition.
///
/// If `B` is the four-lane local matrix and `J + I` is the global layer, then
/// packing commutes with both maps:
///
/// `pack((J + I) B x)_g = pack(B x_g) + sum_h pack(B x_h)`.
///
/// This is the transpose/adjoint form specialized to the fixed tower-basis
/// functional.  It avoids materializing and reducing all sixteen final lanes
/// and introduces no challenge-dependent dot products.
#[inline(never)]
fn external_linear_packed(mut state: [QM31; POSEIDON2_WIDTH]) -> [QM31; 4] {
    let mut local_packed = [QM31::ZERO; 4];
    for (group, values) in state.chunks_exact_mut(4).enumerate() {
        let input: [QM31; 4] = values.try_into().expect("four-lane chunk");
        let input = input.map(extension_limbs);
        for output in 0..4 {
            let raw = core::array::from_fn(|limb| {
                let a = u64::from(input[0][limb]);
                let b = u64::from(input[1][limb]);
                let c = u64::from(input[2][limb]);
                let d = u64::from(input[3][limb]);
                match output {
                    0 => 2 * a + 3 * b + c + d,
                    1 => a + 2 * b + 3 * c + d,
                    2 => a + b + 2 * c + 3 * d,
                    3 => 3 * a + b + c + 2 * d,
                    _ => unreachable!(),
                }
            });
            values[output] = extension_from_raw_limbs(raw);
        }
        local_packed[group] = qm31_pack_base4(values);
    }
    let sum = local_packed.iter().copied().fold(QM31::ZERO, QM31::add);
    local_packed.map(|value| value.add(sum))
}

#[inline(never)]
fn internal_linear_lazy(state: &mut [QM31; POSEIDON2_WIDTH]) {
    const SHIFTS: [u8; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];
    let old_zero = extension_limbs(state[0]);
    let part_sum: [u64; 4] = core::array::from_fn(|limb| {
        state[1..]
            .iter()
            .map(|value| u64::from(extension_limbs(*value)[limb]))
            .sum()
    });
    let full_sum: [u64; 4] =
        core::array::from_fn(|limb| part_sum[limb] + u64::from(old_zero[limb]));
    state[0] = extension_from_raw_limbs(core::array::from_fn(|limb| {
        part_sum[limb] + u64::from(P) - u64::from(old_zero[limb])
    }));
    for lane in 1..POSEIDON2_WIDTH {
        let limbs = extension_limbs(state[lane]);
        state[lane] = extension_from_raw_limbs(core::array::from_fn(|limb| {
            full_sum[limb] + (u64::from(limbs[limb]) << SHIFTS[lane - 1])
        }));
    }
}

#[inline(never)]
fn full_round(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [QM31; POSEIDON2_WIDTH],
) -> [QM31; POSEIDON2_WIDTH] {
    for lane in 0..POSEIDON2_WIDTH {
        state[lane] = pow5(state[lane].add(constants[lane]));
    }
    external_linear_lazy(&mut state);
    state
}

#[inline(never)]
fn full_round_packed(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [QM31; POSEIDON2_WIDTH],
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    for lane in 0..POSEIDON2_WIDTH {
        state[lane] = pow5(state[lane].add(constants[lane]));
    }
    external_linear_packed(state)
}

#[inline(never)]
fn internal_round(mut state: [QM31; POSEIDON2_WIDTH], constant: QM31) -> [QM31; 16] {
    state[0] = pow5(state[0].add(constant));
    internal_linear_lazy(&mut state);
    state
}

fn leading_pair(openings: &StateOnlyPoseidonOpenings) -> [QM31; POSEIDON2_WIDTH] {
    let mut state = openings.z;
    for lane in 0..RATE {
        state[lane] = state[lane].add(openings.xor12_z[lane]);
    }
    external_linear_lazy(&mut state);
    let (round0, round0_full) = trace_round_descriptor(0).expect("pinned round zero");
    let (round1, round1_full) = trace_round_descriptor(1).expect("pinned round one");
    debug_assert!(round0_full && round1_full);
    full_round(full_round(state, round0.map(lift)), round1.map(lift))
}

fn leading_pair_packed(
    openings: &StateOnlyPoseidonOpenings,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let mut state = openings.z;
    for lane in 0..RATE {
        state[lane] = state[lane].add(openings.xor12_z[lane]);
    }
    external_linear_lazy(&mut state);
    let (round0, round0_full) = trace_round_descriptor(0).expect("pinned round zero");
    let (round1, round1_full) = trace_round_descriptor(1).expect("pinned round one");
    debug_assert!(round0_full && round1_full);
    full_round_packed(full_round(state, round0.map(lift)), round1.map(lift))
}

fn interpolated_full_pair(
    state: [QM31; POSEIDON2_WIDTH],
    local: &[QM31; 16],
) -> [QM31; POSEIDON2_WIDTH] {
    const ROWS: [usize; 3] = [1, 9, 10];
    let weights = ROWS.map(|row| local[row]);
    let even = core::array::from_fn(|lane| {
        let constants = ROWS.map(|row| {
            let (constant, full) =
                trace_round_constant(2 * row, lane).expect("pinned full even round");
            debug_assert!(full);
            constant
        });
        qm31_m31_dot(&weights, &constants)
    });
    let odd = core::array::from_fn(|lane| {
        let constants = ROWS.map(|row| {
            let (constant, full) =
                trace_round_constant(2 * row + 1, lane).expect("pinned full odd round");
            debug_assert!(full);
            constant
        });
        qm31_m31_dot(&weights, &constants)
    });
    full_round(full_round(state, even), odd)
}

fn interpolated_full_pair_packed(
    state: [QM31; POSEIDON2_WIDTH],
    local: &[QM31; 16],
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    const ROWS: [usize; 3] = [1, 9, 10];
    let weights = ROWS.map(|row| local[row]);
    let even = core::array::from_fn(|lane| {
        let constants = ROWS.map(|row| {
            let (constant, full) =
                trace_round_constant(2 * row, lane).expect("pinned full even round");
            debug_assert!(full);
            constant
        });
        qm31_m31_dot(&weights, &constants)
    });
    let odd = core::array::from_fn(|lane| {
        let constants = ROWS.map(|row| {
            let (constant, full) =
                trace_round_constant(2 * row + 1, lane).expect("pinned full odd round");
            debug_assert!(full);
            constant
        });
        qm31_m31_dot(&weights, &constants)
    });
    full_round_packed(full_round(state, even), odd)
}

fn interpolated_internal_pair(
    state: [QM31; POSEIDON2_WIDTH],
    local: &[QM31; 16],
) -> [QM31; POSEIDON2_WIDTH] {
    const ROWS: [usize; 7] = [2, 3, 4, 5, 6, 7, 8];
    let weights = ROWS.map(|row| local[row]);
    let even_constants = ROWS.map(|row| {
        let (constant, full) =
            trace_round_constant(2 * row, 0).expect("pinned internal even round");
        debug_assert!(!full);
        constant
    });
    let odd_constants = ROWS.map(|row| {
        let (constant, full) =
            trace_round_constant(2 * row + 1, 0).expect("pinned internal odd round");
        debug_assert!(!full);
        constant
    });
    let even = qm31_m31_dot(&weights, &even_constants);
    let odd = qm31_m31_dot(&weights, &odd_constants);
    internal_round(internal_round(state, even), odd)
}

/// Evaluate the four injectively packed successor-state constraints.
///
/// On an active Boolean row the result is zero exactly when the state at
/// `succ(z)` is the output of the row's two pinned Poseidon rounds (including
/// row zero's absorption and leading external layer).  No intermediate-round
/// state is constrained or committed.
#[inline(never)]
pub fn evaluate_state_only_poseidon_oracle(
    openings: &StateOnlyPoseidonOpenings,
    selectors: &StateOnlyPoseidonSelectors,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let leading_low = selectors.local[0];
    let full_low = [1usize, 9, 10]
        .into_iter()
        .fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
    let internal_low = (2usize..=8).fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
    let active_low = leading_low.add(full_low).add(internal_low);

    let leading = leading_pair(openings);
    let full = interpolated_full_pair(openings.z, &selectors.local);
    let internal = interpolated_internal_pair(openings.z, &selectors.local);
    let weights = [
        active_low,
        leading_low.neg(),
        full_low.neg(),
        internal_low.neg(),
    ];

    core::array::from_fn(|group| {
        let start = 4 * group;
        let target = qm31_pack_base4(&openings.succ_z[start..start + 4]);
        let leading = qm31_pack_base4(&leading[start..start + 4]);
        let full = qm31_pack_base4(&full[start..start + 4]);
        let internal = qm31_pack_base4(&internal[start..start + 4]);
        selectors.block.mul(qm31_sum_products4(
            [target, leading, full, internal],
            weights,
        ))
    })
}

/// Exact packed-projection implementation of [`evaluate_state_only_poseidon_oracle`].
///
/// Only the two full/full branches benefit: their second external layer is
/// consumed through its four packed adjoint functionals.  The internal branch
/// remains on the original path because a generic adjoint there would replace
/// additions by sixteen extension-field products.
#[inline(never)]
pub fn evaluate_state_only_poseidon_oracle_projected(
    openings: &StateOnlyPoseidonOpenings,
    selectors: &StateOnlyPoseidonSelectors,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let leading_low = selectors.local[0];
    let full_low = [1usize, 9, 10]
        .into_iter()
        .fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
    let internal_low = (2usize..=8).fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
    let active_low = leading_low.add(full_low).add(internal_low);

    let leading = leading_pair_packed(openings);
    let full = interpolated_full_pair_packed(openings.z, &selectors.local);
    let internal = interpolated_internal_pair(openings.z, &selectors.local);
    let weights = [
        active_low,
        leading_low.neg(),
        full_low.neg(),
        internal_low.neg(),
    ];

    core::array::from_fn(|group| {
        let start = 4 * group;
        let target = qm31_pack_base4(&openings.succ_z[start..start + 4]);
        let internal = qm31_pack_base4(&internal[start..start + 4]);
        selectors.block.mul(qm31_sum_products4(
            [target, leading[group], full[group], internal],
            weights,
        ))
    })
}

fn multilinear_evaluate(column: &[M31], point: &[QM31; 10]) -> Option<QM31> {
    if column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS {
        return None;
    }
    let mut layer = column.iter().copied().map(lift).collect::<Vec<_>>();
    let mut width = layer.len();
    for coordinate in point.iter().rev() {
        let prepared = PreparedQm31Multiplier::new(*coordinate);
        for index in 0..width / 2 {
            let left = layer[2 * index];
            let right = layer[2 * index + 1];
            layer[index] = left.add(prepared.mul(right.sub(left)));
        }
        width /= 2;
    }
    Some(layer[0])
}

/// Host helper that derives the three opening vectors from a raw 16-column
/// candidate trace.  The returned values still need ordinary PCS binding.
#[cfg(not(target_os = "solana"))]
pub fn state_only_poseidon_openings_at_point(
    columns: &[Vec<M31>; STATE_ONLY_POSEIDON_COLUMNS],
    point: &[QM31; 10],
) -> Option<StateOnlyPoseidonOpenings> {
    if columns
        .iter()
        .any(|column| column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS)
    {
        return None;
    }
    let successor = successor_point(point);
    let absorption = xor12_point(point);
    Some(StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|lane| multilinear_evaluate(&columns[lane], point).unwrap()),
        succ_z: core::array::from_fn(|lane| {
            multilinear_evaluate(&columns[lane], &successor).unwrap()
        }),
        xor12_z: core::array::from_fn(|lane| {
            multilinear_evaluate(&columns[lane], &absorption).unwrap()
        }),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints_v4::multilinear_evaluate as v4_multilinear_evaluate;
    use crate::spend::{
        derive_nullifier, derive_owner_key, merkle_root, note_commitment, output_commitment,
        MerklePath, SpendPublic, SpendWitness,
    };
    use crate::state_only_trace::{
        binary_successor_point, project_state_only_trace_v4, xor12_point as trace_xor12_point,
        STATE_ONLY_ABSORPTION_ROW_IN_BLOCK, STATE_ONLY_C1_COLUMNS, STATE_ONLY_FINAL_ROW_IN_BLOCK,
        STATE_ONLY_TRANSITIONS_PER_BLOCK,
    };
    use crate::trace_v4::{build_spend_trace_v4, TRACE_ROWS};

    fn boolean_point(row: usize) -> [QM31; 10] {
        core::array::from_fn(|coordinate| {
            if (row >> (9 - coordinate)) & 1 == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        })
    }

    fn digest(seed: u32) -> [M31; 8] {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn fixture() -> (SpendPublic, SpendWitness) {
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
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
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
        (public, witness)
    }

    fn state_only_columns_from_v4() -> [Vec<M31>; STATE_ONLY_POSEIDON_COLUMNS] {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        project_state_only_trace_v4(&trace).unwrap().c1.clone()
    }

    #[test]
    fn successor_and_xor12_maps_are_exact_on_all_boolean_rows() {
        for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
            let point = boolean_point(row);
            assert_eq!(
                successor_point(&point),
                boolean_point((row + 1) & (STATE_ONLY_POSEIDON_TRACE_ROWS - 1))
            );
            assert_eq!(xor12_point(&point), boolean_point(row ^ 12));
        }
    }

    #[test]
    fn oracle_and_trace_foundation_constants_and_point_maps_cannot_drift() {
        assert_eq!(STATE_ONLY_POSEIDON_COLUMNS, STATE_ONLY_C1_COLUMNS);
        assert_eq!(
            STATE_ONLY_POSEIDON_ACTIVE_LOCAL_ROWS,
            STATE_ONLY_TRANSITIONS_PER_BLOCK
        );
        assert_eq!(
            STATE_ONLY_POSEIDON_FINAL_LOCAL_ROW,
            STATE_ONLY_FINAL_ROW_IN_BLOCK
        );
        assert_eq!(
            STATE_ONLY_POSEIDON_ABSORPTION_LOCAL_ROW,
            STATE_ONLY_ABSORPTION_ROW_IN_BLOCK
        );

        let mut seed = 0xe449_193a_cdb0_77f1;
        for _ in 0..64 {
            let point = core::array::from_fn(|_| random_qm31(&mut seed));
            assert_eq!(successor_point(&point), binary_successor_point(&point));
            assert_eq!(xor12_point(&point), trace_xor12_point(&point));
        }
    }

    #[test]
    fn three_point_opening_helper_matches_the_existing_mle_reference() {
        let columns = state_only_columns_from_v4();
        let mut seed = 0x0954_bf71_a2de_4c83;
        for sample in 0..8 {
            let point = core::array::from_fn(|_| random_qm31(&mut seed));
            let successor = successor_point(&point);
            let absorption = xor12_point(&point);
            let openings = state_only_poseidon_openings_at_point(&columns, &point).unwrap();
            for lane in 0..POSEIDON2_WIDTH {
                assert_eq!(
                    openings.z[lane],
                    v4_multilinear_evaluate(&columns[lane], &point).unwrap(),
                    "sample={sample} z lane={lane}"
                );
                assert_eq!(
                    openings.succ_z[lane],
                    v4_multilinear_evaluate(&columns[lane], &successor).unwrap(),
                    "sample={sample} successor lane={lane}"
                );
                assert_eq!(
                    openings.xor12_z[lane],
                    v4_multilinear_evaluate(&columns[lane], &absorption).unwrap(),
                    "sample={sample} absorption lane={lane}"
                );
            }
        }
    }

    #[test]
    fn state_only_oracle_matches_every_honest_v4_boolean_transition() {
        let columns = state_only_columns_from_v4();
        let mut active = 0usize;
        for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
            let point = boolean_point(row);
            let openings = StateOnlyPoseidonOpenings {
                z: core::array::from_fn(|lane| lift(columns[lane][row])),
                succ_z: core::array::from_fn(|lane| {
                    lift(columns[lane][(row + 1) & (STATE_ONLY_POSEIDON_TRACE_ROWS - 1)])
                }),
                xor12_z: core::array::from_fn(|lane| lift(columns[lane][row ^ 12])),
            };
            let residuals = evaluate_state_only_poseidon_oracle(
                &openings,
                &StateOnlyPoseidonSelectors::at_point(&point),
            );
            assert!(
                residuals.iter().all(|value| value.is_zero()),
                "row={row} residuals={residuals:?}"
            );
            if row / 16 < STATE_ONLY_POSEIDON_BLOCKS && row % 16 < 11 {
                active += 1;
            }
        }
        assert_eq!(active, STATE_ONLY_POSEIDON_BLOCKS * 11);
    }

    #[test]
    fn successor_and_absorption_mutations_have_teeth() {
        let columns = state_only_columns_from_v4();
        let row = 0usize;
        let point = boolean_point(row);
        let selectors = StateOnlyPoseidonSelectors::at_point(&point);
        let honest = StateOnlyPoseidonOpenings {
            z: core::array::from_fn(|lane| lift(columns[lane][row])),
            succ_z: core::array::from_fn(|lane| lift(columns[lane][row + 1])),
            xor12_z: core::array::from_fn(|lane| lift(columns[lane][row ^ 12])),
        };
        assert!(evaluate_state_only_poseidon_oracle(&honest, &selectors)
            .iter()
            .all(|value| value.is_zero()));

        for lane in 0..POSEIDON2_WIDTH {
            let mut adversarial = honest;
            adversarial.succ_z[lane] = adversarial.succ_z[lane].add(QM31::ONE);
            assert!(
                evaluate_state_only_poseidon_oracle(&adversarial, &selectors)
                    .iter()
                    .any(|value| !value.is_zero()),
                "successor lane {lane} escaped"
            );
        }

        for lane in 0..RATE {
            let mut adversarial = honest;
            adversarial.xor12_z[lane] = adversarial.xor12_z[lane].add(QM31::ONE);
            assert!(
                evaluate_state_only_poseidon_oracle(&adversarial, &selectors)
                    .iter()
                    .any(|value| !value.is_zero()),
                "absorption lane {lane} escaped"
            );
        }
    }

    #[test]
    fn relation_free_mask_padding_rows_are_not_constrained() {
        let columns = state_only_columns_from_v4();
        for block in 0..STATE_ONLY_POSEIDON_BLOCKS {
            for local_row in 13usize..=15 {
                let row = block * 16 + local_row;
                let point = boolean_point(row);
                let selectors = StateOnlyPoseidonSelectors::at_point(&point);
                let mut openings = StateOnlyPoseidonOpenings {
                    z: core::array::from_fn(|lane| lift(columns[lane][row])),
                    succ_z: core::array::from_fn(|lane| {
                        lift(columns[lane][(row + 1) & (TRACE_ROWS - 1)])
                    }),
                    xor12_z: core::array::from_fn(|lane| lift(columns[lane][row ^ 12])),
                };
                for lane in 0..POSEIDON2_WIDTH {
                    openings.z[lane] = lift(M31(10_000 + row as u32 + lane as u32));
                    openings.succ_z[lane] = lift(M31(20_000 + row as u32 + lane as u32));
                    openings.xor12_z[lane] = lift(M31(30_000 + row as u32 + lane as u32));
                }
                assert!(
                    evaluate_state_only_poseidon_oracle(&openings, &selectors)
                        .iter()
                        .all(|value| value.is_zero()),
                    "relation-free padding row {row} was constrained"
                );
            }
        }
    }

    fn external_linear_reference(state: &mut [QM31; 16]) {
        for chunk in state.chunks_exact_mut(4) {
            let [a, b, c, d]: [QM31; 4] = chunk.try_into().unwrap();
            chunk.copy_from_slice(&[
                a.add(a).add(b).add(b).add(b).add(c).add(d),
                a.add(b).add(b).add(c).add(c).add(c).add(d),
                a.add(b).add(c).add(c).add(d).add(d).add(d),
                a.add(a).add(a).add(b).add(c).add(d).add(d),
            ]);
        }
        let sums: [QM31; 4] = core::array::from_fn(|column| {
            (0..4).fold(QM31::ZERO, |sum, row| sum.add(state[row * 4 + column]))
        });
        for (index, value) in state.iter_mut().enumerate() {
            *value = value.add(sums[index & 3]);
        }
    }

    fn internal_linear_reference(state: &mut [QM31; 16]) {
        const SHIFTS: [u8; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];
        let part = state[1..].iter().copied().fold(QM31::ZERO, QM31::add);
        let full = part.add(state[0]);
        state[0] = part.sub(state[0]);
        for lane in 1..16 {
            state[lane] = full.add(state[lane].mul_m31(M31(1u32 << SHIFTS[lane - 1])));
        }
    }

    fn full_round_reference(mut state: [QM31; 16], constants: [QM31; 16]) -> [QM31; 16] {
        for lane in 0..16 {
            state[lane] = state[lane].add(constants[lane]).pow(5);
        }
        external_linear_reference(&mut state);
        state
    }

    fn internal_round_reference(mut state: [QM31; 16], constant: QM31) -> [QM31; 16] {
        state[0] = state[0].add(constant).pow(5);
        internal_linear_reference(&mut state);
        state
    }

    fn generic_pack(values: &[QM31]) -> QM31 {
        let i = QM31 {
            c0: CM31::new(M31::ZERO, M31::ONE),
            c1: CM31::ZERO,
        };
        let u = QM31 {
            c0: CM31::ZERO,
            c1: CM31::ONE,
        };
        let basis = [QM31::ONE, i, u, i.mul(u)];
        values
            .iter()
            .copied()
            .zip(basis)
            .fold(QM31::ZERO, |sum, (value, basis)| sum.add(value.mul(basis)))
    }

    fn oracle_reference(
        openings: &StateOnlyPoseidonOpenings,
        selectors: &StateOnlyPoseidonSelectors,
    ) -> [QM31; 4] {
        let leading_low = selectors.local[0];
        let full_low = [1usize, 9, 10]
            .into_iter()
            .fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
        let internal_low = (2usize..=8).fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
        let active_low = leading_low.add(full_low).add(internal_low);

        let mut leading = openings.z;
        for lane in 0..RATE {
            leading[lane] = leading[lane].add(openings.xor12_z[lane]);
        }
        external_linear_reference(&mut leading);
        let round0 = trace_round_descriptor(0).unwrap().0.map(lift);
        let round1 = trace_round_descriptor(1).unwrap().0.map(lift);
        leading = full_round_reference(full_round_reference(leading, round0), round1);

        let mut full_even = [QM31::ZERO; 16];
        let mut full_odd = [QM31::ZERO; 16];
        for row in [1usize, 9, 10] {
            for lane in 0..16 {
                full_even[lane] = full_even[lane].add(
                    selectors.local[row].mul_m31(trace_round_constant(2 * row, lane).unwrap().0),
                );
                full_odd[lane] = full_odd[lane].add(
                    selectors.local[row]
                        .mul_m31(trace_round_constant(2 * row + 1, lane).unwrap().0),
                );
            }
        }
        let full = full_round_reference(full_round_reference(openings.z, full_even), full_odd);

        let mut internal_even = QM31::ZERO;
        let mut internal_odd = QM31::ZERO;
        for row in 2usize..=8 {
            internal_even = internal_even
                .add(selectors.local[row].mul_m31(trace_round_constant(2 * row, 0).unwrap().0));
            internal_odd = internal_odd
                .add(selectors.local[row].mul_m31(trace_round_constant(2 * row + 1, 0).unwrap().0));
        }
        let internal = internal_round_reference(
            internal_round_reference(openings.z, internal_even),
            internal_odd,
        );

        core::array::from_fn(|group| {
            let start = 4 * group;
            let inside = active_low
                .mul(generic_pack(&openings.succ_z[start..start + 4]))
                .sub(leading_low.mul(generic_pack(&leading[start..start + 4])))
                .sub(full_low.mul(generic_pack(&full[start..start + 4])))
                .sub(internal_low.mul(generic_pack(&internal[start..start + 4])));
            selectors.block.mul(inside)
        })
    }

    fn next_u32(state: &mut u64) -> u32 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((*state >> 32) as u32) % P
    }

    fn random_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(M31(next_u32(state)), M31(next_u32(state))),
            c1: CM31::new(M31(next_u32(state)), M31(next_u32(state))),
        }
    }

    #[test]
    fn optimized_oracle_matches_independent_reference_at_random_off_domain_points() {
        let mut seed = 0x7bf0_4a19_91cd_e229;
        for sample in 0..64 {
            let point = core::array::from_fn(|_| random_qm31(&mut seed));
            let openings = StateOnlyPoseidonOpenings {
                z: core::array::from_fn(|_| random_qm31(&mut seed)),
                succ_z: core::array::from_fn(|_| random_qm31(&mut seed)),
                xor12_z: core::array::from_fn(|_| random_qm31(&mut seed)),
            };
            let selectors = StateOnlyPoseidonSelectors::at_point(&point);
            assert_eq!(
                evaluate_state_only_poseidon_oracle(&openings, &selectors),
                oracle_reference(&openings, &selectors),
                "sample={sample}"
            );
            assert_eq!(
                evaluate_state_only_poseidon_oracle_projected(&openings, &selectors),
                oracle_reference(&openings, &selectors),
                "projected sample={sample}"
            );
        }
    }

    fn affine_column_value(point: &[QM31; 10], lane: usize, salt: u32) -> QM31 {
        let mut value = lift(M31((salt + 97 * lane as u32 + 13) % P));
        for (coordinate, x) in point.iter().enumerate() {
            let coefficient = M31((salt
                .wrapping_mul(17 + coordinate as u32)
                .wrapping_add(131 * lane as u32)
                .wrapping_add(19 * coordinate as u32)
                .wrapping_add(1))
                % P);
            value = value.add(x.mul_m31(coefficient));
        }
        value
    }

    fn affine_openings(point: &[QM31; 10], salt: u32) -> StateOnlyPoseidonOpenings {
        let successor = successor_point(point);
        let absorption = xor12_point(point);
        StateOnlyPoseidonOpenings {
            z: core::array::from_fn(|lane| affine_column_value(point, lane, salt)),
            succ_z: core::array::from_fn(|lane| affine_column_value(&successor, lane, salt)),
            xor12_z: core::array::from_fn(|lane| affine_column_value(&absorption, lane, salt)),
        }
    }

    #[test]
    fn individual_degree_is_at_most_27_and_has_a_high_degree_witness() {
        let mut saw_high_degree = false;
        for salt in [3u32, 29, 101] {
            for varying_coordinate in 0..10 {
                let mut evaluations = Vec::with_capacity(29);
                for t in 0..=28u32 {
                    let mut point: [QM31; 10] = core::array::from_fn(|coordinate| {
                        lift(M31((7 + salt * 11 + coordinate as u32 * 23) % P))
                    });
                    point[varying_coordinate] = lift(M31(t));
                    evaluations.push(evaluate_state_only_poseidon_oracle(
                        &affine_openings(&point, salt),
                        &StateOnlyPoseidonSelectors::at_point(&point),
                    ));
                }

                for order in 1..=28 {
                    for index in 0..evaluations.len() - 1 {
                        evaluations[index] = core::array::from_fn(|lane| {
                            evaluations[index + 1][lane].sub(evaluations[index][lane])
                        });
                    }
                    evaluations.pop();
                    if (25..=27).contains(&order)
                        && evaluations[0].iter().any(|value| !value.is_zero())
                    {
                        saw_high_degree = true;
                    }
                    if order == 28 {
                        assert!(
                            evaluations[0].iter().all(|value| value.is_zero()),
                            "salt={salt} coordinate={varying_coordinate} exceeded degree 27"
                        );
                    }
                }
            }
        }
        assert!(saw_high_degree, "no degree-25-or-higher witness was found");
        assert!(
            STATE_ONLY_POSEIDON_ORACLE_INDIVIDUAL_DEGREE
                <= STATE_ONLY_POSEIDON_ZEROCHECK_INDIVIDUAL_DEGREE
        );
    }
}
