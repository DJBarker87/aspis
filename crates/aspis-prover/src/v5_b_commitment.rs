//! Host-only prototype for binding the v5 component-B sumcheck mask.
//!
//! The prototype embeds the 271 independent coordinates of
//! [`V5SumcheckMask`] and exactly 752 independent QM31 pads into one 1024-row
//! lane. The first row selected by the current copy-inactive functional is a
//! pivot. Every other row carries one input coordinate, in row order, and the
//! pivot is fixed so that the copy-inactive functional is zero. This is a
//! linear bijection from 1023 QM31 coordinates onto that functional's kernel.
//!
//! [`v5_b_terminal_covector`] returns the public, dense row-basis covector for
//! evaluating the chained mask at a ten-coordinate point. Its pivot and pad
//! entries are zero, so the terminal value depends only on the 271 mask
//! coordinates.
//!
//! # Deliberate boundary
//!
//! Nothing here is wired into a Merkle tree, transcript, verifier, proof
//! envelope, or the v4 prover. The hiding rank of the complete committed view
//! is still open. So is a kernel-checked correspondence between this Rust row
//! encoding and `AspisFormal/SumcheckMasking.lean`; the Lean file currently
//! proves the chained-mask algebra, not this 1024-row representation.

use aspis_core::field::QM31;
use aspis_core::state_only_sumcheck::{STATE_ONLY_SUMCHECK_DEGREE, STATE_ONLY_SUMCHECK_ROUNDS};
use aspis_statement::state_only_copy_inactive_row_masks_v4;

use crate::v5_sumcheck_mask::{V5SumcheckMask, V5_SUMCHECK_MASK_RANDOMNESS};

/// Number of QM31 rows in the provisional component-B lane.
pub const V5_B_LANE_ROWS: usize = 1024;
/// Chained-mask coordinates placed in the lane.
pub const V5_B_MASK_COORDINATES: usize = V5_SUMCHECK_MASK_RANDOMNESS;
/// Independent padding coordinates placed in the lane.
pub const V5_B_PAD_COORDINATES: usize = 752;
/// Dimension of the kernel of one nonzero functional on 1024 rows.
pub const V5_B_KERNEL_DIMENSION: usize = V5_B_LANE_ROWS - 1;

const _: () = assert!(V5_B_MASK_COORDINATES == 271);
const _: () = assert!(V5_B_PAD_COORDINATES == 752);
const _: () = assert!(V5_B_MASK_COORDINATES + V5_B_PAD_COORDINATES == V5_B_KERNEL_DIMENSION);
const _: () = assert!(STATE_ONLY_SUMCHECK_ROUNDS == 10);
const _: () = assert!(STATE_ONLY_SUMCHECK_DEGREE == 27);

/// One component-B lane in the current copy-inactive functional's kernel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5BCommitmentLane {
    values: [QM31; V5_B_LANE_ROWS],
}

impl V5BCommitmentLane {
    /// Encode a chained mask and exactly 752 independent pad coordinates.
    pub fn encode(mask: &V5SumcheckMask, pads: &[QM31; V5_B_PAD_COORDINATES]) -> Self {
        let pivot = v5_b_pivot_row();
        let mask_coordinates = mask.commitment_coordinates();
        let mut values = [QM31::ZERO; V5_B_LANE_ROWS];

        for (coordinate, value) in mask_coordinates.into_iter().enumerate() {
            values[free_coordinate_row(coordinate, pivot)] = value;
        }
        for (coordinate, value) in pads.iter().copied().enumerate() {
            let free_coordinate = V5_B_MASK_COORDINATES + coordinate;
            values[free_coordinate_row(free_coordinate, pivot)] = value;
        }

        values[pivot] = v5_b_copy_inactive_functional(&values).neg();
        debug_assert_eq!(v5_b_copy_inactive_functional(&values), QM31::ZERO);
        Self { values }
    }

    /// Borrow the complete 1024-row lane.
    pub const fn values(&self) -> &[QM31; V5_B_LANE_ROWS] {
        &self.values
    }

    /// Consume the wrapper and return the complete 1024-row lane.
    pub fn into_values(self) -> [QM31; V5_B_LANE_ROWS] {
        self.values
    }
}

/// The first row selected by the current copy-inactive functional.
pub fn v5_b_pivot_row() -> usize {
    let masks = state_only_copy_inactive_row_masks_v4();
    (0..V5_B_LANE_ROWS)
        .find(|&row| copy_inactive_row(&masks, row))
        .expect("the pinned copy-inactive functional is nonzero")
}

/// Apply the current copy-inactive functional to a 1024-row lane.
pub fn v5_b_copy_inactive_functional(values: &[QM31; V5_B_LANE_ROWS]) -> QM31 {
    let masks = state_only_copy_inactive_row_masks_v4();
    values
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| copy_inactive_row(&masks, *row))
        .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
}

/// Public row-basis covector for the chained mask's terminal evaluation.
///
/// If round `i` has free coefficients `a[i,1]..a[i,27]`, its recurrence is
///
/// ```text
/// s[i+1] = s[i]/2 + sum_k a[i,k] * (z[i]^k - 1/2).
/// ```
///
/// Unrolling the ten rounds gives the weights placed here. Pad and pivot rows
/// have weight zero.
pub fn v5_b_terminal_covector(
    point: &[QM31; STATE_ONLY_SUMCHECK_ROUNDS],
) -> [QM31; V5_B_LANE_ROWS] {
    let pivot = v5_b_pivot_row();
    let half = QM31::ONE.half();
    let mut coordinate_weights = [QM31::ZERO; V5_B_MASK_COORDINATES];
    coordinate_weights[0] = half.pow(STATE_ONLY_SUMCHECK_ROUNDS as u64);

    for (round, challenge) in point.iter().copied().enumerate() {
        let later_round_scale = half.pow((STATE_ONLY_SUMCHECK_ROUNDS - 1 - round) as u64);
        let mut challenge_power = challenge;
        for degree in 1..=STATE_ONLY_SUMCHECK_DEGREE {
            let coordinate = 1 + round * STATE_ONLY_SUMCHECK_DEGREE + degree - 1;
            coordinate_weights[coordinate] = later_round_scale.mul(challenge_power.sub(half));
            challenge_power = challenge_power.mul(challenge);
        }
    }

    let mut covector = [QM31::ZERO; V5_B_LANE_ROWS];
    for (coordinate, weight) in coordinate_weights.into_iter().enumerate() {
        covector[free_coordinate_row(coordinate, pivot)] = weight;
    }
    covector
}

/// Dense QM31 inner product used by the host-only prototype.
pub fn v5_b_dense_dot(left: &[QM31; V5_B_LANE_ROWS], right: &[QM31; V5_B_LANE_ROWS]) -> QM31 {
    left.iter()
        .copied()
        .zip(right.iter().copied())
        .fold(QM31::ZERO, |sum, (left, right)| sum.add(left.mul(right)))
}

fn copy_inactive_row(masks: &[u16; 64], row: usize) -> bool {
    masks[row >> 4] & (1 << (row & 15)) != 0
}

fn free_coordinate_row(coordinate: usize, pivot: usize) -> usize {
    debug_assert!(coordinate < V5_B_KERNEL_DIMENSION);
    if coordinate < pivot {
        coordinate
    } else {
        coordinate + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31};

    use crate::v5_mask::Qm31WordSource;

    struct XorShift(u64);

    impl Qm31WordSource for XorShift {
        fn next_word(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            (x >> 21) as u32
        }
    }

    fn sample(seed: u64) -> V5SumcheckMask {
        V5SumcheckMask::sample(&mut XorShift(seed)).expect("test source remains canonical")
    }

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn pads(seed: u32) -> [QM31; V5_B_PAD_COORDINATES] {
        core::array::from_fn(|coordinate| q(seed + coordinate as u32))
    }

    #[test]
    fn encoded_lane_lies_in_current_copy_inactive_kernel() {
        let lane = V5BCommitmentLane::encode(&sample(0xa1c5_5eed_91b7_3201), &pads(20_000));
        assert_eq!(v5_b_copy_inactive_functional(lane.values()), QM31::ZERO);

        let masks = state_only_copy_inactive_row_masks_v4();
        assert!(copy_inactive_row(&masks, v5_b_pivot_row()));
    }

    #[test]
    fn dense_terminal_covector_matches_chained_mask_evaluation() {
        let mask = sample(0x61d0_8c35_27a9_44ef);
        let point = core::array::from_fn(|coordinate| q(100 + coordinate as u32));
        let lane = V5BCommitmentLane::encode(&mask, &pads(30_000));
        let covector = v5_b_terminal_covector(&point);

        assert_eq!(
            v5_b_dense_dot(lane.values(), &covector),
            mask.evaluate(&point)
        );
    }

    #[test]
    fn pad_changes_do_not_change_the_terminal_functional() {
        let mask = sample(0x8b23_d4f0_5ea1_7719);
        let point = core::array::from_fn(|coordinate| q(400 + coordinate as u32));
        let first = V5BCommitmentLane::encode(&mask, &pads(40_000));
        let second = V5BCommitmentLane::encode(&mask, &pads(50_000));
        let covector = v5_b_terminal_covector(&point);
        let pivot = v5_b_pivot_row();

        assert_ne!(first, second);
        assert_eq!(covector[pivot], QM31::ZERO);
        for coordinate in 0..V5_B_PAD_COORDINATES {
            let free_coordinate = V5_B_MASK_COORDINATES + coordinate;
            assert_eq!(
                covector[free_coordinate_row(free_coordinate, pivot)],
                QM31::ZERO
            );
        }
        assert_eq!(
            v5_b_dense_dot(first.values(), &covector),
            mask.evaluate(&point)
        );
        assert_eq!(
            v5_b_dense_dot(second.values(), &covector),
            mask.evaluate(&point)
        );
    }

    #[test]
    fn dimensions_constants_and_coordinate_order_are_exact() {
        assert_eq!(V5_B_LANE_ROWS, 1024);
        assert_eq!(V5_B_MASK_COORDINATES, 271);
        assert_eq!(V5_B_PAD_COORDINATES, 752);
        assert_eq!(V5_B_KERNEL_DIMENSION, 1023);

        let mask = sample(0x09f3_c4a2_d8e1_675b);
        let pad_coordinates = pads(60_000);
        let lane = V5BCommitmentLane::encode(&mask, &pad_coordinates);
        let mask_coordinates = mask.commitment_coordinates();
        let pivot = v5_b_pivot_row();
        let mut seen_rows = [false; V5_B_LANE_ROWS];

        assert_eq!(mask_coordinates[0], mask.initial_claim());
        for round in 0..STATE_ONLY_SUMCHECK_ROUNDS {
            let polynomial = mask.zero_boundary_round(round).unwrap();
            for degree in 1..=STATE_ONLY_SUMCHECK_DEGREE {
                let coordinate = 1 + round * STATE_ONLY_SUMCHECK_DEGREE + degree - 1;
                assert_eq!(mask_coordinates[coordinate], polynomial[degree]);
            }
        }

        for (coordinate, expected) in mask_coordinates.into_iter().enumerate() {
            let row = free_coordinate_row(coordinate, pivot);
            assert!(!seen_rows[row]);
            seen_rows[row] = true;
            assert_eq!(lane.values()[row], expected);
        }
        for (coordinate, expected) in pad_coordinates.into_iter().enumerate() {
            let free_coordinate = V5_B_MASK_COORDINATES + coordinate;
            let row = free_coordinate_row(free_coordinate, pivot);
            assert!(!seen_rows[row]);
            seen_rows[row] = true;
            assert_eq!(lane.values()[row], expected);
        }

        assert!(!seen_rows[pivot]);
        assert_eq!(seen_rows.into_iter().filter(|seen| *seen).count(), 1023);
    }
}
