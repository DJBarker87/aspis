//! V5 Component C: a full-kernel PCS masking lane.
//!
//! V5 uses the third already-budgeted QM31 helper lane. Its
//! message is uniform in the kernel of the exact atomic-v3 copy-inactive
//! functional: 1,023 coordinates are sampled independently and the first
//! selected row is derived so the functional is zero.  Consequently it does
//! not change the root claim enforced by the existing PCS relation.
//!
//! This module owns the row encoding and its four public linear claims. The
//! complete runtime path and Rust-to-Lean correspondence are joined in the V5
//! release proofs.

use aspis_core::field::QM31;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::{binary_successor_point, xor12_point};

use super::{sample_qm31, MaskSampleExhausted, Qm31WordSource};

pub const V5_C_ROWS: usize = 1024;
pub const V5_C_FREE_COORDINATES: usize = V5_C_ROWS - 1;
pub const V5_C_POINT_CLAIMS: usize = 3;
pub const V5_C_TOTAL_CLAIMS: usize = 4;

const _: () = assert!(V5_C_FREE_COORDINATES == 1023);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCLane {
    values: [QM31; V5_C_ROWS],
}

enum V5CEncodeCorrespondence {
    MissingPivot,
    Encoded([QM31; V5_C_ROWS], [u16; 64]),
}

enum V5CDecodeCorrespondence {
    MissingPivot,
    Decoded([QM31; V5_C_FREE_COORDINATES]),
}

impl V5ComponentCLane {
    /// Sample the 1,023 free coordinates in row order and derive the pivot.
    pub fn sample<S: Qm31WordSource>(source: &mut S) -> Result<Self, MaskSampleExhausted> {
        let mut free = [QM31::ZERO; V5_C_FREE_COORDINATES];
        for value in &mut free {
            *value = sample_qm31(source)?;
        }
        Ok(Self::encode_free_coordinates(&free))
    }

    /// Linear bijection from `K^1023` to the kernel of the inactive
    /// functional.  The pivot coefficient is one, so no inversion is needed.
    pub fn encode_free_coordinates(free: &[QM31; V5_C_FREE_COORDINATES]) -> Self {
        let (values, masks) = match v5_c_encode_free_coordinates_checked(free) {
            V5CEncodeCorrespondence::Encoded(values, masks) => (values, masks),
            V5CEncodeCorrespondence::MissingPivot => {
                panic!("atomic-v3 inactive functional is nonzero")
            }
        };
        debug_assert_eq!(
            v5_c_inactive_functional_with_masks(&values, &masks),
            QM31::ZERO
        );
        Self { values }
    }

    pub const fn values(&self) -> &[QM31; V5_C_ROWS] {
        &self.values
    }

    pub fn into_values(self) -> [QM31; V5_C_ROWS] {
        self.values
    }

    /// Recover the independent coordinates.  Together with
    /// `encode_free_coordinates`, this makes the kernel bijection executable.
    pub fn free_coordinates(&self) -> [QM31; V5_C_FREE_COORDINATES] {
        match v5_c_free_coordinates_checked(&self.values) {
            V5CDecodeCorrespondence::Decoded(free) => free,
            V5CDecodeCorrespondence::MissingPivot => {
                panic!("atomic-v3 inactive functional is nonzero")
            }
        }
    }

    /// The three ordinary MLE claims plus the fourth structured terminal
    /// functional already budgeted by the v5 relation.
    pub fn relation_claims(
        &self,
        point: &[QM31; 10],
        terminal_covector: &[QM31; V5_C_ROWS],
    ) -> [QM31; V5_C_TOTAL_CLAIMS] {
        let points = [*point, binary_successor_point(point), xor12_point(point)];
        let mut claims = [QM31::ZERO; V5_C_TOTAL_CLAIMS];
        for (index, evaluation_point) in points.iter().enumerate() {
            claims[index] = crate::multilinear_eval_extension(&self.values, evaluation_point);
        }
        claims[V5_C_POINT_CLAIMS] = v5_c_dot(&self.values, terminal_covector);
        claims
    }
}

fn v5_c_encode_free_coordinates_checked(
    free: &[QM31; V5_C_FREE_COORDINATES],
) -> V5CEncodeCorrespondence {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    v5_c_encode_free_coordinates_checked_with_masks(free, masks)
}

fn v5_c_encode_free_coordinates_checked_with_masks(
    free: &[QM31; V5_C_FREE_COORDINATES],
    masks: [u16; 64],
) -> V5CEncodeCorrespondence {
    let pivot = v5_c_pivot_row_with_masks(&masks);
    if pivot == V5_C_ROWS {
        return V5CEncodeCorrespondence::MissingPivot;
    }
    let values = v5_c_encode_free_coordinates_with_pivot_and_masks(free, pivot, &masks);
    V5CEncodeCorrespondence::Encoded(values, masks)
}

fn v5_c_free_coordinates_checked(values: &[QM31; V5_C_ROWS]) -> V5CDecodeCorrespondence {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    v5_c_free_coordinates_checked_with_masks(values, &masks)
}

fn v5_c_free_coordinates_checked_with_masks(
    values: &[QM31; V5_C_ROWS],
    masks: &[u16; 64],
) -> V5CDecodeCorrespondence {
    let pivot = v5_c_pivot_row_with_masks(masks);
    if pivot == V5_C_ROWS {
        return V5CDecodeCorrespondence::MissingPivot;
    }
    V5CDecodeCorrespondence::Decoded(v5_c_free_coordinates_with_pivot(values, pivot))
}

fn v5_c_encode_free_coordinates_correspondence(
    free: &[QM31; V5_C_FREE_COORDINATES],
) -> V5CEncodeCorrespondence {
    v5_c_encode_free_coordinates_checked(free)
}

fn v5_c_free_coordinates_correspondence(values: &[QM31; V5_C_ROWS]) -> V5CDecodeCorrespondence {
    v5_c_free_coordinates_checked(values)
}

fn v5_c_encode_free_coordinates_with_pivot_and_masks(
    free: &[QM31; V5_C_FREE_COORDINATES],
    pivot: usize,
    masks: &[u16; 64],
) -> [QM31; V5_C_ROWS] {
    let mut values = [QM31::ZERO; V5_C_ROWS];
    let mut coordinate = 0;
    while coordinate < V5_C_FREE_COORDINATES {
        values[free_coordinate_row(coordinate, pivot)] = free[coordinate];
        coordinate += 1;
    }
    values[pivot] = v5_c_inactive_functional_with_masks(&values, masks).neg();
    values
}

fn v5_c_free_coordinates_with_pivot(
    values: &[QM31; V5_C_ROWS],
    pivot: usize,
) -> [QM31; V5_C_FREE_COORDINATES] {
    let mut free = [QM31::ZERO; V5_C_FREE_COORDINATES];
    let mut coordinate = 0;
    while coordinate < V5_C_FREE_COORDINATES {
        free[coordinate] = values[free_coordinate_row(coordinate, pivot)];
        coordinate += 1;
    }
    free
}

/// First coefficient-one row of the exact atomic-v3 inactive functional.
pub fn v5_c_pivot_row() -> usize {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    let pivot = v5_c_pivot_row_with_masks(&masks);
    if pivot == V5_C_ROWS {
        panic!("atomic-v3 inactive functional is nonzero");
    }
    pivot
}

fn v5_c_pivot_row_with_masks(masks: &[u16; 64]) -> usize {
    let mut row = 0;
    while row < V5_C_ROWS {
        if inactive_row(masks, row) {
            return row;
        }
        row += 1;
    }
    V5_C_ROWS
}

/// Exact functional installed by the atomic-v3 PCS relation.
pub fn v5_c_inactive_functional(values: &[QM31; V5_C_ROWS]) -> QM31 {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    v5_c_inactive_functional_with_masks(values, &masks)
}

fn v5_c_inactive_functional_with_masks(values: &[QM31; V5_C_ROWS], masks: &[u16; 64]) -> QM31 {
    let mut sum = QM31::ZERO;
    let mut row = 0;
    while row < V5_C_ROWS {
        if inactive_row(masks, row) {
            sum = sum.add(values[row]);
        }
        row += 1;
    }
    sum
}

pub fn v5_c_dot(left: &[QM31; V5_C_ROWS], right: &[QM31; V5_C_ROWS]) -> QM31 {
    left.iter()
        .copied()
        .zip(right.iter().copied())
        .fold(QM31::ZERO, |sum, (left, right)| sum.add(left.mul(right)))
}

fn inactive_row(masks: &[u16; 64], row: usize) -> bool {
    masks[row >> 4u32] & (1u16 << ((row & 15usize) as u32)) != 0
}

fn free_coordinate_row(coordinate: usize, pivot: usize) -> usize {
    debug_assert!(coordinate < V5_C_FREE_COORDINATES);
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

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn free(seed: u32) -> [QM31; V5_C_FREE_COORDINATES] {
        core::array::from_fn(|coordinate| q(seed + coordinate as u32))
    }

    #[test]
    fn full_kernel_encoding_is_bijective_and_atomic_v3_exact() {
        let coordinates = free(10_000);
        let lane = V5ComponentCLane::encode_free_coordinates(&coordinates);
        let pivot = v5_c_pivot_row();
        let masks = atomic_state_only_copy_inactive_row_masks_v3();

        assert!(inactive_row(&masks, pivot));
        assert_eq!(v5_c_inactive_functional(lane.values()), QM31::ZERO);
        assert_eq!(lane.free_coordinates(), coordinates);
        assert_eq!(V5_C_FREE_COORDINATES, 1023);
    }

    #[test]
    fn sampler_is_nontrivial_and_stays_in_the_kernel() {
        let lane = V5ComponentCLane::sample(&mut XorShift(0xc031_5eed_71a4_902d)).unwrap();
        assert!(lane.values().iter().any(|value| *value != QM31::ZERO));
        assert_eq!(v5_c_inactive_functional(lane.values()), QM31::ZERO);
    }

    #[test]
    fn four_claims_match_literal_linear_functionals() {
        let lane = V5ComponentCLane::encode_free_coordinates(&free(20_000));
        let point = core::array::from_fn(|coordinate| q(30_000 + coordinate as u32));
        let terminal = core::array::from_fn(|row| q(40_000 + row as u32));
        let claims = lane.relation_claims(&point, &terminal);
        let points = [point, binary_successor_point(&point), xor12_point(&point)];

        for index in 0..V5_C_POINT_CLAIMS {
            assert_eq!(
                claims[index],
                crate::multilinear_eval_extension(lane.values(), &points[index])
            );
        }
        assert_eq!(claims[3], v5_c_dot(lane.values(), &terminal));
    }

    #[test]
    fn every_free_coordinate_survives_round_trip() {
        let pivot = v5_c_pivot_row();
        for coordinate in 0..V5_C_FREE_COORDINATES {
            let mut basis = [QM31::ZERO; V5_C_FREE_COORDINATES];
            basis[coordinate] = QM31::ONE;
            let lane = V5ComponentCLane::encode_free_coordinates(&basis);
            assert_eq!(lane.free_coordinates(), basis);
            assert_eq!(v5_c_inactive_functional(lane.values()), QM31::ZERO);
            assert_eq!(
                lane.values()[free_coordinate_row(coordinate, pivot)],
                QM31::ONE
            );
        }
    }

    #[test]
    fn correspondence_entrypoints_match_public_entrypoints_and_fail_closed() {
        for seed in 0..32 {
            let coordinates = free(50_000 + seed * 2_000);
            let lane = V5ComponentCLane::encode_free_coordinates(&coordinates);
            let V5CEncodeCorrespondence::Encoded(values, masks) =
                v5_c_encode_free_coordinates_correspondence(&coordinates)
            else {
                panic!("production atomic-v3 table has no Component-C pivot")
            };
            assert_eq!(values, *lane.values());
            assert_eq!(masks, atomic_state_only_copy_inactive_row_masks_v3());
            let V5CDecodeCorrespondence::Decoded(decoded) =
                v5_c_free_coordinates_correspondence(lane.values())
            else {
                panic!("production atomic-v3 table has no Component-C pivot")
            };
            assert_eq!(decoded, lane.free_coordinates());
        }

        let no_inactive_rows = [0u16; 64];
        let coordinates = free(120_000);
        let values = [QM31::ZERO; V5_C_ROWS];
        assert!(matches!(
            v5_c_encode_free_coordinates_checked_with_masks(&coordinates, no_inactive_rows),
            V5CEncodeCorrespondence::MissingPivot
        ));
        assert!(matches!(
            v5_c_free_coordinates_checked_with_masks(&values, &no_inactive_rows),
            V5CDecodeCorrespondence::MissingPivot
        ));
    }
}
