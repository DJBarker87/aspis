//! Exact test support for Component-A and structured Component-B rank checks.
//!
//! This is deliberately test-only.  It supplies the exact inactive-kernel
//! basis and rank helpers used by the current structured-layout probes, plus a
//! Boolean-MLE counterexample showing why fibre injectivity alone cannot imply
//! deterministic rank for arbitrary Fiat--Shamir schedules.

use aspis_core::field::{M31, QM31};
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::{
    binary_successor_point, decode_asset_id_canonical, decode_digest_canonical, xor12_point,
    AtomicPaymentStatementV4, SpendPublic,
};

use super::{mask_m31_column, M31BlockMask, V5_MASK_B, V5_MASK_M, V5_TRACE_ROWS};
use crate::multilinear_eval;

fn decode_hex_32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64);
    let mut decoded = [0u8; 32];
    for (index, output) in decoded.iter_mut().enumerate() {
        *output = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    decoded
}

pub(super) fn release_statement() -> AtomicPaymentStatementV4 {
    let digest = |value: &str| decode_digest_canonical(&decode_hex_32(value)).unwrap();
    AtomicPaymentStatementV4 {
        pool: decode_hex_32("2605b65c88655a479c2bd504ae207556acd0d42c49a8eeaed8cdbca5a256ca70"),
        sequence: 0,
        spend: SpendPublic {
            anchor: digest("90bc3005a8029b06072f386dc6b1ee4e9b4ba513b126d033a96ecc49829cab5a"),
            nullifier: digest("890266278df8f3073cab562c6c7d89471363c46841748a1ef3b0432acd0afd5f"),
            output_commitment: digest(
                "69517012bd98fe78bef9b076069520614ef27f2fc7a0854f72e65055a2edc319",
            ),
            asset_id: decode_asset_id_canonical(17).unwrap(),
            fee: 1,
        },
        output_anchor: digest("9f5b8c2dc991e401f3538941af35fd29e00aa319edca8013c7260c61c2e7486e"),
        deployment_domain: decode_hex_32(
            "ba43feb01d7d7f5ee3f57a6481b202066c83c6c3e76020a619c1611abbd08c8f",
        ),
    }
}

fn coordinate_mask(coordinate: usize, scale: M31) -> M31BlockMask {
    let mut mask = M31BlockMask {
        p: [M31::ZERO; V5_MASK_M],
        q: [M31::ZERO; V5_MASK_M],
    };
    if coordinate < V5_MASK_M {
        mask.p[coordinate] = scale;
    } else {
        mask.q[coordinate - V5_MASK_M] = scale;
    }
    mask
}

fn add_coordinate(mask: &mut M31BlockMask, coordinate: usize, value: M31) {
    if coordinate < V5_MASK_M {
        mask.p[coordinate] = mask.p[coordinate].add(value);
    } else {
        let coordinate = coordinate - V5_MASK_M;
        mask.q[coordinate] = mask.q[coordinate].add(value);
    }
}

fn inactive_sum(message: &[M31]) -> M31 {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    message
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| masks[row >> 4] & (1 << (row & 15)) != 0)
        .fold(M31::ZERO, |sum, (_, value)| sum.add(value))
}

/// A basis of the 95-dimensional slice where component A preserves the
/// current copy-inactive zero claim.  Coordinates are the ordinary p/q
/// coefficients; `mask_m31_column` performs the real natural-basis change.
pub(super) fn inactive_kernel_messages() -> Vec<Vec<M31>> {
    let zero = [M31::ZERO; V5_TRACE_ROWS];
    let relation = core::array::from_fn::<_, V5_MASK_B, _>(|coordinate| {
        let message = mask_m31_column(&zero, &coordinate_mask(coordinate, M31::ONE)).unwrap();
        inactive_sum(&message)
    });
    let pivot = relation
        .iter()
        .position(|value| !value.is_zero())
        .expect("component A meets the nonzero inactive functional");
    let pivot_inverse = relation[pivot].inv();

    (0..V5_MASK_B)
        .filter(|&coordinate| coordinate != pivot)
        .map(|coordinate| {
            let mut mask = coordinate_mask(coordinate, M31::ONE);
            add_coordinate(
                &mut mask,
                pivot,
                relation[coordinate].neg().mul(pivot_inverse),
            );
            let message = mask_m31_column(&zero, &mask).unwrap();
            assert_eq!(inactive_sum(&message), M31::ZERO);
            message
        })
        .collect()
}

pub(super) fn qm31_coordinates(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

pub(super) fn m31_rank(matrix: &[Vec<M31>]) -> usize {
    let rows = matrix.len();
    let columns = matrix.first().map_or(0, Vec::len);
    let mut work = matrix.to_vec();
    let mut rank = 0;
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|&row| !work[row][column].is_zero()) else {
            continue;
        };
        work.swap(rank, pivot);
        let pivot_row = work[rank].clone();
        let inverse = pivot_row[column].inv();
        for (row, values) in work.iter_mut().enumerate() {
            if row == rank {
                continue;
            }
            let scale = values[column].mul(inverse);
            if scale.is_zero() {
                continue;
            }
            for (value, pivot_value) in values[column..].iter_mut().zip(&pivot_row[column..]) {
                *value = value.sub(scale.mul(*pivot_value));
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

#[test]
fn boolean_mle_schedule_is_a_rank_zero_counterexample_for_reserved_support() {
    let basis = inactive_kernel_messages();
    let z = [QM31::ZERO; 10];
    let points = [z, binary_successor_point(&z), xor12_point(&z)];
    let mut observations = vec![vec![M31::ZERO; basis.len()]; 12];
    for (column, message) in basis.iter().enumerate() {
        let mut output = 0;
        for point in &points {
            for coordinate in qm31_coordinates(multilinear_eval(message, point)) {
                observations[output][column] = coordinate;
                output += 1;
            }
        }
        assert_eq!(output, 12);
    }

    // All three Boolean points select active message rows.  A mask confined to
    // rows 896..991 is therefore zero at every one of them.  Boolean challenges
    // are rare under Fiat--Shamir, but they are not excluded by the wire, so the
    // twelve-row MLE rank cannot be a deterministic consequence of fibre
    // injectivity.
    assert!(observations
        .iter()
        .all(|row| row.iter().all(|value| value.is_zero())));
    assert_eq!(m31_rank(&observations), 0);
}
