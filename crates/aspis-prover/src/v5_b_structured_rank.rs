//! Exact host-only rank probes for the structured component-B row map.
//!
//! This module is test-only. It checks one candidate commitment layout against
//! the real atomic-v3 copy-inactive functional, Component A's 95-dimensional
//! constrained mask slice, and the frozen q18 release schedule. The measured
//! transcript ranks are facts about that schedule, not a proof for every
//! future Fiat--Shamir transcript.

use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_spend_transcript_schedule_host_v3, StateOnlySpendPrefix,
    STATE_ONLY_SPEND_QUERY_COUNT,
};
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::{atomic_payment_statement_digest_v4, binary_successor_point, xor12_point};

use super::v5_a_full_view_rank::{
    inactive_kernel_messages, m31_rank, qm31_coordinates, release_statement,
};
use super::{qm31_rank, v5_encoder, V5_FIBRE_SIZE, V5_TRACE_ROWS};
use crate::{multilinear_eval, multilinear_eval_extension, HOST_HASH};

const CURRENT_V5_EMAT_ARTIFACT: &str = "../../results/spend/v5_component_c_frozen_q18_emat.bin";

const RELEASE_PROOF: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/fixtures/spend_q18_g37_release.bin"
));

const ROUND_BLOCKS: [usize; 10] = [0, 1, 2, 3, 4, 5, 6, 28, 29, 30];
const ROUND_BLOCK_ROWS: usize = 32;
const ROUND_COEFFICIENTS: usize = 28;
const ROUND_FREE_COEFFICIENTS: usize = 27;
const INITIAL_CLAIM_ROW: usize = 992;
const INACTIVE_PIVOT_ROW: usize = 993;
const PAD_START: usize = 224;
const PAD_COUNT: usize = 255;
const STATE_DIMENSION: usize = 1 + 10 * ROUND_FREE_COEFFICIENTS;
const PHYSICAL_FREE_DIMENSION: usize = STATE_DIMENSION + PAD_COUNT;
const AFFINE_FREE_DIMENSION: usize = PHYSICAL_FREE_DIMENSION + 1;

const _: () = assert!(STATE_DIMENSION == 271);
const _: () = assert!(PHYSICAL_FREE_DIMENSION == 526);
const _: () = assert!(AFFINE_FREE_DIMENSION == 527);
const _: () = assert!(PAD_START + PAD_COUNT == 479);

fn block_row(round: usize, offset: usize) -> usize {
    ROUND_BLOCKS[round] * ROUND_BLOCK_ROWS + offset
}

fn atomic_inactive(row: usize) -> bool {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    masks[row >> 4] & (1 << (row & 15)) != 0
}

/// The public terminal functional for the candidate row layout.
///
/// Round `i` occupies one 32-row aligned block. Only the degree-27
/// coefficients at offsets 0..27 receive weights. Offsets 28..31 are zero in
/// both the component-B message and this functional, so soundness does not
/// assume that unauthenticated slack is zero. The same 28 weights act on the
/// corresponding C1 semantic-lane rows after relation batching.
fn structured_terminal_covector(point: &[QM31; 10]) -> [QM31; V5_TRACE_ROWS] {
    let half = QM31::ONE.half();
    let mut covector = [QM31::ZERO; V5_TRACE_ROWS];
    covector[INITIAL_CLAIM_ROW] = half.pow(10);
    for (round, challenge) in point.iter().copied().enumerate() {
        let scale = half.pow((9 - round) as u64);
        let mut power = QM31::ONE;
        for offset in 0..ROUND_COEFFICIENTS {
            covector[block_row(round, offset)] = scale.mul(power);
            power = power.mul(challenge);
        }
    }
    covector
}

fn frozen_schedule() -> ([QM31; 10], Vec<usize>) {
    let statement = release_statement();
    let statement_digest = atomic_payment_statement_digest_v4(&statement, HOST_HASH).unwrap();
    let (prefix, suffix) = StateOnlySpendPrefix::parse_from_proof(RELEASE_PROOF).unwrap();
    assert!(!suffix.is_empty());
    let schedule = run_atomic_state_only_spend_transcript_schedule_host_v3(
        HOST_HASH,
        &prefix,
        &statement_digest,
    )
    .unwrap();
    assert_eq!(
        schedule.query_count,
        usize::from(STATE_ONLY_SPEND_QUERY_COUNT)
    );

    let encoder = v5_encoder();
    let indices = derive_circle_line_query_indices_for_count(
        &schedule.queries[..schedule.query_count],
        encoder.codeword_len() / V5_FIBRE_SIZE,
    )
    .unwrap();
    let positions = indices
        .layer0
        .iter()
        .flat_map(|query| {
            (0..V5_FIBRE_SIZE).map(move |slot| *query as usize * V5_FIBRE_SIZE + slot)
        })
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 72);
    (schedule.prefix.z, positions)
}

fn c1_view_matrix(point: &[QM31; 10], positions: &[usize]) -> Vec<Vec<M31>> {
    let basis = inactive_kernel_messages();
    assert_eq!(basis.len(), 95);
    let encoder = v5_encoder();
    let mle_points = [*point, binary_successor_point(point), xor12_point(point)];
    let dense = structured_terminal_covector(point);
    let mut observations = vec![vec![M31::ZERO; basis.len()]; 88];

    for (column, message) in basis.iter().enumerate() {
        let mut output = 0;
        for &position in positions {
            let value = (896..=991).fold(M31::ZERO, |sum, row| {
                sum.add(
                    message[row].mul(
                        encoder
                            .encode_c1_basis_value(row, position)
                            .expect("real encoder basis position"),
                    ),
                )
            });
            observations[output][column] = value;
            output += 1;
        }
        for mle_point in &mle_points {
            for coordinate in qm31_coordinates(multilinear_eval(message, mle_point)) {
                observations[output][column] = coordinate;
                output += 1;
            }
        }
        let dense_value = message
            .iter()
            .copied()
            .zip(dense.iter().copied())
            .fold(QM31::ZERO, |sum, (value, weight)| {
                sum.add(weight.mul_m31(value))
            });
        for coordinate in qm31_coordinates(dense_value) {
            observations[output][column] = coordinate;
            output += 1;
        }
        assert_eq!(output, 88);
    }
    observations
}

fn inactive_sum(values: &[QM31; V5_TRACE_ROWS]) -> QM31 {
    values
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| atomic_inactive(*row))
        .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
}

/// Linear test fixture for the component-B physical message map.
fn encode_b_message(
    state: &[QM31; STATE_DIMENSION],
    pads: &[QM31; PAD_COUNT],
    pivot_pad: QM31,
) -> [QM31; V5_TRACE_ROWS] {
    let mut values = [QM31::ZERO; V5_TRACE_ROWS];
    let half = QM31::ONE.half();
    values[INITIAL_CLAIM_ROW] = state[0];

    for round in 0..10 {
        let state_start = 1 + round * ROUND_FREE_COEFFICIENTS;
        let mut tail_sum = QM31::ZERO;
        for offset in 1..ROUND_COEFFICIENTS {
            let value = state[state_start + offset - 1];
            values[block_row(round, offset)] = value;
            tail_sum = tail_sum.add(value);
        }
        values[block_row(round, 0)] = tail_sum.neg().mul(half);
    }

    for (offset, pad) in pads.iter().copied().enumerate() {
        values[PAD_START + offset] = pad;
    }
    values[INACTIVE_PIVOT_ROW] = pivot_pad.add(inactive_sum(&values).neg());
    assert_eq!(inactive_sum(&values), pivot_pad);
    values
}

fn encode_pad_basis(pad: usize) -> [QM31; V5_TRACE_ROWS] {
    let mut values = [QM31::ZERO; V5_TRACE_ROWS];
    let row = PAD_START + pad;
    values[row] = QM31::ONE;
    if atomic_inactive(row) {
        values[INACTIVE_PIVOT_ROW] = QM31::ONE.neg();
    }
    assert_eq!(inactive_sum(&values), QM31::ZERO);
    values
}

fn terminal_from_state(state: &[QM31; STATE_DIMENSION], point: &[QM31; 10]) -> QM31 {
    let half = QM31::ONE.half();
    let mut terminal = half.pow(10).mul(state[0]);
    for (round, challenge) in point.iter().copied().enumerate() {
        let scale = half.pow((9 - round) as u64);
        let state_start = 1 + round * ROUND_FREE_COEFFICIENTS;
        let mut tail_sum = QM31::ZERO;
        for offset in 1..ROUND_COEFFICIENTS {
            tail_sum = tail_sum.add(state[state_start + offset - 1]);
        }
        let mut polynomial = tail_sum.neg().mul(half);
        let mut power = challenge;
        for offset in 1..ROUND_COEFFICIENTS {
            polynomial = polynomial.add(state[state_start + offset - 1].mul(power));
            power = power.mul(challenge);
        }
        terminal = terminal.add(scale.mul(polynomial));
    }
    terminal
}

fn q(seed: u32) -> QM31 {
    use aspis_core::field::CM31;
    QM31 {
        c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
        c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
    }
}

#[test]
fn structured_claim_reaches_rank_88_on_the_frozen_schedule() {
    let (point, positions) = frozen_schedule();
    let observations = c1_view_matrix(&point, &positions);
    assert_eq!(m31_rank(&observations[..72]), 72);
    assert_eq!(m31_rank(&observations[..84]), 84);
    assert_eq!(m31_rank(&observations), 88);

    let dense = structured_terminal_covector(&point);
    assert!(dense[..224].iter().any(|value| !value.is_zero()));
    assert!(dense[224..896].iter().all(|value| value.is_zero()));
    for round in 7..10 {
        assert!((0..ROUND_COEFFICIENTS).all(|offset| !dense[block_row(round, offset)].is_zero()));
        assert!((ROUND_COEFFICIENTS..ROUND_BLOCK_ROWS)
            .all(|offset| dense[block_row(round, offset)].is_zero()));
    }
    assert!(!dense[INITIAL_CLAIM_ROW].is_zero());
    assert!(dense[993..].iter().all(|value| value.is_zero()));
}

#[test]
fn boolean_challenge_is_a_counterexample_to_universal_rank_88() {
    let (_, positions) = frozen_schedule();
    let point = [QM31::ZERO; 10];
    let observations = c1_view_matrix(&point, &positions);
    assert_eq!(m31_rank(&observations[..72]), 72);
    assert_eq!(m31_rank(&observations[..84]), 72);
    assert_eq!(m31_rank(&observations), 73);

    // At a base-field Boolean point the four M31 coordinate rows of the dense
    // QM31 claim collapse to at most one row. Hence the rank-88 result above is
    // schedule-specific and cannot be promoted to deterministic availability.
    assert!(observations[85..88]
        .iter()
        .all(|row| row.iter().all(|value| value.is_zero())));
}

#[test]
fn structured_b_physical_map_has_271_state_and_255_pad_dimensions() {
    assert_eq!(ROUND_BLOCKS, [0, 1, 2, 3, 4, 5, 6, 28, 29, 30]);
    assert!(atomic_inactive(INACTIVE_PIVOT_ROW));
    assert!((896..=991).all(atomic_inactive));

    let state = core::array::from_fn::<_, STATE_DIMENSION, _>(|index| q(index as u32 + 1));
    let pads = core::array::from_fn::<_, PAD_COUNT, _>(|index| q(index as u32 + 10_000));
    let pivot_pad = q(19_999);
    let message = encode_b_message(&state, &pads, pivot_pad);

    assert_eq!(message[INITIAL_CLAIM_ROW], state[0]);
    for round in 0..10 {
        let state_start = 1 + round * ROUND_FREE_COEFFICIENTS;
        for offset in 1..ROUND_COEFFICIENTS {
            assert_eq!(
                message[block_row(round, offset)],
                state[state_start + offset - 1]
            );
        }
        assert!((ROUND_COEFFICIENTS..ROUND_BLOCK_ROWS)
            .all(|offset| message[block_row(round, offset)].is_zero()));
    }
    for (offset, expected) in pads.iter().copied().enumerate() {
        assert_eq!(message[PAD_START + offset], expected);
    }
    assert_eq!(inactive_sum(&message), pivot_pad);

    let point = core::array::from_fn(|index| q(index as u32 + 20_000));
    let covector = structured_terminal_covector(&point);
    let opening = message
        .iter()
        .copied()
        .zip(covector)
        .fold(QM31::ZERO, |sum, (value, weight)| {
            sum.add(value.mul(weight))
        });
    assert_eq!(opening, terminal_from_state(&state, &point));

    // The first 526 independent inputs occur unchanged at distinct coordinate
    // rows: s0, every c1..c27, and every pad. The ten c0 values are dependent.
    // The caller-owned pivot pad is the 527th affine input and is recovered by
    // the inactive functional even though row 993 also cancels the other
    // inactive rows. This certifies the physical map only.
    assert_eq!(STATE_DIMENSION, 271);
    assert_eq!(PAD_COUNT, 255);
    assert_eq!(PHYSICAL_FREE_DIMENSION, 526);
    assert_eq!(AFFINE_FREE_DIMENSION, 527);
}

#[test]
fn frozen_pad_map_covers_72_raw_and_three_mle_values_but_not_dense() {
    let (point, positions) = frozen_schedule();
    let mle_points = [point, binary_successor_point(&point), xor12_point(&point)];
    let dense = structured_terminal_covector(&point);
    let encoder = v5_encoder();
    let mut observations = vec![vec![QM31::ZERO; PAD_COUNT]; 76];

    // Pin the sparse basis calculation below to the actual C2 encoder, rather
    // than relying only on the fact that C1 and C2 use the same M31 twiddles.
    let first_pad_message = encode_pad_basis(0);
    let first_pad_codeword = encoder.encode_c2_message(&first_pad_message).unwrap();
    for &position in &positions {
        let sparse = first_pad_message
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, value)| !value.is_zero())
            .fold(QM31::ZERO, |sum, (row, value)| {
                sum.add(
                    value.mul_m31(
                        encoder
                            .encode_c1_basis_value(row, position)
                            .expect("real encoder basis position"),
                    ),
                )
            });
        assert_eq!(sparse, first_pad_codeword[position]);
    }

    for pad in 0..PAD_COUNT {
        let message = encode_pad_basis(pad);
        let mut output = 0;
        for &position in &positions {
            observations[output][pad] = message
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, value)| !value.is_zero())
                .fold(QM31::ZERO, |sum, (row, value)| {
                    sum.add(
                        value.mul_m31(
                            encoder
                                .encode_c1_basis_value(row, position)
                                .expect("C1 and C2 share the row-basis transform"),
                        ),
                    )
                });
            output += 1;
        }
        for mle_point in &mle_points {
            observations[output][pad] = multilinear_eval_extension(&message, mle_point);
            output += 1;
        }
        observations[output][pad] = message
            .iter()
            .copied()
            .zip(dense)
            .fold(QM31::ZERO, |sum, (value, weight)| {
                sum.add(value.mul(weight))
            });
        output += 1;
        assert_eq!(output, 76);
    }

    assert_eq!(qm31_rank(&observations[..72]), 72);
    assert_eq!(qm31_rank(&observations[..75]), 75);
    assert!(observations[75].iter().all(|value| value.is_zero()));
    assert_eq!(qm31_rank(&observations), 75);
}

/// Re-run Component A's complete 88-coordinate rank check on the exact
/// frozen-v5 schedule used by the Component-C E artifact.  This keeps the
/// current structured terminal covector separate from the rejected older
/// dense-covector probe in `v5_a_full_view_rank`.
#[test]
#[ignore = "offline diagnostic; generate the current salted+p Emat artifact first"]
fn current_v5_emat_component_a_view_has_rank_88() {
    use std::path::Path;

    use super::component_c::v5_c_pivot_row;
    use super::component_c_emat::{
        validate_component_c_emat_artifact, V5ComponentCEmat, V5_C_EMAT_COLUMNS,
        V5_C_EMAT_LAYER_ZERO_ROWS, V5_C_EMAT_ROWS,
    };

    let artifact_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CURRENT_V5_EMAT_ARTIFACT);
    let artifact = std::fs::read(&artifact_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", artifact_path.display()));
    let view = validate_component_c_emat_artifact(&artifact).expect("canonical current E artifact");
    let entries = view
        .matrix_bytes
        .chunks_exact(16)
        .map(|bytes| QM31::from_le_bytes(bytes).expect("canonical E entry"))
        .collect::<Vec<_>>();
    let emat = V5ComponentCEmat::from_entries(entries).expect("76x1023 E matrix");

    let basis = inactive_kernel_messages();
    assert_eq!(basis.len(), 95);
    let pivot = v5_c_pivot_row();
    let mut observations = vec![vec![M31::ZERO; basis.len()]; 88];
    for (column, message) in basis.iter().enumerate() {
        let free: [QM31; V5_C_EMAT_COLUMNS] = core::array::from_fn(|coordinate| {
            let row = if coordinate < pivot {
                coordinate
            } else {
                coordinate + 1
            };
            QM31::from_cm31(CM31::from_m31(message[row]))
        });
        let output = emat.mul_vec(&free);

        for row in 0..V5_C_EMAT_LAYER_ZERO_ROWS {
            let coordinates = qm31_coordinates(output[row]);
            assert_eq!(coordinates[1..], [M31::ZERO; 3]);
            observations[row][column] = coordinates[0];
        }
        let mut row = V5_C_EMAT_LAYER_ZERO_ROWS;
        for value in &output[V5_C_EMAT_LAYER_ZERO_ROWS..V5_C_EMAT_ROWS] {
            for coordinate in qm31_coordinates(*value) {
                observations[row][column] = coordinate;
                row += 1;
            }
        }
        assert_eq!(row, 88);
    }

    assert_eq!(m31_rank(&observations[..72]), 72);
    assert_eq!(m31_rank(&observations[..84]), 84);
    assert_eq!(m31_rank(&observations), 88);
}

/// The same exact frozen-v5 E artifact sees all 76 Component-B released
/// coordinates from the actual 271 state plus 255 pad directions.  Pads alone
/// cover 75 rows; the structured state supplies the remaining terminal row.
#[test]
#[ignore = "offline diagnostic; generate the current salted+p Emat artifact first"]
fn current_v5_emat_component_b_physical_view_has_rank_76() {
    use std::path::Path;

    use super::component_c::{v5_c_pivot_row, V5ComponentCLane};
    use super::component_c_emat::{
        validate_component_c_emat_artifact, V5ComponentCEmat, V5_C_EMAT_COLUMNS, V5_C_EMAT_ROWS,
    };

    let artifact_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CURRENT_V5_EMAT_ARTIFACT);
    let artifact = std::fs::read(&artifact_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", artifact_path.display()));
    let view = validate_component_c_emat_artifact(&artifact).expect("canonical current E artifact");
    let entries = view
        .matrix_bytes
        .chunks_exact(16)
        .map(|bytes| QM31::from_le_bytes(bytes).expect("canonical E entry"))
        .collect::<Vec<_>>();
    let emat = V5ComponentCEmat::from_entries(entries).expect("76x1023 E matrix");
    let pivot = v5_c_pivot_row();

    let mut physical = Vec::with_capacity(PHYSICAL_FREE_DIMENSION);
    for coordinate in 0..STATE_DIMENSION {
        let mut state = [QM31::ZERO; STATE_DIMENSION];
        state[coordinate] = QM31::ONE;
        physical.push(encode_b_message(
            &state,
            &[QM31::ZERO; PAD_COUNT],
            QM31::ZERO,
        ));
    }
    for coordinate in 0..PAD_COUNT {
        physical.push(encode_pad_basis(coordinate));
    }
    assert_eq!(physical.len(), PHYSICAL_FREE_DIMENSION);

    let mut observations = vec![vec![QM31::ZERO; physical.len()]; V5_C_EMAT_ROWS];
    for (column, message) in physical.iter().enumerate() {
        let free: [QM31; V5_C_EMAT_COLUMNS] = core::array::from_fn(|coordinate| {
            let row = if coordinate < pivot {
                coordinate
            } else {
                coordinate + 1
            };
            message[row]
        });
        assert_eq!(
            V5ComponentCLane::encode_free_coordinates(&free).values(),
            message
        );
        for (row, value) in emat.mul_vec(&free).into_iter().enumerate() {
            observations[row][column] = value;
        }
    }

    let pad_start = STATE_DIMENSION;
    let pad_only = observations
        .iter()
        .map(|row| row[pad_start..].to_vec())
        .collect::<Vec<_>>();
    assert_eq!(qm31_rank(&pad_only), 75);
    assert_eq!(qm31_rank(&observations), 76);
}

/// Return `(old released, old joint, affine released, affine joint,
/// state block, pads+p restricted, independent triangular)` ranks for one
/// exact transcript schedule. This is shared with the real-host fixture so the
/// salted+p transcript, not only the older frozen release schedule, is checked
/// against the same 527 sampler directions.
pub(super) fn component_b_affine_joint_ranks(
    point: &[QM31; 10],
    positions: &[usize],
) -> [usize; 7] {
    assert_eq!(positions.len(), 72);
    let mle_points = [*point, binary_successor_point(point), xor12_point(point)];
    let terminal = structured_terminal_covector(point);
    let encoder = v5_encoder();

    let mut directions = Vec::with_capacity(AFFINE_FREE_DIMENSION);
    for coordinate in 0..STATE_DIMENSION {
        let mut state = [QM31::ZERO; STATE_DIMENSION];
        state[coordinate] = QM31::ONE;
        directions.push(encode_b_message(
            &state,
            &[QM31::ZERO; PAD_COUNT],
            QM31::ZERO,
        ));
    }
    for coordinate in 0..PAD_COUNT {
        directions.push(encode_pad_basis(coordinate));
    }
    let mut pivot_direction = [QM31::ZERO; V5_TRACE_ROWS];
    pivot_direction[INACTIVE_PIVOT_ROW] = QM31::ONE;
    directions.push(pivot_direction);
    assert_eq!(directions.len(), AFFINE_FREE_DIMENSION);

    // Row zero is ell(B); rows 1..=76 are the supplied schedule's complete B view:
    // 72 q18 layer-zero positions, three MLE claims, and the structured
    // terminal claim.
    let mut joint = vec![vec![QM31::ZERO; directions.len()]; 77];
    for (column, message) in directions.iter().enumerate() {
        joint[0][column] = inactive_sum(message);
        let mut output = 1;
        for &position in positions {
            joint[output][column] = message
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, value)| !value.is_zero())
                .fold(QM31::ZERO, |sum, (row, value)| {
                    sum.add(
                        value.mul_m31(
                            encoder
                                .encode_c1_basis_value(row, position)
                                .expect("C1 and C2 share the row-basis transform"),
                        ),
                    )
                });
            output += 1;
        }
        for mle_point in &mle_points {
            joint[output][column] = multilinear_eval_extension(message, mle_point);
            output += 1;
        }
        joint[output][column] = message
            .iter()
            .copied()
            .zip(terminal)
            .fold(QM31::ZERO, |sum, (value, weight)| {
                sum.add(value.mul(weight))
            });
        output += 1;
        assert_eq!(output, 77);
    }

    let old_joint = joint
        .iter()
        .map(|row| row[..PHYSICAL_FREE_DIMENSION].to_vec())
        .collect::<Vec<_>>();
    let old_released = old_joint[1..].to_vec();
    let full_released = joint[1..].to_vec();

    // The 271 pre-challenge sumcheck-mask coordinates are released in their
    // own block and occur literally at row 992 and offsets 1..27 of each
    // selected block. Once those are conditioned, only the 255 pads plus p
    // remain available to couple ell, 72 raw openings, and three MLE claims.
    // The structured terminal is omitted from that second target because it is
    // a deterministic functional of the already-fixed 271 state values.
    let mut state_block = vec![vec![QM31::ZERO; AFFINE_FREE_DIMENSION]; STATE_DIMENSION];
    for (column, message) in directions.iter().enumerate() {
        let mut row = 0;
        state_block[row][column] = message[INITIAL_CLAIM_ROW];
        row += 1;
        for round in 0..10 {
            for offset in 1..ROUND_COEFFICIENTS {
                state_block[row][column] = message[block_row(round, offset)];
                row += 1;
            }
        }
        assert_eq!(row, STATE_DIMENSION);
    }
    let state_left = state_block
        .iter()
        .map(|row| row[..STATE_DIMENSION].to_vec())
        .collect::<Vec<_>>();
    assert!(state_block
        .iter()
        .all(|row| row[STATE_DIMENSION..].iter().all(|value| value.is_zero())));
    let pads_and_p = joint[..76]
        .iter()
        .map(|row| row[STATE_DIMENSION..].to_vec())
        .collect::<Vec<_>>();
    assert!(joint[76][STATE_DIMENSION..]
        .iter()
        .all(|value| value.is_zero()));

    let state_rank = qm31_rank(&state_left);
    let pads_and_p_rank = qm31_rank(&pads_and_p);
    let ranks = [
        qm31_rank(&old_released),
        qm31_rank(&old_joint),
        qm31_rank(&full_released),
        qm31_rank(&joint),
        state_rank,
        pads_and_p_rank,
        state_rank + pads_and_p_rank,
    ];
    assert_eq!(joint[0][PHYSICAL_FREE_DIMENSION], QM31::ONE);
    assert_eq!(joint[76][PHYSICAL_FREE_DIMENSION], QM31::ZERO);
    ranks
}

/// Algebraic regression on the older frozen release schedule. The distinct
/// real-host salted+p schedule is checked in `v5_real_host_proof`.
#[test]
fn frozen_release_component_b_affine_joint_map_has_rank_77() {
    let (point, positions) = frozen_schedule();
    assert_eq!(
        component_b_affine_joint_ranks(&point, &positions),
        [76, 76, 76, 77, 271, 76, 347]
    );
}

/// Hcopy's independent inactive-row, zero-sum padding alone can match every
/// one of the 76 released Hcopy coordinates on the current frozen-v5
/// schedule.  This isolates the linear padding from the witness-dependent,
/// post-A derivation of the unpadded Hcopy word.
#[test]
#[ignore = "offline diagnostic; generate the current salted+p Emat artifact first"]
fn current_v5_emat_hcopy_padding_view_has_rank_76() {
    use std::path::Path;

    use super::component_c::{v5_c_pivot_row, V5ComponentCLane};
    use super::component_c_emat::{
        validate_component_c_emat_artifact, V5ComponentCEmat, V5_C_EMAT_COLUMNS, V5_C_EMAT_ROWS,
    };

    let artifact_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(CURRENT_V5_EMAT_ARTIFACT);
    let artifact = std::fs::read(&artifact_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", artifact_path.display()));
    let view = validate_component_c_emat_artifact(&artifact).expect("canonical current E artifact");
    let entries = view
        .matrix_bytes
        .chunks_exact(16)
        .map(|bytes| QM31::from_le_bytes(bytes).expect("canonical E entry"))
        .collect::<Vec<_>>();
    let emat = V5ComponentCEmat::from_entries(entries).expect("76x1023 E matrix");

    let inactive_rows = (0..V5_TRACE_ROWS)
        .filter(|row| atomic_inactive(*row))
        .collect::<Vec<_>>();
    let dependent = inactive_rows[0];
    let padding = inactive_rows[1..]
        .iter()
        .copied()
        .map(|row| {
            let mut message = [QM31::ZERO; V5_TRACE_ROWS];
            message[row] = QM31::ONE;
            message[dependent] = QM31::ONE.neg();
            assert_eq!(inactive_sum(&message), QM31::ZERO);
            message
        })
        .collect::<Vec<_>>();
    assert_eq!(padding.len(), inactive_rows.len() - 1);

    let pivot = v5_c_pivot_row();
    let mut observations = vec![vec![QM31::ZERO; padding.len()]; V5_C_EMAT_ROWS];
    for (column, message) in padding.iter().enumerate() {
        let free: [QM31; V5_C_EMAT_COLUMNS] = core::array::from_fn(|coordinate| {
            let row = if coordinate < pivot {
                coordinate
            } else {
                coordinate + 1
            };
            message[row]
        });
        assert_eq!(
            V5ComponentCLane::encode_free_coordinates(&free).values(),
            message
        );
        for (row, value) in emat.mul_vec(&free).into_iter().enumerate() {
            observations[row][column] = value;
        }
    }

    assert_eq!(qm31_rank(&observations), 76);
}
