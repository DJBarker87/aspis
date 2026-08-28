//! Host algebraic residuals for the merged-C1 Pool pair trace.
//!
//! The evaluator consumes the exact sixteen semantic columns produced by
//! `merge_pool_v1_pair_trace_banks_v1` and the complete pre-root ASPLATE1
//! public record. It expands every Poseidon row equation and all remaining
//! schedules, aliases, occupancy, append, frontier, value and padding
//! obligations without constructing a randomized oracle or verifier terminal.
//!
//! The old `current_root` is transcript-bound but deliberately not
//! reconstructed by these rows: the twenty late blocks prove the append from
//! the account-derived frontier/index to the candidate state. Consistency of
//! the redundant old root with that frontier is the inductive validated-Pool
//! state invariant at the production caller boundary.

use alloc::vec::Vec;

use aspis_core::field::M31;

use crate::{
    poseidon2::{
        evaluate_trace_round_pair, Digest, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK,
        POSEIDON2_WIDTH, RATE,
    },
    spend::{DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY, VALUE_LIMIT},
    state_only_trace::StateOnlyTraceFoundation,
};

use super::{
    pair_trace::{
        build_pool_v1_pair_copy_registry_v1, PoolV1PairCopyTupleV1, PoolV1PairCopyWeightV1,
        PoolV1PairTraceBankV1, PoolV1PairTupleLimbV1, POOL_V1_PAIR_VALUE_BITS,
        POOL_V1_PAIR_VALUE_COUNT,
    },
    pair_tree_hiding::{
        pool_v1_pair_relation_free_mask_cells_v1, POOL_V1_PAIR_COPY_ROW_LINKS_V1,
        POOL_V1_PAIR_RELATION_FREE_MASK_CELLS_V1,
    },
    pair_tree_profile::{
        pool_v1_pair_path_base_row_v1, PoolV1PairLatePublicStatementV1,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW, POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN,
        POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START, POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW, POOL_V1_PAIR_PRIVATE_DIRECTIONS,
        POOL_V1_PAIR_TRACE_BLOCK_ROWS, POOL_V1_PAIR_TRACE_COLUMNS, POOL_V1_PAIR_TRACE_ROWS,
        POOL_V1_PAIR_TREE_DEPTH, POOL_V1_PAIR_VALUE_AUX_ROW_START,
    },
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
    pool_v1_tree_parent,
};

pub const POOL_V1_PAIR_POSEIDON_SBOX_DEGREE: usize = 5;
pub const POOL_V1_PAIR_TWO_ROUND_INTRINSIC_DEGREE: usize = 25;
pub const POOL_V1_PAIR_BOOLEAN_INTRINSIC_DEGREE: usize = 2;
pub const POOL_V1_PAIR_AFFINE_INTRINSIC_DEGREE: usize = 1;
pub const POOL_V1_PAIR_MAX_INTRINSIC_DEGREE: usize = 25;
pub const POOL_V1_PAIR_SELECTED_ORACLE_INDIVIDUAL_DEGREE: usize = 26;
pub const POOL_V1_PAIR_ZEROCHECK_INDIVIDUAL_DEGREE: usize = 27;

pub const POOL_V1_PAIR_POSEIDON_RESIDUAL_COUNT: usize = 54 * 11 * POSEIDON2_WIDTH;
pub const POOL_V1_PAIR_TRANSFER_SCHEDULE_RESIDUAL_COUNT: usize = 978;
pub const POOL_V1_PAIR_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT: usize = 996;
pub const POOL_V1_PAIR_COPY_ALIAS_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_COPY_ROW_LINKS_V1 * POSEIDON2_WIDTH;
pub const POOL_V1_PAIR_PATH_ORDERING_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_PRIVATE_DIRECTIONS * DIGEST_ELEMS * 2;
pub const POOL_V1_PAIR_VALUE_BOOLEAN_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_VALUE_COUNT * POOL_V1_PAIR_VALUE_BITS;
pub const POOL_V1_PAIR_OCCUPANCY_RESIDUAL_COUNT: usize = 24;
pub const POOL_V1_PAIR_TRANSFER_PUBLIC_RESIDUAL_COUNT: usize = 4 * DIGEST_ELEMS + 3;
pub const POOL_V1_PAIR_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT: usize = 3 * DIGEST_ELEMS + 3;
pub const POOL_V1_PAIR_APPEND_PATH_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_TREE_DEPTH * DIGEST_ELEMS * 2;
pub const POOL_V1_PAIR_CANDIDATE_ROOT_RESIDUAL_COUNT: usize = DIGEST_ELEMS;
pub const POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_TREE_DEPTH * DIGEST_ELEMS;
pub const POOL_V1_PAIR_INDEX_SEQUENCE_RESIDUAL_COUNT: usize = 2;
pub const POOL_V1_PAIR_ZERO_PADDING_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_RELATION_FREE_MASK_CELLS_V1;
pub const POOL_V1_PAIR_TRANSFER_TOTAL_RESIDUAL_COUNT: usize = 17_849;
pub const POOL_V1_PAIR_WITHDRAWAL_TOTAL_RESIDUAL_COUNT: usize = 17_859;

const _: () = assert!(POOL_V1_PAIR_TWO_ROUND_INTRINSIC_DEGREE == 25);
const _: () = assert!(POOL_V1_PAIR_MAX_INTRINSIC_DEGREE == 25);
const _: () = assert!(POOL_V1_PAIR_ZEROCHECK_INDIVIDUAL_DEGREE == 27);
const _: () = assert!(POOL_V1_PAIR_POSEIDON_RESIDUAL_COUNT == 9_504);
const _: () = assert!(POOL_V1_PAIR_COPY_ALIAS_RESIDUAL_COUNT == 2_032);
const _: () = assert!(POOL_V1_PAIR_PATH_ORDERING_RESIDUAL_COUNT == 336);
const _: () = assert!(POOL_V1_PAIR_VALUE_BOOLEAN_RESIDUAL_COUNT == 90);
const _: () = assert!(POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT == 160);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairResidualClassV1 {
    PoseidonRoundPairs,
    Schedule,
    CopyAliases,
    DirectionBooleanity,
    PathOrdering,
    ValueBooleanity,
    ValueRecomposition,
    Conservation,
    Occupancy,
    PublicBindings,
    AppendPathBindings,
    CandidateRoot,
    CandidateFrontier,
    IndexSequence,
    ZeroPadding,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairConstraintResidualsV1 {
    pub poseidon_round_pairs: Vec<M31>,
    pub schedule: Vec<M31>,
    pub copy_aliases: Vec<M31>,
    pub direction_booleanity: [M31; POOL_V1_PAIR_PRIVATE_DIRECTIONS],
    pub path_ordering: Vec<M31>,
    pub value_booleanity: [[M31; POOL_V1_PAIR_VALUE_BITS]; POOL_V1_PAIR_VALUE_COUNT],
    pub value_recomposition: [M31; POOL_V1_PAIR_VALUE_COUNT],
    pub conservation: [M31; 2],
    pub occupancy: Vec<M31>,
    pub public_bindings: Vec<M31>,
    pub append_path_bindings: Vec<M31>,
    pub candidate_root: [M31; DIGEST_ELEMS],
    pub candidate_frontier: Vec<M31>,
    pub index_sequence: [M31; POOL_V1_PAIR_INDEX_SEQUENCE_RESIDUAL_COUNT],
    pub zero_padding: Vec<M31>,
}

impl PoolV1PairConstraintResidualsV1 {
    fn zero(values: &[M31]) -> bool {
        values.iter().all(|value| *value == M31::ZERO)
    }

    pub fn class_is_zero(&self, class: PoolV1PairResidualClassV1) -> bool {
        match class {
            PoolV1PairResidualClassV1::PoseidonRoundPairs => Self::zero(&self.poseidon_round_pairs),
            PoolV1PairResidualClassV1::Schedule => Self::zero(&self.schedule),
            PoolV1PairResidualClassV1::CopyAliases => Self::zero(&self.copy_aliases),
            PoolV1PairResidualClassV1::DirectionBooleanity => {
                Self::zero(&self.direction_booleanity)
            }
            PoolV1PairResidualClassV1::PathOrdering => Self::zero(&self.path_ordering),
            PoolV1PairResidualClassV1::ValueBooleanity => self
                .value_booleanity
                .iter()
                .flatten()
                .all(|value| *value == M31::ZERO),
            PoolV1PairResidualClassV1::ValueRecomposition => Self::zero(&self.value_recomposition),
            PoolV1PairResidualClassV1::Conservation => Self::zero(&self.conservation),
            PoolV1PairResidualClassV1::Occupancy => Self::zero(&self.occupancy),
            PoolV1PairResidualClassV1::PublicBindings => Self::zero(&self.public_bindings),
            PoolV1PairResidualClassV1::AppendPathBindings => Self::zero(&self.append_path_bindings),
            PoolV1PairResidualClassV1::CandidateRoot => Self::zero(&self.candidate_root),
            PoolV1PairResidualClassV1::CandidateFrontier => Self::zero(&self.candidate_frontier),
            PoolV1PairResidualClassV1::IndexSequence => Self::zero(&self.index_sequence),
            PoolV1PairResidualClassV1::ZeroPadding => Self::zero(&self.zero_padding),
        }
    }

    pub fn all_zero(&self) -> bool {
        [
            PoolV1PairResidualClassV1::PoseidonRoundPairs,
            PoolV1PairResidualClassV1::Schedule,
            PoolV1PairResidualClassV1::CopyAliases,
            PoolV1PairResidualClassV1::DirectionBooleanity,
            PoolV1PairResidualClassV1::PathOrdering,
            PoolV1PairResidualClassV1::ValueBooleanity,
            PoolV1PairResidualClassV1::ValueRecomposition,
            PoolV1PairResidualClassV1::Conservation,
            PoolV1PairResidualClassV1::Occupancy,
            PoolV1PairResidualClassV1::PublicBindings,
            PoolV1PairResidualClassV1::AppendPathBindings,
            PoolV1PairResidualClassV1::CandidateRoot,
            PoolV1PairResidualClassV1::CandidateFrontier,
            PoolV1PairResidualClassV1::IndexSequence,
            PoolV1PairResidualClassV1::ZeroPadding,
        ]
        .into_iter()
        .all(|class| self.class_is_zero(class))
    }

    pub fn residual_count(&self) -> usize {
        self.poseidon_round_pairs.len()
            + self.schedule.len()
            + self.copy_aliases.len()
            + self.direction_booleanity.len()
            + self.path_ordering.len()
            + POOL_V1_PAIR_VALUE_BOOLEAN_RESIDUAL_COUNT
            + self.value_recomposition.len()
            + self.conservation.len()
            + self.occupancy.len()
            + self.public_bindings.len()
            + self.append_path_bindings.len()
            + self.candidate_root.len()
            + self.candidate_frontier.len()
            + self.index_sequence.len()
            + self.zero_padding.len()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairConstraintResidualErrorV1 {
    Shape,
    InvalidWithdrawalAmount,
    PublicRecordMismatch,
    Layout,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PairVariant {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy)]
struct ConstraintPublic {
    variant: PairVariant,
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient_commitment: Option<Digest>,
    change_commitment: Digest,
    withdrawal_amount: Option<u32>,
}

#[inline(always)]
fn cell(trace: &StateOnlyTraceFoundation, block: usize, local_row: usize, lane: usize) -> M31 {
    trace.c1[lane][block * POOL_V1_PAIR_TRACE_BLOCK_ROWS + local_row]
}

#[inline(always)]
fn row_cell(trace: &StateOnlyTraceFoundation, row: usize, column: usize) -> M31 {
    trace.c1[column][row]
}

fn append_equal(left: M31, right: M31, output: &mut Vec<M31>) {
    output.push(left.sub(right));
}

fn append_digest_equal(left: &Digest, right: &Digest, output: &mut Vec<M31>) {
    for lane in 0..DIGEST_ELEMS {
        append_equal(left[lane], right[lane], output);
    }
}

fn trace_digest(trace: &StateOnlyTraceFoundation, block: usize) -> Digest {
    core::array::from_fn(|lane| cell(trace, block, 11, lane))
}

fn node_left(trace: &StateOnlyTraceFoundation, block: usize) -> Digest {
    core::array::from_fn(|lane| cell(trace, block, 12, lane))
}

fn node_right(trace: &StateOnlyTraceFoundation, block: usize) -> Digest {
    core::array::from_fn(|lane| {
        let value = cell(trace, block, 0, RATE + lane);
        if lane + 1 == DIGEST_ELEMS {
            value.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            value
        }
    })
}

fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
    let zero = [M31::ZERO; DIGEST_ELEMS];
    let mut roots = [zero; POOL_V1_PAIR_TREE_DEPTH + 1];
    roots[0] = pool_v1_tree_parent(&zero, &zero);
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
    }
    roots
}

fn append_poseidon_residuals(trace: &StateOnlyTraceFoundation, output: &mut Vec<M31>) {
    for block in 0..54 {
        for local_row in 0..11 {
            let mut input = core::array::from_fn(|lane| cell(trace, block, local_row, lane));
            if local_row == 0 {
                for lane in 0..RATE {
                    input[lane] = input[lane].add(cell(trace, block, 12, lane));
                }
            }
            let (_, expected) = evaluate_trace_round_pair(input, local_row)
                .expect("pair Poseidon local row lies in 0..11");
            for lane in 0..POSEIDON2_WIDTH {
                append_equal(
                    cell(trace, block, local_row + 1, lane),
                    expected[lane],
                    output,
                );
            }
        }
    }
}

fn append_sponge_schedule(
    trace: &StateOnlyTraceFoundation,
    block_start: usize,
    domain: M31,
    input_length: usize,
    chunk_lengths: &[usize],
    output: &mut Vec<M31>,
) {
    debug_assert_eq!(chunk_lengths.iter().sum::<usize>(), input_length);
    let mut initial = [M31::ZERO; POSEIDON2_WIDTH];
    initial[RATE] = domain;
    initial[RATE + 1] = M31(input_length as u32);
    for lane in 0..POSEIDON2_WIDTH {
        append_equal(cell(trace, block_start, 0, lane), initial[lane], output);
    }
    for offset in 1..chunk_lengths.len() {
        for lane in 0..POSEIDON2_WIDTH {
            append_equal(
                cell(trace, block_start + offset, 0, lane),
                cell(trace, block_start + offset - 1, 11, lane),
                output,
            );
        }
    }
    for (offset, chunk_length) in chunk_lengths.iter().copied().enumerate() {
        for lane in chunk_length..POSEIDON2_WIDTH {
            output.push(cell(trace, block_start + offset, 12, lane));
        }
    }
}

fn append_node_schedule(trace: &StateOnlyTraceFoundation, output: &mut Vec<M31>) {
    for block in (4..=24).chain(33..=53) {
        for lane in 0..RATE {
            output.push(cell(trace, block, 0, lane));
        }
        for lane in RATE..POSEIDON2_WIDTH {
            output.push(cell(trace, block, 12, lane));
        }
    }
}

fn append_fixed_zero_block(trace: &StateOnlyTraceFoundation, block: usize, output: &mut Vec<M31>) {
    for lane in 0..POSEIDON2_WIDTH {
        output.push(cell(trace, block, 0, lane));
        output.push(cell(trace, block, 12, lane));
    }
}

fn append_schedule_residuals(
    trace: &StateOnlyTraceFoundation,
    variant: PairVariant,
    output: &mut Vec<M31>,
) {
    append_sponge_schedule(trace, 0, DOMAIN_OWNER_KEY, 8, &[8], output);
    append_sponge_schedule(trace, 1, DOMAIN_NOTE, 18, &[8, 8, 2], output);
    append_node_schedule(trace, output);
    append_sponge_schedule(trace, 25, DOMAIN_NULLIFIER, 16, &[8, 8], output);
    match variant {
        PairVariant::PrivateTransfer => {
            append_sponge_schedule(trace, 27, DOMAIN_NOTE, 18, &[8, 8, 2], output)
        }
        PairVariant::Withdrawal => {
            for block in 27..=29 {
                append_fixed_zero_block(trace, block, output);
            }
        }
    }
    append_sponge_schedule(trace, 30, DOMAIN_NOTE, 18, &[8, 8, 2], output);
}

fn tuple_limb_value(trace: &StateOnlyTraceFoundation, limb: PoolV1PairTupleLimbV1) -> M31 {
    match limb {
        PoolV1PairTupleLimbV1::Zero => M31::ZERO,
        PoolV1PairTupleLimbV1::Cell { source, offset } => {
            // The checked merger makes both legacy bank names views of the
            // same committed semantic C1 column at the source row.
            let _bank: PoolV1PairTraceBankV1 = source.bank;
            row_cell(
                trace,
                usize::from(source.cell.row),
                usize::from(source.cell.column),
            )
            .add(offset)
        }
    }
}

fn append_tuple_equal(
    trace: &StateOnlyTraceFoundation,
    producer: PoolV1PairCopyTupleV1,
    consumer: PoolV1PairCopyTupleV1,
    weight: M31,
    output: &mut Vec<M31>,
) {
    for lane in 0..POSEIDON2_WIDTH {
        output.push(
            weight.mul(
                tuple_limb_value(trace, producer.limbs[lane])
                    .sub(tuple_limb_value(trace, consumer.limbs[lane])),
            ),
        );
    }
}

fn append_copy_alias_residuals(
    trace: &StateOnlyTraceFoundation,
    append_index: u64,
    variant: PairVariant,
    output: &mut Vec<M31>,
) -> Result<(), PoolV1PairConstraintResidualErrorV1> {
    for link in build_pool_v1_pair_copy_registry_v1()
        .map_err(|_| PoolV1PairConstraintResidualErrorV1::Layout)?
    {
        let weight = match link.weight {
            PoolV1PairCopyWeightV1::One => M31::ONE,
            PoolV1PairCopyWeightV1::PrivateTransferOnly => {
                M31(u32::from(variant == PairVariant::PrivateTransfer))
            }
            PoolV1PairCopyWeightV1::WithdrawalOnly => {
                M31(u32::from(variant == PairVariant::Withdrawal))
            }
            PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => {
                M31(1 - ((append_index >> level) & 1) as u32)
            }
            PoolV1PairCopyWeightV1::AppendCurrentRight { level } => {
                M31(((append_index >> level) & 1) as u32)
            }
        };
        append_tuple_equal(trace, link.producer, link.consumer, weight, output);
    }
    Ok(())
}

fn direction_cell(trace: &StateOnlyTraceFoundation, level: usize) -> M31 {
    let row = pool_v1_pair_path_base_row_v1(level).expect("pair path level");
    row_cell(trace, row, 0)
}

fn append_path_residuals(
    trace: &StateOnlyTraceFoundation,
    direction_booleanity: &mut [M31; POOL_V1_PAIR_PRIVATE_DIRECTIONS],
    ordering: &mut Vec<M31>,
) {
    for level in 0..POOL_V1_PAIR_PRIVATE_DIRECTIONS {
        let base = pool_v1_pair_path_base_row_v1(level).expect("pair path level");
        let bit = direction_cell(trace, level);
        direction_booleanity[level] = bit.mul(bit.sub(M31::ONE));
        for lane in 0..DIGEST_ELEMS {
            let current = row_cell(trace, base, 1 + lane);
            let sibling = row_cell(trace, base ^ 12, lane);
            let left = row_cell(trace, base + 1, lane);
            let right = row_cell(trace, base + 1, RATE + lane);
            ordering.push(left.sub(current.add(bit.mul(sibling.sub(current)))));
            ordering.push(right.sub(sibling.add(bit.mul(current.sub(sibling)))));
        }
    }
}

fn value_bit_cell(trace: &StateOnlyTraceFoundation, value: usize, bit: usize) -> M31 {
    let base = POOL_V1_PAIR_VALUE_AUX_ROW_START + 2 * value;
    let row = if bit < 10 {
        base
    } else if bit < 20 {
        base + 1
    } else {
        base ^ 12
    };
    row_cell(trace, row, bit % 10)
}

fn evaluate_value_residuals(
    trace: &StateOnlyTraceFoundation,
) -> (
    [[M31; POOL_V1_PAIR_VALUE_BITS]; POOL_V1_PAIR_VALUE_COUNT],
    [M31; POOL_V1_PAIR_VALUE_COUNT],
    [M31; 2],
) {
    let booleanity = core::array::from_fn(|value| {
        core::array::from_fn(|bit| {
            let bit = value_bit_cell(trace, value, bit);
            bit.mul(bit.sub(M31::ONE))
        })
    });
    let recomposition = core::array::from_fn(|value| {
        let reconstructed = (0..POOL_V1_PAIR_VALUE_BITS).fold(M31::ZERO, |sum, bit| {
            sum.add(value_bit_cell(trace, value, bit).mul(M31(1u32 << bit)))
        });
        row_cell(trace, POOL_V1_PAIR_VALUE_AUX_ROW_START + 2 * value, 10).sub(reconstructed)
    });
    let partial_row = POOL_V1_PAIR_VALUE_AUX_ROW_START + 6;
    let final_row = POOL_V1_PAIR_VALUE_AUX_ROW_START + 7;
    let conservation = [
        row_cell(trace, partial_row, 2).sub(row_cell(trace, partial_row, 0).sub(row_cell(
            trace,
            partial_row,
            1,
        ))),
        row_cell(trace, final_row, 0).sub(row_cell(trace, final_row, 1)),
    ];
    (booleanity, recomposition, conservation)
}

fn append_one_occupancy_row(trace: &StateOnlyTraceFoundation, row: usize, output: &mut Vec<M31>) {
    let occupied = row_cell(trace, row, 0);
    let inverse = row_cell(trace, row, POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN);
    let one_minus = M31::ONE.sub(occupied);
    let sentinel = row_cell(
        trace,
        row,
        POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START + DIGEST_ELEMS - 1,
    );
    output.push(occupied.mul(occupied.sub(M31::ONE)));
    output.push(sentinel.mul(inverse).sub(occupied));
    output.push(one_minus.mul(inverse));
    for lane in 0..DIGEST_ELEMS {
        output.push(one_minus.mul(row_cell(
            trace,
            row,
            POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START + lane,
        )));
    }
}

fn append_occupancy_residuals(
    trace: &StateOnlyTraceFoundation,
    variant: PairVariant,
    output: &mut Vec<M31>,
) {
    append_one_occupancy_row(trace, POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW, output);
    append_one_occupancy_row(trace, POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW, output);
    let input_occupied = row_cell(trace, POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW, 0);
    let selected = row_cell(
        trace,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
        POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN,
    );
    output.push(selected.mul(M31::ONE.sub(input_occupied)));
    let output_occupied = row_cell(trace, POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW, 0);
    let expected = M31(u32::from(variant == PairVariant::PrivateTransfer));
    // This variant gate is essential: a withdrawal appends exactly one note,
    // while a private transfer appends exactly two. Occupancy validity alone
    // would otherwise permit an unaccounted spendable second withdrawal note.
    output.push(output_occupied.sub(expected));
}

fn append_public_binding_residuals(
    trace: &StateOnlyTraceFoundation,
    public: ConstraintPublic,
    output: &mut Vec<M31>,
) {
    append_digest_equal(&trace_digest(trace, 24), &public.anchor, output);
    append_digest_equal(&trace_digest(trace, 26), &public.nullifier, output);
    if let Some(recipient) = public.recipient_commitment {
        append_digest_equal(&trace_digest(trace, 29), &recipient, output);
    }
    append_digest_equal(&trace_digest(trace, 32), &public.change_commitment, output);
    append_equal(cell(trace, 2, 12, 1), public.asset_id, output);
    if public.variant == PairVariant::PrivateTransfer {
        append_equal(cell(trace, 28, 12, 1), public.asset_id, output);
    } else {
        append_equal(
            row_cell(trace, POOL_V1_PAIR_VALUE_AUX_ROW_START + 2, 10),
            M31(public
                .withdrawal_amount
                .expect("withdrawal variant carries amount")),
            output,
        );
    }
    append_equal(cell(trace, 31, 12, 1), public.asset_id, output);
}

fn append_append_path_bindings(
    trace: &StateOnlyTraceFoundation,
    statement: &PoolV1PairLatePublicStatementV1,
    empty: &[Digest; POOL_V1_PAIR_TREE_DEPTH + 1],
    output: &mut Vec<M31>,
) {
    let append_index = statement.live_snapshot.next_pair_index;
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        let bit = ((append_index >> level) & 1) != 0;
        let current = trace_digest(trace, 33 + level);
        let sibling = if bit {
            statement.live_snapshot.frontier[level]
        } else {
            empty[level]
        };
        let (expected_left, expected_right) = if bit {
            (sibling, current)
        } else {
            (current, sibling)
        };
        append_digest_equal(&node_left(trace, 34 + level), &expected_left, output);
        append_digest_equal(&node_right(trace, 34 + level), &expected_right, output);
    }
}

fn candidate_frontier_expected(
    trace: &StateOnlyTraceFoundation,
    statement: &PoolV1PairLatePublicStatementV1,
    empty: &[Digest; POOL_V1_PAIR_TREE_DEPTH + 1],
    level: usize,
) -> Digest {
    let index = statement.live_snapshot.next_pair_index;
    let carry_level = core::cmp::min(index.trailing_ones() as usize, POOL_V1_PAIR_TREE_DEPTH);
    if level < carry_level {
        empty[level]
    } else if level == carry_level && carry_level < POOL_V1_PAIR_TREE_DEPTH {
        // Prehash current at level zero is the output pair (block 33); at
        // level k it is the output of append block 33+k.
        trace_digest(trace, 33 + level)
    } else if ((index >> level) & 1) == 0 {
        empty[level]
    } else {
        statement.live_snapshot.frontier[level]
    }
}

fn evaluate_append_result_residuals(
    trace: &StateOnlyTraceFoundation,
    statement: &PoolV1PairLatePublicStatementV1,
) -> (Vec<M31>, [M31; DIGEST_ELEMS], Vec<M31>, [M31; 2]) {
    let empty = pair_empty_roots();
    let mut append_path = Vec::with_capacity(POOL_V1_PAIR_APPEND_PATH_RESIDUAL_COUNT);
    append_append_path_bindings(trace, statement, &empty, &mut append_path);

    let terminal = trace_digest(trace, 53);
    let candidate_root = core::array::from_fn(|lane| {
        terminal[lane].sub(statement.candidate_afterstate.next_root[lane])
    });
    let mut candidate_frontier = Vec::with_capacity(POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT);
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        let expected = candidate_frontier_expected(trace, statement, &empty, level);
        append_digest_equal(
            &statement.candidate_afterstate.next_frontier[level],
            &expected,
            &mut candidate_frontier,
        );
    }
    let old_index = statement.live_snapshot.next_pair_index;
    let index_sequence = [
        M31(statement.live_snapshot.sequence as u32).sub(M31(old_index as u32)),
        M31(statement.candidate_afterstate.next_pair_index as u32)
            .sub(M31(old_index as u32).add(M31::ONE)),
    ];
    (
        append_path,
        candidate_root,
        candidate_frontier,
        index_sequence,
    )
}

fn append_zero_padding_residuals(
    trace: &StateOnlyTraceFoundation,
    output: &mut Vec<M31>,
) -> Result<(), PoolV1PairConstraintResidualErrorV1> {
    for target in pool_v1_pair_relation_free_mask_cells_v1()
        .map_err(|_| PoolV1PairConstraintResidualErrorV1::Layout)?
    {
        output.push(row_cell(
            trace,
            usize::from(target.row),
            usize::from(target.column),
        ));
    }
    Ok(())
}

fn evaluate_pair_constraint_residuals(
    public: ConstraintPublic,
    statement: &PoolV1PairLatePublicStatementV1,
    trace: &StateOnlyTraceFoundation,
) -> Result<PoolV1PairConstraintResidualsV1, PoolV1PairConstraintResidualErrorV1> {
    if trace.c1.len() != POOL_V1_PAIR_TRACE_COLUMNS
        || trace
            .c1
            .iter()
            .any(|column| column.len() != POOL_V1_PAIR_TRACE_ROWS)
    {
        return Err(PoolV1PairConstraintResidualErrorV1::Shape);
    }
    if public.pool != statement.live_snapshot.pool
        || public.deployment_domain != statement.live_snapshot.deployment_domain
        || statement.live_snapshot.sequence >= (1u64 << POOL_V1_PAIR_TREE_DEPTH)
        || statement.live_snapshot.next_pair_index >= (1u64 << POOL_V1_PAIR_TREE_DEPTH)
        || statement.candidate_afterstate.next_pair_index > (1u64 << POOL_V1_PAIR_TREE_DEPTH)
    {
        return Err(PoolV1PairConstraintResidualErrorV1::PublicRecordMismatch);
    }
    if let Some(amount) = public.withdrawal_amount {
        if amount >= VALUE_LIMIT {
            return Err(PoolV1PairConstraintResidualErrorV1::InvalidWithdrawalAmount);
        }
    }

    let mut poseidon_round_pairs = Vec::with_capacity(POOL_V1_PAIR_POSEIDON_RESIDUAL_COUNT);
    append_poseidon_residuals(trace, &mut poseidon_round_pairs);
    let expected_schedule = match public.variant {
        PairVariant::PrivateTransfer => POOL_V1_PAIR_TRANSFER_SCHEDULE_RESIDUAL_COUNT,
        PairVariant::Withdrawal => POOL_V1_PAIR_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT,
    };
    let mut schedule = Vec::with_capacity(expected_schedule);
    append_schedule_residuals(trace, public.variant, &mut schedule);
    let mut copy_aliases = Vec::with_capacity(POOL_V1_PAIR_COPY_ALIAS_RESIDUAL_COUNT);
    append_copy_alias_residuals(
        trace,
        statement.live_snapshot.next_pair_index,
        public.variant,
        &mut copy_aliases,
    )?;
    let mut direction_booleanity = [M31::ZERO; POOL_V1_PAIR_PRIVATE_DIRECTIONS];
    let mut path_ordering = Vec::with_capacity(POOL_V1_PAIR_PATH_ORDERING_RESIDUAL_COUNT);
    append_path_residuals(trace, &mut direction_booleanity, &mut path_ordering);
    let (value_booleanity, value_recomposition, conservation) = evaluate_value_residuals(trace);
    let mut occupancy = Vec::with_capacity(POOL_V1_PAIR_OCCUPANCY_RESIDUAL_COUNT);
    append_occupancy_residuals(trace, public.variant, &mut occupancy);
    let expected_public = match public.variant {
        PairVariant::PrivateTransfer => POOL_V1_PAIR_TRANSFER_PUBLIC_RESIDUAL_COUNT,
        PairVariant::Withdrawal => POOL_V1_PAIR_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT,
    };
    let mut public_bindings = Vec::with_capacity(expected_public);
    append_public_binding_residuals(trace, public, &mut public_bindings);
    let (append_path_bindings, candidate_root, candidate_frontier, index_sequence) =
        evaluate_append_result_residuals(trace, statement);
    let mut zero_padding = Vec::with_capacity(POOL_V1_PAIR_ZERO_PADDING_RESIDUAL_COUNT);
    append_zero_padding_residuals(trace, &mut zero_padding)?;

    debug_assert_eq!(
        poseidon_round_pairs.len(),
        POOL_V1_PAIR_POSEIDON_RESIDUAL_COUNT
    );
    debug_assert_eq!(schedule.len(), expected_schedule);
    debug_assert_eq!(copy_aliases.len(), POOL_V1_PAIR_COPY_ALIAS_RESIDUAL_COUNT);
    debug_assert_eq!(
        path_ordering.len(),
        POOL_V1_PAIR_PATH_ORDERING_RESIDUAL_COUNT
    );
    debug_assert_eq!(occupancy.len(), POOL_V1_PAIR_OCCUPANCY_RESIDUAL_COUNT);
    debug_assert_eq!(public_bindings.len(), expected_public);
    debug_assert_eq!(
        append_path_bindings.len(),
        POOL_V1_PAIR_APPEND_PATH_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        candidate_frontier.len(),
        POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT
    );
    debug_assert_eq!(zero_padding.len(), POOL_V1_PAIR_ZERO_PADDING_RESIDUAL_COUNT);

    Ok(PoolV1PairConstraintResidualsV1 {
        poseidon_round_pairs,
        schedule,
        copy_aliases,
        direction_booleanity,
        path_ordering,
        value_booleanity,
        value_recomposition,
        conservation,
        occupancy,
        public_bindings,
        append_path_bindings,
        candidate_root,
        candidate_frontier,
        index_sequence,
        zero_padding,
    })
}

pub fn evaluate_pool_v1_pair_private_transfer_constraint_residuals_v1(
    public: &PoolV1PrivateTransferPublicV1,
    statement: &PoolV1PairLatePublicStatementV1,
    trace: &StateOnlyTraceFoundation,
) -> Result<PoolV1PairConstraintResidualsV1, PoolV1PairConstraintResidualErrorV1> {
    evaluate_pair_constraint_residuals(
        ConstraintPublic {
            variant: PairVariant::PrivateTransfer,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient_commitment: Some(public.recipient_commitment),
            change_commitment: public.change_commitment,
            withdrawal_amount: None,
        },
        statement,
        trace,
    )
}

pub fn evaluate_pool_v1_pair_withdrawal_constraint_residuals_v1(
    public: &PoolV1WithdrawalPublicV1,
    statement: &PoolV1PairLatePublicStatementV1,
    trace: &StateOnlyTraceFoundation,
) -> Result<PoolV1PairConstraintResidualsV1, PoolV1PairConstraintResidualErrorV1> {
    evaluate_pair_constraint_residuals(
        ConstraintPublic {
            variant: PairVariant::Withdrawal,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient_commitment: None,
            change_commitment: public.change_commitment,
            withdrawal_amount: Some(public.amount),
        },
        statement,
        trace,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        derive_owner_key,
        pool_v1::{
            pair_trace::{
                compile_pool_v1_pair_private_transfer_merged_c1_v1,
                compile_pool_v1_pair_withdrawal_merged_c1_v1, verify_pool_v1_pair_copy_registry_v1,
                PoolV1PairInputNoteWitnessV1, PoolV1PairMergedC1CompilationV1,
                PoolV1PairPrivateTransferWitnessV1, PoolV1PairWithdrawalWitnessV1,
            },
            pool_v1_note_commitment, pool_v1_nullifier, IncrementalMerkleTreeV1,
            PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1, PoolV1PairLeafWitnessV1,
            PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        },
    };
    use aspis_core::field::{CM31, QM31};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
    }

    fn snapshot_at(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        index: u64,
    ) -> super::super::PoolV1PairLiveSnapshotV1 {
        let empty = pair_empty_roots();
        let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            empty[POOL_V1_PAIR_TREE_DEPTH],
            core::array::from_fn(|level| empty[level]),
            &empty,
        )
        .unwrap();
        for leaf in 0..index {
            tree = tree
                .append_one_with_empty_roots(digest(20_000 + 32 * leaf as u32), &empty)
                .unwrap()
                .0;
        }
        super::super::PoolV1PairLiveSnapshotV1 {
            pool,
            deployment_domain,
            sequence: index,
            next_pair_index: index,
            current_root: tree.root,
            frontier: tree.frontier,
        }
    }

    fn input_witness(value: u32) -> PoolV1PairInputNoteWitnessV1 {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset = M31(77);
        let owner = derive_owner_key(&nullifier_key);
        let input_commitment = pool_v1_note_commitment(&owner, value, asset, &salt);
        let pair_leaf =
            PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900)).unwrap();
        PoolV1PairInputNoteWitnessV1 {
            nullifier_key,
            salt,
            value,
            pair_leaf,
            selected_second: false,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                index: 0x5_4321,
            },
        }
    }

    fn input_anchor(input: &PoolV1PairInputNoteWitnessV1) -> Digest {
        let mut current = input.pair_leaf.leaf_digest().unwrap();
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            let sibling = input.membership.siblings[level];
            current = if ((input.membership.index >> level) & 1) == 0 {
                pool_v1_tree_parent(&current, &sibling)
            } else {
                pool_v1_tree_parent(&sibling, &current)
            };
        }
        current
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn context<'a>(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor: Digest,
        asset_id: M31,
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool,
                deployment_domain,
                anchor_sequence: 42,
                anchor_root: anchor,
                asset_id,
            },
            spent_nullifiers: &[],
        }
    }

    fn transfer_at(
        append_index: u64,
    ) -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PairMergedC1CompilationV1,
    ) {
        let input = input_witness(1_000);
        let recipient = output(300, 600);
        let change = output(500, 400);
        let witness = PoolV1PairPrivateTransferWitnessV1 {
            input,
            recipient,
            change,
        };
        let asset_id = M31(77);
        let anchor = input_anchor(&witness.input);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            recipient_commitment: pool_v1_note_commitment(
                &witness.recipient.owner_key,
                witness.recipient.value,
                asset_id,
                &witness.recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        let snapshot = snapshot_at(public.pool, public.deployment_domain, append_index);
        let compiled = compile_pool_v1_pair_private_transfer_merged_c1_v1(
            &public,
            &witness,
            context(public.pool, public.deployment_domain, anchor, asset_id),
            snapshot,
        )
        .unwrap();
        (public, compiled)
    }

    fn withdrawal_at(
        append_index: u64,
    ) -> (PoolV1WithdrawalPublicV1, PoolV1PairMergedC1CompilationV1) {
        let input = input_witness(1_000);
        let change = output(700, 750);
        let witness = PoolV1PairWithdrawalWitnessV1 { input, change };
        let asset_id = M31(77);
        let anchor = input_anchor(&witness.input);
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            amount: 250,
            destination_token_account: [9; 32],
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        let snapshot = snapshot_at(public.pool, public.deployment_domain, append_index);
        let compiled = compile_pool_v1_pair_withdrawal_merged_c1_v1(
            &public,
            &witness,
            context(public.pool, public.deployment_domain, anchor, asset_id),
            snapshot,
        )
        .unwrap();
        (public, compiled)
    }

    fn assert_nonzero(
        residuals: &PoolV1PairConstraintResidualsV1,
        class: PoolV1PairResidualClassV1,
    ) {
        assert!(
            !residuals.class_is_zero(class),
            "class unexpectedly zero: {class:?}"
        );
        assert!(!residuals.all_zero());
    }

    fn transfer_residuals(
        public: &PoolV1PrivateTransferPublicV1,
        compiled: &PoolV1PairMergedC1CompilationV1,
    ) -> PoolV1PairConstraintResidualsV1 {
        evaluate_pool_v1_pair_private_transfer_constraint_residuals_v1(
            public,
            &compiled.public_statement,
            &compiled.semantic_c1,
        )
        .unwrap()
    }

    #[test]
    fn honest_populated_variants_and_binary_carry_frontiers_are_exact() {
        assert_eq!(POOL_V1_PAIR_MAX_INTRINSIC_DEGREE, 25);
        assert_eq!(POOL_V1_PAIR_SELECTED_ORACLE_INDIVIDUAL_DEGREE, 26);
        assert_eq!(POOL_V1_PAIR_ZEROCHECK_INDIVIDUAL_DEGREE, 27);

        for index in [0, 1, 3, 13] {
            let (public, compiled) = transfer_at(index);
            let residuals = transfer_residuals(&public, &compiled);
            assert!(
                residuals.all_zero(),
                "transfer index={index}: {residuals:?}"
            );
            assert_eq!(
                residuals.residual_count(),
                POOL_V1_PAIR_TRANSFER_TOTAL_RESIDUAL_COUNT
            );
            assert_eq!(residuals.poseidon_round_pairs.len(), 9_504);
            assert_eq!(residuals.schedule.len(), 978);
            assert_eq!(residuals.copy_aliases.len(), 2_032);
            assert_eq!(residuals.path_ordering.len(), 336);
            assert_eq!(residuals.occupancy.len(), 24);
            assert_eq!(residuals.public_bindings.len(), 35);
            assert_eq!(residuals.append_path_bindings.len(), 320);
            assert_eq!(residuals.candidate_frontier.len(), 160);
            assert_eq!(residuals.zero_padding.len(), 4_334);
        }

        let (public, compiled) = withdrawal_at(13);
        let residuals = evaluate_pool_v1_pair_withdrawal_constraint_residuals_v1(
            &public,
            &compiled.public_statement,
            &compiled.semantic_c1,
        )
        .unwrap();
        for class in [
            PoolV1PairResidualClassV1::PoseidonRoundPairs,
            PoolV1PairResidualClassV1::Schedule,
            PoolV1PairResidualClassV1::CopyAliases,
            PoolV1PairResidualClassV1::DirectionBooleanity,
            PoolV1PairResidualClassV1::PathOrdering,
            PoolV1PairResidualClassV1::ValueBooleanity,
            PoolV1PairResidualClassV1::ValueRecomposition,
            PoolV1PairResidualClassV1::Conservation,
            PoolV1PairResidualClassV1::Occupancy,
            PoolV1PairResidualClassV1::PublicBindings,
            PoolV1PairResidualClassV1::AppendPathBindings,
            PoolV1PairResidualClassV1::CandidateRoot,
            PoolV1PairResidualClassV1::CandidateFrontier,
            PoolV1PairResidualClassV1::IndexSequence,
            PoolV1PairResidualClassV1::ZeroPadding,
        ] {
            if class == PoolV1PairResidualClassV1::CopyAliases && !residuals.class_is_zero(class) {
                let registry = build_pool_v1_pair_copy_registry_v1().unwrap();
                for (index, chunk) in residuals.copy_aliases.chunks_exact(16).enumerate() {
                    assert!(
                        chunk.iter().all(|value| *value == M31::ZERO),
                        "withdrawal nonzero copy link={index} kind={:?}",
                        registry[index].kind,
                    );
                }
            }
            assert!(residuals.class_is_zero(class), "withdrawal class={class:?}");
        }
        assert_eq!(residuals.schedule.len(), 996);
        assert_eq!(residuals.public_bindings.len(), 27);
        assert_eq!(
            residuals.residual_count(),
            POOL_V1_PAIR_WITHDRAWAL_TOTAL_RESIDUAL_COUNT
        );
        verify_pool_v1_pair_copy_registry_v1(
            &compiled.trace,
            13,
            QM31::from_cm31(CM31::from_m31(M31(19))),
            QM31::from_cm31(CM31::from_m31(M31(23))),
        )
        .unwrap();

        let mut changed_public = public;
        changed_public.amount += 1;
        let changed = evaluate_pool_v1_pair_withdrawal_constraint_residuals_v1(
            &changed_public,
            &compiled.public_statement,
            &compiled.semantic_c1,
        )
        .unwrap();
        assert_nonzero(&changed, PoolV1PairResidualClassV1::PublicBindings);
    }

    #[test]
    fn output_occupancy_is_exactly_the_payment_variant() {
        let (public, honest) = transfer_at(0);
        let mut forged_single = honest.clone();
        for column in 0..POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START + DIGEST_ELEMS {
            forged_single.semantic_c1.c1[column][POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW] = M31::ZERO;
        }
        let residuals = transfer_residuals(&public, &forged_single);
        assert!(residuals.occupancy[..23]
            .iter()
            .all(|value| *value == M31::ZERO));
        assert_ne!(residuals.occupancy[23], M31::ZERO);

        let (public, honest) = withdrawal_at(0);
        let mut forged_second = honest.clone();
        forged_second.semantic_c1.c1[0][POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW] = M31::ONE;
        forged_second.semantic_c1.c1[POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN]
            [POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW] = M31::ONE;
        forged_second.semantic_c1.c1
            [POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START + DIGEST_ELEMS - 1]
            [POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW] = M31::ONE;
        let residuals = evaluate_pool_v1_pair_withdrawal_constraint_residuals_v1(
            &public,
            &forged_second.public_statement,
            &forged_second.semantic_c1,
        )
        .unwrap();
        assert!(residuals.occupancy[..23]
            .iter()
            .all(|value| *value == M31::ZERO));
        assert_ne!(residuals.occupancy[23], M31::ZERO);
    }

    #[test]
    fn every_pair_residual_class_has_a_detected_mutation() {
        let (public, honest) = transfer_at(13);

        let mut changed = honest.clone();
        changed.semantic_c1.c1[7][10 * 16 + 6] =
            changed.semantic_c1.c1[7][10 * 16 + 6].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::PoseidonRoundPairs,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[0][4 * 16] = M31::ONE;
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::Schedule,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[2][POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW] =
            changed.semantic_c1.c1[2][POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::CopyAliases,
        );

        let mut changed = honest.clone();
        let direction_row = pool_v1_pair_path_base_row_v1(0).unwrap();
        changed.semantic_c1.c1[0][direction_row] = M31(2);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::DirectionBooleanity,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[0][direction_row] =
            M31::ONE.sub(changed.semantic_c1.c1[0][direction_row]);
        let residuals = transfer_residuals(&public, &changed);
        assert!(residuals.class_is_zero(PoolV1PairResidualClassV1::DirectionBooleanity));
        assert_nonzero(&residuals, PoolV1PairResidualClassV1::PathOrdering);

        let mut changed = honest.clone();
        changed.semantic_c1.c1[0][POOL_V1_PAIR_VALUE_AUX_ROW_START] = M31(2);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::ValueBooleanity,
        );

        let mut changed = honest.clone();
        let bit = &mut changed.semantic_c1.c1[0][POOL_V1_PAIR_VALUE_AUX_ROW_START];
        *bit = M31::ONE.sub(*bit);
        let residuals = transfer_residuals(&public, &changed);
        assert!(residuals.class_is_zero(PoolV1PairResidualClassV1::ValueBooleanity));
        assert_nonzero(&residuals, PoolV1PairResidualClassV1::ValueRecomposition);

        let mut changed = honest.clone();
        changed.semantic_c1.c1[0][POOL_V1_PAIR_VALUE_AUX_ROW_START + 7] =
            changed.semantic_c1.c1[0][POOL_V1_PAIR_VALUE_AUX_ROW_START + 7].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::Conservation,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN]
            [POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW] = changed.semantic_c1.c1
            [POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN][POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW]
            .add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::Occupancy,
        );

        let mut changed_public = public;
        changed_public.anchor_root[0] = changed_public.anchor_root[0].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&changed_public, &honest),
            PoolV1PairResidualClassV1::PublicBindings,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[0][34 * 16 + 12] =
            changed.semantic_c1.c1[0][34 * 16 + 12].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::AppendPathBindings,
        );

        let mut changed = honest.clone();
        changed.public_statement.candidate_afterstate.next_root[0] =
            changed.public_statement.candidate_afterstate.next_root[0].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::CandidateRoot,
        );

        let mut changed = honest.clone();
        changed.public_statement.candidate_afterstate.next_frontier[7][0] =
            changed.public_statement.candidate_afterstate.next_frontier[7][0].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::CandidateFrontier,
        );

        let mut changed = honest.clone();
        changed
            .public_statement
            .candidate_afterstate
            .next_pair_index += 1;
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::IndexSequence,
        );

        let mut changed = honest;
        changed.semantic_c1.c1[0][13] = M31::ONE;
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::ZeroPadding,
        );
    }
}
