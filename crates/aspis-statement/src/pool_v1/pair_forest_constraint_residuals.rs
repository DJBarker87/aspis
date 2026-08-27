//! Host residual evaluator for the production-inactive eight-lane forest.
//!
//! The unchanged legacy relation is evaluated through an exact coordinate
//! projection. Forest-specific Poseidon, schedule, copy, path, anchor, and
//! padding residuals are evaluated directly in the forest coordinates.

use alloc::vec::Vec;

use aspis_core::field::M31;

use crate::{
    poseidon2::{evaluate_trace_round_pair, Digest, DIGEST_ELEMS, POSEIDON2_WIDTH, RATE},
    state_only_trace::StateOnlyTraceFoundation,
};

use super::{
    pair_constraint_residuals::{
        evaluate_pool_v1_pair_private_transfer_constraint_residuals_v1,
        evaluate_pool_v1_pair_withdrawal_constraint_residuals_v1,
        PoolV1PairConstraintResidualErrorV1, PoolV1PairConstraintResidualsV1,
        POOL_V1_PAIR_AFFINE_INTRINSIC_DEGREE, POOL_V1_PAIR_APPEND_PATH_RESIDUAL_COUNT,
        POOL_V1_PAIR_BOOLEAN_INTRINSIC_DEGREE, POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT,
        POOL_V1_PAIR_CANDIDATE_ROOT_RESIDUAL_COUNT, POOL_V1_PAIR_INDEX_SEQUENCE_RESIDUAL_COUNT,
        POOL_V1_PAIR_MAX_INTRINSIC_DEGREE, POOL_V1_PAIR_OCCUPANCY_RESIDUAL_COUNT,
        POOL_V1_PAIR_POSEIDON_SBOX_DEGREE, POOL_V1_PAIR_SELECTED_ORACLE_INDIVIDUAL_DEGREE,
        POOL_V1_PAIR_TRANSFER_SCHEDULE_RESIDUAL_COUNT as LEGACY_TRANSFER_SCHEDULE_RESIDUAL_COUNT,
        POOL_V1_PAIR_TWO_ROUND_INTRINSIC_DEGREE, POOL_V1_PAIR_VALUE_BOOLEAN_RESIDUAL_COUNT,
        POOL_V1_PAIR_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT as LEGACY_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT,
        POOL_V1_PAIR_ZEROCHECK_INDIVIDUAL_DEGREE,
    },
    pair_forest_hiding::{
        pool_v1_pair_forest_path_base_row_v1, pool_v1_pair_forest_relation_free_mask_cells_v1,
        POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1, POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1,
        POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1, POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1,
        POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_CELLS_V1,
        POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1,
    },
    pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1,
    pair_trace::{
        PoolV1PairCopyTupleV1, PoolV1PairCopyWeightV1, PoolV1PairTraceBankV1,
        PoolV1PairTupleLimbV1, POOL_V1_PAIR_VALUE_BITS, POOL_V1_PAIR_VALUE_COUNT,
    },
    pair_tree_profile::{
        pool_v1_pair_path_base_row_v1, PoolV1PairLatePublicStatementV1, POOL_V1_PAIR_TRACE_COLUMNS,
        POOL_V1_PAIR_TRACE_ROWS,
    },
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
};

pub use super::pair_constraint_residuals::PoolV1PairResidualClassV1;

pub const POOL_V1_PAIR_FOREST_POSEIDON_RESIDUAL_COUNT: usize = 57 * 11 * POSEIDON2_WIDTH;
pub const POOL_V1_PAIR_FOREST_TRANSFER_SCHEDULE_RESIDUAL_COUNT: usize =
    LEGACY_TRANSFER_SCHEDULE_RESIDUAL_COUNT + 3 * POSEIDON2_WIDTH;
pub const POOL_V1_PAIR_FOREST_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT: usize =
    LEGACY_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT + 3 * POSEIDON2_WIDTH;
pub const POOL_V1_PAIR_FOREST_COPY_ALIAS_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1 * POSEIDON2_WIDTH;
pub const POOL_V1_PAIR_FOREST_PATH_ORDERING_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 * DIGEST_ELEMS * 2;
pub const POOL_V1_PAIR_FOREST_TRANSFER_PUBLIC_RESIDUAL_COUNT: usize = 4 * DIGEST_ELEMS + 3;
pub const POOL_V1_PAIR_FOREST_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT: usize = 3 * DIGEST_ELEMS + 3;
pub const POOL_V1_PAIR_FOREST_ZERO_PADDING_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_CELLS_V1;
const POOL_V1_PAIR_FOREST_COMMON_NON_PUBLIC_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_FOREST_POSEIDON_RESIDUAL_COUNT
        + POOL_V1_PAIR_FOREST_COPY_ALIAS_RESIDUAL_COUNT
        + POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1
        + POOL_V1_PAIR_FOREST_PATH_ORDERING_RESIDUAL_COUNT
        + POOL_V1_PAIR_VALUE_BOOLEAN_RESIDUAL_COUNT
        + POOL_V1_PAIR_VALUE_COUNT
        + 2
        + POOL_V1_PAIR_OCCUPANCY_RESIDUAL_COUNT
        + POOL_V1_PAIR_APPEND_PATH_RESIDUAL_COUNT
        + POOL_V1_PAIR_CANDIDATE_ROOT_RESIDUAL_COUNT
        + POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT
        + POOL_V1_PAIR_INDEX_SEQUENCE_RESIDUAL_COUNT
        + POOL_V1_PAIR_FOREST_ZERO_PADDING_RESIDUAL_COUNT;
pub const POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_FOREST_COMMON_NON_PUBLIC_RESIDUAL_COUNT
        + POOL_V1_PAIR_FOREST_TRANSFER_SCHEDULE_RESIDUAL_COUNT
        + POOL_V1_PAIR_FOREST_TRANSFER_PUBLIC_RESIDUAL_COUNT;
pub const POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT: usize =
    POOL_V1_PAIR_FOREST_COMMON_NON_PUBLIC_RESIDUAL_COUNT
        + POOL_V1_PAIR_FOREST_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT
        + POOL_V1_PAIR_FOREST_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT;

const _: () = assert!(POOL_V1_PAIR_FOREST_POSEIDON_RESIDUAL_COUNT == 10_032);
const _: () = assert!(POOL_V1_PAIR_FOREST_COPY_ALIAS_RESIDUAL_COUNT == 2_176);
const _: () = assert!(POOL_V1_PAIR_FOREST_PATH_ORDERING_RESIDUAL_COUNT == 384);
const _: () = assert!(POOL_V1_PAIR_FOREST_TRANSFER_SCHEDULE_RESIDUAL_COUNT == 1_026);
const _: () = assert!(POOL_V1_PAIR_FOREST_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT == 1_044);
const _: () = assert!(POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT == 17_896);
const _: () = assert!(POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT == 17_906);
const _: () = assert!(POOL_V1_PAIR_MAX_INTRINSIC_DEGREE == 25);
const _: () = assert!(POOL_V1_PAIR_SELECTED_ORACLE_INDIVIDUAL_DEGREE == 26);
const _: () = assert!(POOL_V1_PAIR_ZEROCHECK_INDIVIDUAL_DEGREE == 27);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestConstraintResidualsV1 {
    pub poseidon_round_pairs: Vec<M31>,
    pub schedule: Vec<M31>,
    pub copy_aliases: Vec<M31>,
    pub direction_booleanity: [M31; POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1],
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

impl PoolV1PairForestConstraintResidualsV1 {
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
        self.poseidon_round_pairs
            .iter()
            .chain(&self.schedule)
            .chain(&self.copy_aliases)
            .chain(&self.direction_booleanity)
            .chain(&self.path_ordering)
            .chain(self.value_booleanity.iter().flatten())
            .chain(&self.value_recomposition)
            .chain(&self.conservation)
            .chain(&self.occupancy)
            .chain(&self.public_bindings)
            .chain(&self.append_path_bindings)
            .chain(&self.candidate_root)
            .chain(&self.candidate_frontier)
            .chain(&self.index_sequence)
            .chain(&self.zero_padding)
            .all(|value| *value == M31::ZERO)
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

#[inline]
fn row_cell(trace: &StateOnlyTraceFoundation, row: usize, column: usize) -> M31 {
    trace.c1[column][row]
}

#[inline]
fn cell(trace: &StateOnlyTraceFoundation, block: usize, local: usize, column: usize) -> M31 {
    row_cell(trace, block * 16 + local, column)
}

fn trace_digest(trace: &StateOnlyTraceFoundation, block: usize) -> Digest {
    core::array::from_fn(|lane| cell(trace, block, 11, lane))
}

fn project_legacy(trace: &StateOnlyTraceFoundation) -> StateOnlyTraceFoundation {
    let mut projected = trace.clone();
    for column in &mut projected.c1 {
        column[864..].fill(M31::ZERO);
    }
    for level in 0..21 {
        let source = pool_v1_pair_forest_path_base_row_v1(level).expect("forest path");
        let target = pool_v1_pair_path_base_row_v1(level).expect("legacy path");
        for column in 0..=8 {
            projected.c1[column][target] = trace.c1[column][source];
        }
        for column in 0..16 {
            projected.c1[column][target + 1] = trace.c1[column][source + 1];
        }
        for column in 0..8 {
            projected.c1[column][target ^ 12] = trace.c1[column][source ^ 12];
        }
    }
    for column in 0..16 {
        projected.c1[column][960..976].copy_from_slice(&trace.c1[column][1008..1024]);
    }
    projected
}

fn append_new_poseidon_residuals(trace: &StateOnlyTraceFoundation, output: &mut Vec<M31>) {
    for block in 54..57 {
        for local_row in 0..11 {
            let mut input = core::array::from_fn(|lane| cell(trace, block, local_row, lane));
            if local_row == 0 {
                for lane in 0..RATE {
                    input[lane] = input[lane].add(cell(trace, block, 12, lane));
                }
            }
            let (_, expected) = evaluate_trace_round_pair(input, local_row)
                .expect("forest Poseidon local row lies in 0..11");
            for lane in 0..POSEIDON2_WIDTH {
                output.push(cell(trace, block, local_row + 1, lane).sub(expected[lane]));
            }
        }
    }
}

fn append_new_node_schedule(trace: &StateOnlyTraceFoundation, output: &mut Vec<M31>) {
    for block in 54..57 {
        for lane in 0..RATE {
            output.push(cell(trace, block, 0, lane));
        }
        for lane in RATE..POSEIDON2_WIDTH {
            output.push(cell(trace, block, 12, lane));
        }
    }
}

fn tuple_limb_value(trace: &StateOnlyTraceFoundation, limb: PoolV1PairTupleLimbV1) -> M31 {
    match limb {
        PoolV1PairTupleLimbV1::Zero => M31::ZERO,
        PoolV1PairTupleLimbV1::Cell { source, offset } => {
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Variant {
    Transfer,
    Withdrawal,
}

fn append_copy_residuals(
    trace: &StateOnlyTraceFoundation,
    append_index: u64,
    variant: Variant,
    output: &mut Vec<M31>,
) -> Result<(), PoolV1PairConstraintResidualErrorV1> {
    for link in build_pool_v1_pair_forest_copy_registry_v1()
        .map_err(|_| PoolV1PairConstraintResidualErrorV1::Layout)?
    {
        let weight = match link.weight {
            PoolV1PairCopyWeightV1::One => M31::ONE,
            PoolV1PairCopyWeightV1::PrivateTransferOnly => {
                M31(u32::from(variant == Variant::Transfer))
            }
            PoolV1PairCopyWeightV1::WithdrawalOnly => {
                M31(u32::from(variant == Variant::Withdrawal))
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

fn forest_path_residuals(
    trace: &StateOnlyTraceFoundation,
) -> ([M31; POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1], Vec<M31>) {
    let mut booleanity = [M31::ZERO; POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1];
    let mut ordering = Vec::with_capacity(POOL_V1_PAIR_FOREST_PATH_ORDERING_RESIDUAL_COUNT);
    for level in 0..POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        let base = pool_v1_pair_forest_path_base_row_v1(level).expect("forest path");
        let bit = row_cell(trace, base, 0);
        booleanity[level] = bit.mul(bit.sub(M31::ONE));
        for lane in 0..DIGEST_ELEMS {
            let current = row_cell(trace, base, 1 + lane);
            let left = row_cell(trace, base + 1, lane);
            let right = row_cell(trace, base + 1, RATE + lane);
            let sibling = row_cell(trace, base ^ 12, lane);
            ordering.push(left.sub(current.add(bit.mul(sibling.sub(current)))));
            ordering.push(right.sub(sibling.add(bit.mul(current.sub(sibling)))));
        }
    }
    (booleanity, ordering)
}

fn forest_zero_padding(
    trace: &StateOnlyTraceFoundation,
) -> Result<Vec<M31>, PoolV1PairConstraintResidualErrorV1> {
    Ok(pool_v1_pair_forest_relation_free_mask_cells_v1()
        .map_err(|_| PoolV1PairConstraintResidualErrorV1::Layout)?
        .into_iter()
        .map(|target| row_cell(trace, usize::from(target.row), usize::from(target.column)))
        .collect())
}

fn assemble(
    mut legacy: PoolV1PairConstraintResidualsV1,
    trace: &StateOnlyTraceFoundation,
    statement: &PoolV1PairLatePublicStatementV1,
    anchor: &Digest,
    variant: Variant,
) -> Result<PoolV1PairForestConstraintResidualsV1, PoolV1PairConstraintResidualErrorV1> {
    append_new_poseidon_residuals(trace, &mut legacy.poseidon_round_pairs);
    append_new_node_schedule(trace, &mut legacy.schedule);
    let mut copy_aliases = Vec::with_capacity(POOL_V1_PAIR_FOREST_COPY_ALIAS_RESIDUAL_COUNT);
    append_copy_residuals(
        trace,
        statement.live_snapshot.next_pair_index,
        variant,
        &mut copy_aliases,
    )?;
    let (direction_booleanity, path_ordering) = forest_path_residuals(trace);
    for lane in 0..DIGEST_ELEMS {
        legacy.public_bindings[lane] = trace_digest(trace, 56)[lane].sub(anchor[lane]);
    }
    let zero_padding = forest_zero_padding(trace)?;
    let residuals = PoolV1PairForestConstraintResidualsV1 {
        poseidon_round_pairs: legacy.poseidon_round_pairs,
        schedule: legacy.schedule,
        copy_aliases,
        direction_booleanity,
        path_ordering,
        value_booleanity: legacy.value_booleanity,
        value_recomposition: legacy.value_recomposition,
        conservation: legacy.conservation,
        occupancy: legacy.occupancy,
        public_bindings: legacy.public_bindings,
        append_path_bindings: legacy.append_path_bindings,
        candidate_root: legacy.candidate_root,
        candidate_frontier: legacy.candidate_frontier,
        index_sequence: legacy.index_sequence,
        zero_padding,
    };
    debug_assert_eq!(
        residuals.poseidon_round_pairs.len(),
        POOL_V1_PAIR_FOREST_POSEIDON_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        residuals.copy_aliases.len(),
        POOL_V1_PAIR_FOREST_COPY_ALIAS_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        residuals.path_ordering.len(),
        POOL_V1_PAIR_FOREST_PATH_ORDERING_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        residuals.zero_padding.len(),
        POOL_V1_PAIR_FOREST_ZERO_PADDING_RESIDUAL_COUNT
    );
    Ok(residuals)
}

pub fn evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1(
    public: &PoolV1PrivateTransferPublicV1,
    statement: &PoolV1PairLatePublicStatementV1,
    trace: &StateOnlyTraceFoundation,
) -> Result<PoolV1PairForestConstraintResidualsV1, PoolV1PairConstraintResidualErrorV1> {
    if trace.c1.len() != POOL_V1_PAIR_TRACE_COLUMNS
        || trace
            .c1
            .iter()
            .any(|column| column.len() != POOL_V1_PAIR_TRACE_ROWS)
    {
        return Err(PoolV1PairConstraintResidualErrorV1::Shape);
    }
    let projected = project_legacy(trace);
    let legacy_public = PoolV1PrivateTransferPublicV1 {
        anchor_root: trace_digest(&projected, 24),
        ..*public
    };
    let legacy = evaluate_pool_v1_pair_private_transfer_constraint_residuals_v1(
        &legacy_public,
        statement,
        &projected,
    )?;
    let residuals = assemble(
        legacy,
        trace,
        statement,
        &public.anchor_root,
        Variant::Transfer,
    )?;
    debug_assert_eq!(
        residuals.schedule.len(),
        POOL_V1_PAIR_FOREST_TRANSFER_SCHEDULE_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        residuals.public_bindings.len(),
        POOL_V1_PAIR_FOREST_TRANSFER_PUBLIC_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        residuals.residual_count(),
        POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT
    );
    Ok(residuals)
}

pub fn evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1(
    public: &PoolV1WithdrawalPublicV1,
    statement: &PoolV1PairLatePublicStatementV1,
    trace: &StateOnlyTraceFoundation,
) -> Result<PoolV1PairForestConstraintResidualsV1, PoolV1PairConstraintResidualErrorV1> {
    if trace.c1.len() != POOL_V1_PAIR_TRACE_COLUMNS
        || trace
            .c1
            .iter()
            .any(|column| column.len() != POOL_V1_PAIR_TRACE_ROWS)
    {
        return Err(PoolV1PairConstraintResidualErrorV1::Shape);
    }
    let projected = project_legacy(trace);
    let legacy_public = PoolV1WithdrawalPublicV1 {
        anchor_root: trace_digest(&projected, 24),
        ..*public
    };
    let legacy = evaluate_pool_v1_pair_withdrawal_constraint_residuals_v1(
        &legacy_public,
        statement,
        &projected,
    )?;
    let residuals = assemble(
        legacy,
        trace,
        statement,
        &public.anchor_root,
        Variant::Withdrawal,
    )?;
    debug_assert_eq!(
        residuals.schedule.len(),
        POOL_V1_PAIR_FOREST_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        residuals.public_bindings.len(),
        POOL_V1_PAIR_FOREST_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT
    );
    debug_assert_eq!(
        residuals.residual_count(),
        POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT
    );
    Ok(residuals)
}

const _: () = assert!(POOL_V1_PAIR_AFFINE_INTRINSIC_DEGREE == 1);
const _: () = assert!(POOL_V1_PAIR_BOOLEAN_INTRINSIC_DEGREE == 2);
const _: () = assert!(POOL_V1_PAIR_POSEIDON_SBOX_DEGREE == 5);
const _: () = assert!(POOL_V1_PAIR_TWO_ROUND_INTRINSIC_DEGREE == 25);
const _: () = assert!(POOL_V1_PAIR_OCCUPANCY_RESIDUAL_COUNT == 23);
const _: () = assert!(POOL_V1_PAIR_APPEND_PATH_RESIDUAL_COUNT == 320);
const _: () = assert!(POOL_V1_PAIR_CANDIDATE_ROOT_RESIDUAL_COUNT == 8);
const _: () = assert!(POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT == 160);
const _: () = assert!(POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1 == 1017);
const _: () = assert!(POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1 == 1018);
const _: () = assert!(POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1 == 1008);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        derive_owner_key,
        pool_v1::{
            pair_forest_trace::{
                compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
                compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
                verify_pool_v1_pair_forest_copy_registry_v1, PoolV1PairForestInputNoteWitnessV1,
                PoolV1PairForestMergedC1CompilationV1, PoolV1PairForestPrivateTransferWitnessV1,
                PoolV1PairForestWithdrawalWitnessV1,
            },
            pair_trace::PoolV1PairInputNoteWitnessV1,
            pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent,
            IncrementalMerkleTreeV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
            PoolV1PairLeafWitnessV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
            POOL_V1_PAIR_TREE_DEPTH,
        },
    };
    use aspis_core::field::{CM31, QM31};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
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

    fn input_witness(value: u32) -> PoolV1PairForestInputNoteWitnessV1 {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset = M31(77);
        let owner = derive_owner_key(&nullifier_key);
        let input_commitment = pool_v1_note_commitment(&owner, value, asset, &salt);
        let pair_leaf =
            PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900)).unwrap();
        PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt,
                value,
                pair_leaf,
                selected_second: false,
                membership: PoolV1MembershipWitnessV1 {
                    siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                    index: 0x5_4321,
                },
            },
            super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
            // Deliberately unrelated to the public nullifier/output lane.
            super_root_directions: [true, false, true],
        }
    }

    fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
        let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            let sibling = input.pair.membership.siblings[level];
            current = if ((input.pair.membership.index >> level) & 1) == 0 {
                pool_v1_tree_parent(&current, &sibling)
            } else {
                pool_v1_tree_parent(&sibling, &current)
            };
        }
        for level in 0..3 {
            let sibling = input.super_root_siblings[level];
            current = if input.super_root_directions[level] {
                pool_v1_tree_parent(&sibling, &current)
            } else {
                pool_v1_tree_parent(&current, &sibling)
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
        PoolV1PairForestMergedC1CompilationV1,
    ) {
        let input = input_witness(1_000);
        let recipient = output(300, 600);
        let change = output(500, 400);
        let witness = PoolV1PairForestPrivateTransferWitnessV1 {
            input,
            recipient,
            change,
        };
        let asset_id = M31(77);
        let anchor = global_anchor(&witness.input);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(
                &witness.input.pair.nullifier_key,
                &witness.input.pair.salt,
            ),
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
        let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
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
    ) -> (
        PoolV1WithdrawalPublicV1,
        PoolV1PairForestMergedC1CompilationV1,
    ) {
        let input = input_witness(1_000);
        let change = output(700, 750);
        let witness = PoolV1PairForestWithdrawalWitnessV1 { input, change };
        let asset_id = M31(77);
        let anchor = global_anchor(&witness.input);
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(
                &witness.input.pair.nullifier_key,
                &witness.input.pair.salt,
            ),
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
        let compiled = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
            &public,
            &witness,
            context(public.pool, public.deployment_domain, anchor, asset_id),
            snapshot,
        )
        .unwrap();
        (public, compiled)
    }

    fn transfer_residuals(
        public: &PoolV1PrivateTransferPublicV1,
        compiled: &PoolV1PairForestMergedC1CompilationV1,
    ) -> PoolV1PairForestConstraintResidualsV1 {
        evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1(
            public,
            &compiled.public_statement,
            &compiled.semantic_c1,
        )
        .unwrap()
    }

    fn assert_nonzero(
        residuals: &PoolV1PairForestConstraintResidualsV1,
        class: PoolV1PairResidualClassV1,
    ) {
        assert!(
            !residuals.class_is_zero(class),
            "class unexpectedly zero: {class:?}"
        );
        assert!(!residuals.all_zero());
    }

    #[test]
    fn honest_forest_transfer_and_withdrawal_have_exact_layout_and_residual_counts() {
        let (transfer_public, transfer) = transfer_at(13);
        let transfer_residuals = transfer_residuals(&transfer_public, &transfer);
        assert!(transfer_residuals.all_zero(), "{transfer_residuals:?}");
        assert_eq!(
            transfer_residuals.residual_count(),
            POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT
        );
        assert_eq!(transfer_residuals.poseidon_round_pairs.len(), 57 * 11 * 16);
        assert_eq!(transfer_residuals.schedule.len(), 1_026);
        assert_eq!(transfer_residuals.copy_aliases.len(), 136 * 16);
        assert_eq!(transfer_residuals.direction_booleanity.len(), 24);
        assert_eq!(transfer_residuals.path_ordering.len(), 24 * 8 * 2);
        assert_eq!(transfer_residuals.zero_padding.len(), 3_611);
        assert_eq!(
            trace_digest(&transfer.semantic_c1, 56),
            transfer_public.anchor_root
        );
        assert_eq!(
            trace_digest(&transfer.semantic_c1, 53),
            transfer.trace.afterstate.next_root
        );
        verify_pool_v1_pair_forest_copy_registry_v1(
            &transfer.trace,
            13,
            QM31::from_cm31(CM31::from_m31(M31(19))),
            QM31::from_cm31(CM31::from_m31(M31(23))),
        )
        .unwrap();

        let (withdrawal_public, withdrawal) = withdrawal_at(13);
        let withdrawal_residuals = evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1(
            &withdrawal_public,
            &withdrawal.public_statement,
            &withdrawal.semantic_c1,
        )
        .unwrap();
        assert!(withdrawal_residuals.all_zero(), "{withdrawal_residuals:?}");
        assert_eq!(
            withdrawal_residuals.residual_count(),
            POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT
        );
        assert_eq!(withdrawal_residuals.schedule.len(), 1_044);
        verify_pool_v1_pair_forest_copy_registry_v1(
            &withdrawal.trace,
            13,
            QM31::from_cm31(CM31::from_m31(M31(29))),
            QM31::from_cm31(CM31::from_m31(M31(31))),
        )
        .unwrap();
    }

    #[test]
    fn forest_specific_mutations_are_detected_by_each_new_or_shifted_class() {
        let (public, honest) = transfer_at(13);

        let mut changed = honest.clone();
        changed.semantic_c1.c1[7][54 * 16 + 6] =
            changed.semantic_c1.c1[7][54 * 16 + 6].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::PoseidonRoundPairs,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[0][54 * 16] = M31::ONE;
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::Schedule,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[2][POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1] =
            changed.semantic_c1.c1[2][POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1].add(M31::ONE);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::CopyAliases,
        );

        let direction_row = pool_v1_pair_forest_path_base_row_v1(23).unwrap();
        let mut changed = honest.clone();
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
        changed.semantic_c1.c1[0][POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1] = M31(2);
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::ValueBooleanity,
        );

        let mut changed = honest.clone();
        changed.semantic_c1.c1[1][POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1] =
            changed.semantic_c1.c1[1][POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1]
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

        let mut changed = honest;
        changed.semantic_c1.c1[0][877] = M31::ONE;
        assert_nonzero(
            &transfer_residuals(&public, &changed),
            PoolV1PairResidualClassV1::ZeroPadding,
        );
    }
}
