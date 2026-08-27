//! Production-inactive eight-lane forest trace compiler.
//!
//! This preserves the legacy pair compiler and relocates only its auxiliary
//! tail. Three private witness directions and siblings extend the historical
//! input path to the global forest root. The live append remains the existing
//! depth-20 selected output-lane transition in blocks `34..=53`.

use alloc::{vec, vec::Vec};

use aspis_core::field::{M31, QM31};

use crate::{
    logup::{
        build_copy_logup_helper, compress_tagged_tuple, verify_copy_logup_constraints, CopyLogUpRow,
    },
    poseidon2::{
        permute_optimized_with_trace, Digest, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_ROUNDS,
    },
    state_only_trace::StateOnlyTraceFoundation,
    trace_v4::TraceCell,
};

use super::{
    pair_forest_hiding::{
        build_pool_v1_pair_forest_copy_row_schedule_v1, pool_v1_pair_forest_path_base_row_v1,
        POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1, POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1,
        POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1, POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1,
        POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1, POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1,
    },
    pair_trace::{
        build_pool_v1_pair_copy_registry_v1, build_pool_v1_pair_private_transfer_trace_v1,
        build_pool_v1_pair_withdrawal_trace_v1, PoolV1PairCopyLinkV1, PoolV1PairCopyTupleV1,
        PoolV1PairCopyWeightV1, PoolV1PairInputNoteWitnessV1, PoolV1PairPrivateTransferWitnessV1,
        PoolV1PairTraceBankV1, PoolV1PairTraceCellV1, PoolV1PairTraceErrorV1,
        PoolV1PairTracePublicOutputsV1, PoolV1PairTraceVariantV1, PoolV1PairTupleLimbV1,
        PoolV1PairWithdrawalWitnessV1, POOL_V1_PAIR_COPY_TAG_BASE_V1, POOL_V1_PAIR_VALUE_BITS,
        POOL_V1_PAIR_VALUE_COUNT,
    },
    pair_tree_hiding::PoolV1PairCopyRowLinkKindV1,
    pair_tree_profile::{
        PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotV1, POOL_V1_PAIR_TRACE_COLUMNS,
        POOL_V1_PAIR_TRACE_ROWS,
    },
    payment_relation::{
        PoolV1OutputNoteWitnessV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
    },
    pool_v1_tree_parent,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestInputNoteWitnessV1 {
    pub pair: PoolV1PairInputNoteWitnessV1,
    pub super_root_siblings: [Digest; POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1],
    /// Private input-lane path bits. They are intentionally independent of the
    /// operationally selected output lane.
    pub super_root_directions: [bool; POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestPrivateTransferWitnessV1 {
    pub input: PoolV1PairForestInputNoteWitnessV1,
    pub recipient: PoolV1OutputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestWithdrawalWitnessV1 {
    pub input: PoolV1PairForestInputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTraceV1 {
    pub stable: StateOnlyTraceFoundation,
    pub late: [Vec<M31>; POOL_V1_PAIR_TRACE_COLUMNS],
    pub variant: PoolV1PairTraceVariantV1,
    pub private_directions: [M31; POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1],
    pub value_bits: [[M31; POOL_V1_PAIR_VALUE_BITS]; POOL_V1_PAIR_VALUE_COUNT],
    pub public_outputs: PoolV1PairTracePublicOutputsV1,
    pub afterstate: super::pair_terminal::PoolV1PairVerifiedAfterstateV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestMergedC1CompilationV1 {
    pub trace: PoolV1PairForestTraceV1,
    pub semantic_c1: StateOnlyTraceFoundation,
    pub public_statement: PoolV1PairLatePublicStatementV1,
}

fn lane_root(input: &PoolV1PairInputNoteWitnessV1) -> Result<Digest, PoolV1PairTraceErrorV1> {
    let mut current = input
        .pair_leaf
        .leaf_digest()
        .map_err(PoolV1PairTraceErrorV1::PairLeaf)?;
    for level in 0..20 {
        let sibling = input.membership.siblings[level];
        current = if ((input.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &current)
        };
    }
    Ok(current)
}

fn temporary_context<'a>(
    context: PoolV1PaymentRelationContextV1<'a>,
    anchor_root: Digest,
) -> PoolV1PaymentRelationContextV1<'a> {
    PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            anchor_root,
            ..context.runtime_binding
        },
        spent_nullifiers: context.spent_nullifiers,
    }
}

#[inline]
fn trace_digest(columns: &[Vec<M31>; 16], block: usize) -> Digest {
    core::array::from_fn(|lane| columns[lane][block * 16 + 11])
}

#[inline]
fn node_left(columns: &[Vec<M31>; 16], block: usize) -> Digest {
    core::array::from_fn(|lane| columns[lane][block * 16 + 12])
}

#[inline]
fn node_right(columns: &[Vec<M31>; 16], block: usize) -> Digest {
    core::array::from_fn(|lane| {
        let value = columns[8 + lane][block * 16];
        if lane == 7 {
            value.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            value
        }
    })
}

fn write_forest_path_aux(
    columns: &mut [Vec<M31>; 16],
    level: usize,
    bit: M31,
    current: Digest,
    sibling: Digest,
    left: Digest,
    right: Digest,
) -> Result<(), PoolV1PairTraceErrorV1> {
    let base =
        pool_v1_pair_forest_path_base_row_v1(level).ok_or(PoolV1PairTraceErrorV1::HashSchedule)?;
    columns[0][base] = bit;
    for lane in 0..8 {
        columns[1 + lane][base] = current[lane];
        columns[lane][base + 1] = left[lane];
        columns[8 + lane][base + 1] = right[lane];
        columns[lane][base ^ 12] = sibling[lane];
    }
    Ok(())
}

fn write_forest_node(
    columns: &mut [Vec<M31>; 16],
    block: usize,
    left: Digest,
    right: Digest,
) -> Result<Digest, PoolV1PairTraceErrorV1> {
    if !(54..=56).contains(&block) {
        return Err(PoolV1PairTraceErrorV1::HashSchedule);
    }
    let base = block * 16;
    let mut state = [M31::ZERO; 16];
    state[8..].copy_from_slice(&right);
    state[15] = state[15].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    for lane in 0..8 {
        columns[lane][base + 12] = left[lane];
        state[lane] = state[lane].add(left[lane]);
    }
    for lane in 0..16 {
        columns[lane][base] = if lane < 8 { M31::ZERO } else { state[lane] };
    }
    let mut rounds = 0;
    permute_optimized_with_trace(&mut state, |transition| {
        rounds += 1;
        if transition.round & 1 == 1 {
            let row = base + usize::from(transition.round) / 2 + 1;
            for lane in 0..16 {
                columns[lane][row] = transition.output[lane];
            }
        }
    });
    if rounds != POSEIDON2_ROUNDS {
        return Err(PoolV1PairTraceErrorV1::HashSchedule);
    }
    Ok(core::array::from_fn(|lane| state[lane]))
}

fn relocate_and_extend(
    mut legacy: super::pair_trace::PoolV1PairTraceV1,
    input: &PoolV1PairForestInputNoteWitnessV1,
    expected_global_anchor: Digest,
) -> Result<PoolV1PairForestTraceV1, PoolV1PairTraceErrorV1> {
    if input
        .super_root_siblings
        .iter()
        .flatten()
        .any(|limb| limb.0 >= aspis_core::field::P)
    {
        return Err(PoolV1PairTraceErrorV1::WitnessDigest);
    }
    let old = legacy.stable.c1.clone();
    for column in &mut legacy.stable.c1 {
        column[864..].fill(M31::ZERO);
    }
    let mut directions = [M31::ZERO; POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1];
    directions[..21].copy_from_slice(&legacy.private_directions);
    for level in 0..21 {
        let target = 4 + level;
        let previous = if level == 0 { 3 } else { target - 1 };
        let current = trace_digest(&old, previous);
        let left = node_left(&old, target);
        let right = node_right(&old, target);
        let bit = directions[level];
        let sibling = if bit == M31::ZERO { right } else { left };
        write_forest_path_aux(
            &mut legacy.stable.c1,
            level,
            bit,
            current,
            sibling,
            left,
            right,
        )?;
    }
    for column in 0..16 {
        legacy.stable.c1[column][1008..1024].copy_from_slice(&old[column][960..976]);
    }
    let mut current = trace_digest(&legacy.stable.c1, 24);
    for level in 0..POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1 {
        let bit = M31(u32::from(input.super_root_directions[level]));
        directions[21 + level] = bit;
        let sibling = input.super_root_siblings[level];
        let (left, right) = if bit == M31::ZERO {
            (current, sibling)
        } else {
            (sibling, current)
        };
        write_forest_path_aux(
            &mut legacy.stable.c1,
            21 + level,
            bit,
            current,
            sibling,
            left,
            right,
        )?;
        current = write_forest_node(&mut legacy.stable.c1, 54 + level, left, right)?;
    }
    if current != expected_global_anchor {
        return Err(PoolV1PairTraceErrorV1::AnchorMismatch);
    }
    let public_outputs = match legacy.public_outputs {
        PoolV1PairTracePublicOutputsV1::PrivateTransfer {
            nullifier,
            recipient_commitment,
            change_commitment,
            output_pair,
            ..
        } => PoolV1PairTracePublicOutputsV1::PrivateTransfer {
            anchor: current,
            nullifier,
            recipient_commitment,
            change_commitment,
            output_pair,
        },
        PoolV1PairTracePublicOutputsV1::Withdrawal {
            nullifier,
            change_commitment,
            output_pair,
            ..
        } => PoolV1PairTracePublicOutputsV1::Withdrawal {
            anchor: current,
            nullifier,
            change_commitment,
            output_pair,
        },
    };
    Ok(PoolV1PairForestTraceV1 {
        stable: legacy.stable,
        late: legacy.late,
        variant: legacy.variant,
        private_directions: directions,
        value_bits: legacy.value_bits,
        public_outputs,
        afterstate: legacy.afterstate,
    })
}

pub fn merge_pool_v1_pair_forest_trace_banks_v1(
    trace: &PoolV1PairForestTraceV1,
) -> Result<StateOnlyTraceFoundation, PoolV1PairTraceErrorV1> {
    if trace.stable.c1.len() != POOL_V1_PAIR_TRACE_COLUMNS
        || trace
            .stable
            .c1
            .iter()
            .any(|column| column.len() != POOL_V1_PAIR_TRACE_ROWS)
        || trace
            .late
            .iter()
            .any(|column| column.len() != POOL_V1_PAIR_TRACE_ROWS)
    {
        return Err(PoolV1PairTraceErrorV1::Shape);
    }
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        if trace.stable.c1[column][544..864]
            .iter()
            .any(|value| *value != M31::ZERO)
            || trace.late[column][..544]
                .iter()
                .chain(&trace.late[column][864..])
                .any(|value| *value != M31::ZERO)
        {
            return Err(PoolV1PairTraceErrorV1::Shape);
        }
    }
    let mut merged = trace.stable.clone();
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        merged.c1[column][544..864].copy_from_slice(&trace.late[column][544..864]);
    }
    Ok(merged)
}

pub fn compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairForestPrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairForestMergedC1CompilationV1, PoolV1PairTraceErrorV1> {
    let lane_anchor = lane_root(&witness.input.pair)?;
    let temporary_public = PoolV1PrivateTransferPublicV1 {
        anchor_root: lane_anchor,
        ..*public
    };
    let legacy = build_pool_v1_pair_private_transfer_trace_v1(
        &temporary_public,
        &PoolV1PairPrivateTransferWitnessV1 {
            input: witness.input.pair,
            recipient: witness.recipient,
            change: witness.change,
        },
        temporary_context(context, lane_anchor),
        snapshot,
    )?;
    let trace = relocate_and_extend(legacy, &witness.input, public.anchor_root)?;
    let semantic_c1 = merge_pool_v1_pair_forest_trace_banks_v1(&trace)?;
    Ok(PoolV1PairForestMergedC1CompilationV1 {
        public_statement: PoolV1PairLatePublicStatementV1 {
            live_snapshot: snapshot,
            candidate_afterstate: trace.afterstate,
        },
        trace,
        semantic_c1,
    })
}

pub fn compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairForestWithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairForestMergedC1CompilationV1, PoolV1PairTraceErrorV1> {
    let lane_anchor = lane_root(&witness.input.pair)?;
    let temporary_public = PoolV1WithdrawalPublicV1 {
        anchor_root: lane_anchor,
        ..*public
    };
    let legacy = build_pool_v1_pair_withdrawal_trace_v1(
        &temporary_public,
        &PoolV1PairWithdrawalWitnessV1 {
            input: witness.input.pair,
            change: witness.change,
        },
        temporary_context(context, lane_anchor),
        snapshot,
    )?;
    let trace = relocate_and_extend(legacy, &witness.input, public.anchor_root)?;
    let semantic_c1 = merge_pool_v1_pair_forest_trace_banks_v1(&trace)?;
    Ok(PoolV1PairForestMergedC1CompilationV1 {
        public_statement: PoolV1PairLatePublicStatementV1 {
            live_snapshot: snapshot,
            candidate_afterstate: trace.afterstate,
        },
        trace,
        semantic_c1,
    })
}

fn tuple_cells(row: usize, start: usize, count: usize, tweak_right: bool) -> PoolV1PairCopyTupleV1 {
    let bank = if (544..864).contains(&row) {
        PoolV1PairTraceBankV1::Late
    } else {
        PoolV1PairTraceBankV1::Stable
    };
    let mut limbs = [PoolV1PairTupleLimbV1::Zero; 16];
    for lane in 0..count {
        let column = start + lane;
        let offset = if tweak_right && lane + 1 == count {
            M31::ZERO.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            M31::ZERO
        };
        limbs[lane] = PoolV1PairTupleLimbV1::Cell {
            source: PoolV1PairTraceCellV1 {
                bank,
                cell: TraceCell {
                    row: row as u16,
                    column: column as u8,
                },
            },
            offset,
        };
    }
    PoolV1PairCopyTupleV1 {
        row: row as u16,
        limbs,
    }
}

fn translate_aux_tuple(mut tuple: PoolV1PairCopyTupleV1) -> PoolV1PairCopyTupleV1 {
    if usize::from(tuple.row) >= 864 {
        tuple.row += 48;
    }
    for limb in &mut tuple.limbs {
        if let PoolV1PairTupleLimbV1::Cell { source, .. } = limb {
            if usize::from(source.cell.row) >= 864 {
                source.cell.row += 48;
            }
        }
    }
    tuple
}

fn path_kind(kind: PoolV1PairCopyRowLinkKindV1) -> bool {
    matches!(
        kind,
        PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. }
    )
}

pub fn build_pool_v1_pair_forest_copy_registry_v1(
) -> Result<Vec<PoolV1PairCopyLinkV1>, PoolV1PairTraceErrorV1> {
    let legacy = build_pool_v1_pair_copy_registry_v1()?;
    let schedule = build_pool_v1_pair_forest_copy_row_schedule_v1()
        .map_err(|_| PoolV1PairTraceErrorV1::CopyLayout)?;
    let mut output = Vec::with_capacity(schedule.len());
    for scheduled in schedule {
        let (producer, consumer, weight) = if path_kind(scheduled.kind) {
            match scheduled.kind {
                PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 0, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 1, 8, false),
                    PoolV1PairCopyWeightV1::One,
                ),
                PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 0, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 0, 8, false),
                    PoolV1PairCopyWeightV1::One,
                ),
                PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 8, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 8, 8, true),
                    PoolV1PairCopyWeightV1::One,
                ),
                _ => return Err(PoolV1PairTraceErrorV1::CopyLayout),
            }
        } else {
            let old = legacy
                .iter()
                .find(|link| link.kind == scheduled.kind)
                .ok_or(PoolV1PairTraceErrorV1::CopyLayout)?;
            (
                translate_aux_tuple(old.producer),
                translate_aux_tuple(old.consumer),
                old.weight,
            )
        };
        if producer.row != scheduled.producer_row || consumer.row != scheduled.consumer_row {
            return Err(PoolV1PairTraceErrorV1::CopyLayout);
        }
        let id = output.len() as u16;
        output.push(PoolV1PairCopyLinkV1 {
            id,
            tag: M31(POOL_V1_PAIR_COPY_TAG_BASE_V1 + u32::from(id)),
            kind: scheduled.kind,
            weight,
            producer,
            consumer,
        });
    }
    if output.len() != POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairTraceErrorV1::CopyLayout);
    }
    Ok(output)
}

fn tuple_value(trace: &PoolV1PairForestTraceV1, tuple: PoolV1PairCopyTupleV1) -> [M31; 16] {
    tuple.limbs.map(|limb| match limb {
        PoolV1PairTupleLimbV1::Zero => M31::ZERO,
        PoolV1PairTupleLimbV1::Cell { source, offset } => {
            let columns = match source.bank {
                PoolV1PairTraceBankV1::Stable => &trace.stable.c1,
                PoolV1PairTraceBankV1::Late => &trace.late,
            };
            columns[source.cell.column as usize][source.cell.row as usize].add(offset)
        }
    })
}

fn copy_weight(
    weight: PoolV1PairCopyWeightV1,
    append_index: u64,
    variant: PoolV1PairTraceVariantV1,
) -> M31 {
    match weight {
        PoolV1PairCopyWeightV1::One => M31::ONE,
        PoolV1PairCopyWeightV1::PrivateTransferOnly => M31(u32::from(
            variant == PoolV1PairTraceVariantV1::PrivateTransfer,
        )),
        PoolV1PairCopyWeightV1::WithdrawalOnly => {
            M31(u32::from(variant == PoolV1PairTraceVariantV1::Withdrawal))
        }
        PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => {
            M31(1 - ((append_index >> level) & 1) as u32)
        }
        PoolV1PairCopyWeightV1::AppendCurrentRight { level } => {
            M31(((append_index >> level) & 1) as u32)
        }
    }
}

pub fn pool_v1_pair_forest_copy_rows_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
) -> Result<Vec<CopyLogUpRow>, PoolV1PairTraceErrorV1> {
    let empty = CopyLogUpRow {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [M31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [M31::ZERO; 2],
    };
    let mut rows = vec![empty; 1024];
    for link in build_pool_v1_pair_forest_copy_registry_v1()? {
        let weight = copy_weight(link.weight, append_index, trace.variant);
        for (tuple, producer) in [(link.producer, true), (link.consumer, false)] {
            let row = &mut rows[tuple.row as usize];
            let (values, weights) = if producer {
                (&mut row.producer_values, &mut row.producer_weights)
            } else {
                (&mut row.consumer_values, &mut row.consumer_weights)
            };
            let slot = weights
                .iter()
                .position(|value| *value == M31::ZERO)
                .ok_or(PoolV1PairTraceErrorV1::CopyLayout)?;
            values[slot] = compress_tagged_tuple(link.tag, &tuple_value(trace, tuple), lambda);
            weights[slot] = weight;
        }
    }
    Ok(rows)
}

pub fn verify_pool_v1_pair_forest_copy_registry_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
    chi: QM31,
) -> Result<(), PoolV1PairTraceErrorV1> {
    let rows = pool_v1_pair_forest_copy_rows_v1(trace, append_index, lambda)?;
    let helper =
        build_copy_logup_helper(&rows, chi).map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)?;
    verify_copy_logup_constraints(&rows, &helper, chi)
        .map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)
}

const _: () = assert!(POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1 == 1008);
const _: () = assert!(POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1 == 1017);
const _: () = assert!(POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1 == 1018);
