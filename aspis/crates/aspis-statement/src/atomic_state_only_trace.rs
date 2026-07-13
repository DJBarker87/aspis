//! Production-neutral state-only trace foundation for atomic statement v3.
//!
//! This module deliberately does not alter the frozen v4/state-only copy,
//! semantic, terminal, or hiding registries. It materializes the selected
//! 49-block schedule and exposes the exact same-path sources which a later
//! registry generator must bind.

use alloc::vec::Vec;

use aspis_core::field::M31;

use crate::atomic_state_only_registry::atomic_state_only_path_aux_layout_v3;
use crate::atomic_statement::{AtomicPaymentStatementV3, ATOMIC_PAYMENT_TREE_DEPTH};
use crate::poseidon2::{
    merkle_node_compress_v3, permute_optimized_with_trace, Digest, DIGEST_ELEMS,
    MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_ROUNDS, POSEIDON2_WIDTH, RATE,
};
use crate::spend::{
    derive_owner_key, merkle_root, note_commitment, output_commitment, MerklePath, SpendPublic,
    SpendWitness,
};
use crate::state_only_trace::{
    project_state_only_trace_v4, StateOnlyTraceFoundation, STATE_ONLY_ABSORPTION_ROW_IN_BLOCK,
    STATE_ONLY_C1_COLUMNS, STATE_ONLY_FINAL_ROW_IN_BLOCK,
};
use crate::trace_v4::{build_spend_trace_v4, TraceCell, BLOCK_ROWS, PERMUTATION_COUNT, TRACE_ROWS};

pub const ATOMIC_STATE_ONLY_INPUT_PATH_BLOCK_START: usize = 4;
pub const ATOMIC_STATE_ONLY_OUTPUT_PATH_BLOCK_START: usize = 24;
pub const ATOMIC_STATE_ONLY_INPUT_ROOT_BLOCK: usize = 23;
pub const ATOMIC_STATE_ONLY_OUTPUT_ROOT_BLOCK: usize = 43;
pub const ATOMIC_STATE_ONLY_NULLIFIER_BLOCKS: core::ops::RangeInclusive<usize> = 44..=45;
pub const ATOMIC_STATE_ONLY_OUTPUT_NOTE_BLOCKS: core::ops::RangeInclusive<usize> = 46..=48;

const _: () = assert!(ATOMIC_PAYMENT_TREE_DEPTH == 20);
const _: () = assert!(PERMUTATION_COUNT == 49);
const _: () = assert!(STATE_ONLY_C1_COLUMNS == POSEIDON2_WIDTH);
const _: () = assert!(STATE_ONLY_FINAL_ROW_IN_BLOCK == 11);
const _: () = assert!(STATE_ONLY_ABSORPTION_ROW_IN_BLOCK == 12);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicStateOnlyBlockV3 {
    OwnerKey,
    InputNote(u8),
    InputPath(u8),
    OutputPath(u8),
    Nullifier(u8),
    OutputNote(u8),
}

pub const fn atomic_state_only_block_schedule_v3(block: usize) -> Option<AtomicStateOnlyBlockV3> {
    match block {
        0 => Some(AtomicStateOnlyBlockV3::OwnerKey),
        1..=3 => Some(AtomicStateOnlyBlockV3::InputNote((block - 1) as u8)),
        4..=23 => Some(AtomicStateOnlyBlockV3::InputPath((block - 4) as u8)),
        24..=43 => Some(AtomicStateOnlyBlockV3::OutputPath((block - 24) as u8)),
        44..=45 => Some(AtomicStateOnlyBlockV3::Nullifier((block - 44) as u8)),
        46..=48 => Some(AtomicStateOnlyBlockV3::OutputNote((block - 46) as u8)),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicStateOnlyPathLevelV3 {
    pub level: u8,
    pub bit: u8,
    pub sibling: Digest,
    pub sibling_source: [TraceCell; DIGEST_ELEMS],
    pub bit_source: TraceCell,
    pub input_block: u8,
    pub output_block: u8,
    pub input_current: Digest,
    pub output_current: Digest,
    pub input_left: Digest,
    pub input_right: Digest,
    pub output_left: Digest,
    pub output_right: Digest,
    pub input_parent: Digest,
    pub output_parent: Digest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicStateOnlyTraceV3 {
    pub trace: StateOnlyTraceFoundation,
    pub input_leaf: Digest,
    pub output_leaf: Digest,
    pub current_anchor: Digest,
    pub output_anchor: Digest,
    /// Both paths name the same source cells in each entry. There is no
    /// second sibling or direction-bit witness namespace.
    pub path: [AtomicStateOnlyPathLevelV3; ATOMIC_PAYMENT_TREE_DEPTH],
}

fn volatile_clear_digest(digest: &mut Digest) {
    for value in digest {
        // SAFETY: all metadata is uniquely borrowed during drop.
        unsafe { core::ptr::write_volatile(value, M31::ZERO) };
    }
}

impl Drop for AtomicStateOnlyTraceV3 {
    fn drop(&mut self) {
        volatile_clear_digest(&mut self.input_leaf);
        volatile_clear_digest(&mut self.output_leaf);
        volatile_clear_digest(&mut self.current_anchor);
        volatile_clear_digest(&mut self.output_anchor);
        for level in &mut self.path {
            volatile_clear_digest(&mut level.sibling);
            volatile_clear_digest(&mut level.input_current);
            volatile_clear_digest(&mut level.output_current);
            volatile_clear_digest(&mut level.input_left);
            volatile_clear_digest(&mut level.input_right);
            volatile_clear_digest(&mut level.output_left);
            volatile_clear_digest(&mut level.output_right);
            volatile_clear_digest(&mut level.input_parent);
            volatile_clear_digest(&mut level.output_parent);
            // The direction bit is witness-derived even though it is also
            // represented inside the trace.
            unsafe { core::ptr::write_volatile(&mut level.bit, 0) };
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicStateOnlyTraceV3Error {
    PathDepth,
    PathIndexOutOfRange,
    CurrentAnchorMismatch,
    OutputAnchorMismatch,
    SpendBinding,
    SurrogateTrace,
    Projection,
    Layout,
    TraceMismatch { row: u16, column: u8 },
    PathMetadataMismatch { level: u8 },
}

fn ordered_children(current: Digest, sibling: Digest, bit: u8) -> (Digest, Digest) {
    if bit == 0 {
        (current, sibling)
    } else {
        (sibling, current)
    }
}

pub fn atomic_merkle_root_v3(
    leaf: Digest,
    path: &MerklePath,
) -> Result<Digest, AtomicStateOnlyTraceV3Error> {
    if path.siblings.len() != ATOMIC_PAYMENT_TREE_DEPTH {
        return Err(AtomicStateOnlyTraceV3Error::PathDepth);
    }
    if u64::from(path.index) >= (1u64 << ATOMIC_PAYMENT_TREE_DEPTH) {
        return Err(AtomicStateOnlyTraceV3Error::PathIndexOutOfRange);
    }
    let mut current = leaf;
    for (level, sibling) in path.siblings.iter().copied().enumerate() {
        let bit = ((path.index >> level) & 1) as u8;
        let (left, right) = ordered_children(current, sibling, bit);
        current = merkle_node_compress_v3(&left, &right);
    }
    Ok(current)
}

fn clear_block(trace: &mut StateOnlyTraceFoundation, block: usize) {
    let base = block * BLOCK_ROWS;
    for column in &mut trace.c1 {
        column[base..base + BLOCK_ROWS].fill(M31::ZERO);
    }
}

fn write_node_block(
    trace: &mut StateOnlyTraceFoundation,
    block: usize,
    left: &Digest,
    right: &Digest,
) -> Digest {
    clear_block(trace, block);
    let base = block * BLOCK_ROWS;

    // The state-only leading transition adds row 12 into the first eight
    // lanes of row 0. Keep the full-state tweak in row 0 lane 15.
    for lane in 0..DIGEST_ELEMS {
        trace.c1[RATE + lane][base] = right[lane];
        trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] = left[lane];
    }
    trace.c1[POSEIDON2_WIDTH - 1][base] =
        trace.c1[POSEIDON2_WIDTH - 1][base].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);

    let mut state = [M31::ZERO; POSEIDON2_WIDTH];
    state[..DIGEST_ELEMS].copy_from_slice(left);
    state[DIGEST_ELEMS..].copy_from_slice(right);
    state[POSEIDON2_WIDTH - 1] = state[POSEIDON2_WIDTH - 1].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    let mut transitions = Vec::with_capacity(POSEIDON2_ROUNDS);
    permute_optimized_with_trace(&mut state, |transition| transitions.push(transition));
    debug_assert_eq!(transitions.len(), POSEIDON2_ROUNDS);

    for local_row in 1..STATE_ONLY_FINAL_ROW_IN_BLOCK {
        let input = transitions[2 * local_row - 1].output;
        for lane in 0..POSEIDON2_WIDTH {
            trace.c1[lane][base + local_row] = input[lane];
        }
    }
    for lane in 0..POSEIDON2_WIDTH {
        trace.c1[lane][base + STATE_ONLY_FINAL_ROW_IN_BLOCK] = state[lane];
    }
    core::array::from_fn(|lane| state[lane])
}

fn digest_at(trace: &StateOnlyTraceFoundation, block: usize, local_row: usize) -> Digest {
    let row = block * BLOCK_ROWS + local_row;
    core::array::from_fn(|lane| trace.c1[lane][row])
}

fn read_cell(trace: &StateOnlyTraceFoundation, cell: TraceCell) -> M31 {
    trace.c1[usize::from(cell.column)][usize::from(cell.row)]
}

fn write_cell(trace: &mut StateOnlyTraceFoundation, cell: TraceCell, value: M31) {
    trace.c1[usize::from(cell.column)][usize::from(cell.row)] = value;
}

fn build_unvalidated(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
) -> Result<AtomicStateOnlyTraceV3, AtomicStateOnlyTraceV3Error> {
    if witness.merkle_path.siblings.len() != ATOMIC_PAYMENT_TREE_DEPTH {
        return Err(AtomicStateOnlyTraceV3Error::PathDepth);
    }
    if u64::from(witness.merkle_path.index) >= (1u64 << ATOMIC_PAYMENT_TREE_DEPTH) {
        return Err(AtomicStateOnlyTraceV3Error::PathIndexOutOfRange);
    }

    let owner_key = derive_owner_key(&witness.nullifier_key);
    let input_leaf = note_commitment(
        &owner_key,
        witness.value,
        witness.input_asset_id,
        &witness.input_salt,
    );
    let output_leaf = output_commitment(
        &witness.output_owner_key,
        witness.value_out,
        witness.input_asset_id,
        &witness.output_salt,
    );
    if output_leaf != statement.spend.output_commitment {
        return Err(AtomicStateOnlyTraceV3Error::SpendBinding);
    }
    let current_anchor = atomic_merkle_root_v3(input_leaf, &witness.merkle_path)?;
    if current_anchor != statement.spend.anchor {
        return Err(AtomicStateOnlyTraceV3Error::CurrentAnchorMismatch);
    }
    let output_anchor = atomic_merkle_root_v3(output_leaf, &witness.merkle_path)?;
    if output_anchor != statement.output_anchor {
        return Err(AtomicStateOnlyTraceV3Error::OutputAnchorMismatch);
    }

    // The unchanged blocks are produced by the already hardened v2 SpendV0
    // recorder under a surrogate v2 anchor. Blocks 4..43 are replaced below.
    let surrogate_anchor = merkle_root(input_leaf, &witness.merkle_path)
        .map_err(|_| AtomicStateOnlyTraceV3Error::SurrogateTrace)?;
    let surrogate_public = SpendPublic {
        anchor: surrogate_anchor,
        nullifier: statement.spend.nullifier,
        output_commitment: statement.spend.output_commitment,
        asset_id: statement.spend.asset_id,
        fee: statement.spend.fee,
    };
    let source = build_spend_trace_v4(&surrogate_public, witness)
        .map_err(|_| AtomicStateOnlyTraceV3Error::SurrogateTrace)?;
    let mut trace = project_state_only_trace_v4(&source)
        .map_err(|_| AtomicStateOnlyTraceV3Error::Projection)?;
    let atomic_aux =
        atomic_state_only_path_aux_layout_v3().map_err(|_| AtomicStateOnlyTraceV3Error::Layout)?;

    let mut input_current = input_leaf;
    let mut output_current = output_leaf;
    let mut path = Vec::with_capacity(ATOMIC_PAYMENT_TREE_DEPTH);
    for level in 0..ATOMIC_PAYMENT_TREE_DEPTH {
        let sibling = witness.merkle_path.siblings[level];
        let bit = ((witness.merkle_path.index >> level) & 1) as u8;
        let (input_left, input_right) = ordered_children(input_current, sibling, bit);
        let (output_left, output_right) = ordered_children(output_current, sibling, bit);
        let path_aux = atomic_aux[level];
        write_cell(&mut trace, path_aux.input_bit, M31(u32::from(bit)));
        write_cell(&mut trace, path_aux.output_bit, M31(u32::from(bit)));
        write_cell(&mut trace, path_aux.sibling_bit, M31(u32::from(bit)));
        for limb in 0..DIGEST_ELEMS {
            write_cell(
                &mut trace,
                path_aux.input_current[limb],
                input_current[limb],
            );
            write_cell(
                &mut trace,
                path_aux.output_current[limb],
                output_current[limb],
            );
            write_cell(&mut trace, path_aux.sibling[limb], sibling[limb]);
        }
        let input_block = ATOMIC_STATE_ONLY_INPUT_PATH_BLOCK_START + level;
        let output_block = ATOMIC_STATE_ONLY_OUTPUT_PATH_BLOCK_START + level;
        let input_parent = write_node_block(&mut trace, input_block, &input_left, &input_right);
        let output_parent = write_node_block(&mut trace, output_block, &output_left, &output_right);
        debug_assert_eq!(
            input_parent,
            merkle_node_compress_v3(&input_left, &input_right)
        );
        debug_assert_eq!(
            output_parent,
            merkle_node_compress_v3(&output_left, &output_right)
        );
        path.push(AtomicStateOnlyPathLevelV3 {
            level: level as u8,
            bit,
            sibling,
            sibling_source: path_aux.sibling,
            bit_source: path_aux.input_bit,
            input_block: input_block as u8,
            output_block: output_block as u8,
            input_current,
            output_current,
            input_left,
            input_right,
            output_left,
            output_right,
            input_parent,
            output_parent,
        });
        input_current = input_parent;
        output_current = output_parent;
    }
    debug_assert_eq!(input_current, current_anchor);
    debug_assert_eq!(output_current, output_anchor);
    debug_assert_eq!(
        digest_at(
            &trace,
            ATOMIC_STATE_ONLY_INPUT_ROOT_BLOCK,
            STATE_ONLY_FINAL_ROW_IN_BLOCK,
        ),
        current_anchor
    );
    debug_assert_eq!(
        digest_at(
            &trace,
            ATOMIC_STATE_ONLY_OUTPUT_ROOT_BLOCK,
            STATE_ONLY_FINAL_ROW_IN_BLOCK,
        ),
        output_anchor
    );

    let path: [AtomicStateOnlyPathLevelV3; ATOMIC_PAYMENT_TREE_DEPTH] = path
        .try_into()
        .map_err(|_| AtomicStateOnlyTraceV3Error::PathDepth)?;
    Ok(AtomicStateOnlyTraceV3 {
        trace,
        input_leaf,
        output_leaf,
        current_anchor,
        output_anchor,
        path,
    })
}

pub fn build_atomic_state_only_trace_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
) -> Result<AtomicStateOnlyTraceV3, AtomicStateOnlyTraceV3Error> {
    let foundation = build_unvalidated(statement, witness)?;
    validate_atomic_state_only_trace_v3(statement, witness, &foundation)?;
    Ok(foundation)
}

/// Exact host reference guard. This is intentionally independent of future
/// compiled copy/terminal constants: it rebuilds from the public statement
/// and the one private path, then compares every cell and alias descriptor.
pub fn validate_atomic_state_only_trace_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    candidate: &AtomicStateOnlyTraceV3,
) -> Result<(), AtomicStateOnlyTraceV3Error> {
    let expected = build_unvalidated(statement, witness)?;
    if candidate
        .trace
        .c1
        .iter()
        .any(|column| column.len() != TRACE_ROWS)
    {
        return Err(AtomicStateOnlyTraceV3Error::Projection);
    }
    for row in 0..TRACE_ROWS {
        for column in 0..STATE_ONLY_C1_COLUMNS {
            if candidate.trace.c1[column][row] != expected.trace.c1[column][row] {
                return Err(AtomicStateOnlyTraceV3Error::TraceMismatch {
                    row: row as u16,
                    column: column as u8,
                });
            }
        }
    }
    if candidate.input_leaf != expected.input_leaf
        || candidate.output_leaf != expected.output_leaf
        || candidate.current_anchor != expected.current_anchor
        || candidate.output_anchor != expected.output_anchor
    {
        return Err(AtomicStateOnlyTraceV3Error::SpendBinding);
    }
    for level in 0..ATOMIC_PAYMENT_TREE_DEPTH {
        if candidate.path[level] != expected.path[level] {
            return Err(AtomicStateOnlyTraceV3Error::PathMetadataMismatch { level: level as u8 });
        }
        for limb in 0..DIGEST_ELEMS {
            if read_cell(&candidate.trace, candidate.path[level].sibling_source[limb])
                != witness.merkle_path.siblings[level][limb]
            {
                return Err(AtomicStateOnlyTraceV3Error::PathMetadataMismatch {
                    level: level as u8,
                });
            }
        }
        if read_cell(&candidate.trace, candidate.path[level].bit_source)
            != M31(candidate.path[level].bit as u32)
        {
            return Err(AtomicStateOnlyTraceV3Error::PathMetadataMismatch { level: level as u8 });
        }
    }
    Ok(())
}

/// Public-root parity helper used by the future semantic binding generator.
pub fn atomic_state_only_bound_roots_v3(trace: &AtomicStateOnlyTraceV3) -> (Digest, Digest) {
    (
        digest_at(
            &trace.trace,
            ATOMIC_STATE_ONLY_INPUT_ROOT_BLOCK,
            STATE_ONLY_FINAL_ROW_IN_BLOCK,
        ),
        digest_at(
            &trace.trace,
            ATOMIC_STATE_ONLY_OUTPUT_ROOT_BLOCK,
            STATE_ONLY_FINAL_ROW_IN_BLOCK,
        ),
    )
}

/// Extract the exact ordered node input represented by row 0 plus row 12.
pub fn atomic_state_only_node_input_v3(
    trace: &AtomicStateOnlyTraceV3,
    block: usize,
) -> Option<[M31; POSEIDON2_WIDTH]> {
    match atomic_state_only_block_schedule_v3(block)? {
        AtomicStateOnlyBlockV3::InputPath(_) | AtomicStateOnlyBlockV3::OutputPath(_) => {}
        _ => return None,
    }
    let base = block * BLOCK_ROWS;
    let mut state = core::array::from_fn(|lane| trace.trace.c1[lane][base]);
    for lane in 0..RATE {
        state[lane] =
            state[lane].add(trace.trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK]);
    }
    Some(state)
}
