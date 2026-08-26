//! Pool V1 payment-trace foundation for the frozen Tag-73 geometry.
//!
//! This module records the exact existing Poseidon2-M31 sponge and v3-node
//! permutations used by an accepted Pool V1 payment relation.  It is a host
//! trace/compiler foundation only: it does not claim a verifier, prover,
//! terminal-oracle, transcript, or on-chain integration.

use alloc::vec;

use aspis_core::field::M31;

use crate::{
    poseidon2::{
        evaluate_trace_round_pair, hash_fields_with_trace, permute_optimized_with_trace, Digest,
        DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_ROUNDS, POSEIDON2_WIDTH, RATE,
    },
    spend::{DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY},
    state_only_trace::{
        StateOnlyTraceFoundation, STATE_ONLY_ABSORPTION_ROW_IN_BLOCK, STATE_ONLY_C1_COLUMNS,
        STATE_ONLY_FINAL_ROW_IN_BLOCK,
    },
    trace_v4::{TraceCell, BLOCK_ROWS, PERMUTATION_COUNT, TRACE_ROWS},
};

use super::{
    evaluate_pool_v1_private_transfer_v1, evaluate_pool_v1_withdrawal_v1,
    format::{pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent},
    payment_relation::{
        PoolV1InputNoteWitnessV1, PoolV1OutputNoteWitnessV1, PoolV1PaymentRelationContextV1,
        PoolV1PaymentRelationError, PoolV1PrivateTransferPublicV1, PoolV1PrivateTransferWitnessV1,
        PoolV1WithdrawalPublicV1, PoolV1WithdrawalWitnessV1,
    },
    payment_semantic_registry::{
        pool_v1_payment_aux_cell_is_used_v1, pool_v1_payment_conservation_aux_v1,
        pool_v1_payment_path_aux_v1, pool_v1_payment_value_aux_v1,
        POOL_V1_PAYMENT_AUX_ROW_END as ROUTED_AUX_ROW_END, POOL_V1_PAYMENT_VALUE_AUX_ROW_START,
    },
    POOL_V1_TREE_DEPTH,
};

pub const POOL_V1_PAYMENT_TRACE_ROWS: usize = 1 << 10;
pub const POOL_V1_PAYMENT_TRACE_C1_COLUMNS: usize = 16;
pub const POOL_V1_PAYMENT_TRACE_BLOCKS: usize = 49;
pub const POOL_V1_PAYMENT_TRACE_BLOCK_ROWS: usize = 16;
pub const POOL_V1_PAYMENT_TRACE_TWO_ROUND_ROWS_PER_BLOCK: usize = 11;
pub const POOL_V1_PAYMENT_TRACE_TWO_ROUND_TRANSITIONS: usize =
    POOL_V1_PAYMENT_TRACE_BLOCKS * POOL_V1_PAYMENT_TRACE_TWO_ROUND_ROWS_PER_BLOCK;
pub const POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS: usize =
    POOL_V1_PAYMENT_TRACE_BLOCKS * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS;

pub const POOL_V1_PAYMENT_DIRECTION_BITS: usize = 20;
pub const POOL_V1_PAYMENT_VALUE_COUNT: usize = 3;
pub const POOL_V1_PAYMENT_VALUE_BITS: usize = 30;
pub const POOL_V1_PAYMENT_DIRECTION_ROW_START: usize = 784;
pub const POOL_V1_PAYMENT_VALUE_ROW_START: usize = POOL_V1_PAYMENT_VALUE_AUX_ROW_START;
pub const POOL_V1_PAYMENT_AUX_ROW_END: usize = ROUTED_AUX_ROW_END;

/// The already-frozen Tag-73 native proof grammar.  This arithmetic screen is
/// recorded here to prevent a trace-only change from silently changing it; it
/// is not a claim that this new payment trace is wired into that verifier.
pub const POOL_V1_TAG73_FIXED_GRAMMAR_BYTES: usize = 9_936;
pub const POOL_V1_TAG73_ROOT_BYTES: usize = 52;
pub const POOL_V1_TAG73_WORK_BYTES: usize = 24;
pub const POOL_V1_TAG73_QUERY_COUNT: usize = 16;
pub const POOL_V1_TAG73_QUERY_BYTES: usize = 621;
pub const POOL_V1_TAG73_FRONTIER_COUNT: usize = 2;
pub const POOL_V1_TAG73_FRONTIER_NODES: usize = 203;
pub const POOL_V1_TAG73_FRONTIER_NODE_BYTES: usize = 26;
pub const POOL_V1_TAG73_PROOF_GRAMMAR_BYTES: usize = POOL_V1_TAG73_FIXED_GRAMMAR_BYTES
    + POOL_V1_TAG73_ROOT_BYTES
    + POOL_V1_TAG73_WORK_BYTES
    + POOL_V1_TAG73_QUERY_COUNT * POOL_V1_TAG73_QUERY_BYTES
    + POOL_V1_TAG73_FRONTIER_COUNT
        * POOL_V1_TAG73_FRONTIER_NODES
        * POOL_V1_TAG73_FRONTIER_NODE_BYTES;

const _: () = assert!(POOL_V1_TREE_DEPTH == 20);
const _: () = assert!(TRACE_ROWS == POOL_V1_PAYMENT_TRACE_ROWS);
const _: () = assert!(STATE_ONLY_C1_COLUMNS == POOL_V1_PAYMENT_TRACE_C1_COLUMNS);
const _: () = assert!(PERMUTATION_COUNT == POOL_V1_PAYMENT_TRACE_BLOCKS);
const _: () = assert!(BLOCK_ROWS == POOL_V1_PAYMENT_TRACE_BLOCK_ROWS);
const _: () = assert!(STATE_ONLY_FINAL_ROW_IN_BLOCK == 11);
const _: () = assert!(STATE_ONLY_ABSORPTION_ROW_IN_BLOCK == 12);
const _: () = assert!(POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS == 784);
const _: () = assert!(POOL_V1_TAG73_PROOF_GRAMMAR_BYTES == 30_504);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentTraceVariantV1 {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentTraceBlockV1 {
    OwnerKey,
    InputNote(u8),
    InputPath(u8),
    Nullifier(u8),
    RecipientNoteOrWithdrawalPadding(u8),
    ChangeNote(u8),
    FixedZeroPadding(u8),
}

pub const fn pool_v1_payment_trace_block_v1(block: usize) -> Option<PoolV1PaymentTraceBlockV1> {
    match block {
        0 => Some(PoolV1PaymentTraceBlockV1::OwnerKey),
        1..=3 => Some(PoolV1PaymentTraceBlockV1::InputNote((block - 1) as u8)),
        4..=23 => Some(PoolV1PaymentTraceBlockV1::InputPath((block - 4) as u8)),
        24..=25 => Some(PoolV1PaymentTraceBlockV1::Nullifier((block - 24) as u8)),
        26..=28 => Some(PoolV1PaymentTraceBlockV1::RecipientNoteOrWithdrawalPadding(
            (block - 26) as u8,
        )),
        29..=31 => Some(PoolV1PaymentTraceBlockV1::ChangeNote((block - 29) as u8)),
        32..=48 => Some(PoolV1PaymentTraceBlockV1::FixedZeroPadding(
            (block - 32) as u8,
        )),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentTracePublicOutputsV1 {
    PrivateTransfer {
        anchor: Digest,
        nullifier: Digest,
        recipient_commitment: Digest,
        change_commitment: Digest,
    },
    Withdrawal {
        anchor: Digest,
        nullifier: Digest,
        change_commitment: Digest,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentTraceV1 {
    /// Column-major 1024-row / 16-C1 physical trace.
    pub trace: StateOnlyTraceFoundation,
    pub variant: PoolV1PaymentTraceVariantV1,
    /// Private path directions, duplicated in the pinned auxiliary cells.
    pub direction_bits: [M31; POOL_V1_PAYMENT_DIRECTION_BITS],
    /// Input, recipient/withdrawal, and change values, in that order.
    pub value_bits: [[M31; POOL_V1_PAYMENT_VALUE_BITS]; POOL_V1_PAYMENT_VALUE_COUNT],
    pub public_outputs: PoolV1PaymentTracePublicOutputsV1,
}

impl Drop for PoolV1PaymentTraceV1 {
    fn drop(&mut self) {
        for bit in &mut self.direction_bits {
            // SAFETY: the trace metadata is uniquely borrowed during drop.
            unsafe { core::ptr::write_volatile(bit, M31::ZERO) };
        }
        for value in &mut self.value_bits {
            for bit in value {
                // SAFETY: the trace metadata is uniquely borrowed during drop.
                unsafe { core::ptr::write_volatile(bit, M31::ZERO) };
            }
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentTraceErrorV1 {
    Relation(PoolV1PaymentRelationError),
    Shape,
    WrongVariant,
    HashSchedule,
    BlockPreimageMismatch { block: u8, lane: u8 },
    BlockAbsorptionMismatch { block: u8, lane: u8 },
    TwoRoundTransitionMismatch { block: u8, local_row: u8, lane: u8 },
    NonZeroBlockPadding { block: u8, local_row: u8, lane: u8 },
    AuxiliaryMismatch { row: u16, column: u8 },
    DirectionMetadataMismatch { level: u8 },
    ValueMetadataMismatch { value: u8, bit: u8 },
    OwnerKeyParity,
    InputNoteParity,
    AnchorParity,
    NullifierParity,
    RecipientCommitmentParity,
    ChangeCommitmentParity,
    PublicOutputMetadata,
}

fn empty_trace() -> StateOnlyTraceFoundation {
    StateOnlyTraceFoundation {
        c1: core::array::from_fn(|_| vec![M31::ZERO; POOL_V1_PAYMENT_TRACE_ROWS]),
    }
}

fn note_input(note: &PoolV1OutputNoteWitnessV1, asset_id: M31) -> [M31; DIGEST_ELEMS * 2 + 2] {
    let mut input = [M31::ZERO; DIGEST_ELEMS * 2 + 2];
    input[..DIGEST_ELEMS].copy_from_slice(&note.owner_key);
    input[DIGEST_ELEMS] = M31(note.value);
    input[DIGEST_ELEMS + 1] = asset_id;
    input[DIGEST_ELEMS + 2..].copy_from_slice(&note.salt);
    input
}

fn input_note_input(
    owner_key: &Digest,
    input_note: &PoolV1InputNoteWitnessV1,
    asset_id: M31,
) -> [M31; DIGEST_ELEMS * 2 + 2] {
    note_input(
        &PoolV1OutputNoteWitnessV1 {
            owner_key: *owner_key,
            salt: input_note.salt,
            value: input_note.value,
        },
        asset_id,
    )
}

fn nullifier_input(input: &PoolV1InputNoteWitnessV1) -> [M31; DIGEST_ELEMS * 2] {
    let mut fields = [M31::ZERO; DIGEST_ELEMS * 2];
    fields[..DIGEST_ELEMS].copy_from_slice(&input.nullifier_key);
    fields[DIGEST_ELEMS..].copy_from_slice(&input.salt);
    fields
}

fn value_bits(value: u32) -> [M31; POOL_V1_PAYMENT_VALUE_BITS] {
    core::array::from_fn(|bit| M31((value >> bit) & 1))
}

fn direction_bits(input: &PoolV1InputNoteWitnessV1) -> [M31; POOL_V1_PAYMENT_DIRECTION_BITS] {
    core::array::from_fn(|level| M31((input.membership.index >> level) & 1))
}

fn write_direct_permutation(
    trace: &mut StateOnlyTraceFoundation,
    block: usize,
    pre_absorb: [M31; POSEIDON2_WIDTH],
    absorption: [M31; RATE],
) -> Result<[M31; POSEIDON2_WIDTH], PoolV1PaymentTraceErrorV1> {
    if block >= POOL_V1_PAYMENT_TRACE_BLOCKS {
        return Err(PoolV1PaymentTraceErrorV1::HashSchedule);
    }
    let base = block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS;
    for lane in 0..POSEIDON2_WIDTH {
        trace.c1[lane][base] = pre_absorb[lane];
    }
    for lane in 0..RATE {
        trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] = absorption[lane];
    }

    let mut state = pre_absorb;
    for lane in 0..RATE {
        state[lane] = state[lane].add(absorption[lane]);
    }
    let mut rounds = 0usize;
    permute_optimized_with_trace(&mut state, |transition| {
        rounds += 1;
        if transition.round & 1 == 1 {
            let local_row = usize::from(transition.round) / 2;
            for lane in 0..POSEIDON2_WIDTH {
                trace.c1[lane][base + local_row + 1] = transition.output[lane];
            }
        }
    });
    if rounds != POSEIDON2_ROUNDS {
        return Err(PoolV1PaymentTraceErrorV1::HashSchedule);
    }
    Ok(state)
}

fn write_sponge(
    trace: &mut StateOnlyTraceFoundation,
    block_start: usize,
    domain: M31,
    input: &[M31],
) -> Result<Digest, PoolV1PaymentTraceErrorV1> {
    let permutation_count = input.len().div_ceil(RATE);
    if input.is_empty() || permutation_count > 3 || block_start + permutation_count > 49 {
        return Err(PoolV1PaymentTraceErrorV1::HashSchedule);
    }
    let mut round_counts = [0u8; 3];
    let mut malformed = false;
    let digest = hash_fields_with_trace(domain, input, |permutation, transition| {
        if permutation >= permutation_count {
            malformed = true;
            return;
        }
        round_counts[permutation] = round_counts[permutation].saturating_add(1);
        let block = block_start + permutation;
        let base = block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS;
        let start = permutation * RATE;
        let chunk = &input[start..core::cmp::min(start + RATE, input.len())];
        if transition.round == 0 {
            for lane in 0..POSEIDON2_WIDTH {
                let absorbed = if lane < chunk.len() {
                    chunk[lane]
                } else {
                    M31::ZERO
                };
                trace.c1[lane][base] = transition.input[lane].sub(absorbed);
            }
            for (lane, value) in chunk.iter().copied().enumerate() {
                trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] = value;
            }
        }
        if transition.round & 1 == 1 {
            let local_row = usize::from(transition.round) / 2;
            for lane in 0..POSEIDON2_WIDTH {
                trace.c1[lane][base + local_row + 1] = transition.output[lane];
            }
        }
    });
    if malformed
        || round_counts[..permutation_count]
            .iter()
            .any(|rounds| usize::from(*rounds) != POSEIDON2_ROUNDS)
    {
        return Err(PoolV1PaymentTraceErrorV1::HashSchedule);
    }
    Ok(digest)
}

fn write_node(
    trace: &mut StateOnlyTraceFoundation,
    block: usize,
    left: &Digest,
    right: &Digest,
) -> Result<Digest, PoolV1PaymentTraceErrorV1> {
    let mut pre_absorb = [M31::ZERO; POSEIDON2_WIDTH];
    pre_absorb[RATE..].copy_from_slice(right);
    pre_absorb[POSEIDON2_WIDTH - 1] =
        pre_absorb[POSEIDON2_WIDTH - 1].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    let final_state = write_direct_permutation(trace, block, pre_absorb, *left)?;
    Ok(core::array::from_fn(|lane| final_state[lane]))
}

fn write_zero_padding(
    trace: &mut StateOnlyTraceFoundation,
    block: usize,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    write_direct_permutation(
        trace,
        block,
        [M31::ZERO; POSEIDON2_WIDTH],
        [M31::ZERO; RATE],
    )?;
    Ok(())
}

fn write_trace_cell(trace: &mut StateOnlyTraceFoundation, target: TraceCell, value: M31) {
    trace.c1[usize::from(target.column)][usize::from(target.row)] = value;
}

fn write_path_auxiliary(
    trace: &mut StateOnlyTraceFoundation,
    level: usize,
    bit: M31,
    current: &Digest,
    sibling: &Digest,
    left: &Digest,
    right: &Digest,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    let aux = pool_v1_payment_path_aux_v1(level).ok_or(PoolV1PaymentTraceErrorV1::HashSchedule)?;
    write_trace_cell(trace, aux.bit, bit);
    for lane in 0..DIGEST_ELEMS {
        write_trace_cell(trace, aux.current[lane], current[lane]);
        write_trace_cell(trace, aux.sibling[lane], sibling[lane]);
        write_trace_cell(trace, aux.left[lane], left[lane]);
        write_trace_cell(trace, aux.right[lane], right[lane]);
    }
    Ok(())
}

fn write_auxiliary(
    trace: &mut StateOnlyTraceFoundation,
    values: &[[M31; POOL_V1_PAYMENT_VALUE_BITS]; POOL_V1_PAYMENT_VALUE_COUNT],
    actual_values: &[M31; POOL_V1_PAYMENT_VALUE_COUNT],
) {
    for (value_index, bits) in values.iter().enumerate() {
        let aux = pool_v1_payment_value_aux_v1(value_index).expect("three-value layout");
        for (bit_index, bit) in bits.iter().copied().enumerate() {
            write_trace_cell(trace, aux.bits[bit_index], bit);
        }
        write_trace_cell(trace, aux.source, actual_values[value_index]);
    }
    let conservation = pool_v1_payment_conservation_aux_v1();
    let partial = actual_values[0].sub(actual_values[1]);
    write_trace_cell(trace, conservation.input, actual_values[0]);
    write_trace_cell(trace, conservation.recipient_or_amount, actual_values[1]);
    write_trace_cell(trace, conservation.partial, partial);
    write_trace_cell(trace, conservation.carried_partial, partial);
    write_trace_cell(trace, conservation.change, actual_values[2]);
}

fn ordered_children(current: Digest, sibling: Digest, bit: M31) -> (Digest, Digest) {
    if bit == M31::ZERO {
        (current, sibling)
    } else {
        (sibling, current)
    }
}

fn build_common_prefix(
    trace: &mut StateOnlyTraceFoundation,
    input: &PoolV1InputNoteWitnessV1,
    asset_id: M31,
) -> Result<(Digest, Digest), PoolV1PaymentTraceErrorV1> {
    let owner_key = write_sponge(trace, 0, DOMAIN_OWNER_KEY, &input.nullifier_key)?;
    if owner_key != crate::derive_owner_key(&input.nullifier_key) {
        return Err(PoolV1PaymentTraceErrorV1::OwnerKeyParity);
    }
    let input_fields = input_note_input(&owner_key, input, asset_id);
    let input_leaf = write_sponge(trace, 1, DOMAIN_NOTE, &input_fields)?;
    if input_leaf != pool_v1_note_commitment(&owner_key, input.value, asset_id, &input.salt) {
        return Err(PoolV1PaymentTraceErrorV1::InputNoteParity);
    }
    let directions = direction_bits(input);
    let mut current = input_leaf;
    for level in 0..POOL_V1_TREE_DEPTH {
        let previous = current;
        let (left, right) = ordered_children(
            previous,
            input.membership.siblings[level],
            directions[level],
        );
        write_path_auxiliary(
            trace,
            level,
            directions[level],
            &previous,
            &input.membership.siblings[level],
            &left,
            &right,
        )?;
        current = write_node(trace, 4 + level, &left, &right)?;
        if current != pool_v1_tree_parent(&left, &right) {
            return Err(PoolV1PaymentTraceErrorV1::AnchorParity);
        }
    }
    let nullifier_fields = nullifier_input(input);
    let nullifier = write_sponge(trace, 24, DOMAIN_NULLIFIER, &nullifier_fields)?;
    if nullifier != pool_v1_nullifier(&input.nullifier_key, &input.salt) {
        return Err(PoolV1PaymentTraceErrorV1::NullifierParity);
    }
    Ok((current, nullifier))
}

fn build_transfer_after_relation(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PrivateTransferWitnessV1,
) -> Result<PoolV1PaymentTraceV1, PoolV1PaymentTraceErrorV1> {
    let mut trace = empty_trace();
    let (anchor, nullifier) = build_common_prefix(&mut trace, &witness.input, public.asset_id)?;
    if anchor != public.anchor_root {
        return Err(PoolV1PaymentTraceErrorV1::AnchorParity);
    }
    if nullifier != public.nullifier {
        return Err(PoolV1PaymentTraceErrorV1::NullifierParity);
    }

    let recipient_fields = note_input(&witness.recipient, public.asset_id);
    let recipient_commitment = write_sponge(&mut trace, 26, DOMAIN_NOTE, &recipient_fields)?;
    if recipient_commitment != public.recipient_commitment {
        return Err(PoolV1PaymentTraceErrorV1::RecipientCommitmentParity);
    }
    let change_fields = note_input(&witness.change, public.asset_id);
    let change_commitment = write_sponge(&mut trace, 29, DOMAIN_NOTE, &change_fields)?;
    if change_commitment != public.change_commitment {
        return Err(PoolV1PaymentTraceErrorV1::ChangeCommitmentParity);
    }
    for block in 32..POOL_V1_PAYMENT_TRACE_BLOCKS {
        write_zero_padding(&mut trace, block)?;
    }

    let directions = direction_bits(&witness.input);
    let values = [
        value_bits(witness.input.value),
        value_bits(witness.recipient.value),
        value_bits(witness.change.value),
    ];
    write_auxiliary(
        &mut trace,
        &values,
        &[
            M31(witness.input.value),
            M31(witness.recipient.value),
            M31(witness.change.value),
        ],
    );
    Ok(PoolV1PaymentTraceV1 {
        trace,
        variant: PoolV1PaymentTraceVariantV1::PrivateTransfer,
        direction_bits: directions,
        value_bits: values,
        public_outputs: PoolV1PaymentTracePublicOutputsV1::PrivateTransfer {
            anchor,
            nullifier,
            recipient_commitment,
            change_commitment,
        },
    })
}

fn build_withdrawal_after_relation(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1WithdrawalWitnessV1,
) -> Result<PoolV1PaymentTraceV1, PoolV1PaymentTraceErrorV1> {
    let mut trace = empty_trace();
    let (anchor, nullifier) = build_common_prefix(&mut trace, &witness.input, public.asset_id)?;
    if anchor != public.anchor_root {
        return Err(PoolV1PaymentTraceErrorV1::AnchorParity);
    }
    if nullifier != public.nullifier {
        return Err(PoolV1PaymentTraceErrorV1::NullifierParity);
    }

    for block in 26..=28 {
        write_zero_padding(&mut trace, block)?;
    }
    let change_fields = note_input(&witness.change, public.asset_id);
    let change_commitment = write_sponge(&mut trace, 29, DOMAIN_NOTE, &change_fields)?;
    if change_commitment != public.change_commitment {
        return Err(PoolV1PaymentTraceErrorV1::ChangeCommitmentParity);
    }
    for block in 32..POOL_V1_PAYMENT_TRACE_BLOCKS {
        write_zero_padding(&mut trace, block)?;
    }

    let directions = direction_bits(&witness.input);
    let values = [
        value_bits(witness.input.value),
        value_bits(public.amount),
        value_bits(witness.change.value),
    ];
    write_auxiliary(
        &mut trace,
        &values,
        &[
            M31(witness.input.value),
            M31(public.amount),
            M31(witness.change.value),
        ],
    );
    Ok(PoolV1PaymentTraceV1 {
        trace,
        variant: PoolV1PaymentTraceVariantV1::Withdrawal,
        direction_bits: directions,
        value_bits: values,
        public_outputs: PoolV1PaymentTracePublicOutputsV1::Withdrawal {
            anchor,
            nullifier,
            change_commitment,
        },
    })
}

fn check_shape(trace: &PoolV1PaymentTraceV1) -> Result<(), PoolV1PaymentTraceErrorV1> {
    if trace
        .trace
        .c1
        .iter()
        .any(|column| column.len() != POOL_V1_PAYMENT_TRACE_ROWS)
    {
        return Err(PoolV1PaymentTraceErrorV1::Shape);
    }
    Ok(())
}

fn replay_block(
    trace: &PoolV1PaymentTraceV1,
    block: usize,
    expected_pre_absorb: [M31; POSEIDON2_WIDTH],
    expected_absorption: [M31; RATE],
) -> Result<[M31; POSEIDON2_WIDTH], PoolV1PaymentTraceErrorV1> {
    let base = block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS;
    for lane in 0..POSEIDON2_WIDTH {
        if trace.trace.c1[lane][base] != expected_pre_absorb[lane] {
            return Err(PoolV1PaymentTraceErrorV1::BlockPreimageMismatch {
                block: block as u8,
                lane: lane as u8,
            });
        }
        let expected = if lane < RATE {
            expected_absorption[lane]
        } else {
            M31::ZERO
        };
        if trace.trace.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] != expected {
            return Err(PoolV1PaymentTraceErrorV1::BlockAbsorptionMismatch {
                block: block as u8,
                lane: lane as u8,
            });
        }
    }
    for local_row in STATE_ONLY_ABSORPTION_ROW_IN_BLOCK + 1..POOL_V1_PAYMENT_TRACE_BLOCK_ROWS {
        for lane in 0..POSEIDON2_WIDTH {
            if trace.trace.c1[lane][base + local_row] != M31::ZERO {
                return Err(PoolV1PaymentTraceErrorV1::NonZeroBlockPadding {
                    block: block as u8,
                    local_row: local_row as u8,
                    lane: lane as u8,
                });
            }
        }
    }

    let mut state = expected_pre_absorb;
    for lane in 0..RATE {
        state[lane] = state[lane].add(expected_absorption[lane]);
    }
    for local_row in 0..POOL_V1_PAYMENT_TRACE_TWO_ROUND_ROWS_PER_BLOCK {
        let (_, second) = evaluate_trace_round_pair(state, local_row)
            .ok_or(PoolV1PaymentTraceErrorV1::HashSchedule)?;
        for lane in 0..POSEIDON2_WIDTH {
            if trace.trace.c1[lane][base + local_row + 1] != second[lane] {
                return Err(PoolV1PaymentTraceErrorV1::TwoRoundTransitionMismatch {
                    block: block as u8,
                    local_row: local_row as u8,
                    lane: lane as u8,
                });
            }
        }
        state = second;
    }
    Ok(state)
}

fn replay_sponge(
    trace: &PoolV1PaymentTraceV1,
    block_start: usize,
    domain: M31,
    input: &[M31],
) -> Result<Digest, PoolV1PaymentTraceErrorV1> {
    if input.is_empty() {
        return Err(PoolV1PaymentTraceErrorV1::HashSchedule);
    }
    let mut pre_absorb = [M31::ZERO; POSEIDON2_WIDTH];
    pre_absorb[RATE] = domain;
    pre_absorb[RATE + 1] = M31(input.len() as u32);
    for (permutation, chunk) in input.chunks(RATE).enumerate() {
        let mut absorption = [M31::ZERO; RATE];
        absorption[..chunk.len()].copy_from_slice(chunk);
        pre_absorb = replay_block(trace, block_start + permutation, pre_absorb, absorption)?;
    }
    Ok(core::array::from_fn(|lane| pre_absorb[lane]))
}

fn replay_node(
    trace: &PoolV1PaymentTraceV1,
    block: usize,
    left: &Digest,
    right: &Digest,
) -> Result<Digest, PoolV1PaymentTraceErrorV1> {
    let mut pre_absorb = [M31::ZERO; POSEIDON2_WIDTH];
    pre_absorb[RATE..].copy_from_slice(right);
    pre_absorb[POSEIDON2_WIDTH - 1] =
        pre_absorb[POSEIDON2_WIDTH - 1].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    let final_state = replay_block(trace, block, pre_absorb, *left)?;
    Ok(core::array::from_fn(|lane| final_state[lane]))
}

fn replay_zero_padding(
    trace: &PoolV1PaymentTraceV1,
    block: usize,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    replay_block(
        trace,
        block,
        [M31::ZERO; POSEIDON2_WIDTH],
        [M31::ZERO; RATE],
    )?;
    Ok(())
}

fn validate_trace_cell(
    trace: &PoolV1PaymentTraceV1,
    target: TraceCell,
    expected: M31,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    if trace.trace.c1[usize::from(target.column)][usize::from(target.row)] != expected {
        return Err(PoolV1PaymentTraceErrorV1::AuxiliaryMismatch {
            row: target.row,
            column: target.column,
        });
    }
    Ok(())
}

fn validate_path_auxiliary(
    trace: &PoolV1PaymentTraceV1,
    level: usize,
    bit: M31,
    current: &Digest,
    sibling: &Digest,
    left: &Digest,
    right: &Digest,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    let aux = pool_v1_payment_path_aux_v1(level).ok_or(PoolV1PaymentTraceErrorV1::HashSchedule)?;
    validate_trace_cell(trace, aux.bit, bit)?;
    for lane in 0..DIGEST_ELEMS {
        validate_trace_cell(trace, aux.current[lane], current[lane])?;
        validate_trace_cell(trace, aux.sibling[lane], sibling[lane])?;
        validate_trace_cell(trace, aux.left[lane], left[lane])?;
        validate_trace_cell(trace, aux.right[lane], right[lane])?;
    }
    Ok(())
}

fn validate_auxiliary(
    trace: &PoolV1PaymentTraceV1,
    directions: &[M31; POOL_V1_PAYMENT_DIRECTION_BITS],
    values: &[[M31; POOL_V1_PAYMENT_VALUE_BITS]; POOL_V1_PAYMENT_VALUE_COUNT],
    actual_values: &[M31; POOL_V1_PAYMENT_VALUE_COUNT],
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    for (level, expected) in directions.iter().copied().enumerate() {
        if trace.direction_bits[level] != expected {
            return Err(PoolV1PaymentTraceErrorV1::DirectionMetadataMismatch {
                level: level as u8,
            });
        }
    }
    for (value_index, expected_bits) in values.iter().enumerate() {
        for (bit_index, expected) in expected_bits.iter().copied().enumerate() {
            if trace.value_bits[value_index][bit_index] != expected {
                return Err(PoolV1PaymentTraceErrorV1::ValueMetadataMismatch {
                    value: value_index as u8,
                    bit: bit_index as u8,
                });
            }
        }
    }

    for (value_index, bits) in values.iter().enumerate() {
        let aux = pool_v1_payment_value_aux_v1(value_index)
            .ok_or(PoolV1PaymentTraceErrorV1::HashSchedule)?;
        for (bit_index, expected) in bits.iter().copied().enumerate() {
            validate_trace_cell(trace, aux.bits[bit_index], expected)?;
        }
        validate_trace_cell(trace, aux.source, actual_values[value_index])?;
    }
    let conservation = pool_v1_payment_conservation_aux_v1();
    let partial = actual_values[0].sub(actual_values[1]);
    for (target, expected) in [
        (conservation.input, actual_values[0]),
        (conservation.recipient_or_amount, actual_values[1]),
        (conservation.partial, partial),
        (conservation.carried_partial, partial),
        (conservation.change, actual_values[2]),
    ] {
        validate_trace_cell(trace, target, expected)?;
    }

    for row in POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS..POOL_V1_PAYMENT_TRACE_ROWS {
        for column in 0..POSEIDON2_WIDTH {
            if !pool_v1_payment_aux_cell_is_used_v1(row, column)
                && trace.trace.c1[column][row] != M31::ZERO
            {
                return Err(PoolV1PaymentTraceErrorV1::AuxiliaryMismatch {
                    row: row as u16,
                    column: column as u8,
                });
            }
        }
    }
    Ok(())
}

fn validate_common_prefix(
    trace: &PoolV1PaymentTraceV1,
    input: &PoolV1InputNoteWitnessV1,
    asset_id: M31,
) -> Result<(Digest, Digest), PoolV1PaymentTraceErrorV1> {
    let owner_key = replay_sponge(trace, 0, DOMAIN_OWNER_KEY, &input.nullifier_key)?;
    if owner_key != crate::derive_owner_key(&input.nullifier_key) {
        return Err(PoolV1PaymentTraceErrorV1::OwnerKeyParity);
    }
    let input_fields = input_note_input(&owner_key, input, asset_id);
    let input_leaf = replay_sponge(trace, 1, DOMAIN_NOTE, &input_fields)?;
    if input_leaf != pool_v1_note_commitment(&owner_key, input.value, asset_id, &input.salt) {
        return Err(PoolV1PaymentTraceErrorV1::InputNoteParity);
    }
    let directions = direction_bits(input);
    let mut current = input_leaf;
    for level in 0..POOL_V1_TREE_DEPTH {
        let previous = current;
        let (left, right) = ordered_children(
            previous,
            input.membership.siblings[level],
            directions[level],
        );
        validate_path_auxiliary(
            trace,
            level,
            directions[level],
            &previous,
            &input.membership.siblings[level],
            &left,
            &right,
        )?;
        current = replay_node(trace, 4 + level, &left, &right)?;
        if current != pool_v1_tree_parent(&left, &right) {
            return Err(PoolV1PaymentTraceErrorV1::AnchorParity);
        }
    }
    let nullifier_fields = nullifier_input(input);
    let nullifier = replay_sponge(trace, 24, DOMAIN_NULLIFIER, &nullifier_fields)?;
    if nullifier != pool_v1_nullifier(&input.nullifier_key, &input.salt) {
        return Err(PoolV1PaymentTraceErrorV1::NullifierParity);
    }
    Ok((current, nullifier))
}

fn validate_transfer_after_relation(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PrivateTransferWitnessV1,
    trace: &PoolV1PaymentTraceV1,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    check_shape(trace)?;
    if trace.variant != PoolV1PaymentTraceVariantV1::PrivateTransfer {
        return Err(PoolV1PaymentTraceErrorV1::WrongVariant);
    }
    let (anchor, nullifier) = validate_common_prefix(trace, &witness.input, public.asset_id)?;
    if anchor != public.anchor_root {
        return Err(PoolV1PaymentTraceErrorV1::AnchorParity);
    }
    if nullifier != public.nullifier {
        return Err(PoolV1PaymentTraceErrorV1::NullifierParity);
    }
    let recipient_fields = note_input(&witness.recipient, public.asset_id);
    let recipient_commitment = replay_sponge(trace, 26, DOMAIN_NOTE, &recipient_fields)?;
    if recipient_commitment != public.recipient_commitment {
        return Err(PoolV1PaymentTraceErrorV1::RecipientCommitmentParity);
    }
    let change_fields = note_input(&witness.change, public.asset_id);
    let change_commitment = replay_sponge(trace, 29, DOMAIN_NOTE, &change_fields)?;
    if change_commitment != public.change_commitment {
        return Err(PoolV1PaymentTraceErrorV1::ChangeCommitmentParity);
    }
    for block in 32..POOL_V1_PAYMENT_TRACE_BLOCKS {
        replay_zero_padding(trace, block)?;
    }
    let directions = direction_bits(&witness.input);
    let values = [
        value_bits(witness.input.value),
        value_bits(witness.recipient.value),
        value_bits(witness.change.value),
    ];
    validate_auxiliary(
        trace,
        &directions,
        &values,
        &[
            M31(witness.input.value),
            M31(witness.recipient.value),
            M31(witness.change.value),
        ],
    )?;
    if trace.public_outputs
        != (PoolV1PaymentTracePublicOutputsV1::PrivateTransfer {
            anchor,
            nullifier,
            recipient_commitment,
            change_commitment,
        })
    {
        return Err(PoolV1PaymentTraceErrorV1::PublicOutputMetadata);
    }
    Ok(())
}

fn validate_withdrawal_after_relation(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1WithdrawalWitnessV1,
    trace: &PoolV1PaymentTraceV1,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    check_shape(trace)?;
    if trace.variant != PoolV1PaymentTraceVariantV1::Withdrawal {
        return Err(PoolV1PaymentTraceErrorV1::WrongVariant);
    }
    let (anchor, nullifier) = validate_common_prefix(trace, &witness.input, public.asset_id)?;
    if anchor != public.anchor_root {
        return Err(PoolV1PaymentTraceErrorV1::AnchorParity);
    }
    if nullifier != public.nullifier {
        return Err(PoolV1PaymentTraceErrorV1::NullifierParity);
    }
    for block in 26..=28 {
        replay_zero_padding(trace, block)?;
    }
    let change_fields = note_input(&witness.change, public.asset_id);
    let change_commitment = replay_sponge(trace, 29, DOMAIN_NOTE, &change_fields)?;
    if change_commitment != public.change_commitment {
        return Err(PoolV1PaymentTraceErrorV1::ChangeCommitmentParity);
    }
    for block in 32..POOL_V1_PAYMENT_TRACE_BLOCKS {
        replay_zero_padding(trace, block)?;
    }
    let directions = direction_bits(&witness.input);
    let values = [
        value_bits(witness.input.value),
        value_bits(public.amount),
        value_bits(witness.change.value),
    ];
    validate_auxiliary(
        trace,
        &directions,
        &values,
        &[
            M31(witness.input.value),
            M31(public.amount),
            M31(witness.change.value),
        ],
    )?;
    if trace.public_outputs
        != (PoolV1PaymentTracePublicOutputsV1::Withdrawal {
            anchor,
            nullifier,
            change_commitment,
        })
    {
        return Err(PoolV1PaymentTraceErrorV1::PublicOutputMetadata);
    }
    Ok(())
}

pub fn build_pool_v1_private_transfer_trace_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
) -> Result<PoolV1PaymentTraceV1, PoolV1PaymentTraceErrorV1> {
    evaluate_pool_v1_private_transfer_v1(public, witness, context)
        .map_err(PoolV1PaymentTraceErrorV1::Relation)?;
    let trace = build_transfer_after_relation(public, witness)?;
    validate_transfer_after_relation(public, witness, &trace)?;
    Ok(trace)
}

pub fn build_pool_v1_withdrawal_trace_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1WithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
) -> Result<PoolV1PaymentTraceV1, PoolV1PaymentTraceErrorV1> {
    evaluate_pool_v1_withdrawal_v1(public, witness, context)
        .map_err(PoolV1PaymentTraceErrorV1::Relation)?;
    let trace = build_withdrawal_after_relation(public, witness)?;
    validate_withdrawal_after_relation(public, witness, &trace)?;
    Ok(trace)
}

pub fn validate_pool_v1_private_transfer_trace_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    trace: &PoolV1PaymentTraceV1,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    evaluate_pool_v1_private_transfer_v1(public, witness, context)
        .map_err(PoolV1PaymentTraceErrorV1::Relation)?;
    validate_transfer_after_relation(public, witness, trace)
}

pub fn validate_pool_v1_withdrawal_trace_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1WithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    trace: &PoolV1PaymentTraceV1,
) -> Result<(), PoolV1PaymentTraceErrorV1> {
    evaluate_pool_v1_withdrawal_v1(public, witness, context)
        .map_err(PoolV1PaymentTraceErrorV1::Relation)?;
    validate_withdrawal_after_relation(public, witness, trace)
}

#[cfg(test)]
mod tests {
    use super::super::payment_relation::{
        pool_v1_membership_root_v1, PoolV1MembershipWitnessV1, PoolV1PaymentRuntimeBindingV1,
    };
    use super::super::payment_semantic_registry::verify_pool_v1_payment_copy_registry_v1;
    use super::*;
    use crate::derive_owner_key;
    use aspis_core::field::{CM31, QM31};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn input(value: u32) -> PoolV1InputNoteWitnessV1 {
        PoolV1InputNoteWitnessV1 {
            nullifier_key: digest(10),
            salt: digest(100),
            value,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|level| digest(1_000 + level as u32 * 100)),
                index: 0x5_4321,
            },
        }
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn transfer_fixture() -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PrivateTransferWitnessV1,
    ) {
        let witness = PoolV1PrivateTransferWitnessV1 {
            input: input(1_000),
            recipient: output(300, 600),
            change: output(500, 400),
        };
        let asset_id = M31(77);
        let owner_key = derive_owner_key(&witness.input.nullifier_key);
        let leaf = pool_v1_note_commitment(
            &owner_key,
            witness.input.value,
            asset_id,
            &witness.input.salt,
        );
        let anchor_root = pool_v1_membership_root_v1(leaf, &witness.input.membership).unwrap();
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 42,
            anchor_root,
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
        (public, witness)
    }

    fn withdrawal_fixture() -> (PoolV1WithdrawalPublicV1, PoolV1WithdrawalWitnessV1) {
        let witness = PoolV1WithdrawalWitnessV1 {
            input: input(1_000),
            change: output(700, 750),
        };
        let asset_id = M31(77);
        let owner_key = derive_owner_key(&witness.input.nullifier_key);
        let leaf = pool_v1_note_commitment(
            &owner_key,
            witness.input.value,
            asset_id,
            &witness.input.salt,
        );
        let anchor_root = pool_v1_membership_root_v1(leaf, &witness.input.membership).unwrap();
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 42,
            anchor_root,
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            amount: 250,
            destination_token_account: [9u8; 32],
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        (public, witness)
    }

    fn transfer_context<'a>(
        public: &PoolV1PrivateTransferPublicV1,
        spent: &'a [Digest],
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: spent,
        }
    }

    fn withdrawal_context<'a>(
        public: &PoolV1WithdrawalPublicV1,
        spent: &'a [Digest],
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: spent,
        }
    }

    #[test]
    fn accepted_transfer_and_withdrawal_fill_exact_geometry_and_replay() {
        let (transfer_public, transfer_witness) = transfer_fixture();
        let transfer = build_pool_v1_private_transfer_trace_v1(
            &transfer_public,
            &transfer_witness,
            transfer_context(&transfer_public, &[]),
        )
        .unwrap();
        assert_eq!(transfer.trace.c1.len(), 16);
        assert!(transfer.trace.c1.iter().all(|column| column.len() == 1024));
        assert_eq!(POOL_V1_PAYMENT_TRACE_TWO_ROUND_TRANSITIONS, 539);
        assert_eq!(POOL_V1_TAG73_PROOF_GRAMMAR_BYTES, 30_504);
        assert_eq!(
            validate_pool_v1_private_transfer_trace_v1(
                &transfer_public,
                &transfer_witness,
                transfer_context(&transfer_public, &[]),
                &transfer,
            ),
            Ok(())
        );

        let (withdrawal_public, withdrawal_witness) = withdrawal_fixture();
        let withdrawal = build_pool_v1_withdrawal_trace_v1(
            &withdrawal_public,
            &withdrawal_witness,
            withdrawal_context(&withdrawal_public, &[]),
        )
        .unwrap();
        assert_eq!(
            validate_pool_v1_withdrawal_trace_v1(
                &withdrawal_public,
                &withdrawal_witness,
                withdrawal_context(&withdrawal_public, &[]),
                &withdrawal,
            ),
            Ok(())
        );

        // Withdrawal recipient slots and all common tail-padding slots are
        // the same exact, independently initialized zero-input permutation.
        for block in 27..=28 {
            for local_row in 0..POOL_V1_PAYMENT_TRACE_BLOCK_ROWS {
                for lane in 0..POSEIDON2_WIDTH {
                    assert_eq!(
                        withdrawal.trace.c1[lane][block * BLOCK_ROWS + local_row],
                        withdrawal.trace.c1[lane][26 * BLOCK_ROWS + local_row]
                    );
                }
            }
        }
        for block in 32..POOL_V1_PAYMENT_TRACE_BLOCKS {
            for local_row in 0..POOL_V1_PAYMENT_TRACE_BLOCK_ROWS {
                for lane in 0..POSEIDON2_WIDTH {
                    assert_eq!(
                        transfer.trace.c1[lane][block * BLOCK_ROWS + local_row],
                        withdrawal.trace.c1[lane][26 * BLOCK_ROWS + local_row]
                    );
                }
            }
        }
    }

    #[test]
    fn transition_and_auxiliary_mutations_fail_closed() {
        let (public, witness) = transfer_fixture();
        let mut trace = build_pool_v1_private_transfer_trace_v1(
            &public,
            &witness,
            transfer_context(&public, &[]),
        )
        .unwrap();
        trace.trace.c1[7][10 * BLOCK_ROWS + 6] =
            trace.trace.c1[7][10 * BLOCK_ROWS + 6].add(M31::ONE);
        assert!(matches!(
            validate_pool_v1_private_transfer_trace_v1(
                &public,
                &witness,
                transfer_context(&public, &[]),
                &trace,
            ),
            Err(PoolV1PaymentTraceErrorV1::TwoRoundTransitionMismatch { .. })
        ));

        let mut trace = build_pool_v1_private_transfer_trace_v1(
            &public,
            &witness,
            transfer_context(&public, &[]),
        )
        .unwrap();
        trace.trace.c1[0][POOL_V1_PAYMENT_DIRECTION_ROW_START] =
            trace.trace.c1[0][POOL_V1_PAYMENT_DIRECTION_ROW_START].add(M31::ONE);
        assert!(matches!(
            validate_pool_v1_private_transfer_trace_v1(
                &public,
                &witness,
                transfer_context(&public, &[]),
                &trace,
            ),
            Err(PoolV1PaymentTraceErrorV1::AuxiliaryMismatch { .. })
        ));
    }

    #[test]
    fn relation_rejection_precedes_trace_construction() {
        let (public, mut witness) = transfer_fixture();
        witness.change.value -= 1;
        assert_eq!(
            build_pool_v1_private_transfer_trace_v1(
                &public,
                &witness,
                transfer_context(&public, &[]),
            ),
            Err(PoolV1PaymentTraceErrorV1::Relation(
                PoolV1PaymentRelationError::ConservationMismatch
            ))
        );

        let (public, witness) = withdrawal_fixture();
        assert_eq!(
            build_pool_v1_withdrawal_trace_v1(
                &public,
                &witness,
                withdrawal_context(&public, &[public.nullifier]),
            ),
            Err(PoolV1PaymentTraceErrorV1::Relation(
                PoolV1PaymentRelationError::NullifierAlreadySpent
            ))
        );
    }

    #[test]
    fn fixed_schedule_and_auxiliary_cells_are_pinned() {
        assert_eq!(
            pool_v1_payment_trace_block_v1(0),
            Some(PoolV1PaymentTraceBlockV1::OwnerKey)
        );
        assert_eq!(
            pool_v1_payment_trace_block_v1(23),
            Some(PoolV1PaymentTraceBlockV1::InputPath(19))
        );
        assert_eq!(
            pool_v1_payment_trace_block_v1(25),
            Some(PoolV1PaymentTraceBlockV1::Nullifier(1))
        );
        assert_eq!(
            pool_v1_payment_trace_block_v1(28),
            Some(PoolV1PaymentTraceBlockV1::RecipientNoteOrWithdrawalPadding(
                2
            ))
        );
        assert_eq!(
            pool_v1_payment_trace_block_v1(31),
            Some(PoolV1PaymentTraceBlockV1::ChangeNote(2))
        );
        assert_eq!(
            pool_v1_payment_trace_block_v1(48),
            Some(PoolV1PaymentTraceBlockV1::FixedZeroPadding(16))
        );
        assert_eq!(pool_v1_payment_trace_block_v1(49), None);

        let (public, witness) = transfer_fixture();
        let trace = build_pool_v1_private_transfer_trace_v1(
            &public,
            &witness,
            transfer_context(&public, &[]),
        )
        .unwrap();
        for level in 0..20 {
            let target = pool_v1_payment_path_aux_v1(level).unwrap().bit;
            assert_eq!(
                trace.trace.c1[usize::from(target.column)][usize::from(target.row)],
                trace.direction_bits[level]
            );
        }
        for value in 0..3 {
            for bit in 0..30 {
                let target = pool_v1_payment_value_aux_v1(value).unwrap().bits[bit];
                assert_eq!(
                    trace.trace.c1[usize::from(target.column)][usize::from(target.row)],
                    trace.value_bits[value][bit]
                );
            }
        }
        for row in POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS..POOL_V1_PAYMENT_TRACE_ROWS {
            for column in 0..POSEIDON2_WIDTH {
                if !pool_v1_payment_aux_cell_is_used_v1(row, column) {
                    assert_eq!(trace.trace.c1[column][row], M31::ZERO);
                }
            }
        }
    }

    #[test]
    fn honest_routed_transfer_and_withdrawal_copy_registries_balance() {
        let lambda = QM31 {
            c0: CM31::new(M31(123), M31(456)),
            c1: CM31::new(M31(789), M31(1_011)),
        };
        let chi = QM31 {
            c0: CM31::new(M31(1_213), M31(1_415)),
            c1: CM31::new(M31(1_617), M31(1_819)),
        };

        let (public, witness) = transfer_fixture();
        let transfer = build_pool_v1_private_transfer_trace_v1(
            &public,
            &witness,
            transfer_context(&public, &[]),
        )
        .unwrap();
        verify_pool_v1_payment_copy_registry_v1(
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
            &transfer.trace,
            lambda,
            chi,
        )
        .unwrap();

        let (public, witness) = withdrawal_fixture();
        let withdrawal =
            build_pool_v1_withdrawal_trace_v1(&public, &witness, withdrawal_context(&public, &[]))
                .unwrap();
        verify_pool_v1_payment_copy_registry_v1(
            PoolV1PaymentTraceVariantV1::Withdrawal,
            &withdrawal.trace,
            lambda,
            chi,
        )
        .unwrap();
    }
}
