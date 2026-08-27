//! Literal two-bank trace compiler for the conservative staged pair profile.
//!
//! Rows `0..544` and `864..976` are first compiled into the stable buffer;
//! rows `544..864` are compiled into a separate checked append buffer. The
//! buffers are overlaid into the same sixteen semantic C1 columns before the
//! C1 root is committed. Transcript, PCS and terminal integration live in the
//! prover.

use alloc::{vec, vec::Vec};

use aspis_core::field::{M31, P, QM31};

use crate::{
    logup::{
        build_copy_logup_helper, compress_tagged_tuple, verify_copy_logup_constraints, CopyLogUpRow,
    },
    poseidon2::{
        evaluate_trace_round_pair, hash_fields_with_trace, permute_optimized_with_trace, Digest,
        DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_ROUNDS, POSEIDON2_WIDTH, RATE,
    },
    spend::{DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY},
    state_only_trace::{
        StateOnlyTraceFoundation, STATE_ONLY_ABSORPTION_ROW_IN_BLOCK, STATE_ONLY_FINAL_ROW_IN_BLOCK,
    },
    trace_v4::TraceCell,
    VALUE_LIMIT,
};

use super::{
    incremental_merkle::{IncrementalMerkleTreeV1, PoolV1TreeError},
    pair_terminal::PoolV1PairVerifiedAfterstateV1,
    pair_tree_hiding::{
        build_pool_v1_pair_copy_row_schedule_v1, PoolV1PairCopyRowLinkKindV1,
        POOL_V1_PAIR_COPY_ROW_LINKS_V1,
    },
    pair_tree_profile::{
        pool_v1_pair_path_base_row_v1, PoolV1PairLeafErrorV1, PoolV1PairLeafWitnessV1,
        PoolV1PairLiveSnapshotV1, POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
        POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN, POOL_V1_PAIR_LATE_APPEND_POSEIDON_BLOCKS,
        POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START, POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW, POOL_V1_PAIR_PRIVATE_DIRECTIONS,
        POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS, POOL_V1_PAIR_TRACE_COLUMNS, POOL_V1_PAIR_TRACE_ROWS,
        POOL_V1_PAIR_TREE_DEPTH, POOL_V1_PAIR_VALUE_AUX_ROW_START,
    },
    payment_relation::{
        validate_pool_v1_private_transfer_public_v1, validate_pool_v1_withdrawal_public_v1,
        PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1, PoolV1PaymentRelationContextV1,
        PoolV1PaymentStatementFormatError, PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
    },
    pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent,
};

pub const POOL_V1_PAIR_VALUE_BITS: usize = 30;
pub const POOL_V1_PAIR_VALUE_COUNT: usize = 3;
pub const POOL_V1_PAIR_COPY_TAG_BASE_V1: u32 = 0x4300_0000;

const _: () = assert!(POSEIDON2_WIDTH == POOL_V1_PAIR_TRACE_COLUMNS);
const _: () = assert!(POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS * 16 == 544);
const _: () = assert!(POOL_V1_PAIR_LATE_APPEND_POSEIDON_BLOCKS * 16 == 320);
const _: () = assert!(STATE_ONLY_FINAL_ROW_IN_BLOCK == 11);
const _: () = assert!(STATE_ONLY_ABSORPTION_ROW_IN_BLOCK == 12);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairTraceVariantV1 {
    PrivateTransfer,
    Withdrawal,
}

/// Input-note witness for a depth-21 pair tree. `membership` is the twenty
/// upper pair-tree levels; `selected_second` is the private bottom direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairInputNoteWitnessV1 {
    pub nullifier_key: Digest,
    pub salt: Digest,
    pub value: u32,
    pub pair_leaf: PoolV1PairLeafWitnessV1,
    pub selected_second: bool,
    pub membership: PoolV1MembershipWitnessV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairPrivateTransferWitnessV1 {
    pub input: PoolV1PairInputNoteWitnessV1,
    pub recipient: PoolV1OutputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairWithdrawalWitnessV1 {
    pub input: PoolV1PairInputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairTracePublicOutputsV1 {
    PrivateTransfer {
        anchor: Digest,
        nullifier: Digest,
        recipient_commitment: Digest,
        change_commitment: Digest,
        output_pair: Digest,
    },
    Withdrawal {
        anchor: Digest,
        nullifier: Digest,
        change_commitment: Digest,
        output_pair: Digest,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairTraceV1 {
    /// Pre-snapshot bank committed as the 16 semantic C1 columns.
    pub stable: StateOnlyTraceFoundation,
    /// Checked append buffer. Only rows 544..864 may be nonzero; the merger
    /// overlays them into the semantic C1 columns before commitment.
    pub late: [Vec<M31>; POOL_V1_PAIR_TRACE_COLUMNS],
    pub variant: PoolV1PairTraceVariantV1,
    pub private_directions: [M31; POOL_V1_PAIR_PRIVATE_DIRECTIONS],
    pub value_bits: [[M31; POOL_V1_PAIR_VALUE_BITS]; POOL_V1_PAIR_VALUE_COUNT],
    pub public_outputs: PoolV1PairTracePublicOutputsV1,
    pub afterstate: PoolV1PairVerifiedAfterstateV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairTraceErrorV1 {
    Statement(PoolV1PaymentStatementFormatError),
    PairLeaf(PoolV1PairLeafErrorV1),
    Tree(PoolV1TreeError),
    Shape,
    WrongVariant,
    RuntimeBinding,
    NullifierAlreadySpent,
    WitnessDigest,
    ValueOutOfRange,
    Conservation,
    HashSchedule,
    SelectedCommitmentMismatch,
    AnchorMismatch,
    NullifierMismatch,
    RecipientCommitmentMismatch,
    ChangeCommitmentMismatch,
    SnapshotBindingMismatch,
    BlockMismatch { block: u8, local_row: u8, lane: u8 },
    AuxiliaryMismatch { row: u16, column: u8 },
    MetadataMismatch,
    CopyLayout,
    CopyImbalance,
}

/// Merge the disjoint stable and append banks into the ordinary sixteen
/// semantic C1 columns. This check is the soundness gate for the pre-root
/// profile: a caller cannot silently overwrite a stable cell or carry a late
/// value outside rows 544..864.
pub fn merge_pool_v1_pair_trace_banks_v1(
    trace: &PoolV1PairTraceV1,
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
    let late_rows = 544..864;
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        if trace.stable.c1[column][late_rows.clone()]
            .iter()
            .any(|value| *value != M31::ZERO)
            || trace.late[column][..late_rows.start]
                .iter()
                .chain(&trace.late[column][late_rows.end..])
                .any(|value| *value != M31::ZERO)
        {
            return Err(PoolV1PairTraceErrorV1::Shape);
        }
    }
    let mut merged = trace.stable.clone();
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        merged.c1[column][late_rows.clone()]
            .copy_from_slice(&trace.late[column][late_rows.clone()]);
    }
    Ok(merged)
}

fn empty_columns() -> [Vec<M31>; POOL_V1_PAIR_TRACE_COLUMNS] {
    core::array::from_fn(|_| vec![M31::ZERO; POOL_V1_PAIR_TRACE_ROWS])
}

fn empty_stable() -> StateOnlyTraceFoundation {
    StateOnlyTraceFoundation {
        c1: empty_columns(),
    }
}

#[inline]
fn digest_canonical(value: &Digest) -> bool {
    value.iter().all(|limb| limb.0 < P)
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

fn note_input(note: &PoolV1OutputNoteWitnessV1, asset_id: M31) -> [M31; 18] {
    let mut input = [M31::ZERO; 18];
    input[..8].copy_from_slice(&note.owner_key);
    input[8] = M31(note.value);
    input[9] = asset_id;
    input[10..].copy_from_slice(&note.salt);
    input
}

fn input_note_input(input: &PoolV1PairInputNoteWitnessV1, owner: Digest, asset: M31) -> [M31; 18] {
    note_input(
        &PoolV1OutputNoteWitnessV1 {
            owner_key: owner,
            salt: input.salt,
            value: input.value,
        },
        asset,
    )
}

fn nullifier_input(input: &PoolV1PairInputNoteWitnessV1) -> [M31; 16] {
    let mut fields = [M31::ZERO; 16];
    fields[..8].copy_from_slice(&input.nullifier_key);
    fields[8..].copy_from_slice(&input.salt);
    fields
}

fn value_bits(value: u32) -> [M31; POOL_V1_PAIR_VALUE_BITS] {
    core::array::from_fn(|bit| M31((value >> bit) & 1))
}

fn directions(input: &PoolV1PairInputNoteWitnessV1) -> [M31; POOL_V1_PAIR_PRIVATE_DIRECTIONS] {
    core::array::from_fn(|level| {
        if level == 0 {
            M31(u32::from(input.selected_second))
        } else {
            M31((input.membership.index >> (level - 1)) & 1)
        }
    })
}

fn write_permutation(
    columns: &mut [Vec<M31>; 16],
    block: usize,
    pre_absorb: [M31; 16],
    absorption: [M31; 8],
) -> Result<Digest, PoolV1PairTraceErrorV1> {
    if block >= 54 {
        return Err(PoolV1PairTraceErrorV1::HashSchedule);
    }
    let base = block * 16;
    for lane in 0..16 {
        columns[lane][base] = pre_absorb[lane];
    }
    for lane in 0..8 {
        columns[lane][base + 12] = absorption[lane];
    }
    let mut state = pre_absorb;
    for lane in 0..8 {
        state[lane] = state[lane].add(absorption[lane]);
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

fn write_sponge(
    columns: &mut [Vec<M31>; 16],
    block_start: usize,
    domain: M31,
    input: &[M31],
) -> Result<Digest, PoolV1PairTraceErrorV1> {
    if input.is_empty() || input.len().div_ceil(RATE) > 3 {
        return Err(PoolV1PairTraceErrorV1::HashSchedule);
    }
    let mut counts = [0u8; 3];
    let mut malformed = false;
    let digest = hash_fields_with_trace(domain, input, |permutation, transition| {
        if permutation >= counts.len() {
            malformed = true;
            return;
        }
        counts[permutation] = counts[permutation].saturating_add(1);
        let block = block_start + permutation;
        let base = block * 16;
        let start = permutation * RATE;
        let chunk = &input[start..core::cmp::min(start + RATE, input.len())];
        if transition.round == 0 {
            for lane in 0..16 {
                let absorbed = if lane < chunk.len() {
                    chunk[lane]
                } else {
                    M31::ZERO
                };
                columns[lane][base] = transition.input[lane].sub(absorbed);
            }
            for (lane, value) in chunk.iter().copied().enumerate() {
                columns[lane][base + 12] = value;
            }
        }
        if transition.round & 1 == 1 {
            let row = base + usize::from(transition.round) / 2 + 1;
            for lane in 0..16 {
                columns[lane][row] = transition.output[lane];
            }
        }
    });
    let permutations = input.len().div_ceil(RATE);
    if malformed
        || counts[..permutations]
            .iter()
            .any(|count| usize::from(*count) != POSEIDON2_ROUNDS)
    {
        return Err(PoolV1PairTraceErrorV1::HashSchedule);
    }
    Ok(digest)
}

fn write_node(
    columns: &mut [Vec<M31>; 16],
    block: usize,
    left: Digest,
    right: Digest,
) -> Result<Digest, PoolV1PairTraceErrorV1> {
    let mut pre = [M31::ZERO; 16];
    pre[8..].copy_from_slice(&right);
    pre[15] = pre[15].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    write_permutation(columns, block, pre, left)
}

fn ordered(current: Digest, sibling: Digest, bit: M31) -> (Digest, Digest) {
    if bit == M31::ZERO {
        (current, sibling)
    } else {
        (sibling, current)
    }
}

#[inline]
fn set(columns: &mut [Vec<M31>; 16], row: usize, column: usize, value: M31) {
    columns[column][row] = value;
}

fn write_path_aux(
    columns: &mut [Vec<M31>; 16],
    level: usize,
    bit: M31,
    current: Digest,
    sibling: Digest,
    left: Digest,
    right: Digest,
) -> Result<(), PoolV1PairTraceErrorV1> {
    let base = pool_v1_pair_path_base_row_v1(level).ok_or(PoolV1PairTraceErrorV1::HashSchedule)?;
    set(columns, base, 0, bit);
    for lane in 0..8 {
        set(columns, base, 1 + lane, current[lane]);
        set(columns, base + 1, lane, left[lane]);
        set(columns, base + 1, 8 + lane, right[lane]);
        set(columns, base ^ 12, lane, sibling[lane]);
    }
    Ok(())
}

fn write_value_aux(columns: &mut [Vec<M31>; 16], values: [u32; 3]) {
    for (value, raw) in values.into_iter().enumerate() {
        let base = POOL_V1_PAIR_VALUE_AUX_ROW_START + 2 * value;
        for bit in 0..30 {
            let row = if bit < 10 {
                base
            } else if bit < 20 {
                base + 1
            } else {
                base ^ 12
            };
            set(columns, row, bit % 10, M31((raw >> bit) & 1));
        }
        set(columns, base, 10, M31(raw));
    }
    let partial = M31(values[0]).sub(M31(values[1]));
    set(
        columns,
        POOL_V1_PAIR_VALUE_AUX_ROW_START + 6,
        0,
        M31(values[0]),
    );
    set(
        columns,
        POOL_V1_PAIR_VALUE_AUX_ROW_START + 6,
        1,
        M31(values[1]),
    );
    set(columns, POOL_V1_PAIR_VALUE_AUX_ROW_START + 6, 2, partial);
    set(columns, POOL_V1_PAIR_VALUE_AUX_ROW_START + 7, 0, partial);
    set(
        columns,
        POOL_V1_PAIR_VALUE_AUX_ROW_START + 7,
        1,
        M31(values[2]),
    );
}

fn write_occupancy(
    columns: &mut [Vec<M31>; 16],
    row: usize,
    witness: PoolV1PairLeafWitnessV1,
    selected: Option<bool>,
) {
    set(columns, row, 0, witness.second_occupied);
    set(
        columns,
        row,
        POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN,
        witness.second_occupancy_inverse,
    );
    for lane in 0..8 {
        set(
            columns,
            row,
            POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START + lane,
            witness.second_commitment[lane],
        );
    }
    if let Some(selected) = selected {
        set(
            columns,
            row,
            POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN,
            M31(u32::from(selected)),
        );
    }
}

fn validate_common(
    public_pool: [u8; 32],
    public_domain: [u8; 32],
    anchor_sequence: u64,
    anchor: Digest,
    nullifier: Digest,
    asset: M31,
    input: &PoolV1PairInputNoteWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
) -> Result<(), PoolV1PairTraceErrorV1> {
    if context.runtime_binding.pool != public_pool
        || context.runtime_binding.deployment_domain != public_domain
        || context.runtime_binding.anchor_sequence != anchor_sequence
        || context.runtime_binding.anchor_root != anchor
        || context.runtime_binding.asset_id != asset
    {
        return Err(PoolV1PairTraceErrorV1::RuntimeBinding);
    }
    if context.spent_nullifiers.contains(&nullifier) {
        return Err(PoolV1PairTraceErrorV1::NullifierAlreadySpent);
    }
    if !digest_canonical(&input.nullifier_key)
        || !digest_canonical(&input.salt)
        || input
            .membership
            .siblings
            .iter()
            .any(|node| !digest_canonical(node))
    {
        return Err(PoolV1PairTraceErrorV1::WitnessDigest);
    }
    if input.value == 0 || input.value >= VALUE_LIMIT || input.membership.index >= (1 << 20) {
        return Err(PoolV1PairTraceErrorV1::ValueOutOfRange);
    }
    input
        .pair_leaf
        .require_selected_spendable(input.selected_second)
        .map_err(PoolV1PairTraceErrorV1::PairLeaf)
}

fn build_common_stable(
    stable: &mut [Vec<M31>; 16],
    input: &PoolV1PairInputNoteWitnessV1,
    asset: M31,
) -> Result<(Digest, Digest), PoolV1PairTraceErrorV1> {
    let owner = write_sponge(stable, 0, DOMAIN_OWNER_KEY, &input.nullifier_key)?;
    let input_leaf = write_sponge(
        stable,
        1,
        DOMAIN_NOTE,
        &input_note_input(input, owner, asset),
    )?;
    if input.pair_leaf.selected_commitment(input.selected_second) != &input_leaf {
        return Err(PoolV1PairTraceErrorV1::SelectedCommitmentMismatch);
    }
    let bits = directions(input);
    let other = if input.selected_second {
        input.pair_leaf.first_commitment
    } else {
        input.pair_leaf.second_commitment
    };
    let (left, right) = ordered(input_leaf, other, bits[0]);
    write_path_aux(stable, 0, bits[0], input_leaf, other, left, right)?;
    let mut current = write_node(stable, 4, left, right)?;
    if current
        != input
            .pair_leaf
            .leaf_digest()
            .map_err(PoolV1PairTraceErrorV1::PairLeaf)?
    {
        return Err(PoolV1PairTraceErrorV1::SelectedCommitmentMismatch);
    }
    for level in 0..20 {
        let sibling = input.membership.siblings[level];
        let (left, right) = ordered(current, sibling, bits[level + 1]);
        write_path_aux(
            stable,
            level + 1,
            bits[level + 1],
            current,
            sibling,
            left,
            right,
        )?;
        current = write_node(stable, 5 + level, left, right)?;
    }
    let nullifier = write_sponge(stable, 25, DOMAIN_NULLIFIER, &nullifier_input(input))?;
    Ok((current, nullifier))
}

fn build_late_append(
    late: &mut [Vec<M31>; 16],
    snapshot: PoolV1PairLiveSnapshotV1,
    output_pair: Digest,
) -> Result<PoolV1PairVerifiedAfterstateV1, PoolV1PairTraceErrorV1> {
    if snapshot.sequence != snapshot.next_pair_index {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    let empty = pair_empty_roots();
    let source = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
        snapshot.next_pair_index,
        snapshot.current_root,
        snapshot.frontier,
        &empty,
    )
    .map_err(PoolV1PairTraceErrorV1::Tree)?;
    let (next, _) = source
        .append_one_with_empty_roots(output_pair, &empty)
        .map_err(PoolV1PairTraceErrorV1::Tree)?;
    let mut current = output_pair;
    for level in 0..20 {
        let bit = M31(((snapshot.next_pair_index >> level) & 1) as u32);
        let sibling = if bit == M31::ZERO {
            empty[level]
        } else {
            snapshot.frontier[level]
        };
        let (left, right) = ordered(current, sibling, bit);
        current = write_node(late, 34 + level, left, right)?;
    }
    if current != next.root {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    Ok(PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: next.next_leaf_index,
        next_root: next.root,
        next_frontier: next.frontier,
    })
}

fn build_transfer_inner(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairPrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairTraceV1, PoolV1PairTraceErrorV1> {
    validate_pool_v1_private_transfer_public_v1(public)
        .map_err(PoolV1PairTraceErrorV1::Statement)?;
    validate_common(
        public.pool,
        public.deployment_domain,
        public.anchor_sequence,
        public.anchor_root,
        public.nullifier,
        public.asset_id,
        &witness.input,
        context,
    )?;
    if snapshot.pool != public.pool || snapshot.deployment_domain != public.deployment_domain {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    if witness.recipient.value == 0
        || witness.change.value == 0
        || witness.recipient.value >= VALUE_LIMIT
        || witness.change.value >= VALUE_LIMIT
        || witness.recipient.value.checked_add(witness.change.value) != Some(witness.input.value)
    {
        return Err(PoolV1PairTraceErrorV1::Conservation);
    }
    let mut stable = empty_stable();
    let (anchor, nullifier) = build_common_stable(&mut stable.c1, &witness.input, public.asset_id)?;
    if anchor != public.anchor_root {
        return Err(PoolV1PairTraceErrorV1::AnchorMismatch);
    }
    if nullifier != public.nullifier
        || nullifier != pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt)
    {
        return Err(PoolV1PairTraceErrorV1::NullifierMismatch);
    }
    let recipient = write_sponge(
        &mut stable.c1,
        27,
        DOMAIN_NOTE,
        &note_input(&witness.recipient, public.asset_id),
    )?;
    let change = write_sponge(
        &mut stable.c1,
        30,
        DOMAIN_NOTE,
        &note_input(&witness.change, public.asset_id),
    )?;
    if recipient != public.recipient_commitment {
        return Err(PoolV1PairTraceErrorV1::RecipientCommitmentMismatch);
    }
    if change != public.change_commitment {
        return Err(PoolV1PairTraceErrorV1::ChangeCommitmentMismatch);
    }
    let output_witness = PoolV1PairLeafWitnessV1::two_outputs(recipient, change)
        .map_err(PoolV1PairTraceErrorV1::PairLeaf)?;
    let output_pair = write_node(&mut stable.c1, 33, recipient, change)?;
    write_value_aux(
        &mut stable.c1,
        [
            witness.input.value,
            witness.recipient.value,
            witness.change.value,
        ],
    );
    write_occupancy(
        &mut stable.c1,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
        witness.input.pair_leaf,
        Some(witness.input.selected_second),
    );
    write_occupancy(
        &mut stable.c1,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
        output_witness,
        None,
    );
    let mut late = empty_columns();
    let afterstate = build_late_append(&mut late, snapshot, output_pair)?;
    Ok(PoolV1PairTraceV1 {
        stable,
        late,
        variant: PoolV1PairTraceVariantV1::PrivateTransfer,
        private_directions: directions(&witness.input),
        value_bits: [
            value_bits(witness.input.value),
            value_bits(witness.recipient.value),
            value_bits(witness.change.value),
        ],
        public_outputs: PoolV1PairTracePublicOutputsV1::PrivateTransfer {
            anchor,
            nullifier,
            recipient_commitment: recipient,
            change_commitment: change,
            output_pair,
        },
        afterstate,
    })
}

fn build_withdrawal_inner(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairWithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairTraceV1, PoolV1PairTraceErrorV1> {
    validate_pool_v1_withdrawal_public_v1(public).map_err(PoolV1PairTraceErrorV1::Statement)?;
    validate_common(
        public.pool,
        public.deployment_domain,
        public.anchor_sequence,
        public.anchor_root,
        public.nullifier,
        public.asset_id,
        &witness.input,
        context,
    )?;
    if snapshot.pool != public.pool || snapshot.deployment_domain != public.deployment_domain {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    if witness.change.value == 0
        || witness.change.value >= VALUE_LIMIT
        || public.amount.checked_add(witness.change.value) != Some(witness.input.value)
    {
        return Err(PoolV1PairTraceErrorV1::Conservation);
    }
    let mut stable = empty_stable();
    let (anchor, nullifier) = build_common_stable(&mut stable.c1, &witness.input, public.asset_id)?;
    if anchor != public.anchor_root {
        return Err(PoolV1PairTraceErrorV1::AnchorMismatch);
    }
    if nullifier != public.nullifier
        || nullifier != pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt)
    {
        return Err(PoolV1PairTraceErrorV1::NullifierMismatch);
    }
    // Blocks 27..29 are the canonical zero-input permutation for withdrawal.
    for block in 27..=29 {
        let _ = write_permutation(&mut stable.c1, block, [M31::ZERO; 16], [M31::ZERO; 8])?;
    }
    let change = write_sponge(
        &mut stable.c1,
        30,
        DOMAIN_NOTE,
        &note_input(&witness.change, public.asset_id),
    )?;
    if change != public.change_commitment {
        return Err(PoolV1PairTraceErrorV1::ChangeCommitmentMismatch);
    }
    let output_witness =
        PoolV1PairLeafWitnessV1::single_output(change).map_err(PoolV1PairTraceErrorV1::PairLeaf)?;
    let output_pair = write_node(&mut stable.c1, 33, change, [M31::ZERO; 8])?;
    write_value_aux(
        &mut stable.c1,
        [witness.input.value, public.amount, witness.change.value],
    );
    write_occupancy(
        &mut stable.c1,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
        witness.input.pair_leaf,
        Some(witness.input.selected_second),
    );
    write_occupancy(
        &mut stable.c1,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
        output_witness,
        None,
    );
    let mut late = empty_columns();
    let afterstate = build_late_append(&mut late, snapshot, output_pair)?;
    Ok(PoolV1PairTraceV1 {
        stable,
        late,
        variant: PoolV1PairTraceVariantV1::Withdrawal,
        private_directions: directions(&witness.input),
        value_bits: [
            value_bits(witness.input.value),
            value_bits(public.amount),
            value_bits(witness.change.value),
        ],
        public_outputs: PoolV1PairTracePublicOutputsV1::Withdrawal {
            anchor,
            nullifier,
            change_commitment: change,
            output_pair,
        },
        afterstate,
    })
}

pub fn build_pool_v1_pair_private_transfer_trace_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairPrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairTraceV1, PoolV1PairTraceErrorV1> {
    let trace = build_transfer_inner(public, witness, context, snapshot)?;
    validate_pool_v1_pair_private_transfer_trace_v1(public, witness, context, snapshot, &trace)?;
    Ok(trace)
}

pub fn build_pool_v1_pair_withdrawal_trace_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairWithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairTraceV1, PoolV1PairTraceErrorV1> {
    let trace = build_withdrawal_inner(public, witness, context, snapshot)?;
    validate_pool_v1_pair_withdrawal_trace_v1(public, witness, context, snapshot, &trace)?;
    Ok(trace)
}

fn compare_trace(
    actual: &PoolV1PairTraceV1,
    expected: &PoolV1PairTraceV1,
) -> Result<(), PoolV1PairTraceErrorV1> {
    if actual.stable.c1.len() != 16
        || actual.stable.c1.iter().any(|c| c.len() != 1024)
        || actual.late.iter().any(|c| c.len() != 1024)
    {
        return Err(PoolV1PairTraceErrorV1::Shape);
    }
    for (bank_actual, bank_expected) in [
        (&actual.stable.c1, &expected.stable.c1),
        (&actual.late, &expected.late),
    ] {
        for column in 0..16 {
            for row in 0..1024 {
                if bank_actual[column][row] != bank_expected[column][row] {
                    return Err(PoolV1PairTraceErrorV1::BlockMismatch {
                        block: (row / 16) as u8,
                        local_row: (row % 16) as u8,
                        lane: column as u8,
                    });
                }
            }
        }
    }
    validate_physical_poseidon_rows(actual)?;
    if actual.variant != expected.variant
        || actual.private_directions != expected.private_directions
        || actual.value_bits != expected.value_bits
        || actual.public_outputs != expected.public_outputs
        || actual.afterstate != expected.afterstate
    {
        return Err(PoolV1PairTraceErrorV1::MetadataMismatch);
    }
    Ok(())
}

/// Replay every allocated permutation from its committed row-0/row-12
/// inputs using the round equations, independently of the trace builder's
/// `permute_optimized_with_trace` callback.
fn validate_physical_poseidon_rows(
    trace: &PoolV1PairTraceV1,
) -> Result<(), PoolV1PairTraceErrorV1> {
    for block in 0..54 {
        let columns = if block < POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS {
            &trace.stable.c1
        } else {
            &trace.late
        };
        let base = block * 16;
        let mut state = core::array::from_fn(|lane| columns[lane][base]);
        for lane in 0..RATE {
            state[lane] = state[lane].add(columns[lane][base + 12]);
        }
        for local_row in 0..11 {
            let (_, second) = evaluate_trace_round_pair(state, local_row)
                .ok_or(PoolV1PairTraceErrorV1::HashSchedule)?;
            for lane in 0..16 {
                if columns[lane][base + local_row + 1] != second[lane] {
                    return Err(PoolV1PairTraceErrorV1::BlockMismatch {
                        block: block as u8,
                        local_row: (local_row + 1) as u8,
                        lane: lane as u8,
                    });
                }
            }
            state = second;
        }
        for local_row in 13..16 {
            for lane in 0..16 {
                if columns[lane][base + local_row] != M31::ZERO {
                    return Err(PoolV1PairTraceErrorV1::BlockMismatch {
                        block: block as u8,
                        local_row: local_row as u8,
                        lane: lane as u8,
                    });
                }
            }
        }
    }
    Ok(())
}

pub fn validate_pool_v1_pair_private_transfer_trace_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairPrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
    trace: &PoolV1PairTraceV1,
) -> Result<(), PoolV1PairTraceErrorV1> {
    if trace.variant != PoolV1PairTraceVariantV1::PrivateTransfer {
        return Err(PoolV1PairTraceErrorV1::WrongVariant);
    }
    let expected = build_transfer_inner(public, witness, context, snapshot)?;
    compare_trace(trace, &expected)
}

pub fn validate_pool_v1_pair_withdrawal_trace_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairWithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
    trace: &PoolV1PairTraceV1,
) -> Result<(), PoolV1PairTraceErrorV1> {
    if trace.variant != PoolV1PairTraceVariantV1::Withdrawal {
        return Err(PoolV1PairTraceErrorV1::WrongVariant);
    }
    let expected = build_withdrawal_inner(public, witness, context, snapshot)?;
    compare_trace(trace, &expected)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairTraceBankV1 {
    Stable,
    Late,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairTraceCellV1 {
    pub bank: PoolV1PairTraceBankV1,
    pub cell: TraceCell,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairCopyWeightV1 {
    One,
    AppendCurrentLeft { level: u8 },
    AppendCurrentRight { level: u8 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairTupleLimbV1 {
    Zero,
    Cell {
        source: PoolV1PairTraceCellV1,
        offset: M31,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairCopyTupleV1 {
    pub row: u16,
    pub limbs: [PoolV1PairTupleLimbV1; 16],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairCopyLinkV1 {
    pub id: u16,
    pub tag: M31,
    pub kind: PoolV1PairCopyRowLinkKindV1,
    pub weight: PoolV1PairCopyWeightV1,
    pub producer: PoolV1PairCopyTupleV1,
    pub consumer: PoolV1PairCopyTupleV1,
}

#[inline]
fn bank_for_row(row: usize) -> PoolV1PairTraceBankV1 {
    if (544..864).contains(&row) {
        PoolV1PairTraceBankV1::Late
    } else {
        PoolV1PairTraceBankV1::Stable
    }
}

fn tuple_cells(row: usize, start: usize, count: usize, tweak_right: bool) -> PoolV1PairCopyTupleV1 {
    let bank = bank_for_row(row);
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

fn aux_tuple(row: usize, start: usize, count: usize) -> PoolV1PairCopyTupleV1 {
    tuple_cells(row, start, count, false)
}

pub fn build_pool_v1_pair_copy_registry_v1(
) -> Result<Vec<PoolV1PairCopyLinkV1>, PoolV1PairTraceErrorV1> {
    let rows = build_pool_v1_pair_copy_row_schedule_v1()
        .map_err(|_| PoolV1PairTraceErrorV1::CopyLayout)?;
    let mut output = Vec::with_capacity(rows.len());
    for scheduled in rows {
        let (producer, consumer, weight) = match scheduled.kind {
            PoolV1PairCopyRowLinkKindV1::SpongeCarry { .. } => (
                tuple_cells(scheduled.producer_row as usize, 0, 16, false),
                tuple_cells(scheduled.consumer_row as usize, 0, 16, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::OwnerOutput => (
                tuple_cells(11, 0, 8, false),
                tuple_cells(28, 0, 8, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::NullifierKey => (
                tuple_cells(12, 0, 8, false),
                tuple_cells(412, 0, 8, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSaltHead => (
                tuple_cells(44, 2, 6, false),
                tuple_cells(428, 0, 6, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSaltTail => (
                tuple_cells(60, 0, 2, false),
                tuple_cells(428, 6, 2, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. } => (
                tuple_cells(scheduled.producer_row as usize, 0, 8, false),
                aux_tuple(scheduled.consumer_row as usize, 1, 8),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. } => (
                aux_tuple(scheduled.producer_row as usize, 0, 8),
                tuple_cells(scheduled.consumer_row as usize, 0, 8, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. } => (
                aux_tuple(scheduled.producer_row as usize, 8, 8),
                tuple_cells(scheduled.consumer_row as usize, 8, 8, true),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ValueSource { .. } => (
                tuple_cells(scheduled.producer_row as usize, 0, 1, false),
                aux_tuple(scheduled.consumer_row as usize, 10, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationInput => (
                aux_tuple(960, 10, 1),
                aux_tuple(966, 0, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationRecipient => (
                aux_tuple(962, 10, 1),
                aux_tuple(966, 1, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationChange => (
                aux_tuple(964, 10, 1),
                aux_tuple(967, 1, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationPartial => (
                aux_tuple(966, 2, 1),
                aux_tuple(967, 0, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSecondCommitment => (
                tuple_cells(64, 8, 8, true),
                aux_tuple(969, 2, 8),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSelectedSide => (
                aux_tuple(scheduled.producer_row as usize, 0, 1),
                aux_tuple(969, 10, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::OutputSecondCommitment => (
                tuple_cells(523, 0, 8, false),
                aux_tuple(970, 2, 8),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::OutputPairFirst => (
                tuple_cells(475, 0, 8, false),
                tuple_cells(540, 0, 8, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::OutputPairSecond => (
                aux_tuple(970, 2, 8),
                tuple_cells(528, 8, 8, true),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::AppendCurrentLeft { level } => (
                tuple_cells(scheduled.producer_row as usize, 0, 8, false),
                tuple_cells(scheduled.consumer_row as usize, 0, 8, false),
                PoolV1PairCopyWeightV1::AppendCurrentLeft { level },
            ),
            PoolV1PairCopyRowLinkKindV1::AppendCurrentRight { level } => (
                tuple_cells(scheduled.producer_row as usize, 0, 8, false),
                tuple_cells(scheduled.consumer_row as usize, 8, 8, true),
                PoolV1PairCopyWeightV1::AppendCurrentRight { level },
            ),
        };
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
    if output.len() != POOL_V1_PAIR_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairTraceErrorV1::CopyLayout);
    }
    Ok(output)
}

fn tuple_value(trace: &PoolV1PairTraceV1, tuple: PoolV1PairCopyTupleV1) -> [M31; 16] {
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

fn copy_weight(weight: PoolV1PairCopyWeightV1, append_index: u64) -> M31 {
    match weight {
        PoolV1PairCopyWeightV1::One => M31::ONE,
        PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => {
            M31(1 - ((append_index >> level) & 1) as u32)
        }
        PoolV1PairCopyWeightV1::AppendCurrentRight { level } => {
            M31(((append_index >> level) & 1) as u32)
        }
    }
}

pub fn pool_v1_pair_copy_rows_v1(
    trace: &PoolV1PairTraceV1,
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
    for link in build_pool_v1_pair_copy_registry_v1()? {
        let weight = copy_weight(link.weight, append_index);
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

pub fn verify_pool_v1_pair_copy_registry_v1(
    trace: &PoolV1PairTraceV1,
    append_index: u64,
    lambda: QM31,
    chi: QM31,
) -> Result<(), PoolV1PairTraceErrorV1> {
    let rows = pool_v1_pair_copy_rows_v1(trace, append_index, lambda)?;
    let helper =
        build_copy_logup_helper(&rows, chi).map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)?;
    verify_copy_logup_constraints(&rows, &helper, chi)
        .map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derive_owner_key;
    use aspis_core::field::CM31;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + lane as u32 + 1))
    }

    fn fixture() -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PairPrivateTransferWitnessV1,
        PoolV1PaymentRelationContextV1<'static>,
        PoolV1PairLiveSnapshotV1,
    ) {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset = M31(77);
        let owner = derive_owner_key(&nullifier_key);
        let input_commitment = pool_v1_note_commitment(&owner, 1_000, asset, &salt);
        let pair_leaf =
            PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900)).unwrap();
        let membership = PoolV1MembershipWitnessV1 {
            siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
            index: 0x54321,
        };
        let mut anchor = pair_leaf.leaf_digest().unwrap();
        for level in 0..20 {
            let bit = M31((membership.index >> level) & 1);
            let (left, right) = ordered(anchor, membership.siblings[level], bit);
            anchor = pool_v1_tree_parent(&left, &right);
        }
        let recipient = PoolV1OutputNoteWitnessV1 {
            owner_key: digest(300),
            salt: digest(400),
            value: 600,
        };
        let change = PoolV1OutputNoteWitnessV1 {
            owner_key: digest(500),
            salt: digest(600),
            value: 400,
        };
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&nullifier_key, &salt),
            asset_id: asset,
            recipient_commitment: pool_v1_note_commitment(
                &recipient.owner_key,
                recipient.value,
                asset,
                &recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &change.owner_key,
                change.value,
                asset,
                &change.salt,
            ),
        };
        let witness = PoolV1PairPrivateTransferWitnessV1 {
            input: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt,
                value: 1_000,
                pair_leaf,
                selected_second: false,
                membership,
            },
            recipient,
            change,
        };
        let context = PoolV1PaymentRelationContextV1 {
            runtime_binding: super::super::payment_relation::PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: &[],
        };
        let snapshot = snapshot_at(public.pool, public.deployment_domain, 0);
        (public, witness, context, snapshot)
    }

    fn snapshot_at(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        index: u64,
    ) -> PoolV1PairLiveSnapshotV1 {
        let empty = pair_empty_roots();
        let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            empty[20],
            core::array::from_fn(|level| empty[level]),
            &empty,
        )
        .unwrap();
        for leaf in 0..index {
            tree = tree
                .append_one_with_empty_roots(digest(10_000 + 32 * leaf as u32), &empty)
                .unwrap()
                .0;
        }
        PoolV1PairLiveSnapshotV1 {
            pool,
            deployment_domain,
            sequence: index,
            next_pair_index: index,
            current_root: tree.root,
            frontier: tree.frontier,
        }
    }

    #[test]
    fn honest_pair_trace_has_exact_two_bank_geometry_and_copy_balance() {
        let (public, witness, context, snapshot) = fixture();
        let trace =
            build_pool_v1_pair_private_transfer_trace_v1(&public, &witness, context, snapshot)
                .unwrap();
        assert!(trace
            .stable
            .c1
            .iter()
            .all(|column| column[544..864].iter().all(|value| *value == M31::ZERO)));
        assert!(trace.late.iter().all(|column| column[..544]
            .iter()
            .chain(&column[864..])
            .all(|value| *value == M31::ZERO)));
        assert_eq!(trace.afterstate.next_pair_index, 1);
        assert_eq!(build_pool_v1_pair_copy_registry_v1().unwrap().len(), 126);
        verify_pool_v1_pair_copy_registry_v1(
            &trace,
            snapshot.next_pair_index,
            QM31::from_cm31(CM31::from_m31(M31(19))),
            QM31::from_cm31(CM31::from_m31(M31(23))),
        )
        .unwrap();
    }

    #[test]
    fn checked_merge_overlays_only_the_disjoint_late_rows() {
        let (public, witness, context, snapshot) = fixture();
        let trace =
            build_pool_v1_pair_private_transfer_trace_v1(&public, &witness, context, snapshot)
                .unwrap();
        let merged = merge_pool_v1_pair_trace_banks_v1(&trace).unwrap();
        for column in 0..16 {
            assert_eq!(&merged.c1[column][..544], &trace.stable.c1[column][..544]);
            assert_eq!(&merged.c1[column][544..864], &trace.late[column][544..864]);
            assert_eq!(&merged.c1[column][864..], &trace.stable.c1[column][864..]);
        }

        let mut stable_overlap = trace.clone();
        stable_overlap.stable.c1[0][544] = M31::ONE;
        assert_eq!(
            merge_pool_v1_pair_trace_banks_v1(&stable_overlap).err(),
            Some(PoolV1PairTraceErrorV1::Shape)
        );
        let mut late_escape = trace;
        late_escape.late[0][543] = M31::ONE;
        assert_eq!(
            merge_pool_v1_pair_trace_banks_v1(&late_escape).err(),
            Some(PoolV1PairTraceErrorV1::Shape)
        );
    }

    #[test]
    fn stable_and_late_mutations_fail_closed() {
        let (public, witness, context, snapshot) = fixture();
        let trace =
            build_pool_v1_pair_private_transfer_trace_v1(&public, &witness, context, snapshot)
                .unwrap();
        let mut stable_bad = trace.clone();
        stable_bad.stable.c1[7][100] = stable_bad.stable.c1[7][100].add(M31::ONE);
        assert!(validate_pool_v1_pair_private_transfer_trace_v1(
            &public,
            &witness,
            context,
            snapshot,
            &stable_bad
        )
        .is_err());
        let mut late_bad = trace;
        late_bad.late[4][700] = late_bad.late[4][700].add(M31::ONE);
        assert!(validate_pool_v1_pair_private_transfer_trace_v1(
            &public, &witness, context, snapshot, &late_bad
        )
        .is_err());
    }

    #[test]
    fn populated_live_frontier_uses_the_exact_twenty_late_blocks() {
        let (public, witness, context, _) = fixture();
        let snapshot = snapshot_at(public.pool, public.deployment_domain, 13);
        let trace =
            build_pool_v1_pair_private_transfer_trace_v1(&public, &witness, context, snapshot)
                .unwrap();
        assert_eq!(trace.afterstate.next_pair_index, 14);
        verify_pool_v1_pair_copy_registry_v1(
            &trace,
            snapshot.next_pair_index,
            QM31::from_cm31(CM31::from_m31(M31(29))),
            QM31::from_cm31(CM31::from_m31(M31(31))),
        )
        .unwrap();
    }
}
