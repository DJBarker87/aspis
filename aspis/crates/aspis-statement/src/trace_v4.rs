//! Frozen lr10/r2 host trace layout for the depth-20 SpendV0-min evaluator.
//!
//! This is a witness/layout foundation, not a constraint system or proof.
//! It records the evaluator's real Poseidon2 sponge calls into 49 aligned
//! blocks and makes the intended copy endpoints mechanically enumerable.

use alloc::vec;
use alloc::vec::Vec;

use aspis_core::field::M31;

use crate::poseidon2::{
    hash_fields_with_trace, Digest, Poseidon2RoundTransition, DIGEST_ELEMS, POSEIDON2_ROUNDS,
    POSEIDON2_WIDTH, RATE,
};
use crate::spend::{
    evaluate_spend_with_range_lookup_and_hasher, EvaluationContext, RangeLookupWitness, SpendError,
    SpendPublic, SpendWitness, DOMAIN_MERKLE_NODE, DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OUTPUT,
    DOMAIN_OWNER_KEY,
};
use crate::wide_v4::C1_COLUMNS;

pub const TRACE_ROWS: usize = 1 << 10;
pub const STATE_AND_INTERFACE_COLUMNS: usize = 48;
pub const INTERFACE_COLUMN_START: usize = 0;
pub const FIRST_ROUND_OUTPUT_COLUMN_START: usize = 16;
pub const SECOND_ROUND_OUTPUT_COLUMN_START: usize = 32;
pub const MULTIPLICITY_COLUMN: usize = 48;
pub const PERMUTATION_COUNT: usize = 49;
pub const BLOCK_ROWS: usize = 16;
pub const ACTIVE_ROWS_PER_BLOCK: usize = 11;
pub const ABSORPTION_ROW_IN_BLOCK: usize = ACTIVE_ROWS_PER_BLOCK;
pub const DEAD_ROW_START_IN_BLOCK: usize = ABSORPTION_ROW_IN_BLOCK + 1;
pub const PADDING_ROWS_PER_BLOCK: usize = BLOCK_ROWS - DEAD_ROW_START_IN_BLOCK;
pub const POSEIDON_ACTIVE_ROWS: usize = PERMUTATION_COUNT * ACTIVE_ROWS_PER_BLOCK;
pub const ALLOCATED_PERMUTATION_ROWS: usize = PERMUTATION_COUNT * BLOCK_ROWS;
pub const MERKLE_LEVEL_BOUNDARIES: usize = 19;
pub const AUX_WITNESS_ROW_START: usize = ALLOCATED_PERMUTATION_ROWS;
pub const AUX_ABSORPTION_PRODUCER_ROW_START: usize = 808;

pub const STATE_COPY_LINK_COUNT: usize = 490 + 25 + 19;
pub const SEMANTIC_INGRESS_COPY_LINK_COUNT: usize = 6;
pub const ABSORPTION_COPY_LINK_COUNT: usize = PERMUTATION_COUNT;
pub const COPY_LINK_COUNT: usize =
    STATE_COPY_LINK_COUNT + SEMANTIC_INGRESS_COPY_LINK_COUNT + ABSORPTION_COPY_LINK_COUNT;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HashInvocationKind {
    OwnerKey,
    Note,
    MerkleLevel(u8),
    Nullifier,
    Output,
}

/// Verifier-computable two-round selector for one trace row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoseidonRowKind {
    ExternalInitial,
    Internal,
    ExternalFinal,
    Absorption,
    Padding,
    OutsidePermutationRegion,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PermutationBlock {
    pub invocation: HashInvocationKind,
    pub chunk_index: u8,
    pub absorbed_len: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TracePublicOutputs {
    pub owner_key: Digest,
    pub note: Digest,
    pub anchor: Digest,
    pub nullifier: Digest,
    pub output_commitment: Digest,
}

/// Explicit use of one copied Merkle-level digest by the next compression.
/// The side bit is private witness data stored beside the copied digest; the
/// endpoint row itself is fixed by `level` and therefore verifier-computable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MerkleBoundaryBinding {
    pub level: u8,
    pub source_row: u16,
    pub path_bit: TraceCell,
    pub left: [TraceCell; DIGEST_ELEMS],
    pub right: [TraceCell; DIGEST_ELEMS],
    pub current: [TraceCell; DIGEST_ELEMS],
    pub sibling: [TraceCell; DIGEST_ELEMS],
    pub left_permutation_block: u8,
    pub right_permutation_block: u8,
}

/// Fixed committed cells for private inputs and lookup limbs. Hashed values
/// occupy row-local source rows; only path-index and range limbs use the
/// separate scalar area.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessAuxLayout {
    pub nullifier_key: [TraceCell; DIGEST_ELEMS],
    pub input_salt: [TraceCell; DIGEST_ELEMS],
    pub output_salt: [TraceCell; DIGEST_ELEMS],
    pub output_owner_key: [TraceCell; DIGEST_ELEMS],
    pub input_asset_id: TraceCell,
    pub value: TraceCell,
    pub value_out: TraceCell,
    pub merkle_siblings: [[TraceCell; DIGEST_ELEMS]; 20],
    pub merkle_path_index: TraceCell,
    pub merkle_path_bits: [TraceCell; 20],
    pub input_value_limbs: [TraceCell; 3],
    pub output_value_limbs: [TraceCell; 3],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendTraceV4 {
    /// Column-major C1 coefficient table. Columns 0..48 are state/interface;
    /// column 48 is the fixed-table multiplicity witness.
    pub c1: [Vec<M31>; C1_COLUMNS],
    pub outputs: TracePublicOutputs,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraceBuildError {
    Spend(SpendError),
    HashSchedule,
    PermutationCount,
    Validation(TraceValidationError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraceValidationError {
    Shape,
    NonZeroPadding { row: u16, column: u8 },
    NonZeroAbsorptionTail { block: u8, column: u8 },
    InitialSpongeState { block: u8 },
    PermutationReplay { block: u8, round: u8 },
    SourceRelation { block: u8, limb: u8 },
    MerkleSelection { level: u8, limb: u8 },
    PublicBinding,
    CopyMismatch { link: u16 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RecordedPermutation {
    pre_absorb: [M31; POSEIDON2_WIDTH],
    absorbed_len: u8,
    absorbed: [M31; RATE],
    transitions: [Poseidon2RoundTransition; POSEIDON2_ROUNDS],
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RecordedHashCall {
    kind: HashInvocationKind,
    output: Digest,
    permutations: Vec<RecordedPermutation>,
}

#[derive(Default)]
struct TraceRecorder {
    calls: Vec<RecordedHashCall>,
    merkle_level: u8,
}

impl TraceRecorder {
    fn classify(&mut self, domain: M31) -> Option<HashInvocationKind> {
        if domain == DOMAIN_OWNER_KEY {
            Some(HashInvocationKind::OwnerKey)
        } else if domain == DOMAIN_NOTE {
            Some(HashInvocationKind::Note)
        } else if domain == DOMAIN_MERKLE_NODE {
            let level = self.merkle_level;
            self.merkle_level = self.merkle_level.checked_add(1)?;
            Some(HashInvocationKind::MerkleLevel(level))
        } else if domain == DOMAIN_NULLIFIER {
            Some(HashInvocationKind::Nullifier)
        } else if domain == DOMAIN_OUTPUT {
            Some(HashInvocationKind::Output)
        } else {
            None
        }
    }

    fn hash(&mut self, domain: M31, input: &[M31]) -> Digest {
        let kind = self.classify(domain);
        let permutation_count = if input.is_empty() {
            1
        } else {
            input.len().div_ceil(RATE)
        };
        let mut transitions = (0..permutation_count)
            .map(|_| Vec::with_capacity(POSEIDON2_ROUNDS))
            .collect::<Vec<_>>();
        let output = hash_fields_with_trace(domain, input, |permutation, transition| {
            transitions[permutation].push(transition);
        });

        let mut pre_absorb = [M31::ZERO; POSEIDON2_WIDTH];
        pre_absorb[RATE] = domain;
        pre_absorb[RATE + 1] = M31(input.len() as u32);
        let mut recorded = Vec::with_capacity(permutation_count);
        for (permutation, permutation_transitions) in transitions.iter().enumerate() {
            let chunk = if input.is_empty() {
                &[][..]
            } else {
                let start = permutation * RATE;
                &input[start..core::cmp::min(start + RATE, input.len())]
            };
            let mut absorbed = [M31::ZERO; RATE];
            absorbed[..chunk.len()].copy_from_slice(chunk);
            let round_array: [Poseidon2RoundTransition; POSEIDON2_ROUNDS] = permutation_transitions
                .as_slice()
                .try_into()
                .expect("instrumented permutation must emit 22 rounds");
            let mut expected_input = pre_absorb;
            for (index, value) in chunk.iter().enumerate() {
                expected_input[index] = expected_input[index].add(*value);
            }
            debug_assert_eq!(round_array[0].input, expected_input);
            recorded.push(RecordedPermutation {
                pre_absorb,
                absorbed_len: chunk.len() as u8,
                absorbed,
                transitions: round_array,
            });
            pre_absorb = round_array[POSEIDON2_ROUNDS - 1].output;
        }
        self.calls.push(RecordedHashCall {
            kind: kind.unwrap_or(HashInvocationKind::MerkleLevel(u8::MAX)),
            output,
            permutations: recorded,
        });
        output
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TraceCell {
    pub row: u16,
    pub column: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TupleLimb {
    Cell(TraceCell),
    Zero,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CopyTuple {
    pub limbs: [TupleLimb; POSEIDON2_WIDTH],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CopyLinkKind {
    IntraPermutation,
    SpongeContinuation,
    MerkleLevel,
    SemanticIngress,
    Absorption,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CopyLink {
    pub id: u16,
    pub tag: M31,
    pub kind: CopyLinkKind,
    pub producer_row: u16,
    pub consumer_row: u16,
    pub producer: CopyTuple,
    pub consumer: CopyTuple,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CopyLayout {
    pub links: Vec<CopyLink>,
    producer_by_row: Vec<Option<u16>>,
    consumer_by_row: Vec<Option<u16>>,
}

impl CopyLayout {
    pub fn producer_link(&self, row: usize) -> Option<&CopyLink> {
        let id = usize::from(*self.producer_by_row.get(row)?.as_ref()?);
        self.links.get(id)
    }

    pub fn consumer_link(&self, row: usize) -> Option<&CopyLink> {
        let id = usize::from(*self.consumer_by_row.get(row)?.as_ref()?);
        self.links.get(id)
    }
}

fn state_tuple(row: usize, column_start: usize) -> CopyTuple {
    CopyTuple {
        limbs: core::array::from_fn(|limb| {
            TupleLimb::Cell(TraceCell {
                row: row as u16,
                column: (column_start + limb) as u8,
            })
        }),
    }
}

fn digest_tuple(row: usize, column_start: usize) -> CopyTuple {
    CopyTuple {
        limbs: core::array::from_fn(|limb| {
            if limb < DIGEST_ELEMS {
                TupleLimb::Cell(TraceCell {
                    row: row as u16,
                    column: (column_start + limb) as u8,
                })
            } else {
                TupleLimb::Zero
            }
        }),
    }
}

fn final_digest_cells(block: usize) -> [TraceCell; DIGEST_ELEMS] {
    let row = block * BLOCK_ROWS + ACTIVE_ROWS_PER_BLOCK - 1;
    core::array::from_fn(|limb| TraceCell {
        row: row as u16,
        column: (SECOND_ROUND_OUTPUT_COLUMN_START + limb) as u8,
    })
}

fn is_merkle_left_block(block: usize) -> bool {
    (4..=42).contains(&block) && block & 1 == 0
}

fn has_carry_payload(block: usize) -> bool {
    matches!(block, 0 | 2 | 3 | 47) || is_merkle_left_block(block)
}

fn absorption_source_tuple(block: usize) -> CopyTuple {
    let row = AUX_ABSORPTION_PRODUCER_ROW_START + block;
    CopyTuple {
        limbs: core::array::from_fn(|limb| {
            if limb < RATE {
                TupleLimb::Cell(TraceCell {
                    row: row as u16,
                    column: limb as u8,
                })
            } else if has_carry_payload(block) {
                TupleLimb::Cell(TraceCell {
                    row: row as u16,
                    column: if is_merkle_left_block(block) {
                        limb as u8
                    } else {
                        (limb + RATE) as u8
                    },
                })
            } else {
                TupleLimb::Zero
            }
        }),
    }
}

#[inline(never)]
fn append_link(
    layout: &mut CopyLayout,
    kind: CopyLinkKind,
    producer_row: usize,
    consumer_row: usize,
    producer: CopyTuple,
    consumer: CopyTuple,
) {
    let id = layout.links.len() as u16;
    debug_assert!(layout.producer_by_row[producer_row].is_none());
    debug_assert!(layout.consumer_by_row[consumer_row].is_none());
    layout.producer_by_row[producer_row] = Some(id);
    layout.consumer_by_row[consumer_row] = Some(id);
    layout.links.push(CopyLink {
        id,
        tag: M31(producer_row as u32 + 1),
        kind,
        producer_row: producer_row as u16,
        consumer_row: consumer_row as u16,
        producer,
        consumer,
    });
}

#[inline(never)]
fn append_intra_permutation_links(layout: &mut CopyLayout) {
    for block in 0..PERMUTATION_COUNT {
        let base = block * BLOCK_ROWS;
        for local_row in 0..ACTIVE_ROWS_PER_BLOCK - 1 {
            let producer_row = base + local_row;
            let consumer_row = producer_row + 1;
            append_link(
                layout,
                CopyLinkKind::IntraPermutation,
                producer_row,
                consumer_row,
                state_tuple(producer_row, SECOND_ROUND_OUTPUT_COLUMN_START),
                state_tuple(consumer_row, INTERFACE_COLUMN_START),
            );
        }
    }
}

#[inline(never)]
fn append_sponge_continuation_links(layout: &mut CopyLayout) {
    let mut continuations = Vec::with_capacity(25);
    continuations.extend_from_slice(&[(1usize, 2usize), (2, 3)]);
    for level in 0..20usize {
        continuations.push((4 + 2 * level, 5 + 2 * level));
    }
    continuations.push((44, 45));
    continuations.extend_from_slice(&[(46, 47), (47, 48)]);
    for (producer_block, consumer_block) in continuations {
        let producer_row = producer_block * BLOCK_ROWS + ACTIVE_ROWS_PER_BLOCK - 1;
        let consumer_row = consumer_block * BLOCK_ROWS;
        append_link(
            layout,
            CopyLinkKind::SpongeContinuation,
            producer_row,
            consumer_row,
            state_tuple(producer_row, SECOND_ROUND_OUTPUT_COLUMN_START),
            state_tuple(consumer_row, INTERFACE_COLUMN_START),
        );
    }
}

#[inline(never)]
fn append_merkle_level_links(layout: &mut CopyLayout) {
    for level in 0..MERKLE_LEVEL_BOUNDARIES {
        let producer_block = 5 + 2 * level;
        let producer_row = producer_block * BLOCK_ROWS + ACTIVE_ROWS_PER_BLOCK - 1;
        let consumer_row = AUX_ABSORPTION_PRODUCER_ROW_START + 6 + 2 * level;
        append_link(
            layout,
            CopyLinkKind::MerkleLevel,
            producer_row,
            consumer_row,
            digest_tuple(producer_row, SECOND_ROUND_OUTPUT_COLUMN_START),
            digest_tuple(consumer_row, FIRST_ROUND_OUTPUT_COLUMN_START),
        );
    }
}

#[inline(never)]
fn append_semantic_ingress_links(layout: &mut CopyLayout) {
    let links = [
        (
            ACTIVE_ROWS_PER_BLOCK - 1,
            SECOND_ROUND_OUTPUT_COLUMN_START,
            AUX_ABSORPTION_PRODUCER_ROW_START + 1,
            FIRST_ROUND_OUTPUT_COLUMN_START,
        ),
        (
            3 * BLOCK_ROWS + ACTIVE_ROWS_PER_BLOCK - 1,
            SECOND_ROUND_OUTPUT_COLUMN_START,
            AUX_ABSORPTION_PRODUCER_ROW_START + 4,
            FIRST_ROUND_OUTPUT_COLUMN_START,
        ),
        (
            ABSORPTION_ROW_IN_BLOCK,
            RATE,
            AUX_ABSORPTION_PRODUCER_ROW_START + 44,
            FIRST_ROUND_OUTPUT_COLUMN_START,
        ),
        (
            2 * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK,
            RATE,
            AUX_ABSORPTION_PRODUCER_ROW_START + 3,
            FIRST_ROUND_OUTPUT_COLUMN_START,
        ),
        (
            3 * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK,
            RATE,
            AUX_ABSORPTION_PRODUCER_ROW_START + 45,
            FIRST_ROUND_OUTPUT_COLUMN_START,
        ),
        (
            47 * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK,
            RATE,
            AUX_ABSORPTION_PRODUCER_ROW_START + 48,
            FIRST_ROUND_OUTPUT_COLUMN_START,
        ),
    ];
    for (producer_row, producer_column, consumer_row, consumer_column) in links {
        append_link(
            layout,
            CopyLinkKind::SemanticIngress,
            producer_row,
            consumer_row,
            digest_tuple(producer_row, producer_column),
            digest_tuple(consumer_row, consumer_column),
        );
    }
}

fn is_merkle_right_block(block: usize) -> bool {
    (5..=43).contains(&block) && block & 1 == 1
}

#[inline(never)]
fn append_absorption_links(layout: &mut CopyLayout) {
    for block in 0..PERMUTATION_COUNT {
        let consumer_row = block * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK;
        if is_merkle_right_block(block) {
            let producer_row = (block - 1) * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK;
            append_link(
                layout,
                CopyLinkKind::Absorption,
                producer_row,
                consumer_row,
                digest_tuple(producer_row, RATE),
                digest_tuple(consumer_row, INTERFACE_COLUMN_START),
            );
        } else {
            append_link(
                layout,
                CopyLinkKind::Absorption,
                AUX_ABSORPTION_PRODUCER_ROW_START + block,
                consumer_row,
                absorption_source_tuple(block),
                state_tuple(consumer_row, INTERFACE_COLUMN_START),
            );
        }
    }
}

/// Deterministic copy layout. It depends only on the frozen block schedule,
/// never on witness values or Fiat-Shamir challenges.
pub fn copy_layout() -> CopyLayout {
    let mut layout = CopyLayout {
        links: Vec::with_capacity(COPY_LINK_COUNT),
        producer_by_row: vec![None; TRACE_ROWS],
        consumer_by_row: vec![None; TRACE_ROWS],
    };

    append_intra_permutation_links(&mut layout);
    append_sponge_continuation_links(&mut layout);
    append_merkle_level_links(&mut layout);
    append_semantic_ingress_links(&mut layout);
    append_absorption_links(&mut layout);

    debug_assert_eq!(layout.links.len(), COPY_LINK_COUNT);
    layout
}

fn witness_aux_cell(offset: usize) -> TraceCell {
    TraceCell {
        row: (AUX_WITNESS_ROW_START + offset / STATE_AND_INTERFACE_COLUMNS) as u16,
        column: (offset % STATE_AND_INTERFACE_COLUMNS) as u8,
    }
}

fn source_cell(block: usize, column: usize) -> TraceCell {
    TraceCell {
        row: (AUX_ABSORPTION_PRODUCER_ROW_START + block) as u16,
        column: column as u8,
    }
}

/// Verifier-computable placement of private statement inputs. Hashed values
/// live only in the row-local source slab; the separate scalar area holds
/// only path-index and range-limb witnesses.
pub fn witness_aux_layout() -> WitnessAuxLayout {
    let nullifier_key = core::array::from_fn(|index| source_cell(0, 16 + index));
    let input_salt = core::array::from_fn(|index| source_cell(2, 16 + index));
    let output_salt = core::array::from_fn(|index| source_cell(47, 16 + index));
    let output_owner_key = core::array::from_fn(|index| source_cell(46, 16 + index));
    let input_asset_id = source_cell(2, 34);
    let value = source_cell(2, 33);
    let value_out = source_cell(47, 33);
    let merkle_siblings = core::array::from_fn(|level| {
        core::array::from_fn(|limb| source_cell(4 + 2 * level, 24 + limb))
    });
    let merkle_path_index = witness_aux_cell(0);
    let merkle_path_bits = core::array::from_fn(|level| source_cell(4 + 2 * level, 32));
    let input_value_limbs = core::array::from_fn(|index| witness_aux_cell(1 + index));
    let output_value_limbs = core::array::from_fn(|index| witness_aux_cell(4 + index));
    WitnessAuxLayout {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id,
        value,
        value_out,
        merkle_siblings,
        merkle_path_index,
        merkle_path_bits,
        input_value_limbs,
        output_value_limbs,
    }
}

/// Frozen, verifier-derived block schedule. None of these values are witness
/// metadata: a verifier obtains the invocation, chunk index, and live
/// absorption width from the public block index alone.
pub const fn permutation_block_schedule(block: usize) -> Option<PermutationBlock> {
    if block == 0 {
        Some(PermutationBlock {
            invocation: HashInvocationKind::OwnerKey,
            chunk_index: 0,
            absorbed_len: 8,
        })
    } else if block <= 3 {
        Some(PermutationBlock {
            invocation: HashInvocationKind::Note,
            chunk_index: (block - 1) as u8,
            absorbed_len: if block == 3 { 2 } else { 8 },
        })
    } else if block <= 43 {
        Some(PermutationBlock {
            invocation: HashInvocationKind::MerkleLevel(((block - 4) / 2) as u8),
            chunk_index: ((block - 4) % 2) as u8,
            absorbed_len: 8,
        })
    } else if block <= 45 {
        Some(PermutationBlock {
            invocation: HashInvocationKind::Nullifier,
            chunk_index: (block - 44) as u8,
            absorbed_len: 8,
        })
    } else if block < PERMUTATION_COUNT {
        Some(PermutationBlock {
            invocation: HashInvocationKind::Output,
            chunk_index: (block - 46) as u8,
            absorbed_len: if block == 48 { 2 } else { 8 },
        })
    } else {
        None
    }
}

const fn invocation_domain_and_input_len(kind: HashInvocationKind) -> (M31, usize) {
    match kind {
        HashInvocationKind::OwnerKey => (DOMAIN_OWNER_KEY, 8),
        HashInvocationKind::Note => (DOMAIN_NOTE, 18),
        HashInvocationKind::MerkleLevel(_) => (DOMAIN_MERKLE_NODE, 16),
        HashInvocationKind::Nullifier => (DOMAIN_NULLIFIER, 16),
        HashInvocationKind::Output => (DOMAIN_OUTPUT, 18),
    }
}

fn expected_initial_sponge_state(kind: HashInvocationKind) -> [M31; POSEIDON2_WIDTH] {
    let (domain, input_len) = invocation_domain_and_input_len(kind);
    let mut state = [M31::ZERO; POSEIDON2_WIDTH];
    state[RATE] = domain;
    state[RATE + 1] = M31(input_len as u32);
    state
}

/// The 20 path-dependent left/right bindings are fixed by level. Only their
/// committed Boolean path-bit values vary with the witness.
pub fn merkle_boundary_layout() -> Vec<MerkleBoundaryBinding> {
    let aux = witness_aux_layout();
    (0..20usize)
        .map(|level| {
            let block = 4 + 2 * level;
            let row = AUX_ABSORPTION_PRODUCER_ROW_START + block;
            MerkleBoundaryBinding {
                level: level as u8,
                source_row: row as u16,
                path_bit: aux.merkle_path_bits[level],
                left: core::array::from_fn(|limb| TraceCell {
                    row: row as u16,
                    column: limb as u8,
                }),
                right: core::array::from_fn(|limb| TraceCell {
                    row: row as u16,
                    column: (RATE + limb) as u8,
                }),
                current: core::array::from_fn(|limb| TraceCell {
                    row: row as u16,
                    column: (16 + limb) as u8,
                }),
                sibling: core::array::from_fn(|limb| TraceCell {
                    row: row as u16,
                    column: (24 + limb) as u8,
                }),
                left_permutation_block: block as u8,
                right_permutation_block: (block + 1) as u8,
            }
        })
        .collect()
}

pub const fn is_poseidon_active_row(row: usize) -> bool {
    row < ALLOCATED_PERMUTATION_ROWS && row % BLOCK_ROWS < ACTIVE_ROWS_PER_BLOCK
}

pub const fn is_absorption_row(row: usize) -> bool {
    row < ALLOCATED_PERMUTATION_ROWS && row % BLOCK_ROWS == ABSORPTION_ROW_IN_BLOCK
}

pub const fn is_poseidon_padding_row(row: usize) -> bool {
    row < ALLOCATED_PERMUTATION_ROWS && row % BLOCK_ROWS >= DEAD_ROW_START_IN_BLOCK
}

pub const fn poseidon_row_kind(row: usize) -> PoseidonRowKind {
    if row >= ALLOCATED_PERMUTATION_ROWS {
        return PoseidonRowKind::OutsidePermutationRegion;
    }
    match row % BLOCK_ROWS {
        0 | 1 => PoseidonRowKind::ExternalInitial,
        2..=8 => PoseidonRowKind::Internal,
        9 | 10 => PoseidonRowKind::ExternalFinal,
        11 => PoseidonRowKind::Absorption,
        _ => PoseidonRowKind::Padding,
    }
}

fn expected_call_schedule(calls: &[RecordedHashCall]) -> bool {
    if calls.len() != 24 {
        return false;
    }
    if calls[0].kind != HashInvocationKind::OwnerKey
        || calls[1].kind != HashInvocationKind::Note
        || calls[22].kind != HashInvocationKind::Nullifier
        || calls[23].kind != HashInvocationKind::Output
    {
        return false;
    }
    (0..20usize).all(|level| calls[2 + level].kind == HashInvocationKind::MerkleLevel(level as u8))
}

fn call_output(calls: &[RecordedHashCall], kind: HashInvocationKind) -> Option<Digest> {
    calls
        .iter()
        .find(|call| call.kind == kind)
        .map(|call| call.output)
}

fn write_cell(c1: &mut [Vec<M31>; C1_COLUMNS], cell: TraceCell, value: M31) {
    c1[cell.column as usize][cell.row as usize] = value;
}

/// Execute the real range-aware SpendV0 evaluator and lay its 49 recorded
/// permutations into the frozen C1 table.
pub fn build_spend_trace_v4(
    public: &SpendPublic,
    witness: &SpendWitness,
) -> Result<SpendTraceV4, TraceBuildError> {
    let range_witness = RangeLookupWitness::from_spend(witness);
    let mut recorder = TraceRecorder::default();
    let evaluation = {
        let mut hasher = |domain, input: &[M31]| recorder.hash(domain, input);
        evaluate_spend_with_range_lookup_and_hasher(
            public,
            witness,
            &range_witness,
            EvaluationContext {
                merkle_depth: 20,
                spent_nullifiers: &[],
            },
            &mut hasher,
        )
    };
    evaluation.map_err(TraceBuildError::Spend)?;

    if !expected_call_schedule(&recorder.calls) {
        return Err(TraceBuildError::HashSchedule);
    }
    let permutation_count = recorder
        .calls
        .iter()
        .map(|call| call.permutations.len())
        .sum::<usize>();
    if permutation_count != PERMUTATION_COUNT {
        return Err(TraceBuildError::PermutationCount);
    }

    let mut c1: [Vec<M31>; C1_COLUMNS] = core::array::from_fn(|_| vec![M31::ZERO; TRACE_ROWS]);
    let mut block = 0usize;
    for call in &recorder.calls {
        for (chunk_index, permutation) in call.permutations.iter().enumerate() {
            let schedule =
                permutation_block_schedule(block).ok_or(TraceBuildError::HashSchedule)?;
            if schedule.invocation != call.kind
                || usize::from(schedule.chunk_index) != chunk_index
                || schedule.absorbed_len != permutation.absorbed_len
            {
                return Err(TraceBuildError::HashSchedule);
            }
            let base = block * BLOCK_ROWS;
            for limb in 0..POSEIDON2_WIDTH {
                c1[INTERFACE_COLUMN_START + limb][base] = permutation.pre_absorb[limb];
            }
            for local_row in 0..ACTIVE_ROWS_PER_BLOCK {
                let row = base + local_row;
                let first = permutation.transitions[2 * local_row];
                let second = permutation.transitions[2 * local_row + 1];
                if local_row > 0 {
                    for limb in 0..POSEIDON2_WIDTH {
                        c1[INTERFACE_COLUMN_START + limb][row] = first.input[limb];
                    }
                }
                for limb in 0..POSEIDON2_WIDTH {
                    c1[FIRST_ROUND_OUTPUT_COLUMN_START + limb][row] = first.output[limb];
                    c1[SECOND_ROUND_OUTPUT_COLUMN_START + limb][row] = second.output[limb];
                }
            }
            let absorption_row = base + ABSORPTION_ROW_IN_BLOCK;
            for (limb, value) in permutation.absorbed.into_iter().enumerate() {
                c1[limb][absorption_row] = value;
                if is_merkle_right_block(block) {
                    let left_block = block - 1;
                    c1[RATE + limb][left_block * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK] = value;
                    c1[RATE + limb][AUX_ABSORPTION_PRODUCER_ROW_START + left_block] = value;
                } else {
                    c1[limb][AUX_ABSORPTION_PRODUCER_ROW_START + block] = value;
                }
            }
            block += 1;
        }
    }

    let limbs = range_witness
        .input_value_limbs
        .into_iter()
        .chain(range_witness.output_value_limbs);
    for limb in limbs {
        let row = usize::from(limb);
        c1[MULTIPLICITY_COLUMN][row] = c1[MULTIPLICITY_COLUMN][row].add(M31::ONE);
    }

    let aux = witness_aux_layout();
    for (cell, value) in aux.nullifier_key.into_iter().zip(witness.nullifier_key) {
        write_cell(&mut c1, cell, value);
    }
    for (cell, value) in aux.input_salt.into_iter().zip(witness.input_salt) {
        write_cell(&mut c1, cell, value);
    }
    for (cell, value) in aux.output_salt.into_iter().zip(witness.output_salt) {
        write_cell(&mut c1, cell, value);
    }
    for (cell, value) in aux
        .output_owner_key
        .into_iter()
        .zip(witness.output_owner_key)
    {
        write_cell(&mut c1, cell, value);
    }
    write_cell(&mut c1, aux.input_asset_id, witness.input_asset_id);
    write_cell(&mut c1, aux.value, M31(witness.value));
    write_cell(&mut c1, aux.value_out, M31(witness.value_out));
    c1[34][AUX_ABSORPTION_PRODUCER_ROW_START + 47] = public.asset_id;
    for (cells, sibling) in aux
        .merkle_siblings
        .into_iter()
        .zip(&witness.merkle_path.siblings)
    {
        for (cell, value) in cells.into_iter().zip(*sibling) {
            write_cell(&mut c1, cell, value);
        }
    }
    write_cell(
        &mut c1,
        aux.merkle_path_index,
        M31(witness.merkle_path.index),
    );
    for (level, cell) in aux.merkle_path_bits.into_iter().enumerate() {
        write_cell(&mut c1, cell, M31((witness.merkle_path.index >> level) & 1));
    }
    for (cell, limb) in aux
        .input_value_limbs
        .into_iter()
        .zip(range_witness.input_value_limbs)
    {
        write_cell(&mut c1, cell, M31(u32::from(limb)));
    }
    for (cell, limb) in aux
        .output_value_limbs
        .into_iter()
        .zip(range_witness.output_value_limbs)
    {
        write_cell(&mut c1, cell, M31(u32::from(limb)));
    }

    let owner_key = call_output(&recorder.calls, HashInvocationKind::OwnerKey)
        .ok_or(TraceBuildError::HashSchedule)?;
    let note = call_output(&recorder.calls, HashInvocationKind::Note)
        .ok_or(TraceBuildError::HashSchedule)?;
    let anchor = call_output(&recorder.calls, HashInvocationKind::MerkleLevel(19))
        .ok_or(TraceBuildError::HashSchedule)?;
    let nullifier = call_output(&recorder.calls, HashInvocationKind::Nullifier)
        .ok_or(TraceBuildError::HashSchedule)?;
    let output_commitment = call_output(&recorder.calls, HashInvocationKind::Output)
        .ok_or(TraceBuildError::HashSchedule)?;

    for (block, digest) in [
        (1usize, owner_key),
        (3, witness.input_salt),
        (4, note),
        (44, witness.nullifier_key),
        (45, witness.input_salt),
        (48, witness.output_salt),
    ] {
        let row = AUX_ABSORPTION_PRODUCER_ROW_START + block;
        for (limb, value) in digest.into_iter().enumerate() {
            c1[FIRST_ROUND_OUTPUT_COLUMN_START + limb][row] = value;
        }
    }

    for (block, digest) in [
        (0usize, witness.nullifier_key),
        (2, witness.input_salt),
        (3, witness.input_salt),
        (47, witness.output_salt),
    ] {
        let row = block * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK;
        for (limb, value) in digest.into_iter().enumerate() {
            c1[RATE + limb][row] = value;
        }
    }

    for level in 0..MERKLE_LEVEL_BOUNDARIES {
        let digest = call_output(
            &recorder.calls,
            HashInvocationKind::MerkleLevel(level as u8),
        )
        .ok_or(TraceBuildError::HashSchedule)?;
        let row = AUX_ABSORPTION_PRODUCER_ROW_START + 6 + 2 * level;
        for limb in 0..DIGEST_ELEMS {
            c1[FIRST_ROUND_OUTPUT_COLUMN_START + limb][row] = digest[limb];
        }
    }

    let outputs = TracePublicOutputs {
        owner_key,
        note,
        anchor,
        nullifier,
        output_commitment,
    };

    let trace = SpendTraceV4 { c1, outputs };
    validate_spend_trace_v4(public, &trace).map_err(TraceBuildError::Validation)?;
    Ok(trace)
}

fn read_cell(trace: &SpendTraceV4, cell: TraceCell) -> M31 {
    trace.c1[cell.column as usize][cell.row as usize]
}

fn tuple_value(trace: &SpendTraceV4, tuple: CopyTuple) -> [M31; POSEIDON2_WIDTH] {
    tuple.limbs.map(|limb| match limb {
        TupleLimb::Cell(cell) => read_cell(trace, cell),
        TupleLimb::Zero => M31::ZERO,
    })
}

#[inline(never)]
fn validate_trace_shape(trace: &SpendTraceV4) -> Result<(), TraceValidationError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(TraceValidationError::Shape);
    }
    Ok(())
}

#[inline(never)]
fn validate_dead_and_absorption_rows(trace: &SpendTraceV4) -> Result<(), TraceValidationError> {
    for block in 0..PERMUTATION_COUNT {
        let schedule = permutation_block_schedule(block).ok_or(TraceValidationError::Shape)?;
        let absorption_row = block * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK;
        for column in usize::from(schedule.absorbed_len)..RATE {
            if trace.c1[column][absorption_row] != M31::ZERO {
                return Err(TraceValidationError::NonZeroAbsorptionTail {
                    block: block as u8,
                    column: column as u8,
                });
            }
        }
        if !has_carry_payload(block) {
            for column in RATE..POSEIDON2_WIDTH {
                if trace.c1[column][absorption_row] != M31::ZERO {
                    return Err(TraceValidationError::NonZeroAbsorptionTail {
                        block: block as u8,
                        column: column as u8,
                    });
                }
            }
        }
        for column in POSEIDON2_WIDTH..STATE_AND_INTERFACE_COLUMNS {
            if trace.c1[column][absorption_row] != M31::ZERO {
                return Err(TraceValidationError::NonZeroAbsorptionTail {
                    block: block as u8,
                    column: column as u8,
                });
            }
        }
        for local_row in DEAD_ROW_START_IN_BLOCK..BLOCK_ROWS {
            let row = block * BLOCK_ROWS + local_row;
            for column in 0..STATE_AND_INTERFACE_COLUMNS {
                if trace.c1[column][row] != M31::ZERO {
                    return Err(TraceValidationError::NonZeroPadding {
                        row: row as u16,
                        column: column as u8,
                    });
                }
            }
        }
    }
    Ok(())
}

#[inline(never)]
fn validate_permutation_replay(trace: &SpendTraceV4) -> Result<(), TraceValidationError> {
    for block in 0..PERMUTATION_COUNT {
        let schedule = permutation_block_schedule(block).ok_or(TraceValidationError::Shape)?;
        let base = block * BLOCK_ROWS;
        let mut state = core::array::from_fn(|limb| trace.c1[limb][base]);
        if schedule.chunk_index == 0 && state != expected_initial_sponge_state(schedule.invocation)
        {
            return Err(TraceValidationError::InitialSpongeState { block: block as u8 });
        }
        let absorption_row = base + ABSORPTION_ROW_IN_BLOCK;
        for (limb, state_limb) in state
            .iter_mut()
            .take(usize::from(schedule.absorbed_len))
            .enumerate()
        {
            *state_limb = state_limb.add(trace.c1[limb][absorption_row]);
        }

        let mut failed_round = None;
        crate::poseidon2::permute_optimized_with_trace(&mut state, |transition| {
            if failed_round.is_some() {
                return;
            }
            let round = usize::from(transition.round);
            let local_row = round / 2;
            let row = base + local_row;
            let mismatch = if round % 2 == 0 {
                (local_row > 0
                    && (0..POSEIDON2_WIDTH).any(|limb| {
                        trace.c1[INTERFACE_COLUMN_START + limb][row] != transition.input[limb]
                    }))
                    || (0..POSEIDON2_WIDTH).any(|limb| {
                        trace.c1[FIRST_ROUND_OUTPUT_COLUMN_START + limb][row]
                            != transition.output[limb]
                    })
            } else {
                (0..POSEIDON2_WIDTH).any(|limb| {
                    trace.c1[SECOND_ROUND_OUTPUT_COLUMN_START + limb][row]
                        != transition.output[limb]
                })
            };
            if mismatch {
                failed_round = Some(transition.round);
            }
        });
        if let Some(round) = failed_round {
            return Err(TraceValidationError::PermutationReplay {
                block: block as u8,
                round,
            });
        }
    }
    Ok(())
}

fn validate_equal_source_cells(
    trace: &SpendTraceV4,
    block: usize,
    pairs: &[(usize, usize)],
) -> Result<(), TraceValidationError> {
    let row = AUX_ABSORPTION_PRODUCER_ROW_START + block;
    for (limb, (left, right)) in pairs.iter().copied().enumerate() {
        if trace.c1[left][row] != trace.c1[right][row] {
            return Err(TraceValidationError::SourceRelation {
                block: block as u8,
                limb: limb as u8,
            });
        }
    }
    Ok(())
}

#[inline(never)]
fn validate_source_relations(trace: &SpendTraceV4) -> Result<(), TraceValidationError> {
    let full_digest_pairs = [
        (0, 16),
        (1, 17),
        (2, 18),
        (3, 19),
        (4, 20),
        (5, 21),
        (6, 22),
        (7, 23),
    ];
    for block in [0usize, 1, 44, 45, 46] {
        validate_equal_source_cells(trace, block, &full_digest_pairs)?;
    }
    validate_equal_source_cells(
        trace,
        2,
        &[
            (0, 33),
            (1, 34),
            (2, 16),
            (3, 17),
            (4, 18),
            (5, 19),
            (6, 20),
            (7, 21),
        ],
    )?;
    validate_equal_source_cells(trace, 3, &[(0, 22), (1, 23)])?;
    validate_equal_source_cells(
        trace,
        47,
        &[
            (0, 33),
            (1, 34),
            (2, 16),
            (3, 17),
            (4, 18),
            (5, 19),
            (6, 20),
            (7, 21),
        ],
    )?;
    validate_equal_source_cells(trace, 48, &[(0, 22), (1, 23)])?;

    for binding in merkle_boundary_layout() {
        let bit = read_cell(trace, binding.path_bit);
        if bit != M31::ZERO && bit != M31::ONE {
            return Err(TraceValidationError::Shape);
        }
        for limb in 0..DIGEST_ELEMS {
            let current = read_cell(trace, binding.current[limb]);
            let sibling = read_cell(trace, binding.sibling[limb]);
            let expected_left = if bit == M31::ZERO { current } else { sibling };
            let expected_right = if bit == M31::ZERO { sibling } else { current };
            if read_cell(trace, binding.left[limb]) != expected_left
                || read_cell(trace, binding.right[limb]) != expected_right
            {
                return Err(TraceValidationError::MerkleSelection {
                    level: binding.level,
                    limb: limb as u8,
                });
            }
        }
    }
    Ok(())
}

#[inline(never)]
fn validate_aux_values(trace: &SpendTraceV4) -> Result<(), TraceValidationError> {
    let aux = witness_aux_layout();
    let mut reconstructed_index = 0u32;
    for (level, cell) in aux.merkle_path_bits.into_iter().enumerate() {
        let bit = read_cell(trace, cell);
        if bit != M31::ZERO && bit != M31::ONE {
            return Err(TraceValidationError::Shape);
        }
        reconstructed_index |= bit.0 << level;
    }
    if read_cell(trace, aux.merkle_path_index) != M31(reconstructed_index) {
        return Err(TraceValidationError::Shape);
    }

    for (limbs, target) in [
        (aux.input_value_limbs, aux.value),
        (aux.output_value_limbs, aux.value_out),
    ] {
        let mut reconstructed = 0u32;
        for (index, cell) in limbs.into_iter().enumerate() {
            let limb = read_cell(trace, cell).0;
            if limb >= TRACE_ROWS as u32 {
                return Err(TraceValidationError::Shape);
            }
            reconstructed |= limb << (index as u32 * 10);
        }
        if read_cell(trace, target) != M31(reconstructed) {
            return Err(TraceValidationError::Shape);
        }
    }

    let mut expected_multiplicities = vec![0u32; TRACE_ROWS];
    for cell in aux
        .input_value_limbs
        .into_iter()
        .chain(aux.output_value_limbs)
    {
        let value = read_cell(trace, cell).0 as usize;
        if value >= TRACE_ROWS {
            return Err(TraceValidationError::Shape);
        }
        expected_multiplicities[value] += 1;
    }
    for (row, expected) in expected_multiplicities.into_iter().enumerate() {
        if trace.c1[MULTIPLICITY_COLUMN][row] != M31(expected) {
            return Err(TraceValidationError::Shape);
        }
    }
    Ok(())
}

fn derived_public_outputs(trace: &SpendTraceV4) -> TracePublicOutputs {
    let digest_at = |block| final_digest_cells(block).map(|cell| read_cell(trace, cell));
    TracePublicOutputs {
        owner_key: digest_at(0),
        note: digest_at(3),
        anchor: digest_at(43),
        nullifier: digest_at(45),
        output_commitment: digest_at(48),
    }
}

#[inline(never)]
fn validate_copy_links(trace: &SpendTraceV4) -> Result<(), TraceValidationError> {
    let layout = copy_layout();
    for link in &layout.links {
        if tuple_value(trace, link.producer) != tuple_value(trace, link.consumer) {
            return Err(TraceValidationError::CopyMismatch { link: link.id });
        }
    }
    Ok(())
}

#[inline(never)]
fn validate_public_bindings(
    public: &SpendPublic,
    trace: &SpendTraceV4,
    outputs: &TracePublicOutputs,
) -> Result<(), TraceValidationError> {
    let aux = witness_aux_layout();
    if outputs.anchor != public.anchor
        || outputs.nullifier != public.nullifier
        || outputs.output_commitment != public.output_commitment
        || read_cell(trace, aux.input_asset_id) != public.asset_id
        || trace.c1[34][AUX_ABSORPTION_PRODUCER_ROW_START + 47] != public.asset_id
    {
        return Err(TraceValidationError::PublicBinding);
    }
    Ok(())
}

/// Structural replay for the trace foundation. Constraint batching and
/// statement-sumcheck checks deliberately live in later milestones.
pub fn validate_spend_trace_v4(
    public: &SpendPublic,
    trace: &SpendTraceV4,
) -> Result<(), TraceValidationError> {
    validate_trace_shape(trace)?;
    validate_dead_and_absorption_rows(trace)?;
    validate_permutation_replay(trace)?;
    validate_source_relations(trace)?;
    validate_aux_values(trace)?;
    let outputs = derived_public_outputs(trace);
    if trace.outputs != outputs {
        return Err(TraceValidationError::Shape);
    }
    validate_public_bindings(public, trace, &outputs)?;
    validate_copy_links(trace)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spend::{
        derive_nullifier, derive_owner_key, merkle_root, note_commitment, output_commitment,
        MerklePath,
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn fixture() -> (SpendPublic, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let fee = 1;
        let owner_key = derive_owner_key(&nullifier_key);
        let note = note_commitment(&owner_key, value, asset_id, &input_salt);
        let path = MerklePath {
            siblings: (0..20)
                .map(|level| digest(1_000 + level as u32 * 31))
                .collect(),
            index: 0x5a5a5,
        };
        let public = SpendPublic {
            anchor: merkle_root(note, &path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee,
        };
        let witness = SpendWitness {
            nullifier_key,
            input_salt,
            output_salt,
            output_owner_key,
            input_asset_id: asset_id,
            value,
            value_out,
            merkle_path: path,
        };
        (public, witness)
    }

    #[test]
    fn frozen_shape_and_real_evaluator_schedule_match() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        assert_eq!(trace.c1.len(), 49);
        assert!(trace.c1.iter().all(|column| column.len() == TRACE_ROWS));
        assert_eq!(
            (0..PERMUTATION_COUNT)
                .filter_map(permutation_block_schedule)
                .count(),
            PERMUTATION_COUNT
        );
        assert_eq!(POSEIDON_ACTIVE_ROWS, 539);
        assert_eq!(ALLOCATED_PERMUTATION_ROWS, 784);
        assert_eq!(TRACE_ROWS, 1024);
        assert_eq!(
            (0..TRACE_ROWS)
                .filter(|row| is_poseidon_active_row(*row))
                .count(),
            POSEIDON_ACTIVE_ROWS
        );
        assert_eq!(poseidon_row_kind(0), PoseidonRowKind::ExternalInitial);
        assert_eq!(poseidon_row_kind(2), PoseidonRowKind::Internal);
        assert_eq!(poseidon_row_kind(9), PoseidonRowKind::ExternalFinal);
        assert_eq!(poseidon_row_kind(11), PoseidonRowKind::Absorption);
        assert_eq!(poseidon_row_kind(12), PoseidonRowKind::Padding);
        assert_eq!(
            poseidon_row_kind(ALLOCATED_PERMUTATION_ROWS),
            PoseidonRowKind::OutsidePermutationRegion
        );
        assert_eq!(validate_spend_trace_v4(&public, &trace), Ok(()));
    }

    #[test]
    fn trace_outputs_equal_the_public_evaluator_digests() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let owner_key = derive_owner_key(&witness.nullifier_key);
        let note = note_commitment(
            &owner_key,
            witness.value,
            witness.input_asset_id,
            &witness.input_salt,
        );
        assert_eq!(trace.outputs.owner_key, owner_key);
        assert_eq!(trace.outputs.note, note);
        assert_eq!(trace.outputs.anchor, public.anchor);
        assert_eq!(trace.outputs.nullifier, public.nullifier);
        assert_eq!(trace.outputs.output_commitment, public.output_commitment);
    }

    #[test]
    fn permutation_and_boundary_corruptions_are_detected() {
        let (public, witness) = fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        trace.c1[FIRST_ROUND_OUTPUT_COLUMN_START][0] =
            trace.c1[FIRST_ROUND_OUTPUT_COLUMN_START][0].add(M31::ONE);
        assert_eq!(
            validate_spend_trace_v4(&public, &trace),
            Err(TraceValidationError::PermutationReplay { block: 0, round: 0 })
        );

        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        let source_row = AUX_ABSORPTION_PRODUCER_ROW_START + 6;
        trace.c1[FIRST_ROUND_OUTPUT_COLUMN_START][source_row] =
            trace.c1[FIRST_ROUND_OUTPUT_COLUMN_START][source_row].add(M31::ONE);
        assert!(matches!(
            validate_spend_trace_v4(&public, &trace),
            Err(TraceValidationError::MerkleSelection { .. })
        ));
    }

    #[test]
    fn multiplicity_column_is_the_real_six_limb_histogram() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let expected = RangeLookupWitness::from_spend(&witness);
        let mut counts = [0u32; TRACE_ROWS];
        for limb in expected
            .input_value_limbs
            .into_iter()
            .chain(expected.output_value_limbs)
        {
            counts[usize::from(limb)] += 1;
        }
        assert_eq!(
            trace.c1[MULTIPLICITY_COLUMN]
                .iter()
                .map(|value| value.0)
                .sum::<u32>(),
            6
        );
        for (row, count) in counts.into_iter().enumerate() {
            assert_eq!(trace.c1[MULTIPLICITY_COLUMN][row], M31(count));
        }
    }

    #[test]
    fn copy_layout_recounts_all_589_row_local_explicit_endpoints() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let layout = copy_layout();
        assert_eq!(layout.links.len(), COPY_LINK_COUNT);
        assert_eq!(COPY_LINK_COUNT, 589);
        assert_eq!(
            layout
                .links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::IntraPermutation)
                .count(),
            490
        );
        assert_eq!(
            layout
                .links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::SpongeContinuation)
                .count(),
            25
        );
        assert_eq!(
            layout
                .links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::MerkleLevel)
                .count(),
            19
        );
        assert_eq!(
            layout
                .links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::SemanticIngress)
                .count(),
            6
        );
        assert_eq!(
            layout
                .links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::Absorption)
                .count(),
            49
        );
        let mut producer_rows = [false; TRACE_ROWS];
        for link in layout.links {
            assert_eq!(
                tuple_value(&trace, link.producer),
                tuple_value(&trace, link.consumer)
            );
            assert!(!producer_rows[usize::from(link.producer_row)]);
            producer_rows[usize::from(link.producer_row)] = true;
            assert_eq!(link.tag, M31(u32::from(link.producer_row) + 1));
            for limb in link.producer.limbs {
                if let TupleLimb::Cell(cell) = limb {
                    assert_eq!(cell.row, link.producer_row);
                }
            }
            for limb in link.consumer.limbs {
                if let TupleLimb::Cell(cell) = limb {
                    assert_eq!(cell.row, link.consumer_row);
                }
            }
        }
    }

    #[test]
    fn padding_is_zero_dead_and_absent_from_copy_selectors() {
        let (public, witness) = fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        let layout = copy_layout();
        for row in 0..ALLOCATED_PERMUTATION_ROWS {
            if is_poseidon_padding_row(row) {
                assert!(!is_poseidon_active_row(row));
                assert!(layout.producer_link(row).is_none());
                assert!(layout.consumer_link(row).is_none());
                assert!((0..STATE_AND_INTERFACE_COLUMNS)
                    .all(|column| trace.c1[column][row] == M31::ZERO));
            }
        }

        let padding_row = DEAD_ROW_START_IN_BLOCK;
        trace.c1[0][padding_row] = M31::ONE;
        assert_eq!(
            validate_spend_trace_v4(&public, &trace),
            Err(TraceValidationError::NonZeroPadding {
                row: padding_row as u16,
                column: 0,
            })
        );
        assert!(layout.producer_link(padding_row).is_none());
        assert!(layout.consumer_link(padding_row).is_none());
    }

    #[test]
    fn all_absorptions_are_committed_bound_and_replayed_from_row_11() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let layout = copy_layout();
        for block in 0..PERMUTATION_COUNT {
            let row = block * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK;
            let schedule = permutation_block_schedule(block).unwrap();
            assert!(is_absorption_row(row));
            assert_eq!(
                layout.consumer_link(row).map(|link| link.kind),
                Some(CopyLinkKind::Absorption)
            );
            assert!((usize::from(schedule.absorbed_len)..RATE)
                .all(|column| trace.c1[column][row] == M31::ZERO));
            if !has_carry_payload(block) {
                assert!((RATE..POSEIDON2_WIDTH).all(|column| trace.c1[column][row] == M31::ZERO));
            }
            assert!((POSEIDON2_WIDTH..STATE_AND_INTERFACE_COLUMNS)
                .all(|column| trace.c1[column][row] == M31::ZERO));
        }

        let mut corrupted = trace.clone();
        let row = ABSORPTION_ROW_IN_BLOCK;
        corrupted.c1[0][row] = corrupted.c1[0][row].add(M31::ONE);
        assert_eq!(
            validate_spend_trace_v4(&public, &corrupted),
            Err(TraceValidationError::PermutationReplay { block: 0, round: 0 })
        );

        let mut tail_corrupted = trace;
        let short_block = 3usize;
        let row = short_block * BLOCK_ROWS + ABSORPTION_ROW_IN_BLOCK;
        tail_corrupted.c1[2][row] = M31::ONE;
        assert_eq!(
            validate_spend_trace_v4(&public, &tail_corrupted),
            Err(TraceValidationError::NonZeroAbsorptionTail {
                block: short_block as u8,
                column: 2,
            })
        );
    }

    #[test]
    fn witness_public_and_conditional_absorption_bindings_have_teeth() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let aux = witness_aux_layout();

        let mut witness_corrupted = trace.clone();
        let cell = aux.nullifier_key[0];
        witness_corrupted.c1[cell.column as usize][cell.row as usize] =
            witness_corrupted.c1[cell.column as usize][cell.row as usize].add(M31::ONE);
        assert!(matches!(
            validate_spend_trace_v4(&public, &witness_corrupted),
            Err(TraceValidationError::SourceRelation { .. })
        ));

        let mut wrong_public = public.clone();
        wrong_public.output_commitment[0] = wrong_public.output_commitment[0].add(M31::ONE);
        assert!(matches!(
            validate_spend_trace_v4(&wrong_public, &trace),
            Err(TraceValidationError::PublicBinding)
        ));

        let mut conditional_corrupted = trace;
        let level = 7usize;
        let sibling = aux.merkle_siblings[level][0];
        conditional_corrupted.c1[sibling.column as usize][sibling.row as usize] =
            conditional_corrupted.c1[sibling.column as usize][sibling.row as usize].add(M31::ONE);
        assert!(matches!(
            validate_spend_trace_v4(&public, &conditional_corrupted),
            Err(TraceValidationError::MerkleSelection { .. })
        ));
    }

    #[test]
    fn initial_sponge_domain_and_length_are_verifier_derived() {
        let (public, witness) = fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        let note_first_block = 1usize;
        let row = note_first_block * BLOCK_ROWS;
        trace.c1[RATE + 1][row] = trace.c1[RATE + 1][row].add(M31::ONE);
        assert_eq!(
            validate_spend_trace_v4(&public, &trace),
            Err(TraceValidationError::InitialSpongeState {
                block: note_first_block as u8,
            })
        );
    }
}
