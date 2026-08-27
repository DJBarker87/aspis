//! Production-inactive source contract for the staged Pool pair-tree profile.
//!
//! This module freezes the three design gates which must be source-bound
//! before the profile can be enabled by verifier dispatch:
//!
//! * an empty second slot is algebraically distinguished from an occupied one;
//! * the historical membership anchor is separate from the exact live append
//!   snapshot, whose complete account-derived image is absorbed after the
//!   Stage-A challenges; and
//! * the 1,024-row trace allocates exactly 976 semantic rows and retains the
//!   deployed degree-27 cap.
//!
//! Nothing in this module adds a dispatch tag, registry release, account
//! decoder, prover, verifier, or state mutation path.

use aspis_core::field::{M31, P};

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest};

use super::{pool_v1_tree_parent, POOL_V1_TREE_DEPTH};

pub const POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION: u8 = 1;
pub const POOL_V1_PAIR_TREE_DEPTH: usize = POOL_V1_TREE_DEPTH;
pub const POOL_V1_PAIR_NOTE_DEPTH: usize = POOL_V1_PAIR_TREE_DEPTH + 1;
pub const POOL_V1_PAIR_CAPACITY: u64 = 1u64 << POOL_V1_PAIR_TREE_DEPTH;
pub const POOL_V1_PAIR_NOTE_SLOT_CAPACITY: u64 = 2 * POOL_V1_PAIR_CAPACITY;
pub const POOL_V1_PAIR_SECOND_SENTINEL_LANE: usize = 7;

/// Explicitly distinct from the ordinary single-note Pool V1 storage format.
/// A state account may use one format or the other; no profile may reinterpret
/// an existing root across this boundary.
pub const POOL_V1_PAIR_TREE_FORMAT_BINDING: [u8; 32] = [
    b'A',
    b'S',
    b'P',
    b'P',
    b'A',
    b'I',
    b'R',
    b'1',
    POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
    POOL_V1_PAIR_TREE_DEPTH as u8,
    POOL_V1_PAIR_NOTE_DEPTH as u8,
    POOL_V1_PAIR_SECOND_SENTINEL_LANE as u8,
    1, // first slot is always occupied
    1, // second occupancy is an algebraic zero test
    1, // empty second commitment is the all-zero digest
    1, // spend relation checks selected occupancy equals one
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairLeafErrorV1 {
    NonCanonicalCommitment,
    NonCanonicalOccupancy,
    NonCanonicalInverse,
    OccupancyNotBoolean,
    SentinelInverseMismatch,
    EmptyInverseNonZero,
    EmptyCommitmentNonZero,
    OccupiedSentinelZero,
    SelectedSlotEmpty,
}

/// Private algebraic witness for one public pair-tree leaf.
///
/// The public leaf digest commits only to the ordered pair of complete note
/// commitments. `second_occupied` and `second_occupancy_inverse` are relation
/// witnesses which prove whether that already-committed second digest is the
/// canonical empty digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairLeafWitnessV1 {
    pub first_commitment: Digest,
    pub second_occupied: M31,
    pub second_commitment: Digest,
    pub second_occupancy_inverse: M31,
}

#[inline]
fn digest_is_canonical(value: &Digest) -> bool {
    value.iter().all(|limb| limb.0 < P)
}

impl PoolV1PairLeafWitnessV1 {
    #[inline]
    pub fn second_sentinel(&self) -> M31 {
        self.second_commitment[POOL_V1_PAIR_SECOND_SENTINEL_LANE]
    }

    /// Check the literal field equations mirrored by
    /// `V7PairLeafOccupancy.PairLeaf.Valid`.
    pub fn validate(&self) -> Result<(), PoolV1PairLeafErrorV1> {
        if !digest_is_canonical(&self.first_commitment)
            || !digest_is_canonical(&self.second_commitment)
        {
            return Err(PoolV1PairLeafErrorV1::NonCanonicalCommitment);
        }
        if self.second_occupied.0 >= P {
            return Err(PoolV1PairLeafErrorV1::NonCanonicalOccupancy);
        }
        if self.second_occupancy_inverse.0 >= P {
            return Err(PoolV1PairLeafErrorV1::NonCanonicalInverse);
        }

        let one_minus_occupied = M31::ONE.sub(self.second_occupied);
        if self.second_occupied.mul(self.second_occupied.sub(M31::ONE)) != M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::OccupancyNotBoolean);
        }
        if self.second_sentinel().mul(self.second_occupancy_inverse) != self.second_occupied {
            return Err(PoolV1PairLeafErrorV1::SentinelInverseMismatch);
        }
        if one_minus_occupied.mul(self.second_occupancy_inverse) != M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::EmptyInverseNonZero);
        }
        if self
            .second_commitment
            .iter()
            .any(|limb| one_minus_occupied.mul(*limb) != M31::ZERO)
        {
            return Err(PoolV1PairLeafErrorV1::EmptyCommitmentNonZero);
        }
        if self.second_occupied == M31::ONE && self.second_sentinel() == M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::OccupiedSentinelZero);
        }
        Ok(())
    }

    /// Exact one-permutation pair-leaf preimage. Occupancy metadata is not an
    /// uncommitted public convention: validity makes it the zero test of the
    /// committed second digest.
    #[inline]
    pub fn leaf_digest(&self) -> Result<Digest, PoolV1PairLeafErrorV1> {
        self.validate()?;
        Ok(pool_v1_tree_parent(
            &self.first_commitment,
            &self.second_commitment,
        ))
    }

    #[inline]
    pub fn selected_commitment(&self, second_slot: bool) -> &Digest {
        if second_slot {
            &self.second_commitment
        } else {
            &self.first_commitment
        }
    }

    /// Relation-level spend gate. Merkle membership alone is insufficient.
    pub fn require_selected_spendable(
        &self,
        second_slot: bool,
    ) -> Result<(), PoolV1PairLeafErrorV1> {
        self.validate()?;
        if second_slot && self.second_occupied != M31::ONE {
            return Err(PoolV1PairLeafErrorV1::SelectedSlotEmpty);
        }
        Ok(())
    }

    pub fn single_output(first_commitment: Digest) -> Result<Self, PoolV1PairLeafErrorV1> {
        let result = Self {
            first_commitment,
            second_occupied: M31::ZERO,
            second_commitment: [M31::ZERO; 8],
            second_occupancy_inverse: M31::ZERO,
        };
        result.validate()?;
        Ok(result)
    }

    /// Build a two-output witness. A zero sentinel is a retry condition for
    /// note-salt generation, never an empty-slot hash/preimage assumption.
    pub fn two_outputs(
        first_commitment: Digest,
        second_commitment: Digest,
    ) -> Result<Self, PoolV1PairLeafErrorV1> {
        if !digest_is_canonical(&first_commitment) || !digest_is_canonical(&second_commitment) {
            return Err(PoolV1PairLeafErrorV1::NonCanonicalCommitment);
        }
        let sentinel = second_commitment[POOL_V1_PAIR_SECOND_SENTINEL_LANE];
        if sentinel == M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::OccupiedSentinelZero);
        }
        let result = Self {
            first_commitment,
            second_occupied: M31::ONE,
            second_commitment,
            second_occupancy_inverse: sentinel.inv(),
        };
        result.validate()?;
        Ok(result)
    }
}

// Exact candidate trace geometry.

pub const POOL_V1_PAIR_TRACE_ROWS: usize = 1 << 10;
pub const POOL_V1_PAIR_TRACE_COLUMNS: usize = 16;
pub const POOL_V1_PAIR_TRACE_BLOCK_ROWS: usize = 16;
pub const POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS: usize = 34;
pub const POOL_V1_PAIR_LATE_APPEND_POSEIDON_BLOCKS: usize = 20;
pub const POOL_V1_PAIR_POSEIDON_BLOCKS: usize =
    POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS + POOL_V1_PAIR_LATE_APPEND_POSEIDON_BLOCKS;
pub const POOL_V1_PAIR_PRIVATE_DIRECTIONS: usize = 21;
pub const POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK: usize = 4;
pub const POOL_V1_PAIR_PATH_AUX_BLOCKS: usize = 6;
pub const POOL_V1_PAIR_VALUE_AUX_BLOCKS: usize = 1;
pub const POOL_V1_PAIR_ALLOCATED_BLOCKS: usize =
    POOL_V1_PAIR_POSEIDON_BLOCKS + POOL_V1_PAIR_PATH_AUX_BLOCKS + POOL_V1_PAIR_VALUE_AUX_BLOCKS;
pub const POOL_V1_PAIR_ALLOCATED_ROWS: usize =
    POOL_V1_PAIR_ALLOCATED_BLOCKS * POOL_V1_PAIR_TRACE_BLOCK_ROWS;
pub const POOL_V1_PAIR_UNALLOCATED_SEMANTIC_ROWS: usize =
    POOL_V1_PAIR_TRACE_ROWS - POOL_V1_PAIR_ALLOCATED_ROWS;
pub const POOL_V1_PAIR_POSEIDON_ROW_END: usize =
    POOL_V1_PAIR_POSEIDON_BLOCKS * POOL_V1_PAIR_TRACE_BLOCK_ROWS;
pub const POOL_V1_PAIR_PATH_AUX_ROW_START: usize = POOL_V1_PAIR_POSEIDON_ROW_END;
pub const POOL_V1_PAIR_PATH_AUX_ROW_END: usize =
    POOL_V1_PAIR_PATH_AUX_ROW_START + POOL_V1_PAIR_PATH_AUX_BLOCKS * POOL_V1_PAIR_TRACE_BLOCK_ROWS;
pub const POOL_V1_PAIR_VALUE_AUX_ROW_START: usize = POOL_V1_PAIR_PATH_AUX_ROW_END;
pub const POOL_V1_PAIR_SEMANTIC_ROW_END: usize = POOL_V1_PAIR_ALLOCATED_ROWS;
pub const POOL_V1_PAIR_OCCUPANCY_AUX_ROW: usize = POOL_V1_PAIR_VALUE_AUX_ROW_START + 9;

pub const POOL_V1_PAIR_POSEIDON_INTRINSIC_DEGREE: usize = 25;
pub const POOL_V1_PAIR_NEW_RESIDUAL_MAX_INTRINSIC_DEGREE: usize = 2;
pub const POOL_V1_PAIR_SELECTOR_DEGREE_OVERHEAD: usize = 1;
pub const POOL_V1_PAIR_ZEROCHECK_DEGREE_OVERHEAD: usize = 1;
pub const POOL_V1_PAIR_MAX_DEPLOYED_DEGREE: usize = POOL_V1_PAIR_POSEIDON_INTRINSIC_DEGREE
    + POOL_V1_PAIR_SELECTOR_DEGREE_OVERHEAD
    + POOL_V1_PAIR_ZEROCHECK_DEGREE_OVERHEAD;

/// Root roles are intentionally distinct. The historical anchor may be any
/// retained pair-tree root accepted by history; the live append snapshot must
/// be the exact current Pool account image at execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairHistoricalMembershipAnchorV1 {
    pub sequence: u64,
    pub root: Digest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PoolV1PairTranscriptStepV1 {
    StableStatement = 0,
    StageARoot = 1,
    Lambda = 2,
    Chi = 3,
    LiveAppendSnapshot = 4,
    StageBRoot = 5,
    BatchingChallenges = 6,
}

pub const POOL_V1_PAIR_STAGED_TRANSCRIPT_PREFIX_V1: [PoolV1PairTranscriptStepV1; 7] = [
    PoolV1PairTranscriptStepV1::StableStatement,
    PoolV1PairTranscriptStepV1::StageARoot,
    PoolV1PairTranscriptStepV1::Lambda,
    PoolV1PairTranscriptStepV1::Chi,
    PoolV1PairTranscriptStepV1::LiveAppendSnapshot,
    PoolV1PairTranscriptStepV1::StageBRoot,
    PoolV1PairTranscriptStepV1::BatchingChallenges,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairPoseidonBlockRoleV1 {
    OwnerKey,
    InputNote(u8),
    InputPair,
    InputTreePath(u8),
    Nullifier(u8),
    RecipientNote(u8),
    ChangeNote(u8),
    OutputPair,
    AppendTreePath(u8),
}

pub const fn pool_v1_pair_poseidon_block_role_v1(
    block: usize,
) -> Option<PoolV1PairPoseidonBlockRoleV1> {
    match block {
        0 => Some(PoolV1PairPoseidonBlockRoleV1::OwnerKey),
        1..=3 => Some(PoolV1PairPoseidonBlockRoleV1::InputNote((block - 1) as u8)),
        4 => Some(PoolV1PairPoseidonBlockRoleV1::InputPair),
        5..=24 => Some(PoolV1PairPoseidonBlockRoleV1::InputTreePath(
            (block - 5) as u8,
        )),
        25..=26 => Some(PoolV1PairPoseidonBlockRoleV1::Nullifier((block - 25) as u8)),
        27..=29 => Some(PoolV1PairPoseidonBlockRoleV1::RecipientNote(
            (block - 27) as u8,
        )),
        30..=32 => Some(PoolV1PairPoseidonBlockRoleV1::ChangeNote(
            (block - 30) as u8,
        )),
        33 => Some(PoolV1PairPoseidonBlockRoleV1::OutputPair),
        34..=53 => Some(PoolV1PairPoseidonBlockRoleV1::AppendTreePath(
            (block - 34) as u8,
        )),
        _ => None,
    }
}

pub const fn pool_v1_pair_path_base_row_v1(level: usize) -> Option<usize> {
    if level >= POOL_V1_PAIR_PRIVATE_DIRECTIONS {
        return None;
    }
    Some(
        POOL_V1_PAIR_PATH_AUX_ROW_START
            + (level / POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK) * POOL_V1_PAIR_TRACE_BLOCK_ROWS
            + 2 * (level % POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK),
    )
}

const _: () = assert!(POOL_V1_PAIR_TREE_DEPTH == 20);
const _: () = assert!(POOL_V1_PAIR_NOTE_DEPTH == 21);
const _: () = assert!(POOL_V1_PAIR_POSEIDON_BLOCKS == 54);
const _: () = assert!(POOL_V1_PAIR_PATH_AUX_BLOCKS == 6);
const _: () = assert!(POOL_V1_PAIR_ALLOCATED_BLOCKS == 61);
const _: () = assert!(POOL_V1_PAIR_POSEIDON_ROW_END == 864);
const _: () = assert!(POOL_V1_PAIR_PATH_AUX_ROW_END == 960);
const _: () = assert!(POOL_V1_PAIR_VALUE_AUX_ROW_START == 960);
const _: () = assert!(POOL_V1_PAIR_OCCUPANCY_AUX_ROW == 969);
const _: () = assert!(POOL_V1_PAIR_SEMANTIC_ROW_END == 976);
const _: () = assert!(POOL_V1_PAIR_UNALLOCATED_SEMANTIC_ROWS == 48);
const _: () = assert!(POOL_V1_PAIR_NEW_RESIDUAL_MAX_INTRINSIC_DEGREE <= 2);
const _: () = assert!(POOL_V1_PAIR_MAX_DEPLOYED_DEGREE == 27);

// Exact late-bound live snapshot.

pub const POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC: [u8; 8] = *b"ASPLIVE1";
pub const POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION: u8 = 1;
pub const POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES: usize = 800;
pub const POOL_V1_PAIR_LIVE_SNAPSHOT_TRANSCRIPT_DOMAIN: &[u8] =
    b"aspis:pool-v1:pair-tree:late-live-snapshot:after-lambda-chi:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairLiveSnapshotV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub sequence: u64,
    pub next_pair_index: u64,
    pub current_root: Digest,
    pub frontier: [Digest; POOL_V1_PAIR_TREE_DEPTH],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairLiveSnapshotErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongFormatBinding,
    NonZeroReserved,
    ZeroRequiredBinding,
    SequenceIndexMismatch,
    TreeFull,
    NonCanonicalDigest,
}

fn validate_pool_v1_pair_live_snapshot_v1(
    snapshot: &PoolV1PairLiveSnapshotV1,
) -> Result<(), PoolV1PairLiveSnapshotErrorV1> {
    if snapshot.pool == [0u8; 32] || snapshot.deployment_domain == [0u8; 32] {
        return Err(PoolV1PairLiveSnapshotErrorV1::ZeroRequiredBinding);
    }
    if snapshot.sequence != snapshot.next_pair_index {
        return Err(PoolV1PairLiveSnapshotErrorV1::SequenceIndexMismatch);
    }
    if snapshot.next_pair_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1PairLiveSnapshotErrorV1::TreeFull);
    }
    if !digest_is_canonical(&snapshot.current_root)
        || snapshot
            .frontier
            .iter()
            .any(|node| !digest_is_canonical(node))
    {
        return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);
    }
    Ok(())
}

pub fn encode_pool_v1_pair_live_snapshot_v1(
    snapshot: &PoolV1PairLiveSnapshotV1,
    output: &mut [u8],
) -> Result<(), PoolV1PairLiveSnapshotErrorV1> {
    if output.len() != POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES {
        return Err(PoolV1PairLiveSnapshotErrorV1::WrongLength);
    }
    validate_pool_v1_pair_live_snapshot_v1(snapshot)?;

    output.fill(0);
    output[..8].copy_from_slice(&POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC);
    output[8] = POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION;
    output[16..48].copy_from_slice(&POOL_V1_PAIR_TREE_FORMAT_BINDING);
    output[48..80].copy_from_slice(&snapshot.pool);
    output[80..112].copy_from_slice(&snapshot.deployment_domain);
    output[112..120].copy_from_slice(&snapshot.sequence.to_le_bytes());
    output[120..128].copy_from_slice(&snapshot.next_pair_index.to_le_bytes());
    output[128..160].copy_from_slice(&encode_digest_canonical(&snapshot.current_root));
    for (level, node) in snapshot.frontier.iter().enumerate() {
        let start = 160 + 32 * level;
        output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    }
    Ok(())
}

pub fn decode_pool_v1_pair_live_snapshot_v1(
    bytes: &[u8],
) -> Result<PoolV1PairLiveSnapshotV1, PoolV1PairLiveSnapshotErrorV1> {
    if bytes.len() != POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES {
        return Err(PoolV1PairLiveSnapshotErrorV1::WrongLength);
    }
    if bytes[..8] != POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC {
        return Err(PoolV1PairLiveSnapshotErrorV1::WrongMagic);
    }
    if bytes[8] != POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION {
        return Err(PoolV1PairLiveSnapshotErrorV1::WrongVersion);
    }
    if bytes[9..16].iter().any(|byte| *byte != 0) {
        return Err(PoolV1PairLiveSnapshotErrorV1::NonZeroReserved);
    }
    if bytes[16..48] != POOL_V1_PAIR_TREE_FORMAT_BINDING {
        return Err(PoolV1PairLiveSnapshotErrorV1::WrongFormatBinding);
    }
    let current_root = decode_digest_canonical(bytes[128..160].try_into().unwrap())
        .map_err(|_| PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest)?;
    let mut frontier = [[M31::ZERO; 8]; POOL_V1_PAIR_TREE_DEPTH];
    for (level, node) in frontier.iter_mut().enumerate() {
        let start = 160 + 32 * level;
        *node = decode_digest_canonical(bytes[start..start + 32].try_into().unwrap())
            .map_err(|_| PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest)?;
    }
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: bytes[48..80].try_into().unwrap(),
        deployment_domain: bytes[80..112].try_into().unwrap(),
        sequence: u64::from_le_bytes(bytes[112..120].try_into().unwrap()),
        next_pair_index: u64::from_le_bytes(bytes[120..128].try_into().unwrap()),
        current_root,
        frontier,
    };
    validate_pool_v1_pair_live_snapshot_v1(&snapshot)?;
    Ok(snapshot)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + lane as u32 + 1))
    }

    #[test]
    fn empty_and_occupied_slots_are_algebraically_distinct() {
        let first = digest(10);
        let empty = PoolV1PairLeafWitnessV1::single_output(first).unwrap();
        assert_eq!(empty.validate(), Ok(()));
        assert_eq!(
            empty.require_selected_spendable(true),
            Err(PoolV1PairLeafErrorV1::SelectedSlotEmpty)
        );
        assert_eq!(
            empty.leaf_digest().unwrap(),
            pool_v1_tree_parent(&first, &[M31::ZERO; 8])
        );

        let occupied = PoolV1PairLeafWitnessV1::two_outputs(first, digest(100)).unwrap();
        assert_eq!(occupied.second_occupied, M31::ONE);
        assert_eq!(occupied.validate(), Ok(()));
        assert_eq!(occupied.require_selected_spendable(true), Ok(()));
    }

    #[test]
    fn occupied_zero_sentinel_is_a_retry_not_an_empty_hash_assumption() {
        let mut second = digest(100);
        second[POOL_V1_PAIR_SECOND_SENTINEL_LANE] = M31::ZERO;
        assert_eq!(
            PoolV1PairLeafWitnessV1::two_outputs(digest(10), second),
            Err(PoolV1PairLeafErrorV1::OccupiedSentinelZero)
        );
    }

    #[test]
    fn occupancy_cannot_be_changed_without_invalidating_the_same_pair_preimage() {
        let occupied = PoolV1PairLeafWitnessV1::two_outputs(digest(10), digest(100)).unwrap();
        let mut claimed_empty = occupied;
        claimed_empty.second_occupied = M31::ZERO;
        claimed_empty.second_occupancy_inverse = M31::ZERO;
        assert_eq!(
            claimed_empty.validate(),
            Err(PoolV1PairLeafErrorV1::EmptyCommitmentNonZero)
        );
    }

    #[test]
    fn exact_trace_boundaries_and_degree_cap_are_source_frozen() {
        assert_eq!(
            pool_v1_pair_poseidon_block_role_v1(0),
            Some(PoolV1PairPoseidonBlockRoleV1::OwnerKey)
        );
        assert_eq!(
            pool_v1_pair_poseidon_block_role_v1(33),
            Some(PoolV1PairPoseidonBlockRoleV1::OutputPair)
        );
        assert_eq!(
            pool_v1_pair_poseidon_block_role_v1(53),
            Some(PoolV1PairPoseidonBlockRoleV1::AppendTreePath(19))
        );
        assert_eq!(pool_v1_pair_poseidon_block_role_v1(54), None);
        assert_eq!(pool_v1_pair_path_base_row_v1(0), Some(864));
        assert_eq!(pool_v1_pair_path_base_row_v1(20), Some(944));
        assert_eq!(pool_v1_pair_path_base_row_v1(21), None);
        assert_eq!(POOL_V1_PAIR_SEMANTIC_ROW_END, 976);
        assert_eq!(POOL_V1_PAIR_UNALLOCATED_SEMANTIC_ROWS, 48);
        assert_eq!(POOL_V1_PAIR_MAX_DEPLOYED_DEGREE, 27);
        assert_eq!(
            POOL_V1_PAIR_STAGED_TRANSCRIPT_PREFIX_V1[4],
            PoolV1PairTranscriptStepV1::LiveAppendSnapshot
        );
    }

    #[test]
    fn live_snapshot_encoding_is_exact_and_rejects_stale_shape() {
        let snapshot = PoolV1PairLiveSnapshotV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            sequence: 73,
            next_pair_index: 73,
            current_root: digest(300),
            frontier: core::array::from_fn(|level| digest(400 + 10 * level as u32)),
        };
        let mut encoded = [0u8; POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
        encode_pool_v1_pair_live_snapshot_v1(&snapshot, &mut encoded).unwrap();
        assert_eq!(&encoded[..8], &POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC);
        assert_eq!(&encoded[16..48], &POOL_V1_PAIR_TREE_FORMAT_BINDING);
        assert_eq!(
            u64::from_le_bytes(encoded[112..120].try_into().unwrap()),
            73
        );
        assert_eq!(
            u64::from_le_bytes(encoded[120..128].try_into().unwrap()),
            73
        );
        assert_eq!(
            &encoded[768..800],
            &encode_digest_canonical(&snapshot.frontier[19])
        );
        assert_eq!(decode_pool_v1_pair_live_snapshot_v1(&encoded), Ok(snapshot));

        let mut stale = snapshot;
        stale.sequence += 1;
        assert_eq!(
            encode_pool_v1_pair_live_snapshot_v1(&stale, &mut encoded),
            Err(PoolV1PairLiveSnapshotErrorV1::SequenceIndexMismatch)
        );
    }
}
