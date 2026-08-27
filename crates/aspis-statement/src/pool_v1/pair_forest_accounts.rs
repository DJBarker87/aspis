//! Production-inactive account formats for the eight-lane pair forest.
//!
//! These codecs deliberately do not reinterpret the existing single-tree Pair
//! Pool formats.  The master is the stable per-mint identity and policy
//! namespace; each lane owns an independent pair-tree image; immutable
//! checkpoints bind one coherent vector of eight lane sequences to a supplied
//! global root.  Computing that root remains outside this plumbing module.

use aspis_core::field::P;

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest};

use super::{
    decode_pool_identity_v1, decode_verifier_policy_v1, encode_pool_identity_v1,
    encode_verifier_policy_v1, validate_verifier_policy_v1, IncrementalMerkleTreeV1,
    PoolIdentityV1, PoolV1TreeError, VerifierPolicyV1, POOL_V1_DIGEST_ENCODING_VERSION,
    POOL_V1_IDENTITY_BYTES, POOL_V1_PAIR_CAPACITY, POOL_V1_TREE_DEPTH,
    POOL_V1_TREE_STATE_ACCOUNT_BYTES, POOL_V1_VERIFIER_POLICY_BYTES,
};

pub const POOL_V1_PAIR_FOREST_LANE_COUNT: usize = 8;
pub const POOL_V1_PAIR_FOREST_ALL_LANES_MASK: u8 = 0xff;

pub const POOL_V1_PAIR_FOREST_MASTER_MAGIC: [u8; 4] = *b"ASM8";
pub const POOL_V1_PAIR_FOREST_MASTER_VERSION: u8 = 1;
pub const POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES: usize = 384;

pub const POOL_V1_PAIR_FOREST_LANE_MAGIC: [u8; 4] = *b"ASL8";
pub const POOL_V1_PAIR_FOREST_LANE_VERSION: u8 = 1;
pub const POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES: usize = 80;
pub const POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES: usize =
    POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES + POOL_V1_TREE_STATE_ACCOUNT_BYTES;

pub const POOL_V1_PAIR_FOREST_CHECKPOINT_MAGIC: [u8; 4] = *b"ASC8";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION: u8 = 1;
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES: usize = 192;

/// Separate binding for the account forest.  Existing V1 single-tree images
/// must fail closed rather than acquire these semantics by reinterpretation.
pub const POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING: [u8; 32] = [
    b'A',
    b'S',
    b'P',
    b'I',
    b'S',
    b'F',
    b'O',
    b'R',
    b'E',
    b'S',
    b'T',
    b'8',
    POOL_V1_PAIR_FOREST_MASTER_VERSION,
    POOL_V1_PAIR_FOREST_LANE_VERSION,
    POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION,
    POOL_V1_PAIR_FOREST_LANE_COUNT as u8,
    POOL_V1_DIGEST_ENCODING_VERSION,
    POOL_V1_TREE_DEPTH as u8,
    1, // one pair append advances one lane sequence
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

const MASTER_NEXT_CHECKPOINT_OFFSET: usize = 40;
const MASTER_INITIALIZED_MASK_OFFSET: usize = 48;
const MASTER_HAS_CHECKPOINT_OFFSET: usize = 49;
const MASTER_IDENTITY_OFFSET: usize = 64;
const MASTER_POLICY_OFFSET: usize = MASTER_IDENTITY_OFFSET + POOL_V1_IDENTITY_BYTES;
const MASTER_LAST_SEQUENCES_OFFSET: usize = 320;

const LANE_MASTER_OFFSET: usize = 40;
const LANE_TREE_OFFSET: usize = POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES;

const CHECKPOINT_MASTER_OFFSET: usize = 8;
const CHECKPOINT_DOMAIN_OFFSET: usize = 40;
const CHECKPOINT_SEQUENCE_OFFSET: usize = 72;
const CHECKPOINT_GLOBAL_ROOT_OFFSET: usize = 80;
const CHECKPOINT_LANE_SEQUENCES_OFFSET: usize = 112;

const _: () = assert!(MASTER_POLICY_OFFSET + POOL_V1_VERIFIER_POLICY_BYTES == 312);
const _: () = assert!(POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES == 768);
const _: () = assert!(CHECKPOINT_LANE_SEQUENCES_OFFSET + 8 * 8 == 176);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestAccountErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongLaneCount,
    WrongDigestEncoding,
    WrongDepth,
    WrongFormatBinding,
    NonZeroReserved,
    ZeroRequiredBinding,
    InvalidBoolean,
    InvalidMasterState,
    InvalidLane,
    LaneMasterMismatch,
    LaneOrderMismatch,
    LaneSequenceDecreased,
    DuplicateCheckpoint,
    CheckpointSequenceOverflow,
    NonCanonicalDigest,
    Identity,
    Policy,
    Tree(PoolV1TreeError),
}

impl From<PoolV1TreeError> for PoolV1PairForestAccountErrorV1 {
    fn from(error: PoolV1TreeError) -> Self {
        Self::Tree(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestMasterV1 {
    pub identity: PoolIdentityV1,
    pub verifier_policy: VerifierPolicyV1,
    pub initialized_lane_mask: u8,
    pub has_checkpoint: bool,
    /// Sequence assigned to the next immutable checkpoint account.
    pub next_checkpoint_sequence: u64,
    pub last_checkpoint_lane_sequences: [u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestLaneStateV1 {
    pub master: [u8; 32],
    pub lane_id: u8,
    pub tree: IncrementalMerkleTreeV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestCheckpointV1 {
    pub master: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub checkpoint_sequence: u64,
    pub global_root: Digest,
    pub lane_sequences: [u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestCheckpointPlanV1 {
    pub next_master: PoolV1PairForestMasterV1,
    pub checkpoint: PoolV1PairForestCheckpointV1,
}

#[inline]
fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

#[inline]
fn first_canonical_byte(digest: &Digest) -> u8 {
    encode_digest_canonical(digest)[0]
}

/// Canonical output lane for both outputs of a private spend.
#[inline]
pub fn pool_v1_pair_forest_output_lane_v1(
    nullifier: &Digest,
) -> Result<u8, PoolV1PairForestAccountErrorV1> {
    if !digest_is_canonical(nullifier) {
        return Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest);
    }
    Ok(first_canonical_byte(nullifier) & 7)
}

/// Canonical lane for a public deposit commitment.
#[inline]
pub fn pool_v1_pair_forest_deposit_lane_v1(
    commitment: &Digest,
) -> Result<u8, PoolV1PairForestAccountErrorV1> {
    if !digest_is_canonical(commitment) {
        return Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest);
    }
    Ok(first_canonical_byte(commitment) & 7)
}

fn validate_master(
    master: &PoolV1PairForestMasterV1,
) -> Result<(), PoolV1PairForestAccountErrorV1> {
    if master.identity.pool == [0u8; 32]
        || master.identity.asset_mint == [0u8; 32]
        || master.identity.token_program == [0u8; 32]
        || master.identity.deployment_domain == [0u8; 32]
    {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    validate_verifier_policy_v1(&master.verifier_policy)
        .map_err(|_| PoolV1PairForestAccountErrorV1::Policy)?;
    if master
        .last_checkpoint_lane_sequences
        .iter()
        .any(|sequence| *sequence > POOL_V1_PAIR_CAPACITY)
    {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    if (!master.has_checkpoint
        && (master.next_checkpoint_sequence != 0
            || master.last_checkpoint_lane_sequences != [0u64; 8]))
        || (master.has_checkpoint && master.next_checkpoint_sequence == 0)
    {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    Ok(())
}

pub fn encode_pool_v1_pair_forest_master_v1(
    master: &PoolV1PairForestMasterV1,
) -> Result<[u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES], PoolV1PairForestAccountErrorV1> {
    validate_master(master)?;
    let mut output = [0u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_MASTER_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_MASTER_VERSION;
    output[5] = POOL_V1_PAIR_FOREST_LANE_COUNT as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[8..40].copy_from_slice(&POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING);
    output[MASTER_NEXT_CHECKPOINT_OFFSET..MASTER_INITIALIZED_MASK_OFFSET]
        .copy_from_slice(&master.next_checkpoint_sequence.to_le_bytes());
    output[MASTER_INITIALIZED_MASK_OFFSET] = master.initialized_lane_mask;
    output[MASTER_HAS_CHECKPOINT_OFFSET] = u8::from(master.has_checkpoint);
    output[MASTER_IDENTITY_OFFSET..MASTER_POLICY_OFFSET]
        .copy_from_slice(&encode_pool_identity_v1(&master.identity));
    output[MASTER_POLICY_OFFSET..312].copy_from_slice(
        &encode_verifier_policy_v1(&master.verifier_policy)
            .map_err(|_| PoolV1PairForestAccountErrorV1::Policy)?,
    );
    for (lane, sequence) in master.last_checkpoint_lane_sequences.iter().enumerate() {
        let start = MASTER_LAST_SEQUENCES_OFFSET + 8 * lane;
        output[start..start + 8].copy_from_slice(&sequence.to_le_bytes());
    }
    Ok(output)
}

pub fn decode_pool_v1_pair_forest_master_v1(
    bytes: &[u8],
) -> Result<PoolV1PairForestMasterV1, PoolV1PairForestAccountErrorV1> {
    if bytes.len() != POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES {
        return Err(PoolV1PairForestAccountErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_MASTER_MAGIC {
        return Err(PoolV1PairForestAccountErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_MASTER_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8 {
        return Err(PoolV1PairForestAccountErrorV1::WrongLaneCount);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 || bytes[50..64].iter().any(|byte| *byte != 0) || bytes[312..320] != [0u8; 8] {
        return Err(PoolV1PairForestAccountErrorV1::NonZeroReserved);
    }
    if bytes[8..40] != POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING {
        return Err(PoolV1PairForestAccountErrorV1::WrongFormatBinding);
    }
    let has_checkpoint = match bytes[MASTER_HAS_CHECKPOINT_OFFSET] {
        0 => false,
        1 => true,
        _ => return Err(PoolV1PairForestAccountErrorV1::InvalidBoolean),
    };
    let identity = decode_pool_identity_v1(&bytes[MASTER_IDENTITY_OFFSET..MASTER_POLICY_OFFSET])
        .map_err(|_| PoolV1PairForestAccountErrorV1::Identity)?;
    let verifier_policy = decode_verifier_policy_v1(&bytes[MASTER_POLICY_OFFSET..312])
        .map_err(|_| PoolV1PairForestAccountErrorV1::Policy)?;
    let mut last_checkpoint_lane_sequences = [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for (lane, sequence) in last_checkpoint_lane_sequences.iter_mut().enumerate() {
        let start = MASTER_LAST_SEQUENCES_OFFSET + 8 * lane;
        *sequence = u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap());
    }
    let master = PoolV1PairForestMasterV1 {
        identity,
        verifier_policy,
        initialized_lane_mask: bytes[MASTER_INITIALIZED_MASK_OFFSET],
        has_checkpoint,
        next_checkpoint_sequence: u64::from_le_bytes(
            bytes[MASTER_NEXT_CHECKPOINT_OFFSET..MASTER_INITIALIZED_MASK_OFFSET]
                .try_into()
                .unwrap(),
        ),
        last_checkpoint_lane_sequences,
    };
    validate_master(&master)?;
    Ok(master)
}

pub fn encode_pool_v1_pair_forest_lane_state_v1(
    lane: &PoolV1PairForestLaneStateV1,
    pair_empty_roots: &[Digest; POOL_V1_TREE_DEPTH + 1],
) -> Result<[u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES], PoolV1PairForestAccountErrorV1> {
    if usize::from(lane.lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(PoolV1PairForestAccountErrorV1::InvalidLane);
    }
    if lane.master == [0u8; 32] {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    if lane.tree.next_leaf_index > POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    let tree = lane.tree.encode_with_empty_roots(pair_empty_roots)?;
    let mut output = [0u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_LANE_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_LANE_VERSION;
    output[5] = lane.lane_id;
    output[6] = POOL_V1_PAIR_FOREST_LANE_COUNT as u8;
    output[7] = POOL_V1_TREE_DEPTH as u8;
    output[8..40].copy_from_slice(&POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING);
    output[LANE_MASTER_OFFSET..72].copy_from_slice(&lane.master);
    output[LANE_TREE_OFFSET..].copy_from_slice(&tree);
    Ok(output)
}

pub fn decode_pool_v1_pair_forest_lane_state_v1(
    bytes: &[u8],
    pair_empty_roots: &[Digest; POOL_V1_TREE_DEPTH + 1],
) -> Result<PoolV1PairForestLaneStateV1, PoolV1PairForestAccountErrorV1> {
    if bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES {
        return Err(PoolV1PairForestAccountErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_LANE_MAGIC {
        return Err(PoolV1PairForestAccountErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_LANE_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongVersion);
    }
    if usize::from(bytes[5]) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(PoolV1PairForestAccountErrorV1::InvalidLane);
    }
    if bytes[6] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8 {
        return Err(PoolV1PairForestAccountErrorV1::WrongLaneCount);
    }
    if bytes[7] != POOL_V1_TREE_DEPTH as u8 {
        return Err(PoolV1PairForestAccountErrorV1::WrongDepth);
    }
    if bytes[8..40] != POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING {
        return Err(PoolV1PairForestAccountErrorV1::WrongFormatBinding);
    }
    let master: [u8; 32] = bytes[LANE_MASTER_OFFSET..72].try_into().unwrap();
    if master == [0u8; 32] {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    if bytes[72..LANE_TREE_OFFSET].iter().any(|byte| *byte != 0) {
        return Err(PoolV1PairForestAccountErrorV1::NonZeroReserved);
    }
    let tree = IncrementalMerkleTreeV1::decode_with_empty_roots(
        &bytes[LANE_TREE_OFFSET..],
        pair_empty_roots,
    )?;
    if tree.next_leaf_index > POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    Ok(PoolV1PairForestLaneStateV1 {
        master,
        lane_id: bytes[5],
        tree,
    })
}

pub fn encode_pool_v1_pair_forest_checkpoint_v1(
    checkpoint: &PoolV1PairForestCheckpointV1,
) -> Result<[u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES], PoolV1PairForestAccountErrorV1> {
    if checkpoint.master == [0u8; 32] || checkpoint.deployment_domain == [0u8; 32] {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    if !digest_is_canonical(&checkpoint.global_root) {
        return Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest);
    }
    if checkpoint
        .lane_sequences
        .iter()
        .any(|sequence| *sequence > POOL_V1_PAIR_CAPACITY)
    {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    let mut output = [0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_CHECKPOINT_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION;
    output[5] = POOL_V1_PAIR_FOREST_LANE_COUNT as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[CHECKPOINT_MASTER_OFFSET..CHECKPOINT_DOMAIN_OFFSET].copy_from_slice(&checkpoint.master);
    output[CHECKPOINT_DOMAIN_OFFSET..CHECKPOINT_SEQUENCE_OFFSET]
        .copy_from_slice(&checkpoint.deployment_domain);
    output[CHECKPOINT_SEQUENCE_OFFSET..CHECKPOINT_GLOBAL_ROOT_OFFSET]
        .copy_from_slice(&checkpoint.checkpoint_sequence.to_le_bytes());
    output[CHECKPOINT_GLOBAL_ROOT_OFFSET..CHECKPOINT_LANE_SEQUENCES_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&checkpoint.global_root));
    for (lane, sequence) in checkpoint.lane_sequences.iter().enumerate() {
        let start = CHECKPOINT_LANE_SEQUENCES_OFFSET + 8 * lane;
        output[start..start + 8].copy_from_slice(&sequence.to_le_bytes());
    }
    Ok(output)
}

pub fn decode_pool_v1_pair_forest_checkpoint_v1(
    bytes: &[u8],
) -> Result<PoolV1PairForestCheckpointV1, PoolV1PairForestAccountErrorV1> {
    if bytes.len() != POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES {
        return Err(PoolV1PairForestAccountErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_CHECKPOINT_MAGIC {
        return Err(PoolV1PairForestAccountErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8 {
        return Err(PoolV1PairForestAccountErrorV1::WrongLaneCount);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 || bytes[176..].iter().any(|byte| *byte != 0) {
        return Err(PoolV1PairForestAccountErrorV1::NonZeroReserved);
    }
    let master: [u8; 32] = bytes[CHECKPOINT_MASTER_OFFSET..CHECKPOINT_DOMAIN_OFFSET]
        .try_into()
        .unwrap();
    let deployment_domain: [u8; 32] = bytes[CHECKPOINT_DOMAIN_OFFSET..CHECKPOINT_SEQUENCE_OFFSET]
        .try_into()
        .unwrap();
    if master == [0u8; 32] || deployment_domain == [0u8; 32] {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    let global_root = decode_digest_canonical(
        bytes[CHECKPOINT_GLOBAL_ROOT_OFFSET..CHECKPOINT_LANE_SEQUENCES_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1PairForestAccountErrorV1::NonCanonicalDigest)?;
    let mut lane_sequences = [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for (lane, sequence) in lane_sequences.iter_mut().enumerate() {
        let start = CHECKPOINT_LANE_SEQUENCES_OFFSET + 8 * lane;
        *sequence = u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap());
        if *sequence > POOL_V1_PAIR_CAPACITY {
            return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
        }
    }
    Ok(PoolV1PairForestCheckpointV1 {
        master,
        deployment_domain,
        checkpoint_sequence: u64::from_le_bytes(
            bytes[CHECKPOINT_SEQUENCE_OFFSET..CHECKPOINT_GLOBAL_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        global_root,
        lane_sequences,
    })
}

/// Validate a coherent fixed-order snapshot and prepare one immutable record.
/// The caller supplies the global root computed by the separately reviewed
/// forest combiner; this function owns only account/state chronology.
pub fn plan_pool_v1_pair_forest_checkpoint_v1(
    master: &PoolV1PairForestMasterV1,
    lanes: &[PoolV1PairForestLaneStateV1; POOL_V1_PAIR_FOREST_LANE_COUNT],
    global_root: Digest,
) -> Result<PoolV1PairForestCheckpointPlanV1, PoolV1PairForestAccountErrorV1> {
    validate_master(master)?;
    if master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    if !digest_is_canonical(&global_root) {
        return Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest);
    }
    let mut lane_sequences = [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for (expected_lane, lane) in lanes.iter().enumerate() {
        if lane.master != master.identity.pool {
            return Err(PoolV1PairForestAccountErrorV1::LaneMasterMismatch);
        }
        if usize::from(lane.lane_id) != expected_lane {
            return Err(PoolV1PairForestAccountErrorV1::LaneOrderMismatch);
        }
        if lane.tree.next_leaf_index > POOL_V1_PAIR_CAPACITY {
            return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
        }
        lane_sequences[expected_lane] = lane.tree.next_leaf_index;
    }
    if master.has_checkpoint {
        let mut progressed = false;
        for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
            if lane_sequences[lane] < master.last_checkpoint_lane_sequences[lane] {
                return Err(PoolV1PairForestAccountErrorV1::LaneSequenceDecreased);
            }
            progressed |= lane_sequences[lane] > master.last_checkpoint_lane_sequences[lane];
        }
        if !progressed {
            return Err(PoolV1PairForestAccountErrorV1::DuplicateCheckpoint);
        }
    }
    let next_sequence = master
        .next_checkpoint_sequence
        .checked_add(1)
        .ok_or(PoolV1PairForestAccountErrorV1::CheckpointSequenceOverflow)?;
    let checkpoint = PoolV1PairForestCheckpointV1 {
        master: master.identity.pool,
        deployment_domain: master.identity.deployment_domain,
        checkpoint_sequence: master.next_checkpoint_sequence,
        global_root,
        lane_sequences,
    };
    let next_master = PoolV1PairForestMasterV1 {
        has_checkpoint: true,
        next_checkpoint_sequence: next_sequence,
        last_checkpoint_lane_sequences: lane_sequences,
        ..*master
    };
    validate_master(&next_master)?;
    Ok(PoolV1PairForestCheckpointPlanV1 {
        next_master,
        checkpoint,
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;

    use super::*;
    use crate::pool_v1::{pool_v1_empty_roots, pool_v1_tree_parent, POOL_V1_PAIR_TREE_DEPTH};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn pair_empty_roots() -> [Digest; POOL_V1_TREE_DEPTH + 1] {
        let ordinary = pool_v1_empty_roots();
        core::array::from_fn(|level| {
            if level < POOL_V1_TREE_DEPTH {
                ordinary[level + 1]
            } else {
                pool_v1_tree_parent(&ordinary[POOL_V1_TREE_DEPTH], &ordinary[POOL_V1_TREE_DEPTH])
            }
        })
    }

    fn master() -> PoolV1PairForestMasterV1 {
        PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: [1u8; 32],
                asset_mint: [2u8; 32],
                token_program: [3u8; 32],
                asset_id: M31(4),
                deployment_domain: [5u8; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: 1,
                registry_program: [6u8; 32],
                registry_authority: [0u8; 32],
                policy_binding: [7u8; 32],
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: false,
            next_checkpoint_sequence: 0,
            last_checkpoint_lane_sequences: [0u64; 8],
        }
    }

    fn lanes(master: [u8; 32]) -> [PoolV1PairForestLaneStateV1; 8] {
        let empty = pair_empty_roots();
        core::array::from_fn(|lane| PoolV1PairForestLaneStateV1 {
            master,
            lane_id: lane as u8,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: empty[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| empty[level]),
            },
        })
    }

    #[test]
    fn canonical_byte_routes_cover_all_eight_lanes() {
        for expected in 0..8u32 {
            let value = [M31(expected); 8];
            assert_eq!(
                pool_v1_pair_forest_output_lane_v1(&value),
                Ok(expected as u8)
            );
            assert_eq!(
                pool_v1_pair_forest_deposit_lane_v1(&value),
                Ok(expected as u8)
            );
            assert_eq!(encode_digest_canonical(&value)[0] & 7, expected as u8);
        }
        let noncanonical = [M31(P); 8];
        assert_eq!(
            pool_v1_pair_forest_output_lane_v1(&noncanonical),
            Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)
        );
        assert_eq!(
            pool_v1_pair_forest_deposit_lane_v1(&noncanonical),
            Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)
        );
    }

    #[test]
    fn master_lane_and_checkpoint_codecs_are_exact_and_version_separated() {
        let master = master();
        let master_image = encode_pool_v1_pair_forest_master_v1(&master).unwrap();
        assert_eq!(
            decode_pool_v1_pair_forest_master_v1(&master_image),
            Ok(master)
        );
        assert_eq!(master_image.len(), 384);

        let empty = pair_empty_roots();
        for lane in lanes(master.identity.pool) {
            let image = encode_pool_v1_pair_forest_lane_state_v1(&lane, &empty).unwrap();
            assert_eq!(
                decode_pool_v1_pair_forest_lane_state_v1(&image, &empty),
                Ok(lane)
            );
            assert_eq!(image.len(), 768);
        }

        let plan = plan_pool_v1_pair_forest_checkpoint_v1(
            &master,
            &lanes(master.identity.pool),
            digest(100),
        )
        .unwrap();
        let checkpoint_image = encode_pool_v1_pair_forest_checkpoint_v1(&plan.checkpoint).unwrap();
        assert_eq!(
            decode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_image),
            Ok(plan.checkpoint)
        );
        assert_eq!(checkpoint_image.len(), 192);

        let mut old_single_tree = master_image;
        old_single_tree[..4].copy_from_slice(b"ASPJ");
        assert_eq!(
            decode_pool_v1_pair_forest_master_v1(&old_single_tree),
            Err(PoolV1PairForestAccountErrorV1::WrongMagic)
        );
    }

    #[test]
    fn checkpoint_chronology_rejects_duplicate_decrease_and_wrong_lane_order() {
        let master = master();
        let mut lanes = lanes(master.identity.pool);
        let first = plan_pool_v1_pair_forest_checkpoint_v1(&master, &lanes, digest(100)).unwrap();
        assert_eq!(first.checkpoint.checkpoint_sequence, 0);
        assert_eq!(first.next_master.next_checkpoint_sequence, 1);
        assert_eq!(
            plan_pool_v1_pair_forest_checkpoint_v1(&first.next_master, &lanes, digest(101)),
            Err(PoolV1PairForestAccountErrorV1::DuplicateCheckpoint)
        );

        let empty = pair_empty_roots();
        lanes[3].tree = lanes[3]
            .tree
            .append_one_with_empty_roots(digest(500), &empty)
            .unwrap()
            .0;
        let second =
            plan_pool_v1_pair_forest_checkpoint_v1(&first.next_master, &lanes, digest(102))
                .unwrap();
        assert_eq!(second.checkpoint.lane_sequences[3], 1);

        let mut decreased_master = second.next_master;
        decreased_master.last_checkpoint_lane_sequences[2] = 1;
        assert_eq!(
            plan_pool_v1_pair_forest_checkpoint_v1(&decreased_master, &lanes, digest(103)),
            Err(PoolV1PairForestAccountErrorV1::LaneSequenceDecreased)
        );

        lanes.swap(0, 1);
        assert_eq!(
            plan_pool_v1_pair_forest_checkpoint_v1(&master, &lanes, digest(104)),
            Err(PoolV1PairForestAccountErrorV1::LaneOrderMismatch)
        );
    }

    #[test]
    fn reserved_noncanonical_and_incomplete_master_mutations_fail_closed() {
        let master = master();
        let mut master_image = encode_pool_v1_pair_forest_master_v1(&master).unwrap();
        master_image[50] = 1;
        assert_eq!(
            decode_pool_v1_pair_forest_master_v1(&master_image),
            Err(PoolV1PairForestAccountErrorV1::NonZeroReserved)
        );

        let mut incomplete = master;
        incomplete.initialized_lane_mask ^= 1;
        assert_eq!(
            plan_pool_v1_pair_forest_checkpoint_v1(
                &incomplete,
                &lanes(master.identity.pool),
                digest(1)
            ),
            Err(PoolV1PairForestAccountErrorV1::InvalidMasterState)
        );

        let plan = plan_pool_v1_pair_forest_checkpoint_v1(
            &master,
            &lanes(master.identity.pool),
            digest(1),
        )
        .unwrap();
        let mut image = encode_pool_v1_pair_forest_checkpoint_v1(&plan.checkpoint).unwrap();
        image[80..84].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            decode_pool_v1_pair_forest_checkpoint_v1(&image),
            Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)
        );
    }
}
