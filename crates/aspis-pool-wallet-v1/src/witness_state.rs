//! Exact append-only Merkle witness maintenance for locally owned Pool notes.
//!
//! For an existing leaf `i` and a newly appended leaf `n`, exactly one sibling
//! in `i`'s authentication path changes: the level of the most significant set
//! bit of `i XOR n`.  The replacement is the partially padded subtree root
//! carried by the canonical append algorithm immediately before that level.
//! This module applies that update, then recomputes every tracked path against
//! the externally authenticated resulting root before committing the state.

use aspis_core::field::M31;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        pool_v1_empty_roots, pool_v1_tree_parent, IncrementalMerkleTreeV1, PoolV1TreeError,
        POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_LEAF_CAPACITY, POOL_V1_TREE_DEPTH,
        POOL_V1_TREE_HASH_VERSION, POOL_V1_TREE_STATE_ACCOUNT_BYTES,
    },
    Digest,
};
use sha2::{Digest as _, Sha256};

use crate::{finalized_indexer::FinalizedAppendEvidenceV1, scan_state::DepositEventIdV1};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitnessStateErrorV1 {
    Tree(PoolV1TreeError),
    NonCanonicalDigest,
    LeafIndexMismatch,
    RootSequenceMismatch,
    RootMismatch,
    DuplicateWitness,
    WitnessNotFound,
    InvalidWitness,
    WrongImageLength,
    WrongImageMagic,
    WrongImageVersion,
    WrongImageParameters,
    NonZeroReserved,
    ChecksumMismatch,
    CountOverflow,
    NonCanonicalOrder,
    InvalidEventIdentity,
}

pub const WALLET_WITNESS_STATE_MAGIC_V1: [u8; 4] = *b"ASWS";
pub const WALLET_WITNESS_STATE_VERSION_V1: u8 = 1;
pub const WALLET_WITNESS_STATE_HEADER_BYTES_V1: usize = 64;
pub const WALLET_WITNESS_RECORD_BYTES_V1: usize = 108 + 8 + 32 + 32 * POOL_V1_TREE_DEPTH;
const WALLET_WITNESS_CHECKSUM_OFFSET_V1: usize = 32;
const MAX_WALLET_WITNESS_IMAGE_BYTES_V1: usize = 64 * 1024 * 1024;
const WALLET_WITNESS_CHECKSUM_DOMAIN_V1: &[u8] = b"aspis:pool-v1:wallet-witness-state:sha256:v1";

impl From<PoolV1TreeError> for WitnessStateErrorV1 {
    fn from(error: PoolV1TreeError) -> Self {
        Self::Tree(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrackedMerkleWitnessV1 {
    event_id: DepositEventIdV1,
    leaf_index: u64,
    leaf: Digest,
    siblings: [Digest; POOL_V1_TREE_DEPTH],
}

impl TrackedMerkleWitnessV1 {
    pub fn event_id(&self) -> DepositEventIdV1 {
        self.event_id
    }

    pub fn leaf_index(&self) -> u64 {
        self.leaf_index
    }

    pub fn leaf(&self) -> &Digest {
        &self.leaf
    }

    pub fn siblings(&self) -> &[Digest; POOL_V1_TREE_DEPTH] {
        &self.siblings
    }

    pub fn root(&self) -> Digest {
        witness_root_v1(self.leaf_index, self.leaf, &self.siblings)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WitnessAppendReceiptV1 {
    pub leaf_index: u64,
    pub root_sequence: u64,
    pub root: [u8; 32],
    pub tracked_event_id: Option<DepositEventIdV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WalletWitnessStateV1 {
    tree: IncrementalMerkleTreeV1,
    tracked: Vec<TrackedMerkleWitnessV1>,
}

impl WalletWitnessStateV1 {
    pub fn empty() -> Self {
        Self {
            tree: IncrementalMerkleTreeV1::empty(),
            tracked: Vec::new(),
        }
    }

    /// Start from an authenticated Pool tree account.  The caller must first
    /// validate account owner/PDA/finality and supply the same current root
    /// from authenticated history.  This explicit equality also closes the
    /// otherwise-unreconstructible terminal-root case for a full tree.
    pub fn from_authenticated_tree_v1(
        tree: IncrementalMerkleTreeV1,
        authenticated_root_bytes: [u8; 32],
    ) -> Result<Self, WitnessStateErrorV1> {
        tree.validate()?;
        let authenticated_root = decode_digest_canonical(&authenticated_root_bytes)
            .map_err(|_| WitnessStateErrorV1::NonCanonicalDigest)?;
        if tree.root != authenticated_root {
            return Err(WitnessStateErrorV1::RootMismatch);
        }
        Ok(Self {
            tree,
            tracked: Vec::new(),
        })
    }

    pub fn tree(&self) -> &IncrementalMerkleTreeV1 {
        &self.tree
    }

    pub fn tracked(&self) -> &[TrackedMerkleWitnessV1] {
        &self.tracked
    }

    pub fn witness_v1(
        &self,
        event_id: DepositEventIdV1,
    ) -> Result<&TrackedMerkleWitnessV1, WitnessStateErrorV1> {
        self.tracked
            .iter()
            .find(|witness| witness.event_id == event_id)
            .ok_or(WitnessStateErrorV1::WitnessNotFound)
    }

    pub fn remove_witness_v1(
        &mut self,
        event_id: DepositEventIdV1,
    ) -> Result<TrackedMerkleWitnessV1, WitnessStateErrorV1> {
        let index = self
            .tracked
            .iter()
            .position(|witness| witness.event_id == event_id)
            .ok_or(WitnessStateErrorV1::WitnessNotFound)?;
        Ok(self.tracked.remove(index))
    }

    /// Import a path supplied by an untrusted indexer only after recomputing it
    /// to the exact authenticated current root.  This permits wallet recovery
    /// from a later tree snapshot without retaining every historical leaf.
    pub fn import_current_witness_v1(
        &mut self,
        event_id: DepositEventIdV1,
        leaf_index: u64,
        leaf_bytes: [u8; 32],
        sibling_bytes: [[u8; 32]; POOL_V1_TREE_DEPTH],
    ) -> Result<(), WitnessStateErrorV1> {
        if leaf_index >= self.tree.next_leaf_index {
            return Err(WitnessStateErrorV1::LeafIndexMismatch);
        }
        if self
            .tracked
            .iter()
            .any(|witness| witness.event_id == event_id || witness.leaf_index == leaf_index)
        {
            return Err(WitnessStateErrorV1::DuplicateWitness);
        }
        let leaf = decode_digest_canonical(&leaf_bytes)
            .map_err(|_| WitnessStateErrorV1::NonCanonicalDigest)?;
        let mut siblings = [[M31::ZERO; 8]; POOL_V1_TREE_DEPTH];
        for (output, encoded) in siblings.iter_mut().zip(sibling_bytes) {
            *output = decode_digest_canonical(&encoded)
                .map_err(|_| WitnessStateErrorV1::NonCanonicalDigest)?;
        }
        let witness = TrackedMerkleWitnessV1 {
            event_id,
            leaf_index,
            leaf,
            siblings,
        };
        if witness.root() != self.tree.root {
            return Err(WitnessStateErrorV1::InvalidWitness);
        }
        self.tracked.push(witness);
        Ok(())
    }

    /// Apply one finalized append and optionally begin tracking the new leaf.
    /// The supplied index/sequence/root come from the authenticated Pool
    /// instruction and root-history evidence.  All work happens on clones;
    /// any mismatch leaves both the frontier and every witness unchanged.
    pub fn append_authenticated_leaf_v1(
        &mut self,
        leaf_index: u64,
        root_sequence: u64,
        leaf_bytes: [u8; 32],
        root_bytes: [u8; 32],
        tracked_event_id: Option<DepositEventIdV1>,
    ) -> Result<WitnessAppendReceiptV1, WitnessStateErrorV1> {
        if leaf_index != self.tree.next_leaf_index {
            return Err(WitnessStateErrorV1::LeafIndexMismatch);
        }
        if leaf_index.checked_add(1) != Some(root_sequence) {
            return Err(WitnessStateErrorV1::RootSequenceMismatch);
        }
        if tracked_event_id.is_some_and(|event_id| {
            self.tracked
                .iter()
                .any(|witness| witness.event_id == event_id)
        }) {
            return Err(WitnessStateErrorV1::DuplicateWitness);
        }
        let leaf = decode_digest_canonical(&leaf_bytes)
            .map_err(|_| WitnessStateErrorV1::NonCanonicalDigest)?;
        let expected_root = decode_digest_canonical(&root_bytes)
            .map_err(|_| WitnessStateErrorV1::NonCanonicalDigest)?;
        let empty = pool_v1_empty_roots();
        let (partial, terminal) = append_partial_roots_v1(&self.tree, leaf, &empty)?;
        let (next_tree, append) = self.tree.append_one(leaf)?;
        if append.leaf_index != leaf_index
            || append.root_sequence != root_sequence
            || append.root != expected_root
            || next_tree.root != expected_root
            || terminal != expected_root
        {
            return Err(WitnessStateErrorV1::RootMismatch);
        }

        let mut tracked = self.tracked.clone();
        for witness in &mut tracked {
            let differing = witness.leaf_index ^ leaf_index;
            if differing == 0 {
                return Err(WitnessStateErrorV1::DuplicateWitness);
            }
            let level = (u64::BITS - 1 - differing.leading_zeros()) as usize;
            if level >= POOL_V1_TREE_DEPTH {
                return Err(WitnessStateErrorV1::InvalidWitness);
            }
            witness.siblings[level] = partial[level];
        }

        if let Some(event_id) = tracked_event_id {
            let siblings = core::array::from_fn(|level| {
                if (leaf_index >> level) & 1 == 0 {
                    empty[level]
                } else {
                    self.tree.frontier[level]
                }
            });
            tracked.push(TrackedMerkleWitnessV1 {
                event_id,
                leaf_index,
                leaf,
                siblings,
            });
        }
        if tracked
            .iter()
            .any(|witness| witness.root() != expected_root)
        {
            return Err(WitnessStateErrorV1::InvalidWitness);
        }
        self.tree = next_tree;
        self.tracked = tracked;
        Ok(WitnessAppendReceiptV1 {
            leaf_index,
            root_sequence,
            root: root_bytes,
            tracked_event_id,
        })
    }

    /// Apply the complete append stream returned by finalized ingestion.  The
    /// selection contains only locally owned event IDs; every unselected leaf
    /// is still applied because it changes later authentication paths.
    pub fn apply_finalized_appends_v1(
        &mut self,
        appends: &[FinalizedAppendEvidenceV1],
        track_event_ids: &[DepositEventIdV1],
    ) -> Result<Vec<WitnessAppendReceiptV1>, WitnessStateErrorV1> {
        let mut unique_appends = std::collections::HashSet::with_capacity(appends.len());
        if !appends
            .iter()
            .all(|append| unique_appends.insert(append.event_id))
        {
            return Err(WitnessStateErrorV1::DuplicateWitness);
        }
        let mut unique_tracks = std::collections::HashSet::with_capacity(track_event_ids.len());
        if !track_event_ids
            .iter()
            .all(|event_id| unique_tracks.insert(*event_id) && unique_appends.contains(event_id))
        {
            return Err(WitnessStateErrorV1::WitnessNotFound);
        }
        let mut working = self.clone();
        let mut receipts = Vec::with_capacity(appends.len());
        for append in appends {
            receipts.push(
                working.append_authenticated_leaf_v1(
                    append.leaf_index,
                    append.root_sequence,
                    append.note_commitment,
                    append.root,
                    unique_tracks
                        .contains(&append.event_id)
                        .then_some(append.event_id),
                )?,
            );
        }
        *self = working;
        Ok(receipts)
    }
}

fn append_partial_roots_v1(
    tree: &IncrementalMerkleTreeV1,
    leaf: Digest,
    empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
) -> Result<([Digest; POOL_V1_TREE_DEPTH], Digest), WitnessStateErrorV1> {
    if tree.next_leaf_index >= POOL_V1_LEAF_CAPACITY {
        return Err(WitnessStateErrorV1::Tree(PoolV1TreeError::TreeFull));
    }
    let mut partial = [[M31::ZERO; 8]; POOL_V1_TREE_DEPTH];
    let mut current = leaf;
    for level in 0..POOL_V1_TREE_DEPTH {
        partial[level] = current;
        current = if (tree.next_leaf_index >> level) & 1 == 0 {
            pool_v1_tree_parent(&current, &empty[level])
        } else {
            pool_v1_tree_parent(&tree.frontier[level], &current)
        };
    }
    Ok((partial, current))
}

fn witness_root_v1(
    leaf_index: u64,
    leaf: Digest,
    siblings: &[Digest; POOL_V1_TREE_DEPTH],
) -> Digest {
    let mut current = leaf;
    for (level, sibling) in siblings.iter().enumerate() {
        current = if (leaf_index >> level) & 1 == 0 {
            pool_v1_tree_parent(&current, sibling)
        } else {
            pool_v1_tree_parent(sibling, &current)
        };
    }
    current
}

/// Canonical fixed-record image for the authenticated frontier and every
/// locally tracked path. Records are sorted by leaf index, then event ID, so
/// logically identical state has one byte representation.
pub fn encode_wallet_witness_state_v1(
    state: &WalletWitnessStateV1,
) -> Result<Vec<u8>, WitnessStateErrorV1> {
    state.tree.validate()?;
    let count = state.tracked.len();
    let records_bytes = count
        .checked_mul(WALLET_WITNESS_RECORD_BYTES_V1)
        .ok_or(WitnessStateErrorV1::CountOverflow)?;
    let length = WALLET_WITNESS_STATE_HEADER_BYTES_V1
        .checked_add(POOL_V1_TREE_STATE_ACCOUNT_BYTES)
        .and_then(|value| value.checked_add(records_bytes))
        .ok_or(WitnessStateErrorV1::CountOverflow)?;
    if length > MAX_WALLET_WITNESS_IMAGE_BYTES_V1 {
        return Err(WitnessStateErrorV1::CountOverflow);
    }
    let count = u32::try_from(count).map_err(|_| WitnessStateErrorV1::CountOverflow)?;
    let mut ordered: Vec<_> = state.tracked.iter().collect();
    ordered.sort_by_key(|witness| (witness.leaf_index, encode_event_id_v1(witness.event_id)));
    if ordered.windows(2).any(|pair| {
        pair[0].leaf_index == pair[1].leaf_index || pair[0].event_id == pair[1].event_id
    }) {
        return Err(WitnessStateErrorV1::DuplicateWitness);
    }

    let mut output = vec![0u8; length];
    output[..4].copy_from_slice(&WALLET_WITNESS_STATE_MAGIC_V1);
    output[4] = WALLET_WITNESS_STATE_VERSION_V1;
    output[5] = POOL_V1_TREE_DEPTH as u8;
    output[6] = POOL_V1_TREE_HASH_VERSION;
    output[7] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[8..12].copy_from_slice(&count.to_le_bytes());
    output[12..16].copy_from_slice(
        &u32::try_from(WALLET_WITNESS_RECORD_BYTES_V1)
            .map_err(|_| WitnessStateErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    output[16..20].copy_from_slice(
        &u32::try_from(POOL_V1_TREE_STATE_ACCOUNT_BYTES)
            .map_err(|_| WitnessStateErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    let tree = state.tree.encode()?;
    let tree_start = WALLET_WITNESS_STATE_HEADER_BYTES_V1;
    output[tree_start..tree_start + tree.len()].copy_from_slice(&tree);
    let mut offset = tree_start + tree.len();
    for witness in ordered {
        let record = &mut output[offset..offset + WALLET_WITNESS_RECORD_BYTES_V1];
        record[..108].copy_from_slice(&encode_event_id_v1(witness.event_id));
        record[108..116].copy_from_slice(&witness.leaf_index.to_le_bytes());
        record[116..148].copy_from_slice(&encode_digest_canonical(&witness.leaf));
        for (level, sibling) in witness.siblings.iter().enumerate() {
            let start = 148 + 32 * level;
            record[start..start + 32].copy_from_slice(&encode_digest_canonical(sibling));
        }
        offset += WALLET_WITNESS_RECORD_BYTES_V1;
    }
    let checksum = wallet_witness_checksum_v1(&output)?;
    output[WALLET_WITNESS_CHECKSUM_OFFSET_V1..WALLET_WITNESS_CHECKSUM_OFFSET_V1 + 32]
        .copy_from_slice(&checksum);
    Ok(output)
}

pub fn decode_wallet_witness_state_v1(
    bytes: &[u8],
) -> Result<WalletWitnessStateV1, WitnessStateErrorV1> {
    if bytes.len() < WALLET_WITNESS_STATE_HEADER_BYTES_V1 + POOL_V1_TREE_STATE_ACCOUNT_BYTES
        || bytes.len() > MAX_WALLET_WITNESS_IMAGE_BYTES_V1
    {
        return Err(WitnessStateErrorV1::WrongImageLength);
    }
    if bytes[..4] != WALLET_WITNESS_STATE_MAGIC_V1 {
        return Err(WitnessStateErrorV1::WrongImageMagic);
    }
    if bytes[4] != WALLET_WITNESS_STATE_VERSION_V1 {
        return Err(WitnessStateErrorV1::WrongImageVersion);
    }
    if bytes[5] != POOL_V1_TREE_DEPTH as u8
        || bytes[6] != POOL_V1_TREE_HASH_VERSION
        || bytes[7] != POOL_V1_DIGEST_ENCODING_VERSION
        || u32::from_le_bytes(bytes[12..16].try_into().unwrap()) as usize
            != WALLET_WITNESS_RECORD_BYTES_V1
        || u32::from_le_bytes(bytes[16..20].try_into().unwrap()) as usize
            != POOL_V1_TREE_STATE_ACCOUNT_BYTES
    {
        return Err(WitnessStateErrorV1::WrongImageParameters);
    }
    if bytes[20..32].iter().any(|byte| *byte != 0) {
        return Err(WitnessStateErrorV1::NonZeroReserved);
    }
    let encoded_checksum: [u8; 32] = bytes[32..64].try_into().unwrap();
    if encoded_checksum != wallet_witness_checksum_v1(bytes)? {
        return Err(WitnessStateErrorV1::ChecksumMismatch);
    }
    let count = u32::from_le_bytes(bytes[8..12].try_into().unwrap()) as usize;
    let expected_length = WALLET_WITNESS_STATE_HEADER_BYTES_V1
        .checked_add(POOL_V1_TREE_STATE_ACCOUNT_BYTES)
        .and_then(|value| {
            count
                .checked_mul(WALLET_WITNESS_RECORD_BYTES_V1)
                .and_then(|records| value.checked_add(records))
        })
        .ok_or(WitnessStateErrorV1::CountOverflow)?;
    if expected_length != bytes.len() {
        return Err(WitnessStateErrorV1::WrongImageLength);
    }
    let tree_start = WALLET_WITNESS_STATE_HEADER_BYTES_V1;
    let tree_end = tree_start + POOL_V1_TREE_STATE_ACCOUNT_BYTES;
    let tree = IncrementalMerkleTreeV1::decode(&bytes[tree_start..tree_end])?;
    let mut state = WalletWitnessStateV1::from_authenticated_tree_v1(
        tree,
        encode_digest_canonical(&tree.root),
    )?;
    let mut previous_key = None;
    let mut offset = tree_end;
    for _ in 0..count {
        let record = &bytes[offset..offset + WALLET_WITNESS_RECORD_BYTES_V1];
        let encoded_event: [u8; 108] = record[..108].try_into().unwrap();
        let event_id = decode_event_id_v1(&encoded_event)?;
        let leaf_index = u64::from_le_bytes(record[108..116].try_into().unwrap());
        let key = (leaf_index, encoded_event);
        if previous_key.is_some_and(|previous| previous >= key) {
            return Err(WitnessStateErrorV1::NonCanonicalOrder);
        }
        previous_key = Some(key);
        let leaf: [u8; 32] = record[116..148].try_into().unwrap();
        let mut siblings = [[0u8; 32]; POOL_V1_TREE_DEPTH];
        for (level, sibling) in siblings.iter_mut().enumerate() {
            let start = 148 + 32 * level;
            *sibling = record[start..start + 32].try_into().unwrap();
        }
        state.import_current_witness_v1(event_id, leaf_index, leaf, siblings)?;
        offset += WALLET_WITNESS_RECORD_BYTES_V1;
    }
    Ok(state)
}

fn wallet_witness_checksum_v1(bytes: &[u8]) -> Result<[u8; 32], WitnessStateErrorV1> {
    if bytes.len() < WALLET_WITNESS_STATE_HEADER_BYTES_V1 {
        return Err(WitnessStateErrorV1::WrongImageLength);
    }
    let length = u64::try_from(bytes.len()).map_err(|_| WitnessStateErrorV1::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(WALLET_WITNESS_CHECKSUM_DOMAIN_V1);
    hasher.update(length.to_le_bytes());
    hasher.update(&bytes[..WALLET_WITNESS_CHECKSUM_OFFSET_V1]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[WALLET_WITNESS_CHECKSUM_OFFSET_V1 + 32..]);
    Ok(hasher.finalize().into())
}

fn encode_event_id_v1(event_id: DepositEventIdV1) -> [u8; 108] {
    let mut bytes = [0u8; 108];
    bytes[..8].copy_from_slice(&event_id.point().slot().to_le_bytes());
    bytes[8..40].copy_from_slice(event_id.point().block_hash());
    bytes[40..104].copy_from_slice(event_id.transaction_signature());
    bytes[104..106].copy_from_slice(&event_id.instruction_index().to_le_bytes());
    bytes[106..108].copy_from_slice(&event_id.event_index().to_le_bytes());
    bytes
}

fn decode_event_id_v1(bytes: &[u8; 108]) -> Result<DepositEventIdV1, WitnessStateErrorV1> {
    let point = crate::scan_state::FinalizedChainPointV1::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        bytes[8..40].try_into().unwrap(),
    )
    .map_err(|_| WitnessStateErrorV1::InvalidEventIdentity)?;
    DepositEventIdV1::new(
        point,
        bytes[40..104].try_into().unwrap(),
        u16::from_le_bytes(bytes[104..106].try_into().unwrap()),
        u16::from_le_bytes(bytes[106..108].try_into().unwrap()),
    )
    .map_err(|_| WitnessStateErrorV1::InvalidEventIdentity)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scan_state::FinalizedChainPointV1;
    use aspis_core::field::P;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31((seed + 101 * index as u32) % P))
    }

    fn event(index: u64) -> DepositEventIdV1 {
        DepositEventIdV1::new(
            FinalizedChainPointV1::new(index + 1, [(index as u8).wrapping_add(1); 32]).unwrap(),
            [(index as u8).wrapping_add(2); 64],
            0,
            0,
        )
        .unwrap()
    }

    fn reference_prefix_root(leaves: &[Digest]) -> Digest {
        let empty = pool_v1_empty_roots();
        let mut nodes = leaves.to_vec();
        if nodes.is_empty() {
            return empty[POOL_V1_TREE_DEPTH];
        }
        for level in 0..POOL_V1_TREE_DEPTH {
            if nodes.len() & 1 == 1 {
                nodes.push(empty[level]);
            }
            nodes = nodes
                .chunks_exact(2)
                .map(|pair| pool_v1_tree_parent(&pair[0], &pair[1]))
                .collect();
        }
        assert_eq!(nodes.len(), 1);
        nodes[0]
    }

    #[test]
    fn tracked_paths_follow_every_append_and_match_independent_roots() {
        let mut state = WalletWitnessStateV1::empty();
        let mut leaves = Vec::new();
        let tracked_indices = [0u64, 1, 2, 5, 31, 32, 63];
        for index in 0..64u64 {
            let leaf = digest(index as u32 + 1);
            leaves.push(leaf);
            let root = reference_prefix_root(&leaves);
            state
                .append_authenticated_leaf_v1(
                    index,
                    index + 1,
                    encode_digest_canonical(&leaf),
                    encode_digest_canonical(&root),
                    tracked_indices.contains(&index).then(|| event(index)),
                )
                .unwrap();
            assert_eq!(state.tree().root, root);
            assert!(state.tracked().iter().all(|witness| witness.root() == root));
        }
        assert_eq!(state.tracked().len(), tracked_indices.len());
        for index in tracked_indices {
            let witness = state.witness_v1(event(index)).unwrap();
            assert_eq!(witness.leaf_index(), index);
            assert_eq!(witness.leaf(), &leaves[index as usize]);
        }
    }

    #[test]
    fn finalized_append_stream_tracks_selected_notes_and_is_atomic() {
        let leaves: Vec<_> = (0..4).map(|index| digest(index + 1)).collect();
        let mut appends = Vec::new();
        for index in 0..leaves.len() {
            appends.push(FinalizedAppendEvidenceV1 {
                event_id: event(index as u64),
                leaf_index: index as u64,
                root_sequence: index as u64 + 1,
                note_commitment: encode_digest_canonical(&leaves[index]),
                root: encode_digest_canonical(&reference_prefix_root(&leaves[..=index])),
            });
        }

        let mut state = WalletWitnessStateV1::empty();
        let receipts = state
            .apply_finalized_appends_v1(&appends, &[event(1), event(3)])
            .unwrap();
        assert_eq!(receipts.len(), appends.len());
        assert_eq!(state.tracked().len(), 2);
        assert!(state
            .tracked()
            .iter()
            .all(|witness| witness.root() == state.tree().root));

        let before = state.clone();
        let mut bad = appends[3];
        bad.leaf_index = 4;
        assert_eq!(
            state.apply_finalized_appends_v1(&[bad], &[]),
            Err(WitnessStateErrorV1::RootSequenceMismatch)
        );
        assert_eq!(state, before);
    }

    #[test]
    fn canonical_witness_image_round_trips_and_rejects_corruption() {
        let leaves: Vec<_> = (0..4).map(|index| digest(index + 1)).collect();
        let mut state = WalletWitnessStateV1::empty();
        for index in 0..leaves.len() {
            state
                .append_authenticated_leaf_v1(
                    index as u64,
                    index as u64 + 1,
                    encode_digest_canonical(&leaves[index]),
                    encode_digest_canonical(&reference_prefix_root(&leaves[..=index])),
                    [1usize, 3].contains(&index).then(|| event(index as u64)),
                )
                .unwrap();
        }
        let encoded = encode_wallet_witness_state_v1(&state).unwrap();
        assert_eq!(
            encoded.len(),
            WALLET_WITNESS_STATE_HEADER_BYTES_V1
                + POOL_V1_TREE_STATE_ACCOUNT_BYTES
                + 2 * WALLET_WITNESS_RECORD_BYTES_V1
        );
        assert_eq!(decode_wallet_witness_state_v1(&encoded).unwrap(), state);
        assert_eq!(
            encode_wallet_witness_state_v1(&decode_wallet_witness_state_v1(&encoded).unwrap())
                .unwrap(),
            encoded
        );

        let mut corrupt = encoded;
        *corrupt.last_mut().unwrap() ^= 1;
        assert_eq!(
            decode_wallet_witness_state_v1(&corrupt),
            Err(WitnessStateErrorV1::ChecksumMismatch)
        );
    }

    #[test]
    fn imported_and_authenticated_updates_fail_atomically_on_any_mismatch() {
        let mut state = WalletWitnessStateV1::empty();
        let leaf = digest(1);
        let root = reference_prefix_root(&[leaf]);
        state
            .append_authenticated_leaf_v1(
                0,
                1,
                encode_digest_canonical(&leaf),
                encode_digest_canonical(&root),
                Some(event(0)),
            )
            .unwrap();
        let before = state.clone();
        assert_eq!(
            state.append_authenticated_leaf_v1(
                1,
                2,
                encode_digest_canonical(&digest(2)),
                encode_digest_canonical(&digest(999)),
                None,
            ),
            Err(WitnessStateErrorV1::RootMismatch)
        );
        assert_eq!(state, before);

        let witness = *state.witness_v1(event(0)).unwrap();
        let siblings = witness.siblings.map(|node| encode_digest_canonical(&node));
        assert_eq!(
            state.import_current_witness_v1(
                event(0),
                witness.leaf_index,
                encode_digest_canonical(&witness.leaf),
                siblings,
            ),
            Err(WitnessStateErrorV1::DuplicateWitness)
        );
        let mut corrupt = siblings;
        corrupt[0] = encode_digest_canonical(&digest(700));
        assert_eq!(
            WalletWitnessStateV1::from_authenticated_tree_v1(
                *state.tree(),
                encode_digest_canonical(&state.tree().root),
            )
            .unwrap()
            .import_current_witness_v1(
                event(9),
                witness.leaf_index,
                encode_digest_canonical(&witness.leaf),
                corrupt,
            ),
            Err(WitnessStateErrorV1::InvalidWitness)
        );
    }
}
