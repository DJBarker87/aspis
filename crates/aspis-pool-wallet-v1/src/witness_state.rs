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
        POOL_V1_LEAF_CAPACITY, POOL_V1_TREE_DEPTH,
    },
    Digest,
};

use crate::scan_state::DepositEventIdV1;

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
}

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
