//! 216-bit binary Merkle kernel for the selected V7 compact profile.
//!
//! SHA-256 remains the primitive.  Leaf and parent digests are the first 27
//! bytes of the domain-separated SHA-256 output.  A parent preimage is exactly
//! `0x11 || left27 || right27` (55 bytes), so it occupies one SHA-256 message
//! block including padding instead of the two blocks required by V6's 65-byte
//! parent preimage.

use alloc::vec::Vec;

use crate::state_only_private_merkle::private_leaf_hash;
use crate::HashFn;

pub const V7_MERKLE_DIGEST_BYTES: usize = 27;
pub const V7_MERKLE_PARENT_PREIMAGE_BYTES: usize = 1 + 2 * V7_MERKLE_DIGEST_BYTES;
pub const V7_C1_TREE_TAG: u8 = 0x71;
pub const V7_C2_TREE_TAG: u8 = 0xf1;

const DOM_NODE: u8 = 0x11;

pub type V7Digest = [u8; V7_MERKLE_DIGEST_BYTES];

#[inline(always)]
pub fn truncate_sha256(digest: [u8; 32]) -> V7Digest {
    digest[..V7_MERKLE_DIGEST_BYTES]
        .try_into()
        .expect("fixed 27-byte SHA-256 prefix")
}

#[inline]
pub fn private_leaf_hash216(hash: HashFn, tree_tag: u8, value: &[u8], salt: &[u8; 32]) -> V7Digest {
    truncate_sha256(private_leaf_hash(hash, tree_tag, value, salt))
}

#[inline]
pub fn node_hash216(hash: HashFn, left: &V7Digest, right: &V7Digest) -> V7Digest {
    let mut input = [0u8; V7_MERKLE_PARENT_PREIMAGE_BYTES];
    input[0] = DOM_NODE;
    input[1..1 + V7_MERKLE_DIGEST_BYTES].copy_from_slice(left);
    input[1 + V7_MERKLE_DIGEST_BYTES..].copy_from_slice(right);
    truncate_sha256(hash(&[&input]))
}

/// Verify two typed V7 trees over one sorted query topology.  The two hash
/// computations remain independent; only the public index walk and scratch
/// allocation are shared.  Both frontier streams must have the same exact
/// node count and are consumed without trailing bytes.
pub fn verify_two_minimal_subtrees216_bytes(
    hash: HashFn,
    roots: (&V7Digest, &V7Digest),
    depth: u32,
    entries: &[(u32, V7Digest, V7Digest)],
    node_bytes: (&[u8], &[u8]),
    level: &mut Vec<(u32, V7Digest, V7Digest)>,
    next: &mut Vec<(u32, V7Digest, V7Digest)>,
) -> bool {
    if entries.is_empty()
        || depth >= 32
        || node_bytes.0.len() % V7_MERKLE_DIGEST_BYTES != 0
        || node_bytes.1.len() % V7_MERKLE_DIGEST_BYTES != 0
        || node_bytes.0.len() != node_bytes.1.len()
    {
        return false;
    }
    if entries.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || entries.last().unwrap().0 >= (1u32 << depth)
    {
        return false;
    }

    let mut node_pos = 0usize;
    level.clear();
    level.extend_from_slice(entries);
    for _ in 0..depth {
        next.clear();
        let mut index = 0usize;
        while index < level.len() {
            let (position, c1, c2) = level[index];
            let parent = if position & 1 == 0
                && index + 1 < level.len()
                && level[index + 1].0 == position + 1
            {
                let (_, c1_right, c2_right) = level[index + 1];
                index += 2;
                (
                    node_hash216(hash, &c1, &c1_right),
                    node_hash216(hash, &c2, &c2_right),
                )
            } else {
                if node_pos + V7_MERKLE_DIGEST_BYTES > node_bytes.0.len() {
                    return false;
                }
                let c1_sibling: V7Digest = node_bytes.0
                    [node_pos..node_pos + V7_MERKLE_DIGEST_BYTES]
                    .try_into()
                    .unwrap();
                let c2_sibling: V7Digest = node_bytes.1
                    [node_pos..node_pos + V7_MERKLE_DIGEST_BYTES]
                    .try_into()
                    .unwrap();
                node_pos += V7_MERKLE_DIGEST_BYTES;
                index += 1;
                if position & 1 == 0 {
                    (
                        node_hash216(hash, &c1, &c1_sibling),
                        node_hash216(hash, &c2, &c2_sibling),
                    )
                } else {
                    (
                        node_hash216(hash, &c1_sibling, &c1),
                        node_hash216(hash, &c2_sibling, &c2),
                    )
                }
            };
            next.push((position >> 1, parent.0, parent.1));
        }
        core::mem::swap(level, next);
    }

    node_pos == node_bytes.0.len()
        && level.len() == 1
        && level[0].0 == 0
        && level[0].1 == *roots.0
        && level[0].2 == *roots.1
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn levels(mut leaves: Vec<V7Digest>) -> Vec<Vec<V7Digest>> {
        let mut output = vec![leaves.clone()];
        while leaves.len() > 1 {
            leaves = leaves
                .chunks_exact(2)
                .map(|pair| node_hash216(test_hash, &pair[0], &pair[1]))
                .collect();
            output.push(leaves.clone());
        }
        output
    }

    fn frontier(tree: &[Vec<V7Digest>], queries: &[u32]) -> Vec<V7Digest> {
        let mut active = queries.to_vec();
        active.sort_unstable();
        let mut output = Vec::new();
        for nodes in tree.iter().take(tree.len() - 1) {
            let mut parents = Vec::new();
            for &position in &active {
                if !active.contains(&(position ^ 1)) {
                    output.push(nodes[(position ^ 1) as usize]);
                }
                let parent = position >> 1;
                if parents.last().copied() != Some(parent) {
                    parents.push(parent);
                }
            }
            active = parents;
        }
        output
    }

    fn flatten(nodes: &[V7Digest]) -> Vec<u8> {
        nodes.iter().flat_map(|node| node.iter().copied()).collect()
    }

    #[test]
    fn parent_preimage_is_one_sha256_block_and_matches_literal_hash() {
        assert_eq!(V7_MERKLE_PARENT_PREIMAGE_BYTES, 55);
        let left = [0x31; V7_MERKLE_DIGEST_BYTES];
        let right = [0xa7; V7_MERKLE_DIGEST_BYTES];
        let actual = node_hash216(test_hash, &left, &right);
        let mut literal = [0u8; V7_MERKLE_PARENT_PREIMAGE_BYTES];
        literal[0] = DOM_NODE;
        literal[1..28].copy_from_slice(&left);
        literal[28..].copy_from_slice(&right);
        assert_eq!(actual, truncate_sha256(test_hash(&[&literal])));
    }

    #[test]
    fn paired_minimal_subtree_accepts_exact_frontiers_only() {
        const DEPTH: u32 = 4;
        let salt = [0x5a; 32];
        let c1_leaves: Vec<_> = (0u8..16)
            .map(|value| private_leaf_hash216(test_hash, V7_C1_TREE_TAG, &[value], &salt))
            .collect();
        let c2_leaves: Vec<_> = (0u8..16)
            .map(|value| {
                private_leaf_hash216(test_hash, V7_C2_TREE_TAG, &[value.wrapping_mul(7)], &salt)
            })
            .collect();
        let c1_tree = levels(c1_leaves.clone());
        let c2_tree = levels(c2_leaves.clone());
        let queries = [1u32, 4, 7, 12];
        let entries: Vec<_> = queries
            .iter()
            .copied()
            .map(|query| (query, c1_leaves[query as usize], c2_leaves[query as usize]))
            .collect();
        let c1_frontier = flatten(&frontier(&c1_tree, &queries));
        let c2_frontier = flatten(&frontier(&c2_tree, &queries));
        let roots = (
            c1_tree.last().unwrap().first().unwrap(),
            c2_tree.last().unwrap().first().unwrap(),
        );
        let mut level = Vec::new();
        let mut next = Vec::new();
        assert!(verify_two_minimal_subtrees216_bytes(
            test_hash,
            roots,
            DEPTH,
            &entries,
            (&c1_frontier, &c2_frontier),
            &mut level,
            &mut next,
        ));

        let mut changed = c2_frontier.clone();
        changed[17] ^= 1;
        assert!(!verify_two_minimal_subtrees216_bytes(
            test_hash,
            roots,
            DEPTH,
            &entries,
            (&c1_frontier, &changed),
            &mut level,
            &mut next,
        ));

        let mut trailing = c1_frontier.clone();
        trailing.extend_from_slice(&[0u8; V7_MERKLE_DIGEST_BYTES]);
        assert!(!verify_two_minimal_subtrees216_bytes(
            test_hash,
            roots,
            DEPTH,
            &entries,
            (&trailing, &c2_frontier),
            &mut level,
            &mut next,
        ));
    }
}
