//! 208-bit binary Merkle kernel for V7.
//!
//! SHA-256 remains the primitive. Leaf and parent digests are the first 26
//! bytes of the domain-separated SHA-256 output. A parent preimage is exactly
//! `0x11 || left26 || right26` (53 bytes), so it occupies one SHA-256 message
//! block including padding. The 104-bit generic collision bound remains above
//! V7's 100-bit security target.

use alloc::vec::Vec;

use crate::state_only_private_merkle::private_leaf_hash;
use crate::HashFn;

pub const V7_MERKLE_DIGEST_BYTES: usize = 26;
pub const V7_MERKLE_PARENT_PREIMAGE_BYTES: usize = 1 + 2 * V7_MERKLE_DIGEST_BYTES;
pub const V7_C1_TREE_TAG: u8 = 0x71;
pub const V7_C2_TREE_TAG: u8 = 0xf1;

const DOM_NODE: u8 = 0x11;

pub type V7Digest = [u8; V7_MERKLE_DIGEST_BYTES];

#[inline(always)]
pub fn truncate_sha256_v7(digest: [u8; 32]) -> V7Digest {
    digest[..V7_MERKLE_DIGEST_BYTES]
        .try_into()
        .expect("fixed 26-byte SHA-256 prefix")
}

#[inline]
pub fn private_leaf_hash_v7(hash: HashFn, tree_tag: u8, value: &[u8], salt: &[u8; 32]) -> V7Digest {
    truncate_sha256_v7(private_leaf_hash(hash, tree_tag, value, salt))
}

#[inline]
pub fn node_hash_v7(hash: HashFn, left: &V7Digest, right: &V7Digest) -> V7Digest {
    let mut input = [0u8; V7_MERKLE_PARENT_PREIMAGE_BYTES];
    input[0] = DOM_NODE;
    input[1..1 + V7_MERKLE_DIGEST_BYTES].copy_from_slice(left);
    input[1 + V7_MERKLE_DIGEST_BYTES..].copy_from_slice(right);
    truncate_sha256_v7(hash(&[&input]))
}

/// Verify both typed V7 trees over one sorted query topology. Hashes remain
/// independent; only the public index walk and scratch allocation are shared.
pub fn verify_two_minimal_subtrees_v7_bytes(
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
                    node_hash_v7(hash, &c1, &c1_right),
                    node_hash_v7(hash, &c2, &c2_right),
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
                        node_hash_v7(hash, &c1, &c1_sibling),
                        node_hash_v7(hash, &c2, &c2_sibling),
                    )
                } else {
                    (
                        node_hash_v7(hash, &c1_sibling, &c1),
                        node_hash_v7(hash, &c2_sibling, &c2),
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
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    #[test]
    fn parent_preimage_is_one_block_and_exact() {
        assert_eq!(V7_MERKLE_PARENT_PREIMAGE_BYTES, 53);
        let left = [0x31; V7_MERKLE_DIGEST_BYTES];
        let right = [0xa7; V7_MERKLE_DIGEST_BYTES];
        let mut literal = [0u8; V7_MERKLE_PARENT_PREIMAGE_BYTES];
        literal[0] = DOM_NODE;
        literal[1..1 + V7_MERKLE_DIGEST_BYTES].copy_from_slice(&left);
        literal[1 + V7_MERKLE_DIGEST_BYTES..].copy_from_slice(&right);
        assert_eq!(
            node_hash_v7(test_hash, &left, &right),
            truncate_sha256_v7(test_hash(&[&literal]))
        );
    }
}
