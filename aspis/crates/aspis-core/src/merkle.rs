//! SHA-256 Merkle commitments over fiber-packed leaves.
//!
//! One leaf commits one whole fold fiber (4 values at stride N/4), so each
//! query costs exactly one opening per layer. Two opening packagings:
//! `SinglePaths` (independent authentication paths) and `MinimalSubtree`
//! (deduplicated multiproof — the Phase 2 `minimal_subtree` win).

use alloc::vec::Vec;

use crate::transcript::HashFn;

const DOM_LEAF: u8 = 0x10;
const DOM_NODE: u8 = 0x11;
const DOM_NODE4: u8 = 0x12;

pub fn leaf_hash(hash: HashFn, layer: u8, leaf_bytes: &[u8]) -> [u8; 32] {
    hash(&[&[DOM_LEAF, layer], leaf_bytes])
}

pub fn node_hash(hash: HashFn, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    // `hashv` hashes the concatenation of its slices. Pack the fixed-size
    // node into one stack buffer so the SBF syscall translates one slice
    // descriptor instead of three; digest bytes are unchanged.
    let mut input = [0u8; 65];
    input[0] = DOM_NODE;
    input[1..33].copy_from_slice(left);
    input[33..65].copy_from_slice(right);
    hash(&[&input])
}

/// Domain-separated radix-4 parent compression. One syscall hashes all four
/// children; this is the structural CU win over two binary levels.
pub fn node_hash4(hash: HashFn, children: &[[u8; 32]; 4]) -> [u8; 32] {
    let mut input = [0u8; 129];
    input[0] = DOM_NODE4;
    for (slot, child) in children.iter().enumerate() {
        input[1 + slot * 32..1 + (slot + 1) * 32].copy_from_slice(child);
    }
    hash(&[&input])
}

/// Verify one independent authentication path.
/// `path` is `depth` sibling hashes, leaf level first.
pub fn verify_single_path(
    hash: HashFn,
    root: &[u8; 32],
    depth: u32,
    mut index: u32,
    leaf: [u8; 32],
    path: &[[u8; 32]],
) -> bool {
    if path.len() != depth as usize {
        return false;
    }
    let mut acc = leaf;
    for sibling in path {
        acc = if index & 1 == 0 {
            node_hash(hash, &acc, sibling)
        } else {
            node_hash(hash, sibling, &acc)
        };
        index >>= 1;
    }
    index == 0 && acc == *root
}

/// Allocation-free sibling-path verifier. `path_bytes` is `depth` sibling
/// hashes, leaf level first.
pub fn verify_single_path_bytes(
    hash: HashFn,
    root: &[u8; 32],
    depth: u32,
    mut index: u32,
    leaf: [u8; 32],
    path_bytes: &[u8],
) -> bool {
    if path_bytes.len() != depth as usize * 32 {
        return false;
    }
    let mut acc = leaf;
    for sibling in path_bytes.chunks_exact(32) {
        let sibling: [u8; 32] = sibling.try_into().unwrap();
        acc = if index & 1 == 0 {
            node_hash(hash, &acc, &sibling)
        } else {
            node_hash(hash, &sibling, &acc)
        };
        index >>= 1;
    }
    index == 0 && acc == *root
}

/// Verify a deduplicated multiproof for `entries` = sorted, unique
/// (leaf_index, leaf_hash) pairs. `nodes` supplies the frontier siblings in
/// deterministic traversal order (level by level, ascending index, a sibling
/// consumed only when its subtree is not derivable from the entry set).
/// Returns true iff the root matches and the node stream is fully consumed.
pub fn verify_minimal_subtree(
    hash: HashFn,
    root: &[u8; 32],
    depth: u32,
    entries: &[(u32, [u8; 32])],
    nodes: &[[u8; 32]],
) -> bool {
    if entries.is_empty() || depth >= 32 {
        return false;
    }
    // check sorted unique and in range
    for pair in entries.windows(2) {
        if pair[0].0 >= pair[1].0 {
            return false;
        }
    }
    if entries.last().unwrap().0 >= (1u32 << depth) {
        return false;
    }

    let mut stream = nodes.iter();
    let mut level: Vec<(u32, [u8; 32])> = entries.to_vec();
    for _ in 0..depth {
        let mut next: Vec<(u32, [u8; 32])> = Vec::with_capacity(level.len());
        let mut i = 0;
        while i < level.len() {
            let (idx, h) = level[i];
            let parent = if idx & 1 == 0 {
                if i + 1 < level.len() && level[i + 1].0 == idx + 1 {
                    let combined = node_hash(hash, &h, &level[i + 1].1);
                    i += 2;
                    combined
                } else {
                    let Some(sib) = stream.next() else {
                        return false;
                    };
                    i += 1;
                    node_hash(hash, &h, sib)
                }
            } else {
                let Some(sib) = stream.next() else {
                    return false;
                };
                i += 1;
                node_hash(hash, sib, &h)
            };
            next.push((idx >> 1, parent));
        }
        level = next;
    }
    stream.next().is_none() && level.len() == 1 && level[0].0 == 0 && level[0].1 == *root
}

/// Allocation-reusing minimal-subtree verifier. `node_bytes` is the same node
/// stream as `verify_minimal_subtree`, encoded as contiguous 32-byte hashes.
/// `level` and `next` are caller-owned scratch buffers reused across layers.
pub fn verify_minimal_subtree_bytes(
    hash: HashFn,
    root: &[u8; 32],
    depth: u32,
    entries: &[(u32, [u8; 32])],
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if entries.is_empty() || depth >= 32 || node_bytes.len() & 31 != 0 {
        return false;
    }
    for pair in entries.windows(2) {
        if pair[0].0 >= pair[1].0 {
            return false;
        }
    }
    if entries.last().unwrap().0 >= (1u32 << depth) {
        return false;
    }

    let mut node_pos = 0usize;
    level.clear();
    level.extend_from_slice(entries);
    for _ in 0..depth {
        next.clear();
        let mut i = 0;
        while i < level.len() {
            let (idx, h) = level[i];
            let parent = if idx & 1 == 0 {
                if i + 1 < level.len() && level[i + 1].0 == idx + 1 {
                    let combined = node_hash(hash, &h, &level[i + 1].1);
                    i += 2;
                    combined
                } else {
                    if node_pos + 32 > node_bytes.len() {
                        return false;
                    }
                    let sib: [u8; 32] = node_bytes[node_pos..node_pos + 32].try_into().unwrap();
                    node_pos += 32;
                    i += 1;
                    node_hash(hash, &h, &sib)
                }
            } else {
                if node_pos + 32 > node_bytes.len() {
                    return false;
                }
                let sib: [u8; 32] = node_bytes[node_pos..node_pos + 32].try_into().unwrap();
                node_pos += 32;
                i += 1;
                node_hash(hash, &sib, &h)
            };
            next.push((idx >> 1, parent));
        }
        core::mem::swap(level, next);
    }
    node_pos == node_bytes.len() && level.len() == 1 && level[0].0 == 0 && level[0].1 == *root
}

/// Allocation-reusing radix-4 minimal-subtree verifier.
///
/// `binary_depth` is log2(number of leaves), so it must be even. Frontier
/// nodes are consumed level-by-level, parent-index order, and child-slot
/// order; any child derivable from `entries` is omitted from the stream.
pub fn verify_radix4_minimal_subtree_bytes(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    entries: &[(u32, [u8; 32])],
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if entries.is_empty() || binary_depth & 1 != 0 || node_bytes.len() & 31 != 0 {
        return false;
    }
    for pair in entries.windows(2) {
        if pair[0].0 >= pair[1].0 {
            return false;
        }
    }
    if binary_depth >= 32 || entries.last().unwrap().0 >= (1u32 << binary_depth) {
        return false;
    }

    let mut node_pos = 0usize;
    level.clear();
    level.extend_from_slice(entries);
    for _ in 0..binary_depth / 2 {
        next.clear();
        let mut position = 0usize;
        while position < level.len() {
            let parent_index = level[position].0 >> 2;
            let mut children = [[0u8; 32]; 4];
            let mut present = 0u8;
            while position < level.len() && level[position].0 >> 2 == parent_index {
                let slot = (level[position].0 & 3) as usize;
                let slot_mask = 1u8 << slot;
                if present & slot_mask != 0 {
                    return false;
                }
                children[slot] = level[position].1;
                present |= slot_mask;
                position += 1;
            }
            for (slot, child) in children.iter_mut().enumerate() {
                if present & (1u8 << slot) == 0 {
                    if node_pos + 32 > node_bytes.len() {
                        return false;
                    }
                    *child = node_bytes[node_pos..node_pos + 32].try_into().unwrap();
                    node_pos += 32;
                }
            }
            next.push((parent_index, node_hash4(hash, &children)));
        }
        core::mem::swap(level, next);
    }

    node_pos == node_bytes.len() && level.len() == 1 && level[0].0 == 0 && level[0].1 == *root
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        for i in inputs {
            h.update(i);
        }
        h.finalize().into()
    }

    fn build_tree(leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let mut next = Vec::with_capacity(prev.len() / 2);
            for pair in prev.chunks_exact(2) {
                next.push(node_hash(test_hash, &pair[0], &pair[1]));
            }
            levels.push(next);
        }
        levels
    }

    fn build_tree4(leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let mut next = Vec::with_capacity(prev.len() / 4);
            for children in prev.chunks_exact(4) {
                next.push(node_hash4(test_hash, children.try_into().unwrap()));
            }
            levels.push(next);
        }
        levels
    }

    #[test]
    fn single_path_roundtrip() {
        let leaves: Vec<[u8; 32]> = (0u32..16)
            .map(|i| leaf_hash(test_hash, 0, &i.to_le_bytes()))
            .collect();
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];
        for index in [0u32, 5, 15] {
            let mut path = Vec::new();
            let mut idx = index;
            for level in &levels[..levels.len() - 1] {
                path.push(level[(idx ^ 1) as usize]);
                idx >>= 1;
            }
            assert!(verify_single_path(
                test_hash,
                &root,
                4,
                index,
                leaves[index as usize],
                &path
            ));
            // wrong index fails
            assert!(!verify_single_path(
                test_hash,
                &root,
                4,
                index ^ 1,
                leaves[index as usize],
                &path
            ));
        }
    }

    #[test]
    fn minimal_subtree_roundtrip() {
        let leaves: Vec<[u8; 32]> = (0u32..32)
            .map(|i| leaf_hash(test_hash, 3, &i.to_le_bytes()))
            .collect();
        let levels = build_tree(&leaves);
        let root = levels.last().unwrap()[0];
        let indices = [1u32, 4, 5, 19, 30];
        // prover-side emission mirrors the verifier traversal
        let entries: Vec<(u32, [u8; 32])> =
            indices.iter().map(|&i| (i, leaves[i as usize])).collect();
        let nodes = crate::merkle::tests::emit_nodes(&levels, &indices);
        assert!(verify_minimal_subtree(
            test_hash, &root, 5, &entries, &nodes
        ));
        // truncated stream fails
        assert!(!verify_minimal_subtree(
            test_hash,
            &root,
            5,
            &entries,
            &nodes[..nodes.len() - 1]
        ));
        // extra node fails
        let mut extra = nodes.clone();
        extra.push([0u8; 32]);
        assert!(!verify_minimal_subtree(
            test_hash, &root, 5, &entries, &extra
        ));
    }

    #[test]
    fn binary_minimal_subtree_rejects_unrepresentable_depth() {
        let root = [0u8; 32];
        let entries = [(0u32, [0u8; 32])];
        assert!(!verify_minimal_subtree(test_hash, &root, 32, &entries, &[],));

        let mut level = Vec::new();
        let mut next = Vec::new();
        assert!(!verify_minimal_subtree_bytes(
            test_hash,
            &root,
            32,
            &entries,
            &[],
            &mut level,
            &mut next,
        ));
    }

    #[test]
    fn radix4_minimal_subtree_roundtrip_and_framing() {
        let leaves: Vec<[u8; 32]> = (0u32..64)
            .map(|i| leaf_hash(test_hash, 7, &i.to_le_bytes()))
            .collect();
        let levels = build_tree4(&leaves);
        let root = levels.last().unwrap()[0];
        let indices = [0u32, 1, 4, 7, 19, 30, 63];
        let entries: Vec<(u32, [u8; 32])> =
            indices.iter().map(|&i| (i, leaves[i as usize])).collect();
        let nodes = emit_nodes4(&levels, &indices);
        let node_bytes = nodes.iter().flatten().copied().collect::<Vec<_>>();
        let mut level = Vec::new();
        let mut next = Vec::new();

        assert!(verify_radix4_minimal_subtree_bytes(
            test_hash,
            &root,
            6,
            &entries,
            &node_bytes,
            &mut level,
            &mut next,
        ));
        assert!(!verify_radix4_minimal_subtree_bytes(
            test_hash,
            &root,
            5,
            &entries,
            &node_bytes,
            &mut level,
            &mut next,
        ));
        assert!(!verify_radix4_minimal_subtree_bytes(
            test_hash,
            &root,
            6,
            &entries,
            &node_bytes[..node_bytes.len() - 32],
            &mut level,
            &mut next,
        ));
        let mut extra = node_bytes.clone();
        extra.extend_from_slice(&[0u8; 32]);
        assert!(!verify_radix4_minimal_subtree_bytes(
            test_hash, &root, 6, &entries, &extra, &mut level, &mut next,
        ));
    }

    pub(crate) fn emit_nodes(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
        let mut nodes = Vec::new();
        let mut level_indices: Vec<u32> = indices.to_vec();
        for level in &levels[..levels.len() - 1] {
            let mut next = Vec::new();
            let mut i = 0;
            while i < level_indices.len() {
                let idx = level_indices[i];
                if idx & 1 == 0 {
                    if i + 1 < level_indices.len() && level_indices[i + 1] == idx + 1 {
                        i += 2;
                    } else {
                        nodes.push(level[(idx + 1) as usize]);
                        i += 1;
                    }
                } else {
                    nodes.push(level[(idx - 1) as usize]);
                    i += 1;
                }
                next.push(idx >> 1);
            }
            level_indices = next;
        }
        nodes
    }

    fn emit_nodes4(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
        let mut nodes = Vec::new();
        let mut level_indices = indices.to_vec();
        for level in &levels[..levels.len() - 1] {
            let mut next = Vec::new();
            let mut position = 0usize;
            while position < level_indices.len() {
                let parent = level_indices[position] >> 2;
                let mut present = 0u8;
                while position < level_indices.len() && level_indices[position] >> 2 == parent {
                    present |= 1u8 << (level_indices[position] & 3);
                    position += 1;
                }
                for slot in 0..4u32 {
                    if present & (1u8 << slot) == 0 {
                        nodes.push(level[(parent * 4 + slot) as usize]);
                    }
                }
                next.push(parent);
            }
            level_indices = next;
        }
        nodes
    }
}
