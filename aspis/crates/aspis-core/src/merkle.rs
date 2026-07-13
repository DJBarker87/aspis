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
    level.clear();
    level.extend_from_slice(entries);
    verify_radix4_minimal_subtree_level_bytes(hash, root, binary_depth, node_bytes, level, next)
}

/// Verify a radix-4 frontier when the caller has already populated `level`
/// with sorted, unique, in-range leaf entries derived from transcript
/// queries. This removes the temporary entry vector and copy in composed
/// circle verification while retaining all proof-byte framing checks.
pub(crate) fn verify_radix4_minimal_subtree_prevalidated_in_place(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if level.is_empty()
        || binary_depth & 1 != 0
        || binary_depth >= 32
        || node_bytes.len() & 31 != 0
        || level.last().unwrap().0 >= (1u32 << binary_depth)
    {
        return false;
    }
    verify_radix4_minimal_subtree_level_bytes(hash, root, binary_depth, node_bytes, level, next)
}

/// Radix-4 minimal-subtree verifier with an optional final binary cap.
///
/// Even binary depths are byte-identical to the existing radix-4 verifier.
/// An odd depth performs `(depth-1)/2` radix-4 levels and authenticates the
/// remaining two nodes with the ordinary domain-separated binary parent.
/// This is the exact tree needed by rate-1/32 depths 13/11/9/7.
pub fn verify_radix4_binary_cap_minimal_subtree_bytes(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    entries: &[(u32, [u8; 32])],
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if entries.is_empty() || binary_depth >= 32 || node_bytes.len() & 31 != 0 {
        return false;
    }
    for pair in entries.windows(2) {
        if pair[0].0 >= pair[1].0 {
            return false;
        }
    }
    if entries.last().unwrap().0 >= (1u32 << binary_depth) {
        return false;
    }
    level.clear();
    level.extend_from_slice(entries);
    verify_radix4_binary_cap_level_bytes(hash, root, binary_depth, node_bytes, level, next)
}

pub(crate) fn verify_radix4_binary_cap_prevalidated_in_place(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if level.is_empty()
        || binary_depth >= 32
        || node_bytes.len() & 31 != 0
        || level.last().unwrap().0 >= (1u32 << binary_depth)
    {
        return false;
    }
    if binary_depth & 1 == 0 {
        return verify_radix4_minimal_subtree_level_bytes(
            hash,
            root,
            binary_depth,
            node_bytes,
            level,
            next,
        );
    }
    verify_radix4_binary_cap_level_bytes(hash, root, binary_depth, node_bytes, level, next)
}

fn verify_radix4_binary_cap_level_bytes(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    if binary_depth & 1 == 0 {
        return verify_radix4_minimal_subtree_level_bytes(
            hash,
            root,
            binary_depth,
            node_bytes,
            level,
            next,
        );
    }
    let mut node_pos = 0usize;
    for _ in 0..binary_depth / 2 {
        next.clear();
        let mut position = 0usize;
        while position < level.len() {
            let parent_index = level[position].0 >> 2;
            let mut children = [[0u8; 32]; 4];
            let mut present = 0u8;
            while position < level.len() && level[position].0 >> 2 == parent_index {
                let slot = (level[position].0 & 3) as usize;
                if present & (1 << slot) != 0 {
                    return false;
                }
                children[slot] = level[position].1;
                present |= 1 << slot;
                position += 1;
            }
            for (slot, child) in children.iter_mut().enumerate() {
                if present & (1 << slot) == 0 {
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

    let top = match level.as_slice() {
        [(0, left), (1, right)] => node_hash(hash, left, right),
        [(index, value)] => {
            if node_pos + 32 > node_bytes.len() {
                return false;
            }
            let sibling: [u8; 32] = node_bytes[node_pos..node_pos + 32].try_into().unwrap();
            node_pos += 32;
            if *index == 0 {
                node_hash(hash, value, &sibling)
            } else if *index == 1 {
                node_hash(hash, &sibling, value)
            } else {
                return false;
            }
        }
        _ => return false,
    };
    node_pos == node_bytes.len() && top == *root
}

fn verify_radix4_minimal_subtree_level_bytes(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    node_bytes: &[u8],
    level: &mut Vec<(u32, [u8; 32])>,
    next: &mut Vec<(u32, [u8; 32])>,
) -> bool {
    let mut node_pos = 0usize;
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

    fn build_tree4_binary_cap(leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let previous = levels.last().unwrap();
            let next = if previous.len() == 2 {
                vec![node_hash(test_hash, &previous[0], &previous[1])]
            } else {
                previous
                    .chunks_exact(4)
                    .map(|children| node_hash4(test_hash, children.try_into().unwrap()))
                    .collect()
            };
            levels.push(next);
        }
        levels
    }

    fn frontier4_binary_cap(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
        let mut result = Vec::new();
        let mut current = indices.to_vec();
        for level in &levels[..levels.len() - 1] {
            if level.len() == 2 {
                if current.len() == 1 {
                    result.push(level[(current[0] ^ 1) as usize]);
                }
                current = vec![0];
                continue;
            }
            let mut next = Vec::new();
            let mut position = 0;
            while position < current.len() {
                let parent = current[position] >> 2;
                let mut present = 0u8;
                while position < current.len() && current[position] >> 2 == parent {
                    present |= 1 << (current[position] & 3);
                    position += 1;
                }
                for slot in 0..4u32 {
                    if present & (1 << slot) == 0 {
                        result.push(level[(4 * parent + slot) as usize]);
                    }
                }
                next.push(parent);
            }
            current = next;
        }
        result
    }

    #[test]
    fn radix4_binary_cap_roundtrips_odd_depths_and_rejects_framing() {
        for depth in [7u32, 9, 11, 13] {
            let leaves = (0..1usize << depth)
                .map(|index| test_hash(&[&index.to_le_bytes()]))
                .collect::<Vec<_>>();
            let levels = build_tree4_binary_cap(&leaves);
            let indices = [1u32, 7, (1u32 << depth) - 2];
            let entries = indices
                .into_iter()
                .map(|index| (index, leaves[index as usize]))
                .collect::<Vec<_>>();
            let frontier = frontier4_binary_cap(&levels, &indices);
            let bytes = frontier.iter().flatten().copied().collect::<Vec<_>>();
            let mut level = Vec::new();
            let mut next = Vec::new();
            assert!(verify_radix4_binary_cap_minimal_subtree_bytes(
                test_hash,
                &levels.last().unwrap()[0],
                depth,
                &entries,
                &bytes,
                &mut level,
                &mut next,
            ));
            let mut trailing = bytes.clone();
            trailing.extend_from_slice(&[0u8; 32]);
            assert!(!verify_radix4_binary_cap_minimal_subtree_bytes(
                test_hash,
                &levels.last().unwrap()[0],
                depth,
                &entries,
                &trailing,
                &mut level,
                &mut next,
            ));
        }
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

    #[test]
    fn prevalidated_in_place_matches_eager_radix4_across_depths_and_corruptions() {
        let mut state = 0x5241_4449_5834_4449u64;
        for depth in [2u32, 4, 6, 8, 10, 12] {
            let leaf_count = 1usize << depth;
            let leaves = (0..leaf_count)
                .map(|index| leaf_hash(test_hash, depth as u8, &(index as u32).to_le_bytes()))
                .collect::<Vec<_>>();
            let tree = build_tree4(&leaves);
            let root = tree.last().unwrap()[0];
            let target_count = core::cmp::min(36, leaf_count);
            let mut indices = Vec::with_capacity(target_count);
            while indices.len() < target_count {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let candidate = ((state >> 32) as usize & (leaf_count - 1)) as u32;
                if !indices.contains(&candidate) {
                    indices.push(candidate);
                }
            }
            indices.sort_unstable();
            let entries = indices
                .iter()
                .map(|&index| (index, leaves[index as usize]))
                .collect::<Vec<_>>();
            let frontier = emit_nodes4(&tree, &indices)
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();

            let compare = |root: &[u8; 32], frontier: &[u8]| {
                let mut eager_level = Vec::new();
                let mut eager_next = Vec::new();
                let eager = verify_radix4_minimal_subtree_bytes(
                    test_hash,
                    root,
                    depth,
                    &entries,
                    frontier,
                    &mut eager_level,
                    &mut eager_next,
                );
                let mut optimized_level = entries.clone();
                let mut optimized_next = Vec::with_capacity(entries.len());
                let optimized = verify_radix4_minimal_subtree_prevalidated_in_place(
                    test_hash,
                    root,
                    depth,
                    frontier,
                    &mut optimized_level,
                    &mut optimized_next,
                );
                assert_eq!(optimized, eager, "depth={depth}");
            };

            compare(&root, &frontier);
            let mut wrong_root = root;
            wrong_root[0] ^= 1;
            compare(&wrong_root, &frontier);
            if !frontier.is_empty() {
                let mut corrupted = frontier.clone();
                corrupted[frontier.len() / 2] ^= 1;
                compare(&root, &corrupted);
                compare(&root, &frontier[..frontier.len() - 32]);
            }
            let mut extra = frontier.clone();
            extra.extend_from_slice(&[0u8; 32]);
            compare(&root, &extra);
        }
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
