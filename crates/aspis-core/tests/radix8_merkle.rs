use std::collections::BTreeMap;

use aspis_core::merkle_radix8::{node_hash8, verify_radix8_minimal_subtree_bytes, DOM_NODE8};
use sha2::{Digest, Sha256};

fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}

/// Deliberately does not call the production parent helper.
fn reference_parent(children: &[[u8; 32]; 8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update([DOM_NODE8]);
    for child in children {
        hasher.update(child);
    }
    hasher.finalize().into()
}

fn deterministic_leaves(count: usize) -> Vec<[u8; 32]> {
    (0..count)
        .map(|index| {
            let mut hasher = Sha256::new();
            hasher.update(b"aspis-independent-radix8-leaf");
            hasher.update((index as u32).to_le_bytes());
            hasher.finalize().into()
        })
        .collect()
}

/// Independent full-tree construction using the direct SHA reference above.
fn build_reference_tree(leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
    assert!(leaves.len().is_power_of_two());
    assert_eq!(leaves.len().trailing_zeros() % 3, 0);
    let mut levels = vec![leaves.to_vec()];
    while levels.last().unwrap().len() > 1 {
        let prior = levels.last().unwrap();
        let next = prior
            .chunks_exact(8)
            .map(|children| reference_parent(children.try_into().unwrap()))
            .collect();
        levels.push(next);
    }
    levels
}

/// Prover-side deterministic frontier emission, kept outside the core module.
fn emit_reference_frontier(tree: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<u8> {
    let mut frontier = Vec::new();
    let mut active = indices.to_vec();
    for level in &tree[..tree.len() - 1] {
        let mut parents = Vec::new();
        let mut position = 0usize;
        while position < active.len() {
            let parent = active[position] / 8;
            let mut present = [false; 8];
            while position < active.len() && active[position] / 8 == parent {
                present[(active[position] % 8) as usize] = true;
                position += 1;
            }
            for slot in 0..8u32 {
                if !present[slot as usize] {
                    frontier.extend_from_slice(&level[(parent * 8 + slot) as usize]);
                }
            }
            parents.push(parent);
        }
        active = parents;
    }
    frontier
}

/// Map-based verifier used only as a differential oracle. Its traversal and
/// parent compression do not call either production implementation helper.
fn reference_verify(
    root: &[u8; 32],
    binary_depth: u32,
    entries: &[(u32, [u8; 32])],
    frontier: &[u8],
) -> bool {
    if entries.is_empty()
        || binary_depth % 3 != 0
        || binary_depth >= 32
        || frontier.len() % 32 != 0
        || entries.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || entries.last().unwrap().0 >= (1u32 << binary_depth)
    {
        return false;
    }

    let mut active = entries.iter().copied().collect::<BTreeMap<_, _>>();
    let mut frontier_chunks = frontier.chunks_exact(32);
    for _ in 0..binary_depth / 3 {
        let parent_indices = active
            .keys()
            .map(|index| index / 8)
            .collect::<std::collections::BTreeSet<_>>();
        let mut next = BTreeMap::new();
        for parent in parent_indices {
            let mut children = [[0u8; 32]; 8];
            for slot in 0..8u32 {
                let child_index = parent * 8 + slot;
                children[slot as usize] = if let Some(value) = active.remove(&child_index) {
                    value
                } else if let Some(bytes) = frontier_chunks.next() {
                    bytes.try_into().unwrap()
                } else {
                    return false;
                };
            }
            next.insert(parent, reference_parent(&children));
        }
        if !active.is_empty() {
            return false;
        }
        active = next;
    }
    frontier_chunks.next().is_none() && active.get(&0) == Some(root) && active.len() == 1
}

fn production_verify(
    root: &[u8; 32],
    binary_depth: u32,
    entries: &[(u32, [u8; 32])],
    frontier: &[u8],
) -> bool {
    verify_radix8_minimal_subtree_bytes(
        sha256,
        root,
        binary_depth,
        entries,
        frontier,
        &mut Vec::new(),
        &mut Vec::new(),
    )
}

fn sample_indices(state: &mut u64, leaf_count: usize, count: usize) -> Vec<u32> {
    let mut indices = Vec::with_capacity(count);
    while indices.len() < count {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let candidate = ((*state >> 32) as usize & (leaf_count - 1)) as u32;
        if !indices.contains(&candidate) {
            indices.push(candidate);
        }
    }
    indices.sort_unstable();
    indices
}

fn frontier_geometry(indices: &[u32], arity: u32, levels: usize) -> (usize, usize) {
    let mut active = indices.to_vec();
    let mut frontier_hashes = 0usize;
    let mut occupied_parent_hashes = 0usize;
    for _ in 0..levels {
        let child_count = active.len();
        for index in &mut active {
            *index /= arity;
        }
        active.dedup();
        occupied_parent_hashes += active.len();
        frontier_hashes += arity as usize * active.len() - child_count;
    }
    (frontier_hashes, occupied_parent_hashes)
}

#[test]
fn reference_parent_matches_production_for_fresh_inputs() {
    let mut state = 0x5241_4438_5041_5245u64;
    for _ in 0..64 {
        let mut children = [[0u8; 32]; 8];
        for child in &mut children {
            for byte in child {
                state = state
                    .wrapping_mul(2_862_933_555_777_941_757)
                    .wrapping_add(3_037_000_493);
                *byte = (state >> 56) as u8;
            }
        }
        assert_eq!(node_hash8(sha256, &children), reference_parent(&children));
    }
}

#[test]
fn randomized_roundtrips_match_independent_reference() {
    let mut state = 0x4153_5049_535f_5238u64;
    for depth in [3u32, 6, 9, 12] {
        let leaf_count = 1usize << depth;
        let leaves = deterministic_leaves(leaf_count);
        let tree = build_reference_tree(&leaves);
        let root = tree.last().unwrap()[0];
        for requested in [1usize, 2, 7, 8, 9, 36] {
            let count = requested.min(leaf_count);
            for _ in 0..4 {
                let indices = sample_indices(&mut state, leaf_count, count);
                let entries = indices
                    .iter()
                    .map(|&index| (index, leaves[index as usize]))
                    .collect::<Vec<_>>();
                let frontier = emit_reference_frontier(&tree, &indices);
                assert!(reference_verify(&root, depth, &entries, &frontier));
                assert!(production_verify(&root, depth, &entries, &frontier));
            }
        }
    }
}

#[test]
fn corruption_and_framing_corpus_matches_independent_reference() {
    let depth = 12u32;
    let leaves = deterministic_leaves(1usize << depth);
    let tree = build_reference_tree(&leaves);
    let root = tree.last().unwrap()[0];
    let mut state = 0x5445_4554_485f_5238u64;
    let indices = sample_indices(&mut state, leaves.len(), 36);
    let entries = indices
        .iter()
        .map(|&index| (index, leaves[index as usize]))
        .collect::<Vec<_>>();
    let frontier = emit_reference_frontier(&tree, &indices);

    let agree = |root: &[u8; 32], depth: u32, entries: &[(u32, [u8; 32])], bytes: &[u8]| {
        assert_eq!(
            production_verify(root, depth, entries, bytes),
            reference_verify(root, depth, entries, bytes)
        );
    };

    agree(&root, depth, &entries, &frontier);

    let mut wrong_root = root;
    wrong_root[17] ^= 0x80;
    agree(&wrong_root, depth, &entries, &frontier);
    assert!(!production_verify(&wrong_root, depth, &entries, &frontier));

    for hash_index in [0, frontier.len() / 64, frontier.len() / 32 - 1] {
        let mut corrupted = frontier.clone();
        corrupted[hash_index * 32 + (hash_index % 32)] ^= 1;
        agree(&root, depth, &entries, &corrupted);
        assert!(!production_verify(&root, depth, &entries, &corrupted));
    }

    let mut wrong_leaf = entries.clone();
    wrong_leaf[entries.len() / 2].1[9] ^= 1;
    agree(&root, depth, &wrong_leaf, &frontier);
    assert!(!production_verify(&root, depth, &wrong_leaf, &frontier));

    let truncated = &frontier[..frontier.len() - 32];
    agree(&root, depth, &entries, truncated);
    assert!(!production_verify(&root, depth, &entries, truncated));

    let mut extra = frontier.clone();
    extra.extend_from_slice(&[0x5a; 32]);
    agree(&root, depth, &entries, &extra);
    assert!(!production_verify(&root, depth, &entries, &extra));

    let malformed = &frontier[..frontier.len() - 1];
    agree(&root, depth, &entries, malformed);
    assert!(!production_verify(&root, depth, &entries, malformed));

    let mut unsorted = entries.clone();
    unsorted.swap(0, 1);
    agree(&root, depth, &unsorted, &frontier);
    assert!(!production_verify(&root, depth, &unsorted, &frontier));

    let mut duplicate = entries.clone();
    duplicate[1].0 = duplicate[0].0;
    agree(&root, depth, &duplicate, &frontier);
    assert!(!production_verify(&root, depth, &duplicate, &frontier));

    let mut out_of_range = entries.clone();
    out_of_range[entries.len() - 1].0 = 1u32 << depth;
    agree(&root, depth, &out_of_range, &frontier);
    assert!(!production_verify(&root, depth, &out_of_range, &frontier));

    for invalid_depth in [1u32, 2, 4, 5, 31, 32] {
        agree(&root, invalid_depth, &entries, &frontier);
        assert!(!production_verify(
            &root,
            invalid_depth,
            &entries,
            &frontier
        ));
    }
}

#[test]
fn q36_depth12_fixed_geometry_is_pinned() {
    let leaves = deterministic_leaves(1usize << 12);
    let tree = build_reference_tree(&leaves);
    let mut state = 0x4745_4f4d_4554_5259u64;
    let indices = sample_indices(&mut state, leaves.len(), 36);
    let frontier = emit_reference_frontier(&tree, &indices);

    // A stable, collision-free fixture for later host/SBF measurement. These
    // are fixture counts, not the sampling-without-replacement expectation.
    let radix8 = frontier_geometry(&indices, 8, 4);
    assert_eq!(radix8, (469, 72));
    assert_eq!(frontier.len() / 32, radix8.0);

    // Same exact leaf fixture under the current radix-4 geometry. This pins
    // the A/B input rather than comparing unrelated transcript draws.
    assert_eq!(frontier_geometry(&indices, 4, 6), (301, 112));
}
