//! Experimental, production-neutral verifier for a staggered radix-4 forest.
//!
//! The five circle commitments authenticate the same query topology at
//! staggered levels: C1/C2 start at `q`, then the three fold trees start at
//! `q >> 2`, `q >> 4`, and `q >> 6`.  Verifying the trees independently
//! repeats the index grouping walk.  This candidate performs that public
//! geometry walk once while retaining independent roots, leaf digests,
//! frontier streams, and SHA-256 calls for every commitment.

use alloc::vec::Vec;

use crate::{merkle::node_hash4, HashFn};

/// One independently committed tree in a shared radix-4 query geometry.
///
/// `start_level` is measured in radix-4 levels from the base query indices.
/// Its leaf digests must be ordered by the sorted unique indices obtained by
/// shifting every base index right by `2 * start_level` and deduplicating.
#[derive(Clone, Copy, Debug)]
pub struct StaggeredRadix4Lane<'a> {
    pub start_level: u32,
    pub root: &'a [u8; 32],
    pub leaf_digests: &'a [[u8; 32]],
    pub frontier: &'a [u8],
}

/// Caller-owned buffers for allocation-stable forest verification.
///
/// The candidate deliberately exposes scratch ownership so an SBF A/B does
/// not disguise allocator work as a geometry saving.
pub struct StaggeredRadix4ForestScratch<const LANES: usize> {
    indices: Vec<u32>,
    next_indices: Vec<u32>,
    digests: [Vec<[u8; 32]>; LANES],
    next_digests: [Vec<[u8; 32]>; LANES],
}

impl<const LANES: usize> StaggeredRadix4ForestScratch<LANES> {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            indices: Vec::with_capacity(capacity),
            next_indices: Vec::with_capacity(capacity),
            digests: core::array::from_fn(|_| Vec::with_capacity(capacity)),
            next_digests: core::array::from_fn(|_| Vec::with_capacity(capacity)),
        }
    }
}

/// Verify independently committed radix-4 trees while sharing only their
/// public index/group traversal.
///
/// This is acceptance-equivalent to calling
/// [`crate::merkle::verify_radix4_minimal_subtree_bytes`] once per lane on
/// the corresponding shifted indices.  In particular, each lane consumes a
/// separate frontier, performs a separate hash for every parent, and checks
/// a separate root.  No commitment or Fiat--Shamir phase is merged.
pub fn verify_staggered_radix4_forest_bytes<const LANES: usize>(
    hash: HashFn,
    base_binary_depth: u32,
    base_indices: &[u32],
    lanes: &[StaggeredRadix4Lane<'_>; LANES],
    scratch: &mut StaggeredRadix4ForestScratch<LANES>,
) -> bool {
    if LANES == 0
        || base_indices.is_empty()
        || base_binary_depth == 0
        || base_binary_depth >= 32
        || base_binary_depth & 1 != 0
    {
        return false;
    }
    for pair in base_indices.windows(2) {
        if pair[0] >= pair[1] {
            return false;
        }
    }
    if base_indices.last().copied().unwrap() >= (1u32 << base_binary_depth) {
        return false;
    }
    let radix4_levels = base_binary_depth / 2;
    if lanes
        .iter()
        .any(|lane| lane.start_level >= radix4_levels || lane.frontier.len() & 31 != 0)
    {
        return false;
    }

    scratch.indices.clear();
    scratch.indices.extend_from_slice(base_indices);
    for values in &mut scratch.digests {
        values.clear();
    }
    for values in &mut scratch.next_digests {
        values.clear();
    }
    let mut frontier_positions = [0usize; LANES];

    for level in 0..radix4_levels {
        for lane_index in 0..LANES {
            let lane = lanes[lane_index];
            if lane.start_level == level {
                if lane.leaf_digests.len() != scratch.indices.len() {
                    return false;
                }
                scratch.digests[lane_index].clear();
                scratch.digests[lane_index].extend_from_slice(lane.leaf_digests);
            }
            if lane.start_level <= level
                && scratch.digests[lane_index].len() != scratch.indices.len()
            {
                return false;
            }
            scratch.next_digests[lane_index].clear();
        }

        scratch.next_indices.clear();
        let mut position = 0usize;
        while position < scratch.indices.len() {
            let group_start = position;
            let parent_index = scratch.indices[position] >> 2;
            let mut present = 0u8;
            while position < scratch.indices.len() && scratch.indices[position] >> 2 == parent_index
            {
                let slot = (scratch.indices[position] & 3) as usize;
                let slot_mask = 1u8 << slot;
                if present & slot_mask != 0 {
                    return false;
                }
                present |= slot_mask;
                position += 1;
            }
            scratch.next_indices.push(parent_index);

            for lane_index in 0..LANES {
                let lane = lanes[lane_index];
                if lane.start_level > level {
                    continue;
                }
                let mut children = [[0u8; 32]; 4];
                for digest_position in group_start..position {
                    let slot = (scratch.indices[digest_position] & 3) as usize;
                    children[slot] = scratch.digests[lane_index][digest_position];
                }
                for (slot, child) in children.iter_mut().enumerate() {
                    if present & (1u8 << slot) != 0 {
                        continue;
                    }
                    let frontier_position = frontier_positions[lane_index];
                    let Some(bytes) = lane.frontier.get(frontier_position..frontier_position + 32)
                    else {
                        return false;
                    };
                    *child = bytes.try_into().unwrap();
                    frontier_positions[lane_index] += 32;
                }
                scratch.next_digests[lane_index].push(node_hash4(hash, &children));
            }
        }

        core::mem::swap(&mut scratch.indices, &mut scratch.next_indices);
        for lane_index in 0..LANES {
            if lanes[lane_index].start_level <= level {
                core::mem::swap(
                    &mut scratch.digests[lane_index],
                    &mut scratch.next_digests[lane_index],
                );
            }
        }
    }

    if scratch.indices.as_slice() != [0] {
        return false;
    }
    for lane_index in 0..LANES {
        let lane = lanes[lane_index];
        if frontier_positions[lane_index] != lane.frontier.len()
            || scratch.digests[lane_index].as_slice() != [*lane.root]
        {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::verify_radix4_minimal_subtree_bytes;
    use alloc::vec;
    use sha2::{Digest, Sha256};

    const DEPTH: u32 = 12;
    const STARTS: [u32; 5] = [0, 0, 1, 2, 3];
    const BASE_INDICES: [u32; 36] = [
        31, 77, 185, 248, 420, 431, 693, 915, 961, 1_366, 1_371, 1_418, 1_525, 1_533, 1_690, 1_788,
        1_894, 1_898, 1_922, 1_981, 1_983, 2_141, 2_266, 2_369, 2_513, 2_637, 2_710, 2_851, 2_877,
        2_884, 3_017, 3_348, 3_420, 3_566, 3_896, 4_053,
    ];

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn independent_parent(children: &[[u8; 32]; 4]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update([0x12]);
        for child in children {
            hasher.update(child);
        }
        hasher.finalize().into()
    }

    fn shifted_indices(start: u32, base: &[u32]) -> Vec<u32> {
        let mut result = base
            .iter()
            .map(|index| index >> (2 * start))
            .collect::<Vec<_>>();
        result.dedup();
        result
    }

    fn build_levels_for_depth(lane: usize, start: u32, depth: u32) -> Vec<Vec<[u8; 32]>> {
        let leaf_count = 1usize << (depth - 2 * start);
        let mut levels = vec![(0..leaf_count)
            .map(|index| {
                let mut hasher = Sha256::new();
                hasher.update(b"aspis-forest-independent-leaf");
                hasher.update([lane as u8]);
                hasher.update((index as u32).to_le_bytes());
                hasher.finalize().into()
            })
            .collect::<Vec<_>>()];
        while levels.last().unwrap().len() > 1 {
            let next = levels
                .last()
                .unwrap()
                .chunks_exact(4)
                .map(|children| independent_parent(children.try_into().unwrap()))
                .collect::<Vec<_>>();
            levels.push(next);
        }
        levels
    }

    fn build_levels(lane: usize, start: u32) -> Vec<Vec<[u8; 32]>> {
        build_levels_for_depth(lane, start, DEPTH)
    }

    fn independent_frontier(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<u8> {
        let mut output = Vec::new();
        let mut current = indices.to_vec();
        for tree_level in &levels[..levels.len() - 1] {
            let mut next = Vec::new();
            let mut position = 0usize;
            while position < current.len() {
                let parent = current[position] >> 2;
                let mut present = 0u8;
                while position < current.len() && current[position] >> 2 == parent {
                    present |= 1u8 << (current[position] & 3);
                    position += 1;
                }
                for slot in 0..4u32 {
                    if present & (1u8 << slot) == 0 {
                        output.extend_from_slice(&tree_level[(4 * parent + slot) as usize]);
                    }
                }
                next.push(parent);
            }
            current = next;
        }
        output
    }

    struct Fixture {
        roots: [[u8; 32]; 5],
        leaves: [Vec<[u8; 32]>; 5],
        frontiers: [Vec<u8>; 5],
    }

    fn fixture() -> Fixture {
        let levels: [Vec<Vec<[u8; 32]>>; 5] =
            core::array::from_fn(|lane| build_levels(lane, STARTS[lane]));
        let roots = core::array::from_fn(|lane| *levels[lane].last().unwrap().first().unwrap());
        let leaves = core::array::from_fn(|lane| {
            shifted_indices(STARTS[lane], &BASE_INDICES)
                .iter()
                .map(|index| levels[lane][0][*index as usize])
                .collect()
        });
        let frontiers = core::array::from_fn(|lane| {
            independent_frontier(&levels[lane], &shifted_indices(STARTS[lane], &BASE_INDICES))
        });
        Fixture {
            roots,
            leaves,
            frontiers,
        }
    }

    fn candidate(fixture: &Fixture, indices: &[u32]) -> bool {
        let lanes: [StaggeredRadix4Lane<'_>; 5] =
            core::array::from_fn(|lane| StaggeredRadix4Lane {
                start_level: STARTS[lane],
                root: &fixture.roots[lane],
                leaf_digests: &fixture.leaves[lane],
                frontier: &fixture.frontiers[lane],
            });
        verify_staggered_radix4_forest_bytes(
            test_hash,
            DEPTH,
            indices,
            &lanes,
            &mut StaggeredRadix4ForestScratch::with_capacity(indices.len()),
        )
    }

    fn independent_reference(fixture: &Fixture) -> bool {
        (0..5).all(|lane| {
            let indices = shifted_indices(STARTS[lane], &BASE_INDICES);
            let entries = indices
                .iter()
                .copied()
                .zip(fixture.leaves[lane].iter().copied())
                .collect::<Vec<_>>();
            verify_radix4_minimal_subtree_bytes(
                test_hash,
                &fixture.roots[lane],
                DEPTH - 2 * STARTS[lane],
                &entries,
                &fixture.frontiers[lane],
                &mut Vec::with_capacity(entries.len()),
                &mut Vec::with_capacity(entries.len()),
            )
        })
    }

    #[test]
    fn staggered_forest_matches_five_independent_verifiers() {
        let fixture = fixture();
        assert!(independent_reference(&fixture));
        assert!(candidate(&fixture, &BASE_INDICES));
    }

    #[test]
    fn randomized_geometries_match_independent_lane_verifiers() {
        const RANDOM_DEPTH: u32 = 8;
        const RANDOM_STARTS: [u32; 4] = [0, 0, 1, 2];
        let levels: [Vec<Vec<[u8; 32]>>; 4] = core::array::from_fn(|lane| {
            build_levels_for_depth(lane + 17, RANDOM_STARTS[lane], RANDOM_DEPTH)
        });
        let roots: [[u8; 32]; 4] =
            core::array::from_fn(|lane| *levels[lane].last().unwrap().first().unwrap());
        let mut state = 0x8f3c_d1a2_6b79_4501u64;
        for _ in 0..32 {
            let mut base = Vec::with_capacity(20);
            while base.len() < 20 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let candidate = (state as u32) & ((1 << RANDOM_DEPTH) - 1);
                if !base.contains(&candidate) {
                    base.push(candidate);
                }
            }
            base.sort_unstable();
            let shifted: [Vec<u32>; 4] =
                core::array::from_fn(|lane| shifted_indices(RANDOM_STARTS[lane], &base));
            let leaves: [Vec<[u8; 32]>; 4] = core::array::from_fn(|lane| {
                shifted[lane]
                    .iter()
                    .map(|index| levels[lane][0][*index as usize])
                    .collect()
            });
            let frontiers: [Vec<u8>; 4] =
                core::array::from_fn(|lane| independent_frontier(&levels[lane], &shifted[lane]));
            let lanes: [StaggeredRadix4Lane<'_>; 4] =
                core::array::from_fn(|lane| StaggeredRadix4Lane {
                    start_level: RANDOM_STARTS[lane],
                    root: &roots[lane],
                    leaf_digests: &leaves[lane],
                    frontier: &frontiers[lane],
                });
            let mut scratch = StaggeredRadix4ForestScratch::with_capacity(base.len());
            assert!(verify_staggered_radix4_forest_bytes(
                test_hash,
                RANDOM_DEPTH,
                &base,
                &lanes,
                &mut scratch,
            ));
            for lane in 0..4 {
                let entries = shifted[lane]
                    .iter()
                    .copied()
                    .zip(leaves[lane].iter().copied())
                    .collect::<Vec<_>>();
                assert!(verify_radix4_minimal_subtree_bytes(
                    test_hash,
                    &roots[lane],
                    RANDOM_DEPTH - 2 * RANDOM_STARTS[lane],
                    &entries,
                    &frontiers[lane],
                    &mut Vec::with_capacity(entries.len()),
                    &mut Vec::with_capacity(entries.len()),
                ));
            }
        }
    }

    #[test]
    fn every_independent_lane_retains_its_own_teeth() {
        let valid = fixture();
        for lane in 0..5 {
            let mut bad_frontier = fixture();
            let middle = bad_frontier.frontiers[lane].len() / 2;
            bad_frontier.frontiers[lane][middle] ^= 1;
            assert!(!independent_reference(&bad_frontier));
            assert!(!candidate(&bad_frontier, &BASE_INDICES));

            let mut bad_root = fixture();
            bad_root.roots[lane][lane] ^= 1;
            assert!(!independent_reference(&bad_root));
            assert!(!candidate(&bad_root, &BASE_INDICES));

            let mut bad_leaf = fixture();
            bad_leaf.leaves[lane][0][lane] ^= 1;
            assert!(!independent_reference(&bad_leaf));
            assert!(!candidate(&bad_leaf, &BASE_INDICES));

            let mut truncated = fixture();
            truncated.frontiers[lane].pop();
            assert!(!candidate(&truncated, &BASE_INDICES));

            let mut extended = fixture();
            extended.frontiers[lane].extend_from_slice(&[0u8; 32]);
            assert!(!candidate(&extended, &BASE_INDICES));
        }
        assert!(candidate(&valid, &BASE_INDICES));
    }

    #[test]
    fn shared_geometry_rejects_order_duplicates_range_and_wrong_stagger() {
        let fixture = fixture();
        let mut unsorted = BASE_INDICES;
        unsorted.swap(3, 4);
        assert!(!candidate(&fixture, &unsorted));
        let mut duplicate = BASE_INDICES;
        duplicate[4] = duplicate[3];
        assert!(!candidate(&fixture, &duplicate));
        let mut out_of_range = BASE_INDICES;
        out_of_range[35] = 1 << DEPTH;
        assert!(!candidate(&fixture, &out_of_range));

        let mut lanes: [StaggeredRadix4Lane<'_>; 5] =
            core::array::from_fn(|lane| StaggeredRadix4Lane {
                start_level: STARTS[lane],
                root: &fixture.roots[lane],
                leaf_digests: &fixture.leaves[lane],
                frontier: &fixture.frontiers[lane],
            });
        lanes[4].start_level = 2;
        assert!(!verify_staggered_radix4_forest_bytes(
            test_hash,
            DEPTH,
            &BASE_INDICES,
            &lanes,
            &mut StaggeredRadix4ForestScratch::with_capacity(BASE_INDICES.len()),
        ));
    }
}
