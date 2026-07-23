//! Prover-side serializer for the fixed circle-candidate opening suffix.

use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices, derive_circle_line_query_indices_for_count,
    CircleLineMerkleError, CIRCLE_LINE_LAYER_COUNT, CIRCLE_LINE_TAGS,
};
use aspis_core::circle_merkle::{
    CIRCLE_C1_LAYER0_TAG, CIRCLE_C1_LEAF_BYTES, CIRCLE_C2_LAYER0_TAG, CIRCLE_C2_LEAF_BYTES,
};
use aspis_core::circle_pcs_shape::{CirclePcsShape, CirclePcsShapeError};
use aspis_core::merkle::{leaf_hash, node_hash, node_hash4};
use aspis_core::HashFn;

use crate::circle_candidate::{CircleFoldCommitments, COMBINED_LAYER_LEAF_BYTES, FIBER_COUNT};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidateOpeningBuildError {
    Query(CircleLineMerkleError),
    Shape(CirclePcsShapeError),
    Layer0Shape,
    Layer0Width {
        expected_c1: usize,
        actual_c1: usize,
        expected_c2: usize,
        actual_c2: usize,
    },
    QueryCountMismatch {
        expected: usize,
        actual: usize,
    },
    LaterShape {
        layer: usize,
    },
}

impl From<CircleLineMerkleError> for CandidateOpeningBuildError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

impl From<CirclePcsShapeError> for CandidateOpeningBuildError {
    fn from(error: CirclePcsShapeError) -> Self {
        Self::Shape(error)
    }
}

fn tree<const N: usize>(leaves: &[[u8; N]], tag: u8, hash: HashFn) -> Vec<Vec<[u8; 32]>> {
    let mut levels = vec![leaves
        .iter()
        .map(|leaf| leaf_hash(hash, tag, leaf))
        .collect::<Vec<_>>()];
    while levels.last().unwrap().len() > 1 {
        let previous = levels.last().unwrap();
        levels.push(if previous.len() == 2 {
            vec![node_hash(hash, &previous[0], &previous[1])]
        } else {
            previous
                .chunks_exact(4)
                .map(|children| node_hash4(hash, children.try_into().unwrap()))
                .collect()
        });
    }
    levels
}

fn frontier(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
    let mut result = Vec::new();
    let mut current = indices.to_vec();
    for level in &levels[..levels.len() - 1] {
        if level.len() == 2 {
            if current.len() == 1 {
                result.push(level[(current[0] ^ 1) as usize]);
            }
            current.clear();
            current.push(0);
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

fn append_frontier(bytes: &mut Vec<u8>, nodes: &[[u8; 32]]) {
    bytes.extend_from_slice(&(nodes.len() as u32).to_le_bytes());
    for node in nodes {
        bytes.extend_from_slice(node);
    }
}

/// Serialize the canonical layer0||layer1||layer2||layer3 opening suffix.
pub fn serialize_candidate_openings(
    queries: &[u32],
    c1_leaves: &[[u8; CIRCLE_C1_LEAF_BYTES]],
    c2_leaves: &[[u8; CIRCLE_C2_LEAF_BYTES]],
    folds: &CircleFoldCommitments,
    hash: HashFn,
) -> Result<Vec<u8>, CandidateOpeningBuildError> {
    serialize_candidate_openings_for_fiber_count(
        queries,
        c1_leaves,
        c2_leaves,
        folds,
        FIBER_COUNT,
        hash,
    )
}

pub fn serialize_candidate_openings_for_fiber_count(
    queries: &[u32],
    c1_leaves: &[[u8; CIRCLE_C1_LEAF_BYTES]],
    c2_leaves: &[[u8; CIRCLE_C2_LEAF_BYTES]],
    folds: &CircleFoldCommitments,
    fiber_count: usize,
    hash: HashFn,
) -> Result<Vec<u8>, CandidateOpeningBuildError> {
    serialize_candidate_openings_for_fiber_count_with_c2(
        queries,
        c1_leaves,
        c2_leaves,
        folds,
        fiber_count,
        hash,
    )
}

pub fn serialize_candidate_openings_for_fiber_count_with_c2<const C2_BYTES: usize>(
    queries: &[u32],
    c1_leaves: &[[u8; CIRCLE_C1_LEAF_BYTES]],
    c2_leaves: &[[u8; C2_BYTES]],
    folds: &CircleFoldCommitments,
    fiber_count: usize,
    hash: HashFn,
) -> Result<Vec<u8>, CandidateOpeningBuildError> {
    serialize_candidate_openings_for_fiber_count_with_leaf_bytes(
        queries,
        c1_leaves,
        c2_leaves,
        folds,
        fiber_count,
        hash,
    )
}

pub fn serialize_candidate_openings_for_fiber_count_with_leaf_bytes<
    const C1_BYTES: usize,
    const C2_BYTES: usize,
>(
    queries: &[u32],
    c1_leaves: &[[u8; C1_BYTES]],
    c2_leaves: &[[u8; C2_BYTES]],
    folds: &CircleFoldCommitments,
    fiber_count: usize,
    hash: HashFn,
) -> Result<Vec<u8>, CandidateOpeningBuildError> {
    serialize_candidate_openings_with_tags(
        queries,
        c1_leaves,
        c2_leaves,
        folds,
        fiber_count,
        CIRCLE_C1_LAYER0_TAG,
        CIRCLE_C2_LAYER0_TAG,
        CIRCLE_LINE_TAGS,
        hash,
    )
}

/// Serialize an additive PCS opening forest under the exact widths, rate,
/// and Merkle tags carried by `shape`. Frozen wrappers above still route
/// through the V4 constants.
pub fn serialize_candidate_openings_for_shape<const C1_BYTES: usize, const C2_BYTES: usize>(
    queries: &[u32],
    c1_leaves: &[[u8; C1_BYTES]],
    c2_leaves: &[[u8; C2_BYTES]],
    folds: &CircleFoldCommitments,
    shape: CirclePcsShape,
    hash: HashFn,
) -> Result<Vec<u8>, CandidateOpeningBuildError> {
    let shape = shape.validate()?;
    let expected_c1 = shape.c1_leaf_bytes_checked()?;
    let expected_c2 = shape.c2_leaf_bytes_checked()?;
    if C1_BYTES != expected_c1 || C2_BYTES != expected_c2 {
        return Err(CandidateOpeningBuildError::Layer0Width {
            expected_c1,
            actual_c1: C1_BYTES,
            expected_c2,
            actual_c2: C2_BYTES,
        });
    }
    if queries.len() != usize::from(shape.query_count) {
        return Err(CandidateOpeningBuildError::QueryCountMismatch {
            expected: usize::from(shape.query_count),
            actual: queries.len(),
        });
    }
    serialize_candidate_openings_with_tags(
        queries,
        c1_leaves,
        c2_leaves,
        folds,
        shape.fiber_count(),
        shape.c1_layer0_tag,
        shape.c2_layer0_tag,
        shape.later_layer_tags,
        hash,
    )
}

#[allow(clippy::too_many_arguments)]
fn serialize_candidate_openings_with_tags<const C1_BYTES: usize, const C2_BYTES: usize>(
    queries: &[u32],
    c1_leaves: &[[u8; C1_BYTES]],
    c2_leaves: &[[u8; C2_BYTES]],
    folds: &CircleFoldCommitments,
    fiber_count: usize,
    c1_layer_tag: u8,
    c2_layer_tag: u8,
    later_layer_tags: [u8; CIRCLE_LINE_LAYER_COUNT],
    hash: HashFn,
) -> Result<Vec<u8>, CandidateOpeningBuildError> {
    if c1_leaves.len() != fiber_count || c2_leaves.len() != fiber_count {
        return Err(CandidateOpeningBuildError::Layer0Shape);
    }
    let indices = if fiber_count == FIBER_COUNT {
        derive_circle_line_query_indices(queries)?
    } else {
        derive_circle_line_query_indices_for_count(queries, fiber_count)?
    };
    let c1_tree = tree(c1_leaves, c1_layer_tag, hash);
    let c2_tree = tree(c2_leaves, c2_layer_tag, hash);
    let mut bytes = Vec::new();

    bytes.extend_from_slice(&(indices.layer0.len() as u16).to_le_bytes());
    for &index in &indices.layer0 {
        bytes.extend_from_slice(&c1_leaves[index as usize]);
    }
    for &index in &indices.layer0 {
        bytes.extend_from_slice(&c2_leaves[index as usize]);
    }
    append_frontier(&mut bytes, &frontier(&c1_tree, &indices.layer0));
    append_frontier(&mut bytes, &frontier(&c2_tree, &indices.layer0));

    for (layer, layer_tag) in later_layer_tags.into_iter().enumerate() {
        let leaves: &[[u8; COMBINED_LAYER_LEAF_BYTES]] = &folds.committed_leaves[layer];
        let expected = fiber_count >> (2 * (layer + 1));
        if leaves.len() != expected {
            return Err(CandidateOpeningBuildError::LaterShape { layer });
        }
        let levels = tree(leaves, layer_tag, hash);
        bytes.extend_from_slice(&(indices.later[layer].len() as u16).to_le_bytes());
        for &index in &indices.later[layer] {
            bytes.extend_from_slice(&leaves[index as usize]);
        }
        append_frontier(&mut bytes, &frontier(&levels, &indices.later[layer]));
    }
    Ok(bytes)
}
