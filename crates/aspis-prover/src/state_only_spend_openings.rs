//! Private-opening serializer for spend's widened C2 section.

use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineMerkleError, CircleLineQueryIndices,
};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_spend_openings::{
    SPEND_LAYER0_LEAF_COUNT, SPEND_PRIVATE_DEPTHS, SPEND_PRIVATE_SECTION_COUNT,
    SPEND_PRIVATE_TREE_TAGS, SPEND_PRIVATE_VALUE_WIDTHS,
};

use crate::state_only_private_openings::{
    serialize_state_only_private_opening, StateOnlyPrivateMerkleTree,
    StateOnlyPrivateOpeningBuildError,
};

#[derive(Clone, Copy)]
pub struct StateOnlySpendTreeInput<'a> {
    pub tree: &'a StateOnlyPrivateMerkleTree,
    pub values: &'a [u8],
    pub salts: &'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
}

#[derive(Clone, Copy)]
pub struct StateOnlySpendOpeningInputs<'a> {
    pub c1: StateOnlySpendTreeInput<'a>,
    pub c2: StateOnlySpendTreeInput<'a>,
    pub later: [StateOnlySpendTreeInput<'a>; 3],
}

impl<'a> StateOnlySpendOpeningInputs<'a> {
    fn as_array(&self) -> [StateOnlySpendTreeInput<'a>; SPEND_PRIVATE_SECTION_COUNT] {
        [
            self.c1,
            self.c2,
            self.later[0],
            self.later[1],
            self.later[2],
        ]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlySpendOpeningBuildError {
    Query(CircleLineMerkleError),
    SectionShape {
        section: u8,
        expected_depth: u32,
        actual_depth: u32,
        expected_tag: u8,
        actual_tag: u8,
        expected_width: usize,
        actual_width: usize,
    },
    Section {
        section: u8,
        error: StateOnlyPrivateOpeningBuildError,
    },
}

impl From<CircleLineMerkleError> for StateOnlySpendOpeningBuildError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuiltStateOnlySpendOpenings {
    pub bytes: Vec<u8>,
    pub indices: CircleLineQueryIndices,
    pub section_bytes: [usize; SPEND_PRIVATE_SECTION_COUNT],
    pub frontier_nodes: [usize; SPEND_PRIVATE_SECTION_COUNT],
}

pub fn serialize_state_only_spend_openings(
    queries: &[u32],
    inputs: &StateOnlySpendOpeningInputs<'_>,
) -> Result<BuiltStateOnlySpendOpenings, StateOnlySpendOpeningBuildError> {
    let indices = derive_circle_line_query_indices_for_count(queries, SPEND_LAYER0_LEAF_COUNT)?;
    let section_indices: [&[u32]; 5] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let inputs = inputs.as_array();
    let mut bytes = Vec::new();
    let mut section_bytes = [0usize; 5];
    let mut frontier_nodes = [0usize; 5];
    for section in 0..5 {
        let tree = inputs[section].tree;
        let actual = (tree.binary_depth(), tree.tree_tag(), tree.value_width());
        let expected = (
            SPEND_PRIVATE_DEPTHS[section],
            SPEND_PRIVATE_TREE_TAGS[section],
            SPEND_PRIVATE_VALUE_WIDTHS[section],
        );
        if actual != expected {
            return Err(StateOnlySpendOpeningBuildError::SectionShape {
                section: section as u8,
                expected_depth: expected.0,
                actual_depth: actual.0,
                expected_tag: expected.1,
                actual_tag: actual.1,
                expected_width: expected.2,
                actual_width: actual.2,
            });
        }
        let opening = serialize_state_only_private_opening(
            tree,
            inputs[section].values,
            inputs[section].salts,
            section_indices[section],
        )
        .map_err(|error| StateOnlySpendOpeningBuildError::Section {
            section: section as u8,
            error,
        })?;
        section_bytes[section] = opening.bytes.len();
        frontier_nodes[section] = opening.frontier_nodes;
        bytes.extend_from_slice(&opening.bytes);
    }
    Ok(BuiltStateOnlySpendOpenings {
        bytes,
        indices,
        section_bytes,
        frontier_nodes,
    })
}
