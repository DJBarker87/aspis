//! Aggregate serializer for the five private profile-22 opening sections.

use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineMerkleError, CircleLineQueryIndices,
};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_profile22_openings::{
    PROFILE22_LAYER0_LEAF_COUNT, PROFILE22_PRIVATE_DEPTHS, PROFILE22_PRIVATE_SECTION_COUNT,
    PROFILE22_PRIVATE_TREE_TAGS, PROFILE22_PRIVATE_VALUE_WIDTHS,
};

use crate::state_only_private_openings::{
    serialize_state_only_private_opening, StateOnlyPrivateMerkleTree,
    StateOnlyPrivateOpeningBuildError,
};

#[derive(Clone, Copy)]
pub struct StateOnlyProfile22TreeInput<'a> {
    pub tree: &'a StateOnlyPrivateMerkleTree,
    pub values: &'a [u8],
    pub salts: &'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
}

#[derive(Clone, Copy)]
pub struct StateOnlyProfile22OpeningInputs<'a> {
    pub c1: StateOnlyProfile22TreeInput<'a>,
    pub c2: StateOnlyProfile22TreeInput<'a>,
    pub later: [StateOnlyProfile22TreeInput<'a>; 3],
}

impl<'a> StateOnlyProfile22OpeningInputs<'a> {
    fn as_array(&self) -> [StateOnlyProfile22TreeInput<'a>; PROFILE22_PRIVATE_SECTION_COUNT] {
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
pub enum StateOnlyProfile22OpeningBuildError {
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

impl From<CircleLineMerkleError> for StateOnlyProfile22OpeningBuildError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuiltStateOnlyProfile22Openings {
    pub bytes: Vec<u8>,
    pub indices: CircleLineQueryIndices,
    pub section_bytes: [usize; PROFILE22_PRIVATE_SECTION_COUNT],
    pub frontier_nodes: [usize; PROFILE22_PRIVATE_SECTION_COUNT],
}

fn validate_tree_shape(
    section: usize,
    tree: &StateOnlyPrivateMerkleTree,
) -> Result<(), StateOnlyProfile22OpeningBuildError> {
    let expected_depth = PROFILE22_PRIVATE_DEPTHS[section];
    let expected_tag = PROFILE22_PRIVATE_TREE_TAGS[section];
    let expected_width = PROFILE22_PRIVATE_VALUE_WIDTHS[section];
    let actual_depth = tree.binary_depth();
    let actual_tag = tree.tree_tag();
    let actual_width = tree.value_width();
    if (actual_depth, actual_tag, actual_width) != (expected_depth, expected_tag, expected_width) {
        return Err(StateOnlyProfile22OpeningBuildError::SectionShape {
            section: section as u8,
            expected_depth,
            actual_depth,
            expected_tag,
            actual_tag,
            expected_width,
            actual_width,
        });
    }
    Ok(())
}

/// Concatenate C1, ordinary C2, W1, W2 and W3 private openings.
pub fn serialize_state_only_profile22_openings(
    queries: &[u32],
    inputs: &StateOnlyProfile22OpeningInputs<'_>,
) -> Result<BuiltStateOnlyProfile22Openings, StateOnlyProfile22OpeningBuildError> {
    let indices = derive_circle_line_query_indices_for_count(queries, PROFILE22_LAYER0_LEAF_COUNT)?;
    let section_indices: [&[u32]; PROFILE22_PRIVATE_SECTION_COUNT] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let inputs = inputs.as_array();
    let mut bytes = Vec::new();
    let mut section_bytes = [0usize; PROFILE22_PRIVATE_SECTION_COUNT];
    let mut frontier_nodes = [0usize; PROFILE22_PRIVATE_SECTION_COUNT];
    for section in 0..PROFILE22_PRIVATE_SECTION_COUNT {
        validate_tree_shape(section, inputs[section].tree)?;
        let opening = serialize_state_only_private_opening(
            inputs[section].tree,
            inputs[section].values,
            inputs[section].salts,
            section_indices[section],
        )
        .map_err(|error| StateOnlyProfile22OpeningBuildError::Section {
            section: section as u8,
            error,
        })?;
        section_bytes[section] = opening.bytes.len();
        frontier_nodes[section] = opening.frontier_nodes;
        bytes.extend_from_slice(&opening.bytes);
    }
    Ok(BuiltStateOnlyProfile22Openings {
        bytes,
        indices,
        section_bytes,
        frontier_nodes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state_only_private_openings::build_state_only_private_merkle_tree;
    use crate::HOST_HASH;

    #[test]
    fn wrong_c2_width_is_rejected() {
        let values = vec![7u8; 2];
        let salts = vec![[9u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]; 2];
        let wrong = build_state_only_private_merkle_tree(
            HOST_HASH,
            1,
            PROFILE22_PRIVATE_TREE_TAGS[1],
            1,
            &values,
            &salts,
        )
        .unwrap();
        assert!(matches!(
            validate_tree_shape(1, &wrong),
            Err(StateOnlyProfile22OpeningBuildError::SectionShape {
                expected_width: 128,
                actual_width: 1,
                ..
            })
        ));
    }
}
