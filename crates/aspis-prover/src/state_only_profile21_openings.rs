//! Aggregate serializer for the five private Profile 21 opening sections.

use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineMerkleError, CircleLineQueryIndices,
};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_profile21_openings::{
    PROFILE21_LAYER0_LEAF_COUNT, PROFILE21_PRIVATE_DEPTHS, PROFILE21_PRIVATE_SECTION_COUNT,
    PROFILE21_PRIVATE_TREE_TAGS, PROFILE21_PRIVATE_VALUE_WIDTHS,
};

use crate::state_only_private_openings::{
    serialize_state_only_private_opening, StateOnlyPrivateMerkleTree,
    StateOnlyPrivateOpeningBuildError,
};

#[derive(Clone, Copy)]
pub struct StateOnlyProfile21TreeInput<'a> {
    pub tree: &'a StateOnlyPrivateMerkleTree,
    pub values: &'a [u8],
    pub salts: &'a [[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
}

#[derive(Clone, Copy)]
pub struct StateOnlyProfile21OpeningInputs<'a> {
    pub c1: StateOnlyProfile21TreeInput<'a>,
    pub c2: StateOnlyProfile21TreeInput<'a>,
    pub later: [StateOnlyProfile21TreeInput<'a>; 3],
}

impl<'a> StateOnlyProfile21OpeningInputs<'a> {
    fn as_array(&self) -> [StateOnlyProfile21TreeInput<'a>; PROFILE21_PRIVATE_SECTION_COUNT] {
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
pub enum StateOnlyProfile21OpeningBuildError {
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

impl From<CircleLineMerkleError> for StateOnlyProfile21OpeningBuildError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuiltStateOnlyProfile21Openings {
    pub bytes: Vec<u8>,
    pub indices: CircleLineQueryIndices,
    pub section_bytes: [usize; PROFILE21_PRIVATE_SECTION_COUNT],
    pub frontier_nodes: [usize; PROFILE21_PRIVATE_SECTION_COUNT],
}

fn validate_tree_shape(
    section: usize,
    tree: &StateOnlyPrivateMerkleTree,
) -> Result<(), StateOnlyProfile21OpeningBuildError> {
    let expected_depth = PROFILE21_PRIVATE_DEPTHS[section];
    let expected_tag = PROFILE21_PRIVATE_TREE_TAGS[section];
    let expected_width = PROFILE21_PRIVATE_VALUE_WIDTHS[section];
    let actual_depth = tree.binary_depth();
    let actual_tag = tree.tree_tag();
    let actual_width = tree.value_width();
    if (actual_depth, actual_tag, actual_width) != (expected_depth, expected_tag, expected_width) {
        return Err(StateOnlyProfile21OpeningBuildError::SectionShape {
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

/// Concatenate C1, widened C2, W1, W2 and W3 private openings in their
/// consensus order. All five sections use one index object derived from the
/// transcript q positions.
pub fn serialize_state_only_profile21_openings(
    queries: &[u32],
    inputs: &StateOnlyProfile21OpeningInputs<'_>,
) -> Result<BuiltStateOnlyProfile21Openings, StateOnlyProfile21OpeningBuildError> {
    let indices = derive_circle_line_query_indices_for_count(queries, PROFILE21_LAYER0_LEAF_COUNT)?;
    let section_indices: [&[u32]; PROFILE21_PRIVATE_SECTION_COUNT] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let inputs = inputs.as_array();
    let mut bytes = Vec::new();
    let mut section_bytes = [0usize; PROFILE21_PRIVATE_SECTION_COUNT];
    let mut frontier_nodes = [0usize; PROFILE21_PRIVATE_SECTION_COUNT];
    for section in 0..PROFILE21_PRIVATE_SECTION_COUNT {
        validate_tree_shape(section, inputs[section].tree)?;
        let opening = serialize_state_only_private_opening(
            inputs[section].tree,
            inputs[section].values,
            inputs[section].salts,
            section_indices[section],
        )
        .map_err(|error| StateOnlyProfile21OpeningBuildError::Section {
            section: section as u8,
            error,
        })?;
        section_bytes[section] = opening.bytes.len();
        frontier_nodes[section] = opening.frontier_nodes;
        bytes.extend_from_slice(&opening.bytes);
    }
    Ok(BuiltStateOnlyProfile21Openings {
        bytes,
        indices,
        section_bytes,
        frontier_nodes,
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;

    use crate::state_only_private_openings::build_state_only_private_merkle_tree;
    use crate::HOST_HASH;

    use super::*;

    #[test]
    fn aggregate_rejects_wrong_depth_tag_and_width_metadata() {
        let values = vec![7u8; 2];
        let salts = vec![[9u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]; 2];
        let wrong =
            build_state_only_private_merkle_tree(HOST_HASH, 1, 0xee, 1, &values, &salts).unwrap();
        assert_eq!(
            validate_tree_shape(0, &wrong),
            Err(StateOnlyProfile21OpeningBuildError::SectionShape {
                section: 0,
                expected_depth: 17,
                actual_depth: 1,
                expected_tag: PROFILE21_PRIVATE_TREE_TAGS[0],
                actual_tag: 0xee,
                expected_width: 416,
                actual_width: 1,
            })
        );
    }

    #[test]
    fn aggregate_query_index_mapping_matches_core_freeze() {
        let indices = derive_circle_line_query_indices_for_count(
            &[131_071, 0, 4, 4, 64],
            PROFILE21_LAYER0_LEAF_COUNT,
        )
        .unwrap();
        assert_eq!(indices.layer0, [0, 4, 64, 131_071]);
        assert_eq!(indices.later[0], [0, 1, 16, 32_767]);
        assert_eq!(indices.later[1], [0, 4, 8_191]);
        assert_eq!(indices.later[2], [0, 1, 2_047]);
    }
}
