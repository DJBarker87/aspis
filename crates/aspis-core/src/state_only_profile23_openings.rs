//! Five-tree private opening verifier for nondefault profile 23.

use crate::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineMerkleError, CircleLineQueryIndices,
    CIRCLE_LINE_TAGS,
};
use crate::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use crate::state_only_private_openings::{
    verify_state_only_private_opening_from_proof, StateOnlyPrivateOpening,
    StateOnlyPrivateOpeningError,
};
use crate::HashFn;

pub const PROFILE23_LAYER0_LEAF_COUNT: usize = 1 << 17;
pub const PROFILE23_PRIVATE_SECTION_COUNT: usize = 5;
pub const PROFILE23_PRIVATE_DEPTHS: [u32; 5] = [17, 17, 15, 13, 11];
pub const PROFILE23_PRIVATE_VALUE_WIDTHS: [usize; 5] = [416, 192, 64, 64, 64];
pub const PROFILE23_PRIVATE_TREE_TAGS: [u8; 5] = [
    CIRCLE_C1_LAYER0_TAG,
    CIRCLE_C2_LAYER0_TAG,
    CIRCLE_LINE_TAGS[0],
    CIRCLE_LINE_TAGS[1],
    CIRCLE_LINE_TAGS[2],
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyProfile23OpeningRoots {
    pub c1: [u8; 32],
    pub c2: [u8; 32],
    pub later: [[u8; 32]; 3],
}

impl StateOnlyProfile23OpeningRoots {
    fn as_array(&self) -> [[u8; 32]; 5] {
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
pub enum StateOnlyProfile23OpeningError {
    Query(CircleLineMerkleError),
    Section {
        section: u8,
        error: StateOnlyPrivateOpeningError,
    },
    TrailingBytes {
        offset: usize,
        remaining: usize,
    },
}

impl From<CircleLineMerkleError> for StateOnlyProfile23OpeningError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedStateOnlyProfile23Openings<'a> {
    pub c1: StateOnlyPrivateOpening<'a>,
    pub c2: StateOnlyPrivateOpening<'a>,
    pub later: [StateOnlyPrivateOpening<'a>; 3],
    pub indices: CircleLineQueryIndices,
    pub end: usize,
}

pub fn verify_state_only_profile23_openings<'a>(
    hash: HashFn,
    roots: &StateOnlyProfile23OpeningRoots,
    queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedStateOnlyProfile23Openings<'a>, StateOnlyProfile23OpeningError> {
    let indices = derive_circle_line_query_indices_for_count(queries, PROFILE23_LAYER0_LEAF_COUNT)?;
    let section_indices: [&[u32]; 5] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let roots = roots.as_array();
    let mut remainder = proof_bytes;
    let mut parsed = [None; 5];
    for section in 0..5 {
        let (opening, next) = verify_state_only_private_opening_from_proof(
            hash,
            &roots[section],
            PROFILE23_PRIVATE_DEPTHS[section],
            PROFILE23_PRIVATE_TREE_TAGS[section],
            PROFILE23_PRIVATE_VALUE_WIDTHS[section],
            section_indices[section],
            remainder,
        )
        .map_err(|error| StateOnlyProfile23OpeningError::Section {
            section: section as u8,
            error,
        })?;
        parsed[section] = Some(opening);
        remainder = next;
    }
    if !remainder.is_empty() {
        return Err(StateOnlyProfile23OpeningError::TrailingBytes {
            offset: proof_bytes.len() - remainder.len(),
            remaining: remainder.len(),
        });
    }
    Ok(VerifiedStateOnlyProfile23Openings {
        c1: parsed[0].unwrap(),
        c2: parsed[1].unwrap(),
        later: [parsed[2].unwrap(), parsed[3].unwrap(), parsed[4].unwrap()],
        indices,
        end: proof_bytes.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profile23_geometry_is_distinct_only_at_c2() {
        assert_eq!(PROFILE23_PRIVATE_DEPTHS, [17, 17, 15, 13, 11]);
        assert_eq!(PROFILE23_PRIVATE_VALUE_WIDTHS, [416, 192, 64, 64, 64]);
    }
}
