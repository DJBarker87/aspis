//! Aggregate five-tree private opening verifier for state-only profile 22.
//!
//! Profile 22 keeps profile 20's two-lane C2 leaf.  Its only opening-format
//! change is that every value is authenticated as `value || salt` by the
//! private Merkle primitive.

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

pub const PROFILE22_LAYER0_LEAF_COUNT: usize = 1 << 17;
pub const PROFILE22_PRIVATE_SECTION_COUNT: usize = 5;
pub const PROFILE22_PRIVATE_DEPTHS: [u32; PROFILE22_PRIVATE_SECTION_COUNT] = [17, 17, 15, 13, 11];
pub const PROFILE22_PRIVATE_VALUE_WIDTHS: [usize; PROFILE22_PRIVATE_SECTION_COUNT] =
    [416, 128, 64, 64, 64];
pub const PROFILE22_PRIVATE_TREE_TAGS: [u8; PROFILE22_PRIVATE_SECTION_COUNT] = [
    CIRCLE_C1_LAYER0_TAG,
    CIRCLE_C2_LAYER0_TAG,
    CIRCLE_LINE_TAGS[0],
    CIRCLE_LINE_TAGS[1],
    CIRCLE_LINE_TAGS[2],
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyProfile22OpeningRoots {
    pub c1: [u8; 32],
    pub c2: [u8; 32],
    pub later: [[u8; 32]; 3],
}

impl StateOnlyProfile22OpeningRoots {
    pub fn as_array(&self) -> [[u8; 32]; PROFILE22_PRIVATE_SECTION_COUNT] {
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
pub enum StateOnlyProfile22OpeningError {
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

impl From<CircleLineMerkleError> for StateOnlyProfile22OpeningError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedStateOnlyProfile22Openings<'a> {
    pub c1: StateOnlyPrivateOpening<'a>,
    pub c2: StateOnlyPrivateOpening<'a>,
    pub later: [StateOnlyPrivateOpening<'a>; 3],
    pub indices: CircleLineQueryIndices,
    pub end: usize,
}

/// Authenticate C1, ordinary two-lane C2, W1, W2 and W3 in consensus order.
pub fn verify_state_only_profile22_openings<'a>(
    hash: HashFn,
    roots: &StateOnlyProfile22OpeningRoots,
    queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedStateOnlyProfile22Openings<'a>, StateOnlyProfile22OpeningError> {
    let indices = derive_circle_line_query_indices_for_count(queries, PROFILE22_LAYER0_LEAF_COUNT)?;
    let section_indices: [&[u32]; PROFILE22_PRIVATE_SECTION_COUNT] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let roots = roots.as_array();
    let mut remainder = proof_bytes;
    let mut parsed = [None; PROFILE22_PRIVATE_SECTION_COUNT];
    for section in 0..PROFILE22_PRIVATE_SECTION_COUNT {
        let (opening, next) = verify_state_only_private_opening_from_proof(
            hash,
            &roots[section],
            PROFILE22_PRIVATE_DEPTHS[section],
            PROFILE22_PRIVATE_TREE_TAGS[section],
            PROFILE22_PRIVATE_VALUE_WIDTHS[section],
            section_indices[section],
            remainder,
        )
        .map_err(|error| StateOnlyProfile22OpeningError::Section {
            section: section as u8,
            error,
        })?;
        parsed[section] = Some(opening);
        remainder = next;
    }
    if !remainder.is_empty() {
        return Err(StateOnlyProfile22OpeningError::TrailingBytes {
            offset: proof_bytes.len() - remainder.len(),
            remaining: remainder.len(),
        });
    }
    Ok(VerifiedStateOnlyProfile22Openings {
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
    fn profile22_geometry_is_frozen() {
        assert_eq!(PROFILE22_LAYER0_LEAF_COUNT, 1 << 17);
        assert_eq!(PROFILE22_PRIVATE_DEPTHS, [17, 17, 15, 13, 11]);
        assert_eq!(PROFILE22_PRIVATE_VALUE_WIDTHS, [416, 128, 64, 64, 64]);
        assert_eq!(
            PROFILE22_PRIVATE_TREE_TAGS,
            [
                CIRCLE_C1_LAYER0_TAG,
                CIRCLE_C2_LAYER0_TAG,
                CIRCLE_LINE_TAGS[0],
                CIRCLE_LINE_TAGS[1],
                CIRCLE_LINE_TAGS[2],
            ]
        );
        let indices = derive_circle_line_query_indices_for_count(
            &[0, 1, 3, 4, 15, 16, 63, 64, 131_071],
            PROFILE22_LAYER0_LEAF_COUNT,
        )
        .unwrap();
        assert_eq!(indices.layer0, [0, 1, 3, 4, 15, 16, 63, 64, 131_071]);
        assert_eq!(indices.later[0], [0, 1, 3, 4, 15, 16, 32_767]);
        assert_eq!(indices.later[1], [0, 1, 3, 4, 8_191]);
        assert_eq!(indices.later[2], [0, 1, 2_047]);
    }
}
