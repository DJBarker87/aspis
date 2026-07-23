//! Five-section private-opening grammar for V5.
//!
//! The earlier production helper fixes C1 at 416 bytes. V5 keeps the same query
//! universe, depths, tree tags, C2 width, and three later-tree widths, but its
//! real sixteen-lane C1 leaf is 256 bytes. The production verifier and local CU
//! probe share this grammar and the public `aspis-core` authentication
//! primitives.

use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineMerkleError, CircleLineQueryIndices,
    CIRCLE_LINE_TAGS,
};
use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::merkle::Radix4BinaryCapTopology;
use aspis_core::state_only_private_openings::{
    verify_state_only_private_opening_from_proof_with_topology, StateOnlyPrivateOpening,
    StateOnlyPrivateOpeningError,
};
use aspis_core::HashFn;

pub const V5_PRIVATE_LAYER0_LEAVES: usize = 1 << 17;
pub const V5_PRIVATE_SECTION_COUNT: usize = 5;
pub const V5_PRIVATE_DEPTHS: [u32; V5_PRIVATE_SECTION_COUNT] = [17, 17, 15, 13, 11];
pub const V5_PRIVATE_VALUE_WIDTHS: [usize; V5_PRIVATE_SECTION_COUNT] = [256, 192, 64, 64, 64];
pub const V5_PRIVATE_TREE_TAGS: [u8; V5_PRIVATE_SECTION_COUNT] = [
    CIRCLE_C1_LAYER0_TAG,
    CIRCLE_C2_LAYER0_TAG,
    CIRCLE_LINE_TAGS[0],
    CIRCLE_LINE_TAGS[1],
    CIRCLE_LINE_TAGS[2],
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5PrivateOpeningRoots {
    pub c1: [u8; 32],
    pub c2: [u8; 32],
    pub later: [[u8; 32]; 3],
}

impl V5PrivateOpeningRoots {
    fn as_array(self) -> [[u8; 32]; V5_PRIVATE_SECTION_COUNT] {
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
pub enum V5PrivateOpeningError {
    Query(CircleLineMerkleError),
    Section {
        section: u8,
        error: StateOnlyPrivateOpeningError,
    },
    TrailingBytes {
        offset: usize,
        remaining: usize,
    },
    InvalidSharedTopology,
}

impl From<CircleLineMerkleError> for V5PrivateOpeningError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedV5PrivateOpenings<'a> {
    pub c1: StateOnlyPrivateOpening<'a>,
    pub c2: StateOnlyPrivateOpening<'a>,
    pub later: [StateOnlyPrivateOpening<'a>; 3],
    pub indices: CircleLineQueryIndices,
    pub bytes_consumed: usize,
}

/// Authenticate five canonical sections at the transcript-derived queries and
/// return the unconsumed proof suffix.  Query indices are never proof bytes.
pub fn verify_v5_private_openings_from_proof<'a>(
    hash: HashFn,
    roots: &V5PrivateOpeningRoots,
    queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<(VerifiedV5PrivateOpenings<'a>, &'a [u8]), V5PrivateOpeningError> {
    let indices = derive_circle_line_query_indices_for_count(queries, V5_PRIVATE_LAYER0_LEAVES)?;
    let section_indices: [&[u32]; V5_PRIVATE_SECTION_COUNT] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let roots = roots.as_array();
    let topology = Radix4BinaryCapTopology::new(V5_PRIVATE_DEPTHS[0], &indices.layer0)
        .ok_or(V5PrivateOpeningError::InvalidSharedTopology)?;
    let mut hash_level = Vec::<[u8; 32]>::with_capacity(indices.layer0.len());
    let mut hash_next = Vec::<[u8; 32]>::with_capacity(indices.layer0.len());
    let mut remainder = proof_bytes;
    let mut parsed = [None; V5_PRIVATE_SECTION_COUNT];
    for section in 0..V5_PRIVATE_SECTION_COUNT {
        let (opening, next) = verify_state_only_private_opening_from_proof_with_topology(
            hash,
            &roots[section],
            V5_PRIVATE_DEPTHS[section],
            V5_PRIVATE_TREE_TAGS[section],
            V5_PRIVATE_VALUE_WIDTHS[section],
            section_indices[section],
            remainder,
            &topology,
            if section < 2 { 0 } else { section - 1 },
            &mut hash_level,
            &mut hash_next,
        )
        .map_err(|error| V5PrivateOpeningError::Section {
            section: section as u8,
            error,
        })?;
        parsed[section] = Some(opening);
        remainder = next;
    }
    let bytes_consumed = proof_bytes.len() - remainder.len();
    Ok((
        VerifiedV5PrivateOpenings {
            c1: parsed[0].unwrap(),
            c2: parsed[1].unwrap(),
            later: [parsed[2].unwrap(), parsed[3].unwrap(), parsed[4].unwrap()],
            indices,
            bytes_consumed,
        },
        remainder,
    ))
}

/// Authenticate exactly the five private sections and reject a trailing byte.
pub fn verify_v5_private_openings<'a>(
    hash: HashFn,
    roots: &V5PrivateOpeningRoots,
    queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedV5PrivateOpenings<'a>, V5PrivateOpeningError> {
    let (verified, remainder) =
        verify_v5_private_openings_from_proof(hash, roots, queries, proof_bytes)?;
    if !remainder.is_empty() {
        return Err(V5PrivateOpeningError::TrailingBytes {
            offset: verified.bytes_consumed,
            remaining: remainder.len(),
        });
    }
    Ok(verified)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v5_changes_only_the_c1_private_width() {
        assert_eq!(V5_PRIVATE_DEPTHS, [17, 17, 15, 13, 11]);
        assert_eq!(V5_PRIVATE_VALUE_WIDTHS, [256, 192, 64, 64, 64]);
        assert_eq!(V5_PRIVATE_SECTION_COUNT, 5);
    }
}
