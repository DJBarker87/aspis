//! Aggregate five-tree private opening verifier for state-only profile 21.

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

pub const PROFILE21_LAYER0_LEAF_COUNT: usize = 1 << 17;
pub const PROFILE21_PRIVATE_SECTION_COUNT: usize = 5;
pub const PROFILE21_PRIVATE_DEPTHS: [u32; PROFILE21_PRIVATE_SECTION_COUNT] = [17, 17, 15, 13, 11];
pub const PROFILE21_PRIVATE_VALUE_WIDTHS: [usize; PROFILE21_PRIVATE_SECTION_COUNT] =
    [416, 256, 64, 64, 64];
pub const PROFILE21_PRIVATE_TREE_TAGS: [u8; PROFILE21_PRIVATE_SECTION_COUNT] = [
    CIRCLE_C1_LAYER0_TAG,
    CIRCLE_C2_LAYER0_TAG,
    CIRCLE_LINE_TAGS[0],
    CIRCLE_LINE_TAGS[1],
    CIRCLE_LINE_TAGS[2],
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyProfile21OpeningRoots {
    pub c1: [u8; 32],
    pub c2: [u8; 32],
    pub later: [[u8; 32]; 3],
}

impl StateOnlyProfile21OpeningRoots {
    pub fn as_array(&self) -> [[u8; 32]; PROFILE21_PRIVATE_SECTION_COUNT] {
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
pub enum StateOnlyProfile21OpeningError {
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

impl From<CircleLineMerkleError> for StateOnlyProfile21OpeningError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedStateOnlyProfile21Openings<'a> {
    pub c1: StateOnlyPrivateOpening<'a>,
    pub c2: StateOnlyPrivateOpening<'a>,
    pub later: [StateOnlyPrivateOpening<'a>; 3],
    pub indices: CircleLineQueryIndices,
    pub end: usize,
}

/// Authenticate exactly C1, widened C2, W1, W2 and W3 in that order and
/// reject any unconsumed byte. Query indices are derived once from the q16
/// line positions over the fixed `2^17` layer-zero leaf domain.
pub fn verify_state_only_profile21_openings<'a>(
    hash: HashFn,
    roots: &StateOnlyProfile21OpeningRoots,
    queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedStateOnlyProfile21Openings<'a>, StateOnlyProfile21OpeningError> {
    let indices = derive_circle_line_query_indices_for_count(queries, PROFILE21_LAYER0_LEAF_COUNT)?;
    let section_indices: [&[u32]; PROFILE21_PRIVATE_SECTION_COUNT] = [
        &indices.layer0,
        &indices.layer0,
        &indices.later[0],
        &indices.later[1],
        &indices.later[2],
    ];
    let roots = roots.as_array();
    let mut remainder = proof_bytes;
    let mut parsed = [None; PROFILE21_PRIVATE_SECTION_COUNT];
    for section in 0..PROFILE21_PRIVATE_SECTION_COUNT {
        let (opening, next) = verify_state_only_private_opening_from_proof(
            hash,
            &roots[section],
            PROFILE21_PRIVATE_DEPTHS[section],
            PROFILE21_PRIVATE_TREE_TAGS[section],
            PROFILE21_PRIVATE_VALUE_WIDTHS[section],
            section_indices[section],
            remainder,
        )
        .map_err(|error| StateOnlyProfile21OpeningError::Section {
            section: section as u8,
            error,
        })?;
        parsed[section] = Some(opening);
        remainder = next;
    }
    if !remainder.is_empty() {
        return Err(StateOnlyProfile21OpeningError::TrailingBytes {
            offset: proof_bytes.len() - remainder.len(),
            remaining: remainder.len(),
        });
    }
    Ok(VerifiedStateOnlyProfile21Openings {
        c1: parsed[0].unwrap(),
        c2: parsed[1].unwrap(),
        later: [parsed[2].unwrap(), parsed[3].unwrap(), parsed[4].unwrap()],
        indices,
        end: proof_bytes.len(),
    })
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;

    use sha2::{Digest, Sha256};

    use crate::merkle::{node_hash, node_hash4};
    use crate::state_only_private_merkle::private_leaf_hash_record;

    use super::*;

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn one_leaf_section(depth: u32, tag: u8, width: usize, seed: u8) -> ([u8; 32], Vec<u8>) {
        let mut record = (0..width)
            .map(|offset| seed.wrapping_add((offset as u8).wrapping_mul(17)))
            .collect::<Vec<_>>();
        record.extend((0..32).map(|offset| {
            seed.wrapping_add(0x80)
                .wrapping_add((offset as u8).wrapping_mul(29))
        }));
        let mut accumulator = private_leaf_hash_record(test_hash, tag, &record);
        let mut frontier = Vec::new();
        for level in 0..depth / 2 {
            let siblings: [[u8; 32]; 3] =
                core::array::from_fn(|slot| test_hash(&[&[seed, level as u8, slot as u8 + 1]]));
            frontier.extend(siblings);
            accumulator = node_hash4(
                test_hash,
                &[accumulator, siblings[0], siblings[1], siblings[2]],
            );
        }
        if depth & 1 != 0 {
            let sibling = test_hash(&[&[seed, 0xff]]);
            frontier.push(sibling);
            accumulator = node_hash(test_hash, &accumulator, &sibling);
        }
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&1u16.to_le_bytes());
        bytes.extend_from_slice(&record);
        bytes.extend_from_slice(&(frontier.len() as u32).to_le_bytes());
        for node in frontier {
            bytes.extend_from_slice(&node);
        }
        (accumulator, bytes)
    }

    #[test]
    fn fixed_depth_width_tag_and_index_mapping_are_pinned() {
        assert_eq!(PROFILE21_PRIVATE_DEPTHS, [17, 17, 15, 13, 11]);
        assert_eq!(PROFILE21_PRIVATE_VALUE_WIDTHS, [416, 256, 64, 64, 64]);
        assert_eq!(
            PROFILE21_PRIVATE_TREE_TAGS,
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
            PROFILE21_LAYER0_LEAF_COUNT,
        )
        .unwrap();
        assert_eq!(indices.layer0, [0, 1, 3, 4, 15, 16, 63, 64, 131_071]);
        assert_eq!(indices.later[0], [0, 1, 3, 4, 15, 16, 32_767]);
        assert_eq!(indices.later[1], [0, 1, 3, 4, 8_191]);
        assert_eq!(indices.later[2], [0, 1, 2_047]);
    }

    #[test]
    fn aggregate_order_roots_and_trailing_teeth() {
        let sections: [([u8; 32], Vec<u8>); PROFILE21_PRIVATE_SECTION_COUNT] =
            core::array::from_fn(|section| {
                one_leaf_section(
                    PROFILE21_PRIVATE_DEPTHS[section],
                    PROFILE21_PRIVATE_TREE_TAGS[section],
                    PROFILE21_PRIVATE_VALUE_WIDTHS[section],
                    11 + section as u8 * 23,
                )
            });
        let roots = StateOnlyProfile21OpeningRoots {
            c1: sections[0].0,
            c2: sections[1].0,
            later: [sections[2].0, sections[3].0, sections[4].0],
        };
        let bytes = sections
            .iter()
            .flat_map(|(_, bytes)| bytes.iter().copied())
            .collect::<Vec<_>>();
        let verified =
            verify_state_only_profile21_openings(test_hash, &roots, &[0], &bytes).unwrap();
        assert_eq!(verified.indices.layer0, [0]);
        assert_eq!(verified.indices.later, [vec![0], vec![0], vec![0]]);
        assert_eq!(verified.c1.value_width, 416);
        assert_eq!(verified.c2.value_width, 256);
        assert_eq!(verified.later.map(|opening| opening.value_width), [64; 3]);
        assert_eq!(verified.end, bytes.len());

        let mut wrong_root = roots;
        wrong_root.c1[0] ^= 1;
        assert!(matches!(
            verify_state_only_profile21_openings(test_hash, &wrong_root, &[0], &bytes),
            Err(StateOnlyProfile21OpeningError::Section {
                section: 0,
                error: StateOnlyPrivateOpeningError::MerkleMismatch,
            })
        ));

        let wrong_order = sections[1]
            .1
            .iter()
            .chain(&sections[0].1)
            .chain(&sections[2].1)
            .chain(&sections[3].1)
            .chain(&sections[4].1)
            .copied()
            .collect::<Vec<_>>();
        assert!(
            verify_state_only_profile21_openings(test_hash, &roots, &[0], &wrong_order).is_err()
        );

        let mut trailing = bytes;
        trailing.push(0xa5);
        assert_eq!(
            verify_state_only_profile21_openings(test_hash, &roots, &[0], &trailing),
            Err(StateOnlyProfile21OpeningError::TrailingBytes {
                offset: trailing.len() - 1,
                remaining: 1,
            })
        );
    }
}
