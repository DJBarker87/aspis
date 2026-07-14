//! Fixed layer-zero Merkle openings for the M31 circle candidate.
//!
//! This module authenticates already-derived query fibers against one C1 and
//! one C2 root. It does not parse a proof prefix, drive a transcript, enable
//! tag 24, select a two-point rule, or accept a complete proof.

use alloc::vec::Vec;

use crate::field::{M31, QM31};
use crate::merkle::{leaf_hash, verify_radix4_binary_cap_prevalidated_in_place};
use crate::proof::{
    M31_CIRCLE_C1_FIBER_LEN, M31_CIRCLE_C2_LAYER_TAG, M31_CIRCLE_COMBINED_LAYER_TAG_BASE,
    SECOND_PHASE_LEAF_LEN_V4_S2,
};
use crate::HashFn;

pub const CIRCLE_LAYER0_BINARY_DEPTH: u32 = 10;
pub const CIRCLE_LAYER0_FIBER_COUNT: usize = 1 << CIRCLE_LAYER0_BINARY_DEPTH;
pub const CIRCLE_C1_LEAF_BYTES: usize = M31_CIRCLE_C1_FIBER_LEN;
pub const CIRCLE_C2_LEAF_BYTES: usize = SECOND_PHASE_LEAF_LEN_V4_S2;
pub const CIRCLE_C1_LAYER0_TAG: u8 = M31_CIRCLE_COMBINED_LAYER_TAG_BASE;
pub const CIRCLE_C2_LAYER0_TAG: u8 = M31_CIRCLE_C2_LAYER_TAG;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleMerkleError {
    EmptyOpening,
    CountOutOfRange { count: usize },
    CountMismatch { expected: usize, actual: usize },
    UnexpectedEnd { offset: usize, needed: usize },
    TrailingBytes { offset: usize, remaining: usize },
    LengthOverflow,
    InvalidC1LeafBytes { actual: usize },
    InvalidC2LeafBytes { actual: usize },
    IndicesNotStrictlyIncreasing,
    FiberIndexOutOfRange { index: u32 },
    NonCanonicalC1 { leaf: usize, offset: usize },
    NonCanonicalC2 { leaf: usize, offset: usize },
    C1MerkleMismatch,
    C2MerkleMismatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleLayer0OpeningOffsets {
    pub unique_count: usize,
    pub c1_leaves: usize,
    pub c2_leaves: usize,
    pub c1_node_count: usize,
    pub c1_frontier: usize,
    pub c2_node_count: usize,
    pub c2_frontier: usize,
    pub end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleLayer0Opening<'a> {
    pub unique_count: usize,
    pub c1_leaf_bytes: usize,
    pub c2_leaf_bytes: usize,
    pub c1_leaves: &'a [u8],
    pub c2_leaves: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
    pub offsets: CircleLayer0OpeningOffsets,
}

impl<'a> CircleLayer0Opening<'a> {
    pub fn c1_leaf(&self, index: usize) -> Option<&'a [u8]> {
        if index >= self.unique_count {
            return None;
        }
        let start = index.checked_mul(self.c1_leaf_bytes)?;
        let end = start.checked_add(self.c1_leaf_bytes)?;
        self.c1_leaves.get(start..end)
    }

    pub fn c2_leaf(&self, index: usize) -> Option<&'a [u8]> {
        if index >= self.unique_count {
            return None;
        }
        let start = index.checked_mul(self.c2_leaf_bytes)?;
        let end = start.checked_add(self.c2_leaf_bytes)?;
        self.c2_leaves.get(start..end)
    }
}

struct ExactCursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> ExactCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], CircleMerkleError> {
        let end = self
            .position
            .checked_add(len)
            .ok_or(CircleMerkleError::LengthOverflow)?;
        if end > self.bytes.len() {
            return Err(CircleMerkleError::UnexpectedEnd {
                offset: self.position,
                needed: len,
            });
        }
        let result = &self.bytes[self.position..end];
        self.position = end;
        Ok(result)
    }

    fn take_u16(&mut self) -> Result<u16, CircleMerkleError> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }

    fn take_u32(&mut self) -> Result<u32, CircleMerkleError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
}

fn section_len(count: usize, item_len: usize) -> Result<usize, CircleMerkleError> {
    count
        .checked_mul(item_len)
        .ok_or(CircleMerkleError::LengthOverflow)
}

/// Parse one fixed layer-zero opening section from the start of a larger
/// opening suffix. The caller supplies the expected unique count derived from
/// query fibers; indices are not proof data. The uninterpreted remainder is
/// returned for the three later-layer sections.
pub fn parse_circle_layer0_opening_from_proof(
    bytes: &[u8],
    expected_unique_count: usize,
) -> Result<(CircleLayer0Opening<'_>, &[u8]), CircleMerkleError> {
    parse_circle_layer0_opening_from_proof_for_depth(
        bytes,
        expected_unique_count,
        CIRCLE_LAYER0_BINARY_DEPTH,
    )
}

pub fn parse_circle_layer0_opening_from_proof_for_depth(
    bytes: &[u8],
    expected_unique_count: usize,
    binary_depth: u32,
) -> Result<(CircleLayer0Opening<'_>, &[u8]), CircleMerkleError> {
    parse_circle_layer0_opening_from_proof_for_depth_and_c2_leaf_bytes(
        bytes,
        expected_unique_count,
        binary_depth,
        CIRCLE_C2_LEAF_BYTES,
    )
}

pub fn parse_circle_layer0_opening_from_proof_for_depth_and_c2_leaf_bytes(
    bytes: &[u8],
    expected_unique_count: usize,
    binary_depth: u32,
    c2_leaf_bytes: usize,
) -> Result<(CircleLayer0Opening<'_>, &[u8]), CircleMerkleError> {
    parse_circle_layer0_opening_from_proof_for_depth_and_leaf_bytes(
        bytes,
        expected_unique_count,
        binary_depth,
        CIRCLE_C1_LEAF_BYTES,
        c2_leaf_bytes,
    )
}

pub fn parse_circle_layer0_opening_from_proof_for_depth_and_leaf_bytes(
    bytes: &[u8],
    expected_unique_count: usize,
    binary_depth: u32,
    c1_leaf_bytes: usize,
    c2_leaf_bytes: usize,
) -> Result<(CircleLayer0Opening<'_>, &[u8]), CircleMerkleError> {
    if c1_leaf_bytes == 0 || c1_leaf_bytes % 4 != 0 {
        return Err(CircleMerkleError::InvalidC1LeafBytes {
            actual: c1_leaf_bytes,
        });
    }
    if c2_leaf_bytes == 0 || c2_leaf_bytes % 16 != 0 {
        return Err(CircleMerkleError::InvalidC2LeafBytes {
            actual: c2_leaf_bytes,
        });
    }
    if expected_unique_count == 0 {
        return Err(CircleMerkleError::EmptyOpening);
    }
    let fiber_count = 1usize << binary_depth;
    if expected_unique_count > fiber_count {
        return Err(CircleMerkleError::CountOutOfRange {
            count: expected_unique_count,
        });
    }

    let mut cursor = ExactCursor::new(bytes);
    let unique_count_offset = cursor.position;
    let actual_count = usize::from(cursor.take_u16()?);
    if actual_count != expected_unique_count {
        return Err(CircleMerkleError::CountMismatch {
            expected: expected_unique_count,
            actual: actual_count,
        });
    }

    let c1_leaves_offset = cursor.position;
    let c1_leaves = cursor.take(section_len(actual_count, c1_leaf_bytes)?)?;
    let c2_leaves_offset = cursor.position;
    let c2_leaves = cursor.take(section_len(actual_count, c2_leaf_bytes)?)?;

    let c1_node_count_offset = cursor.position;
    let c1_node_count = cursor.take_u32()? as usize;
    let c1_frontier_offset = cursor.position;
    let c1_frontier = cursor.take(section_len(c1_node_count, 32)?)?;

    let c2_node_count_offset = cursor.position;
    let c2_node_count = cursor.take_u32()? as usize;
    let c2_frontier_offset = cursor.position;
    let c2_frontier = cursor.take(section_len(c2_node_count, 32)?)?;
    let end = cursor.position;

    let opening = CircleLayer0Opening {
        unique_count: actual_count,
        c1_leaf_bytes,
        c2_leaf_bytes,
        c1_leaves,
        c2_leaves,
        c1_frontier,
        c2_frontier,
        offsets: CircleLayer0OpeningOffsets {
            unique_count: unique_count_offset,
            c1_leaves: c1_leaves_offset,
            c2_leaves: c2_leaves_offset,
            c1_node_count: c1_node_count_offset,
            c1_frontier: c1_frontier_offset,
            c2_node_count: c2_node_count_offset,
            c2_frontier: c2_frontier_offset,
            end,
        },
    };
    Ok((opening, &bytes[end..]))
}

/// Parse exactly one fixed layer-zero section and reject any unconsumed byte.
pub fn parse_circle_layer0_opening(
    bytes: &[u8],
    expected_unique_count: usize,
) -> Result<CircleLayer0Opening<'_>, CircleMerkleError> {
    let (opening, remainder) =
        parse_circle_layer0_opening_from_proof(bytes, expected_unique_count)?;
    if !remainder.is_empty() {
        return Err(CircleMerkleError::TrailingBytes {
            offset: opening.offsets.end,
            remaining: remainder.len(),
        });
    }
    Ok(opening)
}

fn validate_indices_for_depth(indices: &[u32], binary_depth: u32) -> Result<(), CircleMerkleError> {
    if indices.is_empty() {
        return Err(CircleMerkleError::EmptyOpening);
    }
    for pair in indices.windows(2) {
        if pair[0] >= pair[1] {
            return Err(CircleMerkleError::IndicesNotStrictlyIncreasing);
        }
    }
    let fiber_count = 1u32 << binary_depth;
    if let Some(&index) = indices.iter().find(|&&index| index >= fiber_count) {
        return Err(CircleMerkleError::FiberIndexOutOfRange { index });
    }
    Ok(())
}

#[cfg(test)]
fn validate_indices(indices: &[u32]) -> Result<(), CircleMerkleError> {
    validate_indices_for_depth(indices, CIRCLE_LAYER0_BINARY_DEPTH)
}

fn validate_canonical_leaves(opening: &CircleLayer0Opening<'_>) -> Result<(), CircleMerkleError> {
    for leaf in 0..opening.unique_count {
        let bytes = opening.c1_leaf(leaf).unwrap();
        for (offset, value) in bytes.chunks_exact(4).enumerate() {
            if M31::from_le_bytes(value.try_into().unwrap()).is_none() {
                return Err(CircleMerkleError::NonCanonicalC1 {
                    leaf,
                    offset: offset * 4,
                });
            }
        }
    }
    for leaf in 0..opening.unique_count {
        let bytes = opening.c2_leaf(leaf).unwrap();
        for (offset, value) in bytes.chunks_exact(16).enumerate() {
            if QM31::from_le_bytes(value).is_none() {
                return Err(CircleMerkleError::NonCanonicalC2 {
                    leaf,
                    offset: offset * 16,
                });
            }
        }
    }
    Ok(())
}

fn verify_parsed_circle_layer0_opening(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    unique_indices: &[u32],
    opening: &CircleLayer0Opening<'_>,
    validate_canonical: bool,
    binary_depth: u32,
) -> Result<(), CircleMerkleError> {
    validate_indices_for_depth(unique_indices, binary_depth)?;
    if validate_canonical {
        validate_canonical_leaves(opening)?;
    }

    let mut level = Vec::with_capacity(opening.unique_count);
    for (leaf, &fiber_index) in unique_indices.iter().enumerate() {
        level.push((
            fiber_index,
            leaf_hash(hash, CIRCLE_C1_LAYER0_TAG, opening.c1_leaf(leaf).unwrap()),
        ));
    }
    let mut next = Vec::with_capacity(opening.unique_count);
    if !verify_radix4_binary_cap_prevalidated_in_place(
        hash,
        c1_root,
        binary_depth,
        opening.c1_frontier,
        &mut level,
        &mut next,
    ) {
        return Err(CircleMerkleError::C1MerkleMismatch);
    }

    level.clear();
    for (leaf, &fiber_index) in unique_indices.iter().enumerate() {
        level.push((
            fiber_index,
            leaf_hash(hash, CIRCLE_C2_LAYER0_TAG, opening.c2_leaf(leaf).unwrap()),
        ));
    }
    if !verify_radix4_binary_cap_prevalidated_in_place(
        hash,
        c2_root,
        binary_depth,
        opening.c2_frontier,
        &mut level,
        &mut next,
    ) {
        return Err(CircleMerkleError::C2MerkleMismatch);
    }

    Ok(())
}

/// Parse and authenticate one exact C1+C2 layer-zero opening. The two
/// frontiers are independently framed and verified under their fixed tags.
pub fn verify_circle_layer0_opening<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    unique_indices: &[u32],
    proof_bytes: &'a [u8],
) -> Result<CircleLayer0Opening<'a>, CircleMerkleError> {
    let opening = parse_circle_layer0_opening(proof_bytes, unique_indices.len())?;
    verify_parsed_circle_layer0_opening(
        hash,
        c1_root,
        c2_root,
        unique_indices,
        &opening,
        true,
        CIRCLE_LAYER0_BINARY_DEPTH,
    )?;
    Ok(opening)
}

/// Authenticate the layer-zero section at the start of a combined opening
/// suffix and return the still-unparsed later-layer bytes.
pub fn verify_circle_layer0_opening_from_proof<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    unique_indices: &[u32],
    proof_bytes: &'a [u8],
) -> Result<(CircleLayer0Opening<'a>, &'a [u8]), CircleMerkleError> {
    let (opening, remainder) =
        parse_circle_layer0_opening_from_proof(proof_bytes, unique_indices.len())?;
    verify_parsed_circle_layer0_opening(
        hash,
        c1_root,
        c2_root,
        unique_indices,
        &opening,
        true,
        CIRCLE_LAYER0_BINARY_DEPTH,
    )?;
    Ok((opening, remainder))
}

/// Authenticate layer zero while deferring field canonicality to the fixed
/// composed verifier, which subsequently decodes every opened leaf.
pub(crate) fn verify_circle_layer0_opening_from_proof_deferred_canonical_for_depth_and_c2_leaf_bytes<
    'a,
>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    unique_indices: &[u32],
    proof_bytes: &'a [u8],
    binary_depth: u32,
    c2_leaf_bytes: usize,
) -> Result<(CircleLayer0Opening<'a>, &'a [u8]), CircleMerkleError> {
    verify_circle_layer0_opening_from_proof_deferred_canonical_for_depth_and_leaf_bytes(
        hash,
        c1_root,
        c2_root,
        unique_indices,
        proof_bytes,
        binary_depth,
        CIRCLE_C1_LEAF_BYTES,
        c2_leaf_bytes,
    )
}

pub(crate) fn verify_circle_layer0_opening_from_proof_deferred_canonical_for_depth_and_leaf_bytes<
    'a,
>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    unique_indices: &[u32],
    proof_bytes: &'a [u8],
    binary_depth: u32,
    c1_leaf_bytes: usize,
    c2_leaf_bytes: usize,
) -> Result<(CircleLayer0Opening<'a>, &'a [u8]), CircleMerkleError> {
    let (opening, remainder) = parse_circle_layer0_opening_from_proof_for_depth_and_leaf_bytes(
        proof_bytes,
        unique_indices.len(),
        binary_depth,
        c1_leaf_bytes,
        c2_leaf_bytes,
    )?;
    verify_parsed_circle_layer0_opening(
        hash,
        c1_root,
        c2_root,
        unique_indices,
        &opening,
        false,
        binary_depth,
    )?;
    Ok((opening, remainder))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn framed(count: usize, c1_nodes: usize, c2_nodes: usize) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&(count as u16).to_le_bytes());
        bytes.resize(bytes.len() + count * CIRCLE_C1_LEAF_BYTES, 0);
        bytes.resize(bytes.len() + count * CIRCLE_C2_LEAF_BYTES, 0);
        bytes.extend_from_slice(&(c1_nodes as u32).to_le_bytes());
        bytes.resize(bytes.len() + c1_nodes * 32, 0);
        bytes.extend_from_slice(&(c2_nodes as u32).to_le_bytes());
        bytes.resize(bytes.len() + c2_nodes * 32, 0);
        bytes
    }

    #[test]
    fn exact_parser_offsets_and_leaf_slices_are_pinned() {
        let bytes = framed(2, 3, 4);
        let parsed = parse_circle_layer0_opening(&bytes, 2).unwrap();
        assert_eq!(parsed.unique_count, 2);
        assert_eq!(parsed.c1_leaves.len(), 1_568);
        assert_eq!(parsed.c2_leaves.len(), 256);
        assert_eq!(parsed.c1_frontier.len(), 96);
        assert_eq!(parsed.c2_frontier.len(), 128);
        assert_eq!(
            parsed.offsets,
            CircleLayer0OpeningOffsets {
                unique_count: 0,
                c1_leaves: 2,
                c2_leaves: 1_570,
                c1_node_count: 1_826,
                c1_frontier: 1_830,
                c2_node_count: 1_926,
                c2_frontier: 1_930,
                end: 2_058,
            }
        );
        assert_eq!(parsed.c1_leaf(0).unwrap().as_ptr(), bytes[2..].as_ptr());
        assert_eq!(parsed.c1_leaf(1).unwrap().len(), CIRCLE_C1_LEAF_BYTES);
        assert_eq!(parsed.c2_leaf(0).unwrap().as_ptr(), bytes[1_570..].as_ptr());
        assert!(parsed.c1_leaf(2).is_none());
        assert!(parsed.c2_leaf(2).is_none());
    }

    #[test]
    fn profile14_parser_uses_explicit_448_byte_c2_leaves() {
        const PROFILE14_C2_BYTES: usize = 7 * 4 * 16;
        let count = 2usize;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&(count as u16).to_le_bytes());
        bytes.resize(bytes.len() + count * CIRCLE_C1_LEAF_BYTES, 0);
        bytes.resize(bytes.len() + count * PROFILE14_C2_BYTES, 0);
        bytes.extend_from_slice(&0u32.to_le_bytes());
        bytes.extend_from_slice(&0u32.to_le_bytes());
        let (parsed, remainder) =
            parse_circle_layer0_opening_from_proof_for_depth_and_c2_leaf_bytes(
                &bytes,
                count,
                12,
                PROFILE14_C2_BYTES,
            )
            .unwrap();
        assert!(remainder.is_empty());
        assert_eq!(parsed.c2_leaf_bytes, PROFILE14_C2_BYTES);
        assert_eq!(parsed.c2_leaf(0).unwrap().len(), PROFILE14_C2_BYTES);
        assert_eq!(
            parsed.c2_leaf(1).unwrap().as_ptr(),
            bytes[2 + 2 * CIRCLE_C1_LEAF_BYTES + PROFILE14_C2_BYTES..].as_ptr()
        );
        assert_eq!(
            parse_circle_layer0_opening_from_proof_for_depth_and_c2_leaf_bytes(
                &bytes,
                count,
                12,
                PROFILE14_C2_BYTES - 1,
            ),
            Err(CircleMerkleError::InvalidC2LeafBytes {
                actual: PROFILE14_C2_BYTES - 1,
            }),
        );
    }

    #[test]
    fn exact_parser_rejects_count_truncation_and_trailing_bytes() {
        let bytes = framed(2, 3, 4);
        assert_eq!(
            parse_circle_layer0_opening(&bytes, 3),
            Err(CircleMerkleError::CountMismatch {
                expected: 3,
                actual: 2,
            })
        );
        assert_eq!(
            parse_circle_layer0_opening(&[], 1),
            Err(CircleMerkleError::UnexpectedEnd {
                offset: 0,
                needed: 2,
            })
        );
        let truncated = &bytes[..bytes.len() - 1];
        assert_eq!(
            parse_circle_layer0_opening(truncated, 2),
            Err(CircleMerkleError::UnexpectedEnd {
                offset: 1_930,
                needed: 128,
            })
        );
        let mut trailing = bytes;
        trailing.push(0);
        let (prefix, remainder) = parse_circle_layer0_opening_from_proof(&trailing, 2).unwrap();
        assert_eq!(prefix.offsets.end, 2_058);
        assert_eq!(remainder, [0]);
        assert_eq!(
            parse_circle_layer0_opening(&trailing, 2),
            Err(CircleMerkleError::TrailingBytes {
                offset: 2_058,
                remaining: 1,
            })
        );
        assert_eq!(
            parse_circle_layer0_opening(&[0; 2], 0),
            Err(CircleMerkleError::EmptyOpening)
        );
        assert_eq!(
            parse_circle_layer0_opening(&[0; 2], 1_025),
            Err(CircleMerkleError::CountOutOfRange { count: 1_025 })
        );
    }

    #[test]
    fn index_contract_rejects_duplicates_unsorted_and_out_of_range() {
        assert_eq!(
            validate_indices(&[1, 1]),
            Err(CircleMerkleError::IndicesNotStrictlyIncreasing)
        );
        assert_eq!(
            validate_indices(&[2, 1]),
            Err(CircleMerkleError::IndicesNotStrictlyIncreasing)
        );
        assert_eq!(
            validate_indices(&[0, 1_024]),
            Err(CircleMerkleError::FiberIndexOutOfRange { index: 1_024 })
        );
    }
}
