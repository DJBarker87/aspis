//! Merkle openings for the three committed line layers of the M31 candidate.
//!
//! This module consumes only the opening suffix and roots already exposed by
//! [`crate::circle_prefix`]. It does not drive a transcript, enable tag 24,
//! select a two-point rule, or accept a complete proof.

use alloc::vec::Vec;

use crate::circle_prefix::CandidatePrefix;
use crate::field::QM31;
use crate::merkle::{leaf_hash, verify_radix4_binary_cap_prevalidated_in_place};
use crate::proof::M31_CIRCLE_COMBINED_LAYER_TAG_BASE;
use crate::HashFn;

pub const CIRCLE_LINE_LAYER_COUNT: usize = 3;
pub const CIRCLE_LINE_LEAF_BYTES: usize = 4 * 16;
pub const CIRCLE_LINE_BINARY_DEPTHS: [u32; CIRCLE_LINE_LAYER_COUNT] = [8, 6, 4];
pub const CIRCLE_LINE_TAGS: [u8; CIRCLE_LINE_LAYER_COUNT] = [
    M31_CIRCLE_COMBINED_LAYER_TAG_BASE + 1,
    M31_CIRCLE_COMBINED_LAYER_TAG_BASE + 2,
    M31_CIRCLE_COMBINED_LAYER_TAG_BASE + 3,
];
pub const CIRCLE_LINE_QUERY_SHIFTS: [u32; CIRCLE_LINE_LAYER_COUNT] = [2, 4, 6];
pub const CIRCLE_LINE_SLOT_SHIFTS: [u32; CIRCLE_LINE_LAYER_COUNT] = [0, 2, 4];
pub const CIRCLE_LINE_LEAF_COUNTS: [usize; CIRCLE_LINE_LAYER_COUNT] = [256, 64, 16];
const LAYER0_QUERY_COUNT: usize = 1 << 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleOpeningGeometry {
    pub layer0_binary_depth: u32,
    pub later_binary_depths: [u32; CIRCLE_LINE_LAYER_COUNT],
}

pub const FIXED_CIRCLE_OPENING_GEOMETRY: CircleOpeningGeometry = CircleOpeningGeometry {
    layer0_binary_depth: 10,
    later_binary_depths: CIRCLE_LINE_BINARY_DEPTHS,
};

pub const RATE16_CIRCLE_OPENING_GEOMETRY: CircleOpeningGeometry = CircleOpeningGeometry {
    layer0_binary_depth: 12,
    later_binary_depths: [10, 8, 6],
};

pub const RATE32_CIRCLE_OPENING_GEOMETRY: CircleOpeningGeometry = CircleOpeningGeometry {
    layer0_binary_depth: 13,
    later_binary_depths: [11, 9, 7],
};

/// Rate-1/512 geometry for the unchanged 1,024-coefficient message.  Four
/// arity-four folds preserve the rate while each committed tree is four
/// binary levels deeper than the rate-1/32 profile.
pub const RATE512_CIRCLE_OPENING_GEOMETRY: CircleOpeningGeometry = CircleOpeningGeometry {
    layer0_binary_depth: 17,
    later_binary_depths: [15, 13, 11],
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleLineMerkleError {
    EmptyQueries,
    QueryOutOfRange {
        query: u32,
    },
    CountMismatch {
        layer: u8,
        expected: usize,
        actual: usize,
    },
    UnexpectedEnd {
        layer: u8,
        offset: usize,
        needed: usize,
    },
    TrailingBytes {
        offset: usize,
        remaining: usize,
    },
    LengthOverflow,
    NonCanonicalLeaf {
        layer: u8,
        leaf: usize,
        offset: usize,
    },
    MerkleMismatch {
        layer: u8,
    },
    PrefixRootMissing {
        layer: u8,
    },
    InvalidLayer {
        layer: u8,
    },
    QueryNotOpened {
        query: u32,
    },
    LeafIndexNotFound {
        layer: u8,
        index: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircleLineQueryIndices {
    pub layer0: Vec<u32>,
    pub later: [Vec<u32>; CIRCLE_LINE_LAYER_COUNT],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleLineLayerOffsets {
    pub record_start: usize,
    pub unique_count: usize,
    pub leaves: usize,
    pub frontier_count: usize,
    pub frontier: usize,
    pub record_end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleLineLayerOpening<'a> {
    pub layer: u8,
    pub unique_count: usize,
    pub leaves: &'a [u8],
    pub frontier: &'a [u8],
    pub offsets: CircleLineLayerOffsets,
}

impl<'a> CircleLineLayerOpening<'a> {
    pub fn leaf(&self, ordinal: usize) -> Option<&'a [u8; CIRCLE_LINE_LEAF_BYTES]> {
        if ordinal >= self.unique_count {
            return None;
        }
        let start = ordinal.checked_mul(CIRCLE_LINE_LEAF_BYTES)?;
        let end = start.checked_add(CIRCLE_LINE_LEAF_BYTES)?;
        self.leaves.get(start..end)?.try_into().ok()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleLineOpenings<'a> {
    pub layers: [CircleLineLayerOpening<'a>; CIRCLE_LINE_LAYER_COUNT],
    pub end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleLineQuerySlot<'a> {
    pub layer: u8,
    pub leaf_index: u32,
    pub slot: u8,
    pub leaf: &'a [u8; CIRCLE_LINE_LEAF_BYTES],
}

impl CircleLineQuerySlot<'_> {
    pub fn value(&self) -> QM31 {
        let start = usize::from(self.slot) * 16;
        QM31::from_le_bytes(&self.leaf[start..start + 16]).unwrap()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedCircleLineOpenings<'a> {
    pub openings: CircleLineOpenings<'a>,
    pub indices: CircleLineQueryIndices,
}

impl<'a> VerifiedCircleLineOpenings<'a> {
    pub fn query_leaf_slot(
        &self,
        query: u32,
        layer: u8,
    ) -> Result<CircleLineQuerySlot<'a>, CircleLineMerkleError> {
        let layer_index = usize::from(
            layer
                .checked_sub(1)
                .ok_or(CircleLineMerkleError::InvalidLayer { layer })?,
        );
        if layer_index >= CIRCLE_LINE_LAYER_COUNT {
            return Err(CircleLineMerkleError::InvalidLayer { layer });
        }
        if self.indices.layer0.binary_search(&query).is_err() {
            return Err(CircleLineMerkleError::QueryNotOpened { query });
        }
        let leaf_index = query >> CIRCLE_LINE_QUERY_SHIFTS[layer_index];
        let ordinal = self.indices.later[layer_index]
            .binary_search(&leaf_index)
            .map_err(|_| CircleLineMerkleError::LeafIndexNotFound {
                layer,
                index: leaf_index,
            })?;
        let slot = ((query >> CIRCLE_LINE_SLOT_SHIFTS[layer_index]) & 3) as u8;
        Ok(CircleLineQuerySlot {
            layer,
            leaf_index,
            slot,
            leaf: self.openings.layers[layer_index].leaf(ordinal).ok_or(
                CircleLineMerkleError::LeafIndexNotFound {
                    layer,
                    index: leaf_index,
                },
            )?,
        })
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

    fn take(&mut self, layer: u8, len: usize) -> Result<&'a [u8], CircleLineMerkleError> {
        let end = self
            .position
            .checked_add(len)
            .ok_or(CircleLineMerkleError::LengthOverflow)?;
        if end > self.bytes.len() {
            return Err(CircleLineMerkleError::UnexpectedEnd {
                layer,
                offset: self.position,
                needed: len,
            });
        }
        let result = &self.bytes[self.position..end];
        self.position = end;
        Ok(result)
    }

    fn take_u16(&mut self, layer: u8) -> Result<u16, CircleLineMerkleError> {
        Ok(u16::from_le_bytes(self.take(layer, 2)?.try_into().unwrap()))
    }

    fn take_u32(&mut self, layer: u8) -> Result<u32, CircleLineMerkleError> {
        Ok(u32::from_le_bytes(self.take(layer, 4)?.try_into().unwrap()))
    }
}

fn checked_section_len(count: usize, width: usize) -> Result<usize, CircleLineMerkleError> {
    count
        .checked_mul(width)
        .ok_or(CircleLineMerkleError::LengthOverflow)
}

/// Sort/deduplicate layer-zero queries and derive the three fixed later leaf
/// index sets: unique `q>>2`, `q>>4`, and `q>>6`.
pub fn derive_circle_line_query_indices(
    layer0_queries: &[u32],
) -> Result<CircleLineQueryIndices, CircleLineMerkleError> {
    derive_circle_line_query_indices_for_count(layer0_queries, LAYER0_QUERY_COUNT)
}

fn sorted_unique_shifted(indices: &[u32], shift: u32) -> Vec<u32> {
    let mut result = Vec::with_capacity(indices.len());
    let mut index = 0usize;
    while index < indices.len() {
        let value = indices[index] >> shift;
        if result.len() == 0 || result[result.len() - 1] != value {
            result.push(value);
        }
        index += 1;
    }
    result
}

pub fn derive_circle_line_query_indices_for_count(
    layer0_queries: &[u32],
    layer0_query_count: usize,
) -> Result<CircleLineQueryIndices, CircleLineMerkleError> {
    if layer0_queries.len() == 0 {
        return Err(CircleLineMerkleError::EmptyQueries);
    }
    let query_limit = layer0_query_count as u32;
    let mut input_index = 0usize;
    while input_index < layer0_queries.len() {
        let query = layer0_queries[input_index];
        if query >= query_limit {
            return Err(CircleLineMerkleError::QueryOutOfRange { query });
        }
        input_index += 1;
    }

    let mut sorted = layer0_queries.to_vec();
    let mut index = 1usize;
    while index < sorted.len() {
        let mut position = index;
        while position > 0 && sorted[position] < sorted[position - 1] {
            sorted.swap(position, position - 1);
            position -= 1;
        }
        index += 1;
    }

    let mut layer0 = Vec::with_capacity(sorted.len());
    let mut index = 0usize;
    while index < sorted.len() {
        let value = sorted[index];
        if layer0.len() == 0 || layer0[layer0.len() - 1] != value {
            layer0.push(value);
        }
        index += 1;
    }
    let later = [
        sorted_unique_shifted(&layer0, CIRCLE_LINE_QUERY_SHIFTS[0]),
        sorted_unique_shifted(&layer0, CIRCLE_LINE_QUERY_SHIFTS[1]),
        sorted_unique_shifted(&layer0, CIRCLE_LINE_QUERY_SHIFTS[2]),
    ];
    Ok(CircleLineQueryIndices { layer0, later })
}

fn parse_layer<'a>(
    cursor: &mut ExactCursor<'a>,
    layer_index: usize,
    expected_count: usize,
) -> Result<CircleLineLayerOpening<'a>, CircleLineMerkleError> {
    let layer = layer_index as u8 + 1;
    let record_start = cursor.position;
    let count_offset = cursor.position;
    let actual_count = usize::from(cursor.take_u16(layer)?);
    if actual_count != expected_count {
        return Err(CircleLineMerkleError::CountMismatch {
            layer,
            expected: expected_count,
            actual: actual_count,
        });
    }
    let leaves_offset = cursor.position;
    let leaves = cursor.take(
        layer,
        checked_section_len(actual_count, CIRCLE_LINE_LEAF_BYTES)?,
    )?;
    let frontier_count_offset = cursor.position;
    let frontier_count = cursor.take_u32(layer)? as usize;
    let frontier_offset = cursor.position;
    let frontier = cursor.take(layer, checked_section_len(frontier_count, 32)?)?;
    Ok(CircleLineLayerOpening {
        layer,
        unique_count: actual_count,
        leaves,
        frontier,
        offsets: CircleLineLayerOffsets {
            record_start,
            unique_count: count_offset,
            leaves: leaves_offset,
            frontier_count: frontier_count_offset,
            frontier: frontier_offset,
            record_end: cursor.position,
        },
    })
}

/// Parse exactly three sequential line-layer opening records. Counts are
/// recomputed from the supplied layer-zero queries; no indices are proof data.
pub fn parse_circle_line_openings<'a>(
    bytes: &'a [u8],
    layer0_queries: &[u32],
) -> Result<CircleLineOpenings<'a>, CircleLineMerkleError> {
    parse_circle_line_openings_for_geometry(bytes, layer0_queries, FIXED_CIRCLE_OPENING_GEOMETRY)
}

pub fn parse_circle_line_openings_for_geometry<'a>(
    bytes: &'a [u8],
    layer0_queries: &[u32],
    geometry: CircleOpeningGeometry,
) -> Result<CircleLineOpenings<'a>, CircleLineMerkleError> {
    let indices = derive_circle_line_query_indices_for_count(
        layer0_queries,
        1usize << geometry.layer0_binary_depth,
    )?;
    parse_circle_line_openings_with_indices(bytes, &indices)
}

/// Parse later-layer records using query indices already range-checked,
/// sorted, and deduplicated by the composed opening verifier.
pub(crate) fn parse_circle_line_openings_with_indices<'a>(
    bytes: &'a [u8],
    indices: &CircleLineQueryIndices,
) -> Result<CircleLineOpenings<'a>, CircleLineMerkleError> {
    let mut cursor = ExactCursor::new(bytes);
    let layer1 = parse_layer(&mut cursor, 0, indices.later[0].len())?;
    let layer2 = parse_layer(&mut cursor, 1, indices.later[1].len())?;
    let layer3 = parse_layer(&mut cursor, 2, indices.later[2].len())?;
    if cursor.position != bytes.len() {
        return Err(CircleLineMerkleError::TrailingBytes {
            offset: cursor.position,
            remaining: bytes.len() - cursor.position,
        });
    }
    Ok(CircleLineOpenings {
        layers: [layer1, layer2, layer3],
        end: cursor.position,
    })
}

fn validate_canonical_layer(
    opening: &CircleLineLayerOpening<'_>,
) -> Result<(), CircleLineMerkleError> {
    for leaf in 0..opening.unique_count {
        let bytes = opening.leaf(leaf).unwrap();
        for (slot, value) in bytes.chunks_exact(16).enumerate() {
            if QM31::from_le_bytes(value).is_none() {
                return Err(CircleLineMerkleError::NonCanonicalLeaf {
                    layer: opening.layer,
                    leaf,
                    offset: slot * 16,
                });
            }
        }
    }
    Ok(())
}

/// Authenticate all three fixed later layers against explicit roots.
fn verify_circle_line_openings_with_canonical_policy<'a>(
    hash: HashFn,
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    validate_canonical: bool,
    geometry: CircleOpeningGeometry,
    layer_tags: [u8; CIRCLE_LINE_LAYER_COUNT],
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    let indices = derive_circle_line_query_indices_for_count(
        layer0_queries,
        1usize << geometry.layer0_binary_depth,
    )?;
    verify_circle_line_openings_with_canonical_policy_and_indices(
        hash,
        roots,
        indices,
        proof_bytes,
        validate_canonical,
        geometry,
        layer_tags,
    )
}

fn verify_circle_line_openings_with_canonical_policy_and_indices<'a>(
    hash: HashFn,
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    indices: CircleLineQueryIndices,
    proof_bytes: &'a [u8],
    validate_canonical: bool,
    geometry: CircleOpeningGeometry,
    layer_tags: [u8; CIRCLE_LINE_LAYER_COUNT],
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    let openings = parse_circle_line_openings_with_indices(proof_bytes, &indices)?;
    let largest_count = indices.later[0].len();
    let mut level = Vec::with_capacity(largest_count);
    let mut next = Vec::with_capacity(largest_count);
    for layer_index in 0..CIRCLE_LINE_LAYER_COUNT {
        let opening = &openings.layers[layer_index];
        if validate_canonical {
            validate_canonical_layer(opening)?;
        }
        level.clear();
        for (ordinal, &leaf_index) in indices.later[layer_index].iter().enumerate() {
            level.push((
                leaf_index,
                leaf_hash(
                    hash,
                    layer_tags[layer_index],
                    opening.leaf(ordinal).unwrap(),
                ),
            ));
        }
        if !verify_radix4_binary_cap_prevalidated_in_place(
            hash,
            &roots[layer_index],
            geometry.later_binary_depths[layer_index],
            opening.frontier,
            &mut level,
            &mut next,
        ) {
            return Err(CircleLineMerkleError::MerkleMismatch {
                layer: layer_index as u8 + 1,
            });
        }
    }
    Ok(VerifiedCircleLineOpenings { openings, indices })
}

/// Authenticate later layers using the single prederived index object owned
/// by the composed verifier. This is acceptance-equivalent to the public
/// wrapper and avoids cloning/sorting the transcript queries two more times.
pub(crate) fn verify_circle_line_openings_deferred_canonical_for_geometry_with_indices<'a>(
    hash: HashFn,
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    indices: CircleLineQueryIndices,
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    verify_circle_line_openings_with_canonical_policy_and_indices(
        hash,
        roots,
        indices,
        proof_bytes,
        false,
        geometry,
        CIRCLE_LINE_TAGS,
    )
}

pub(crate) fn verify_circle_line_openings_for_geometry_with_indices<'a>(
    hash: HashFn,
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    indices: CircleLineQueryIndices,
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    verify_circle_line_openings_with_canonical_policy_and_indices(
        hash,
        roots,
        indices,
        proof_bytes,
        true,
        geometry,
        CIRCLE_LINE_TAGS,
    )
}

pub fn verify_circle_line_openings<'a>(
    hash: HashFn,
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    verify_circle_line_openings_with_canonical_policy(
        hash,
        roots,
        layer0_queries,
        proof_bytes,
        true,
        FIXED_CIRCLE_OPENING_GEOMETRY,
        CIRCLE_LINE_TAGS,
    )
}

#[allow(dead_code)] // retained for internal callers which have not prederived indices
pub(crate) fn verify_circle_line_openings_deferred_canonical_for_geometry<'a>(
    hash: HashFn,
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    verify_circle_line_openings_with_canonical_policy(
        hash,
        roots,
        layer0_queries,
        proof_bytes,
        false,
        geometry,
        CIRCLE_LINE_TAGS,
    )
}

/// Authenticate all three later layers under an additive profile's exact
/// tags and geometry. Query indices remain transcript-derived and are never
/// accepted as proof data.
pub fn verify_circle_line_openings_for_geometry_and_tags_with_indices<'a>(
    hash: HashFn,
    roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    indices: CircleLineQueryIndices,
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
    layer_tags: [u8; CIRCLE_LINE_LAYER_COUNT],
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    verify_circle_line_openings_with_canonical_policy_and_indices(
        hash,
        roots,
        indices,
        proof_bytes,
        true,
        geometry,
        layer_tags,
    )
}

/// Authenticate against the three later roots already parsed from the fixed
/// candidate prefix. This does not otherwise validate or execute the prefix.
pub fn verify_circle_line_openings_for_prefix<'a>(
    hash: HashFn,
    prefix: &CandidatePrefix<'_>,
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedCircleLineOpenings<'a>, CircleLineMerkleError> {
    let mut roots = [[0u8; 32]; CIRCLE_LINE_LAYER_COUNT];
    for (layer_index, root) in roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer_index + 1].root.copied().ok_or(
            CircleLineMerkleError::PrefixRootMissing {
                layer: layer_index as u8 + 1,
            },
        )?;
    }
    verify_circle_line_openings(hash, &roots, layer0_queries, proof_bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn iterator_query_derivation_reference(
        layer0_queries: &[u32],
        layer0_query_count: usize,
    ) -> Result<CircleLineQueryIndices, CircleLineMerkleError> {
        if layer0_queries.is_empty() {
            return Err(CircleLineMerkleError::EmptyQueries);
        }
        if let Some(&query) = layer0_queries
            .iter()
            .find(|&&query| query >= layer0_query_count as u32)
        {
            return Err(CircleLineMerkleError::QueryOutOfRange { query });
        }
        let mut layer0 = layer0_queries.to_vec();
        layer0.sort_unstable();
        layer0.dedup();
        let later = core::array::from_fn(|layer| {
            let mut indices = layer0
                .iter()
                .map(|query| query >> CIRCLE_LINE_QUERY_SHIFTS[layer])
                .collect::<Vec<_>>();
            indices.dedup();
            indices
        });
        Ok(CircleLineQueryIndices { layer0, later })
    }

    fn framed_from_indices(
        indices: &CircleLineQueryIndices,
        frontier_counts: [usize; 3],
    ) -> Vec<u8> {
        let mut bytes = Vec::new();
        for (layer, &frontier_count) in frontier_counts.iter().enumerate() {
            bytes.extend_from_slice(&(indices.later[layer].len() as u16).to_le_bytes());
            bytes.resize(
                bytes.len() + indices.later[layer].len() * CIRCLE_LINE_LEAF_BYTES,
                0,
            );
            bytes.extend_from_slice(&(frontier_count as u32).to_le_bytes());
            bytes.resize(bytes.len() + frontier_count * 32, 0);
        }
        bytes
    }

    fn framed(queries: &[u32], frontier_counts: [usize; 3]) -> Vec<u8> {
        let indices = derive_circle_line_query_indices(queries).unwrap();
        framed_from_indices(&indices, frontier_counts)
    }

    #[test]
    fn query_derivation_is_sorted_unique_and_pins_all_shifts() {
        let derived = derive_circle_line_query_indices(&[1_023, 0, 4, 1, 4, 16]).unwrap();
        assert_eq!(derived.layer0, [0, 1, 4, 16, 1_023]);
        assert_eq!(derived.later[0], [0, 1, 4, 255]);
        assert_eq!(derived.later[1], [0, 1, 63]);
        assert_eq!(derived.later[2], [0, 15]);
        assert_eq!(
            derive_circle_line_query_indices(&[]),
            Err(CircleLineMerkleError::EmptyQueries)
        );
        assert_eq!(
            derive_circle_line_query_indices(&[1_024]),
            Err(CircleLineMerkleError::QueryOutOfRange { query: 1_024 })
        );
    }

    #[test]
    fn indexed_query_derivation_matches_iterator_reference() {
        let mut state = 0x434f_4d50_4f4e_454eu64;
        for width in 0..=36usize {
            let mut queries = Vec::with_capacity(width);
            for _ in 0..width {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                queries.push(((state >> 32) as u32) & 1023);
            }
            assert_eq!(
                derive_circle_line_query_indices_for_count(&queries, 1024),
                iterator_query_derivation_reference(&queries, 1024),
                "width={width}",
            );
        }
        assert_eq!(
            derive_circle_line_query_indices_for_count(&[7, 1024, 3], 1024),
            iterator_query_derivation_reference(&[7, 1024, 3], 1024),
        );
    }

    #[test]
    fn sequential_parser_offsets_and_full_consumption_are_exact() {
        let queries = [1_023, 0, 4, 1, 4, 16];
        let bytes = framed(&queries, [1, 2, 3]);
        let parsed = parse_circle_line_openings(&bytes, &queries).unwrap();
        assert_eq!(
            parsed.layers[0].offsets,
            CircleLineLayerOffsets {
                record_start: 0,
                unique_count: 0,
                leaves: 2,
                frontier_count: 258,
                frontier: 262,
                record_end: 294,
            }
        );
        assert_eq!(
            parsed.layers[1].offsets,
            CircleLineLayerOffsets {
                record_start: 294,
                unique_count: 294,
                leaves: 296,
                frontier_count: 488,
                frontier: 492,
                record_end: 556,
            }
        );
        assert_eq!(
            parsed.layers[2].offsets,
            CircleLineLayerOffsets {
                record_start: 556,
                unique_count: 556,
                leaves: 558,
                frontier_count: 686,
                frontier: 690,
                record_end: 786,
            }
        );
        assert_eq!(parsed.end, 786);
        assert_eq!(parsed.layers[0].leaf(3).unwrap().len(), 64);
        assert!(parsed.layers[0].leaf(4).is_none());

        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(
            parse_circle_line_openings(&trailing, &queries),
            Err(CircleLineMerkleError::TrailingBytes {
                offset: 786,
                remaining: 1,
            })
        );
        assert_eq!(
            parse_circle_line_openings(&bytes[..bytes.len() - 1], &queries),
            Err(CircleLineMerkleError::UnexpectedEnd {
                layer: 3,
                offset: 690,
                needed: 96,
            })
        );
    }

    #[test]
    fn prederived_parser_matches_eager_derivation_on_random_geometries_and_corruptions() {
        let mut state = 0x5052_4544_4552_4956u64;
        for schedule in 0..32 {
            let geometry = if schedule & 1 == 0 {
                FIXED_CIRCLE_OPENING_GEOMETRY
            } else {
                RATE16_CIRCLE_OPENING_GEOMETRY
            };
            let bound = 1u32 << geometry.layer0_binary_depth;
            let mut queries = Vec::with_capacity(36);
            for _ in 0..36 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                queries.push(((state >> 32) as u32) & (bound - 1));
            }
            let indices =
                derive_circle_line_query_indices_for_count(&queries, bound as usize).unwrap();
            let frontier_counts = core::array::from_fn(|_| {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                (state as usize) & 7
            });
            let bytes = framed_from_indices(&indices, frontier_counts);
            let compare = |candidate: &[u8]| {
                assert_eq!(
                    parse_circle_line_openings_with_indices(candidate, &indices),
                    parse_circle_line_openings_for_geometry(candidate, &queries, geometry),
                    "schedule={schedule}",
                );
            };
            compare(&bytes);
            compare(&bytes[..bytes.len() - 1]);
            let mut trailing = bytes.clone();
            trailing.push(0xa5);
            compare(&trailing);
            let mut wrong_count = bytes.clone();
            wrong_count[0] ^= 1;
            compare(&wrong_count);
        }
    }
}
