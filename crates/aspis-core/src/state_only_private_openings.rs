//! Canonical salted Merkle openings for state-only profile 21.
//!
//! Query indices are transcript-derived and therefore are not serialized.
//! Each opened record is exactly `fixed_width_value || salt32`, followed by
//! one radix-4/binary-cap frontier. The leaf node is the output of
//! [`private_leaf_hash`](crate::state_only_private_merkle::private_leaf_hash)
//! itself; it is never wrapped in a second leaf hash.

use alloc::vec::Vec;

use crate::merkle::verify_radix4_binary_cap_prevalidated_in_place;
use crate::state_only_private_merkle::{
    private_leaf_hash_record, STATE_ONLY_PRIVATE_LEAF_SALT_BYTES,
};
use crate::HashFn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyPrivateOpeningError {
    EmptyOpening,
    InvalidDepth { depth: u32 },
    InvalidValueWidth { width: usize },
    CountOutOfRange { count: usize },
    CountMismatch { expected: usize, actual: usize },
    IndicesNotStrictlyIncreasing,
    LeafIndexOutOfRange { index: u32 },
    UnexpectedEnd { offset: usize, needed: usize },
    LengthOverflow,
    MerkleMismatch,
    TrailingBytes { offset: usize, remaining: usize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyPrivateOpeningOffsets {
    pub count: usize,
    pub records: usize,
    pub frontier_count: usize,
    pub frontier: usize,
    pub end: usize,
}

/// Zero-copy view over one authenticated opening section.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyPrivateOpening<'a> {
    pub count: usize,
    pub value_width: usize,
    pub records: &'a [u8],
    pub frontier: &'a [u8],
    pub offsets: StateOnlyPrivateOpeningOffsets,
}

impl<'a> StateOnlyPrivateOpening<'a> {
    pub fn record_width(&self) -> usize {
        self.value_width + STATE_ONLY_PRIVATE_LEAF_SALT_BYTES
    }

    pub fn record(&self, ordinal: usize) -> Option<&'a [u8]> {
        if ordinal >= self.count {
            return None;
        }
        let start = ordinal.checked_mul(self.record_width())?;
        self.records
            .get(start..start.checked_add(self.record_width())?)
    }

    pub fn value(&self, ordinal: usize) -> Option<&'a [u8]> {
        if ordinal >= self.count {
            return None;
        }
        let start = ordinal.checked_mul(self.record_width())?;
        self.records
            .get(start..start.checked_add(self.value_width)?)
    }

    pub fn salt(&self, ordinal: usize) -> Option<&'a [u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]> {
        if ordinal >= self.count {
            return None;
        }
        let start = ordinal
            .checked_mul(self.record_width())?
            .checked_add(self.value_width)?;
        self.records
            .get(start..start.checked_add(STATE_ONLY_PRIVATE_LEAF_SALT_BYTES)?)?
            .try_into()
            .ok()
    }
}

struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], StateOnlyPrivateOpeningError> {
        let end = self
            .position
            .checked_add(len)
            .ok_or(StateOnlyPrivateOpeningError::LengthOverflow)?;
        if end > self.bytes.len() {
            return Err(StateOnlyPrivateOpeningError::UnexpectedEnd {
                offset: self.position,
                needed: len,
            });
        }
        let result = &self.bytes[self.position..end];
        self.position = end;
        Ok(result)
    }

    fn u16(&mut self) -> Result<u16, StateOnlyPrivateOpeningError> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }

    fn u32(&mut self) -> Result<u32, StateOnlyPrivateOpeningError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
}

fn validate_shape(
    binary_depth: u32,
    value_width: usize,
    indices: &[u32],
) -> Result<(), StateOnlyPrivateOpeningError> {
    if binary_depth >= 32 {
        return Err(StateOnlyPrivateOpeningError::InvalidDepth {
            depth: binary_depth,
        });
    }
    if value_width == 0 {
        return Err(StateOnlyPrivateOpeningError::InvalidValueWidth { width: value_width });
    }
    if indices.is_empty() {
        return Err(StateOnlyPrivateOpeningError::EmptyOpening);
    }
    if indices.len() > u16::MAX as usize {
        return Err(StateOnlyPrivateOpeningError::CountOutOfRange {
            count: indices.len(),
        });
    }
    for pair in indices.windows(2) {
        if pair[0] >= pair[1] {
            return Err(StateOnlyPrivateOpeningError::IndicesNotStrictlyIncreasing);
        }
    }
    let leaf_count = 1u32 << binary_depth;
    if let Some(&index) = indices.iter().find(|&&index| index >= leaf_count) {
        return Err(StateOnlyPrivateOpeningError::LeafIndexOutOfRange { index });
    }
    Ok(())
}

fn checked_section_len(count: usize, width: usize) -> Result<usize, StateOnlyPrivateOpeningError> {
    count
        .checked_mul(width)
        .ok_or(StateOnlyPrivateOpeningError::LengthOverflow)
}

fn parse_private_opening_from_proof<'a>(
    proof_bytes: &'a [u8],
    expected_count: usize,
    value_width: usize,
) -> Result<(StateOnlyPrivateOpening<'a>, &'a [u8]), StateOnlyPrivateOpeningError> {
    let record_width = value_width
        .checked_add(STATE_ONLY_PRIVATE_LEAF_SALT_BYTES)
        .ok_or(StateOnlyPrivateOpeningError::LengthOverflow)?;
    let mut cursor = Cursor::new(proof_bytes);
    let count_offset = cursor.position;
    let actual_count = usize::from(cursor.u16()?);
    if actual_count != expected_count {
        return Err(StateOnlyPrivateOpeningError::CountMismatch {
            expected: expected_count,
            actual: actual_count,
        });
    }
    let records_offset = cursor.position;
    let records = cursor.take(checked_section_len(actual_count, record_width)?)?;
    let frontier_count_offset = cursor.position;
    let frontier_count = cursor.u32()? as usize;
    let frontier_offset = cursor.position;
    let frontier = cursor.take(checked_section_len(frontier_count, 32)?)?;
    let end = cursor.position;
    Ok((
        StateOnlyPrivateOpening {
            count: actual_count,
            value_width,
            records,
            frontier,
            offsets: StateOnlyPrivateOpeningOffsets {
                count: count_offset,
                records: records_offset,
                frontier_count: frontier_count_offset,
                frontier: frontier_offset,
                end,
            },
        },
        &proof_bytes[end..],
    ))
}

/// Parse and authenticate one private opening from the start of a larger
/// proof suffix, returning the unconsumed remainder.
#[allow(clippy::too_many_arguments)]
pub fn verify_state_only_private_opening_from_proof<'a>(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    tree_tag: u8,
    value_width: usize,
    expected_sorted_indices: &[u32],
    proof_bytes: &'a [u8],
) -> Result<(StateOnlyPrivateOpening<'a>, &'a [u8]), StateOnlyPrivateOpeningError> {
    validate_shape(binary_depth, value_width, expected_sorted_indices)?;
    let (opening, remainder) =
        parse_private_opening_from_proof(proof_bytes, expected_sorted_indices.len(), value_width)?;

    let mut level = Vec::with_capacity(opening.count);
    for (ordinal, &leaf_index) in expected_sorted_indices.iter().enumerate() {
        level.push((
            leaf_index,
            private_leaf_hash_record(hash, tree_tag, opening.record(ordinal).unwrap()),
        ));
    }
    let mut next = Vec::with_capacity(opening.count);
    if !verify_radix4_binary_cap_prevalidated_in_place(
        hash,
        root,
        binary_depth,
        opening.frontier,
        &mut level,
        &mut next,
    ) {
        return Err(StateOnlyPrivateOpeningError::MerkleMismatch);
    }
    Ok((opening, remainder))
}

/// Authenticate exactly one private opening and reject any trailing byte.
#[allow(clippy::too_many_arguments)]
pub fn verify_state_only_private_opening<'a>(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    tree_tag: u8,
    value_width: usize,
    expected_sorted_indices: &[u32],
    proof_bytes: &'a [u8],
) -> Result<StateOnlyPrivateOpening<'a>, StateOnlyPrivateOpeningError> {
    let (opening, remainder) = verify_state_only_private_opening_from_proof(
        hash,
        root,
        binary_depth,
        tree_tag,
        value_width,
        expected_sorted_indices,
        proof_bytes,
    )?;
    if !remainder.is_empty() {
        return Err(StateOnlyPrivateOpeningError::TrailingBytes {
            offset: opening.offsets.end,
            remaining: remainder.len(),
        });
    }
    Ok(opening)
}
