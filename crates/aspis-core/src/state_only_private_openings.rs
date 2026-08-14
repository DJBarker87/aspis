//! Canonical salted Merkle openings for state-only profile 21.
//!
//! Query indices are transcript-derived and therefore are not serialized.
//! Each opened record is exactly `fixed_width_value || salt32`, followed by
//! one radix-4/binary-cap frontier. The leaf node is the output of
//! [`private_leaf_hash`](crate::state_only_private_merkle::private_leaf_hash)
//! itself; it is never wrapped in a second leaf hash.

use alloc::vec::Vec;

use crate::merkle::{
    verify_radix4_binary_cap_prevalidated_in_place, verify_radix4_binary_cap_with_matched_topology,
    Radix4BinaryCapTopology,
};
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

/// Parse and authenticate one private opening while reusing an index-only
/// radix-4 topology and caller-owned hash scratch.  This is byte- and
/// hash-identical to [`verify_state_only_private_opening_from_proof`].
/// `radix_level` selects the exact `q >> (2 * radix_level)` suffix and is
/// checked against `expected_sorted_indices` before any proof is accepted.
#[allow(clippy::too_many_arguments)]
pub fn verify_state_only_private_opening_from_proof_with_topology<'a>(
    hash: HashFn,
    root: &[u8; 32],
    binary_depth: u32,
    tree_tag: u8,
    value_width: usize,
    expected_sorted_indices: &[u32],
    proof_bytes: &'a [u8],
    topology: &Radix4BinaryCapTopology,
    radix_level: usize,
    level: &mut Vec<[u8; 32]>,
    next: &mut Vec<[u8; 32]>,
) -> Result<(StateOnlyPrivateOpening<'a>, &'a [u8]), StateOnlyPrivateOpeningError> {
    // `matches_suffix` certifies the same non-empty, strictly increasing,
    // in-range index shape as `validate_shape`. Keep the explicit validator
    // on every mismatch (and on the two shape conditions not represented by
    // the topology) so malformed inputs retain their exact error semantics.
    let matched_topology =
        topology.matched_suffix(radix_level, binary_depth, expected_sorted_indices);
    if value_width == 0
        || expected_sorted_indices.len() > u16::MAX as usize
        || matched_topology.is_none()
    {
        validate_shape(binary_depth, value_width, expected_sorted_indices)?;
    }
    let (opening, remainder) =
        parse_private_opening_from_proof(proof_bytes, expected_sorted_indices.len(), value_width)?;

    level.clear();
    for record in opening.records.chunks_exact(opening.record_width()) {
        level.push(private_leaf_hash_record(hash, tree_tag, record));
    }
    let Some(matched_topology) = matched_topology else {
        return Err(StateOnlyPrivateOpeningError::MerkleMismatch);
    };
    if !verify_radix4_binary_cap_with_matched_topology(
        hash,
        root,
        opening.frontier,
        matched_topology,
        level,
        next,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::{node_hash, node_hash4};
    use alloc::vec;

    const TEST_DEPTH: u32 = 5;
    const TEST_TAG: u8 = 0x63;
    const TEST_VALUE_WIDTH: usize = 8;

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};

        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn test_record(index: u32) -> [u8; TEST_VALUE_WIDTH + STATE_ONLY_PRIVATE_LEAF_SALT_BYTES] {
        core::array::from_fn(|offset| {
            (index as u8)
                .wrapping_mul(37)
                .wrapping_add((offset as u8).wrapping_mul(19))
                .wrapping_add(11)
        })
    }

    fn test_tree() -> (Vec<Vec<[u8; 32]>>, Vec<[u8; 40]>) {
        let records = (0..1u32 << TEST_DEPTH).map(test_record).collect::<Vec<_>>();
        let leaves = records
            .iter()
            .map(|record| private_leaf_hash_record(test_hash, TEST_TAG, record))
            .collect::<Vec<_>>();
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let previous = levels.last().unwrap();
            let next = if previous.len() == 2 {
                vec![node_hash(test_hash, &previous[0], &previous[1])]
            } else {
                previous
                    .chunks_exact(4)
                    .map(|children| node_hash4(test_hash, children.try_into().unwrap()))
                    .collect()
            };
            levels.push(next);
        }
        (levels, records)
    }

    fn test_frontier(levels: &[Vec<[u8; 32]>], indices: &[u32]) -> Vec<[u8; 32]> {
        let mut frontier = Vec::new();
        let mut current = indices.to_vec();
        for level in &levels[..levels.len() - 1] {
            if level.len() == 2 {
                if current.len() == 1 {
                    frontier.push(level[(current[0] ^ 1) as usize]);
                }
                current = vec![0];
                continue;
            }
            let mut next = Vec::new();
            let mut position = 0usize;
            while position < current.len() {
                let parent = current[position] >> 2;
                let mut present = 0u8;
                while position < current.len() && current[position] >> 2 == parent {
                    present |= 1u8 << (current[position] & 3);
                    position += 1;
                }
                for slot in 0..4u32 {
                    if present & (1u8 << slot) == 0 {
                        frontier.push(level[(parent * 4 + slot) as usize]);
                    }
                }
                next.push(parent);
            }
            current = next;
        }
        frontier
    }

    fn test_proof(levels: &[Vec<[u8; 32]>], records: &[[u8; 40]], indices: &[u32]) -> Vec<u8> {
        let frontier = test_frontier(levels, indices);
        let mut proof = Vec::new();
        proof.extend_from_slice(&(indices.len() as u16).to_le_bytes());
        for &index in indices {
            proof.extend_from_slice(&records[index as usize]);
        }
        proof.extend_from_slice(&(frontier.len() as u32).to_le_bytes());
        for node in frontier {
            proof.extend_from_slice(&node);
        }
        proof
    }

    fn assert_topology_parity(
        root: &[u8; 32],
        indices: &[u32],
        proof: &[u8],
        topology: &Radix4BinaryCapTopology,
    ) {
        let eager = verify_state_only_private_opening_from_proof(
            test_hash,
            root,
            TEST_DEPTH,
            TEST_TAG,
            TEST_VALUE_WIDTH,
            indices,
            proof,
        );
        let mut level = Vec::new();
        let mut next = Vec::new();
        let planned = verify_state_only_private_opening_from_proof_with_topology(
            test_hash,
            root,
            TEST_DEPTH,
            TEST_TAG,
            TEST_VALUE_WIDTH,
            indices,
            proof,
            topology,
            0,
            &mut level,
            &mut next,
        );
        assert_eq!(planned, eager);
    }

    #[test]
    fn topology_opening_matches_eager_across_every_proof_byte_mutation() {
        let indices = [1u32, 2, 7, 13, 30];
        let (levels, records) = test_tree();
        let root = levels.last().unwrap()[0];
        let proof = test_proof(&levels, &records, &indices);
        let topology = Radix4BinaryCapTopology::new(TEST_DEPTH, &indices).unwrap();

        assert_topology_parity(&root, &indices, &proof, &topology);
        for offset in 0..proof.len() {
            let mut mutated = proof.clone();
            mutated[offset] ^= 0x80;
            assert_topology_parity(&root, &indices, &mutated, &topology);
        }
        for end in 0..proof.len() {
            assert_topology_parity(&root, &indices, &proof[..end], &topology);
        }

        let mut extra = proof.clone();
        extra.extend_from_slice(&[0xa5; 17]);
        assert_topology_parity(&root, &indices, &extra, &topology);

        let mut wrong_root = root;
        wrong_root[9] ^= 1;
        assert_topology_parity(&wrong_root, &indices, &proof, &topology);

        let different_indices = [1u32, 3, 7, 13, 30];
        assert_topology_parity(&root, &different_indices, &proof, &topology);
    }

    #[test]
    fn topology_opening_retains_exact_shape_errors() {
        let indices = [1u32, 2, 7, 13, 30];
        let topology = Radix4BinaryCapTopology::new(TEST_DEPTH, &indices).unwrap();
        let mut level = Vec::new();
        let mut next = Vec::new();
        let root = [0u8; 32];

        let mut compare = |depth, width, candidate: &[u32]| {
            let eager = verify_state_only_private_opening_from_proof(
                test_hash,
                &root,
                depth,
                TEST_TAG,
                width,
                candidate,
                &[],
            )
            .unwrap_err();
            let planned = verify_state_only_private_opening_from_proof_with_topology(
                test_hash,
                &root,
                depth,
                TEST_TAG,
                width,
                candidate,
                &[],
                &topology,
                0,
                &mut level,
                &mut next,
            )
            .unwrap_err();
            assert_eq!(planned, eager);
        };

        compare(32, TEST_VALUE_WIDTH, &indices);
        compare(TEST_DEPTH, 0, &indices);
        compare(TEST_DEPTH, TEST_VALUE_WIDTH, &[]);
        compare(TEST_DEPTH, TEST_VALUE_WIDTH, &[1, 1, 7, 13, 30]);
        compare(TEST_DEPTH, TEST_VALUE_WIDTH, &[2, 1, 7, 13, 30]);
        compare(TEST_DEPTH, TEST_VALUE_WIDTH, &[1, 2, 7, 13, 32]);
    }

    #[test]
    fn topology_opening_rejects_swapped_radix_four_frontier_children() {
        let indices = [1u32];
        let (levels, records) = test_tree();
        let root = levels.last().unwrap()[0];
        let mut proof = test_proof(&levels, &records, &indices);
        let topology = Radix4BinaryCapTopology::new(TEST_DEPTH, &indices).unwrap();

        // count || one record || frontier_count || frontier. With one active
        // slot, the first two frontier digests are slots 0 and 2 of the same
        // radix-four parent and therefore cannot be interchanged.
        let frontier_start = 2 + TEST_VALUE_WIDTH + STATE_ONLY_PRIVATE_LEAF_SALT_BYTES + 4;
        for offset in 0..32 {
            proof.swap(frontier_start + offset, frontier_start + 32 + offset);
        }
        let mut level = Vec::new();
        let mut next = Vec::new();
        assert!(verify_state_only_private_opening_from_proof_with_topology(
            test_hash,
            &root,
            TEST_DEPTH,
            TEST_TAG,
            TEST_VALUE_WIDTH,
            &indices,
            &proof,
            &topology,
            0,
            &mut level,
            &mut next,
        )
        .is_err());
    }

    #[test]
    fn topology_opening_rejects_the_wrong_odd_cap_side() {
        let honest_indices = [1u32];
        let opposite_cap_indices = [17u32];
        let (levels, records) = test_tree();
        let root = levels.last().unwrap()[0];
        let proof = test_proof(&levels, &records, &honest_indices);

        // At depth five, 1 and 17 have the same two radix-four slots but
        // opposite final binary-cap sides. The proof carries no index bytes;
        // orientation comes only from the matched public topology.
        let honest_topology = Radix4BinaryCapTopology::new(TEST_DEPTH, &honest_indices).unwrap();
        let opposite_topology =
            Radix4BinaryCapTopology::new(TEST_DEPTH, &opposite_cap_indices).unwrap();
        let mut level = Vec::new();
        let mut next = Vec::new();

        assert!(verify_state_only_private_opening_from_proof_with_topology(
            test_hash,
            &root,
            TEST_DEPTH,
            TEST_TAG,
            TEST_VALUE_WIDTH,
            &honest_indices,
            &proof,
            &honest_topology,
            0,
            &mut level,
            &mut next,
        )
        .is_ok());
        assert!(verify_state_only_private_opening_from_proof_with_topology(
            test_hash,
            &root,
            TEST_DEPTH,
            TEST_TAG,
            TEST_VALUE_WIDTH,
            &opposite_cap_indices,
            &proof,
            &opposite_topology,
            0,
            &mut level,
            &mut next,
        )
        .is_err());
    }
}
