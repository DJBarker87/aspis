//! Default-off canonical fixed-field byte-for-CU experiment for Tag-73.
//!
//! The selected proof packs 641 QM31 values into 9,936 bytes. This audit wire
//! carries the same values as 641 canonical 16-byte records (10,256 bytes), a
//! precise +320-byte proof-account trade. Roots, nonces, query records, salts,
//! and both Merkle frontiers are byte-for-byte unchanged.

use alloc::vec::Vec;

use crate::field::QM31;
use crate::state_only_spend_query::StateOnlySpendQueryPowers;
use crate::v6_onefold::{
    gamma_combine_v6_packed_layer0, validate_packed_m31, V6FixedFieldStream, V6WireError,
    V6_C1_LIMBS_PER_QUERY, V6_C1_PACKED_BYTES_PER_QUERY, V6_C2_LIMBS_PER_QUERY,
    V6_C2_PACKED_BYTES_PER_QUERY, V6_FIXED_PACKED_FIELD_BYTES, V6_FIXED_QM31_VALUES,
    V6_QUERY_COUNT, V6_WORK_NONCE_BYTES,
};
use crate::v7_merkle208::{
    private_leaf_hash_v7, verify_two_minimal_subtrees_v7_bytes, V7Digest, V7_C1_TREE_TAG,
    V7_C2_TREE_TAG,
};
use crate::v7_onefold::{
    V7CompactOneFoldWire, V7_COMPACT_DIGEST_BYTES, V7_COMPACT_FRONTIER_CAP_PER_TREE,
    V7_COMPACT_PRIVATE_SALT_BYTES, V7_COMPACT_QUERY_BYTES, V7_COMPACT_QUERY_SECTION_BYTES,
};
use crate::HashFn;

pub const V7_CANONICAL_FIXED_BYTES: usize = 16 * V6_FIXED_QM31_VALUES;
pub const V7_CANONICAL_FIXED_DELTA_BYTES: usize =
    V7_CANONICAL_FIXED_BYTES - V6_FIXED_PACKED_FIELD_BYTES;
pub const V7_CANONICAL_BODY_WITHOUT_FRONTIERS: usize = V7_CANONICAL_FIXED_BYTES
    + 2 * V7_COMPACT_DIGEST_BYTES
    + V6_WORK_NONCE_BYTES
    + V7_COMPACT_QUERY_SECTION_BYTES;

#[derive(Clone, Copy)]
pub(crate) struct V7CanonicalFixedFieldReader<'a> {
    bytes: &'a [u8],
    ordinal: usize,
}

impl<'a> V7CanonicalFixedFieldReader<'a> {
    fn new(bytes: &'a [u8]) -> Result<Self, V6WireError> {
        if bytes.len() != V7_CANONICAL_FIXED_BYTES {
            return Err(V6WireError::WrongLength);
        }
        Ok(Self { bytes, ordinal: 0 })
    }
}

impl V6FixedFieldStream for V7CanonicalFixedFieldReader<'_> {
    #[inline(always)]
    fn next_qm31(&mut self) -> Result<QM31, V6WireError> {
        if self.ordinal >= V6_FIXED_QM31_VALUES {
            return Err(V6WireError::WrongLength);
        }
        let start = 16 * self.ordinal;
        let value = QM31::from_le_bytes(&self.bytes[start..start + 16])
            .ok_or(V6WireError::NonCanonicalM31)?;
        self.ordinal += 1;
        Ok(value)
    }

    fn finish(self) -> Result<(), V6WireError> {
        if self.ordinal == V6_FIXED_QM31_VALUES {
            Ok(())
        } else {
            Err(V6WireError::WrongLength)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7CanonicalQueryRecord<'a> {
    pub c1_packed: &'a [u8],
    pub c2_packed: &'a [u8],
    pub salt: &'a [u8; V7_COMPACT_PRIVATE_SALT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7CanonicalOneFoldWire<'a> {
    pub fixed_fields: &'a [u8],
    pub c1_root: &'a V7Digest,
    pub c2_root: &'a V7Digest,
    pub work_nonces: &'a [u8; V6_WORK_NONCE_BYTES],
    query_section: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
}

impl<'a> V7CanonicalOneFoldWire<'a> {
    pub fn parse(bytes: &'a [u8], frontier_nodes: usize) -> Result<Self, V6WireError> {
        if frontier_nodes > V7_COMPACT_FRONTIER_CAP_PER_TREE {
            return Err(V6WireError::FrontierTooLarge);
        }
        let frontier_bytes = frontier_nodes
            .checked_mul(V7_COMPACT_DIGEST_BYTES)
            .ok_or(V6WireError::WrongLength)?;
        let expected = V7_CANONICAL_BODY_WITHOUT_FRONTIERS
            .checked_add(2 * frontier_bytes)
            .ok_or(V6WireError::WrongLength)?;
        if bytes.len() != expected {
            return Err(V6WireError::WrongLength);
        }
        let (fixed_fields, rest) = bytes.split_at(V7_CANONICAL_FIXED_BYTES);
        let (c1_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (c2_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (work_nonces, rest) = rest.split_at(V6_WORK_NONCE_BYTES);
        let (query_section, rest) = rest.split_at(V7_COMPACT_QUERY_SECTION_BYTES);
        let (c1_frontier, c2_frontier) = rest.split_at(frontier_bytes);
        for ordinal in 0..V6_QUERY_COUNT {
            let start = ordinal * V7_COMPACT_QUERY_BYTES;
            let c1_end = start + V6_C1_PACKED_BYTES_PER_QUERY;
            let c2_end = c1_end + V6_C2_PACKED_BYTES_PER_QUERY;
            validate_packed_m31(&query_section[start..c1_end], V6_C1_LIMBS_PER_QUERY)?;
            validate_packed_m31(&query_section[c1_end..c2_end], V6_C2_LIMBS_PER_QUERY)?;
        }
        // Canonicality is checked lazily by the one-pass transcript reader;
        // every one of the 641 records is consumed before acceptance.
        V7CanonicalFixedFieldReader::new(fixed_fields)?;
        Ok(Self {
            fixed_fields,
            c1_root: c1_root.try_into().map_err(|_| V6WireError::WrongLength)?,
            c2_root: c2_root.try_into().map_err(|_| V6WireError::WrongLength)?,
            work_nonces: work_nonces
                .try_into()
                .map_err(|_| V6WireError::WrongLength)?,
            query_section,
            c1_frontier,
            c2_frontier,
        })
    }

    pub(crate) fn fixed_reader(&self) -> Result<V7CanonicalFixedFieldReader<'a>, V6WireError> {
        V7CanonicalFixedFieldReader::new(self.fixed_fields)
    }

    pub fn query(&self, ordinal: usize) -> Option<V7CanonicalQueryRecord<'a>> {
        if ordinal >= V6_QUERY_COUNT {
            return None;
        }
        let start = ordinal * V7_COMPACT_QUERY_BYTES;
        let c1_end = start + V6_C1_PACKED_BYTES_PER_QUERY;
        let c2_end = c1_end + V6_C2_PACKED_BYTES_PER_QUERY;
        let end = c2_end + V7_COMPACT_PRIVATE_SALT_BYTES;
        Some(V7CanonicalQueryRecord {
            c1_packed: &self.query_section[start..c1_end],
            c2_packed: &self.query_section[c1_end..c2_end],
            salt: self.query_section[c2_end..end].try_into().ok()?,
        })
    }
}

pub fn verify_and_gamma_combine_v7_canonical_openings(
    hash: HashFn,
    wire: &V7CanonicalOneFoldWire<'_>,
    queries: [u32; V6_QUERY_COUNT],
    powers: &StateOnlySpendQueryPowers,
) -> Result<[[QM31; 4]; V6_QUERY_COUNT], V6WireError> {
    let mut order: [(u32, usize); V6_QUERY_COUNT] =
        core::array::from_fn(|ordinal| (queries[ordinal], ordinal));
    order.sort_unstable_by_key(|entry| entry.0);
    if order[V6_QUERY_COUNT - 1].0 >= 1 << 18 || order.windows(2).any(|pair| pair[0].0 == pair[1].0)
    {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    let mut combined = [[QM31::ZERO; 4]; V6_QUERY_COUNT];
    let mut entries = Vec::with_capacity(V6_QUERY_COUNT);
    for (query, ordinal) in order {
        let record = wire
            .query(ordinal)
            .ok_or(V6WireError::InvalidQuerySchedule)?;
        combined[ordinal] =
            gamma_combine_v6_packed_layer0(record.c1_packed, record.c2_packed, powers)?;
        entries.push((
            query,
            private_leaf_hash_v7(hash, V7_C1_TREE_TAG, record.c1_packed, record.salt),
            private_leaf_hash_v7(hash, V7_C2_TREE_TAG, record.c2_packed, record.salt),
        ));
    }
    let mut level = Vec::with_capacity(V6_QUERY_COUNT);
    let mut next = Vec::with_capacity(V6_QUERY_COUNT);
    if !verify_two_minimal_subtrees_v7_bytes(
        hash,
        (wire.c1_root, wire.c2_root),
        18,
        &entries,
        (wire.c1_frontier, wire.c2_frontier),
        &mut level,
        &mut next,
    ) {
        return Err(V6WireError::MerkleMismatch);
    }
    Ok(combined)
}

/// Convert only the selected proof's fixed section; the authenticated tail is
/// copied byte-for-byte. Used by host harnesses to build a fair paired input.
pub fn transcode_tag73_to_canonical_fixed(
    proof: &[u8],
    frontier_nodes: usize,
) -> Result<Vec<u8>, V6WireError> {
    let wire = V7CompactOneFoldWire::parse(proof, frontier_nodes)?;
    let mut reader = crate::v6_onefold::V6FixedFieldReader::new(wire.fixed_fields_packed)?;
    let mut output = Vec::with_capacity(proof.len() + V7_CANONICAL_FIXED_DELTA_BYTES);
    for _ in 0..V6_FIXED_QM31_VALUES {
        let value = reader.next_qm31()?;
        let start = output.len();
        output.resize(start + 16, 0);
        value.write_le_bytes(&mut output[start..start + 16]);
    }
    reader.finish()?;
    output.extend_from_slice(&proof[V6_FIXED_PACKED_FIELD_BYTES..]);
    V7CanonicalOneFoldWire::parse(&output, frontier_nodes)?;
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_fixed_delta_is_exactly_320_bytes() {
        assert_eq!(V6_FIXED_PACKED_FIELD_BYTES, 9_936);
        assert_eq!(V7_CANONICAL_FIXED_BYTES, 10_256);
        assert_eq!(V7_CANONICAL_FIXED_DELTA_BYTES, 320);
    }
}
