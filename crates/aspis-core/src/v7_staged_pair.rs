//! Production-inactive wire slice for the conservative staged Tag-73 pair
//! profile.
//!
//! This module freezes only the changed byte grammar. It deliberately does
//! not route a production instruction or pretend that the existing 29-column
//! terminal verifies the new late append lanes. A future verifier must consume
//! this exact wire through the seven-lane terminal and query authenticator.

use crate::v6_onefold::{validate_packed_m31, V6WireError, V6_QUERY_COUNT, V6_WORK_NONCE_BYTES};
use crate::v7_onefold::{
    V7_COMPACT_C1_BYTES_PER_QUERY, V7_COMPACT_DIGEST_BYTES, V7_COMPACT_FRONTIER_CAP_PER_TREE,
    V7_COMPACT_PRIVATE_SALT_BYTES,
};

pub const V7_STAGED_PAIR_C1_COLUMNS: usize = 26;
pub const V7_STAGED_PAIR_C2_COLUMNS: usize = 7;
pub const V7_STAGED_PAIR_LATE_C2_COLUMNS: usize = 4;
pub const V7_STAGED_PAIR_FIXED_QM31_VALUES: usize = 653;
pub const V7_STAGED_PAIR_FIXED_M31_LIMBS: usize = 4 * V7_STAGED_PAIR_FIXED_QM31_VALUES;
pub const V7_STAGED_PAIR_FIXED_FIELD_BYTES: usize =
    packed_m31_bytes(V7_STAGED_PAIR_FIXED_M31_LIMBS);
pub const V7_STAGED_PAIR_C2_LIMBS_PER_QUERY: usize = 4 * 4 * V7_STAGED_PAIR_C2_COLUMNS;
pub const V7_STAGED_PAIR_C2_BYTES_PER_QUERY: usize =
    packed_m31_bytes(V7_STAGED_PAIR_C2_LIMBS_PER_QUERY);
pub const V7_STAGED_PAIR_QUERY_BYTES: usize = V7_COMPACT_C1_BYTES_PER_QUERY
    + V7_STAGED_PAIR_C2_BYTES_PER_QUERY
    + V7_COMPACT_PRIVATE_SALT_BYTES;
pub const V7_STAGED_PAIR_QUERY_SECTION_BYTES: usize = V6_QUERY_COUNT * V7_STAGED_PAIR_QUERY_BYTES;
pub const V7_STAGED_PAIR_ROOT_BYTES: usize = 2 * V7_COMPACT_DIGEST_BYTES;
pub const V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS: usize = V7_STAGED_PAIR_FIXED_FIELD_BYTES
    + V7_STAGED_PAIR_ROOT_BYTES
    + V6_WORK_NONCE_BYTES
    + V7_STAGED_PAIR_QUERY_SECTION_BYTES;
pub const V7_STAGED_PAIR_MAX_BODY_BYTES: usize = V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS
    + 2 * V7_COMPACT_FRONTIER_CAP_PER_TREE * V7_COMPACT_DIGEST_BYTES;

/// Fresh profile identifier. It is intentionally distinct from both the
/// frozen 30,504-byte Tag-73 profile and the rejected stable-pair transport.
pub const V7_STAGED_PAIR_PROFILE_BINDING: [u8; 32] = [
    b'A', b'V', b'7', b'S', b'P', b'0', b'0', b'1', // magic/version
    26, 7, 10, 16, 0xcb, 0x00, 26, 32, // widths, q, cap203, digest/salt bytes
    27, 4, 6, 35, 31, 34, 0x71, 0xf1, // degree, fibre, work, typed tree tags
    0x8d, 0x02, 8, 20, 18, 1, 64, 2, // 653 fields, logs, stream/cap, staged rev
];

const fn packed_m31_bytes(limbs: usize) -> usize {
    (limbs * 31 + 7) / 8
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7StagedPairQueryRecord<'a> {
    pub c1_packed: &'a [u8],
    /// Complete helper-major `H1[4] || G[4] || D[4] || late[4][4]` fibre.
    pub c2_packed: &'a [u8],
    pub salt: &'a [u8; V7_COMPACT_PRIVATE_SALT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7StagedPairOneFoldWire<'a> {
    pub fixed_fields_packed: &'a [u8],
    pub c1_root: &'a [u8; V7_COMPACT_DIGEST_BYTES],
    pub c2_root: &'a [u8; V7_COMPACT_DIGEST_BYTES],
    pub work_nonces: &'a [u8; V6_WORK_NONCE_BYTES],
    query_section: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
}

impl<'a> V7StagedPairOneFoldWire<'a> {
    pub fn parse(bytes: &'a [u8], frontier_nodes: usize) -> Result<Self, V6WireError> {
        let wire = Self::parse_deferred_canonicality(bytes, frontier_nodes)?;
        validate_packed_m31(wire.fixed_fields_packed, V7_STAGED_PAIR_FIXED_M31_LIMBS)?;
        for ordinal in 0..V6_QUERY_COUNT {
            let query = wire
                .query(ordinal)
                .ok_or(V6WireError::InvalidQuerySchedule)?;
            validate_packed_m31(query.c1_packed, 4 * V7_STAGED_PAIR_C1_COLUMNS)?;
            validate_packed_m31(query.c2_packed, V7_STAGED_PAIR_C2_LIMBS_PER_QUERY)?;
        }
        Ok(wire)
    }

    pub fn parse_deferred_canonicality(
        bytes: &'a [u8],
        frontier_nodes: usize,
    ) -> Result<Self, V6WireError> {
        if frontier_nodes > V7_COMPACT_FRONTIER_CAP_PER_TREE {
            return Err(V6WireError::FrontierTooLarge);
        }
        let frontier_bytes = frontier_nodes
            .checked_mul(V7_COMPACT_DIGEST_BYTES)
            .ok_or(V6WireError::WrongLength)?;
        let expected = V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS
            .checked_add(2 * frontier_bytes)
            .ok_or(V6WireError::WrongLength)?;
        if bytes.len() != expected || bytes.len() > V7_STAGED_PAIR_MAX_BODY_BYTES {
            return Err(V6WireError::WrongLength);
        }

        let (fixed_fields_packed, rest) = bytes.split_at(V7_STAGED_PAIR_FIXED_FIELD_BYTES);
        // 2,612 limbs occupy 80,972 bits, leaving the upper four bits zero.
        if fixed_fields_packed.last().copied().unwrap_or_default() & 0xf0 != 0 {
            return Err(V6WireError::NonCanonicalM31);
        }
        let (c1_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (c2_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (work_nonces, rest) = rest.split_at(V6_WORK_NONCE_BYTES);
        let (query_section, rest) = rest.split_at(V7_STAGED_PAIR_QUERY_SECTION_BYTES);
        let (c1_frontier, c2_frontier) = rest.split_at(frontier_bytes);
        Ok(Self {
            fixed_fields_packed,
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

    pub fn query(&self, ordinal: usize) -> Option<V7StagedPairQueryRecord<'a>> {
        if ordinal >= V6_QUERY_COUNT {
            return None;
        }
        let start = ordinal * V7_STAGED_PAIR_QUERY_BYTES;
        let c1_end = start + V7_COMPACT_C1_BYTES_PER_QUERY;
        let c2_end = c1_end + V7_STAGED_PAIR_C2_BYTES_PER_QUERY;
        let end = c2_end + V7_COMPACT_PRIVATE_SALT_BYTES;
        Some(V7StagedPairQueryRecord {
            c1_packed: &self.query_section[start..c1_end],
            c2_packed: &self.query_section[c1_end..c2_end],
            salt: self.query_section[c2_end..end].try_into().ok()?,
        })
    }
}

const _: () = assert!(V7_STAGED_PAIR_FIXED_FIELD_BYTES == 10_122);
const _: () = assert!(V7_COMPACT_C1_BYTES_PER_QUERY == 403);
const _: () = assert!(V7_STAGED_PAIR_C2_BYTES_PER_QUERY == 434);
const _: () = assert!(V7_STAGED_PAIR_QUERY_BYTES == 869);
const _: () = assert!(V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS == 24_102);
const _: () = assert!(V7_STAGED_PAIR_MAX_BODY_BYTES == 34_658);

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn exact_staged_pair_wire_budget_and_sections_are_frozen() {
        assert_eq!(&V7_STAGED_PAIR_PROFILE_BINDING[..8], b"AV7SP001");
        assert_eq!(V7_STAGED_PAIR_C2_COLUMNS, 7);
        assert_eq!(V7_STAGED_PAIR_LATE_C2_COLUMNS, 4);
        assert_eq!(V7_STAGED_PAIR_FIXED_QM31_VALUES, 653);
        assert_eq!(V7_STAGED_PAIR_FIXED_FIELD_BYTES, 10_122);
        assert_eq!(V7_STAGED_PAIR_C2_BYTES_PER_QUERY, 434);
        assert_eq!(V7_STAGED_PAIR_QUERY_BYTES, 869);
        assert_eq!(V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS, 24_102);
        assert_eq!(V7_STAGED_PAIR_MAX_BODY_BYTES, 34_658);

        let body = vec![0u8; V7_STAGED_PAIR_MAX_BODY_BYTES];
        let wire = V7StagedPairOneFoldWire::parse(&body, V7_COMPACT_FRONTIER_CAP_PER_TREE).unwrap();
        assert_eq!(wire.fixed_fields_packed.len(), 10_122);
        assert_eq!(wire.query(0).unwrap().c1_packed.len(), 403);
        assert_eq!(wire.query(0).unwrap().c2_packed.len(), 434);
        assert_eq!(wire.query(15).unwrap().salt.len(), 32);
        assert_eq!(wire.c1_frontier.len(), 203 * 26);
        assert_eq!(wire.c2_frontier.len(), 203 * 26);
    }

    #[test]
    fn staged_pair_parser_rejects_wrong_length_frontier_and_padding() {
        let mut body = vec![0u8; V7_STAGED_PAIR_MAX_BODY_BYTES];
        assert_eq!(
            V7StagedPairOneFoldWire::parse(&body[..body.len() - 1], 203),
            Err(V6WireError::WrongLength)
        );
        assert_eq!(
            V7StagedPairOneFoldWire::parse(&body, 204),
            Err(V6WireError::FrontierTooLarge)
        );
        body[V7_STAGED_PAIR_FIXED_FIELD_BYTES - 1] = 0x10;
        assert_eq!(
            V7StagedPairOneFoldWire::parse(&body, 203),
            Err(V6WireError::NonCanonicalM31)
        );
    }
}
