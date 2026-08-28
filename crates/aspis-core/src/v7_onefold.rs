//! Selected V7 one-fold wire.
//!
//! V7 retains the frozen 26+3 arithmetic and random-linear q16 equality from
//! V6. It sends each complete C2 fibre, keeps 256-bit private salts, and uses
//! 208-bit truncated-SHA-256 Merkle digests. The 104-bit generic collision
//! strength remains above the 100-bit theorem target while the exact maximum
//! proof body stays below 30 KiB.

use alloc::vec::Vec;

use crate::field::QM31;
use crate::state_only_spend_query::StateOnlySpendQueryPowers;
use crate::transcript::{label, Transcript};
use crate::v6_onefold::{
    binary_frontier_nodes, gamma_combine_v6_packed_layer0, validate_packed_m31, V6WireError,
    V6_C1_LIMBS_PER_QUERY, V6_C1_PACKED_BYTES_PER_QUERY, V6_C2_LIMBS_PER_QUERY,
    V6_C2_PACKED_BYTES_PER_QUERY, V6_FIXED_M31_LIMBS, V6_FIXED_PACKED_FIELD_BYTES, V6_QUERY_COUNT,
    V6_WORK_NONCE_BYTES,
};
use crate::v7_merkle208::{
    private_leaf_hash_v7, verify_two_minimal_subtrees_v7_bytes, V7Digest, V7_C1_TREE_TAG,
    V7_C2_TREE_TAG,
};
use crate::HashFn;

pub const V7_COMPACT_DIGEST_BYTES: usize = 26;
pub const V7_COMPACT_DIGEST_BITS: usize = 8 * V7_COMPACT_DIGEST_BYTES;
pub const V7_COMPACT_CLASSICAL_COLLISION_BITS: usize = V7_COMPACT_DIGEST_BITS / 2;
pub const V7_COMPACT_FRONTIER_CAP_PER_TREE: usize = 203;
pub const V7_COMPACT_QUERY_CANDIDATES: usize = 64;
pub const V7_COMPACT_SELECTOR_STREAMS: usize = 1;
pub const V7_COMPACT_BATCH_WORK_BITS: u8 = 35;
pub const V7_COMPACT_FOLD_WORK_BITS: u8 = 31;
pub const V7_COMPACT_FINAL_WORK_BITS: u8 = 34;

/// Byte-level V7 profile record absorbed before deployment, statement, roots,
/// or challenges. It commits the complete-C2 wire and 208-bit Merkle profile.
pub const V7_COMPACT_PROFILE_BINDING: [u8; 32] = [
    b'A', b'V', b'7', b'O', b'F', b'0', b'0', b'1', // magic/version
    26, 3, 10, 16, 0xcb, 0x00, 26, 32, // widths, q, cap203, digest/salt bytes
    27, 4, 6, 35, 31, 34, 0x71, 0xf1, // transcript widths, work, tree tags
    0x81, 0x02, 8, 20, 18, 1, 64, 1, // 641 fields, logs, stream/cap, full-C2 rev
];

pub const V7_COMPACT_C2_QM31_PER_QUERY: usize = 12;
pub const V7_COMPACT_C2_LIMBS_PER_QUERY: usize = V6_C2_LIMBS_PER_QUERY;
pub const V7_COMPACT_PRIVATE_SALT_BYTES: usize = 32;
pub const V7_COMPACT_PRODUCTION_LIMIT_BYTES: usize = 30 * 1024;
pub const V7_COMPACT_C1_BYTES_PER_QUERY: usize = V6_C1_PACKED_BYTES_PER_QUERY;
pub const V7_COMPACT_C2_BYTES_PER_QUERY: usize = V6_C2_PACKED_BYTES_PER_QUERY;
pub const V7_COMPACT_QUERY_BYTES: usize =
    V7_COMPACT_C1_BYTES_PER_QUERY + V7_COMPACT_C2_BYTES_PER_QUERY + V7_COMPACT_PRIVATE_SALT_BYTES;
pub const V7_COMPACT_QUERY_SECTION_BYTES: usize = V6_QUERY_COUNT * V7_COMPACT_QUERY_BYTES;
pub const V7_COMPACT_ROOT_BYTES: usize = 2 * V7_COMPACT_DIGEST_BYTES;
pub const V7_COMPACT_BODY_WITHOUT_FRONTIERS: usize = V6_FIXED_PACKED_FIELD_BYTES
    + V7_COMPACT_ROOT_BYTES
    + V6_WORK_NONCE_BYTES
    + V7_COMPACT_QUERY_SECTION_BYTES;
pub const V7_COMPACT_MAX_BODY_BYTES: usize = V7_COMPACT_BODY_WITHOUT_FRONTIERS
    + 2 * V7_COMPACT_FRONTIER_CAP_PER_TREE * V7_COMPACT_DIGEST_BYTES;
pub const V7_COMPACT_BODY_HEADROOM_BYTES: usize =
    V7_COMPACT_PRODUCTION_LIMIT_BYTES - V7_COMPACT_MAX_BODY_BYTES;

#[derive(Clone)]
pub struct V7CompactQuerySchedule {
    pub queries: [u32; V6_QUERY_COUNT],
    pub counter: u8,
    pub frontier_nodes: usize,
    pub transcript_state: [u8; 32],
    pub accepted_transcript: Transcript,
}

/// Derive the first cap-203 schedule in the sole V7 counter stream.
pub fn derive_first_v7_compact_queries(
    transcript: &Transcript,
) -> Result<V7CompactQuerySchedule, V6WireError> {
    for counter in 0..V7_COMPACT_QUERY_CANDIDATES as u8 {
        let mut candidate_transcript = transcript.clone();
        candidate_transcript.absorb(label::V7_QUERY_CANDIDATE, &[counter]);
        let candidate = candidate_transcript
            .challenge_queries_without_replacement(V6_QUERY_COUNT, 1 << 18, 64)
            .map_err(|_| V6WireError::InvalidQuerySchedule)?;
        let queries: [u32; V6_QUERY_COUNT] = candidate
            .try_into()
            .map_err(|_| V6WireError::InvalidQuerySchedule)?;
        let frontier_nodes = binary_frontier_nodes(queries, 18)?;
        if frontier_nodes <= V7_COMPACT_FRONTIER_CAP_PER_TREE {
            return Ok(V7CompactQuerySchedule {
                queries,
                counter,
                frontier_nodes,
                transcript_state: candidate_transcript.diagnostic_state(),
                accepted_transcript: candidate_transcript,
            });
        }
    }
    Err(V6WireError::InvalidQuerySchedule)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7CompactQueryRecord<'a> {
    pub c1_packed: &'a [u8],
    pub c2_packed: &'a [u8],
    pub salt: &'a [u8; V7_COMPACT_PRIVATE_SALT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7CompactOneFoldWire<'a> {
    pub fixed_fields_packed: &'a [u8],
    pub c1_root: &'a V7Digest,
    pub c2_root: &'a V7Digest,
    pub work_nonces: &'a [u8; V6_WORK_NONCE_BYTES],
    query_section: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
}

impl<'a> V7CompactOneFoldWire<'a> {
    pub fn parse(bytes: &'a [u8], frontier_nodes: usize) -> Result<Self, V6WireError> {
        let wire = Self::parse_deferred_canonicality(bytes, frontier_nodes)?;
        validate_packed_m31(wire.fixed_fields_packed, V6_FIXED_M31_LIMBS)?;
        for ordinal in 0..V6_QUERY_COUNT {
            let query = wire
                .query(ordinal)
                .ok_or(V6WireError::InvalidQuerySchedule)?;
            validate_packed_m31(query.c1_packed, V6_C1_LIMBS_PER_QUERY)?;
            validate_packed_m31(query.c2_packed, V7_COMPACT_C2_LIMBS_PER_QUERY)?;
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
        let expected = V7_COMPACT_BODY_WITHOUT_FRONTIERS
            .checked_add(2 * frontier_bytes)
            .ok_or(V6WireError::WrongLength)?;
        if bytes.len() != expected || bytes.len() > V7_COMPACT_PRODUCTION_LIMIT_BYTES {
            return Err(V6WireError::WrongLength);
        }
        let (fixed_fields_packed, rest) = bytes.split_at(V6_FIXED_PACKED_FIELD_BYTES);
        if fixed_fields_packed.last().copied().unwrap_or_default() & 0xf0 != 0 {
            return Err(V6WireError::NonCanonicalM31);
        }
        let (c1_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (c2_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (work_nonces, rest) = rest.split_at(V6_WORK_NONCE_BYTES);
        let (query_section, rest) = rest.split_at(V7_COMPACT_QUERY_SECTION_BYTES);
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

    pub fn query(&self, ordinal: usize) -> Option<V7CompactQueryRecord<'a>> {
        if ordinal >= V6_QUERY_COUNT {
            return None;
        }
        let start = ordinal * V7_COMPACT_QUERY_BYTES;
        let c1_end = start + V7_COMPACT_C1_BYTES_PER_QUERY;
        let c2_end = c1_end + V7_COMPACT_C2_BYTES_PER_QUERY;
        let end = c2_end + V7_COMPACT_PRIVATE_SALT_BYTES;
        Some(V7CompactQueryRecord {
            c1_packed: &self.query_section[start..c1_end],
            c2_packed: &self.query_section[c1_end..c2_end],
            salt: self.query_section[c2_end..end].try_into().ok()?,
        })
    }
}

/// Authenticate and gamma-combine every complete V7 query opening.
pub fn verify_and_gamma_combine_v7_openings(
    hash: HashFn,
    wire: &V7CompactOneFoldWire<'_>,
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

/// Production-inactive checkpoints for the local V7 opening profiler.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V7OpeningDiagnosticPhase {
    GammaCombined,
    LeavesHashed,
    MerkleAuthenticated,
}

/// Diagnostic twin of [`verify_and_gamma_combine_v7_openings`].
///
/// This deliberately separates the packed gamma dot, private-leaf hashes and
/// paired minimal-subtree walk so the local SBF profiler can attribute the
/// fused opening cost.  It consumes the same bytes and applies the same
/// canonicality, typed SHA-256 and root checks; production callers retain the
/// fused one-pass wrapper above.
#[inline(never)]
pub fn verify_and_gamma_combine_v7_openings_with_diagnostic_trace<Trace>(
    hash: HashFn,
    wire: &V7CompactOneFoldWire<'_>,
    queries: [u32; V6_QUERY_COUNT],
    powers: &StateOnlySpendQueryPowers,
    mut trace: Trace,
) -> Result<[[QM31; 4]; V6_QUERY_COUNT], V6WireError>
where
    Trace: FnMut(V7OpeningDiagnosticPhase),
{
    let mut order: [(u32, usize); V6_QUERY_COUNT] =
        core::array::from_fn(|ordinal| (queries[ordinal], ordinal));
    order.sort_unstable_by_key(|entry| entry.0);
    if order[V6_QUERY_COUNT - 1].0 >= 1 << 18 || order.windows(2).any(|pair| pair[0].0 == pair[1].0)
    {
        return Err(V6WireError::InvalidQuerySchedule);
    }

    let mut combined = [[QM31::ZERO; 4]; V6_QUERY_COUNT];
    for (_, ordinal) in order {
        let record = wire
            .query(ordinal)
            .ok_or(V6WireError::InvalidQuerySchedule)?;
        combined[ordinal] =
            gamma_combine_v6_packed_layer0(record.c1_packed, record.c2_packed, powers)?;
    }
    trace(V7OpeningDiagnosticPhase::GammaCombined);

    let mut entries = Vec::with_capacity(V6_QUERY_COUNT);
    for (query, ordinal) in order {
        let record = wire
            .query(ordinal)
            .ok_or(V6WireError::InvalidQuerySchedule)?;
        entries.push((
            query,
            private_leaf_hash_v7(hash, V7_C1_TREE_TAG, record.c1_packed, record.salt),
            private_leaf_hash_v7(hash, V7_C2_TREE_TAG, record.c2_packed, record.salt),
        ));
    }
    trace(V7OpeningDiagnosticPhase::LeavesHashed);

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
    trace(V7OpeningDiagnosticPhase::MerkleAuthenticated);
    Ok(combined)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn exact_v7_wire_budget_is_below_thirty_kib() {
        assert_eq!(&V7_COMPACT_PROFILE_BINDING[..8], b"AV7OF001");
        assert_eq!(V7_COMPACT_DIGEST_BITS, 208);
        assert_eq!(V7_COMPACT_CLASSICAL_COLLISION_BITS, 104);
        assert_eq!(V7_COMPACT_C2_BYTES_PER_QUERY, 186);
        assert_eq!(V7_COMPACT_QUERY_BYTES, 621);
        assert_eq!(V7_COMPACT_BODY_WITHOUT_FRONTIERS, 19_948);
        assert_eq!(V7_COMPACT_MAX_BODY_BYTES, 30_504);
        assert_eq!(V7_COMPACT_BODY_HEADROOM_BYTES, 216);
    }

    #[test]
    fn parser_freezes_full_c2_cap203_layout() {
        let body = vec![0u8; V7_COMPACT_MAX_BODY_BYTES];
        let wire = V7CompactOneFoldWire::parse(&body, V7_COMPACT_FRONTIER_CAP_PER_TREE).unwrap();
        assert_eq!(wire.c1_frontier.len(), 203 * 26);
        assert_eq!(wire.c2_frontier.len(), 203 * 26);
        assert_eq!(wire.query(0).unwrap().c1_packed.len(), 403);
        assert_eq!(wire.query(0).unwrap().c2_packed.len(), 186);
        assert_eq!(wire.query(15).unwrap().salt.len(), 32);
    }
}
