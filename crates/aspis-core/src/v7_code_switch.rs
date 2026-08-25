//! Exact host-side byte and frontier census for the V7 code-switch gate.
//!
//! This module deliberately contains no verifier entry point.  It freezes the
//! information-theoretic row widths and the binary-Merkle geometry which must
//! clear the host gate before any SBF implementation is authorized.

use crate::v6_onefold::{
    binary_frontier_nodes, V6WireError, V6_FIXED_PACKED_FIELD_BYTES, V6_QUERY_COUNT,
};

pub const V7_DIGEST_BYTES: usize = 32;
pub const V7_WORK_NONCE_BYTES: usize = 3 * 8;
pub const V7_ROOT_COUNT: usize = 3;
pub const V7_SOURCE_C1_LIMBS_PER_ROW: usize = 26;
pub const V7_SOURCE_C2_LIMBS_PER_ROW: usize = 3 * 4;
pub const V7_TARGET_G_LIMBS_PER_FIBER: usize = 4 * 4;
pub const V7_SHARED_SALT_BYTES: usize = 32;
pub const V7_TARGET_TREE_DEPTH: u8 = 18;
pub const V7_FULL_SOURCE_TREE_DEPTH: u8 = 20;
pub const V7_HALF_SOURCE_TREE_DEPTH: u8 = 19;
pub const V7_REFERENCE_LIMIT_BYTES: usize = 34 * 1024;
pub const V7_PRODUCTION_LIMIT_BYTES: usize = 30 * 1024;
pub const V7_HARD_LIMIT_BYTES: usize = 32 * 1024;

pub const fn packed_m31_bytes(limbs: usize) -> usize {
    (31 * limbs + 7) / 8
}

pub const V7_SOURCE_C1_BYTES_PER_QUERY: usize = packed_m31_bytes(V7_SOURCE_C1_LIMBS_PER_ROW);
pub const V7_SOURCE_C2_BYTES_PER_QUERY: usize = packed_m31_bytes(V7_SOURCE_C2_LIMBS_PER_ROW);
pub const V7_TARGET_G_BYTES_PER_QUERY: usize = packed_m31_bytes(V7_TARGET_G_LIMBS_PER_FIBER);
pub const V7_DIRECT_QUERY_BYTES: usize = V7_SOURCE_C1_BYTES_PER_QUERY
    + V7_SOURCE_C2_BYTES_PER_QUERY
    + V7_TARGET_G_BYTES_PER_QUERY
    + V7_SHARED_SALT_BYTES;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7CodeSwitchCensus {
    pub target_frontier_nodes: usize,
    pub source_c1_frontier_nodes: usize,
    pub source_c2_frontier_nodes: usize,
    pub body_bytes: usize,
}

impl V7CodeSwitchCensus {
    pub const fn total_frontier_nodes(self) -> usize {
        self.target_frontier_nodes + self.source_c1_frontier_nodes + self.source_c2_frontier_nodes
    }

    pub const fn fits_reference(self) -> bool {
        self.body_bytes <= V7_REFERENCE_LIMIT_BYTES
    }

    pub const fn fits_production(self) -> bool {
        self.body_bytes <= V7_PRODUCTION_LIMIT_BYTES
    }

    pub const fn fits_hard_limit(self) -> bool {
        self.body_bytes <= V7_HARD_LIMIT_BYTES
    }
}

const fn body_bytes(frontier_nodes: usize) -> usize {
    V6_FIXED_PACKED_FIELD_BYTES
        + V7_ROOT_COUNT * V7_DIGEST_BYTES
        + V7_WORK_NONCE_BYTES
        + V6_QUERY_COUNT * V7_DIRECT_QUERY_BYTES
        + frontier_nodes * V7_DIGEST_BYTES
}

fn mapped_source_indices(
    queries: [u32; V6_QUERY_COUNT],
    slots: [u8; V6_QUERY_COUNT],
    slot_bits: u8,
) -> Result<[u32; V6_QUERY_COUNT], V6WireError> {
    let slot_limit = 1u8
        .checked_shl(u32::from(slot_bits))
        .ok_or(V6WireError::InvalidQuerySchedule)?;
    let mut output = [0u32; V6_QUERY_COUNT];
    for index in 0..V6_QUERY_COUNT {
        if slots[index] >= slot_limit {
            return Err(V6WireError::InvalidQuerySchedule);
        }
        output[index] = queries[index]
            .checked_shl(u32::from(slot_bits))
            .and_then(|query| query.checked_add(u32::from(slots[index])))
            .ok_or(V6WireError::InvalidQuerySchedule)?;
    }
    Ok(output)
}

/// Census the literal full-domain V7 layout.  Each source tree has `2^20`
/// row leaves and the target tree has `2^18` four-value fibre leaves.
pub fn full_domain_census(
    queries: [u32; V6_QUERY_COUNT],
    slots: [u8; V6_QUERY_COUNT],
) -> Result<V7CodeSwitchCensus, V6WireError> {
    let target = binary_frontier_nodes(queries, V7_TARGET_TREE_DEPTH)?;
    let source_indices = mapped_source_indices(queries, slots, 2)?;
    let source = binary_frontier_nodes(source_indices, V7_FULL_SOURCE_TREE_DEPTH)?;
    let total = target + 2 * source;
    Ok(V7CodeSwitchCensus {
        target_frontier_nodes: target,
        source_c1_frontier_nodes: source,
        source_c2_frontier_nodes: source,
        body_bytes: body_bytes(total),
    })
}

/// Research-only punctured-domain census.  One verifier-derived bit chooses
/// either of two target-domain rows per fibre, producing `2^19` source points.
/// The cryptographic applicability of this puncturing is a separate theorem
/// gate; this function records only its exact wire geometry.
pub fn half_domain_census(
    queries: [u32; V6_QUERY_COUNT],
    slots: [u8; V6_QUERY_COUNT],
) -> Result<V7CodeSwitchCensus, V6WireError> {
    let target = binary_frontier_nodes(queries, V7_TARGET_TREE_DEPTH)?;
    let source_indices = mapped_source_indices(queries, slots, 1)?;
    let source = binary_frontier_nodes(source_indices, V7_HALF_SOURCE_TREE_DEPTH)?;
    let total = target + 2 * source;
    Ok(V7CodeSwitchCensus {
        target_frontier_nodes: target,
        source_c1_frontier_nodes: source,
        source_c2_frontier_nodes: source,
        body_bytes: body_bytes(total),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const FINAL_DEVNET_QUERIES: [u32; V6_QUERY_COUNT] = [
        152_923, 41_573, 125_154, 198_143, 199_195, 126_196, 181_025, 22_338, 192_526, 90_042,
        114_555, 57_175, 202_857, 93_022, 91_980, 133_476,
    ];

    #[test]
    fn direct_row_width_is_information_theoretic_242_bytes() {
        assert_eq!(V7_SOURCE_C1_BYTES_PER_QUERY, 101);
        assert_eq!(V7_SOURCE_C2_BYTES_PER_QUERY, 47);
        assert_eq!(V7_TARGET_G_BYTES_PER_QUERY, 62);
        assert_eq!(V7_DIRECT_QUERY_BYTES, 242);
    }

    #[test]
    fn frozen_full_domain_census_is_36_040_bytes() {
        let slots = core::array::from_fn(|index| (index & 3) as u8);
        let census = full_domain_census(FINAL_DEVNET_QUERIES, slots).unwrap();
        assert_eq!(census.target_frontier_nodes, 209);
        assert_eq!(census.source_c1_frontier_nodes, 241);
        assert_eq!(census.source_c2_frontier_nodes, 241);
        assert_eq!(census.total_frontier_nodes(), 691);
        assert_eq!(census.body_bytes, 36_040);
        assert!(!census.fits_reference());
        assert!(!census.fits_hard_limit());
    }

    #[test]
    fn source_frontier_delta_is_slot_independent() {
        for salt in 0..16u8 {
            let slots = core::array::from_fn(|index| {
                ((salt.wrapping_mul(3).wrapping_add(index as u8)) & 3) as u8
            });
            let census = full_domain_census(FINAL_DEVNET_QUERIES, slots).unwrap();
            assert_eq!(
                census.source_c1_frontier_nodes,
                census.target_frontier_nodes + 2 * V6_QUERY_COUNT
            );
        }
    }

    #[test]
    fn frozen_half_domain_census_is_35_016_bytes() {
        let slots = core::array::from_fn(|index| (index & 1) as u8);
        let census = half_domain_census(FINAL_DEVNET_QUERIES, slots).unwrap();
        assert_eq!(census.target_frontier_nodes, 209);
        assert_eq!(census.source_c1_frontier_nodes, 225);
        assert_eq!(census.source_c2_frontier_nodes, 225);
        assert_eq!(census.total_frontier_nodes(), 659);
        assert_eq!(census.body_bytes, 35_016);
        assert!(!census.fits_reference());
        assert!(!census.fits_hard_limit());
    }
}
