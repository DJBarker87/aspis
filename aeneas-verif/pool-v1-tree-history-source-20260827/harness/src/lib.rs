#![allow(dead_code)]

use aspis_statement::{
    pool_v1::{
        root_history_location, AppendOneV1, AppendTwoV1, IncrementalMerkleTreeV1,
        PoolV1TreeError, RootHistoryLocationV1, POOL_V1_TREE_DEPTH,
    },
    poseidon2::Digest,
};

/// Literal public production constructor used for Pool sequence zero.
pub fn production_tree_genesis() -> IncrementalMerkleTreeV1 {
    IncrementalMerkleTreeV1::empty()
}

/// Literal production one-leaf append with the caller-authenticated empty-root
/// table. The wrapper changes no data and introduces no alternative kernel.
pub fn production_tree_append_one(
    source: &IncrementalMerkleTreeV1,
    leaf: Digest,
    empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
) -> Result<(IncrementalMerkleTreeV1, AppendOneV1), PoolV1TreeError> {
    source.append_one_with_empty_roots(leaf, empty)
}

/// Literal production ordered two-leaf append. Capacity is checked before the
/// first production append and the returned receipts retain their order.
pub fn production_tree_append_two(
    source: &IncrementalMerkleTreeV1,
    first: Digest,
    second: Digest,
    empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
) -> Result<(IncrementalMerkleTreeV1, AppendTwoV1), PoolV1TreeError> {
    source.append_two_with_empty_roots(first, second, empty)
}

/// Literal quotient/remainder location used by both tree receipts and Pool
/// root-history persistence.
pub fn production_root_history_location(sequence: u64) -> RootHistoryLocationV1 {
    root_history_location(sequence)
}
