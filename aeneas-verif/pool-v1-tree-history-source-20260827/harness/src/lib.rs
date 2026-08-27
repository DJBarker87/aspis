#![allow(dead_code)]

use aspis_statement::{
    pool_v1::{
        root_history_location, AppendOneV1, AppendTwoV1, IncrementalMerkleTreeV1,
        PoolV1TreeError, RootHistoryLocationV1, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_TREE_DEPTH,
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

/// Extraction-only normalization of the pure suffix of
/// `history::validate_new_page_account` after Solana has successfully returned
/// the account-data borrow.  The runtime borrow itself deliberately remains a
/// named interface; the exact fixed length and every-byte-zero test remain
/// executable source.
pub fn normalized_validate_new_page_borrowed_data(data: &[u8]) -> bool {
    data.len() == POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
        && !data.iter().any(|byte| *byte != 0)
}

/// Exact after-image tuple of the prepared-settlement Pool/history writes.
/// The fixed arrays begin after all mutable Solana borrows and length checks
/// have succeeded, so assignment is the semantic normalization of
/// `copy_from_slice` on equal-sized buffers.
pub struct NormalizedPreparedHistoryWritebackV1 {
    pub pool: [u8; 1000],
    pub current: [u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    pub rollover: Option<[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>,
}

/// Normalize the three production account copies after successful mutable
/// borrows.  `None` is exactly the production mismatched rollover-option
/// branch, whose transaction is rolled back by Solana.
pub fn normalized_prepared_history_writeback(
    source_current: [u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    source_rollover: Option<[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>,
    next_pool_image: [u8; 1000],
    next_current_page_image: [u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    next_rollover_page_image: Option<[u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>,
    current_writable: bool,
) -> Option<NormalizedPreparedHistoryWritebackV1> {
    let current = if current_writable {
        next_current_page_image
    } else {
        source_current
    };
    let rollover = match (source_rollover, next_rollover_page_image) {
        (Some(_), Some(image)) => Some(image),
        (None, None) => None,
        _ => return None,
    };
    Some(NormalizedPreparedHistoryWritebackV1 {
        pool: next_pool_image,
        current,
        rollover,
    })
}

/// Extraction-only projection of `processor::require_unique_accounts` onto
/// the account keys it reads.  The nested loop bounds and first duplicate
/// rejection are identical to production; no account-data behavior appears.
pub fn normalized_require_unique_account_keys(keys: &[[u8; 32]]) -> bool {
    for left in 0..keys.len() {
        for right in left + 1..keys.len() {
            if keys[left] == keys[right] {
                return false;
            }
        }
    }
    true
}
