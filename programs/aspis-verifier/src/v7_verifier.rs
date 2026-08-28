//! Complete read-only verifier composition for the compact V7 successor to
//! the frozen V6 26+3 one-fold path.
//!
//! V7 reuses the semantic terminal and relation algebra, but has a distinct
//! transcript profile, 208-bit Merkle trees, a first-cap203 query schedule,
//! and complete authenticated C2 fibres.

use aspis_core::field::QM31;
use aspis_core::v6_onefold::{
    fold_v6_onefold_queries, prepare_v6_onefold_coordinates, V6WireError,
};
use aspis_core::v6_query_batch::V6AuthenticatedQueryBatch;
#[cfg(feature = "v7-pair-forest-fixed-canonical-audit")]
use aspis_core::v6_transcript::verify_v7_canonical_transcript_and_relation_prepared_with_hiding_context;
use aspis_core::v6_transcript::{
    verify_v7_compact_transcript_and_relation_prepared,
    verify_v7_compact_transcript_and_relation_prepared_with_hiding_context, V6QueryBatchView,
    V6SemanticView, V6TranscriptContext, V6TranscriptError, V6VerifiedTranscript,
};
#[cfg(feature = "v7-pair-forest-fixed-canonical-audit")]
use aspis_core::v7_fixed_canonical_audit::{
    verify_and_gamma_combine_v7_canonical_openings, V7CanonicalOneFoldWire,
};
use aspis_core::v7_onefold::{verify_and_gamma_combine_v7_openings, V7CompactOneFoldWire};
use aspis_core::{state_only_hiding::StateOnlyHidingContext, HashFn};
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_group_masks_v3, atomic_state_only_copy_inactive_row_groups_v3,
    atomic_state_only_selected_masked_terminal_value_compiled_tag73,
};
use aspis_statement::{
    atomic_payment_statement_digest_v4,
    pool_v1::{
        evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1,
        pool_v1_pair_forest_copy_active_row_masks_compiled_v1,
        pool_v1_private_transfer_copy_active_row_masks_compiled_v1,
        pool_v1_withdrawal_copy_active_row_masks_compiled_v1, PoolV1PairLatePublicStatementV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
    },
    AtomicPaymentStatementV4,
};
use solana_program::pubkey::Pubkey;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V7VerifyError {
    StatementDigest,
    Transcript(V6TranscriptError),
    Query(V6WireError),
}

impl From<V6TranscriptError> for V7VerifyError {
    fn from(error: V6TranscriptError) -> Self {
        Self::Transcript(error)
    }
}

impl From<V6WireError> for V7VerifyError {
    fn from(error: V6WireError) -> Self {
        Self::Query(error)
    }
}

#[derive(Debug)]
pub struct VerifiedV7ReadOnly {
    pub transcript: V6VerifiedTranscript,
    pub folded_query_sum: QM31,
}

fn terminal_matches(statement: &AtomicPaymentStatementV4, view: &V6SemanticView<'_>) -> bool {
    atomic_state_only_selected_masked_terminal_value_compiled_tag73(
        statement,
        &crate::v6_verifier::terminal_claims(view),
        &view.point,
        view.lambda,
        view.chi,
        view.batching.theta,
        &view.batching.zerocheck_point,
        view.batching.mu,
        view.eta,
    )
    .is_ok_and(|expected| expected == view.terminal_claim)
}

/// Build the exact inactive-row covector from a compiled Pool copy registry.
/// The transcript helper accepts a deduplicated 64x16 mask schedule; doing the
/// tiny deduplication here keeps the semantic constants as the sole source of
/// truth and avoids a second hand-maintained row table.
fn pool_inactive_schedule(active: &[u16; 64]) -> ([u8; 64], [u16; 64], usize) {
    let mut row_groups = [0u8; 64];
    let mut group_masks = [0u16; 64];
    let mut group_count = 0usize;
    for (row, active_mask) in active.iter().copied().enumerate() {
        let inactive_mask = !active_mask;
        let group = group_masks[..group_count]
            .iter()
            .position(|mask| *mask == inactive_mask)
            .unwrap_or_else(|| {
                let next = group_count;
                group_masks[next] = inactive_mask;
                group_count += 1;
                next
            });
        row_groups[row] = group as u8;
    }
    (row_groups, group_masks, group_count)
}

fn pool_private_transfer_terminal_matches(
    statement: &PoolV1PrivateTransferPublicV1,
    view: &V6SemanticView<'_>,
) -> bool {
    evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1(
        statement,
        &crate::v6_verifier::terminal_claims(view),
        &view.point,
        view.lambda,
        view.chi,
        view.batching.theta,
        &view.batching.zerocheck_point,
        view.batching.mu,
        view.eta,
    )
    .is_ok_and(|expected| expected == view.terminal_claim)
}

fn pool_withdrawal_terminal_matches(
    statement: &PoolV1WithdrawalPublicV1,
    view: &V6SemanticView<'_>,
) -> bool {
    evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1(
        statement,
        &crate::v6_verifier::terminal_claims(view),
        &view.point,
        view.lambda,
        view.chi,
        view.batching.theta,
        &view.batching.zerocheck_point,
        view.batching.mu,
        view.eta,
    )
    .is_ok_and(|expected| expected == view.terminal_claim)
}

fn pool_pair_forest_private_transfer_terminal_matches(
    statement: &PoolV1PrivateTransferPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    view: &V6SemanticView<'_>,
) -> bool {
    evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
        statement,
        transition,
        &crate::v6_verifier::terminal_claims(view),
        &view.point,
        view.lambda,
        view.chi,
        view.batching.theta,
        &view.batching.zerocheck_point,
        view.batching.mu,
        view.eta,
    )
    .is_ok_and(|expected| expected == view.terminal_claim)
}

fn pool_pair_forest_withdrawal_terminal_matches(
    statement: &PoolV1WithdrawalPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    view: &V6SemanticView<'_>,
) -> bool {
    evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(
        statement,
        transition,
        &crate::v6_verifier::terminal_claims(view),
        &view.point,
        view.lambda,
        view.chi,
        view.batching.theta,
        &view.batching.zerocheck_point,
        view.batching.mu,
        view.eta,
    )
    .is_ok_and(|expected| expected == view.terminal_claim)
}

#[inline(never)]
fn authenticate_and_fold_queries(
    hash: HashFn,
    wire: &V7CompactOneFoldWire<'_>,
    view: &V6QueryBatchView<'_>,
) -> Result<V6AuthenticatedQueryBatch, V6WireError> {
    let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
    let combined =
        verify_and_gamma_combine_v7_openings(hash, wire, view.queries, view.gamma_powers)?;
    Ok(V6AuthenticatedQueryBatch {
        values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
        line_x: coordinates.line_x,
    })
}

#[cfg(feature = "v7-pair-forest-fixed-canonical-audit")]
#[inline(never)]
fn authenticate_and_fold_canonical_queries(
    hash: HashFn,
    wire: &V7CanonicalOneFoldWire<'_>,
    view: &V6QueryBatchView<'_>,
) -> Result<V6AuthenticatedQueryBatch, V6WireError> {
    let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
    let combined = verify_and_gamma_combine_v7_canonical_openings(
        hash,
        wire,
        view.queries,
        view.gamma_powers,
    )?;
    Ok(V6AuthenticatedQueryBatch {
        values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
        line_x: coordinates.line_x,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn verify_v7_read_only(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &AtomicPaymentStatementV4,
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let statement_digest = atomic_payment_statement_digest_v4(statement, hash)
        .map_err(|_| V7VerifyError::StatementDigest)?;
    verify_v7_read_only_with_statement_digest(
        hash,
        proof,
        frontier_nodes,
        program_id,
        release_binding,
        attempt_id,
        statement,
        statement_digest,
        check_pow,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn verify_v7_read_only_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &AtomicPaymentStatementV4,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let wire = V7CompactOneFoldWire::parse_deferred_canonicality(proof, frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let transcript = verify_v7_compact_transcript_and_relation_prepared(
        hash,
        &wire,
        &context,
        atomic_state_only_copy_inactive_row_groups_v3(),
        atomic_state_only_copy_inactive_group_masks_v3(),
        check_pow,
        |view| terminal_matches(statement, view),
        |view| authenticate_and_fold_queries(hash, &wire, view),
    )?;
    let folded_query_sum = transcript.folded_query_sum;
    Ok(VerifiedV7ReadOnly {
        transcript,
        folded_query_sum,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn verify_v7_pool_private_transfer_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &PoolV1PrivateTransferPublicV1,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let wire = V7CompactOneFoldWire::parse_deferred_canonicality(proof, frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let (row_groups, group_masks, group_count) =
        pool_inactive_schedule(pool_v1_private_transfer_copy_active_row_masks_compiled_v1());
    let transcript = verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
        hash,
        &wire,
        &context,
        StateOnlyHidingContext::pool_v1_private_transfer(statement_digest, attempt_id.to_bytes()),
        &row_groups,
        &group_masks[..group_count],
        check_pow,
        |view| pool_private_transfer_terminal_matches(statement, view),
        |view| authenticate_and_fold_queries(hash, &wire, view),
    )?;
    Ok(VerifiedV7ReadOnly {
        folded_query_sum: transcript.folded_query_sum,
        transcript,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn verify_v7_pool_withdrawal_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &PoolV1WithdrawalPublicV1,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let wire = V7CompactOneFoldWire::parse_deferred_canonicality(proof, frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let (row_groups, group_masks, group_count) =
        pool_inactive_schedule(pool_v1_withdrawal_copy_active_row_masks_compiled_v1());
    let transcript = verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
        hash,
        &wire,
        &context,
        StateOnlyHidingContext::pool_v1_withdrawal(statement_digest, attempt_id.to_bytes()),
        &row_groups,
        &group_masks[..group_count],
        check_pow,
        |view| pool_withdrawal_terminal_matches(statement, view),
        |view| authenticate_and_fold_queries(hash, &wire, view),
    )?;
    Ok(VerifiedV7ReadOnly {
        folded_query_sum: transcript.folded_query_sum,
        transcript,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn verify_v7_pool_pair_forest_private_transfer_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &PoolV1PrivateTransferPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let wire = V7CompactOneFoldWire::parse_deferred_canonicality(proof, frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let (row_groups, group_masks, group_count) =
        pool_inactive_schedule(pool_v1_pair_forest_copy_active_row_masks_compiled_v1());
    let transcript = verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
        hash,
        &wire,
        &context,
        StateOnlyHidingContext::pool_v1_pair_forest_v1(statement_digest, attempt_id.to_bytes()),
        &row_groups,
        &group_masks[..group_count],
        check_pow,
        |view| pool_pair_forest_private_transfer_terminal_matches(statement, transition, view),
        |view| authenticate_and_fold_queries(hash, &wire, view),
    )?;
    Ok(VerifiedV7ReadOnly {
        folded_query_sum: transcript.folded_query_sum,
        transcript,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn verify_v7_pool_pair_forest_withdrawal_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &PoolV1WithdrawalPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let wire = V7CompactOneFoldWire::parse_deferred_canonicality(proof, frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let (row_groups, group_masks, group_count) =
        pool_inactive_schedule(pool_v1_pair_forest_copy_active_row_masks_compiled_v1());
    let transcript = verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
        hash,
        &wire,
        &context,
        StateOnlyHidingContext::pool_v1_pair_forest_v1(statement_digest, attempt_id.to_bytes()),
        &row_groups,
        &group_masks[..group_count],
        check_pow,
        |view| pool_pair_forest_withdrawal_terminal_matches(statement, transition, view),
        |view| authenticate_and_fold_queries(hash, &wire, view),
    )?;
    Ok(VerifiedV7ReadOnly {
        folded_query_sum: transcript.folded_query_sum,
        transcript,
    })
}

#[cfg(feature = "v7-pair-forest-fixed-canonical-audit")]
#[allow(clippy::too_many_arguments)]
pub fn verify_v7_pool_pair_forest_private_transfer_canonical_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &PoolV1PrivateTransferPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let wire = V7CanonicalOneFoldWire::parse(proof, frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let (row_groups, group_masks, group_count) =
        pool_inactive_schedule(pool_v1_pair_forest_copy_active_row_masks_compiled_v1());
    let transcript = verify_v7_canonical_transcript_and_relation_prepared_with_hiding_context(
        hash,
        &wire,
        &context,
        StateOnlyHidingContext::pool_v1_pair_forest_v1(statement_digest, attempt_id.to_bytes()),
        &row_groups,
        &group_masks[..group_count],
        check_pow,
        |view| pool_pair_forest_private_transfer_terminal_matches(statement, transition, view),
        |view| authenticate_and_fold_canonical_queries(hash, &wire, view),
    )?;
    Ok(VerifiedV7ReadOnly {
        folded_query_sum: transcript.folded_query_sum,
        transcript,
    })
}

#[cfg(feature = "v7-pair-forest-fixed-canonical-audit")]
#[allow(clippy::too_many_arguments)]
pub fn verify_v7_pool_pair_forest_withdrawal_canonical_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    frontier_nodes: usize,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &PoolV1WithdrawalPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV7ReadOnly, V7VerifyError> {
    let wire = V7CanonicalOneFoldWire::parse(proof, frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let (row_groups, group_masks, group_count) =
        pool_inactive_schedule(pool_v1_pair_forest_copy_active_row_masks_compiled_v1());
    let transcript = verify_v7_canonical_transcript_and_relation_prepared_with_hiding_context(
        hash,
        &wire,
        &context,
        StateOnlyHidingContext::pool_v1_pair_forest_v1(statement_digest, attempt_id.to_bytes()),
        &row_groups,
        &group_masks[..group_count],
        check_pow,
        |view| pool_pair_forest_withdrawal_terminal_matches(statement, transition, view),
        |view| authenticate_and_fold_canonical_queries(hash, &wire, view),
    )?;
    Ok(VerifiedV7ReadOnly {
        folded_query_sum: transcript.folded_query_sum,
        transcript,
    })
}

#[cfg(test)]
mod pool_tests {
    use super::*;

    #[test]
    fn pool_inactive_schedules_are_exact_complements_and_deduplicated() {
        for active in [
            pool_v1_private_transfer_copy_active_row_masks_compiled_v1(),
            pool_v1_withdrawal_copy_active_row_masks_compiled_v1(),
            pool_v1_pair_forest_copy_active_row_masks_compiled_v1(),
        ] {
            let (groups, masks, count) = pool_inactive_schedule(active);
            assert!(count > 0 && count <= 64);
            for row in 0..64 {
                assert!(usize::from(groups[row]) < count);
                assert_eq!(masks[usize::from(groups[row])], !active[row]);
            }
            for left in 0..count {
                for right in left + 1..count {
                    assert_ne!(masks[left], masks[right]);
                }
            }
        }
    }
}
