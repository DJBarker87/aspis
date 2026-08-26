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
use aspis_core::v6_transcript::{
    verify_v7_compact_transcript_and_relation_prepared, V6QueryBatchView, V6SemanticView,
    V6TranscriptContext, V6TranscriptError, V6VerifiedTranscript,
};
use aspis_core::v7_onefold::{
    verify_and_gamma_combine_v7_openings, V7CompactOneFoldWire,
};
use aspis_core::HashFn;
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_group_masks_v3, atomic_state_only_copy_inactive_row_groups_v3,
    atomic_state_only_selected_masked_terminal_value_compiled_tag73,
};
use aspis_statement::{atomic_payment_statement_digest_v4, AtomicPaymentStatementV4};
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

#[inline(never)]
fn authenticate_and_fold_queries(
    hash: HashFn,
    wire: &V7CompactOneFoldWire<'_>,
    view: &V6QueryBatchView<'_>,
) -> Result<V6AuthenticatedQueryBatch, V6WireError> {
    let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
    let combined = verify_and_gamma_combine_v7_openings(
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
