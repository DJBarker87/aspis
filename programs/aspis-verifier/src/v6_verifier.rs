//! Complete read-only verifier composition for the V6 26+3 one-fold path.
//!
//! The frozen tag-72 instruction dispatches this composition surface.  Keep
//! it as the single measured and source-translated V6 acceptance entrypoint.

use aspis_core::field::QM31;
use aspis_core::v6_onefold::{
    fold_v6_onefold_queries, parse_v6_onefold_wire_deferred, prepare_v6_onefold_coordinates,
    verify_and_gamma_combine_v6_binary_openings_prepared, V6OneFoldWire, V6WireError,
};
use aspis_core::v6_query_batch::V6AuthenticatedQueryBatch;
use aspis_core::v6_transcript::{
    verify_v6_transcript_and_relation_prepared, V6QueryBatchView, V6SemanticView,
    V6TranscriptContext, V6TranscriptError, V6VerifiedTranscript,
};
use aspis_core::HashFn;
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_group_masks_v3, atomic_state_only_copy_inactive_row_groups_v3,
    atomic_state_only_selected_masked_terminal_value_compiled_v3,
};
use aspis_statement::{
    atomic_payment_statement_digest_v4, AtomicPaymentStatementV4,
    STATE_ONLY_SELECTED_TERMINAL_CLAIMS,
};
use solana_program::pubkey::Pubkey;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6VerifyError {
    StatementDigest,
    Transcript(V6TranscriptError),
    Query(V6WireError),
}

impl From<V6TranscriptError> for V6VerifyError {
    fn from(error: V6TranscriptError) -> Self {
        Self::Transcript(error)
    }
}

impl From<V6WireError> for V6VerifyError {
    fn from(error: V6WireError) -> Self {
        Self::Query(error)
    }
}

#[derive(Debug)]
pub struct VerifiedV6ReadOnly {
    pub transcript: V6VerifiedTranscript,
    pub folded_query_sum: QM31,
}

fn terminal_claims(view: &V6SemanticView<'_>) -> [QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS] {
    // The maintained atomic selected-hiding terminal consumes 3 x 28 lanes:
    // C1[0..26], H and G. V6's appended D lane is column 28 and participates
    // only in the PCS relation, exactly as in the maintained spend profile.
    core::array::from_fn(|index| {
        let row = index / 28;
        let column = index % 28;
        view.point_claims[row][column]
    })
}

fn terminal_matches(statement: &AtomicPaymentStatementV4, view: &V6SemanticView<'_>) -> bool {
    atomic_state_only_selected_masked_terminal_value_compiled_v3(
        statement,
        &terminal_claims(view),
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
    wire: &V6OneFoldWire<'_>,
    view: &V6QueryBatchView<'_>,
) -> Result<V6AuthenticatedQueryBatch, V6WireError> {
    let combined = verify_and_gamma_combine_v6_binary_openings_prepared(
        hash,
        wire,
        view.queries,
        view.gamma_powers,
    )?;
    let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
    Ok(V6AuthenticatedQueryBatch {
        values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
        line_x: coordinates.line_x,
    })
}

/// Verify the exact V6 read-only proof path. The caller supplies frontier
/// counts and selector from the instruction, while queries and the compact
/// counter are derived entirely by the transcript.
#[allow(clippy::too_many_arguments)]
pub fn verify_v6_read_only(
    hash: HashFn,
    proof: &[u8],
    c1_frontier_nodes: usize,
    c2_frontier_nodes: usize,
    selector: u8,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &AtomicPaymentStatementV4,
    check_pow: bool,
) -> Result<VerifiedV6ReadOnly, V6VerifyError> {
    let statement_digest = atomic_payment_statement_digest_v4(statement, hash)
        .map_err(|_| V6VerifyError::StatementDigest)?;
    verify_v6_read_only_with_statement_digest(
        hash,
        proof,
        c1_frontier_nodes,
        c2_frontier_nodes,
        selector,
        program_id,
        release_binding,
        attempt_id,
        statement,
        statement_digest,
        check_pow,
    )
}

/// Verify V6 with the exact statement digest already checked by the atomic
/// transition wrapper. This is the production entrypoint: the wrapper must
/// construct `statement` and `statement_digest` together and supplies both
/// to this function, avoiding a duplicate SHA-256 statement serialization
/// without weakening the transcript binding.
#[allow(clippy::too_many_arguments)]
pub fn verify_v6_read_only_with_statement_digest(
    hash: HashFn,
    proof: &[u8],
    c1_frontier_nodes: usize,
    c2_frontier_nodes: usize,
    selector: u8,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &AtomicPaymentStatementV4,
    statement_digest: [u8; 32],
    check_pow: bool,
) -> Result<VerifiedV6ReadOnly, V6VerifyError> {
    verify_v6_read_only_with_statement_digest_and_schedule(
        hash,
        proof,
        c1_frontier_nodes,
        c2_frontier_nodes,
        selector,
        program_id,
        release_binding,
        attempt_id,
        statement,
        statement_digest,
        atomic_state_only_copy_inactive_row_groups_v3(),
        atomic_state_only_copy_inactive_group_masks_v3(),
        check_pow,
    )
}

/// Source-translation boundary for the production entrypoint.  The public
/// wrapper above supplies the two frozen generated schedules; separating
/// those references from the acceptance kernel avoids asking Aeneas to
/// synthesize a loan for an opaque `&'static` return value.
#[allow(clippy::too_many_arguments)]
#[inline(always)]
pub(crate) fn verify_v6_read_only_with_statement_digest_and_schedule(
    hash: HashFn,
    proof: &[u8],
    c1_frontier_nodes: usize,
    c2_frontier_nodes: usize,
    selector: u8,
    program_id: &Pubkey,
    release_binding: [u8; 32],
    attempt_id: &Pubkey,
    statement: &AtomicPaymentStatementV4,
    statement_digest: [u8; 32],
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
) -> Result<VerifiedV6ReadOnly, V6VerifyError> {
    let wire = parse_v6_onefold_wire_deferred(proof, c1_frontier_nodes, c2_frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding,
        statement_digest,
        attempt_id: attempt_id.to_bytes(),
    };
    let transcript = verify_v6_transcript_and_relation_prepared(
        hash,
        &wire,
        &context,
        selector,
        inactive_row_groups,
        inactive_group_masks,
        check_pow,
        |view| terminal_matches(statement, view),
        |view| authenticate_and_fold_queries(hash, &wire, view),
    )?;
    let folded_query_sum = transcript.folded_query_sum;
    Ok(VerifiedV6ReadOnly {
        transcript,
        folded_query_sum,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn terminal_claim_projection_excludes_only_d() {
        let point_claims = [[QM31::ZERO; 29]; 3];
        let view = V6SemanticView {
            lambda: QM31::ZERO,
            chi: QM31::ZERO,
            batching: aspis_core::statement_sumcheck::PaymentConstraintChallenges {
                theta: QM31::ZERO,
                zerocheck_point: [QM31::ZERO; 10],
                mu: QM31::ZERO,
            },
            eta: QM31::ONE,
            point: [QM31::ZERO; 10],
            terminal_claim: QM31::ZERO,
            point_claims: &point_claims,
        };
        assert_eq!(terminal_claims(&view).len(), 84);
        assert_eq!(terminal_claims(&view), [QM31::ZERO; 84]);
    }
}
