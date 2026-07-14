//! Complete atomic profile-22 verifier.
//!
//! The relation and q16 arithmetic are profile 20.  Only the five Merkle
//! sections use private salted leaf records.

use alloc::{boxed::Box, vec::Vec};

use aspis_core::circle_fri::{
    normalized_circle_to_line_arity4_prepared_polynomial_candidate, RATE512_CIRCLE_INV_2X,
    RATE512_CIRCLE_INV_2Y, RATE512_FINAL_X, RATE512_LINE1_INV, RATE512_LINE2_INV,
    RATE512_LINE3_INV,
};
use aspis_core::circle_prefix::{
    CandidatePrefixError, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_ROUND_COUNT,
};
use aspis_core::circle_query::{
    check_fixed_line_transition_prepared_polynomial,
    check_fixed_terminal_transition_prepared_polynomial, CircleQueryError,
};
use aspis_core::field::{PreparedQm31Multiplier, M31, QM31};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_transcript_schedule_host_v3, StateOnlyCandidatePrefix,
    StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult,
    STATE_ONLY_PROFILE22_PRIVATE_SHAPE, STATE_ONLY_STATEMENT_VALUE_COUNT,
};
use aspis_core::state_only_private_openings::StateOnlyPrivateOpening;
use aspis_core::state_only_profile22_openings::{
    verify_state_only_profile22_openings, StateOnlyProfile22OpeningError,
    StateOnlyProfile22OpeningRoots, VerifiedStateOnlyProfile22Openings,
    PROFILE22_LAYER0_LEAF_COUNT,
};
use aspis_core::state_only_query::{
    gamma_combine_state_only_layer0_prepared, STATE_ONLY_C2_LEAF_BYTES,
};
use aspis_core::state_only_relation::{prepare_state_only_relation, StateOnlyRelationPrepared};
use aspis_core::HashFn;

use crate::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_row_masks_v3,
    atomic_state_only_selected_masked_terminal_value_compiled_v3,
};
use crate::state_only_terminal::{StateOnlyTerminalError, STATE_ONLY_SELECTED_TERMINAL_CLAIMS};
use crate::state_only_verify::{
    verify_state_only_relation_with_inactive_masks, StateOnlyRelationVerifyError,
};
use crate::{atomic_payment_statement_digest_v3, AtomicPaymentStatementV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile22TraceEvent {
    Parsed,
    Transcript,
    Terminal,
    Relation,
    Openings,
    Layer0Queries,
    LaterQueries,
    Complete,
}

pub type Profile22Trace = fn(Profile22TraceEvent);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile22VerifyError {
    Prefix(CandidatePrefixError),
    Transcript(StateOnlyTranscriptError),
    StatementDigest,
    StatementValues,
    Terminal(StateOnlyTerminalError),
    TerminalMismatch,
    Relation(StateOnlyRelationVerifyError),
    Opening(StateOnlyProfile22OpeningError),
    Query(CircleQueryError),
    MissingRoot,
    MissingOpening,
    NonCanonicalLater { offset: usize },
    FirstFoldMismatch { query: u32 },
}

impl From<CandidatePrefixError> for Profile22VerifyError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}
impl From<StateOnlyTranscriptError> for Profile22VerifyError {
    fn from(error: StateOnlyTranscriptError) -> Self {
        Self::Transcript(error)
    }
}
impl From<StateOnlyTerminalError> for Profile22VerifyError {
    fn from(error: StateOnlyTerminalError) -> Self {
        Self::Terminal(error)
    }
}
impl From<StateOnlyRelationVerifyError> for Profile22VerifyError {
    fn from(error: StateOnlyRelationVerifyError) -> Self {
        Self::Relation(error)
    }
}
impl From<StateOnlyProfile22OpeningError> for Profile22VerifyError {
    fn from(error: StateOnlyProfile22OpeningError) -> Self {
        Self::Opening(error)
    }
}
impl From<CircleQueryError> for Profile22VerifyError {
    fn from(error: CircleQueryError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedAtomicProfile22<'a> {
    pub prefix: StateOnlyCandidatePrefix<'a>,
    pub schedule: Box<StateOnlyTranscriptScheduleResult>,
    pub relation: Box<StateOnlyRelationPrepared>,
    pub openings: Box<VerifiedStateOnlyProfile22Openings<'a>>,
}

#[inline(always)]
fn traced(trace: Option<Profile22Trace>, event: Profile22TraceEvent) {
    if let Some(trace) = trace {
        trace(event);
    }
}

fn statement_values(
    prefix: &StateOnlyCandidatePrefix<'_>,
) -> Result<Box<[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS]>, Profile22VerifyError> {
    if STATE_ONLY_SELECTED_TERMINAL_CLAIMS != STATE_ONLY_STATEMENT_VALUE_COUNT {
        return Err(Profile22VerifyError::StatementValues);
    }
    let mut values = Vec::with_capacity(STATE_ONLY_SELECTED_TERMINAL_CLAIMS);
    for index in 0..STATE_ONLY_SELECTED_TERMINAL_CLAIMS {
        values.push(
            prefix
                .statement_evaluation(index)
                .ok_or(Profile22VerifyError::StatementValues)?,
        );
    }
    values
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Profile22VerifyError::StatementValues)
}

fn later_roots(
    prefix: &StateOnlyCandidatePrefix<'_>,
) -> Result<[[u8; 32]; 3], Profile22VerifyError> {
    let mut roots = [[0u8; 32]; 3];
    for (layer, root) in roots.iter_mut().enumerate() {
        *root = *prefix.rounds[layer + 1]
            .root
            .ok_or(Profile22VerifyError::MissingRoot)?;
    }
    Ok(roots)
}

#[inline(always)]
fn opening_value_for_index<'a>(
    opening: &StateOnlyPrivateOpening<'a>,
    indices: &[u32],
    index: u32,
) -> Result<&'a [u8], Profile22VerifyError> {
    let ordinal = indices
        .binary_search(&index)
        .map_err(|_| Profile22VerifyError::MissingOpening)?;
    opening
        .value(ordinal)
        .ok_or(Profile22VerifyError::MissingOpening)
}

fn verify_profile22_queries(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    relation: &StateOnlyRelationPrepared,
    openings: &VerifiedStateOnlyProfile22Openings<'_>,
    trace: Option<Profile22Trace>,
) -> Result<(), Profile22VerifyError> {
    let queries = &openings.indices.layer0;
    if queries.len() != STATE_ONLY_PROFILE22_PRIVATE_SHAPE.query_count as usize
        || openings.c2.value_width != STATE_ONLY_C2_LEAF_BYTES
    {
        return Err(Profile22VerifyError::MissingOpening);
    }
    let alpha_values = schedule.alpha;
    let alpha_squared_values = alpha_values.map(QM31::square);
    let alpha: [PreparedQm31Multiplier; CANDIDATE_ROUND_COUNT] =
        alpha_values.map(PreparedQm31Multiplier::new);
    let alpha_squared: [PreparedQm31Multiplier; CANDIDATE_ROUND_COUNT] =
        alpha_squared_values.map(PreparedQm31Multiplier::new);
    let alpha_cubed: [PreparedQm31Multiplier; CANDIDATE_ROUND_COUNT] =
        core::array::from_fn(|round| {
            PreparedQm31Multiplier::new(alpha_squared_values[round].mul(alpha_values[round]))
        });

    for (ordinal, &query) in queries.iter().enumerate() {
        let c1 = openings
            .c1
            .value(ordinal)
            .ok_or(Profile22VerifyError::MissingOpening)?;
        let c2 = openings
            .c2
            .value(ordinal)
            .ok_or(Profile22VerifyError::MissingOpening)?;
        let combined = gamma_combine_state_only_layer0_prepared(c1, c2, &relation.query_powers)?;
        let folded = normalized_circle_to_line_arity4_prepared_polynomial_candidate(
            combined,
            alpha[0],
            alpha_squared[0],
            alpha_cubed[0],
            M31(RATE512_CIRCLE_INV_2X[query as usize]),
            M31(RATE512_CIRCLE_INV_2Y[query as usize]),
        );
        let w1 =
            opening_value_for_index(&openings.later[0], &openings.indices.later[0], query >> 2)?;
        let slot = (query & 3) as usize;
        let start = slot * 16;
        let expected = QM31::from_le_bytes(
            w1.get(start..start + 16)
                .ok_or(Profile22VerifyError::MissingOpening)?,
        )
        .ok_or(Profile22VerifyError::NonCanonicalLater { offset: start })?;
        if folded != expected {
            return Err(Profile22VerifyError::FirstFoldMismatch { query });
        }
    }
    traced(trace, Profile22TraceEvent::Layer0Queries);

    let line_tables: [&[u32]; 3] = [&RATE512_LINE1_INV, &RATE512_LINE2_INV, &RATE512_LINE3_INV];
    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(Profile22VerifyError::StatementValues)?;
    }
    for layer in 0..3 {
        for (ordinal, &index) in openings.indices.later[layer].iter().enumerate() {
            let incoming = openings.later[layer]
                .value(ordinal)
                .ok_or(Profile22VerifyError::MissingOpening)?;
            let offset = index as usize * 3;
            let inverses = [
                M31(line_tables[layer][offset]),
                M31(line_tables[layer][offset + 1]),
                M31(line_tables[layer][offset + 2]),
            ];
            if layer < 2 {
                let outgoing = opening_value_for_index(
                    &openings.later[layer + 1],
                    &openings.indices.later[layer + 1],
                    index >> 2,
                )?;
                check_fixed_line_transition_prepared_polynomial(
                    incoming,
                    outgoing,
                    index as usize,
                    layer as u8 + 1,
                    inverses,
                    alpha[layer + 1],
                    alpha_squared[layer + 1],
                    alpha_cubed[layer + 1],
                )?;
            } else {
                check_fixed_terminal_transition_prepared_polynomial(
                    incoming,
                    final_coefficients,
                    index as usize,
                    inverses,
                    M31(RATE512_FINAL_X[index as usize]),
                    alpha[3],
                    alpha_squared[3],
                    alpha_cubed[3],
                )?;
            }
        }
    }
    traced(trace, Profile22TraceEvent::LaterQueries);
    Ok(())
}

fn boxed_schedule(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<Box<StateOnlyTranscriptScheduleResult>, Profile22VerifyError> {
    let schedule = if check_pow {
        run_atomic_state_only_transcript_schedule_host_v3(hash, prefix, statement_digest)?
    } else {
        run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
            hash,
            prefix,
            statement_digest,
        )?
    };
    Ok(Box::new(schedule))
}

#[inline(never)]
fn verify_profile22_terminal(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    statement: &AtomicPaymentStatementV3,
) -> Result<(), Profile22VerifyError> {
    let values = statement_values(prefix)?;
    let terminal = atomic_state_only_selected_masked_terminal_value_compiled_v3(
        statement,
        &values,
        &schedule.prefix.z,
        schedule.prefix.lambda,
        schedule.prefix.chi,
        schedule.prefix.batching.theta,
        &schedule.prefix.batching.zerocheck_point,
        schedule.prefix.batching.mu,
        schedule.prefix.eta,
    )?;
    if terminal != schedule.prefix.masked_terminal_claim {
        return Err(Profile22VerifyError::TerminalMismatch);
    }
    Ok(())
}

#[inline(never)]
fn boxed_profile22_relation(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Box<StateOnlyRelationPrepared>, Profile22VerifyError> {
    let relation =
        prepare_state_only_relation(schedule.prefix.gamma, prefix.statement_evaluations_bytes)
            .ok_or(Profile22VerifyError::StatementValues)?;
    verify_state_only_relation_with_inactive_masks(
        prefix,
        schedule,
        &relation,
        atomic_state_only_copy_inactive_row_masks_v3(),
    )?;
    Ok(Box::new(relation))
}

#[inline(never)]
fn boxed_profile22_openings<'a>(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    suffix: &'a [u8],
) -> Result<Box<VerifiedStateOnlyProfile22Openings<'a>>, Profile22VerifyError> {
    let roots = StateOnlyProfile22OpeningRoots {
        c1: *prefix.c1_root,
        c2: *prefix.c2_root,
        later: later_roots(prefix)?,
    };
    Ok(Box::new(verify_state_only_profile22_openings(
        hash,
        &roots,
        &schedule.queries[..schedule.query_count],
        suffix,
    )?))
}

pub fn verify_atomic_state_only_profile22_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile22Trace>,
) -> Result<VerifiedAtomicProfile22<'a>, Profile22VerifyError> {
    verify_atomic_state_only_profile22_inner_v3(proof, statement, hash, true, trace)
}

pub fn verify_atomic_state_only_profile22_unmined_for_diagnostics_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile22Trace>,
) -> Result<VerifiedAtomicProfile22<'a>, Profile22VerifyError> {
    verify_atomic_state_only_profile22_inner_v3(proof, statement, hash, false, trace)
}

fn verify_atomic_state_only_profile22_inner_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    check_pow: bool,
    trace: Option<Profile22Trace>,
) -> Result<VerifiedAtomicProfile22<'a>, Profile22VerifyError> {
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)
        .map_err(|_| Profile22VerifyError::StatementDigest)?;
    let (prefix, suffix) = StateOnlyCandidatePrefix::parse_from_proof(proof)?;
    if prefix.shape != STATE_ONLY_PROFILE22_PRIVATE_SHAPE {
        return Err(Profile22VerifyError::StatementValues);
    }
    traced(trace, Profile22TraceEvent::Parsed);
    let schedule = boxed_schedule(hash, &prefix, &statement_digest, check_pow)?;
    traced(trace, Profile22TraceEvent::Transcript);

    verify_profile22_terminal(&prefix, &schedule, statement)?;
    traced(trace, Profile22TraceEvent::Terminal);

    let relation = boxed_profile22_relation(&prefix, &schedule)?;
    traced(trace, Profile22TraceEvent::Relation);

    let openings = boxed_profile22_openings(hash, &prefix, &schedule, suffix)?;
    if PROFILE22_LAYER0_LEAF_COUNT != 1usize << 17 {
        return Err(Profile22VerifyError::MissingOpening);
    }
    traced(trace, Profile22TraceEvent::Openings);
    verify_profile22_queries(&prefix, &schedule, &relation, &openings, trace)?;
    traced(trace, Profile22TraceEvent::Complete);

    Ok(VerifiedAtomicProfile22 {
        prefix,
        schedule,
        relation,
        openings,
    })
}
