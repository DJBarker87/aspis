//! Complete verifier for quarantined profile 23 (H26/G27/D28).

use alloc::{boxed::Box, vec::Vec};

#[cfg(feature = "profile23-dynamic-rate512")]
use aspis_core::circle_fri::derive_query_fold_inverses_for_circle;
use aspis_core::circle_fri::{
    normalized_circle_to_line_arity4_prepared_polynomial_candidate, CircleFriError,
};
#[cfg(not(feature = "profile23-dynamic-rate512"))]
use aspis_core::circle_fri::{
    RATE512_CIRCLE_INV_2X, RATE512_CIRCLE_INV_2Y, RATE512_FINAL_X, RATE512_LINE1_INV,
    RATE512_LINE2_INV, RATE512_LINE3_INV,
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
    run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_profile23_transcript_schedule_host_v3, StateOnlyProfile23Prefix,
    StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult,
    STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE, STATE_ONLY_STATEMENT_VALUE_COUNT,
};
use aspis_core::state_only_private_openings::StateOnlyPrivateOpening;
use aspis_core::state_only_profile23_openings::{
    verify_state_only_profile23_openings, StateOnlyProfile23OpeningError,
    StateOnlyProfile23OpeningRoots, VerifiedStateOnlyProfile23Openings,
    PROFILE23_LAYER0_LEAF_COUNT,
};
use aspis_core::state_only_profile23_query::{
    gamma_combine_state_only_profile23_layer0_prepared, PROFILE23_C2_LEAF_BYTES,
};
use aspis_core::state_only_profile23_relation::{
    prepare_state_only_profile23_relation, StateOnlyProfile23RelationPrepared,
};
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
pub enum Profile23TraceEvent {
    Parsed,
    Transcript,
    Terminal,
    Relation,
    Openings,
    Layer0Queries,
    LaterQueries,
    Complete,
}

pub type Profile23Trace = fn(Profile23TraceEvent);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile23VerifyError {
    Prefix(CandidatePrefixError),
    Transcript(StateOnlyTranscriptError),
    StatementDigest,
    StatementValues,
    Terminal(StateOnlyTerminalError),
    TerminalMismatch,
    Relation(StateOnlyRelationVerifyError),
    Opening(StateOnlyProfile23OpeningError),
    Query(CircleQueryError),
    MissingRoot,
    MissingOpening,
    NonCanonicalLater { offset: usize },
    FirstFoldMismatch { query: u32 },
}

macro_rules! from_error {
    ($source:ty, $variant:ident) => {
        impl From<$source> for Profile23VerifyError {
            fn from(value: $source) -> Self {
                Self::$variant(value)
            }
        }
    };
}
from_error!(CandidatePrefixError, Prefix);
from_error!(StateOnlyTranscriptError, Transcript);
from_error!(StateOnlyTerminalError, Terminal);
from_error!(StateOnlyRelationVerifyError, Relation);
from_error!(StateOnlyProfile23OpeningError, Opening);
from_error!(CircleQueryError, Query);

impl From<CircleFriError> for Profile23VerifyError {
    fn from(error: CircleFriError) -> Self {
        Self::Query(CircleQueryError::Fold(error))
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedAtomicProfile23<'a> {
    pub prefix: StateOnlyProfile23Prefix<'a>,
    pub schedule: Box<StateOnlyTranscriptScheduleResult>,
    pub relation: Box<StateOnlyProfile23RelationPrepared>,
    pub openings: Box<VerifiedStateOnlyProfile23Openings<'a>>,
}

#[inline(always)]
fn traced(trace: Option<Profile23Trace>, event: Profile23TraceEvent) {
    if let Some(trace) = trace {
        trace(event);
    }
}

fn statement_values(
    prefix: &StateOnlyProfile23Prefix<'_>,
) -> Result<Box<[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS]>, Profile23VerifyError> {
    if STATE_ONLY_SELECTED_TERMINAL_CLAIMS != STATE_ONLY_STATEMENT_VALUE_COUNT {
        return Err(Profile23VerifyError::StatementValues);
    }
    let mut values = Vec::with_capacity(STATE_ONLY_SELECTED_TERMINAL_CLAIMS);
    for index in 0..STATE_ONLY_SELECTED_TERMINAL_CLAIMS {
        values.push(
            prefix
                .base
                .statement_evaluation(index)
                .ok_or(Profile23VerifyError::StatementValues)?,
        );
    }
    values
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Profile23VerifyError::StatementValues)
}

fn later_roots(
    prefix: &StateOnlyProfile23Prefix<'_>,
) -> Result<[[u8; 32]; 3], Profile23VerifyError> {
    let mut roots = [[0u8; 32]; 3];
    for (layer, root) in roots.iter_mut().enumerate() {
        *root = *prefix.base.rounds[layer + 1]
            .root
            .ok_or(Profile23VerifyError::MissingRoot)?;
    }
    Ok(roots)
}

#[inline(always)]
fn opening_value_for_index<'a>(
    opening: &StateOnlyPrivateOpening<'a>,
    indices: &[u32],
    index: u32,
) -> Result<&'a [u8], Profile23VerifyError> {
    let ordinal = indices
        .binary_search(&index)
        .map_err(|_| Profile23VerifyError::MissingOpening)?;
    opening
        .value(ordinal)
        .ok_or(Profile23VerifyError::MissingOpening)
}

fn verify_profile23_queries(
    prefix: &StateOnlyProfile23Prefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    relation: &StateOnlyProfile23RelationPrepared,
    openings: &VerifiedStateOnlyProfile23Openings<'_>,
    inverse: fn(M31) -> M31,
    trace: Option<Profile23Trace>,
) -> Result<(), Profile23VerifyError> {
    let queries = &openings.indices.layer0;
    if queries.len() != STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE.query_count as usize
        || openings.c2.value_width != PROFILE23_C2_LEAF_BYTES
    {
        return Err(Profile23VerifyError::MissingOpening);
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

    #[cfg(feature = "profile23-dynamic-rate512")]
    let dynamic_coordinates = derive_query_fold_inverses_for_circle(
        19,
        queries,
        [
            &openings.indices.later[0],
            &openings.indices.later[1],
            &openings.indices.later[2],
        ],
        inverse,
    )?;
    #[cfg(not(feature = "profile23-dynamic-rate512"))]
    let _ = inverse;

    for (ordinal, &query) in queries.iter().enumerate() {
        let c1 = openings
            .c1
            .value(ordinal)
            .ok_or(Profile23VerifyError::MissingOpening)?;
        let c2 = openings
            .c2
            .value(ordinal)
            .ok_or(Profile23VerifyError::MissingOpening)?;
        let combined =
            gamma_combine_state_only_profile23_layer0_prepared(c1, c2, &relation.query_powers)?;
        #[cfg(feature = "profile23-dynamic-rate512")]
        let [inv_2x, inv_2y] = *dynamic_coordinates
            .circle
            .get(ordinal)
            .ok_or(Profile23VerifyError::MissingOpening)?;
        #[cfg(not(feature = "profile23-dynamic-rate512"))]
        let (inv_2x, inv_2y) = (
            M31(RATE512_CIRCLE_INV_2X[query as usize]),
            M31(RATE512_CIRCLE_INV_2Y[query as usize]),
        );
        let folded = normalized_circle_to_line_arity4_prepared_polynomial_candidate(
            combined,
            alpha[0],
            alpha_squared[0],
            alpha_cubed[0],
            inv_2x,
            inv_2y,
        );
        let w1 =
            opening_value_for_index(&openings.later[0], &openings.indices.later[0], query >> 2)?;
        let start = (query & 3) as usize * 16;
        let expected = QM31::from_le_bytes(
            w1.get(start..start + 16)
                .ok_or(Profile23VerifyError::MissingOpening)?,
        )
        .ok_or(Profile23VerifyError::NonCanonicalLater { offset: start })?;
        if folded != expected {
            return Err(Profile23VerifyError::FirstFoldMismatch { query });
        }
    }
    traced(trace, Profile23TraceEvent::Layer0Queries);

    #[cfg(not(feature = "profile23-dynamic-rate512"))]
    let line_tables: [&[u32]; 3] = [&RATE512_LINE1_INV, &RATE512_LINE2_INV, &RATE512_LINE3_INV];
    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .base
            .final_coefficient(coefficient)
            .ok_or(Profile23VerifyError::StatementValues)?;
    }
    for layer in 0..3 {
        for (ordinal, &index) in openings.indices.later[layer].iter().enumerate() {
            let incoming = openings.later[layer]
                .value(ordinal)
                .ok_or(Profile23VerifyError::MissingOpening)?;
            #[cfg(feature = "profile23-dynamic-rate512")]
            let inverses = *dynamic_coordinates.later[layer]
                .get(ordinal)
                .ok_or(Profile23VerifyError::MissingOpening)?;
            #[cfg(not(feature = "profile23-dynamic-rate512"))]
            let inverses = {
                let offset = index as usize * 3;
                [
                    M31(line_tables[layer][offset]),
                    M31(line_tables[layer][offset + 1]),
                    M31(line_tables[layer][offset + 2]),
                ]
            };
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
                #[cfg(feature = "profile23-dynamic-rate512")]
                let final_x = *dynamic_coordinates
                    .final_x
                    .get(ordinal)
                    .ok_or(Profile23VerifyError::MissingOpening)?;
                #[cfg(not(feature = "profile23-dynamic-rate512"))]
                let final_x = M31(RATE512_FINAL_X[index as usize]);
                check_fixed_terminal_transition_prepared_polynomial(
                    incoming,
                    final_coefficients,
                    index as usize,
                    inverses,
                    final_x,
                    alpha[3],
                    alpha_squared[3],
                    alpha_cubed[3],
                )?;
            }
        }
    }
    traced(trace, Profile23TraceEvent::LaterQueries);
    Ok(())
}

#[inline(never)]
fn boxed_profile23_schedule(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<Box<StateOnlyTranscriptScheduleResult>, Profile23VerifyError> {
    let schedule = if check_pow {
        run_atomic_state_only_profile23_transcript_schedule_host_v3(hash, prefix, statement_digest)?
    } else {
        run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
            hash,
            prefix,
            statement_digest,
        )?
    };
    Ok(Box::new(schedule))
}

#[inline(never)]
fn verify_terminal(
    prefix: &StateOnlyProfile23Prefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    statement: &AtomicPaymentStatementV3,
) -> Result<(), Profile23VerifyError> {
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
        return Err(Profile23VerifyError::TerminalMismatch);
    }
    Ok(())
}

#[inline(never)]
fn boxed_profile23_relation(
    prefix: &StateOnlyProfile23Prefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Box<StateOnlyProfile23RelationPrepared>, Profile23VerifyError> {
    let relation = prepare_state_only_profile23_relation(
        schedule.prefix.gamma,
        prefix.base.statement_evaluations_bytes,
        prefix.d_claims_bytes,
    )
    .ok_or(Profile23VerifyError::StatementValues)?;
    verify_state_only_relation_with_inactive_masks(
        &prefix.base,
        schedule,
        &relation.relation,
        atomic_state_only_copy_inactive_row_masks_v3(),
    )?;
    Ok(Box::new(relation))
}

#[inline(never)]
fn boxed_profile23_openings<'a>(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    suffix: &'a [u8],
) -> Result<Box<VerifiedStateOnlyProfile23Openings<'a>>, Profile23VerifyError> {
    let roots = StateOnlyProfile23OpeningRoots {
        c1: *prefix.base.c1_root,
        c2: *prefix.base.c2_root,
        later: later_roots(prefix)?,
    };
    Ok(Box::new(verify_state_only_profile23_openings(
        hash,
        &roots,
        &schedule.queries[..schedule.query_count],
        suffix,
    )?))
}

pub fn verify_atomic_state_only_profile23_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile23Trace>,
) -> Result<VerifiedAtomicProfile23<'a>, Profile23VerifyError> {
    verify_inner(proof, statement, hash, true, trace, M31::inv)
}

/// Production verifier with an injected base-field inversion backend.  The
/// dynamic-coordinate feature uses it once for the complete public query
/// forest; SBF callers can supply `sol_big_mod_exp`, while host callers keep
/// [`M31::inv`].
pub fn verify_atomic_state_only_profile23_v3_with_inverse<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile23Trace>,
    inverse: fn(M31) -> M31,
) -> Result<VerifiedAtomicProfile23<'a>, Profile23VerifyError> {
    verify_inner(proof, statement, hash, true, trace, inverse)
}

pub fn verify_atomic_state_only_profile23_unmined_for_diagnostics_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile23Trace>,
) -> Result<VerifiedAtomicProfile23<'a>, Profile23VerifyError> {
    verify_inner(proof, statement, hash, false, trace, M31::inv)
}

pub fn verify_atomic_state_only_profile23_unmined_for_diagnostics_v3_with_inverse<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile23Trace>,
    inverse: fn(M31) -> M31,
) -> Result<VerifiedAtomicProfile23<'a>, Profile23VerifyError> {
    verify_inner(proof, statement, hash, false, trace, inverse)
}

fn verify_inner<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    check_pow: bool,
    trace: Option<Profile23Trace>,
    inverse: fn(M31) -> M31,
) -> Result<VerifiedAtomicProfile23<'a>, Profile23VerifyError> {
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)
        .map_err(|_| Profile23VerifyError::StatementDigest)?;
    let (prefix, suffix) = StateOnlyProfile23Prefix::parse_from_proof(proof)?;
    if prefix.base.shape != STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE {
        return Err(Profile23VerifyError::StatementValues);
    }
    traced(trace, Profile23TraceEvent::Parsed);
    let schedule = boxed_profile23_schedule(hash, &prefix, &statement_digest, check_pow)?;
    traced(trace, Profile23TraceEvent::Transcript);

    verify_terminal(&prefix, &schedule, statement)?;
    traced(trace, Profile23TraceEvent::Terminal);

    let relation = boxed_profile23_relation(&prefix, &schedule)?;
    traced(trace, Profile23TraceEvent::Relation);

    let openings = boxed_profile23_openings(hash, &prefix, &schedule, suffix)?;
    if PROFILE23_LAYER0_LEAF_COUNT != 1usize << 17 {
        return Err(Profile23VerifyError::MissingOpening);
    }
    traced(trace, Profile23TraceEvent::Openings);
    verify_profile23_queries(&prefix, &schedule, &relation, &openings, inverse, trace)?;
    traced(trace, Profile23TraceEvent::Complete);

    Ok(VerifiedAtomicProfile23 {
        prefix,
        schedule,
        relation,
        openings,
    })
}
