//! Complete verifier for quarantined spend (H26/G27/D28).

use alloc::{boxed::Box, vec::Vec};

#[cfg(feature = "spend-dynamic-rate512")]
use aspis_core::circle_fri::derive_query_fold_inverses_for_circle;
use aspis_core::circle_fri::{
    normalized_circle_to_line_arity4_prepared_polynomial_candidate, CircleFriError,
};
#[cfg(not(feature = "spend-dynamic-rate512"))]
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
    run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_spend_transcript_schedule_host_v3, StateOnlySpendPrefix,
    StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult,
    STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE, STATE_ONLY_STATEMENT_VALUE_COUNT,
};
use aspis_core::state_only_private_openings::StateOnlyPrivateOpening;
use aspis_core::state_only_spend_openings::{
    verify_state_only_spend_openings, StateOnlySpendOpeningError, StateOnlySpendOpeningRoots,
    VerifiedStateOnlySpendOpenings, SPEND_LAYER0_LEAF_COUNT,
};
use aspis_core::state_only_spend_query::{
    gamma_combine_state_only_spend_layer0_prepared, SPEND_C2_LEAF_BYTES,
};
use aspis_core::state_only_spend_relation::{
    prepare_state_only_spend_relation, StateOnlySpendRelationPrepared,
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
pub enum SpendTraceEvent {
    Parsed,
    Transcript,
    Terminal,
    Relation,
    Openings,
    Layer0Queries,
    LaterQueries,
    Complete,
}

pub type SpendTrace = fn(SpendTraceEvent);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpendVerifyError {
    Prefix(CandidatePrefixError),
    Transcript(StateOnlyTranscriptError),
    StatementDigest,
    StatementValues,
    Terminal(StateOnlyTerminalError),
    TerminalMismatch,
    Relation(StateOnlyRelationVerifyError),
    Opening(StateOnlySpendOpeningError),
    Query(CircleQueryError),
    MissingRoot,
    MissingOpening,
    NonCanonicalLater { offset: usize },
    FirstFoldMismatch { query: u32 },
}

macro_rules! from_error {
    ($source:ty, $variant:ident) => {
        impl From<$source> for SpendVerifyError {
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
from_error!(StateOnlySpendOpeningError, Opening);
from_error!(CircleQueryError, Query);

impl From<CircleFriError> for SpendVerifyError {
    fn from(error: CircleFriError) -> Self {
        Self::Query(CircleQueryError::Fold(error))
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedAtomicSpend<'a> {
    pub prefix: StateOnlySpendPrefix<'a>,
    pub schedule: Box<StateOnlyTranscriptScheduleResult>,
    pub relation: Box<StateOnlySpendRelationPrepared>,
    pub openings: Box<VerifiedStateOnlySpendOpenings<'a>>,
}

#[inline(always)]
fn traced(trace: Option<SpendTrace>, event: SpendTraceEvent) {
    if let Some(trace) = trace {
        trace(event);
    }
}

fn statement_values(
    prefix: &StateOnlySpendPrefix<'_>,
) -> Result<Box<[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS]>, SpendVerifyError> {
    if STATE_ONLY_SELECTED_TERMINAL_CLAIMS != STATE_ONLY_STATEMENT_VALUE_COUNT {
        return Err(SpendVerifyError::StatementValues);
    }
    let mut values = Vec::with_capacity(STATE_ONLY_SELECTED_TERMINAL_CLAIMS);
    for index in 0..STATE_ONLY_SELECTED_TERMINAL_CLAIMS {
        values.push(
            prefix
                .base
                .statement_evaluation(index)
                .ok_or(SpendVerifyError::StatementValues)?,
        );
    }
    values
        .into_boxed_slice()
        .try_into()
        .map_err(|_| SpendVerifyError::StatementValues)
}

fn later_roots(prefix: &StateOnlySpendPrefix<'_>) -> Result<[[u8; 32]; 3], SpendVerifyError> {
    let mut roots = [[0u8; 32]; 3];
    for (layer, root) in roots.iter_mut().enumerate() {
        *root = *prefix.base.rounds[layer + 1]
            .root
            .ok_or(SpendVerifyError::MissingRoot)?;
    }
    Ok(roots)
}

#[inline(always)]
fn opening_value_for_index<'a>(
    opening: &StateOnlyPrivateOpening<'a>,
    indices: &[u32],
    index: u32,
) -> Result<&'a [u8], SpendVerifyError> {
    let ordinal = indices
        .binary_search(&index)
        .map_err(|_| SpendVerifyError::MissingOpening)?;
    opening
        .value(ordinal)
        .ok_or(SpendVerifyError::MissingOpening)
}

fn verify_spend_queries(
    prefix: &StateOnlySpendPrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    relation: &StateOnlySpendRelationPrepared,
    openings: &VerifiedStateOnlySpendOpenings<'_>,
    inverse: fn(M31) -> M31,
    trace: Option<SpendTrace>,
) -> Result<(), SpendVerifyError> {
    let queries = &openings.indices.layer0;
    if queries.len() != STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE.query_count as usize
        || openings.c2.value_width != SPEND_C2_LEAF_BYTES
    {
        return Err(SpendVerifyError::MissingOpening);
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

    #[cfg(feature = "spend-dynamic-rate512")]
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
    #[cfg(not(feature = "spend-dynamic-rate512"))]
    let _ = inverse;

    for (ordinal, &query) in queries.iter().enumerate() {
        let c1 = openings
            .c1
            .value(ordinal)
            .ok_or(SpendVerifyError::MissingOpening)?;
        let c2 = openings
            .c2
            .value(ordinal)
            .ok_or(SpendVerifyError::MissingOpening)?;
        let combined =
            gamma_combine_state_only_spend_layer0_prepared(c1, c2, &relation.query_powers)?;
        #[cfg(feature = "spend-dynamic-rate512")]
        let [inv_2x, inv_2y] = *dynamic_coordinates
            .circle
            .get(ordinal)
            .ok_or(SpendVerifyError::MissingOpening)?;
        #[cfg(not(feature = "spend-dynamic-rate512"))]
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
                .ok_or(SpendVerifyError::MissingOpening)?,
        )
        .ok_or(SpendVerifyError::NonCanonicalLater { offset: start })?;
        if folded != expected {
            return Err(SpendVerifyError::FirstFoldMismatch { query });
        }
    }
    traced(trace, SpendTraceEvent::Layer0Queries);

    #[cfg(not(feature = "spend-dynamic-rate512"))]
    let line_tables: [&[u32]; 3] = [&RATE512_LINE1_INV, &RATE512_LINE2_INV, &RATE512_LINE3_INV];
    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .base
            .final_coefficient(coefficient)
            .ok_or(SpendVerifyError::StatementValues)?;
    }
    for layer in 0..3 {
        for (ordinal, &index) in openings.indices.later[layer].iter().enumerate() {
            let incoming = openings.later[layer]
                .value(ordinal)
                .ok_or(SpendVerifyError::MissingOpening)?;
            #[cfg(feature = "spend-dynamic-rate512")]
            let inverses = *dynamic_coordinates.later[layer]
                .get(ordinal)
                .ok_or(SpendVerifyError::MissingOpening)?;
            #[cfg(not(feature = "spend-dynamic-rate512"))]
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
                #[cfg(feature = "spend-dynamic-rate512")]
                let final_x = *dynamic_coordinates
                    .final_x
                    .get(ordinal)
                    .ok_or(SpendVerifyError::MissingOpening)?;
                #[cfg(not(feature = "spend-dynamic-rate512"))]
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
    traced(trace, SpendTraceEvent::LaterQueries);
    Ok(())
}

#[inline(never)]
fn boxed_spend_schedule(
    hash: HashFn,
    prefix: &StateOnlySpendPrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<Box<StateOnlyTranscriptScheduleResult>, SpendVerifyError> {
    let schedule = if check_pow {
        run_atomic_state_only_spend_transcript_schedule_host_v3(hash, prefix, statement_digest)?
    } else {
        run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3(
            hash,
            prefix,
            statement_digest,
        )?
    };
    Ok(Box::new(schedule))
}

#[inline(never)]
fn verify_terminal(
    prefix: &StateOnlySpendPrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    statement: &AtomicPaymentStatementV3,
) -> Result<(), SpendVerifyError> {
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
        return Err(SpendVerifyError::TerminalMismatch);
    }
    Ok(())
}

#[inline(never)]
fn boxed_spend_relation(
    prefix: &StateOnlySpendPrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Box<StateOnlySpendRelationPrepared>, SpendVerifyError> {
    let relation = prepare_state_only_spend_relation(
        schedule.prefix.gamma,
        prefix.base.statement_evaluations_bytes,
        prefix.d_claims_bytes,
    )
    .ok_or(SpendVerifyError::StatementValues)?;
    verify_state_only_relation_with_inactive_masks(
        &prefix.base,
        schedule,
        &relation.relation,
        atomic_state_only_copy_inactive_row_masks_v3(),
    )?;
    Ok(Box::new(relation))
}

#[inline(never)]
fn boxed_spend_openings<'a>(
    hash: HashFn,
    prefix: &StateOnlySpendPrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    suffix: &'a [u8],
) -> Result<Box<VerifiedStateOnlySpendOpenings<'a>>, SpendVerifyError> {
    let roots = StateOnlySpendOpeningRoots {
        c1: *prefix.base.c1_root,
        c2: *prefix.base.c2_root,
        later: later_roots(prefix)?,
    };
    Ok(Box::new(verify_state_only_spend_openings(
        hash,
        &roots,
        &schedule.queries[..schedule.query_count],
        suffix,
    )?))
}

pub fn verify_atomic_state_only_spend_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<SpendTrace>,
) -> Result<VerifiedAtomicSpend<'a>, SpendVerifyError> {
    verify_inner(proof, statement, hash, true, trace, M31::inv)
}

/// Production verifier with an injected base-field inversion backend.  The
/// dynamic-coordinate feature uses it once for the complete public query
/// forest; callers select an inversion implementation supported by their
/// runtime.
pub fn verify_atomic_state_only_spend_v3_with_inverse<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<SpendTrace>,
    inverse: fn(M31) -> M31,
) -> Result<VerifiedAtomicSpend<'a>, SpendVerifyError> {
    verify_inner(proof, statement, hash, true, trace, inverse)
}

pub fn verify_atomic_state_only_spend_unmined_for_diagnostics_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<SpendTrace>,
) -> Result<VerifiedAtomicSpend<'a>, SpendVerifyError> {
    verify_inner(proof, statement, hash, false, trace, M31::inv)
}

pub fn verify_atomic_state_only_spend_unmined_for_diagnostics_v3_with_inverse<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<SpendTrace>,
    inverse: fn(M31) -> M31,
) -> Result<VerifiedAtomicSpend<'a>, SpendVerifyError> {
    verify_inner(proof, statement, hash, false, trace, inverse)
}

fn verify_inner<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    check_pow: bool,
    trace: Option<SpendTrace>,
    inverse: fn(M31) -> M31,
) -> Result<VerifiedAtomicSpend<'a>, SpendVerifyError> {
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)
        .map_err(|_| SpendVerifyError::StatementDigest)?;
    let (prefix, suffix) = StateOnlySpendPrefix::parse_from_proof(proof)?;
    if prefix.base.shape != STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE {
        return Err(SpendVerifyError::StatementValues);
    }
    traced(trace, SpendTraceEvent::Parsed);
    let schedule = boxed_spend_schedule(hash, &prefix, &statement_digest, check_pow)?;
    traced(trace, SpendTraceEvent::Transcript);

    verify_terminal(&prefix, &schedule, statement)?;
    traced(trace, SpendTraceEvent::Terminal);

    let relation = boxed_spend_relation(&prefix, &schedule)?;
    traced(trace, SpendTraceEvent::Relation);

    let openings = boxed_spend_openings(hash, &prefix, &schedule, suffix)?;
    if SPEND_LAYER0_LEAF_COUNT != 1usize << 17 {
        return Err(SpendVerifyError::MissingOpening);
    }
    traced(trace, SpendTraceEvent::Openings);
    verify_spend_queries(&prefix, &schedule, &relation, &openings, inverse, trace)?;
    traced(trace, SpendTraceEvent::Complete);

    Ok(VerifiedAtomicSpend {
        prefix,
        schedule,
        relation,
        openings,
    })
}
