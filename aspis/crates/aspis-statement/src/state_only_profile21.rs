//! Complete atomic profile-21 acceptance boundary.
//!
//! Profile 21 keeps the ordinary width-28 layer-zero generator, stores the
//! source X/F circle fibers in the authenticated tail of C2, and replaces W1
//! by `Fold(W0) + Enc(U)`.  This verifier authenticates the five salted trees
//! and checks, at every transcript-derived q16 position,
//!
//! `Enc(U)(q) = Fold(F)(q) + delta Fold(X)(q)
//!            = W1(q) - Fold(W0)(q)`.

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
use aspis_core::state_only_masked_switch::{
    evaluate_masked_switch_logical_at_m31_four, masked_switch_query_x, MaskedSwitchVerifyError,
    MASKED_SWITCH_QUERY_COUNT,
};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_profile21_transcript_schedule_host_v3, StateOnlyProfile21Prefix,
    StateOnlyProfile21TranscriptScheduleResult, StateOnlyTranscriptError,
    STATE_ONLY_PROFILE21_SHAPE, STATE_ONLY_STATEMENT_VALUE_COUNT,
};
use aspis_core::state_only_profile21_openings::{
    verify_state_only_profile21_openings, StateOnlyProfile21OpeningError,
    StateOnlyProfile21OpeningRoots, VerifiedStateOnlyProfile21Openings,
    PROFILE21_LAYER0_LEAF_COUNT,
};
use aspis_core::state_only_query::{
    gamma_combine_state_only_layer0_prepared, STATE_ONLY_C2_LEAF_BYTES,
};
use aspis_core::state_only_relation::{prepare_state_only_relation, StateOnlyRelationPrepared};
use aspis_core::{state_only_private_openings::StateOnlyPrivateOpening, HashFn};

use crate::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_v3;
use crate::state_only_terminal::{StateOnlyTerminalError, STATE_ONLY_SELECTED_TERMINAL_CLAIMS};
use crate::state_only_verify::{
    verify_atomic_state_only_profile21_relation, StateOnlyRelationVerifyError,
};
use crate::{atomic_payment_statement_digest_v3, AtomicPaymentStatementV3};

const PROFILE21_C2_VALUE_BYTES: usize = 256;
const PROFILE21_SOURCE_FIBER_BYTES: usize = 4 * 16;
const PROFILE21_SOURCE_X_START: usize = STATE_ONLY_C2_LEAF_BYTES;
const PROFILE21_SOURCE_F_START: usize = PROFILE21_SOURCE_X_START + PROFILE21_SOURCE_FIBER_BYTES;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile21TraceEvent {
    ParseBase,
    TranscriptBase,
    Terminal,
    Relation,
    ExistingOpenings,
    ExistingQueries,
    SourceXfSharedC2,
    SourceWork,
    TranslatedSplice,
    DirectUQuery,
    FinalQueryWork,
    Complete,
}

pub type Profile21Trace = fn(Profile21TraceEvent);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile21VerifyError {
    Prefix(CandidatePrefixError),
    Transcript(StateOnlyTranscriptError),
    StatementDigest,
    StatementValues,
    Terminal(StateOnlyTerminalError),
    TerminalMismatch,
    Relation(StateOnlyRelationVerifyError),
    Opening(StateOnlyProfile21OpeningError),
    Query(CircleQueryError),
    Source(MaskedSwitchVerifyError),
    MissingRoot,
    MissingOpening,
    NonCanonicalSource { offset: usize },
    AffineQueryMismatch { query: u32 },
    TranslatedSpliceMismatch { query: u32 },
    DirectUQueryMismatch { query: u32 },
}

impl From<CandidatePrefixError> for Profile21VerifyError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}
impl From<StateOnlyTranscriptError> for Profile21VerifyError {
    fn from(error: StateOnlyTranscriptError) -> Self {
        Self::Transcript(error)
    }
}
impl From<StateOnlyTerminalError> for Profile21VerifyError {
    fn from(error: StateOnlyTerminalError) -> Self {
        Self::Terminal(error)
    }
}
impl From<StateOnlyRelationVerifyError> for Profile21VerifyError {
    fn from(error: StateOnlyRelationVerifyError) -> Self {
        Self::Relation(error)
    }
}
impl From<StateOnlyProfile21OpeningError> for Profile21VerifyError {
    fn from(error: StateOnlyProfile21OpeningError) -> Self {
        Self::Opening(error)
    }
}
impl From<CircleQueryError> for Profile21VerifyError {
    fn from(error: CircleQueryError) -> Self {
        Self::Query(error)
    }
}
impl From<MaskedSwitchVerifyError> for Profile21VerifyError {
    fn from(error: MaskedSwitchVerifyError) -> Self {
        Self::Source(error)
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedAtomicProfile21<'a> {
    pub prefix: StateOnlyProfile21Prefix<'a>,
    pub schedule: Box<StateOnlyProfile21TranscriptScheduleResult>,
    pub relation: Box<StateOnlyRelationPrepared>,
    pub openings: Box<VerifiedStateOnlyProfile21Openings<'a>>,
}

#[inline(always)]
fn traced(trace: Option<Profile21Trace>, event: Profile21TraceEvent) {
    if let Some(trace) = trace {
        trace(event);
    }
}

fn statement_values(
    prefix: &StateOnlyProfile21Prefix<'_>,
) -> Result<Box<[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS]>, Profile21VerifyError> {
    if STATE_ONLY_SELECTED_TERMINAL_CLAIMS != STATE_ONLY_STATEMENT_VALUE_COUNT {
        return Err(Profile21VerifyError::StatementValues);
    }
    let mut values = Vec::with_capacity(STATE_ONLY_SELECTED_TERMINAL_CLAIMS);
    for index in 0..STATE_ONLY_SELECTED_TERMINAL_CLAIMS {
        values.push(
            prefix
                .base
                .statement_evaluation(index)
                .ok_or(Profile21VerifyError::StatementValues)?,
        );
    }
    values
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Profile21VerifyError::StatementValues)
}

fn later_roots(
    prefix: &StateOnlyProfile21Prefix<'_>,
) -> Result<[[u8; 32]; 3], Profile21VerifyError> {
    let mut roots = [[0u8; 32]; 3];
    for (layer, root) in roots.iter_mut().enumerate() {
        *root = *prefix.base.rounds[layer + 1]
            .root
            .ok_or(Profile21VerifyError::MissingRoot)?;
    }
    Ok(roots)
}

#[inline(always)]
fn opening_value_for_index<'a>(
    opening: &StateOnlyPrivateOpening<'a>,
    indices: &[u32],
    index: u32,
) -> Result<&'a [u8], Profile21VerifyError> {
    let ordinal = indices
        .binary_search(&index)
        .map_err(|_| Profile21VerifyError::MissingOpening)?;
    opening
        .value(ordinal)
        .ok_or(Profile21VerifyError::MissingOpening)
}

fn decode_qm31_fiber(bytes: &[u8], base_offset: usize) -> Result<[QM31; 4], Profile21VerifyError> {
    let mut values = [QM31::ZERO; 4];
    for (slot, value) in values.iter_mut().enumerate() {
        let start = base_offset + slot * 16;
        *value = QM31::from_le_bytes(
            bytes
                .get(start..start + 16)
                .ok_or(Profile21VerifyError::MissingOpening)?,
        )
        .ok_or(Profile21VerifyError::NonCanonicalSource { offset: start })?;
    }
    Ok(values)
}

fn verify_profile21_queries(
    prefix: &StateOnlyProfile21Prefix<'_>,
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    relation: &StateOnlyRelationPrepared,
    openings: &VerifiedStateOnlyProfile21Openings<'_>,
    trace: Option<Profile21Trace>,
) -> Result<(), Profile21VerifyError> {
    let queries = &openings.indices.layer0;
    if queries.len() != MASKED_SWITCH_QUERY_COUNT {
        return Err(Profile21VerifyError::MissingOpening);
    }
    let alpha_values = schedule.base.alpha;
    let alpha_squared_values = alpha_values.map(QM31::square);
    let alpha: [PreparedQm31Multiplier; CANDIDATE_ROUND_COUNT] =
        alpha_values.map(PreparedQm31Multiplier::new);
    let alpha_squared: [PreparedQm31Multiplier; CANDIDATE_ROUND_COUNT] =
        alpha_squared_values.map(PreparedQm31Multiplier::new);
    let alpha_cubed: [PreparedQm31Multiplier; CANDIDATE_ROUND_COUNT] =
        core::array::from_fn(|round| {
            PreparedQm31Multiplier::new(alpha_squared_values[round].mul(alpha_values[round]))
        });

    let mut base_folded = [QM31::ZERO; MASKED_SWITCH_QUERY_COUNT];
    for (ordinal, &query) in queries.iter().enumerate() {
        let c1 = openings
            .c1
            .value(ordinal)
            .ok_or(Profile21VerifyError::MissingOpening)?;
        let c2 = openings
            .c2
            .value(ordinal)
            .ok_or(Profile21VerifyError::MissingOpening)?;
        if c2.len() != PROFILE21_C2_VALUE_BYTES {
            return Err(Profile21VerifyError::MissingOpening);
        }
        let combined = gamma_combine_state_only_layer0_prepared(
            c1,
            &c2[..STATE_ONLY_C2_LEAF_BYTES],
            &relation.query_powers,
        )?;
        base_folded[ordinal] = normalized_circle_to_line_arity4_prepared_polynomial_candidate(
            combined,
            alpha[0],
            alpha_squared[0],
            alpha_cubed[0],
            M31(RATE512_CIRCLE_INV_2X[query as usize]),
            M31(RATE512_CIRCLE_INV_2Y[query as usize]),
        );
    }
    traced(trace, Profile21TraceEvent::ExistingQueries);

    // This boundary marks entry into the already-authenticated widened-C2
    // tail. The following bucket is the raw X/F decoding, two circle folds,
    // and affine delta combination; the PoW predicate itself was necessarily
    // executed earlier as part of the causal transcript schedule.
    traced(trace, Profile21TraceEvent::SourceXfSharedC2);
    let mut source_combined = [QM31::ZERO; MASKED_SWITCH_QUERY_COUNT];
    for (ordinal, &query) in queries.iter().enumerate() {
        let c2 = openings
            .c2
            .value(ordinal)
            .ok_or(Profile21VerifyError::MissingOpening)?;
        let x = decode_qm31_fiber(c2, PROFILE21_SOURCE_X_START)?;
        let f = decode_qm31_fiber(c2, PROFILE21_SOURCE_F_START)?;
        let inv_x = M31(RATE512_CIRCLE_INV_2X[query as usize]);
        let inv_y = M31(RATE512_CIRCLE_INV_2Y[query as usize]);
        let x = normalized_circle_to_line_arity4_prepared_polynomial_candidate(
            x,
            alpha[0],
            alpha_squared[0],
            alpha_cubed[0],
            inv_x,
            inv_y,
        );
        let f = normalized_circle_to_line_arity4_prepared_polynomial_candidate(
            f,
            alpha[0],
            alpha_squared[0],
            alpha_cubed[0],
            inv_x,
            inv_y,
        );
        source_combined[ordinal] = f.add(schedule.delta.mul(x));
    }
    traced(trace, Profile21TraceEvent::SourceWork);

    let mut w1_values = [QM31::ZERO; MASKED_SWITCH_QUERY_COUNT];
    for ((ordinal, &query), &source) in queries.iter().enumerate().zip(&source_combined) {
        let leaf =
            opening_value_for_index(&openings.later[0], &openings.indices.later[0], query >> 2)?;
        let slot = (query & 3) as usize;
        let w1 = QM31::from_le_bytes(&leaf[slot * 16..slot * 16 + 16])
            .ok_or(Profile21VerifyError::NonCanonicalSource { offset: slot * 16 })?;
        if source != w1.sub(base_folded[ordinal]) {
            return Err(Profile21VerifyError::TranslatedSpliceMismatch { query });
        }
        w1_values[ordinal] = w1;
    }
    traced(trace, Profile21TraceEvent::TranslatedSplice);

    let logical_u = prefix.logical_u();
    let mut direct = [QM31::ZERO; MASKED_SWITCH_QUERY_COUNT];
    for (query_chunk, output_chunk) in queries.chunks_exact(4).zip(direct.chunks_exact_mut(4)) {
        let points = [
            masked_switch_query_x(query_chunk[0])?,
            masked_switch_query_x(query_chunk[1])?,
            masked_switch_query_x(query_chunk[2])?,
            masked_switch_query_x(query_chunk[3])?,
        ];
        output_chunk.copy_from_slice(&evaluate_masked_switch_logical_at_m31_four(
            &logical_u, points,
        ));
    }
    for (ordinal, &query) in queries.iter().enumerate() {
        if direct[ordinal] != source_combined[ordinal] {
            return Err(Profile21VerifyError::AffineQueryMismatch { query });
        }
        if direct[ordinal] != w1_values[ordinal].sub(base_folded[ordinal]) {
            return Err(Profile21VerifyError::DirectUQueryMismatch { query });
        }
    }
    traced(trace, Profile21TraceEvent::DirectUQuery);

    let line_tables: [&[u32]; 3] = [&RATE512_LINE1_INV, &RATE512_LINE2_INV, &RATE512_LINE3_INV];
    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .base
            .final_coefficient(coefficient)
            .ok_or(Profile21VerifyError::StatementValues)?;
    }
    for layer in 0..3 {
        for (ordinal, &index) in openings.indices.later[layer].iter().enumerate() {
            let incoming = openings.later[layer]
                .value(ordinal)
                .ok_or(Profile21VerifyError::MissingOpening)?;
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
    traced(trace, Profile21TraceEvent::FinalQueryWork);
    Ok(())
}

#[inline(never)]
fn boxed_profile21_schedule(
    hash: HashFn,
    prefix: &StateOnlyProfile21Prefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<Box<StateOnlyProfile21TranscriptScheduleResult>, Profile21VerifyError> {
    let schedule = if check_pow {
        run_atomic_state_only_profile21_transcript_schedule_host_v3(hash, prefix, statement_digest)?
    } else {
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            hash,
            prefix,
            statement_digest,
        )?
    };
    Ok(Box::new(schedule))
}

#[inline(never)]
fn verify_profile21_terminal(
    prefix: &StateOnlyProfile21Prefix<'_>,
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    statement: &AtomicPaymentStatementV3,
) -> Result<(), Profile21VerifyError> {
    let values = statement_values(prefix)?;
    let terminal = atomic_state_only_selected_masked_terminal_value_compiled_v3(
        statement,
        &values,
        &schedule.base.prefix.z,
        schedule.base.prefix.lambda,
        schedule.base.prefix.chi,
        schedule.base.prefix.batching.theta,
        &schedule.base.prefix.batching.zerocheck_point,
        schedule.base.prefix.batching.mu,
        schedule.base.prefix.eta,
    )?;
    if terminal != schedule.base.prefix.masked_terminal_claim {
        return Err(Profile21VerifyError::TerminalMismatch);
    }
    Ok(())
}

#[inline(never)]
fn boxed_profile21_relation(
    prefix: &StateOnlyProfile21Prefix<'_>,
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
) -> Result<Box<StateOnlyRelationPrepared>, Profile21VerifyError> {
    let relation = prepare_state_only_relation(
        schedule.base.prefix.gamma,
        prefix.base.statement_evaluations_bytes,
    )
    .ok_or(Profile21VerifyError::StatementValues)?;
    verify_atomic_state_only_profile21_relation(
        &prefix.base,
        &schedule.base,
        &relation,
        prefix.tau(),
    )?;
    Ok(Box::new(relation))
}

#[inline(never)]
fn boxed_profile21_openings<'a>(
    hash: HashFn,
    prefix: &StateOnlyProfile21Prefix<'_>,
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    suffix: &'a [u8],
) -> Result<Box<VerifiedStateOnlyProfile21Openings<'a>>, Profile21VerifyError> {
    let roots = StateOnlyProfile21OpeningRoots {
        c1: *prefix.base.c1_root,
        c2: *prefix.base.c2_root,
        later: later_roots(prefix)?,
    };
    Ok(Box::new(verify_state_only_profile21_openings(
        hash,
        &roots,
        &schedule.base.queries[..schedule.base.query_count],
        suffix,
    )?))
}

pub fn verify_atomic_state_only_profile21_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile21Trace>,
) -> Result<VerifiedAtomicProfile21<'a>, Profile21VerifyError> {
    verify_atomic_state_only_profile21_inner_v3(proof, statement, hash, true, trace)
}

pub fn verify_atomic_state_only_profile21_unmined_for_diagnostics_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<Profile21Trace>,
) -> Result<VerifiedAtomicProfile21<'a>, Profile21VerifyError> {
    verify_atomic_state_only_profile21_inner_v3(proof, statement, hash, false, trace)
}

fn verify_atomic_state_only_profile21_inner_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    check_pow: bool,
    trace: Option<Profile21Trace>,
) -> Result<VerifiedAtomicProfile21<'a>, Profile21VerifyError> {
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)
        .map_err(|_| Profile21VerifyError::StatementDigest)?;
    let (prefix, suffix) = StateOnlyProfile21Prefix::parse_from_proof(proof)?;
    if prefix.base.shape != STATE_ONLY_PROFILE21_SHAPE {
        return Err(Profile21VerifyError::StatementValues);
    }
    traced(trace, Profile21TraceEvent::ParseBase);
    let schedule = boxed_profile21_schedule(hash, &prefix, &statement_digest, check_pow)?;
    traced(trace, Profile21TraceEvent::TranscriptBase);

    verify_profile21_terminal(&prefix, &schedule, statement)?;
    traced(trace, Profile21TraceEvent::Terminal);

    let relation = boxed_profile21_relation(&prefix, &schedule)?;
    traced(trace, Profile21TraceEvent::Relation);

    let openings = boxed_profile21_openings(hash, &prefix, &schedule, suffix)?;
    if PROFILE21_LAYER0_LEAF_COUNT != 1usize << 17 {
        return Err(Profile21VerifyError::MissingOpening);
    }
    traced(trace, Profile21TraceEvent::ExistingOpenings);
    verify_profile21_queries(&prefix, &schedule, &relation, &openings, trace)?;
    traced(trace, Profile21TraceEvent::Complete);

    Ok(VerifiedAtomicProfile21 {
        prefix,
        schedule,
        relation,
        openings,
    })
}
