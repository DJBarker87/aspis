//! Production-neutral composition of the complete state-only verifier.
//!
//! The profile is selected by the transcript-bound header.  Both rate 1/16
//! and rate 1/32 execute the same relation and terminal equations; only the
//! authenticated circle geometry and query count differ.

use alloc::{boxed::Box, vec::Vec};

use aspis_core::circle_fri::FIXED_TRACE_LOG_SIZE;
use aspis_core::circle_line_merkle::{
    CircleOpeningGeometry, RATE16_CIRCLE_OPENING_GEOMETRY, RATE32_CIRCLE_OPENING_GEOMETRY,
    RATE512_CIRCLE_OPENING_GEOMETRY,
};
use aspis_core::circle_openings::{
    verify_state_only_circle_openings_for_geometry, CircleOpeningsError, CircleQuerySegment,
    VerifiedCircleOpenings,
};
use aspis_core::circle_prefix::{
    CandidatePrefixError, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::QM31;
use aspis_core::state_only_prefix::run_state_only_transcript_schedule_host_unmined_for_diagnostics;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_transcript_schedule_host_v3, run_state_only_transcript_schedule_host,
    StateOnlyCandidatePrefix, StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult,
    STATE_ONLY_RATE16_SHAPE, STATE_ONLY_RATE32_SHAPE, STATE_ONLY_RATE512_SHAPE,
    STATE_ONLY_STATEMENT_VALUE_COUNT,
};
use aspis_core::state_only_query::StateOnlyQueryPowers;
use aspis_core::state_only_relation::{prepare_state_only_relation, StateOnlyRelationPrepared};
use aspis_core::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
    SUMCHECK_COEFFICIENTS,
};
use aspis_core::HashFn;

use crate::state_only_poseidon::{successor_point, xor12_point};
use crate::state_only_terminal::{
    state_only_copy_inactive_row_masks_v4, state_only_selected_masked_terminal_value_compiled,
    state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace,
    state_only_selected_unmasked_terminal_value_compiled, StateOnlyTerminalDiagnosticPhase,
    StateOnlyTerminalError, STATE_ONLY_SELECTED_TERMINAL_CLAIMS,
};
use crate::{AtomicPaymentStatementV3, SpendPublic};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyRelationVerifyError {
    PrefixShape,
    WeightShape(TensorWeightError),
    BoundaryMismatch { round: usize },
    Profile21TargetMismatch,
    TerminalMismatch,
}

impl From<TensorWeightError> for StateOnlyRelationVerifyError {
    fn from(error: TensorWeightError) -> Self {
        Self::WeightShape(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyCandidateVerifyError {
    Prefix(CandidatePrefixError),
    Transcript(StateOnlyTranscriptError),
    StatementValues,
    Relation(StateOnlyRelationVerifyError),
    Terminal(StateOnlyTerminalError),
    TerminalMismatch,
    Openings(CircleOpeningsError),
}

impl From<CandidatePrefixError> for StateOnlyCandidateVerifyError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}

impl From<StateOnlyTranscriptError> for StateOnlyCandidateVerifyError {
    fn from(error: StateOnlyTranscriptError) -> Self {
        Self::Transcript(error)
    }
}

impl From<StateOnlyRelationVerifyError> for StateOnlyCandidateVerifyError {
    fn from(error: StateOnlyRelationVerifyError) -> Self {
        Self::Relation(error)
    }
}

impl From<StateOnlyTerminalError> for StateOnlyCandidateVerifyError {
    fn from(error: StateOnlyTerminalError) -> Self {
        Self::Terminal(error)
    }
}

impl From<CircleOpeningsError> for StateOnlyCandidateVerifyError {
    fn from(error: CircleOpeningsError) -> Self {
        Self::Openings(error)
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedStateOnlyCandidate<'a> {
    pub prefix: StateOnlyCandidatePrefix<'a>,
    pub schedule: Box<StateOnlyTranscriptScheduleResult>,
    pub relation: Box<StateOnlyRelationPrepared>,
    pub openings: Box<VerifiedCircleOpenings<'a>>,
}

/// Named boundaries in the complete state-only verifier. The optional trace
/// hook used by diagnostics observes completed phases only; it cannot change
/// the acceptance predicate or skip any check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyVerifyPhase {
    Parsed,
    Transcript,
    Terminal,
    Relation,
    OpeningsParsed,
    QueriesDone,
    TerminalPrepared,
    TerminalPoseidon,
    TerminalSemanticInitial,
    TerminalSemanticAbsorption,
    TerminalSemanticMerkle,
    TerminalSemanticRange,
    TerminalSemanticPublic,
    TerminalCopyPatterns,
    TerminalCopyRouting,
    TerminalCopy,
    TerminalCompositionEquality,
    TerminalMask,
    TerminalFinal,
}

pub type StateOnlyVerifyTrace = fn(StateOnlyVerifyPhase);

/// Fine-grained markers for the append-only relation-structure A/B.  This
/// diagnostic changes no transcript or proof bytes; it exposes where the
/// exact public-covector specialization saves verifier work.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyRelationStructuralPhase {
    Parsed,
    Transcript,
    Prepared,
    PointWeights,
    Round0,
    Round1,
    Round2,
    Round3,
    Final,
}

pub type StateOnlyRelationStructuralTrace = fn(StateOnlyRelationStructuralPhase);

/// Read-only partitions used to price a verifier that exceeds one SBF meter.
/// Every partition parses the same proof and executes the same unmined
/// transcript schedule; no partition is an acceptance boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyVerifyDiagnosticPhase {
    PreparedBase,
    Terminal,
    Relation,
    Openings,
    Queries,
    QueryLayer0,
    QueryLaterAll,
    TerminalBreakdown,
    TerminalNoMask,
}

pub const fn state_only_geometry(
    prefix: &StateOnlyCandidatePrefix<'_>,
) -> Option<CircleOpeningGeometry> {
    if prefix.shape.profile_id == STATE_ONLY_RATE16_SHAPE.profile_id {
        Some(RATE16_CIRCLE_OPENING_GEOMETRY)
    } else if prefix.shape.profile_id == STATE_ONLY_RATE32_SHAPE.profile_id {
        Some(RATE32_CIRCLE_OPENING_GEOMETRY)
    } else if prefix.shape.profile_id == STATE_ONLY_RATE512_SHAPE.profile_id {
        Some(RATE512_CIRCLE_OPENING_GEOMETRY)
    } else {
        None
    }
}

/// Verify the three point claims, two OOD samples at every fold, and the
/// natural final tensor polynomial against the four relation sumchecks.
pub fn verify_state_only_relation(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    prepared: &StateOnlyRelationPrepared,
) -> Result<(), StateOnlyRelationVerifyError> {
    verify_state_only_relation_with_inactive_masks(
        prefix,
        schedule,
        prepared,
        state_only_copy_inactive_row_masks_v4(),
    )
}

pub fn verify_state_only_relation_with_inactive_masks(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    prepared: &StateOnlyRelationPrepared,
    inactive_masks: [u16; 64],
) -> Result<(), StateOnlyRelationVerifyError> {
    verify_state_only_relation_inner(prefix, schedule, prepared, inactive_masks, true, None, None)
}

/// Literal pre-specialization relation evaluator retained as an independent
/// differential reference. Production callers use
/// [`verify_state_only_relation_with_inactive_masks`].
#[doc(hidden)]
pub fn verify_state_only_relation_with_inactive_masks_legacy_reference(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    prepared: &StateOnlyRelationPrepared,
    inactive_masks: [u16; 64],
) -> Result<(), StateOnlyRelationVerifyError> {
    verify_state_only_relation_inner(
        prefix,
        schedule,
        prepared,
        inactive_masks,
        false,
        None,
        None,
    )
}

#[derive(Clone, Copy)]
struct Profile21RelationInjection {
    tau: QM31,
}

fn profile21_claimed_seam_target(profile21: Profile21RelationInjection) -> QM31 {
    profile21.tau
}

/// Verify the atomic profile-21 relation with the masked-switch splice after
/// round zero. `tau` is committed after the nonzero delta and disclosed U,
/// and denotes the complete folded-relation target of U, including all
/// sixteen randomness coordinates. The verifier adds tau before accepting
/// either round-one OOD value.
///
/// The scalars are prover claims, not independently recomputed targets. Their
/// binding is the existing post-final q16 equality
/// `W1(q)-Fold(W0)(q)=Enc(U)(q)=F(q)+delta*X(q)`: conditioned on ordinary and
/// source list events, a false claimed seam leaves a nonzero degree-<256
/// difference polynomial and can pass only when every q16 position lies in
/// its agreement set. No logical-to-natural transform is on the production
/// verifier path, while the ordinary round-one OOD boundary is preserved
/// exactly.
pub fn verify_atomic_state_only_profile21_relation(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    prepared: &StateOnlyRelationPrepared,
    tau: QM31,
) -> Result<(), StateOnlyRelationVerifyError> {
    verify_state_only_relation_inner(
        prefix,
        schedule,
        prepared,
        crate::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3(),
        true,
        Some(Profile21RelationInjection { tau }),
        None,
    )
}

fn verify_state_only_relation_inner(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    prepared: &StateOnlyRelationPrepared,
    inactive_masks: [u16; 64],
    deferred_binary_copy: bool,
    profile21: Option<Profile21RelationInjection>,
    trace: Option<StateOnlyRelationStructuralTrace>,
) -> Result<(), StateOnlyRelationVerifyError> {
    let z = schedule.prefix.z;
    let points = [z, successor_point(&z), xor12_point(&z)];
    let kappa = schedule.prefix.point_scale;
    let point_scales = [QM31::ONE, kappa, kappa.square()];
    let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    for point in 0..3 {
        weights.add_multilinear(point_scales[point], Vec::from(points[point]))?;
    }
    let mut running_claim = if deferred_binary_copy {
        prepared.claims[0]
            .add(kappa.mul(prepared.claims[1]))
            .add(point_scales[2].mul(prepared.claims[2]))
    } else {
        point_scales
            .iter()
            .zip(prepared.claims)
            .fold(QM31::ZERO, |sum, (scale, claim)| sum.add(scale.mul(claim)))
    };
    if deferred_binary_copy {
        weights.add_grouped_64x16_binary_masks_deferred(inactive_masks)?;
    } else {
        weights.add_grouped_64x16_binary_masks(inactive_masks)?;
    }
    if let Some(trace) = trace {
        trace(StateOnlyRelationStructuralPhase::PointWeights);
    }

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let value = prefix.rounds[round]
                .ood_value(sample)
                .ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
            let mix = schedule.mu[round][sample];
            if round == 0 {
                weights.add_circle_tensor(mix, schedule.circle_ood_points[sample])?;
            } else {
                weights.add_line_tensor(mix, schedule.line_ood_points[round - 1][sample])?;
            }
            running_claim = running_claim.add(mix.mul(value));
        }

        let mut polynomial: SumcheckPolynomial = [QM31::ZERO; SUMCHECK_COEFFICIENTS];
        for (coefficient, output) in polynomial.iter_mut().enumerate() {
            *output = prefix.rounds[round]
                .sumcheck_coefficient(coefficient)
                .ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
        }
        if boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlyRelationVerifyError::BoundaryMismatch { round });
        }
        running_claim = evaluate(&polynomial, schedule.alpha[round]);
        weights.fold(schedule.alpha[round]);
        if round == 0 {
            if let Some(profile21) = profile21 {
                running_claim = running_claim.add(profile21_claimed_seam_target(profile21));
            }
        }
        if let Some(trace) = trace {
            trace(match round {
                0 => StateOnlyRelationStructuralPhase::Round0,
                1 => StateOnlyRelationStructuralPhase::Round1,
                2 => StateOnlyRelationStructuralPhase::Round2,
                3 => StateOnlyRelationStructuralPhase::Round3,
                _ => unreachable!(),
            });
        }
    }

    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
    }
    if weights.dot(&final_coefficients) != running_claim {
        return Err(StateOnlyRelationVerifyError::TerminalMismatch);
    }
    if let Some(trace) = trace {
        trace(StateOnlyRelationStructuralPhase::Final);
    }
    Ok(())
}

/// Append-only, read-only A/B of the exact profile-20 relation kernel.
///
/// `deferred_binary_copy=false` executes the current grouped-mask path;
/// `true` executes the identity-tested two-fold binary specialization.  The
/// optional corruption changes one prepared point claim only after transcript
/// derivation and succeeds exactly when the relation rejects it.  It cannot
/// authorize state and is not called by the production verifier.
pub fn verify_state_only_relation_structural_probe_unmined_traced(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    deferred_binary_copy: bool,
    corrupt_claim: bool,
    trace: StateOnlyRelationStructuralTrace,
) -> Result<(), StateOnlyCandidateVerifyError> {
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(proof)?;
    if prefix.shape != STATE_ONLY_RATE512_SHAPE {
        return Err(StateOnlyRelationVerifyError::PrefixShape.into());
    }
    trace(StateOnlyRelationStructuralPhase::Parsed);
    let schedule = boxed_schedule(hash, &prefix, statement_digest, false)?;
    trace(StateOnlyRelationStructuralPhase::Transcript);
    let mut prepared =
        prepare_state_only_relation(schedule.prefix.gamma, prefix.statement_evaluations_bytes)
            .ok_or(StateOnlyCandidateVerifyError::StatementValues)?;
    trace(StateOnlyRelationStructuralPhase::Prepared);
    if corrupt_claim {
        prepared.claims[0] = prepared.claims[0].add(QM31::ONE);
    }
    let result = verify_state_only_relation_inner(
        &prefix,
        &schedule,
        &prepared,
        state_only_copy_inactive_row_masks_v4(),
        deferred_binary_copy,
        None,
        Some(trace),
    );
    if corrupt_claim {
        if result.is_err() {
            Ok(())
        } else {
            Err(StateOnlyRelationVerifyError::TerminalMismatch.into())
        }
    } else {
        result.map_err(Into::into)
    }
}

fn statement_values(
    prefix: &StateOnlyCandidatePrefix<'_>,
) -> Result<Box<[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS]>, StateOnlyCandidateVerifyError> {
    debug_assert_eq!(
        STATE_ONLY_SELECTED_TERMINAL_CLAIMS,
        STATE_ONLY_STATEMENT_VALUE_COUNT
    );
    let mut values = Vec::with_capacity(STATE_ONLY_SELECTED_TERMINAL_CLAIMS);
    for index in 0..STATE_ONLY_SELECTED_TERMINAL_CLAIMS {
        values.push(
            prefix
                .statement_evaluation(index)
                .ok_or(StateOnlyCandidateVerifyError::StatementValues)?,
        );
    }
    values
        .into_boxed_slice()
        .try_into()
        .map_err(|_| StateOnlyCandidateVerifyError::StatementValues)
}

#[inline(never)]
fn boxed_schedule(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<Box<StateOnlyTranscriptScheduleResult>, StateOnlyCandidateVerifyError> {
    let schedule = if check_pow {
        run_state_only_transcript_schedule_host(hash, prefix, statement_digest)?
    } else {
        run_state_only_transcript_schedule_host_unmined_for_diagnostics(
            hash,
            prefix,
            statement_digest,
        )?
    };
    Ok(Box::new(schedule))
}

#[inline(never)]
fn boxed_atomic_schedule_v3(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<Box<StateOnlyTranscriptScheduleResult>, StateOnlyCandidateVerifyError> {
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
fn verify_terminal_phase(
    public: &SpendPublic,
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<(), StateOnlyCandidateVerifyError> {
    let values = statement_values(prefix)?;
    let terminal = state_only_selected_masked_terminal_value_compiled(
        public,
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
        return Err(StateOnlyCandidateVerifyError::TerminalMismatch);
    }
    Ok(())
}

#[inline(never)]
fn verify_terminal_breakdown_phase(
    public: &SpendPublic,
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    trace: StateOnlyVerifyTrace,
) -> Result<(), StateOnlyCandidateVerifyError> {
    let values = statement_values(prefix)?;
    let terminal = state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace(
        public,
        &values,
        &schedule.prefix.z,
        schedule.prefix.lambda,
        schedule.prefix.chi,
        schedule.prefix.batching.theta,
        &schedule.prefix.batching.zerocheck_point,
        schedule.prefix.batching.mu,
        schedule.prefix.eta,
        |phase| {
            trace(match phase {
                StateOnlyTerminalDiagnosticPhase::Prepared => {
                    StateOnlyVerifyPhase::TerminalPrepared
                }
                StateOnlyTerminalDiagnosticPhase::Poseidon => {
                    StateOnlyVerifyPhase::TerminalPoseidon
                }
                StateOnlyTerminalDiagnosticPhase::SemanticInitial => {
                    StateOnlyVerifyPhase::TerminalSemanticInitial
                }
                StateOnlyTerminalDiagnosticPhase::SemanticAbsorption => {
                    StateOnlyVerifyPhase::TerminalSemanticAbsorption
                }
                StateOnlyTerminalDiagnosticPhase::SemanticMerkle => {
                    StateOnlyVerifyPhase::TerminalSemanticMerkle
                }
                StateOnlyTerminalDiagnosticPhase::SemanticRange => {
                    StateOnlyVerifyPhase::TerminalSemanticRange
                }
                StateOnlyTerminalDiagnosticPhase::SemanticPublic => {
                    StateOnlyVerifyPhase::TerminalSemanticPublic
                }
                StateOnlyTerminalDiagnosticPhase::CopyPatterns => {
                    StateOnlyVerifyPhase::TerminalCopyPatterns
                }
                StateOnlyTerminalDiagnosticPhase::CopyRouting => {
                    StateOnlyVerifyPhase::TerminalCopyRouting
                }
                StateOnlyTerminalDiagnosticPhase::Copy => StateOnlyVerifyPhase::TerminalCopy,
                StateOnlyTerminalDiagnosticPhase::CompositionEquality => {
                    StateOnlyVerifyPhase::TerminalCompositionEquality
                }
                StateOnlyTerminalDiagnosticPhase::Mask => StateOnlyVerifyPhase::TerminalMask,
                StateOnlyTerminalDiagnosticPhase::Final => StateOnlyVerifyPhase::TerminalFinal,
            })
        },
    )?;
    if terminal != schedule.prefix.masked_terminal_claim {
        return Err(StateOnlyCandidateVerifyError::TerminalMismatch);
    }
    Ok(())
}

#[inline(never)]
fn verify_terminal_no_mask_phase(
    public: &SpendPublic,
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<(), StateOnlyCandidateVerifyError> {
    let values = statement_values(prefix)?;
    let terminal = state_only_selected_unmasked_terminal_value_compiled(
        public,
        &values,
        &schedule.prefix.z,
        schedule.prefix.lambda,
        schedule.prefix.chi,
        schedule.prefix.batching.theta,
        &schedule.prefix.batching.zerocheck_point,
        schedule.prefix.batching.mu,
    )?;
    core::hint::black_box(terminal);
    Ok(())
}

#[inline(never)]
fn verify_relation_phase(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Box<StateOnlyRelationPrepared>, StateOnlyCandidateVerifyError> {
    let relation =
        prepare_state_only_relation(schedule.prefix.gamma, prefix.statement_evaluations_bytes)
            .ok_or(StateOnlyCandidateVerifyError::StatementValues)?;
    verify_state_only_relation(prefix, schedule, &relation)?;
    Ok(Box::new(relation))
}

#[inline(never)]
fn verify_atomic_relation_phase_v3(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Box<StateOnlyRelationPrepared>, StateOnlyCandidateVerifyError> {
    let relation =
        prepare_state_only_relation(schedule.prefix.gamma, prefix.statement_evaluations_bytes)
            .ok_or(StateOnlyCandidateVerifyError::StatementValues)?;
    verify_state_only_relation_with_inactive_masks(
        prefix,
        schedule,
        &relation,
        crate::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3(),
    )?;
    Ok(Box::new(relation))
}

#[inline(never)]
fn verify_openings_parse_phase<'a>(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    suffix: &'a [u8],
    schedule: &StateOnlyTranscriptScheduleResult,
    geometry: CircleOpeningGeometry,
) -> Result<Box<VerifiedCircleOpenings<'a>>, StateOnlyCandidateVerifyError> {
    let openings = verify_state_only_circle_openings_for_geometry(
        hash,
        prefix.c1_root,
        prefix.c2_root,
        &later_roots(prefix)?,
        &schedule.queries[..schedule.query_count],
        suffix,
        geometry,
    )?;
    Ok(Box::new(openings))
}

#[inline(never)]
fn verify_queries_phase(
    prefix: &StateOnlyCandidatePrefix<'_>,
    schedule: &StateOnlyTranscriptScheduleResult,
    query_powers: &StateOnlyQueryPowers,
    openings: &VerifiedCircleOpenings<'_>,
    geometry: CircleOpeningGeometry,
    segment: CircleQuerySegment,
) -> Result<(), StateOnlyCandidateVerifyError> {
    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
    }
    openings.check_state_only_query_segment_prepared_for_geometry(
        query_powers,
        schedule.alpha,
        final_coefficients,
        segment,
        geometry,
    )?;
    Ok(())
}

fn later_roots(
    prefix: &StateOnlyCandidatePrefix<'_>,
) -> Result<[[u8; 32]; 3], StateOnlyCandidateVerifyError> {
    let mut roots = [[0u8; 32]; 3];
    for (layer, root) in roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer + 1]
            .root
            .copied()
            .ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
    }
    Ok(roots)
}

/// Complete, production-neutral state-only acceptance boundary.  It checks
/// all work witnesses, the masked degree-27 terminal, the three-point PCS
/// relation, both layer-zero roots, all later roots, and every sampled query.
pub fn verify_state_only_candidate<'a>(
    proof: &'a [u8],
    public: &SpendPublic,
    statement_digest: &[u8; 32],
    hash: HashFn,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    verify_state_only_candidate_inner(proof, public, statement_digest, hash, true)
}

pub fn verify_state_only_candidate_unmined_for_diagnostics<'a>(
    proof: &'a [u8],
    public: &SpendPublic,
    statement_digest: &[u8; 32],
    hash: HashFn,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    verify_state_only_candidate_inner(proof, public, statement_digest, hash, false)
}

/// Complete diagnostic verifier with phase-boundary observations. As with the
/// ordinary diagnostic entrypoint, only PoW acceptance predicates are
/// bypassed; nonce absorption and every downstream check still execute.
pub fn verify_state_only_candidate_unmined_for_diagnostics_traced<'a>(
    proof: &'a [u8],
    public: &SpendPublic,
    statement_digest: &[u8; 32],
    hash: HashFn,
    trace: StateOnlyVerifyTrace,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    verify_state_only_candidate_inner_traced(
        proof,
        public,
        statement_digest,
        hash,
        false,
        Some(trace),
    )
}

/// Read-only profile-20 cost candidate for the atomic-v3 terminal.
///
/// This deliberately takes an externally supplied expected terminal because
/// the current proof builder still constructs the non-atomic zerocheck claim.
/// Consequently it is a diagnostic cost path, not an acceptance predicate.
/// It nevertheless parses one proof once, runs the complete atomic terminal,
/// and then checks the unchanged relation, openings, and every query without
/// executing the old terminal.
pub fn verify_state_only_atomic_terminal_cost_candidate_unmined_traced<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    statement_digest: &[u8; 32],
    expected_atomic_terminal: QM31,
    hash: HashFn,
    trace: StateOnlyVerifyTrace,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    let (prefix, suffix) = StateOnlyCandidatePrefix::parse_from_proof(proof)?;
    if prefix.shape != STATE_ONLY_RATE512_SHAPE {
        return Err(StateOnlyRelationVerifyError::PrefixShape.into());
    }
    let geometry = state_only_geometry(&prefix).ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
    trace(StateOnlyVerifyPhase::Parsed);
    let schedule = boxed_schedule(hash, &prefix, statement_digest, false)?;
    trace(StateOnlyVerifyPhase::Transcript);
    let values = statement_values(&prefix)?;
    let atomic_terminal =
        crate::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_v3(
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
    if atomic_terminal != expected_atomic_terminal {
        return Err(StateOnlyCandidateVerifyError::TerminalMismatch);
    }
    trace(StateOnlyVerifyPhase::Terminal);
    let relation = verify_relation_phase(&prefix, &schedule)?;
    trace(StateOnlyVerifyPhase::Relation);
    let openings = verify_openings_parse_phase(hash, &prefix, suffix, &schedule, geometry)?;
    trace(StateOnlyVerifyPhase::OpeningsParsed);
    verify_queries_phase(
        &prefix,
        &schedule,
        &relation.query_powers,
        &openings,
        geometry,
        CircleQuerySegment::Full,
    )?;
    trace(StateOnlyVerifyPhase::QueriesDone);
    Ok(VerifiedStateOnlyCandidate {
        prefix,
        schedule,
        relation,
        openings,
    })
}

/// Read-only acceptance boundary for the atomic same-private-path v3 proof.
/// Every atomic public field is hashed under the atomic statement domain
/// before the atomic hiding context, roots, and sumcheck challenges are drawn.
pub fn verify_atomic_state_only_candidate_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    verify_atomic_state_only_candidate_inner_v3(proof, statement, hash, true, None)
}

pub fn verify_atomic_state_only_candidate_unmined_for_diagnostics_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    trace: Option<StateOnlyVerifyTrace>,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    verify_atomic_state_only_candidate_inner_v3(proof, statement, hash, false, trace)
}

fn verify_atomic_state_only_candidate_inner_v3<'a>(
    proof: &'a [u8],
    statement: &AtomicPaymentStatementV3,
    hash: HashFn,
    check_pow: bool,
    trace: Option<StateOnlyVerifyTrace>,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    let statement_digest = crate::atomic_payment_statement_digest_v3(statement, hash)
        .map_err(|_| StateOnlyCandidateVerifyError::StatementValues)?;
    let (prefix, suffix) = StateOnlyCandidatePrefix::parse_from_proof(proof)?;
    if prefix.shape != STATE_ONLY_RATE512_SHAPE {
        return Err(StateOnlyRelationVerifyError::PrefixShape.into());
    }
    let geometry = state_only_geometry(&prefix).ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Parsed);
    }
    let schedule = boxed_atomic_schedule_v3(hash, &prefix, &statement_digest, check_pow)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Transcript);
    }
    let values = statement_values(&prefix)?;
    let terminal = if let Some(terminal_trace) = trace {
        crate::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace_v3(
            statement,
            &values,
            &schedule.prefix.z,
            schedule.prefix.lambda,
            schedule.prefix.chi,
            schedule.prefix.batching.theta,
            &schedule.prefix.batching.zerocheck_point,
            schedule.prefix.batching.mu,
            schedule.prefix.eta,
            |phase| {
                terminal_trace(match phase {
                    StateOnlyTerminalDiagnosticPhase::Prepared => StateOnlyVerifyPhase::TerminalPrepared,
                    StateOnlyTerminalDiagnosticPhase::Poseidon => StateOnlyVerifyPhase::TerminalPoseidon,
                    StateOnlyTerminalDiagnosticPhase::SemanticInitial => StateOnlyVerifyPhase::TerminalSemanticInitial,
                    StateOnlyTerminalDiagnosticPhase::SemanticAbsorption => StateOnlyVerifyPhase::TerminalSemanticAbsorption,
                    StateOnlyTerminalDiagnosticPhase::SemanticMerkle => StateOnlyVerifyPhase::TerminalSemanticMerkle,
                    StateOnlyTerminalDiagnosticPhase::SemanticRange => StateOnlyVerifyPhase::TerminalSemanticRange,
                    StateOnlyTerminalDiagnosticPhase::SemanticPublic => StateOnlyVerifyPhase::TerminalSemanticPublic,
                    StateOnlyTerminalDiagnosticPhase::CopyPatterns => StateOnlyVerifyPhase::TerminalCopyPatterns,
                    StateOnlyTerminalDiagnosticPhase::CopyRouting => StateOnlyVerifyPhase::TerminalCopyRouting,
                    StateOnlyTerminalDiagnosticPhase::Copy => StateOnlyVerifyPhase::TerminalCopy,
                    StateOnlyTerminalDiagnosticPhase::CompositionEquality => StateOnlyVerifyPhase::TerminalCompositionEquality,
                    StateOnlyTerminalDiagnosticPhase::Mask => StateOnlyVerifyPhase::TerminalMask,
                    StateOnlyTerminalDiagnosticPhase::Final => StateOnlyVerifyPhase::TerminalFinal,
                })
            },
        )?
    } else {
        crate::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_v3(
            statement,
            &values,
            &schedule.prefix.z,
            schedule.prefix.lambda,
            schedule.prefix.chi,
            schedule.prefix.batching.theta,
            &schedule.prefix.batching.zerocheck_point,
            schedule.prefix.batching.mu,
            schedule.prefix.eta,
        )?
    };
    if terminal != schedule.prefix.masked_terminal_claim {
        return Err(StateOnlyCandidateVerifyError::TerminalMismatch);
    }
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Terminal);
    }
    let relation = verify_atomic_relation_phase_v3(&prefix, &schedule)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Relation);
    }
    let openings = verify_openings_parse_phase(hash, &prefix, suffix, &schedule, geometry)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::OpeningsParsed);
    }
    verify_queries_phase(
        &prefix,
        &schedule,
        &relation.query_powers,
        &openings,
        geometry,
        CircleQuerySegment::Full,
    )?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::QueriesDone);
    }
    Ok(VerifiedStateOnlyCandidate {
        prefix,
        schedule,
        relation,
        openings,
    })
}

/// Execute one named, read-only verifier partition against an unmined proof.
/// Only PoW rejection is disabled. `Queries` authenticates the complete
/// suffix and then runs the exact all-query arithmetic; the marker between
/// those operations makes their costs independently observable.
pub fn verify_state_only_candidate_phase_unmined_for_diagnostics(
    proof: &[u8],
    public: &SpendPublic,
    statement_digest: &[u8; 32],
    hash: HashFn,
    phase: StateOnlyVerifyDiagnosticPhase,
    trace: StateOnlyVerifyTrace,
) -> Result<(), StateOnlyCandidateVerifyError> {
    let (prefix, suffix) = StateOnlyCandidatePrefix::parse_from_proof(proof)?;
    let geometry = state_only_geometry(&prefix).ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
    trace(StateOnlyVerifyPhase::Parsed);
    let schedule = boxed_schedule(hash, &prefix, statement_digest, false)?;
    trace(StateOnlyVerifyPhase::Transcript);
    match phase {
        StateOnlyVerifyDiagnosticPhase::PreparedBase => {}
        StateOnlyVerifyDiagnosticPhase::Terminal => {
            verify_terminal_phase(public, &prefix, &schedule)?;
            trace(StateOnlyVerifyPhase::Terminal);
        }
        StateOnlyVerifyDiagnosticPhase::TerminalBreakdown => {
            verify_terminal_breakdown_phase(public, &prefix, &schedule, trace)?;
        }
        StateOnlyVerifyDiagnosticPhase::TerminalNoMask => {
            verify_terminal_no_mask_phase(public, &prefix, &schedule)?;
            trace(StateOnlyVerifyPhase::Terminal);
        }
        StateOnlyVerifyDiagnosticPhase::Relation => {
            let _relation = verify_relation_phase(&prefix, &schedule)?;
            trace(StateOnlyVerifyPhase::Relation);
        }
        StateOnlyVerifyDiagnosticPhase::Openings => {
            let _openings =
                verify_openings_parse_phase(hash, &prefix, suffix, &schedule, geometry)?;
            trace(StateOnlyVerifyPhase::OpeningsParsed);
        }
        StateOnlyVerifyDiagnosticPhase::Queries
        | StateOnlyVerifyDiagnosticPhase::QueryLayer0
        | StateOnlyVerifyDiagnosticPhase::QueryLaterAll => {
            let query_powers = StateOnlyQueryPowers::new(schedule.prefix.gamma);
            let openings = verify_openings_parse_phase(hash, &prefix, suffix, &schedule, geometry)?;
            trace(StateOnlyVerifyPhase::OpeningsParsed);
            let segment = match phase {
                StateOnlyVerifyDiagnosticPhase::Queries => CircleQuerySegment::Full,
                StateOnlyVerifyDiagnosticPhase::QueryLayer0 => CircleQuerySegment::Layer0Range {
                    start: 0,
                    end: openings.later.indices.layer0.len(),
                },
                StateOnlyVerifyDiagnosticPhase::QueryLaterAll => CircleQuerySegment::LaterAll,
                _ => unreachable!(),
            };
            verify_queries_phase(
                &prefix,
                &schedule,
                &query_powers,
                &openings,
                geometry,
                segment,
            )?;
            trace(StateOnlyVerifyPhase::QueriesDone);
        }
    }
    Ok(())
}

fn verify_state_only_candidate_inner<'a>(
    proof: &'a [u8],
    public: &SpendPublic,
    statement_digest: &[u8; 32],
    hash: HashFn,
    check_pow: bool,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    verify_state_only_candidate_inner_traced(proof, public, statement_digest, hash, check_pow, None)
}

fn verify_state_only_candidate_inner_traced<'a>(
    proof: &'a [u8],
    public: &SpendPublic,
    statement_digest: &[u8; 32],
    hash: HashFn,
    check_pow: bool,
    trace: Option<StateOnlyVerifyTrace>,
) -> Result<VerifiedStateOnlyCandidate<'a>, StateOnlyCandidateVerifyError> {
    let (prefix, suffix) = StateOnlyCandidatePrefix::parse_from_proof(proof)?;
    let geometry = state_only_geometry(&prefix).ok_or(StateOnlyRelationVerifyError::PrefixShape)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Parsed);
    }
    let schedule = boxed_schedule(hash, &prefix, statement_digest, check_pow)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Transcript);
    }
    verify_terminal_phase(public, &prefix, &schedule)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Terminal);
    }
    let relation = verify_relation_phase(&prefix, &schedule)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::Relation);
    }
    let openings = verify_openings_parse_phase(hash, &prefix, suffix, &schedule, geometry)?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::OpeningsParsed);
    }
    verify_queries_phase(
        &prefix,
        &schedule,
        &relation.query_powers,
        &openings,
        geometry,
        CircleQuerySegment::Full,
    )?;
    if let Some(trace) = trace {
        trace(StateOnlyVerifyPhase::QueriesDone);
    }
    Ok(VerifiedStateOnlyCandidate {
        prefix,
        schedule,
        relation,
        openings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::circle::SecureCirclePoint;
    use aspis_core::field::{CM31, M31, P};
    use aspis_core::state_only_masked_switch_basis::{
        masked_switch_logical_to_natural, MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT,
        MASKED_SWITCH_UNIVERSAL_DIMENSION, PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT,
    };

    fn next_m31(state: &mut u64) -> M31 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31((*state % u64::from(P)) as u32)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(next_m31(state), next_m31(state)),
            c1: CM31::new(next_m31(state), next_m31(state)),
        }
    }

    #[test]
    fn atomic_inactive_masks_match_deferred_binary_at_64_random_fold_sequences() {
        let masks =
            crate::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3();
        for seed in 1..=64u64 {
            let mut state = seed.wrapping_mul(0x4154_4f4d_5245_4c31);
            let mut legacy = WeightAccumulator::empty(10);
            legacy.add_grouped_64x16_binary_masks(masks).unwrap();
            let mut optimized = WeightAccumulator::empty(10);
            optimized
                .add_grouped_64x16_binary_masks_deferred(masks)
                .unwrap();
            for log_len in [10u32, 8, 6, 4, 2] {
                for index in 0..1u32 << log_len {
                    assert_eq!(
                        optimized.weight_at(index),
                        legacy.weight_at(index),
                        "seed={seed} log_len={log_len} index={index}"
                    );
                }
                let values = (0..1usize << log_len)
                    .map(|_| next_qm31(&mut state))
                    .collect::<Vec<_>>();
                assert_eq!(optimized.dot(&values), legacy.dot(&values));
                if log_len > 2 {
                    let alpha = next_qm31(&mut state);
                    optimized.fold(alpha);
                    legacy.fold(alpha);
                }
            }
        }
    }

    #[test]
    fn profile21_post_delta_tau_matches_full_honest_u_target() {
        let mut state = 0x5052_4f46_494c_4532u64;
        let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
        for _ in 0..3 {
            let coordinates = (0..FIXED_TRACE_LOG_SIZE)
                .map(|_| next_qm31(&mut state))
                .collect();
            weights
                .add_multilinear(next_qm31(&mut state), coordinates)
                .unwrap();
        }
        weights
            .add_grouped_64x16_binary_masks_deferred(
                crate::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3(),
            )
            .unwrap();
        for _ in 0..2 {
            weights
                .add_circle_tensor(
                    next_qm31(&mut state),
                    SecureCirclePoint {
                        x: next_qm31(&mut state),
                        y: next_qm31(&mut state),
                    },
                )
                .unwrap();
        }
        weights.fold(next_qm31(&mut state));

        let full_target = |logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION]| {
            let natural = masked_switch_logical_to_natural(logical);
            natural
                .iter()
                .copied()
                .enumerate()
                .fold(QM31::ZERO, |sum, (index, value)| {
                    sum.add(weights.weight_at(index as u32).mul(value))
                })
        };
        let logical_u = core::array::from_fn(|_| next_qm31(&mut state));
        let translated_target = full_target(&logical_u);
        let valid = Profile21RelationInjection {
            tau: translated_target,
        };
        assert_eq!(profile21_claimed_seam_target(valid), translated_target);
        assert_eq!(
            MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT,
            PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT
        );

        // Tau is not locally recomputed by the verifier; the end-to-end q16
        // tooth binds any wrong seam to authenticated W1/U/source words.
        assert_ne!(
            profile21_claimed_seam_target(Profile21RelationInjection {
                tau: translated_target.add(QM31::ONE),
            }),
            translated_target
        );

        // The full target includes the sixteen OTP coordinates. A historical
        // message-only scalar would fail this direct equality.
        let mut randomness_only = [QM31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
        randomness_only[19] = QM31::ONE;
        assert_ne!(full_target(&randomness_only), QM31::ZERO);
    }
}
