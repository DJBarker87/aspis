//! Selected fresh-kappa verifier composition for the M31 circle candidate.
//!
//! This module joins the fixed transcript, two-point relation, authenticated
//! openings, and per-query arithmetic. It verifies the PCS candidate only; it
//! does not verify payment semantics or authorize a pool transition.

use alloc::{boxed::Box, vec::Vec};

use crate::circle_fri::FIXED_TRACE_LOG_SIZE;
use crate::circle_line_merkle::{CircleOpeningGeometry, RATE16_CIRCLE_OPENING_GEOMETRY};
use crate::circle_openings::{
    verify_circle_openings_deferred_canonical,
    verify_circle_openings_deferred_canonical_for_geometry, CircleOpeningsError,
    CircleQuerySegment, VerifiedCircleOpenings,
};
use crate::circle_prefix::{
    run_candidate_transcript_schedule_host, run_candidate_transcript_schedule_host_for_shape,
    CandidateOneLaneBatchingMode, CandidatePrefix, CandidatePrefixError,
    CandidateTranscriptScheduleError, CandidateTranscriptScheduleResult, CANDIDATE_FINAL_POLY_LEN,
    CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT, CANDIDATE_STATEMENT_POINT_COORDINATES,
    CANDIDATE_STATEMENT_VALUE_COUNT, JOHNSON_CANDIDATE_GRINDING_BITS,
    JOHNSON_CANDIDATE_QUERY_COUNT, JOHNSON_CANDIDATE_SHAPE, RATE16_CANDIDATE_GRINDING_BITS,
    RATE16_CANDIDATE_QUERY_COUNT, RATE16_CANDIDATE_SHAPE, RATE16_HARDENED_CANDIDATE_GRINDING_BITS,
    RATE16_HARDENED_CANDIDATE_SHAPE,
};
use crate::circle_query::CIRCLE_QUERY_TOTAL_COLUMNS;
use crate::field::{qm31_power_table, QM31};
use crate::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
    SUMCHECK_COEFFICIENTS,
};
use crate::HashFn;

pub const SELECTED_CANDIDATE_BATCHING_MODE: CandidateOneLaneBatchingMode =
    CandidateOneLaneBatchingMode::FreshKappa;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FreshKappaTraceEvent {
    Parsed,
    TranscriptDone,
    RelationDone,
    MerkleDone,
    QueriesDone,
}

pub type FreshKappaTraceFn = fn(FreshKappaTraceEvent);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidateRelationVerifyError {
    PrefixShape,
    WeightShape(TensorWeightError),
    BoundaryMismatch { round: usize },
    TerminalMismatch,
}

impl From<TensorWeightError> for CandidateRelationVerifyError {
    fn from(error: TensorWeightError) -> Self {
        Self::WeightShape(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FreshKappaCandidateVerifyError {
    Prefix(CandidatePrefixError),
    Transcript(CandidateTranscriptScheduleError),
    Relation(CandidateRelationVerifyError),
    Openings(CircleOpeningsError),
}

impl From<CandidatePrefixError> for FreshKappaCandidateVerifyError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}

impl From<CandidateTranscriptScheduleError> for FreshKappaCandidateVerifyError {
    fn from(error: CandidateTranscriptScheduleError) -> Self {
        Self::Transcript(error)
    }
}

impl From<CandidateRelationVerifyError> for FreshKappaCandidateVerifyError {
    fn from(error: CandidateRelationVerifyError) -> Self {
        Self::Relation(error)
    }
}

impl From<CircleOpeningsError> for FreshKappaCandidateVerifyError {
    fn from(error: CircleOpeningsError) -> Self {
        Self::Openings(error)
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedFreshKappaCandidate<'a> {
    pub prefix: CandidatePrefix<'a>,
    pub schedule: CandidateTranscriptScheduleResult,
    pub openings: VerifiedCircleOpenings<'a>,
}

fn xor11_point(
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES] {
    let mut point = *z;
    for coordinate in &mut point[CANDIDATE_STATEMENT_POINT_COORDINATES - 2..] {
        *coordinate = QM31::ONE.sub(*coordinate);
    }
    point
}

fn combined_statement_claim(
    prefix: &CandidatePrefix<'_>,
    point: usize,
    gamma_powers: &[QM31; CIRCLE_QUERY_TOTAL_COLUMNS],
) -> Result<QM31, CandidateRelationVerifyError> {
    let values_per_point = CANDIDATE_STATEMENT_VALUE_COUNT / 2;
    debug_assert_eq!(values_per_point, CIRCLE_QUERY_TOTAL_COLUMNS);
    let mut claim = QM31::ZERO;
    for column in 0..values_per_point {
        let value = prefix
            .statement_evaluation(point * values_per_point + column)
            .ok_or(CandidateRelationVerifyError::PrefixShape)?;
        claim = claim.add(gamma_powers[column].mul(value));
    }
    Ok(claim)
}

/// Verify the two-point/OOD/sumcheck relation carried by a parsed prefix.
pub fn verify_candidate_relation<const QUERY_COUNT: usize>(
    prefix: &CandidatePrefix<'_>,
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    schedule: &CandidateTranscriptScheduleResult<QUERY_COUNT>,
) -> Result<(), CandidateRelationVerifyError> {
    let gamma_powers = qm31_power_table::<CIRCLE_QUERY_TOTAL_COLUMNS>(schedule.prefix.gamma);
    verify_candidate_relation_with_gamma_powers(prefix, z, schedule, &gamma_powers)
}

pub fn verify_candidate_relation_with_gamma_powers<const QUERY_COUNT: usize>(
    prefix: &CandidatePrefix<'_>,
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    schedule: &CandidateTranscriptScheduleResult<QUERY_COUNT>,
    gamma_powers: &[QM31; CIRCLE_QUERY_TOTAL_COLUMNS],
) -> Result<(), CandidateRelationVerifyError> {
    let points = [*z, xor11_point(z)];
    let point_scales = [QM31::ONE, schedule.second_point_scale];
    let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    let mut running_claim = QM31::ZERO;

    for point in 0..2 {
        let claim = combined_statement_claim(prefix, point, gamma_powers)?;
        weights.add_multilinear(point_scales[point], Vec::from(points[point]))?;
        running_claim = running_claim.add(point_scales[point].mul(claim));
    }

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let value = prefix.rounds[round]
                .ood_value(sample)
                .ok_or(CandidateRelationVerifyError::PrefixShape)?;
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
                .ok_or(CandidateRelationVerifyError::PrefixShape)?;
        }
        if boundary_sum(&polynomial) != running_claim {
            return Err(CandidateRelationVerifyError::BoundaryMismatch { round });
        }
        running_claim = evaluate(&polynomial, schedule.alpha[round]);
        weights.fold(schedule.alpha[round]);
    }

    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(CandidateRelationVerifyError::PrefixShape)?;
    }
    if weights.dot(&final_coefficients) != running_claim {
        return Err(CandidateRelationVerifyError::TerminalMismatch);
    }
    Ok(())
}

/// Verify one overlap-reconciled segment of the literal q74/g32 Johnson
/// diagnostic. Each call repeats the exact prefix, transcript, relation, and
/// Merkle authentication. The caller must subtract that shared base when
/// combining segments; this function is not a production acceptance tag.
pub fn verify_johnson_candidate_segment(
    proof: &[u8],
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    hash: HashFn,
    segment: CircleQuerySegment,
) -> Result<(), FreshKappaCandidateVerifyError> {
    let (prefix, suffix) =
        CandidatePrefix::parse_from_proof_for_shape(proof, JOHNSON_CANDIDATE_SHAPE)?;
    let schedule = Box::new(run_candidate_transcript_schedule_host_for_shape::<
        { JOHNSON_CANDIDATE_QUERY_COUNT as usize },
    >(
        hash,
        &prefix,
        statement_digest,
        z,
        SELECTED_CANDIDATE_BATCHING_MODE,
        JOHNSON_CANDIDATE_GRINDING_BITS,
    )?);
    verify_candidate_relation(&prefix, z, &schedule)?;
    let mut later_roots = [[0u8; 32]; 3];
    for (layer, root) in later_roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer + 1]
            .root
            .copied()
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    let openings = verify_circle_openings_deferred_canonical(
        hash,
        prefix.c1_root,
        prefix.c2_root,
        &later_roots,
        &schedule.queries,
        suffix,
    )?;
    verify_candidate_query_segment(&openings, &prefix, &schedule, segment)?;
    Ok(())
}

/// Rate-1/16 q36/g32 Johnson-query diagnostic. This changes only the code
/// evaluation/Merkle domains; the 1,024-coefficient relation, four folds,
/// final4, batching rule, and query arithmetic kernels are unchanged.
pub fn verify_rate16_candidate_segment(
    proof: &[u8],
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    hash: HashFn,
    segment: CircleQuerySegment,
) -> Result<(), FreshKappaCandidateVerifyError> {
    let (prefix, suffix) =
        CandidatePrefix::parse_from_proof_for_shape(proof, RATE16_CANDIDATE_SHAPE)?;
    let schedule = Box::new(run_candidate_transcript_schedule_host_for_shape::<
        { RATE16_CANDIDATE_QUERY_COUNT as usize },
    >(
        hash,
        &prefix,
        statement_digest,
        z,
        SELECTED_CANDIDATE_BATCHING_MODE,
        RATE16_CANDIDATE_GRINDING_BITS,
    )?);
    verify_candidate_relation(&prefix, z, &schedule)?;
    let mut later_roots = [[0u8; 32]; 3];
    for (layer, root) in later_roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer + 1]
            .root
            .copied()
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    let openings = verify_circle_openings_deferred_canonical_for_geometry(
        hash,
        prefix.c1_root,
        prefix.c2_root,
        &later_roots,
        &schedule.queries,
        suffix,
        RATE16_CIRCLE_OPENING_GEOMETRY,
    )?;
    verify_candidate_query_segment_for_geometry(
        &openings,
        &prefix,
        &schedule,
        segment,
        RATE16_CIRCLE_OPENING_GEOMETRY,
    )?;
    Ok(())
}

/// Hardened rate-1/16 q36/g36 profile with a transcript-bound work witness
/// before every powers-generator fold challenge.
pub fn verify_rate16_hardened_candidate_segment(
    proof: &[u8],
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    hash: HashFn,
    segment: CircleQuerySegment,
) -> Result<(), FreshKappaCandidateVerifyError> {
    let (prefix, suffix) =
        CandidatePrefix::parse_from_proof_for_shape(proof, RATE16_HARDENED_CANDIDATE_SHAPE)?;
    let schedule = Box::new(run_candidate_transcript_schedule_host_for_shape::<
        { RATE16_CANDIDATE_QUERY_COUNT as usize },
    >(
        hash,
        &prefix,
        statement_digest,
        z,
        SELECTED_CANDIDATE_BATCHING_MODE,
        RATE16_HARDENED_CANDIDATE_GRINDING_BITS,
    )?);
    verify_candidate_relation(&prefix, z, &schedule)?;
    let mut later_roots = [[0u8; 32]; 3];
    for (layer, root) in later_roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer + 1]
            .root
            .copied()
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    let openings = verify_circle_openings_deferred_canonical_for_geometry(
        hash,
        prefix.c1_root,
        prefix.c2_root,
        &later_roots,
        &schedule.queries,
        suffix,
        RATE16_CIRCLE_OPENING_GEOMETRY,
    )?;
    verify_candidate_query_segment_for_geometry(
        &openings,
        &prefix,
        &schedule,
        segment,
        RATE16_CIRCLE_OPENING_GEOMETRY,
    )?;
    Ok(())
}

/// Verify one complete selected fresh-kappa circle-PCS candidate.
pub fn verify_fresh_kappa_candidate<'a>(
    proof: &'a [u8],
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    hash: HashFn,
) -> Result<VerifiedFreshKappaCandidate<'a>, FreshKappaCandidateVerifyError> {
    verify_fresh_kappa_candidate_with_trace(proof, statement_digest, z, hash, None, None)
}

#[inline(never)]
fn verify_candidate_queries(
    openings: &VerifiedCircleOpenings<'_>,
    prefix: &CandidatePrefix<'_>,
    schedule: &CandidateTranscriptScheduleResult,
    query_trace: Option<fn(usize)>,
) -> Result<(), CircleOpeningsError> {
    let mut final_natural = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_natural.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    openings.check_all_queries_with_trace(
        schedule.prefix.gamma,
        schedule.alpha,
        final_natural,
        query_trace,
    )
}

#[inline(never)]
fn verify_candidate_query_segment<const QUERY_COUNT: usize>(
    openings: &VerifiedCircleOpenings<'_>,
    prefix: &CandidatePrefix<'_>,
    schedule: &CandidateTranscriptScheduleResult<QUERY_COUNT>,
    segment: CircleQuerySegment,
) -> Result<(), CircleOpeningsError> {
    let mut final_natural = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_natural.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    openings.check_query_segment(
        schedule.prefix.gamma,
        schedule.alpha,
        final_natural,
        segment,
    )
}

#[inline(never)]
fn verify_candidate_query_segment_for_geometry<const QUERY_COUNT: usize>(
    openings: &VerifiedCircleOpenings<'_>,
    prefix: &CandidatePrefix<'_>,
    schedule: &CandidateTranscriptScheduleResult<QUERY_COUNT>,
    segment: CircleQuerySegment,
    geometry: CircleOpeningGeometry,
) -> Result<(), CircleOpeningsError> {
    let mut final_natural = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_natural.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    openings.check_query_segment_for_geometry(
        schedule.prefix.gamma,
        schedule.alpha,
        final_natural,
        segment,
        geometry,
    )
}

pub fn verify_fresh_kappa_candidate_with_trace<'a>(
    proof: &'a [u8],
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    hash: HashFn,
    trace: Option<FreshKappaTraceFn>,
    query_trace: Option<fn(usize)>,
) -> Result<VerifiedFreshKappaCandidate<'a>, FreshKappaCandidateVerifyError> {
    let (prefix, suffix) = CandidatePrefix::parse_from_proof(proof)?;
    if let Some(trace) = trace {
        trace(FreshKappaTraceEvent::Parsed);
    }
    let schedule = run_candidate_transcript_schedule_host(
        hash,
        &prefix,
        statement_digest,
        z,
        SELECTED_CANDIDATE_BATCHING_MODE,
    )?;
    if let Some(trace) = trace {
        trace(FreshKappaTraceEvent::TranscriptDone);
    }
    verify_candidate_relation(&prefix, z, &schedule)?;
    if let Some(trace) = trace {
        trace(FreshKappaTraceEvent::RelationDone);
    }
    let mut later_roots = [[0u8; 32]; 3];
    for (layer, root) in later_roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer + 1]
            .root
            .copied()
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    let openings = verify_circle_openings_deferred_canonical(
        hash,
        prefix.c1_root,
        prefix.c2_root,
        &later_roots,
        &schedule.queries,
        suffix,
    )?;
    if let Some(trace) = trace {
        trace(FreshKappaTraceEvent::MerkleDone);
    }
    verify_candidate_queries(&openings, &prefix, &schedule, query_trace)?;
    if let Some(trace) = trace {
        trace(FreshKappaTraceEvent::QueriesDone);
    }
    Ok(VerifiedFreshKappaCandidate {
        prefix,
        schedule,
        openings,
    })
}
