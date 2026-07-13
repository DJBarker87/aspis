//! Strict profile-15 PCS composition.
//!
//! This verifier checks the profile-15 transcript (including every PoW
//! witness), the two-point/OOD relation, both layer-zero roots, and all q36
//! fold paths. Payment semantics and the masked-terminal equation are checked
//! by the statement verifier before this PCS result may authorize a spend.

use alloc::{boxed::Box, vec::Vec};

use crate::circle_fri::FIXED_TRACE_LOG_SIZE;
use crate::circle_hiding_prefix::{
    run_payment_hiding_transcript_schedule_host,
    run_payment_hiding_transcript_schedule_host_unmined_for_diagnostics,
    PaymentHidingCandidatePrefix, PaymentHidingTranscriptScheduleResult,
};
use crate::circle_hiding_query::PAYMENT_HIDING_C2_LEAF_BYTES;
use crate::circle_line_merkle::RATE16_CIRCLE_OPENING_GEOMETRY;
use crate::circle_openings::{
    verify_circle_openings_deferred_canonical_for_geometry_and_c2_leaf_bytes, CircleOpeningsError,
    CircleQuerySegment, VerifiedCircleOpenings,
};
use crate::circle_prefix::{
    CandidatePrefixError, CandidateTranscriptScheduleError, CANDIDATE_FINAL_POLY_LEN,
    CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use crate::field::QM31;
use crate::relation_dot_candidate::{
    payment_hiding_relation_dot_candidate, PaymentHidingRelationDotCandidate,
};
use crate::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
    SUMCHECK_COEFFICIENTS,
};
use crate::HashFn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentHidingRelationError {
    PrefixShape,
    NonCanonicalStatementEvaluations,
    WeightShape(TensorWeightError),
    BoundaryMismatch { round: usize },
    TerminalMismatch,
}

impl From<TensorWeightError> for PaymentHidingRelationError {
    fn from(error: TensorWeightError) -> Self {
        Self::WeightShape(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentHidingVerifyError {
    Prefix(CandidatePrefixError),
    Transcript(CandidateTranscriptScheduleError),
    Relation(PaymentHidingRelationError),
    Openings(CircleOpeningsError),
}

impl From<CandidatePrefixError> for PaymentHidingVerifyError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}

impl From<CandidateTranscriptScheduleError> for PaymentHidingVerifyError {
    fn from(error: CandidateTranscriptScheduleError) -> Self {
        Self::Transcript(error)
    }
}

impl From<PaymentHidingRelationError> for PaymentHidingVerifyError {
    fn from(error: PaymentHidingRelationError) -> Self {
        Self::Relation(error)
    }
}

impl From<CircleOpeningsError> for PaymentHidingVerifyError {
    fn from(error: CircleOpeningsError) -> Self {
        Self::Openings(error)
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedPaymentHidingCandidate<'a> {
    pub prefix: PaymentHidingCandidatePrefix<'a>,
    pub schedule: PaymentHidingTranscriptScheduleResult,
    pub openings: VerifiedCircleOpenings<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentHidingTraceEvent {
    Parsed,
    TranscriptDone,
    RelationDone,
    MerkleDone,
    QueriesDone,
}

pub type PaymentHidingTraceFn = fn(PaymentHidingTraceEvent);

fn xor11_point(z: &[QM31; 10]) -> [QM31; 10] {
    let mut shifted = *z;
    for coordinate in [6usize, 8, 9] {
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    shifted
}

pub fn verify_payment_hiding_relation(
    prefix: &PaymentHidingCandidatePrefix<'_>,
    schedule: &PaymentHidingTranscriptScheduleResult,
) -> Result<(), PaymentHidingRelationError> {
    let prepared = prepare_relation_dot(prefix, schedule.prefix.gamma)?;
    verify_payment_hiding_relation_with_claims(prefix, schedule, prepared.claims)
}

#[inline(always)]
fn prepare_relation_dot(
    prefix: &PaymentHidingCandidatePrefix<'_>,
    gamma: QM31,
) -> Result<PaymentHidingRelationDotCandidate, PaymentHidingRelationError> {
    payment_hiding_relation_dot_candidate(gamma, prefix.statement_evaluations_bytes)
        .ok_or(PaymentHidingRelationError::NonCanonicalStatementEvaluations)
}

fn verify_payment_hiding_relation_with_claims(
    prefix: &PaymentHidingCandidatePrefix<'_>,
    schedule: &PaymentHidingTranscriptScheduleResult,
    claims: [QM31; 2],
) -> Result<(), PaymentHidingRelationError> {
    let points = [schedule.prefix.z, xor11_point(&schedule.prefix.z)];
    let point_scales = [QM31::ONE, schedule.prefix.second_point_scale];
    let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    let mut running_claim = QM31::ZERO;
    for point in 0..2 {
        weights.add_multilinear(point_scales[point], Vec::from(points[point]))?;
        running_claim = running_claim.add(point_scales[point].mul(claims[point]));
    }

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let value = prefix.rounds[round]
                .ood_value(sample)
                .ok_or(PaymentHidingRelationError::PrefixShape)?;
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
                .ok_or(PaymentHidingRelationError::PrefixShape)?;
        }
        if boundary_sum(&polynomial) != running_claim {
            return Err(PaymentHidingRelationError::BoundaryMismatch { round });
        }
        running_claim = evaluate(&polynomial, schedule.alpha[round]);
        weights.fold(schedule.alpha[round]);
    }
    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = prefix
            .final_coefficient(coefficient)
            .ok_or(PaymentHidingRelationError::PrefixShape)?;
    }
    if weights.dot(&final_coefficients) != running_claim {
        return Err(PaymentHidingRelationError::TerminalMismatch);
    }
    Ok(())
}

pub fn verify_payment_hiding_candidate_segment<'a>(
    proof: &'a [u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    segment: CircleQuerySegment,
) -> Result<VerifiedPaymentHidingCandidate<'a>, PaymentHidingVerifyError> {
    let (prefix, suffix) = PaymentHidingCandidatePrefix::parse_from_proof(proof)?;
    let schedule = Box::new(run_payment_hiding_transcript_schedule_host(
        hash,
        &prefix,
        statement_digest,
    )?);
    verify_payment_hiding_candidate_with_parsed_schedule(
        prefix, suffix, *schedule, hash, segment, None,
    )
}

/// Measurement/test-only composition when profile-15 PoW witnesses have not
/// yet been mined. The caller supplies the exact transcript schedule used to
/// build the algebraic proof. Production acceptance must call
/// [`verify_payment_hiding_candidate_segment`], which derives that schedule
/// itself and rejects invalid PoW.
pub fn verify_payment_hiding_candidate_with_schedule_for_diagnostics<'a>(
    proof: &'a [u8],
    schedule: PaymentHidingTranscriptScheduleResult,
    hash: HashFn,
    segment: CircleQuerySegment,
) -> Result<VerifiedPaymentHidingCandidate<'a>, PaymentHidingVerifyError> {
    let (prefix, suffix) = PaymentHidingCandidatePrefix::parse_from_proof(proof)?;
    verify_payment_hiding_candidate_with_parsed_schedule(
        prefix, suffix, schedule, hash, segment, None,
    )
}

/// Same algebraic verifier as production, with only the nonce difficulty
/// predicates disabled. Nonce bytes still occupy and advance the exact
/// transcript positions, so this is suitable for CU measurement only.
pub fn verify_payment_hiding_candidate_unmined_for_diagnostics<'a>(
    proof: &'a [u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    segment: CircleQuerySegment,
) -> Result<VerifiedPaymentHidingCandidate<'a>, PaymentHidingVerifyError> {
    verify_payment_hiding_candidate_unmined_for_diagnostics_with_trace(
        proof,
        statement_digest,
        hash,
        segment,
        None,
    )
}

pub fn verify_payment_hiding_candidate_unmined_for_diagnostics_with_trace<'a>(
    proof: &'a [u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    segment: CircleQuerySegment,
    trace: Option<PaymentHidingTraceFn>,
) -> Result<VerifiedPaymentHidingCandidate<'a>, PaymentHidingVerifyError> {
    let (prefix, suffix) = PaymentHidingCandidatePrefix::parse_from_proof(proof)?;
    if let Some(trace) = trace {
        trace(PaymentHidingTraceEvent::Parsed);
    }
    let schedule = run_payment_hiding_transcript_schedule_host_unmined_for_diagnostics(
        hash,
        &prefix,
        statement_digest,
    )?;
    if let Some(trace) = trace {
        trace(PaymentHidingTraceEvent::TranscriptDone);
    }
    verify_payment_hiding_candidate_with_parsed_schedule(
        prefix, suffix, schedule, hash, segment, trace,
    )
}

fn verify_payment_hiding_candidate_with_parsed_schedule<'a>(
    prefix: PaymentHidingCandidatePrefix<'a>,
    suffix: &'a [u8],
    schedule: PaymentHidingTranscriptScheduleResult,
    hash: HashFn,
    segment: CircleQuerySegment,
    trace: Option<PaymentHidingTraceFn>,
) -> Result<VerifiedPaymentHidingCandidate<'a>, PaymentHidingVerifyError> {
    // One traversal canonically decodes both statement rows, computes both
    // relation claims, and retains the exact prepared factors needed by all
    // layer-zero queries. No raw 816-byte gamma table or duplicate field
    // decoding remains live.
    // The fused result contains the 49-column prepared query table. Keep its
    // 856-byte fixed payload off the already dense SBF verifier frame.
    let prepared = Box::new(prepare_relation_dot(&prefix, schedule.prefix.gamma)?);
    verify_payment_hiding_relation_with_claims(&prefix, &schedule, prepared.claims)?;
    if let Some(trace) = trace {
        trace(PaymentHidingTraceEvent::RelationDone);
    }
    let mut later_roots = [[0u8; 32]; 3];
    for (layer, root) in later_roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer + 1]
            .root
            .copied()
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    let openings = verify_circle_openings_deferred_canonical_for_geometry_and_c2_leaf_bytes(
        hash,
        prefix.c1_root,
        prefix.c2_root,
        &later_roots,
        &schedule.queries,
        suffix,
        RATE16_CIRCLE_OPENING_GEOMETRY,
        PAYMENT_HIDING_C2_LEAF_BYTES,
    )?;
    if let Some(trace) = trace {
        trace(PaymentHidingTraceEvent::MerkleDone);
    }
    let mut final_natural = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, value) in final_natural.iter_mut().enumerate() {
        *value = prefix
            .final_coefficient(coefficient)
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    openings.check_payment_hiding_query_segment_prepared_for_geometry(
        &prepared.query_powers,
        schedule.alpha,
        final_natural,
        segment,
        RATE16_CIRCLE_OPENING_GEOMETRY,
    )?;
    if let Some(trace) = trace {
        trace(PaymentHidingTraceEvent::QueriesDone);
    }
    Ok(VerifiedPaymentHidingCandidate {
        prefix,
        schedule,
        openings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circle_hiding_prefix::{
        PAYMENT_HIDING_FLAGS, PAYMENT_HIDING_GRINDING_BITS, PAYMENT_HIDING_LOG_BLOWUP,
        PAYMENT_HIDING_LOG_ROWS, PAYMENT_HIDING_PREFIX_LEN, PAYMENT_HIDING_PREFIX_OFFSETS,
        PAYMENT_HIDING_PROFILE_ID, PAYMENT_HIDING_QUERY_COUNT,
        PAYMENT_HIDING_STATEMENT_VALUE_COUNT,
    };
    use crate::circle_hiding_query::PAYMENT_HIDING_OUTER_COLUMNS;
    use crate::field::{qm31_dot, qm31_power_table, CM31, M31, P};
    use crate::params::{FoldPayload, MerkleMode};
    use crate::proof::{Header, HEADER_LEN, VERSION_V4_S2};
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn zero_prefix() -> [u8; PAYMENT_HIDING_PREFIX_LEN] {
        let mut bytes = [0u8; PAYMENT_HIDING_PREFIX_LEN];
        Header {
            version: VERSION_V4_S2,
            profile_id: PAYMENT_HIDING_PROFILE_ID,
            log_rows: PAYMENT_HIDING_LOG_ROWS,
            log_blowup: PAYMENT_HIDING_LOG_BLOWUP,
            query_count: PAYMENT_HIDING_QUERY_COUNT,
            grinding_bits: PAYMENT_HIDING_GRINDING_BITS,
            fold_payload: FoldPayload::RawFibers as u8,
            merkle_mode: MerkleMode::Radix4MinimalSubtree as u8,
            num_rounds: CANDIDATE_ROUND_COUNT as u32,
            final_poly_log_len: 2,
            flags: PAYMENT_HIDING_FLAGS,
        }
        .write(&mut bytes[..HEADER_LEN]);
        bytes
    }

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
    fn integrated_fused_claims_and_query_powers_match_the_old_path() {
        let mut state = 0x15_51_c0de_7a11_5eed;
        for _ in 0..64 {
            let gamma = next_qm31(&mut state);
            let gamma_powers = qm31_power_table::<PAYMENT_HIDING_OUTER_COLUMNS>(gamma);
            let values: [[QM31; PAYMENT_HIDING_OUTER_COLUMNS]; 2] =
                core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state)));
            let mut bytes = zero_prefix();
            for (point, row) in values.iter().enumerate() {
                for (column, value) in row.iter().enumerate() {
                    let index = point * PAYMENT_HIDING_OUTER_COLUMNS + column;
                    let start =
                        PAYMENT_HIDING_PREFIX_OFFSETS.statement_evaluations_start + index * 16;
                    value.write_le_bytes(&mut bytes[start..start + 16]);
                }
            }
            let parsed = PaymentHidingCandidatePrefix::parse_exact(&bytes).unwrap();
            let fused = prepare_relation_dot(&parsed, gamma).unwrap();
            assert_eq!(
                fused.claims,
                [
                    qm31_dot(&gamma_powers, &values[0]),
                    qm31_dot(&gamma_powers, &values[1]),
                ]
            );
            assert_eq!(
                fused.query_powers,
                crate::circle_hiding_query::PaymentHidingQueryPowers::from_full_table(
                    &gamma_powers
                )
            );
        }
    }

    #[test]
    fn parser_defers_but_full_verifier_rejects_every_noncanonical_statement_limb() {
        let canonical = zero_prefix();
        for limb in 0..PAYMENT_HIDING_STATEMENT_VALUE_COUNT * 4 {
            let mut bytes = canonical;
            let start = PAYMENT_HIDING_PREFIX_OFFSETS.statement_evaluations_start + limb * 4;
            bytes[start..start + 4].copy_from_slice(&P.to_le_bytes());

            let parsed = PaymentHidingCandidatePrefix::parse_exact(&bytes)
                .expect("the parser must defer exactly the statement block");
            assert_eq!(parsed.statement_evaluation(limb / 4), None);
            assert!(
                matches!(
                    verify_payment_hiding_candidate_unmined_for_diagnostics(
                        &bytes,
                        &[0u8; 32],
                        test_hash,
                        CircleQuerySegment::Full,
                    ),
                    Err(PaymentHidingVerifyError::Relation(
                        PaymentHidingRelationError::NonCanonicalStatementEvaluations,
                    )),
                ),
                "full verifier accepted noncanonical statement limb {limb}",
            );
        }
    }
}
