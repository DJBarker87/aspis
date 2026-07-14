//! Sequential one-mask+C1-padding builder through the hiding prefix.
//!
//! This module deliberately stops before the expensive profile-14 proof-of-
//! work search. It nevertheless builds the real C1/C2 commitments, the
//! payment sumcheck, its PCS-bound terminal, all 102 statement values,
//! and replays the exact core parser/transcript schedule.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_fri::evaluate_final_line_tensor_at_query_for_domain_log;
use aspis_core::circle_hiding_prefix::{
    run_payment_hiding_prefix_schedule_host, sample_payment_hiding_queries,
    PaymentHidingCandidatePrefix, PaymentHidingPrefixScheduleResult,
    PaymentHidingTranscriptScheduleResult, PAYMENT_HIDING_FLAGS, PAYMENT_HIDING_GRINDING_BITS,
    PAYMENT_HIDING_LOG_BLOWUP, PAYMENT_HIDING_LOG_ROWS, PAYMENT_HIDING_PREFIX_LEN,
    PAYMENT_HIDING_PREFIX_OFFSETS, PAYMENT_HIDING_PROFILE_ID, PAYMENT_HIDING_QUERY_COUNT,
    PAYMENT_HIDING_STATEMENT_VALUE_COUNT, PAYMENT_HIDING_VALUES_PER_POINT,
};
use aspis_core::circle_prefix::{
    CandidatePrefixError, CandidateTranscriptScheduleError, CANDIDATE_FINAL_POLY_LEN,
    CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::{qm31_power_table, M31, QM31};
use aspis_core::params::{FoldPayload, MerkleMode};
use aspis_core::proof::{Header, HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR, VERSION_V4_S2};
use aspis_core::statement_sumcheck::{
    encode_wire, PAYMENT_SUMCHECK_ROUNDS, PAYMENT_SUMCHECK_ROUND_BYTES,
};
use aspis_core::sumcheck::SUMCHECK_COEFFICIENTS;
use aspis_core::transcript::{
    label, ChallengeSampleExhausted, HashFn, QuerySampleError, Transcript,
};
use aspis_statement::{
    build_direct_range_hiding_helpers_v4, direct_range_hiding_masked_terminal_value,
    direct_range_hiding_trace_openings_at_point, DirectRangeHidingError,
    DirectRangeHidingHelpersV4, SpendPublic, SpendTraceV4,
};

use crate::circle_candidate::{
    build_fold_commitments_for_domain_log, c1_layer0_leaves_for_codeword_len,
    c1_layer0_root_for_codeword_len, combined_candidate_layer_root_for_domain_log,
    fold_candidate_codeword_round_for_domain_log, gamma_combine_codewords_for_len,
    gamma_combine_messages, CircleCandidateError, CircleEncoder,
};
use crate::circle_candidate_openings::{
    serialize_candidate_openings_for_fiber_count_with_c2, CandidateOpeningBuildError,
};
use crate::circle_candidate_prefix::{CandidatePrefixBuildError, IncrementalRelation};
use crate::circle_relation::{
    validate_circle_relation, CircleRelationParameters, CircleRelationPointRule,
    CircleRelationTrace,
};
use crate::mask_oracle_relation::{
    build_payment_hiding_c2_commitment, MaskOracleRelationError, PaymentHidingC2Commitment,
};
use crate::statement_zerocheck::{
    prove_spend_payment_zerocheck_committed_hiding, PaymentZerocheckProveError,
    SpendPaymentCommittedHidingZerocheck,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaymentHidingPrefixMaterial {
    pub c1_root: [u8; 32],
    pub c2_root: [u8; 32],
    pub initial_mask_claim: QM31,
    pub payment_sumcheck:
        [aspis_core::statement_sumcheck::PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS],
    pub statement_evaluations: [QM31; PAYMENT_HIDING_STATEMENT_VALUE_COUNT],
    pub later_roots: [[u8; 32]; CANDIDATE_ROUND_COUNT - 1],
    pub ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub relation_sumchecks: [[QM31; SUMCHECK_COEFFICIENTS]; CANDIDATE_ROUND_COUNT],
    pub final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN],
    pub nonce: u64,
    pub fold_nonces: [u64; CANDIDATE_ROUND_COUNT],
    pub batch_nonce: u64,
}

impl PaymentHidingPrefixMaterial {
    fn front(
        c1_root: [u8; 32],
        c2_root: [u8; 32],
        zerocheck: &SpendPaymentCommittedHidingZerocheck,
        statement_evaluations: [QM31; PAYMENT_HIDING_STATEMENT_VALUE_COUNT],
    ) -> Self {
        Self {
            c1_root,
            c2_root,
            initial_mask_claim: zerocheck.initial_mask_claim,
            payment_sumcheck: zerocheck.sumcheck.messages,
            statement_evaluations,
            later_roots: [[0u8; 32]; CANDIDATE_ROUND_COUNT - 1],
            ood_values: [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
            relation_sumchecks: [[QM31::ZERO; SUMCHECK_COEFFICIENTS]; CANDIDATE_ROUND_COUNT],
            final_coefficients: [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN],
            nonce: 0,
            fold_nonces: [0; CANDIDATE_ROUND_COUNT],
            batch_nonce: 0,
        }
    }
}

#[derive(Clone)]
pub struct BuiltPaymentHidingPrefixFront {
    pub bytes: Vec<u8>,
    pub material: PaymentHidingPrefixMaterial,
    pub schedule: PaymentHidingPrefixScheduleResult,
    pub helpers: DirectRangeHidingHelpersV4,
    pub encoded_c1: Vec<Vec<M31>>,
    pub c2: PaymentHidingC2Commitment,
    pub zerocheck: SpendPaymentCommittedHidingZerocheck,
    pub transcript_after_gamma: Transcript,
    pub batch_pow_valid: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentHidingPowMode {
    /// Build the exact transcript with zero nonce records even when they do
    /// not satisfy PoW. This is only for algebra/CU diagnostics.
    UnminedZero,
    /// Search every profile-14 nonce. This has the protocol's literal
    /// 2^39-class prover work and is never selected by ordinary tests.
    Mine,
}

#[derive(Clone)]
pub struct BuiltPaymentHidingProof {
    pub bytes: Vec<u8>,
    pub material: PaymentHidingPrefixMaterial,
    pub schedule: PaymentHidingTranscriptScheduleResult,
    pub relation: CircleRelationTrace,
    pub pow_valid: bool,
    pub front: BuiltPaymentHidingPrefixFront,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PaymentHidingPrefixBuildError {
    Candidate(CircleCandidateError),
    Mask(MaskOracleRelationError),
    Helper(DirectRangeHidingError),
    Zerocheck(PaymentZerocheckProveError<aspis_statement::ConstraintBuildError>),
    Prefix(CandidatePrefixError),
    Transcript(CandidateTranscriptScheduleError),
    Sequential(CandidatePrefixBuildError),
    Opening(CandidateOpeningBuildError),
    ChallengeSampleExhausted,
    QuerySample(QuerySampleError),
    Consistency(&'static str),
}

impl From<CircleCandidateError> for PaymentHidingPrefixBuildError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Candidate(error)
    }
}

impl From<MaskOracleRelationError> for PaymentHidingPrefixBuildError {
    fn from(error: MaskOracleRelationError) -> Self {
        Self::Mask(error)
    }
}

impl From<DirectRangeHidingError> for PaymentHidingPrefixBuildError {
    fn from(error: DirectRangeHidingError) -> Self {
        Self::Helper(error)
    }
}

impl From<PaymentZerocheckProveError<aspis_statement::ConstraintBuildError>>
    for PaymentHidingPrefixBuildError
{
    fn from(error: PaymentZerocheckProveError<aspis_statement::ConstraintBuildError>) -> Self {
        Self::Zerocheck(error)
    }
}

impl From<CandidatePrefixError> for PaymentHidingPrefixBuildError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}

impl From<CandidateTranscriptScheduleError> for PaymentHidingPrefixBuildError {
    fn from(error: CandidateTranscriptScheduleError) -> Self {
        Self::Transcript(error)
    }
}

impl From<CandidatePrefixBuildError> for PaymentHidingPrefixBuildError {
    fn from(error: CandidatePrefixBuildError) -> Self {
        Self::Sequential(error)
    }
}

impl From<CandidateOpeningBuildError> for PaymentHidingPrefixBuildError {
    fn from(error: CandidateOpeningBuildError) -> Self {
        Self::Opening(error)
    }
}

impl From<ChallengeSampleExhausted> for PaymentHidingPrefixBuildError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

impl From<QuerySampleError> for PaymentHidingPrefixBuildError {
    fn from(error: QuerySampleError) -> Self {
        Self::QuerySample(error)
    }
}

pub fn payment_hiding_header() -> Header {
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
}

pub fn serialize_payment_hiding_prefix(material: &PaymentHidingPrefixMaterial) -> Vec<u8> {
    let mut bytes = vec![0u8; PAYMENT_HIDING_PREFIX_LEN];
    payment_hiding_header().write(&mut bytes[..HEADER_LEN]);
    bytes[PAYMENT_HIDING_PREFIX_OFFSETS.c1_root_start..][..32].copy_from_slice(&material.c1_root);
    bytes[PAYMENT_HIDING_PREFIX_OFFSETS.c2_root_start..][..32].copy_from_slice(&material.c2_root);
    material
        .initial_mask_claim
        .write_le_bytes(&mut bytes[PAYMENT_HIDING_PREFIX_OFFSETS.initial_mask_claim_start..][..16]);
    for (round, wire) in material.payment_sumcheck.iter().enumerate() {
        let start = PAYMENT_HIDING_PREFIX_OFFSETS.payment_sumcheck_start
            + round * PAYMENT_SUMCHECK_ROUND_BYTES;
        bytes[start..start + PAYMENT_SUMCHECK_ROUND_BYTES].copy_from_slice(&encode_wire(wire));
    }
    for (index, value) in material.statement_evaluations.iter().enumerate() {
        let start = PAYMENT_HIDING_PREFIX_OFFSETS.statement_evaluations_start + index * 16;
        value.write_le_bytes(&mut bytes[start..start + 16]);
    }
    for round in 0..CANDIDATE_ROUND_COUNT {
        let offsets = PAYMENT_HIDING_PREFIX_OFFSETS.rounds[round];
        if let Some(root_start) = offsets.root_start {
            bytes[root_start..root_start + 32].copy_from_slice(&material.later_roots[round - 1]);
        }
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let start = offsets.ood_values_start + sample * 16;
            material.ood_values[round][sample].write_le_bytes(&mut bytes[start..start + 16]);
        }
        for coefficient in 0..SUMCHECK_COEFFICIENTS {
            let start = offsets.sumcheck_start + coefficient * 16;
            material.relation_sumchecks[round][coefficient]
                .write_le_bytes(&mut bytes[start..start + 16]);
        }
    }
    for (coefficient, value) in material.final_coefficients.iter().enumerate() {
        let start = PAYMENT_HIDING_PREFIX_OFFSETS.final_polynomial_start + coefficient * 16;
        value.write_le_bytes(&mut bytes[start..start + 16]);
    }
    bytes[PAYMENT_HIDING_PREFIX_OFFSETS.nonce_start..][..CANDIDATE_NONCE_LEN]
        .copy_from_slice(&material.nonce.to_le_bytes());
    for (round, nonce) in material.fold_nonces.iter().enumerate() {
        let start = PAYMENT_HIDING_PREFIX_OFFSETS.fold_nonces_start + round * CANDIDATE_NONCE_LEN;
        bytes[start..start + CANDIDATE_NONCE_LEN].copy_from_slice(&nonce.to_le_bytes());
    }
    bytes[PAYMENT_HIDING_PREFIX_OFFSETS.batch_nonce_start..][..CANDIDATE_NONCE_LEN]
        .copy_from_slice(&material.batch_nonce.to_le_bytes());
    bytes
}

fn encode_statement_points(z: &[QM31; 10]) -> [u8; 320] {
    let points = [*z, aspis_statement::xor11_point(z)];
    let mut bytes = [0u8; 320];
    for (point, coordinates) in points.iter().enumerate() {
        for (coordinate, value) in coordinates.iter().enumerate() {
            value.write_le_bytes(&mut bytes[(point * 10 + coordinate) * 16..][..16]);
        }
    }
    bytes
}

fn statement_evaluations(
    trace: &SpendTraceV4,
    helpers: &DirectRangeHidingHelpersV4,
    z: &[QM31; 10],
) -> Result<[QM31; PAYMENT_HIDING_STATEMENT_VALUE_COUNT], PaymentHidingPrefixBuildError> {
    if trace.c1.len() != 49 || trace.c1.iter().any(|column| column.len() != 1024) {
        return Err(PaymentHidingPrefixBuildError::Consistency(
            "profile-14 C1 table is not 49 by 1024",
        ));
    }
    let points = [*z, aspis_statement::xor11_point(z)];
    let mut output = [QM31::ZERO; PAYMENT_HIDING_STATEMENT_VALUE_COUNT];
    for (point_index, point) in points.iter().enumerate() {
        let base = point_index * PAYMENT_HIDING_VALUES_PER_POINT;
        for (column, message) in trace.c1.iter().enumerate() {
            output[base + column] = crate::multilinear_eval(message, point);
        }
        output[base + 49] = crate::multilinear_eval_extension(&helpers.h1, point);
        output[base + 50] = crate::multilinear_eval_extension(&helpers.payment_mask, point);
    }
    Ok(output)
}

pub fn build_payment_hiding_prefix_front(
    public: &SpendPublic,
    trace: &SpendTraceV4,
    helper_masks: &[QM31],
    payment_mask: &[QM31],
    statement_digest: [u8; 32],
    hash: HashFn,
    pow_mode: PaymentHidingPowMode,
) -> Result<BuiltPaymentHidingPrefixFront, PaymentHidingPrefixBuildError> {
    let encoder = CircleEncoder::new_for_domain_log(14);
    let encoded_c1 = encoder.encode_c1_columns(&trace.c1)?;
    let c1_root = c1_layer0_root_for_codeword_len(&encoded_c1, encoder.codeword_len(), hash)?;
    let mut header_bytes = [0u8; HEADER_LEN];
    payment_hiding_header().write(&mut header_bytes);
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, &statement_digest);
    let mut c1_record = [0u8; 33];
    c1_record[1..].copy_from_slice(&c1_root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &c1_record);
    let lambda = transcript.challenge_qm31()?;
    let chi = transcript.challenge_qm31()?;
    let helpers =
        build_direct_range_hiding_helpers_v4(trace, lambda, chi, helper_masks, payment_mask)?;
    let c2 =
        build_payment_hiding_c2_commitment(&encoder, &helpers.h1, &helpers.payment_mask, hash)?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2.root);
    let zerocheck = prove_spend_payment_zerocheck_committed_hiding(
        &mut transcript,
        public,
        trace,
        &helpers,
        lambda,
        chi,
    )?;
    let z = zerocheck.sumcheck.challenges;
    let openings = direct_range_hiding_trace_openings_at_point(trace, &helpers, &z).ok_or(
        PaymentHidingPrefixBuildError::Consistency(
            "profile-14 terminal openings have the wrong shape",
        ),
    )?;
    let terminal = direct_range_hiding_masked_terminal_value(
        public,
        &openings,
        &z,
        &zerocheck.batching,
        lambda,
        chi,
        zerocheck.eta,
    )
    .map_err(|_| {
        PaymentHidingPrefixBuildError::Consistency("profile-14 terminal evaluation failed")
    })?;
    if terminal != zerocheck.sumcheck.terminal_claim {
        return Err(PaymentHidingPrefixBuildError::Consistency(
            "masked sumcheck terminal is not the committed-oracle terminal",
        ));
    }
    let statement_evaluations = statement_evaluations(trace, &helpers, &z)?;
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_POINTS,
        &encode_statement_points(&z),
    );
    let mut statement_bytes = [0u8; PAYMENT_HIDING_STATEMENT_VALUE_COUNT * 16];
    for (index, value) in statement_evaluations.iter().enumerate() {
        value.write_le_bytes(&mut statement_bytes[index * 16..][..16]);
    }
    transcript.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, &statement_bytes);
    let batch_nonce = pow_nonce(
        &transcript,
        aspis_core::circle_hiding_prefix::PAYMENT_HIDING_BATCH_GRINDING_BITS,
        pow_mode,
    );
    let batch_pow_valid = transcript.grinding_ok(
        batch_nonce,
        aspis_core::circle_hiding_prefix::PAYMENT_HIDING_BATCH_GRINDING_BITS,
    );
    transcript.absorb(
        label::M31_PAYMENT_BATCH_POW_NONCE,
        &batch_nonce.to_le_bytes(),
    );
    let gamma = transcript.challenge_qm31()?;
    let second_point_scale = transcript.challenge_qm31()?;

    let mut material =
        PaymentHidingPrefixMaterial::front(c1_root, c2.root, &zerocheck, statement_evaluations);
    material.batch_nonce = batch_nonce;
    let bytes = serialize_payment_hiding_prefix(&material);
    let parsed = PaymentHidingCandidatePrefix::parse_exact(&bytes)?;
    let schedule = run_payment_hiding_prefix_schedule_host(hash, &parsed, &statement_digest)?;
    if schedule.lambda != lambda
        || schedule.chi != chi
        || schedule.batching != zerocheck.batching
        || schedule.initial_mask_claim != zerocheck.initial_mask_claim
        || schedule.eta != zerocheck.eta
        || schedule.z != z
        || schedule.masked_terminal_claim != zerocheck.sumcheck.terminal_claim
        || schedule.gamma != gamma
        || schedule.second_point_scale != second_point_scale
    {
        return Err(PaymentHidingPrefixBuildError::Consistency(
            "profile-14 verifier replay diverges before PCS OOD sampling",
        ));
    }
    Ok(BuiltPaymentHidingPrefixFront {
        bytes,
        material,
        schedule,
        helpers,
        encoded_c1,
        c2,
        zerocheck,
        transcript_after_gamma: transcript,
        batch_pow_valid,
    })
}

fn absorb_round_root(transcript: &mut Transcript, layer: usize, root: &[u8; 32]) {
    let mut record = [0u8; 33];
    record[0] = layer as u8;
    record[1..].copy_from_slice(root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn absorb_ood_value(
    transcript: &mut Transcript,
    ood_label: u8,
    layer: usize,
    sample: usize,
    value: QM31,
) {
    let mut record = [0u8; 18];
    record[0] = layer as u8;
    record[1] = sample as u8;
    value.write_le_bytes(&mut record[2..]);
    transcript.absorb(ood_label, &record);
}

fn absorb_relation_sumcheck(
    transcript: &mut Transcript,
    layer: usize,
    polynomial: &[QM31; SUMCHECK_COEFFICIENTS],
) {
    let mut record = [0u8; 1 + SUMCHECK_COEFFICIENTS * 16];
    record[0] = layer as u8;
    for (coefficient, value) in polynomial.iter().enumerate() {
        value.write_le_bytes(&mut record[1 + coefficient * 16..][..16]);
    }
    transcript.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &record);
}

fn absorb_fold_pow(transcript: &mut Transcript, layer: usize, nonce: u64) {
    let mut record = [0u8; 1 + CANDIDATE_NONCE_LEN];
    record[0] = layer as u8;
    record[1..].copy_from_slice(&nonce.to_le_bytes());
    transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
}

fn absorb_final(transcript: &mut Transcript, coefficients: &[QM31; CANDIDATE_FINAL_POLY_LEN]) {
    let mut bytes = [0u8; CANDIDATE_FINAL_POLY_LEN * 16];
    for (index, value) in coefficients.iter().enumerate() {
        value.write_le_bytes(&mut bytes[index * 16..][..16]);
    }
    transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, &bytes);
}

fn pow_nonce(transcript: &Transcript, bits: u8, mode: PaymentHidingPowMode) -> u64 {
    match mode {
        PaymentHidingPowMode::UnminedZero => 0,
        PaymentHidingPowMode::Mine => crate::find_grinding_nonce(transcript, bits),
    }
}

fn compressed_statement_claims(
    evaluations: &[QM31; PAYMENT_HIDING_STATEMENT_VALUE_COUNT],
    gamma: QM31,
) -> [QM31; 2] {
    let powers = qm31_power_table::<51>(gamma);
    core::array::from_fn(|point| {
        let base = point * PAYMENT_HIDING_VALUES_PER_POINT;
        let mut claim = QM31::ZERO;
        for column in 0..49 {
            claim = claim.add(powers[column].mul(evaluations[base + column]));
        }
        claim = claim.add(powers[49].mul(evaluations[base + 49]));
        claim.add(powers[50].mul(evaluations[base + 50]))
    })
}

/// Finish the algebraic profile-14 proof. `UnminedZero` is the fast test/CU
/// path and returns `pow_valid=false`; production acceptance still rejects
/// that byte string. `Mine` performs the literal configured work.
pub fn build_payment_hiding_proof(
    public: &SpendPublic,
    trace: &SpendTraceV4,
    helper_masks: &[QM31],
    payment_mask: &[QM31],
    statement_digest: [u8; 32],
    hash: HashFn,
    pow_mode: PaymentHidingPowMode,
) -> Result<BuiltPaymentHidingProof, PaymentHidingPrefixBuildError> {
    let mut front = build_payment_hiding_prefix_front(
        public,
        trace,
        helper_masks,
        payment_mask,
        statement_digest,
        hash,
        pow_mode,
    )?;
    let encoder = CircleEncoder::new_for_domain_log(14);
    let c2_messages = vec![front.helpers.h1.clone(), front.helpers.payment_mask.clone()];
    let original_message = gamma_combine_messages(&trace.c1, &c2_messages, front.schedule.gamma)?;
    let original_codeword = gamma_combine_codewords_for_len(
        &front.encoded_c1,
        &front.c2.encoded_columns,
        front.schedule.gamma,
        encoder.codeword_len(),
    )?;
    let points = [
        front.schedule.z,
        aspis_statement::xor11_point(&front.schedule.z),
    ];
    let mut relation = IncrementalRelation::new(
        original_message.clone(),
        &points,
        [QM31::ONE, front.schedule.second_point_scale],
    )?;
    let mut combined_codeword = original_codeword.clone();
    let mut transcript = front.transcript_after_gamma.clone();
    let mut later_roots = [[0u8; 32]; CANDIDATE_ROUND_COUNT - 1];
    let mut circle_ood_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES];
    let mut line_ood_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut mu = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut alpha = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    let mut fold_nonces = [0u64; CANDIDATE_ROUND_COUNT];
    let mut pow_valid = front.batch_pow_valid;

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = transcript
                    .challenge_secure_circle_point()
                    .map_err(CandidatePrefixBuildError::from)?;
                circle_ood_points[sample] = point;
                let value = relation.evaluate_circle_ood(point)?;
                absorb_ood_value(
                    &mut transcript,
                    label::M31_CIRCLE_OOD_VALUE,
                    round,
                    sample,
                    value,
                );
                mu[round][sample] = transcript.challenge_qm31()?;
                relation.add_circle_ood(point, value, mu[round][sample])?;
            } else {
                let x = transcript
                    .challenge_ood_qm31()
                    .map_err(CandidatePrefixBuildError::from)?;
                line_ood_points[round - 1][sample] = x;
                let value = relation.evaluate_line_ood(x)?;
                absorb_ood_value(
                    &mut transcript,
                    label::M31_LINE_OOD_VALUE,
                    round,
                    sample,
                    value,
                );
                mu[round][sample] = transcript.challenge_qm31()?;
                relation.add_line_ood(x, value, mu[round][sample])?;
            }
        }
        let polynomial = relation.polynomial()?;
        absorb_relation_sumcheck(&mut transcript, round, &polynomial);
        let bits = aspis_core::circle_prefix::RATE16_HARDENED_FOLD_POW_BITS[round];
        fold_nonces[round] = pow_nonce(&transcript, bits, pow_mode);
        pow_valid &= transcript.grinding_ok(fold_nonces[round], bits);
        absorb_fold_pow(&mut transcript, round, fold_nonces[round]);
        alpha[round] = transcript.challenge_qm31()?;
        relation.fold(alpha[round])?;
        combined_codeword = fold_candidate_codeword_round_for_domain_log(
            &combined_codeword,
            alpha[round],
            round,
            14,
        )?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            later_roots[round] = combined_candidate_layer_root_for_domain_log(
                &combined_codeword,
                round + 1,
                14,
                hash,
            )?;
            absorb_round_root(&mut transcript, round + 1, &later_roots[round]);
        }
    }

    let relation = relation.finish()?;
    if relation.point_claims
        != compressed_statement_claims(&front.material.statement_evaluations, front.schedule.gamma)
    {
        return Err(PaymentHidingPrefixBuildError::Consistency(
            "profile-14 relation point claims differ from the safe statement block",
        ));
    }
    if combined_codeword.len() != 64 {
        return Err(PaymentHidingPrefixBuildError::Consistency(
            "profile-14 final codeword is not the rate-1/16 64-value layer",
        ));
    }
    for (index, evaluation) in combined_codeword.iter().enumerate() {
        let expected = evaluate_final_line_tensor_at_query_for_domain_log(
            relation.final_coefficients,
            index << 6,
            14,
        )
        .map_err(CircleCandidateError::from)?;
        if *evaluation != expected {
            return Err(PaymentHidingPrefixBuildError::Consistency(
                "profile-14 final codeword differs from its natural final tensor",
            ));
        }
    }
    absorb_final(&mut transcript, &relation.final_coefficients);
    let state_before_grinding = transcript.diagnostic_state();
    let nonce = pow_nonce(&transcript, PAYMENT_HIDING_GRINDING_BITS, pow_mode);
    pow_valid &= transcript.grinding_ok(nonce, PAYMENT_HIDING_GRINDING_BITS);
    transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes());
    let queries = sample_payment_hiding_queries(&mut transcript)?;
    let schedule = PaymentHidingTranscriptScheduleResult {
        prefix: front.schedule,
        circle_ood_points,
        line_ood_points,
        mu,
        alpha,
        state_before_grinding,
        queries,
        state_after_queries: transcript.diagnostic_state(),
    };
    let parameters = CircleRelationParameters {
        z: front.schedule.z,
        xor11_z: aspis_statement::xor11_point(&front.schedule.z),
        point_rule: CircleRelationPointRule::PaymentBits013,
        point_scales: [QM31::ONE, front.schedule.second_point_scale],
        layer0_ood_points: circle_ood_points,
        later_ood_x: line_ood_points,
        ood_mixes: mu,
        alphas: alpha,
    };
    validate_circle_relation(&original_message, &parameters, &relation)
        .map_err(CandidatePrefixBuildError::from)?;

    let mut material = front.material.clone();
    material.later_roots = later_roots;
    material.ood_values = relation.ood_values;
    material.relation_sumchecks = relation.sumchecks;
    material.final_coefficients = relation.final_coefficients;
    material.nonce = nonce;
    material.fold_nonces = fold_nonces;
    let prefix_bytes = serialize_payment_hiding_prefix(&material);
    let parsed = PaymentHidingCandidatePrefix::parse_exact(&prefix_bytes)?;
    aspis_core::circle_hiding_verify::verify_payment_hiding_relation(&parsed, &schedule).map_err(
        |_| {
            PaymentHidingPrefixBuildError::Consistency(
                "core profile-14 relation replay rejected the generated prefix",
            )
        },
    )?;
    let folds = build_fold_commitments_for_domain_log(
        &original_codeword,
        &original_message,
        alpha,
        14,
        hash,
    )?;
    if folds.roots != later_roots || folds.final_coefficients != relation.final_coefficients {
        return Err(PaymentHidingPrefixBuildError::Consistency(
            "profile-14 opening commitments differ from the sequential prefix",
        ));
    }
    let c1_leaves = c1_layer0_leaves_for_codeword_len(&front.encoded_c1, encoder.codeword_len())?;
    let suffix = serialize_candidate_openings_for_fiber_count_with_c2(
        &queries,
        &c1_leaves,
        &front.c2.leaves,
        &folds,
        encoder.codeword_len() / 4,
        hash,
    )?;
    let mut bytes = Vec::with_capacity(prefix_bytes.len() + suffix.len());
    bytes.extend_from_slice(&prefix_bytes);
    bytes.extend_from_slice(&suffix);
    // The transcript is no longer useful after proof construction and keeps
    // the returned object smaller.
    front.transcript_after_gamma = Transcript::new(hash);
    Ok(BuiltPaymentHidingProof {
        bytes,
        material,
        schedule,
        relation,
        pow_valid,
        front,
    })
}
