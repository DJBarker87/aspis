//! Sequential host builder for the M31 circle candidate.
//!
//! This module exists to prove that the candidate's commitments, claims,
//! relation messages, transcript challenges, folds, terminal tensor, grinding
//! witness, and query positions can all be produced in their actual causal
//! order. It builds both still-unselected one-lane comparison shapes. It does
//! not select either shape, construct openings, register a production KAT, or
//! make a security/CU claim.
//!
//! The two C2 columns accepted here are fixed host fixtures. They are not
//! derived from `lambda` and `chi`, and this builder does not claim that they
//! implement payment LogUp semantics.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_fri::{
    evaluate_final_line_tensor_at_query_for_domain_log, FIXED_TRACE_LOG_SIZE,
};
use aspis_core::circle_prefix::{
    run_candidate_transcript_schedule_host_for_shape, CandidateOneLaneBatchingMode,
    CandidatePrefix, CandidatePrefixError, CandidateProfileShape, CandidateTranscriptScheduleError,
    CandidateTranscriptScheduleResult, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_LOG_ROWS,
    CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_QUERY_COUNT, CANDIDATE_ROUND_COUNT,
    CANDIDATE_STATEMENT_POINT_COORDINATES, CANDIDATE_STATEMENT_VALUE_COUNT, ENCODED_QM31_LEN,
    SELECTED_CANDIDATE_SHAPE,
};
use aspis_core::field::{M31, QM31};
use aspis_core::proof::{HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR, ROOT_LEN};
use aspis_core::sumcheck::{
    boundary_sum, evaluate, polynomial_for_extension, SumcheckPolynomial, TensorWeightError,
    WeightAccumulator, SUMCHECK_BYTES, SUMCHECK_COEFFICIENTS,
};
use aspis_core::transcript::{
    label, ChallengeSampleExhausted, CirclePointSampleError, HashFn, OodSampleError, Transcript,
};

use crate::circle_candidate::{
    c1_layer0_root_for_codeword_len, c2_layer0_root_for_codeword_len,
    candidate_prefix_header_for_shape, candidate_statement_evaluations,
    combined_candidate_layer_root_for_domain_log, fold_adjacent_natural_arity4,
    fold_candidate_codeword_round_for_domain_log, gamma_combine_codewords_for_len,
    gamma_combine_messages, gamma_combine_statement_evaluations,
    serialize_candidate_prefix_for_shape, xor11_point, CandidatePrefixMaterial,
    CircleCandidateError, CircleEncoder, COMBINED_COMMITTED_LAYERS, TRACE_LEN,
};
use crate::circle_candidate_openings::CandidateOpeningBuildError;
use crate::circle_relation::{
    validate_circle_relation, CircleRelationError, CircleRelationParameters,
    CircleRelationPointRule, CircleRelationTrace,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidatePrefixBuildError {
    Candidate(CircleCandidateError),
    Relation(CircleRelationError),
    Prefix(CandidatePrefixError),
    ChallengeSampleExhausted,
    CirclePointSample(CirclePointSampleError),
    LinePointSample(OodSampleError),
    TranscriptReplay(CandidateTranscriptScheduleError),
    RelationShape(TensorWeightError),
    Opening(CandidateOpeningBuildError),
    Consistency(&'static str),
}

impl core::fmt::Display for CandidatePrefixBuildError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Candidate(error) => write!(formatter, "candidate arithmetic failed: {error}"),
            Self::Relation(error) => write!(formatter, "relation validation failed: {error}"),
            Self::Prefix(error) => write!(formatter, "candidate prefix parse failed: {error:?}"),
            Self::ChallengeSampleExhausted => {
                write!(formatter, "exact-uniform challenge sampler exhausted")
            }
            Self::CirclePointSample(error) => {
                write!(formatter, "secure circle point sampler failed: {error:?}")
            }
            Self::LinePointSample(error) => {
                write!(formatter, "line OOD sampler failed: {error:?}")
            }
            Self::TranscriptReplay(error) => {
                write!(formatter, "candidate transcript replay failed: {error:?}")
            }
            Self::RelationShape(error) => {
                write!(formatter, "relation tensor shape failed: {error:?}")
            }
            Self::Opening(error) => write!(formatter, "opening construction failed: {error:?}"),
            Self::Consistency(message) => write!(formatter, "candidate consistency: {message}"),
        }
    }
}

impl std::error::Error for CandidatePrefixBuildError {}

impl From<CircleCandidateError> for CandidatePrefixBuildError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Candidate(error)
    }
}

impl From<CircleRelationError> for CandidatePrefixBuildError {
    fn from(error: CircleRelationError) -> Self {
        Self::Relation(error)
    }
}

impl From<CandidatePrefixError> for CandidatePrefixBuildError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}

impl From<ChallengeSampleExhausted> for CandidatePrefixBuildError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

impl From<CirclePointSampleError> for CandidatePrefixBuildError {
    fn from(error: CirclePointSampleError) -> Self {
        Self::CirclePointSample(error)
    }
}

impl From<OodSampleError> for CandidatePrefixBuildError {
    fn from(error: OodSampleError) -> Self {
        Self::LinePointSample(error)
    }
}

impl From<TensorWeightError> for CandidatePrefixBuildError {
    fn from(error: TensorWeightError) -> Self {
        Self::RelationShape(error)
    }
}

impl From<CandidateOpeningBuildError> for CandidatePrefixBuildError {
    fn from(error: CandidateOpeningBuildError) -> Self {
        Self::Opening(error)
    }
}

/// Complete host-only result for one unselected candidate batching shape.
#[derive(Clone, Debug)]
pub struct BuiltCandidatePrefix<const QUERY_COUNT: usize = { CANDIDATE_QUERY_COUNT as usize }> {
    pub bytes: Vec<u8>,
    pub material: CandidatePrefixMaterial,
    pub batching_mode: CandidateOneLaneBatchingMode,
    pub schedule: CandidateTranscriptScheduleResult<QUERY_COUNT>,
    pub relation: CircleRelationTrace,
}

#[derive(Clone, Debug)]
pub struct BuiltFreshKappaCandidateProof<
    const QUERY_COUNT: usize = { CANDIDATE_QUERY_COUNT as usize },
> {
    pub bytes: Vec<u8>,
    pub prefix: BuiltCandidatePrefix<QUERY_COUNT>,
}

pub(crate) struct IncrementalRelation {
    coefficients: Vec<QM31>,
    weights: WeightAccumulator,
    point_claims: [QM31; 2],
    ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    boundary_claims: [QM31; CANDIDATE_ROUND_COUNT],
    sumchecks: [SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
    running_claims: [QM31; CANDIDATE_ROUND_COUNT + 1],
    running_claim: QM31,
    round: usize,
    samples: usize,
}

impl IncrementalRelation {
    pub(crate) fn new(
        coefficients: Vec<QM31>,
        points: &[[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES]; 2],
        point_scales: [QM31; 2],
    ) -> Result<Self, CandidatePrefixBuildError> {
        if coefficients.len() != TRACE_LEN {
            return Err(CandidatePrefixBuildError::Consistency(
                "combined message has the wrong length",
            ));
        }
        let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
        let mut point_claims = [QM31::ZERO; 2];
        let mut running_claim = QM31::ZERO;
        for point in 0..2 {
            let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
            evaluation.add_multilinear(QM31::ONE, points[point].to_vec())?;
            point_claims[point] = evaluation.dot(&coefficients);
            weights.add_multilinear(point_scales[point], points[point].to_vec())?;
            running_claim = running_claim.add(point_scales[point].mul(point_claims[point]));
        }
        let mut running_claims = [QM31::ZERO; CANDIDATE_ROUND_COUNT + 1];
        running_claims[0] = running_claim;
        Ok(Self {
            coefficients,
            weights,
            point_claims,
            ood_values: [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
            boundary_claims: [QM31::ZERO; CANDIDATE_ROUND_COUNT],
            sumchecks: [[QM31::ZERO; SUMCHECK_COEFFICIENTS]; CANDIDATE_ROUND_COUNT],
            running_claims,
            running_claim,
            round: 0,
            samples: 0,
        })
    }

    pub(crate) fn evaluate_circle_ood(
        &self,
        point: SecureCirclePoint,
    ) -> Result<QM31, CandidatePrefixBuildError> {
        if self.round != 0 || self.samples >= CANDIDATE_OOD_SAMPLES {
            return Err(CandidatePrefixBuildError::Consistency(
                "circle OOD sample requested outside round zero",
            ));
        }
        let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
        evaluation.add_circle_tensor(QM31::ONE, point)?;
        Ok(evaluation.dot(&self.coefficients))
    }

    pub(crate) fn add_circle_ood(
        &mut self,
        point: SecureCirclePoint,
        value: QM31,
        mix: QM31,
    ) -> Result<(), CandidatePrefixBuildError> {
        self.weights.add_circle_tensor(mix, point)?;
        self.ood_values[0][self.samples] = value;
        self.running_claim = self.running_claim.add(mix.mul(value));
        self.samples += 1;
        Ok(())
    }

    pub(crate) fn evaluate_line_ood(&self, x: QM31) -> Result<QM31, CandidatePrefixBuildError> {
        if self.round == 0
            || self.round >= CANDIDATE_ROUND_COUNT
            || self.samples >= CANDIDATE_OOD_SAMPLES
        {
            return Err(CandidatePrefixBuildError::Consistency(
                "line OOD sample requested outside a later round",
            ));
        }
        let mut evaluation = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE - 2 * self.round as u32);
        evaluation.add_line_tensor(QM31::ONE, x)?;
        Ok(evaluation.dot(&self.coefficients))
    }

    pub(crate) fn add_line_ood(
        &mut self,
        x: QM31,
        value: QM31,
        mix: QM31,
    ) -> Result<(), CandidatePrefixBuildError> {
        self.weights.add_line_tensor(mix, x)?;
        self.ood_values[self.round][self.samples] = value;
        self.running_claim = self.running_claim.add(mix.mul(value));
        self.samples += 1;
        Ok(())
    }

    pub(crate) fn polynomial(&mut self) -> Result<SumcheckPolynomial, CandidatePrefixBuildError> {
        if self.samples != CANDIDATE_OOD_SAMPLES {
            return Err(CandidatePrefixBuildError::Consistency(
                "sumcheck built before both OOD samples",
            ));
        }
        let polynomial = polynomial_for_extension(&self.coefficients, &self.weights);
        if boundary_sum(&polynomial) != self.running_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "sumcheck boundary does not equal the running claim",
            ));
        }
        self.boundary_claims[self.round] = self.running_claim;
        self.sumchecks[self.round] = polynomial;
        Ok(polynomial)
    }

    pub(crate) fn fold(&mut self, alpha: QM31) -> Result<(), CandidatePrefixBuildError> {
        if self.samples != CANDIDATE_OOD_SAMPLES || self.round >= CANDIDATE_ROUND_COUNT {
            return Err(CandidatePrefixBuildError::Consistency(
                "relation fold requested out of order",
            ));
        }
        self.running_claim = evaluate(&self.sumchecks[self.round], alpha);
        self.running_claims[self.round + 1] = self.running_claim;
        self.weights.fold(alpha);
        self.coefficients = fold_adjacent_natural_arity4(&self.coefficients, alpha);
        if self.weights.dot(&self.coefficients) != self.running_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "folded relation dot does not equal the running claim",
            ));
        }
        self.round += 1;
        self.samples = 0;
        Ok(())
    }

    pub(crate) fn finish(self) -> Result<CircleRelationTrace, CandidatePrefixBuildError> {
        if self.round != CANDIDATE_ROUND_COUNT
            || self.coefficients.len() != CANDIDATE_FINAL_POLY_LEN
        {
            return Err(CandidatePrefixBuildError::Consistency(
                "relation did not reach the four-coefficient terminal",
            ));
        }
        let final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN] = self
            .coefficients
            .try_into()
            .map_err(|_| CandidatePrefixBuildError::Consistency("terminal conversion failed"))?;
        let terminal_claim = self.weights.dot(&final_coefficients);
        if terminal_claim != self.running_claim {
            return Err(CandidatePrefixBuildError::Consistency(
                "terminal relation dot does not equal the running claim",
            ));
        }
        Ok(CircleRelationTrace {
            point_claims: self.point_claims,
            ood_values: self.ood_values,
            boundary_claims: self.boundary_claims,
            sumchecks: self.sumchecks,
            running_claims: self.running_claims,
            final_coefficients,
            terminal_claim,
        })
    }
}

fn write_statement_evaluations(
    evaluations: &[QM31; CANDIDATE_STATEMENT_VALUE_COUNT],
) -> [u8; CANDIDATE_STATEMENT_VALUE_COUNT * ENCODED_QM31_LEN] {
    let mut bytes = [0u8; CANDIDATE_STATEMENT_VALUE_COUNT * ENCODED_QM31_LEN];
    for (index, value) in evaluations.iter().enumerate() {
        value.write_le_bytes(&mut bytes[index * ENCODED_QM31_LEN..][..ENCODED_QM31_LEN]);
    }
    bytes
}

fn encode_statement_points(
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> [u8; 2 * CANDIDATE_STATEMENT_POINT_COORDINATES * ENCODED_QM31_LEN] {
    let points = [*z, xor11_point(z)];
    let mut bytes = [0u8; 2 * CANDIDATE_STATEMENT_POINT_COORDINATES * ENCODED_QM31_LEN];
    for (point, coordinates) in points.iter().enumerate() {
        for (coordinate, value) in coordinates.iter().enumerate() {
            let index = point * CANDIDATE_STATEMENT_POINT_COORDINATES + coordinate;
            value.write_le_bytes(&mut bytes[index * ENCODED_QM31_LEN..][..ENCODED_QM31_LEN]);
        }
    }
    bytes
}

fn absorb_round_root(transcript: &mut Transcript, layer: usize, root: &[u8; ROOT_LEN]) {
    let mut record = [0u8; 1 + ROOT_LEN];
    record[0] = layer as u8;
    record[1..].copy_from_slice(root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn absorb_ood_value(
    transcript: &mut Transcript,
    label: u8,
    layer: usize,
    sample: usize,
    value: QM31,
) {
    let mut record = [0u8; 2 + ENCODED_QM31_LEN];
    record[0] = layer as u8;
    record[1] = sample as u8;
    value.write_le_bytes(&mut record[2..]);
    transcript.absorb(label, &record);
}

fn absorb_sumcheck(transcript: &mut Transcript, layer: usize, polynomial: SumcheckPolynomial) {
    let mut record = [0u8; 1 + SUMCHECK_BYTES];
    record[0] = layer as u8;
    for (coefficient, value) in polynomial.iter().enumerate() {
        value.write_le_bytes(
            &mut record
                [1 + coefficient * ENCODED_QM31_LEN..1 + (coefficient + 1) * ENCODED_QM31_LEN],
        );
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
    let mut bytes = [0u8; CANDIDATE_FINAL_POLY_LEN * ENCODED_QM31_LEN];
    for (index, value) in coefficients.iter().enumerate() {
        value.write_le_bytes(&mut bytes[index * ENCODED_QM31_LEN..][..ENCODED_QM31_LEN]);
    }
    transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, &bytes);
}

fn check_replay<const QUERY_COUNT: usize>(
    parsed: &CandidatePrefix<'_>,
    material: &CandidatePrefixMaterial,
    built_lambda: QM31,
    built_chi: QM31,
    built_gamma: QM31,
    built_kappa: Option<QM31>,
    built_second_scale: QM31,
    circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    mu: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    alpha: [QM31; CANDIDATE_ROUND_COUNT],
    queries: [u32; QUERY_COUNT],
    replay: &CandidateTranscriptScheduleResult<QUERY_COUNT>,
) -> Result<(), CandidatePrefixBuildError> {
    if parsed.c1_root != &material.c1_root || parsed.c2_root != &material.c2_root {
        return Err(CandidatePrefixBuildError::Consistency(
            "parsed layer-zero roots differ",
        ));
    }
    for index in 0..CANDIDATE_STATEMENT_VALUE_COUNT {
        if parsed.statement_evaluation(index) != Some(material.statement_evaluations[index]) {
            return Err(CandidatePrefixBuildError::Consistency(
                "parsed statement evaluation differs",
            ));
        }
    }
    for layer in 0..CANDIDATE_ROUND_COUNT {
        if layer > 0 && parsed.rounds[layer].root.copied() != Some(material.later_roots[layer - 1])
        {
            return Err(CandidatePrefixBuildError::Consistency(
                "parsed later root differs",
            ));
        }
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if parsed.rounds[layer].ood_value(sample) != Some(material.ood_values[layer][sample]) {
                return Err(CandidatePrefixBuildError::Consistency(
                    "parsed OOD value differs",
                ));
            }
        }
        for coefficient in 0..SUMCHECK_COEFFICIENTS {
            if parsed.rounds[layer].sumcheck_coefficient(coefficient)
                != Some(material.sumchecks[layer][coefficient])
            {
                return Err(CandidatePrefixBuildError::Consistency(
                    "parsed sumcheck coefficient differs",
                ));
            }
        }
    }
    for coefficient in 0..CANDIDATE_FINAL_POLY_LEN {
        if parsed.final_coefficient(coefficient) != Some(material.final_coefficients[coefficient]) {
            return Err(CandidatePrefixBuildError::Consistency(
                "parsed terminal coefficient differs",
            ));
        }
    }
    if parsed.nonce != material.nonce
        || parsed.fold_nonces != material.fold_nonces
        || replay.prefix.lambda != built_lambda
        || replay.prefix.chi != built_chi
        || replay.prefix.gamma != built_gamma
        || replay.kappa != built_kappa
        || replay.second_point_scale != built_second_scale
        || replay.circle_ood_points != circle_ood_points
        || replay.line_ood_points != line_ood_points
        || replay.mu != mu
        || replay.alpha != alpha
        || replay.queries != queries
    {
        return Err(CandidatePrefixBuildError::Consistency(
            "transcript replay differs from sequential generation",
        ));
    }
    Ok(())
}

/// Build, serialize, parse, replay, and independently revalidate one complete
/// candidate prefix in the exact causal transcript order.
pub fn build_candidate_prefix_sequential(
    c1_messages: &[Vec<M31>],
    c2_fixture_messages: &[Vec<QM31>],
    z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    statement_digest: [u8; 32],
    hash: HashFn,
    batching_mode: CandidateOneLaneBatchingMode,
) -> Result<BuiltCandidatePrefix, CandidatePrefixBuildError> {
    build_candidate_prefix_sequential_for_shape::<{ CANDIDATE_QUERY_COUNT as usize }>(
        c1_messages,
        c2_fixture_messages,
        z,
        statement_digest,
        hash,
        batching_mode,
        SELECTED_CANDIDATE_SHAPE,
    )
}

pub fn build_candidate_prefix_sequential_for_shape<const QUERY_COUNT: usize>(
    c1_messages: &[Vec<M31>],
    c2_fixture_messages: &[Vec<QM31>],
    z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    statement_digest: [u8; 32],
    hash: HashFn,
    batching_mode: CandidateOneLaneBatchingMode,
    shape: CandidateProfileShape,
) -> Result<BuiltCandidatePrefix<QUERY_COUNT>, CandidatePrefixBuildError> {
    if usize::from(shape.query_count) != QUERY_COUNT {
        return Err(CandidatePrefixBuildError::Consistency(
            "profile query count differs from the const-generic shape",
        ));
    }
    let domain_log_size = CANDIDATE_LOG_ROWS + shape.log_blowup;
    let codeword_len = 1usize << domain_log_size;
    let encoder = CircleEncoder::new_for_domain_log(domain_log_size);
    let encoded_c1 = encoder.encode_c1_columns(c1_messages)?;
    let encoded_c2 = encoder.encode_c2_columns(c2_fixture_messages)?;
    let c1_root = c1_layer0_root_for_codeword_len(&encoded_c1, codeword_len, hash)?;
    let c2_root = c2_layer0_root_for_codeword_len(&encoded_c2, codeword_len, hash)?;
    let statement_evaluations =
        candidate_statement_evaluations(c1_messages, c2_fixture_messages, &z)?;

    let mut header_bytes = [0u8; HEADER_LEN];
    candidate_prefix_header_for_shape(shape).write(&mut header_bytes);
    let statement_evaluation_bytes = write_statement_evaluations(&statement_evaluations);
    let statement_point_bytes = encode_statement_points(&z);

    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, &statement_digest);
    absorb_round_root(&mut transcript, 0, &c1_root);
    let lambda = transcript.challenge_qm31()?;
    let chi = transcript.challenge_qm31()?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2_root);
    transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &statement_point_bytes);
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        &statement_evaluation_bytes,
    );
    let gamma = transcript.challenge_qm31()?;
    let kappa = match batching_mode {
        CandidateOneLaneBatchingMode::FreshKappa => Some(transcript.challenge_qm31()?),
        CandidateOneLaneBatchingMode::DisjointGamma51 => None,
    };
    let second_point_scale = kappa.unwrap_or_else(|| gamma.pow(51));

    let combined_message = gamma_combine_messages(c1_messages, c2_fixture_messages, gamma)?;
    let mut combined_codeword =
        gamma_combine_codewords_for_len(&encoded_c1, &encoded_c2, gamma, codeword_len)?;
    let points = [z, xor11_point(&z)];
    let mut relation =
        IncrementalRelation::new(combined_message, &points, [QM31::ONE, second_point_scale])?;
    if relation.point_claims != gamma_combine_statement_evaluations(&statement_evaluations, gamma) {
        return Err(CandidatePrefixBuildError::Consistency(
            "gamma-compressed statement claims differ from the combined message",
        ));
    }

    let mut later_roots = [[0u8; ROOT_LEN]; COMBINED_COMMITTED_LAYERS];
    let mut circle_ood_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES];
    let mut line_ood_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut mu = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut alpha = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    let mut fold_nonces = [0u64; CANDIDATE_ROUND_COUNT];

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = transcript.challenge_secure_circle_point()?;
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
                let x = transcript.challenge_ood_qm31()?;
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
        let sumcheck = relation.polynomial()?;
        absorb_sumcheck(&mut transcript, round, sumcheck);
        let fold_pow_bits = shape.fold_pow_bits[round];
        if fold_pow_bits != 0 {
            fold_nonces[round] = crate::find_grinding_nonce(&transcript, fold_pow_bits);
            absorb_fold_pow(&mut transcript, round, fold_nonces[round]);
        }
        alpha[round] = transcript.challenge_qm31()?;
        relation.fold(alpha[round])?;
        combined_codeword = fold_candidate_codeword_round_for_domain_log(
            &combined_codeword,
            alpha[round],
            round,
            domain_log_size,
        )?;
        if round < COMBINED_COMMITTED_LAYERS {
            later_roots[round] = combined_candidate_layer_root_for_domain_log(
                &combined_codeword,
                round + 1,
                domain_log_size,
                hash,
            )?;
            absorb_round_root(&mut transcript, round + 1, &later_roots[round]);
        }
    }

    let relation = relation.finish()?;
    let expected_final_len = 1usize << (domain_log_size - 8);
    if combined_codeword.len() != expected_final_len {
        return Err(CandidatePrefixBuildError::Consistency(
            "final codeword has the wrong domain length",
        ));
    }
    for (index, evaluation) in combined_codeword.iter().enumerate() {
        let expected = evaluate_final_line_tensor_at_query_for_domain_log(
            relation.final_coefficients,
            index << 6,
            domain_log_size,
        )
        .map_err(CircleCandidateError::from)?;
        if *evaluation != expected {
            return Err(CandidatePrefixBuildError::Consistency(
                "final codeword and natural terminal tensor differ",
            ));
        }
    }
    absorb_final(&mut transcript, &relation.final_coefficients);
    let nonce = crate::find_grinding_nonce(&transcript, shape.grinding_bits);
    transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes());
    let query_log_size = CANDIDATE_LOG_ROWS + shape.log_blowup - 2;
    let queries: [u32; QUERY_COUNT] = transcript
        .challenge_queries(QUERY_COUNT, 1u32 << query_log_size)
        .try_into()
        .unwrap();

    let material = CandidatePrefixMaterial {
        c1_root,
        c2_root,
        statement_evaluations,
        later_roots,
        ood_values: relation.ood_values,
        sumchecks: relation.sumchecks,
        final_coefficients: relation.final_coefficients,
        nonce,
        fold_nonces,
    };
    let bytes = serialize_candidate_prefix_for_shape(&material, shape);
    let parsed = CandidatePrefix::parse_exact_for_shape(&bytes, shape)?;
    let schedule = run_candidate_transcript_schedule_host_for_shape::<QUERY_COUNT>(
        hash,
        &parsed,
        &statement_digest,
        &z,
        batching_mode,
        shape.grinding_bits,
    )
    .map_err(CandidatePrefixBuildError::TranscriptReplay)?;
    check_replay(
        &parsed,
        &material,
        lambda,
        chi,
        gamma,
        kappa,
        second_point_scale,
        circle_ood_points,
        line_ood_points,
        mu,
        alpha,
        queries,
        &schedule,
    )?;

    let parameters = CircleRelationParameters {
        z,
        xor11_z: xor11_point(&z),
        point_rule: CircleRelationPointRule::LegacyLowBits2,
        point_scales: [QM31::ONE, second_point_scale],
        layer0_ood_points: circle_ood_points,
        later_ood_x: line_ood_points,
        ood_mixes: mu,
        alphas: alpha,
    };
    let combined_message = gamma_combine_messages(c1_messages, c2_fixture_messages, gamma)?;
    validate_circle_relation(&combined_message, &parameters, &relation)?;

    Ok(BuiltCandidatePrefix {
        bytes,
        material,
        batching_mode,
        schedule,
        relation,
    })
}

/// Build the complete selected fresh-kappa prefix and authenticated suffix.
pub fn build_fresh_kappa_candidate_proof(
    c1_messages: &[Vec<M31>],
    c2_fixture_messages: &[Vec<QM31>],
    z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    statement_digest: [u8; 32],
    hash: HashFn,
) -> Result<BuiltFreshKappaCandidateProof, CandidatePrefixBuildError> {
    build_fresh_kappa_candidate_proof_for_shape::<{ CANDIDATE_QUERY_COUNT as usize }>(
        c1_messages,
        c2_fixture_messages,
        z,
        statement_digest,
        hash,
        SELECTED_CANDIDATE_SHAPE,
    )
}

pub fn build_fresh_kappa_candidate_proof_for_shape<const QUERY_COUNT: usize>(
    c1_messages: &[Vec<M31>],
    c2_fixture_messages: &[Vec<QM31>],
    z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    statement_digest: [u8; 32],
    hash: HashFn,
    shape: CandidateProfileShape,
) -> Result<BuiltFreshKappaCandidateProof<QUERY_COUNT>, CandidatePrefixBuildError> {
    let prefix = build_candidate_prefix_sequential_for_shape::<QUERY_COUNT>(
        c1_messages,
        c2_fixture_messages,
        z,
        statement_digest,
        hash,
        CandidateOneLaneBatchingMode::FreshKappa,
        shape,
    )?;
    let domain_log_size = CANDIDATE_LOG_ROWS + shape.log_blowup;
    let codeword_len = 1usize << domain_log_size;
    let encoder = CircleEncoder::new_for_domain_log(domain_log_size);
    let encoded_c1 = encoder.encode_c1_columns(c1_messages)?;
    let encoded_c2 = encoder.encode_c2_columns(c2_fixture_messages)?;
    let combined_codeword = gamma_combine_codewords_for_len(
        &encoded_c1,
        &encoded_c2,
        prefix.schedule.prefix.gamma,
        codeword_len,
    )?;
    let combined_message = gamma_combine_messages(
        c1_messages,
        c2_fixture_messages,
        prefix.schedule.prefix.gamma,
    )?;
    let folds = crate::circle_candidate::build_fold_commitments_for_domain_log(
        &combined_codeword,
        &combined_message,
        prefix.schedule.alpha,
        domain_log_size,
        hash,
    )?;
    if folds.roots != prefix.material.later_roots
        || folds.final_coefficients != prefix.material.final_coefficients
    {
        return Err(CandidatePrefixBuildError::Consistency(
            "opening commitments differ from the selected prefix",
        ));
    }
    let suffix = crate::circle_candidate_openings::serialize_candidate_openings_for_fiber_count(
        &prefix.schedule.queries,
        &crate::circle_candidate::c1_layer0_leaves_for_codeword_len(&encoded_c1, codeword_len)?,
        &crate::circle_candidate::c2_layer0_leaves_for_codeword_len(&encoded_c2, codeword_len)?,
        &folds,
        codeword_len / 4,
        hash,
    )?;
    let mut bytes = Vec::with_capacity(shape.prefix_len() + suffix.len());
    bytes.extend_from_slice(&prefix.bytes);
    bytes.extend_from_slice(&suffix);
    Ok(BuiltFreshKappaCandidateProof { bytes, prefix })
}
