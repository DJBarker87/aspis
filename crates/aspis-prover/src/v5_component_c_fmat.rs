//! Offline frozen-q18 Component-C private-view matrix generator.
//!
//! This host-only module emits the intrinsic, unscaled `256 x 1023` map
//! `F_sigma`. Its rows are the four relation rounds (two OOD values and seven
//! sumcheck coefficients each), three authenticated later layers (18 fibres
//! by four slots each), and the four final coefficients. The deployed lane
//! coefficient `gamma^18` is deliberately not included in the matrix.
//!
//! This file defines no legal-difference space, `Delta`, C-DEC certificate,
//! verifier wire, proof bytes, or production integration.

use std::collections::BTreeMap;
use std::fmt;

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_fri::{
    normalized_circle_to_line_arity4_at_fiber_for_domain_log,
    normalized_line_arity4_at_fiber_for_domain_log,
};
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
};

use super::component_c::{
    v5_c_inactive_functional, V5ComponentCLane, V5_C_FREE_COORDINATES, V5_C_ROWS,
};
use super::component_c_emat::{
    V5ComponentCFrozenESchedule, V5_C_EMAT_KAT_BASIS_COLUMNS, V5_C_EMAT_QM31_BYTES,
    V5_C_EMAT_SCHEDULE_BYTES,
};
use super::component_c_runtime::{
    evaluate_component_c_runtime_private_view, V5ComponentCRuntimeError,
    V5ComponentCRuntimeSchedule,
};
use super::real_host_proof::V5RealHostArtifact;
use super::relation_prover::{V5RelationProverError, V5RelationTrace};
use super::spend_messages::{V5_FIBRE_SLOTS, V5_LATER_LAYERS};
use super::V5_DOMAIN_LOG;
use crate::circle_candidate::{CircleCandidateError, CircleEncoder};

pub const V5_C_FMAT_RELATION_ROWS: usize = CANDIDATE_ROUND_COUNT * (CANDIDATE_OOD_SAMPLES + 7);
pub const V5_C_FMAT_LATER_ROWS: usize = V5_LATER_LAYERS * 18 * V5_FIBRE_SLOTS;
pub const V5_C_FMAT_FINAL_ROWS: usize = CANDIDATE_FINAL_POLY_LEN;
pub const V5_C_FMAT_ROWS: usize =
    V5_C_FMAT_RELATION_ROWS + V5_C_FMAT_LATER_ROWS + V5_C_FMAT_FINAL_ROWS;
pub const V5_C_FMAT_COLUMNS: usize = V5_C_FREE_COORDINATES;
pub const V5_C_FMAT_MATRIX_BYTES: usize = V5_C_FMAT_ROWS * V5_C_FMAT_COLUMNS * V5_C_EMAT_QM31_BYTES;
pub const V5_C_FMAT_GAMMA18_INCLUDED: bool = false;

pub const V5_C_FMAT_ARTIFACT_MAGIC: [u8; 8] = *b"AV5FMT01";
pub const V5_C_FMAT_ARTIFACT_VERSION: u16 = 1;
/// Bit zero would mean the matrix entries already include `gamma^18`. It is
/// pinned clear for the intrinsic `F_sigma` convention.
pub const V5_C_FMAT_ARTIFACT_FLAGS: u16 = 0;
pub const V5_C_FMAT_ARTIFACT_HEADER_BYTES: usize = 128;

/// The F schedule embeds the exact v1 E schedule, then an eight-byte
/// convention record, gamma/kappa, OOD points, OOD mixes, and fold alphas.
pub const V5_C_FMAT_SCHEDULE_BYTES: usize = V5_C_EMAT_SCHEDULE_BYTES
    + 8
    + 2 * V5_C_EMAT_QM31_BYTES
    + 2 * 2 * V5_C_EMAT_QM31_BYTES
    + 3 * 2 * V5_C_EMAT_QM31_BYTES
    + 4 * 2 * V5_C_EMAT_QM31_BYTES
    + 4 * V5_C_EMAT_QM31_BYTES;

const SCHEDULE_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-fmat-schedule-v1";
const MATRIX_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-fmat-matrix-v1";
const VECTOR_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-fmat-vector-v1";

const _: () = assert!(V5_C_FMAT_RELATION_ROWS == 36);
const _: () = assert!(V5_C_FMAT_LATER_ROWS == 216);
const _: () = assert!(V5_C_FMAT_FINAL_ROWS == 4);
const _: () = assert!(V5_C_FMAT_ROWS == 256);
const _: () = assert!(V5_C_FMAT_COLUMNS == 1023);
const _: () = assert!(V5_C_FMAT_MATRIX_BYTES == 4_190_208);
const _: () = assert!(V5_C_FMAT_SCHEDULE_BYTES == 18_037);
const _: () = assert!(V5_LATER_LAYERS == CANDIDATE_ROUND_COUNT - 1);
const _: () = assert!(!V5_C_FMAT_GAMMA18_INCLUDED);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum V5ComponentCFmatError {
    BaseSchedule(super::component_c_emat::V5ComponentCEmatError),
    ChallengeZero { name: &'static str },
    MessageShape { expected: usize, actual: usize },
    CodewordShape { expected: usize, actual: usize },
    MatrixShape { expected: usize, actual: usize },
    FreeCoordinateRoundTrip { column: usize },
    InactiveFunctional { column: usize },
    SparseRelation { stage: &'static str },
    ReferenceParity { case: &'static str, index: usize },
    Linearity { case: &'static str },
    Gamma18Correspondence { row: usize },
    ArtifactShape,
    ArtifactHash { section: &'static str },
    Circle(CircleCandidateError),
    Relation(V5RelationProverError),
    Runtime(V5ComponentCRuntimeError),
    Weight(TensorWeightError),
}

impl fmt::Display for V5ComponentCFmatError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BaseSchedule(error) => write!(formatter, "frozen E schedule: {error}"),
            Self::ChallengeZero { name } => write!(formatter, "frozen {name} challenge is zero"),
            Self::MessageShape { expected, actual } => {
                write!(
                    formatter,
                    "message expected {expected} values, got {actual}"
                )
            }
            Self::CodewordShape { expected, actual } => {
                write!(
                    formatter,
                    "codeword expected {expected} values, got {actual}"
                )
            }
            Self::MatrixShape { expected, actual } => {
                write!(
                    formatter,
                    "matrix expected {expected} entries, got {actual}"
                )
            }
            Self::FreeCoordinateRoundTrip { column } => {
                write!(
                    formatter,
                    "free-coordinate basis {column} did not round-trip"
                )
            }
            Self::InactiveFunctional { column } => write!(
                formatter,
                "free-coordinate basis {column} left the inactive kernel"
            ),
            Self::SparseRelation { stage } => {
                write!(formatter, "sparse relation invariant failed at {stage}")
            }
            Self::ReferenceParity { case, index } => {
                write!(formatter, "{case} reference parity failed at {index}")
            }
            Self::Linearity { case } => write!(formatter, "linearity failed: {case}"),
            Self::Gamma18Correspondence { row } => {
                write!(formatter, "gamma^18 correspondence failed at row {row}")
            }
            Self::ArtifactShape => write!(formatter, "non-canonical Fmat artifact shape"),
            Self::ArtifactHash { section } => {
                write!(formatter, "Fmat artifact {section} hash mismatch")
            }
            Self::Circle(error) => write!(formatter, "circle arithmetic: {error}"),
            Self::Relation(error) => write!(formatter, "incremental relation: {error:?}"),
            Self::Runtime(error) => write!(formatter, "runtime downstream evaluator: {error:?}"),
            Self::Weight(error) => write!(formatter, "relation weight: {error:?}"),
        }
    }
}

impl std::error::Error for V5ComponentCFmatError {}

impl From<CircleCandidateError> for V5ComponentCFmatError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Circle(error)
    }
}

impl From<V5RelationProverError> for V5ComponentCFmatError {
    fn from(error: V5RelationProverError) -> Self {
        Self::Relation(error)
    }
}

impl From<V5ComponentCRuntimeError> for V5ComponentCFmatError {
    fn from(error: V5ComponentCRuntimeError) -> Self {
        Self::Runtime(error)
    }
}

impl From<TensorWeightError> for V5ComponentCFmatError {
    fn from(error: TensorWeightError) -> Self {
        Self::Weight(error)
    }
}

impl From<super::component_c_emat::V5ComponentCEmatError> for V5ComponentCFmatError {
    fn from(error: super::component_c_emat::V5ComponentCEmatError) -> Self {
        Self::BaseSchedule(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCFrozenFSchedule {
    pub base: V5ComponentCFrozenESchedule,
    /// Frozen transcript challenge used only by the deployed-scaling KAT.
    /// It does not enter any Fmat matrix entry.
    pub gamma: QM31,
    pub kappa: QM31,
    pub circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    pub line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    pub ood_mixes: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub alphas: [QM31; CANDIDATE_ROUND_COUNT],
}

fn write_qm31(bytes: &mut Vec<u8>, value: QM31) {
    let start = bytes.len();
    bytes.resize(start + V5_C_EMAT_QM31_BYTES, 0);
    value.write_le_bytes(&mut bytes[start..]);
}

impl V5ComponentCFrozenFSchedule {
    pub fn from_real_host_artifact(
        artifact: &V5RealHostArtifact,
    ) -> Result<Self, V5ComponentCFmatError> {
        let base = V5ComponentCFrozenESchedule::from_real_host_artifact(artifact)?;
        if artifact.challenges.gamma == QM31::ZERO {
            return Err(V5ComponentCFmatError::ChallengeZero { name: "gamma" });
        }
        if artifact.challenges.kappa == QM31::ZERO {
            return Err(V5ComponentCFmatError::ChallengeZero { name: "kappa" });
        }
        Ok(Self {
            base,
            gamma: artifact.challenges.gamma,
            kappa: artifact.challenges.kappa,
            circle_ood_points: artifact.ood_points_circle[0],
            line_ood_points: artifact.ood_points_line,
            ood_mixes: artifact.ood_mixes,
            alphas: artifact.alphas,
        })
    }

    pub fn gamma18(&self) -> QM31 {
        self.gamma.pow(18)
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = self.base.canonical_bytes();
        bytes.push(u8::from(V5_C_FMAT_GAMMA18_INCLUDED));
        bytes.extend_from_slice(&[0u8; 7]);
        write_qm31(&mut bytes, self.gamma);
        write_qm31(&mut bytes, self.kappa);
        for point in self.circle_ood_points {
            write_qm31(&mut bytes, point.x);
            write_qm31(&mut bytes, point.y);
        }
        for round in self.line_ood_points {
            for point in round {
                write_qm31(&mut bytes, point);
            }
        }
        for round in self.ood_mixes {
            for mix in round {
                write_qm31(&mut bytes, mix);
            }
        }
        for alpha in self.alphas {
            write_qm31(&mut bytes, alpha);
        }
        debug_assert_eq!(bytes.len(), V5_C_FMAT_SCHEDULE_BYTES);
        bytes
    }

    pub fn sha256(&self) -> [u8; 32] {
        crate::host_hashv(&[SCHEDULE_HASH_DOMAIN, &self.canonical_bytes()])
    }
}

fn materialize_weights(weights: &WeightAccumulator, len: usize) -> Vec<QM31> {
    (0..len)
        .map(|index| weights.weight_at(index as u32))
        .collect()
}

struct FrozenLinearRelationSchedule {
    before_round: Vec<Vec<QM31>>,
    polynomial_weights: Vec<Vec<QM31>>,
    evaluations: Vec<[Vec<QM31>; CANDIDATE_OOD_SAMPLES]>,
    final_weights: Vec<QM31>,
}

impl FrozenLinearRelationSchedule {
    fn new(schedule: &V5ComponentCFrozenFSchedule) -> Result<Self, V5ComponentCFmatError> {
        let kappa2 = schedule.kappa.square();
        let kappa3 = kappa2.mul(schedule.kappa);
        let mut weights = WeightAccumulator::empty(10);
        for (point, scale) in schedule
            .base
            .points
            .iter()
            .zip([QM31::ONE, schedule.kappa, kappa2])
        {
            weights.add_multilinear(scale, point.to_vec())?;
        }
        weights.add_grouped_64x16_binary_masks(schedule.base.inactive_masks)?;
        weights.add_dense(
            schedule
                .base
                .terminal_covector
                .iter()
                .copied()
                .map(|value| kappa3.mul(value))
                .collect(),
        )?;

        let mut before_round = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
        let mut polynomial_weights = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
        let mut evaluations = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
        let mut len = V5_C_ROWS;
        for round in 0..CANDIDATE_ROUND_COUNT {
            before_round.push(materialize_weights(&weights, len));
            let round_evaluations = core::array::from_fn(|sample| {
                let mut evaluation = WeightAccumulator::empty(10 - 2 * round as u32);
                let result = if round == 0 {
                    evaluation.add_circle_tensor(QM31::ONE, schedule.circle_ood_points[sample])
                } else {
                    evaluation
                        .add_line_tensor(QM31::ONE, schedule.line_ood_points[round - 1][sample])
                };
                result.expect("frozen F schedule has the exact round tensor width");
                materialize_weights(&evaluation, len)
            });
            for sample in 0..CANDIDATE_OOD_SAMPLES {
                if round == 0 {
                    weights.add_circle_tensor(
                        schedule.ood_mixes[round][sample],
                        schedule.circle_ood_points[sample],
                    )?;
                } else {
                    weights.add_line_tensor(
                        schedule.ood_mixes[round][sample],
                        schedule.line_ood_points[round - 1][sample],
                    )?;
                }
            }
            evaluations.push(round_evaluations);
            polynomial_weights.push(materialize_weights(&weights, len));
            weights.fold(schedule.alphas[round]);
            len /= V5_FIBRE_SLOTS;
        }
        if len != CANDIDATE_FINAL_POLY_LEN {
            return Err(V5ComponentCFmatError::SparseRelation {
                stage: "final length",
            });
        }
        Ok(Self {
            before_round,
            polynomial_weights,
            evaluations,
            final_weights: materialize_weights(&weights, len),
        })
    }
}

type SparseTerms = BTreeMap<usize, QM31>;

fn lane_terms(lane: &V5ComponentCLane) -> SparseTerms {
    lane.values()
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, value)| *value != QM31::ZERO)
        .collect()
}

fn sparse_dot(terms: &SparseTerms, weights: &[QM31]) -> QM31 {
    terms.iter().fold(QM31::ZERO, |sum, (&index, &value)| {
        sum.add(value.mul(weights[index]))
    })
}

fn sparse_basis_polynomial(scale: QM31, index: usize, weights: &[QM31]) -> SumcheckPolynomial {
    let slot = index & (V5_FIBRE_SLOTS - 1);
    let base = index - slot;
    let dual = [
        weights[base],
        weights[base + 3],
        weights[base + 2],
        weights[base + 1],
    ];
    let mut polynomial = [QM31::ZERO; 7];
    for (degree, weight) in dual.into_iter().enumerate() {
        polynomial[slot + degree] = scale.mul(weight).half().half();
    }
    polynomial
}

fn fold_sparse_terms(terms: &SparseTerms, alpha: QM31) -> SparseTerms {
    let powers = [QM31::ONE, alpha, alpha.square(), alpha.pow(3)];
    let mut folded = SparseTerms::new();
    for (&index, &value) in terms {
        let contribution = value.mul(powers[index & (V5_FIBRE_SLOTS - 1)]);
        let target = folded.entry(index / V5_FIBRE_SLOTS).or_insert(QM31::ZERO);
        *target = target.add(contribution);
    }
    folded.retain(|_, value| *value != QM31::ZERO);
    folded
}

fn evaluate_sparse_relation(
    schedule: &V5ComponentCFrozenFSchedule,
    linear: &FrozenLinearRelationSchedule,
    initial_terms: &SparseTerms,
) -> Result<
    (
        [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
        [SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
        [QM31; CANDIDATE_FINAL_POLY_LEN],
    ),
    V5ComponentCFmatError,
> {
    let mut terms = initial_terms.clone();
    let mut running_claim = sparse_dot(&terms, &linear.before_round[0]);
    let mut ood_values = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut polynomials = [[QM31::ZERO; 7]; CANDIDATE_ROUND_COUNT];

    for round in 0..CANDIDATE_ROUND_COUNT {
        if sparse_dot(&terms, &linear.before_round[round]) != running_claim {
            return Err(V5ComponentCFmatError::SparseRelation {
                stage: "before round",
            });
        }
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            let value = sparse_dot(&terms, &linear.evaluations[round][sample]);
            ood_values[round][sample] = value;
            running_claim = running_claim.add(schedule.ood_mixes[round][sample].mul(value));
        }

        let mut polynomial = [QM31::ZERO; 7];
        for (&index, &scale) in &terms {
            let basis = sparse_basis_polynomial(scale, index, &linear.polynomial_weights[round]);
            for (output, contribution) in polynomial.iter_mut().zip(basis) {
                *output = output.add(contribution);
            }
        }
        if boundary_sum(&polynomial) != running_claim {
            return Err(V5ComponentCFmatError::SparseRelation { stage: "boundary" });
        }
        polynomials[round] = polynomial;
        running_claim = evaluate(&polynomial, schedule.alphas[round]);
        terms = fold_sparse_terms(&terms, schedule.alphas[round]);
    }

    if sparse_dot(&terms, &linear.final_weights) != running_claim {
        return Err(V5ComponentCFmatError::SparseRelation { stage: "final dot" });
    }
    let mut final_coefficients = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (index, value) in terms {
        if index >= CANDIDATE_FINAL_POLY_LEN {
            return Err(V5ComponentCFmatError::SparseRelation {
                stage: "final coefficient index",
            });
        }
        final_coefficients[index] = value;
    }
    Ok((ood_values, polynomials, final_coefficients))
}

fn sparse_folded_basis_value(
    encoder: &CircleEncoder,
    schedule: &V5ComponentCFrozenFSchedule,
    row: usize,
    layer: usize,
    index: usize,
    memo: &mut BTreeMap<(usize, usize, usize), QM31>,
) -> Result<QM31, V5ComponentCFmatError> {
    if let Some(value) = memo.get(&(row, layer, index)) {
        return Ok(*value);
    }
    let value = if layer == 0 {
        QM31::from_cm31(CM31::from_m31(encoder.encode_c1_basis_value(row, index)?))
    } else {
        let mut values = [QM31::ZERO; V5_FIBRE_SLOTS];
        for (slot, value) in values.iter_mut().enumerate() {
            *value = sparse_folded_basis_value(
                encoder,
                schedule,
                row,
                layer - 1,
                V5_FIBRE_SLOTS * index + slot,
                memo,
            )?;
        }
        if layer == 1 {
            normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alphas[0],
                V5_DOMAIN_LOG,
                index,
            )
            .map_err(|_| V5ComponentCFmatError::SparseRelation {
                stage: "circle-to-line fold",
            })?
        } else {
            normalized_line_arity4_at_fiber_for_domain_log(
                values,
                schedule.alphas[layer - 1],
                V5_DOMAIN_LOG,
                (layer - 1) as u8,
                index,
            )
            .map_err(|_| V5ComponentCFmatError::SparseRelation { stage: "line fold" })?
        }
    };
    memo.insert((row, layer, index), value);
    Ok(value)
}

fn evaluate_sparse_later(
    schedule: &V5ComponentCFrozenFSchedule,
    encoder: &CircleEncoder,
    terms: &SparseTerms,
) -> Result<[QM31; V5_C_FMAT_LATER_ROWS], V5ComponentCFmatError> {
    let mut output = [QM31::ZERO; V5_C_FMAT_LATER_ROWS];
    let mut cursor = 0usize;
    let mut memo = BTreeMap::new();
    for layer in 0..V5_LATER_LAYERS {
        for fibre in schedule.base.later_fibres[layer] {
            for slot in 0..V5_FIBRE_SLOTS {
                let index = V5_FIBRE_SLOTS * fibre as usize + slot;
                output[cursor] =
                    terms
                        .iter()
                        .try_fold(QM31::ZERO, |sum, (&row, &coefficient)| {
                            let basis = sparse_folded_basis_value(
                                encoder,
                                schedule,
                                row,
                                layer + 1,
                                index,
                                &mut memo,
                            )?;
                            Ok::<_, V5ComponentCFmatError>(sum.add(coefficient.mul(basis)))
                        })?;
                cursor += 1;
            }
        }
    }
    debug_assert_eq!(cursor, V5_C_FMAT_LATER_ROWS);
    Ok(output)
}

fn pack_f_view(
    ood_values: &[[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    polynomials: &[SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
    later: &[QM31; V5_C_FMAT_LATER_ROWS],
    final_coefficients: &[QM31; CANDIDATE_FINAL_POLY_LEN],
) -> [QM31; V5_C_FMAT_ROWS] {
    let mut output = [QM31::ZERO; V5_C_FMAT_ROWS];
    let mut cursor = 0usize;
    for round in 0..CANDIDATE_ROUND_COUNT {
        for value in ood_values[round] {
            output[cursor] = value;
            cursor += 1;
        }
        for value in polynomials[round] {
            output[cursor] = value;
            cursor += 1;
        }
    }
    output[cursor..cursor + V5_C_FMAT_LATER_ROWS].copy_from_slice(later);
    cursor += V5_C_FMAT_LATER_ROWS;
    output[cursor..].copy_from_slice(final_coefficients);
    output
}

fn evaluate_sparse_with_context(
    schedule: &V5ComponentCFrozenFSchedule,
    linear: &FrozenLinearRelationSchedule,
    encoder: &CircleEncoder,
    free: &[QM31; V5_C_FMAT_COLUMNS],
) -> Result<[QM31; V5_C_FMAT_ROWS], V5ComponentCFmatError> {
    let lane = V5ComponentCLane::encode_free_coordinates(free);
    let terms = lane_terms(&lane);
    let (ood_values, polynomials, final_coefficients) =
        evaluate_sparse_relation(schedule, linear, &terms)?;
    let later = evaluate_sparse_later(schedule, encoder, &terms)?;
    Ok(pack_f_view(
        &ood_values,
        &polynomials,
        &later,
        &final_coefficients,
    ))
}

pub fn evaluate_component_c_f_sparse(
    schedule: &V5ComponentCFrozenFSchedule,
    free: &[QM31; V5_C_FMAT_COLUMNS],
) -> Result<[QM31; V5_C_FMAT_ROWS], V5ComponentCFmatError> {
    let linear = FrozenLinearRelationSchedule::new(schedule)?;
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    evaluate_sparse_with_context(schedule, &linear, &encoder, free)
}

pub fn inactive_claim(
    values: &[QM31],
    inactive_masks: &[u16; 64],
) -> Result<QM31, V5ComponentCFmatError> {
    if values.len() != V5_C_ROWS {
        return Err(V5ComponentCFmatError::MessageShape {
            expected: V5_C_ROWS,
            actual: values.len(),
        });
    }
    Ok(values
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| inactive_masks[row >> 4] & (1 << (row & 15)) != 0)
        .fold(QM31::ZERO, |sum, (_, value)| sum.add(value)))
}

/// Full deployed-arithmetic evaluator at a fixed transcript schedule. It is
/// the differential oracle for sparse Fmat generation and for the
/// `X + gamma^18 c` correspondence KAT.
pub fn evaluate_frozen_private_view_reference(
    schedule: &V5ComponentCFrozenFSchedule,
    coefficients: &[QM31],
    codeword: &[QM31],
    expected_inactive_claim: QM31,
) -> Result<[QM31; V5_C_FMAT_ROWS], V5ComponentCFmatError> {
    let runtime_schedule = V5ComponentCRuntimeSchedule {
        points: schedule.base.points,
        terminal_covector: schedule.base.terminal_covector,
        inactive_masks: schedule.base.inactive_masks,
        kappa: schedule.kappa,
        circle_ood_points: schedule.circle_ood_points,
        line_ood_points: schedule.line_ood_points,
        ood_mixes: schedule.ood_mixes,
        alphas: schedule.alphas,
        later_fibres: [
            schedule.base.later_fibres[0].to_vec(),
            schedule.base.later_fibres[1].to_vec(),
            schedule.base.later_fibres[2].to_vec(),
        ],
    };
    let output = evaluate_component_c_runtime_private_view(
        &runtime_schedule,
        coefficients,
        codeword,
        expected_inactive_claim,
    )?;
    output
        .try_into()
        .map_err(|values: Vec<QM31>| V5ComponentCFmatError::MatrixShape {
            expected: V5_C_FMAT_ROWS,
            actual: values.len(),
        })
}

pub fn evaluate_component_c_f_reference(
    schedule: &V5ComponentCFrozenFSchedule,
    free: &[QM31; V5_C_FMAT_COLUMNS],
) -> Result<[QM31; V5_C_FMAT_ROWS], V5ComponentCFmatError> {
    let lane = V5ComponentCLane::encode_free_coordinates(free);
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    let codeword = encoder.encode_c2_message(lane.values())?;
    evaluate_frozen_private_view_reference(schedule, lane.values(), &codeword, QM31::ZERO)
}

fn free_basis(column: usize) -> [QM31; V5_C_FMAT_COLUMNS] {
    let mut free = [QM31::ZERO; V5_C_FMAT_COLUMNS];
    free[column] = QM31::ONE;
    free
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCFmat {
    entries: Vec<QM31>,
}

impl V5ComponentCFmat {
    pub fn generate(schedule: &V5ComponentCFrozenFSchedule) -> Result<Self, V5ComponentCFmatError> {
        let linear = FrozenLinearRelationSchedule::new(schedule)?;
        let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
        let mut entries = vec![QM31::ZERO; V5_C_FMAT_ROWS * V5_C_FMAT_COLUMNS];
        for column in 0..V5_C_FMAT_COLUMNS {
            let free = free_basis(column);
            let lane = V5ComponentCLane::encode_free_coordinates(&free);
            if lane.free_coordinates() != free {
                return Err(V5ComponentCFmatError::FreeCoordinateRoundTrip { column });
            }
            if v5_c_inactive_functional(lane.values()) != QM31::ZERO {
                return Err(V5ComponentCFmatError::InactiveFunctional { column });
            }
            let values = evaluate_sparse_with_context(schedule, &linear, &encoder, &free)?;
            for (row, value) in values.into_iter().enumerate() {
                entries[row * V5_C_FMAT_COLUMNS + column] = value;
            }
        }
        Ok(Self { entries })
    }

    pub fn from_entries(entries: Vec<QM31>) -> Result<Self, V5ComponentCFmatError> {
        let expected = V5_C_FMAT_ROWS * V5_C_FMAT_COLUMNS;
        if entries.len() != expected {
            return Err(V5ComponentCFmatError::MatrixShape {
                expected,
                actual: entries.len(),
            });
        }
        Ok(Self { entries })
    }

    pub fn entry(&self, row: usize, column: usize) -> QM31 {
        self.entries[row * V5_C_FMAT_COLUMNS + column]
    }

    pub fn column(&self, column: usize) -> [QM31; V5_C_FMAT_ROWS] {
        core::array::from_fn(|row| self.entry(row, column))
    }

    pub fn mul_vec(&self, vector: &[QM31; V5_C_FMAT_COLUMNS]) -> [QM31; V5_C_FMAT_ROWS] {
        core::array::from_fn(|row| {
            (0..V5_C_FMAT_COLUMNS).fold(QM31::ZERO, |sum, column| {
                sum.add(self.entry(row, column).mul(vector[column]))
            })
        })
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = vec![0u8; V5_C_FMAT_MATRIX_BYTES];
        for (index, value) in self.entries.iter().copied().enumerate() {
            value.write_le_bytes(
                &mut bytes[index * V5_C_EMAT_QM31_BYTES..(index + 1) * V5_C_EMAT_QM31_BYTES],
            );
        }
        bytes
    }

    pub fn sha256(&self) -> [u8; 32] {
        crate::host_hashv(&[MATRIX_HASH_DOMAIN, &self.canonical_bytes()])
    }

    pub fn encode_artifact(&self, schedule: &V5ComponentCFrozenFSchedule) -> Vec<u8> {
        let schedule_bytes = schedule.canonical_bytes();
        let matrix_bytes = self.canonical_bytes();
        let schedule_hash = crate::host_hashv(&[SCHEDULE_HASH_DOMAIN, &schedule_bytes]);
        let matrix_hash = crate::host_hashv(&[MATRIX_HASH_DOMAIN, &matrix_bytes]);
        let mut output = vec![0u8; V5_C_FMAT_ARTIFACT_HEADER_BYTES];
        output[0..8].copy_from_slice(&V5_C_FMAT_ARTIFACT_MAGIC);
        output[8..10].copy_from_slice(&V5_C_FMAT_ARTIFACT_VERSION.to_le_bytes());
        output[10..12].copy_from_slice(&V5_C_FMAT_ARTIFACT_FLAGS.to_le_bytes());
        output[12..16].copy_from_slice(&(V5_C_FMAT_ARTIFACT_HEADER_BYTES as u32).to_le_bytes());
        output[16..20].copy_from_slice(&(V5_C_FMAT_ROWS as u32).to_le_bytes());
        output[20..24].copy_from_slice(&(V5_C_FMAT_COLUMNS as u32).to_le_bytes());
        output[24..28].copy_from_slice(&(V5_C_FMAT_RELATION_ROWS as u32).to_le_bytes());
        output[28..32].copy_from_slice(&(V5_C_FMAT_LATER_ROWS as u32).to_le_bytes());
        output[32..36].copy_from_slice(&(V5_C_FMAT_FINAL_ROWS as u32).to_le_bytes());
        output[36..40].copy_from_slice(&18u32.to_le_bytes());
        output[40..44].copy_from_slice(&V5_DOMAIN_LOG.to_le_bytes());
        output[44..48].copy_from_slice(&P.to_le_bytes());
        output[48..52].copy_from_slice(&(V5_C_EMAT_QM31_BYTES as u32).to_le_bytes());
        output[52..56].copy_from_slice(&(schedule_bytes.len() as u32).to_le_bytes());
        output[56..64].copy_from_slice(&(matrix_bytes.len() as u64).to_le_bytes());
        output[64..96].copy_from_slice(&schedule_hash);
        output[96..128].copy_from_slice(&matrix_hash);
        output.extend_from_slice(&schedule_bytes);
        output.extend_from_slice(&matrix_bytes);
        output
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCFmatArtifactView<'a> {
    pub schedule_bytes: &'a [u8],
    pub matrix_bytes: &'a [u8],
    pub schedule_sha256: [u8; 32],
    pub matrix_sha256: [u8; 32],
}

fn read_u16(bytes: &[u8], start: usize) -> Result<u16, V5ComponentCFmatError> {
    Ok(u16::from_le_bytes(
        bytes
            .get(start..start + 2)
            .ok_or(V5ComponentCFmatError::ArtifactShape)?
            .try_into()
            .unwrap(),
    ))
}

fn read_u32(bytes: &[u8], start: usize) -> Result<u32, V5ComponentCFmatError> {
    Ok(u32::from_le_bytes(
        bytes
            .get(start..start + 4)
            .ok_or(V5ComponentCFmatError::ArtifactShape)?
            .try_into()
            .unwrap(),
    ))
}

fn read_u64(bytes: &[u8], start: usize) -> Result<u64, V5ComponentCFmatError> {
    Ok(u64::from_le_bytes(
        bytes
            .get(start..start + 8)
            .ok_or(V5ComponentCFmatError::ArtifactShape)?
            .try_into()
            .unwrap(),
    ))
}

pub fn validate_component_c_fmat_artifact(
    bytes: &[u8],
) -> Result<V5ComponentCFmatArtifactView<'_>, V5ComponentCFmatError> {
    if bytes.len() < V5_C_FMAT_ARTIFACT_HEADER_BYTES
        || bytes.get(0..8) != Some(V5_C_FMAT_ARTIFACT_MAGIC.as_slice())
        || read_u16(bytes, 8)? != V5_C_FMAT_ARTIFACT_VERSION
        || read_u16(bytes, 10)? != V5_C_FMAT_ARTIFACT_FLAGS
        || read_u32(bytes, 12)? as usize != V5_C_FMAT_ARTIFACT_HEADER_BYTES
        || read_u32(bytes, 16)? as usize != V5_C_FMAT_ROWS
        || read_u32(bytes, 20)? as usize != V5_C_FMAT_COLUMNS
        || read_u32(bytes, 24)? as usize != V5_C_FMAT_RELATION_ROWS
        || read_u32(bytes, 28)? as usize != V5_C_FMAT_LATER_ROWS
        || read_u32(bytes, 32)? as usize != V5_C_FMAT_FINAL_ROWS
        || read_u32(bytes, 36)? != 18
        || read_u32(bytes, 40)? != V5_DOMAIN_LOG
        || read_u32(bytes, 44)? != P
        || read_u32(bytes, 48)? as usize != V5_C_EMAT_QM31_BYTES
        || read_u32(bytes, 52)? as usize != V5_C_FMAT_SCHEDULE_BYTES
        || read_u64(bytes, 56)? as usize != V5_C_FMAT_MATRIX_BYTES
    {
        return Err(V5ComponentCFmatError::ArtifactShape);
    }
    let schedule_start = V5_C_FMAT_ARTIFACT_HEADER_BYTES;
    let matrix_start = schedule_start + V5_C_FMAT_SCHEDULE_BYTES;
    let end = matrix_start + V5_C_FMAT_MATRIX_BYTES;
    if end != bytes.len() {
        return Err(V5ComponentCFmatError::ArtifactShape);
    }
    let schedule_bytes = &bytes[schedule_start..matrix_start];
    if schedule_bytes[V5_C_EMAT_SCHEDULE_BYTES] != u8::from(V5_C_FMAT_GAMMA18_INCLUDED)
        || schedule_bytes[V5_C_EMAT_SCHEDULE_BYTES + 1..V5_C_EMAT_SCHEDULE_BYTES + 8] != [0u8; 7]
    {
        return Err(V5ComponentCFmatError::ArtifactShape);
    }
    let matrix_bytes = &bytes[matrix_start..end];
    let schedule_sha256: [u8; 32] = bytes[64..96].try_into().unwrap();
    let matrix_sha256: [u8; 32] = bytes[96..128].try_into().unwrap();
    if crate::host_hashv(&[SCHEDULE_HASH_DOMAIN, schedule_bytes]) != schedule_sha256 {
        return Err(V5ComponentCFmatError::ArtifactHash {
            section: "schedule",
        });
    }
    if crate::host_hashv(&[MATRIX_HASH_DOMAIN, matrix_bytes]) != matrix_sha256 {
        return Err(V5ComponentCFmatError::ArtifactHash { section: "matrix" });
    }
    if matrix_bytes
        .chunks_exact(V5_C_EMAT_QM31_BYTES)
        .any(|entry| QM31::from_le_bytes(entry).is_none())
    {
        return Err(V5ComponentCFmatError::ArtifactShape);
    }
    Ok(V5ComponentCFmatArtifactView {
        schedule_bytes,
        matrix_bytes,
        schedule_sha256,
        matrix_sha256,
    })
}

fn encode_qm31_vector(values: &[QM31]) -> Vec<u8> {
    let mut bytes = vec![0u8; values.len() * V5_C_EMAT_QM31_BYTES];
    for (index, value) in values.iter().copied().enumerate() {
        value.write_le_bytes(
            &mut bytes[index * V5_C_EMAT_QM31_BYTES..(index + 1) * V5_C_EMAT_QM31_BYTES],
        );
    }
    bytes
}

fn hash_qm31_vector(values: &[QM31]) -> [u8; 32] {
    crate::host_hashv(&[VECTOR_HASH_DOMAIN, &encode_qm31_vector(values)])
}

pub fn component_c_fmat_kat_word(seed: u32) -> [QM31; V5_C_FMAT_COLUMNS] {
    core::array::from_fn(|index| {
        let index = index as u64 + 1;
        let limb = |factor: u64, add: u64| {
            M31(((u64::from(seed) + factor * index + add) % u64::from(P)) as u32)
        };
        QM31 {
            c0: CM31::new(limb(1_039, 1), limb(1_049, 3)),
            c1: CM31::new(limb(1_051, 5), limb(1_061, 7)),
        }
    })
}

fn sparse_kat_word(values: &[(usize, QM31)]) -> [QM31; V5_C_FMAT_COLUMNS] {
    let mut output = [QM31::ZERO; V5_C_FMAT_COLUMNS];
    for &(index, value) in values {
        output[index] = value;
    }
    output
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCFmatKatMetadata {
    pub basis_columns: [usize; V5_C_EMAT_KAT_BASIS_COLUMNS.len()],
    pub basis_column_sha256: [[u8; 32]; V5_C_EMAT_KAT_BASIS_COLUMNS.len()],
    pub dense_input_sha256: [u8; 32],
    pub dense_output_sha256: [u8; 32],
    pub reference_parity_cases: usize,
    pub linearity_checks: usize,
    pub gamma18_included: bool,
}

pub fn build_component_c_fmat_kats(
    schedule: &V5ComponentCFrozenFSchedule,
    matrix: &V5ComponentCFmat,
) -> Result<V5ComponentCFmatKatMetadata, V5ComponentCFmatError> {
    let linear = FrozenLinearRelationSchedule::new(schedule)?;
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    let mut basis_hashes = [[0u8; 32]; V5_C_EMAT_KAT_BASIS_COLUMNS.len()];
    for (kat, column) in V5_C_EMAT_KAT_BASIS_COLUMNS.iter().copied().enumerate() {
        let free = free_basis(column);
        let sparse = evaluate_sparse_with_context(schedule, &linear, &encoder, &free)?;
        let reference = evaluate_component_c_f_reference(schedule, &free)?;
        let emitted = matrix.column(column);
        if sparse != reference || sparse != emitted {
            return Err(V5ComponentCFmatError::ReferenceParity {
                case: "basis",
                index: column,
            });
        }
        basis_hashes[kat] = hash_qm31_vector(&emitted);
    }

    let dense = component_c_fmat_kat_word(0xf031_5eed);
    let dense_reference = evaluate_component_c_f_reference(schedule, &dense)?;
    let dense_emitted = matrix.mul_vec(&dense);
    if dense_reference != dense_emitted {
        return Err(V5ComponentCFmatError::ReferenceParity {
            case: "dense",
            index: 0,
        });
    }

    let left = sparse_kat_word(&[
        (0, component_c_fmat_kat_word(11)[0]),
        (137, component_c_fmat_kat_word(13)[137]),
        (947, component_c_fmat_kat_word(17)[947]),
    ]);
    let right = sparse_kat_word(&[
        (1, component_c_fmat_kat_word(19)[1]),
        (137, component_c_fmat_kat_word(23)[137]),
        (1022, component_c_fmat_kat_word(29)[1022]),
    ]);
    let scalar = QM31 {
        c0: CM31::new(M31(31), M31(37)),
        c1: CM31::new(M31(41), M31(43)),
    };
    let sum = core::array::from_fn(|index| left[index].add(right[index]));
    let scaled = core::array::from_fn(|index| scalar.mul(left[index]));
    let e_left = evaluate_sparse_with_context(schedule, &linear, &encoder, &left)?;
    let e_right = evaluate_sparse_with_context(schedule, &linear, &encoder, &right)?;
    let e_sum = evaluate_sparse_with_context(schedule, &linear, &encoder, &sum)?;
    let expected_sum = core::array::from_fn(|row| e_left[row].add(e_right[row]));
    if e_sum != expected_sum || matrix.mul_vec(&sum) != expected_sum {
        return Err(V5ComponentCFmatError::Linearity { case: "additivity" });
    }
    let e_scaled = evaluate_sparse_with_context(schedule, &linear, &encoder, &scaled)?;
    let expected_scaled = core::array::from_fn(|row| scalar.mul(e_left[row]));
    if e_scaled != expected_scaled || matrix.mul_vec(&scaled) != expected_scaled {
        return Err(V5ComponentCFmatError::Linearity {
            case: "homogeneity",
        });
    }

    Ok(V5ComponentCFmatKatMetadata {
        basis_columns: V5_C_EMAT_KAT_BASIS_COLUMNS,
        basis_column_sha256: basis_hashes,
        dense_input_sha256: hash_qm31_vector(&dense),
        dense_output_sha256: hash_qm31_vector(&dense_emitted),
        reference_parity_cases: V5_C_EMAT_KAT_BASIS_COLUMNS.len() + 1,
        linearity_checks: 2,
        gamma18_included: V5_C_FMAT_GAMMA18_INCLUDED,
    })
}

pub fn check_gamma18_correspondence(
    schedule: &V5ComponentCFrozenFSchedule,
    matrix: &V5ComponentCFmat,
    baseline_message: &[QM31],
    baseline_codeword: &[QM31],
    free: &[QM31; V5_C_FMAT_COLUMNS],
) -> Result<(), V5ComponentCFmatError> {
    let claim = inactive_claim(baseline_message, &schedule.base.inactive_masks)?;
    let baseline = evaluate_frozen_private_view_reference(
        schedule,
        baseline_message,
        baseline_codeword,
        claim,
    )?;
    let lane = V5ComponentCLane::encode_free_coordinates(free);
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    let lane_codeword = encoder.encode_c2_message(lane.values())?;
    let gamma18 = schedule.gamma18();
    let perturbed_message = baseline_message
        .iter()
        .copied()
        .zip(lane.values().iter().copied())
        .map(|(baseline, mask)| baseline.add(gamma18.mul(mask)))
        .collect::<Vec<_>>();
    let perturbed_codeword = baseline_codeword
        .iter()
        .copied()
        .zip(lane_codeword)
        .map(|(baseline, mask)| baseline.add(gamma18.mul(mask)))
        .collect::<Vec<_>>();
    let perturbed = evaluate_frozen_private_view_reference(
        schedule,
        &perturbed_message,
        &perturbed_codeword,
        claim,
    )?;
    let intrinsic = matrix.mul_vec(free);
    for row in 0..V5_C_FMAT_ROWS {
        if perturbed[row].sub(baseline[row]) != gamma18.mul(intrinsic[row]) {
            return Err(V5ComponentCFmatError::Gamma18Correspondence { row });
        }
    }
    Ok(())
}

pub fn relation_rows(trace: &V5RelationTrace) -> [QM31; V5_C_FMAT_RELATION_ROWS] {
    let mut output = [QM31::ZERO; V5_C_FMAT_RELATION_ROWS];
    let mut cursor = 0usize;
    for round in 0..CANDIDATE_ROUND_COUNT {
        for value in trace.ood_values[round] {
            output[cursor] = value;
            cursor += 1;
        }
        for value in trace.sumchecks[round] {
            output[cursor] = value;
            cursor += 1;
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
    use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
    use aspis_statement::{binary_successor_point, xor12_point};

    use super::super::component_c::v5_c_pivot_row;
    use super::super::real_host_proof::V5_REAL_HOST_QUERY_COUNT;
    use super::super::spend_messages::V5_LAYER_ZERO_LEAVES;
    use super::super::split_layer_zero::v5_structured_terminal_covector;

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn synthetic_schedule() -> V5ComponentCFrozenFSchedule {
        let queries = core::array::from_fn(|index| 123 + 4_096 * index as u32);
        let indices =
            derive_circle_line_query_indices_for_count(&queries, V5_LAYER_ZERO_LEAVES).unwrap();
        assert_eq!(indices.layer0.len(), V5_REAL_HOST_QUERY_COUNT);
        assert!(indices
            .later
            .iter()
            .all(|layer| layer.len() == V5_REAL_HOST_QUERY_COUNT));
        let z = core::array::from_fn(|coordinate| q(100 + coordinate as u32));
        let points = [z, binary_successor_point(&z), xor12_point(&z)];
        let terminal_covector: [QM31; V5_C_ROWS] =
            v5_structured_terminal_covector(&z).try_into().unwrap();
        let base = V5ComponentCFrozenESchedule {
            statement_digest: [0x51; 32],
            transcript_state_after_queries: [0xa7; 32],
            roots: core::array::from_fn(|root| [root as u8 + 1; 32]),
            query_selector: 0,
            queries,
            layer0_fibres: indices.layer0.try_into().unwrap(),
            later_fibres: [
                indices.later[0].clone().try_into().unwrap(),
                indices.later[1].clone().try_into().unwrap(),
                indices.later[2].clone().try_into().unwrap(),
            ],
            points,
            terminal_covector,
            inactive_masks: atomic_state_only_copy_inactive_row_masks_v3(),
            pivot_row: v5_c_pivot_row(),
        };
        V5ComponentCFrozenFSchedule {
            base,
            gamma: q(500),
            kappa: q(501),
            circle_ood_points: [
                SecureCirclePoint {
                    x: QM31::ONE,
                    y: QM31::ZERO,
                },
                SecureCirclePoint {
                    x: QM31::ZERO,
                    y: QM31::ONE,
                },
            ],
            line_ood_points: core::array::from_fn(|round| {
                core::array::from_fn(|sample| q(600 + (2 * round + sample) as u32))
            }),
            ood_mixes: core::array::from_fn(|round| {
                core::array::from_fn(|sample| q(700 + (2 * round + sample) as u32))
            }),
            alphas: core::array::from_fn(|round| q(800 + round as u32)),
        }
    }

    #[test]
    fn fmat_sparse_reference_gamma18_and_artifact_teeth_are_exact() {
        let schedule = synthetic_schedule();
        assert!(!V5_C_FMAT_GAMMA18_INCLUDED);
        let matrix = V5ComponentCFmat::generate(&schedule).unwrap();
        assert_eq!(matrix.canonical_bytes().len(), V5_C_FMAT_MATRIX_BYTES);
        let kats = build_component_c_fmat_kats(&schedule, &matrix).unwrap();
        assert_eq!(kats.reference_parity_cases, 9);
        assert_eq!(kats.linearity_checks, 2);
        assert!(!kats.gamma18_included);

        let baseline_message = component_c_fmat_kat_word(0xba5e_0001).to_vec();
        let baseline_lane = V5ComponentCLane::encode_free_coordinates(
            &baseline_message.as_slice().try_into().unwrap(),
        );
        let baseline_message = baseline_lane.values().to_vec();
        let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
        let baseline_codeword = encoder.encode_c2_message(&baseline_message).unwrap();
        let perturbation = component_c_fmat_kat_word(0xc018_0002);
        check_gamma18_correspondence(
            &schedule,
            &matrix,
            &baseline_message,
            &baseline_codeword,
            &perturbation,
        )
        .unwrap();

        let bytes = matrix.canonical_bytes();
        for (index, encoded) in bytes.chunks_exact(V5_C_EMAT_QM31_BYTES).enumerate() {
            assert_eq!(QM31::from_le_bytes(encoded).unwrap(), matrix.entries[index]);
        }

        let artifact = matrix.encode_artifact(&schedule);
        assert_eq!(artifact, matrix.encode_artifact(&schedule));
        let view = validate_component_c_fmat_artifact(&artifact).unwrap();
        assert_eq!(view.schedule_sha256, schedule.sha256());
        assert_eq!(view.matrix_sha256, matrix.sha256());

        let mut schedule_mutation = artifact.clone();
        schedule_mutation[V5_C_FMAT_ARTIFACT_HEADER_BYTES] ^= 1;
        assert!(matches!(
            validate_component_c_fmat_artifact(&schedule_mutation),
            Err(V5ComponentCFmatError::ArtifactHash {
                section: "schedule"
            })
        ));
        let mut convention_mutation = artifact.clone();
        convention_mutation[V5_C_FMAT_ARTIFACT_HEADER_BYTES + V5_C_EMAT_SCHEDULE_BYTES] = 1;
        assert_eq!(
            validate_component_c_fmat_artifact(&convention_mutation),
            Err(V5ComponentCFmatError::ArtifactShape)
        );
        let mut matrix_mutation = artifact.clone();
        *matrix_mutation.last_mut().unwrap() ^= 1;
        assert!(matches!(
            validate_component_c_fmat_artifact(&matrix_mutation),
            Err(V5ComponentCFmatError::ArtifactHash { section: "matrix" })
        ));
        let mut noncanonical_matrix = artifact.clone();
        let matrix_start = V5_C_FMAT_ARTIFACT_HEADER_BYTES + V5_C_FMAT_SCHEDULE_BYTES;
        noncanonical_matrix[matrix_start..matrix_start + 4].copy_from_slice(&P.to_le_bytes());
        let matrix_hash = crate::host_hashv(&[
            MATRIX_HASH_DOMAIN,
            &noncanonical_matrix[matrix_start..matrix_start + V5_C_FMAT_MATRIX_BYTES],
        ]);
        noncanonical_matrix[96..128].copy_from_slice(&matrix_hash);
        assert_eq!(
            validate_component_c_fmat_artifact(&noncanonical_matrix),
            Err(V5ComponentCFmatError::ArtifactShape)
        );
        let mut header_mutation = artifact.clone();
        header_mutation[16..20].copy_from_slice(&255u32.to_le_bytes());
        assert_eq!(
            validate_component_c_fmat_artifact(&header_mutation),
            Err(V5ComponentCFmatError::ArtifactShape)
        );
        let mut trailing = artifact;
        trailing.push(0);
        assert_eq!(
            validate_component_c_fmat_artifact(&trailing),
            Err(V5ComponentCFmatError::ArtifactShape)
        );

        let mut swapped = matrix.clone();
        for column in 0..V5_C_FMAT_COLUMNS {
            swapped.entries.swap(column, V5_C_FMAT_COLUMNS + column);
        }
        assert!(build_component_c_fmat_kats(&schedule, &swapped).is_err());
        let later_start = V5_C_FMAT_RELATION_ROWS * V5_C_FMAT_COLUMNS;
        for column in 0..V5_C_FMAT_COLUMNS {
            swapped.entries.swap(
                later_start + column,
                later_start + V5_C_FMAT_COLUMNS + column,
            );
        }
        assert!(build_component_c_fmat_kats(&schedule, &swapped).is_err());
    }
}
