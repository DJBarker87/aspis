//! Host-only relation builder for the fixed M31 circle-PCS candidate.
//!
//! The caller supplies every scale, OOD point, OOD mix, and fold challenge.
//! This module does not sample a transcript, select a two-point batching rule,
//! authenticate a commitment, serialize a proof, or make a security claim.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_fri::{FIXED_ARITY4_ROUNDS, FIXED_TRACE_LOG_SIZE};
use aspis_core::field::{CM31, QM31};
use aspis_core::sumcheck::{
    boundary_sum, evaluate, polynomial_for_extension, SumcheckPolynomial, TensorWeightError,
    WeightAccumulator,
};

pub const CIRCLE_RELATION_POINT_COUNT: usize = 2;
pub const CIRCLE_RELATION_OOD_SAMPLES: usize = 2;
pub const CIRCLE_RELATION_ROUNDS: usize = FIXED_ARITY4_ROUNDS as usize;
pub const CIRCLE_RELATION_LATER_ROUNDS: usize = CIRCLE_RELATION_ROUNDS - 1;
pub const CIRCLE_RELATION_MESSAGE_LEN: usize = 1usize << FIXED_TRACE_LOG_SIZE;
pub const CIRCLE_RELATION_FINAL_LEN: usize =
    CIRCLE_RELATION_MESSAGE_LEN >> (2 * CIRCLE_RELATION_ROUNDS);

/// All non-message inputs to one deterministic relation trace.
///
/// `point_scales` deliberately has no batching-mode semantics. A caller may
/// supply fresh-kappa-like, disjoint-gamma-like, or any other explicit scales
/// without this arithmetic module selecting among them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleRelationParameters {
    pub z: [QM31; FIXED_TRACE_LOG_SIZE as usize],
    pub xor11_z: [QM31; FIXED_TRACE_LOG_SIZE as usize],
    pub point_rule: CircleRelationPointRule,
    pub point_scales: [QM31; CIRCLE_RELATION_POINT_COUNT],
    pub layer0_ood_points: [SecureCirclePoint; CIRCLE_RELATION_OOD_SAMPLES],
    pub later_ood_x: [[QM31; CIRCLE_RELATION_OOD_SAMPLES]; CIRCLE_RELATION_LATER_ROUNDS],
    pub ood_mixes: [[QM31; CIRCLE_RELATION_OOD_SAMPLES]; CIRCLE_RELATION_ROUNDS],
    pub alphas: [QM31; CIRCLE_RELATION_ROUNDS],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleRelationPointRule {
    LegacyLowBits2,
    PaymentBits013,
}

/// Honest relation messages and claims derived from one natural-order message.
///
/// `running_claims[0]` is the scaled two-point MLE claim. For round `r`,
/// `boundary_claims[r]` includes that round's two OOD claims, and
/// `running_claims[r + 1]` is the degree-6 polynomial evaluated at `alpha_r`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircleRelationTrace {
    pub point_claims: [QM31; CIRCLE_RELATION_POINT_COUNT],
    pub ood_values: [[QM31; CIRCLE_RELATION_OOD_SAMPLES]; CIRCLE_RELATION_ROUNDS],
    pub boundary_claims: [QM31; CIRCLE_RELATION_ROUNDS],
    pub sumchecks: [SumcheckPolynomial; CIRCLE_RELATION_ROUNDS],
    pub running_claims: [QM31; CIRCLE_RELATION_ROUNDS + 1],
    pub final_coefficients: [QM31; CIRCLE_RELATION_FINAL_LEN],
    pub terminal_claim: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleRelationError {
    MessageLength { expected: usize, actual: usize },
    Xor11PointMismatch { coordinate: usize },
    CirclePointNotOnCurve { sample: usize },
    CirclePointNotOod { sample: usize },
    LinePointNotOod { round: usize, sample: usize },
    WeightShape(TensorWeightError),
    PointClaimMismatch { point: usize },
    OodValueMismatch { round: usize, sample: usize },
    BoundaryMismatch { round: usize },
    SumcheckMismatch { round: usize },
    RunningClaimMismatch { step: usize },
    FinalCoefficientMismatch { coefficient: usize },
    TerminalMismatch,
}

impl core::fmt::Display for CircleRelationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::MessageLength { expected, actual } => {
                write!(
                    formatter,
                    "expected {expected} message values, got {actual}"
                )
            }
            Self::Xor11PointMismatch { coordinate } => {
                write!(formatter, "xor11(z) mismatch at coordinate {coordinate}")
            }
            Self::CirclePointNotOnCurve { sample } => {
                write!(
                    formatter,
                    "layer-zero OOD sample {sample} is not on the circle"
                )
            }
            Self::CirclePointNotOod { sample } => {
                write!(
                    formatter,
                    "layer-zero sample {sample} lies in the CM31 subfield"
                )
            }
            Self::LinePointNotOod { round, sample } => write!(
                formatter,
                "line OOD sample {sample} in round {round} lies in the CM31 subfield"
            ),
            Self::WeightShape(error) => write!(formatter, "relation weight shape error: {error:?}"),
            Self::PointClaimMismatch { point } => {
                write!(formatter, "point claim {point} does not match the message")
            }
            Self::OodValueMismatch { round, sample } => write!(
                formatter,
                "OOD value {sample} in round {round} does not match the message"
            ),
            Self::BoundaryMismatch { round } => {
                write!(formatter, "sumcheck boundary mismatch in round {round}")
            }
            Self::SumcheckMismatch { round } => {
                write!(formatter, "sumcheck polynomial mismatch in round {round}")
            }
            Self::RunningClaimMismatch { step } => {
                write!(formatter, "running relation claim mismatch at step {step}")
            }
            Self::FinalCoefficientMismatch { coefficient } => write!(
                formatter,
                "final natural coefficient {coefficient} does not match the folds"
            ),
            Self::TerminalMismatch => write!(formatter, "terminal relation dot mismatch"),
        }
    }
}

impl std::error::Error for CircleRelationError {}

impl From<TensorWeightError> for CircleRelationError {
    fn from(error: TensorWeightError) -> Self {
        Self::WeightShape(error)
    }
}

fn expected_xor11(
    z: &[QM31; FIXED_TRACE_LOG_SIZE as usize],
    rule: CircleRelationPointRule,
) -> [QM31; FIXED_TRACE_LOG_SIZE as usize] {
    let mut point = *z;
    match rule {
        CircleRelationPointRule::LegacyLowBits2 => {
            for coordinate in &mut point[FIXED_TRACE_LOG_SIZE as usize - 2..] {
                *coordinate = QM31::ONE.sub(*coordinate);
            }
        }
        CircleRelationPointRule::PaymentBits013 => {
            for coordinate in [6usize, 8, 9] {
                point[coordinate] = QM31::ONE.sub(point[coordinate]);
            }
        }
    }
    point
}

fn validate_parameters(parameters: &CircleRelationParameters) -> Result<(), CircleRelationError> {
    let expected = expected_xor11(&parameters.z, parameters.point_rule);
    for (coordinate, (actual, expected)) in parameters.xor11_z.iter().zip(expected).enumerate() {
        if *actual != expected {
            return Err(CircleRelationError::Xor11PointMismatch { coordinate });
        }
    }

    for (sample, point) in parameters.layer0_ood_points.iter().enumerate() {
        if point.x.square().add(point.y.square()) != QM31::ONE {
            return Err(CircleRelationError::CirclePointNotOnCurve { sample });
        }
        if point.x.c1 == CM31::ZERO && point.y.c1 == CM31::ZERO {
            return Err(CircleRelationError::CirclePointNotOod { sample });
        }
    }
    for (later_round, points) in parameters.later_ood_x.iter().enumerate() {
        for (sample, point) in points.iter().enumerate() {
            if point.c1 == CM31::ZERO {
                return Err(CircleRelationError::LinePointNotOod {
                    round: later_round + 1,
                    sample,
                });
            }
        }
    }
    Ok(())
}

fn point_claim(
    message: &[QM31],
    point: &[QM31; FIXED_TRACE_LOG_SIZE as usize],
) -> Result<QM31, CircleRelationError> {
    let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    weights.add_multilinear(QM31::ONE, point.to_vec())?;
    Ok(weights.dot(message))
}

fn add_round_ood_weights(
    round: usize,
    parameters: &CircleRelationParameters,
    coefficients: &[QM31],
    relation_weights: &mut WeightAccumulator,
) -> Result<[QM31; CIRCLE_RELATION_OOD_SAMPLES], CircleRelationError> {
    let mut values = [QM31::ZERO; CIRCLE_RELATION_OOD_SAMPLES];
    for (sample, output) in values.iter_mut().enumerate() {
        let mut evaluation_weights =
            WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE - 2 * round as u32);
        if round == 0 {
            let point = parameters.layer0_ood_points[sample];
            evaluation_weights.add_circle_tensor(QM31::ONE, point)?;
            relation_weights.add_circle_tensor(parameters.ood_mixes[round][sample], point)?;
        } else {
            let point = parameters.later_ood_x[round - 1][sample];
            evaluation_weights.add_line_tensor(QM31::ONE, point)?;
            relation_weights.add_line_tensor(parameters.ood_mixes[round][sample], point)?;
        }
        *output = evaluation_weights.dot(coefficients);
    }
    Ok(values)
}

fn fold_adjacent_natural(coefficients: &[QM31], alpha: QM31) -> Vec<QM31> {
    let alpha_squared = alpha.square();
    let alpha_cubed = alpha_squared.mul(alpha);
    coefficients
        .chunks_exact(4)
        .map(|chunk| {
            chunk[0]
                .add(alpha.mul(chunk[1]))
                .add(alpha_squared.mul(chunk[2]))
                .add(alpha_cubed.mul(chunk[3]))
        })
        .collect()
}

/// Build the complete four-round relation trace over one natural-order
/// combined QM31 message.
pub fn build_circle_relation(
    combined_message: &[QM31],
    parameters: &CircleRelationParameters,
) -> Result<CircleRelationTrace, CircleRelationError> {
    build_circle_relation_internal(combined_message, parameters, None)
}

/// Build the same relation while additionally proving that the coefficient
/// sum on `padding_start..padding_end` is zero. The claim adds no proof field:
/// its public value is zero and its sparse interval covector joins the first
/// relation accumulator before the existing four folds.
pub fn build_circle_relation_with_zero_interval(
    combined_message: &[QM31],
    parameters: &CircleRelationParameters,
    padding_start: usize,
    padding_end: usize,
) -> Result<CircleRelationTrace, CircleRelationError> {
    build_circle_relation_internal(
        combined_message,
        parameters,
        Some((padding_start, padding_end)),
    )
}

fn build_circle_relation_internal(
    combined_message: &[QM31],
    parameters: &CircleRelationParameters,
    zero_interval: Option<(usize, usize)>,
) -> Result<CircleRelationTrace, CircleRelationError> {
    if combined_message.len() != CIRCLE_RELATION_MESSAGE_LEN {
        return Err(CircleRelationError::MessageLength {
            expected: CIRCLE_RELATION_MESSAGE_LEN,
            actual: combined_message.len(),
        });
    }
    validate_parameters(parameters)?;

    let points = [&parameters.z, &parameters.xor11_z];
    let mut relation_weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    let mut point_claims = [QM31::ZERO; CIRCLE_RELATION_POINT_COUNT];
    let mut running_claim = QM31::ZERO;
    for point in 0..CIRCLE_RELATION_POINT_COUNT {
        point_claims[point] = point_claim(combined_message, points[point])?;
        relation_weights.add_multilinear(parameters.point_scales[point], points[point].to_vec())?;
        running_claim = running_claim.add(parameters.point_scales[point].mul(point_claims[point]));
    }
    if let Some((start, end)) = zero_interval {
        relation_weights.add_index_interval(QM31::ONE, start, end)?;
        // The public interval claim is exactly zero, so `running_claim` is
        // unchanged. A nonzero interval dot appears in the first boundary and
        // is rejected below.
    }

    let mut running_claims = [QM31::ZERO; CIRCLE_RELATION_ROUNDS + 1];
    running_claims[0] = running_claim;
    let mut ood_values = [[QM31::ZERO; CIRCLE_RELATION_OOD_SAMPLES]; CIRCLE_RELATION_ROUNDS];
    let mut boundary_claims = [QM31::ZERO; CIRCLE_RELATION_ROUNDS];
    let mut sumchecks = [[QM31::ZERO; 7]; CIRCLE_RELATION_ROUNDS];
    let mut coefficients = combined_message.to_vec();

    for round in 0..CIRCLE_RELATION_ROUNDS {
        ood_values[round] =
            add_round_ood_weights(round, parameters, &coefficients, &mut relation_weights)?;
        for (sample, value) in ood_values[round].iter().copied().enumerate() {
            running_claim = running_claim.add(parameters.ood_mixes[round][sample].mul(value));
        }
        boundary_claims[round] = running_claim;

        let polynomial = polynomial_for_extension(&coefficients, &relation_weights);
        if boundary_sum(&polynomial) != running_claim {
            return Err(CircleRelationError::BoundaryMismatch { round });
        }
        sumchecks[round] = polynomial;
        running_claim = evaluate(&polynomial, parameters.alphas[round]);
        running_claims[round + 1] = running_claim;
        relation_weights.fold(parameters.alphas[round]);
        coefficients = fold_adjacent_natural(&coefficients, parameters.alphas[round]);
    }

    let final_coefficients: [QM31; CIRCLE_RELATION_FINAL_LEN] =
        coefficients.try_into().map_err(|values: Vec<QM31>| {
            CircleRelationError::MessageLength {
                expected: CIRCLE_RELATION_FINAL_LEN,
                actual: values.len(),
            }
        })?;
    let terminal_claim = relation_weights.dot(&final_coefficients);
    if terminal_claim != running_claim {
        return Err(CircleRelationError::TerminalMismatch);
    }

    Ok(CircleRelationTrace {
        point_claims,
        ood_values,
        boundary_claims,
        sumchecks,
        running_claims,
        final_coefficients,
        terminal_claim,
    })
}

/// Recheck a host relation trace against its message and explicit parameters.
///
/// This is an arithmetic conformance helper, not a proof verifier: it receives
/// the whole message and performs no commitment authentication.
pub fn validate_circle_relation(
    combined_message: &[QM31],
    parameters: &CircleRelationParameters,
    trace: &CircleRelationTrace,
) -> Result<(), CircleRelationError> {
    let expected = build_circle_relation(combined_message, parameters)?;

    for point in 0..CIRCLE_RELATION_POINT_COUNT {
        if trace.point_claims[point] != expected.point_claims[point] {
            return Err(CircleRelationError::PointClaimMismatch { point });
        }
    }
    if trace.running_claims[0] != expected.running_claims[0] {
        return Err(CircleRelationError::RunningClaimMismatch { step: 0 });
    }
    for round in 0..CIRCLE_RELATION_ROUNDS {
        for sample in 0..CIRCLE_RELATION_OOD_SAMPLES {
            if trace.ood_values[round][sample] != expected.ood_values[round][sample] {
                return Err(CircleRelationError::OodValueMismatch { round, sample });
            }
        }
        if boundary_sum(&trace.sumchecks[round]) != trace.boundary_claims[round] {
            return Err(CircleRelationError::BoundaryMismatch { round });
        }
        if trace.boundary_claims[round] != expected.boundary_claims[round] {
            return Err(CircleRelationError::BoundaryMismatch { round });
        }
        if trace.sumchecks[round] != expected.sumchecks[round] {
            return Err(CircleRelationError::SumcheckMismatch { round });
        }
        if trace.running_claims[round + 1] != expected.running_claims[round + 1] {
            return Err(CircleRelationError::RunningClaimMismatch { step: round + 1 });
        }
    }
    for coefficient in 0..CIRCLE_RELATION_FINAL_LEN {
        if trace.final_coefficients[coefficient] != expected.final_coefficients[coefficient] {
            return Err(CircleRelationError::FinalCoefficientMismatch { coefficient });
        }
    }
    if trace.terminal_claim != trace.running_claims[CIRCLE_RELATION_ROUNDS]
        || trace.terminal_claim != expected.terminal_claim
    {
        return Err(CircleRelationError::TerminalMismatch);
    }
    Ok(())
}
