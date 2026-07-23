//! Isolated, fixed-width stress wire for the v5 PCS relation verifier.
//!
//! This checker executes the production relation kernel in its deployed
//! order: two circle OOD claims are mixed into round zero, two line OOD
//! claims are mixed into each later round, each degree-six sumcheck message
//! is checked and evaluated, the public covector is dual-folded, and the
//! resulting four weights are checked against the final tensor polynomial.
//! The payload is deliberately separate from every production proof grammar.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_fri::FIXED_TRACE_LOG_SIZE;
use aspis_core::field::QM31;
use aspis_core::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
    SUMCHECK_COEFFICIENTS,
};

pub const V5_RELATION_STRESS_MAGIC: [u8; 8] = *b"AV5REL01";
pub const V5_RELATION_STRESS_ROUNDS: usize = 4;
pub const V5_RELATION_STRESS_SAMPLES: usize = 2;
pub const V5_RELATION_STRESS_FINAL_COEFFICIENTS: usize = 4;

const QM31_BYTES: usize = 16;
const CIRCLE_POINT_VALUES: usize = V5_RELATION_STRESS_SAMPLES * 2;
const LINE_POINT_VALUES: usize = (V5_RELATION_STRESS_ROUNDS - 1) * V5_RELATION_STRESS_SAMPLES;
const MIX_VALUES: usize = V5_RELATION_STRESS_ROUNDS * V5_RELATION_STRESS_SAMPLES;
const ALPHA_VALUES: usize = V5_RELATION_STRESS_ROUNDS;
const OOD_VALUES: usize = V5_RELATION_STRESS_ROUNDS * V5_RELATION_STRESS_SAMPLES;
const SUMCHECK_VALUES: usize = V5_RELATION_STRESS_ROUNDS * SUMCHECK_COEFFICIENTS;

pub const V5_RELATION_STRESS_INITIAL_CLAIM_OFFSET: usize = V5_RELATION_STRESS_MAGIC.len();
pub const V5_RELATION_STRESS_CIRCLE_POINTS_OFFSET: usize =
    V5_RELATION_STRESS_INITIAL_CLAIM_OFFSET + QM31_BYTES;
pub const V5_RELATION_STRESS_LINE_POINTS_OFFSET: usize =
    V5_RELATION_STRESS_CIRCLE_POINTS_OFFSET + CIRCLE_POINT_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_MIXES_OFFSET: usize =
    V5_RELATION_STRESS_LINE_POINTS_OFFSET + LINE_POINT_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_ALPHAS_OFFSET: usize =
    V5_RELATION_STRESS_MIXES_OFFSET + MIX_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_OOD_VALUES_OFFSET: usize =
    V5_RELATION_STRESS_ALPHAS_OFFSET + ALPHA_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_SUMCHECKS_OFFSET: usize =
    V5_RELATION_STRESS_OOD_VALUES_OFFSET + OOD_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_FINAL_OFFSET: usize =
    V5_RELATION_STRESS_SUMCHECKS_OFFSET + SUMCHECK_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_BYTES: usize =
    V5_RELATION_STRESS_FINAL_OFFSET + V5_RELATION_STRESS_FINAL_COEFFICIENTS * QM31_BYTES;

const _: () = assert!(FIXED_TRACE_LOG_SIZE == 10);
const _: () = assert!(V5_RELATION_STRESS_BYTES == 1_016);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5RelationStressError {
    WrongLength,
    WrongMagic,
    NonCanonicalField { value: usize },
    WeightShape(TensorWeightError),
    BoundaryMismatch { round: usize },
    TerminalMismatch,
}

impl From<TensorWeightError> for V5RelationStressError {
    fn from(error: TensorWeightError) -> Self {
        Self::WeightShape(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5RelationStressSink {
    pub terminal_claim: QM31,
    pub terminal_dot: QM31,
}

fn decode_qm31(payload: &[u8], offset: usize, value: usize) -> Result<QM31, V5RelationStressError> {
    QM31::from_le_bytes(
        payload
            .get(offset..offset + QM31_BYTES)
            .ok_or(V5RelationStressError::WrongLength)?,
    )
    .ok_or(V5RelationStressError::NonCanonicalField { value })
}

/// Execute the exact four-round OOD/relation/final-tensor arithmetic over a
/// fixed-size canonical payload. No transcript state or production proof tag
/// is accepted here; the caller must bind this stress record separately.
pub fn verify_v5_relation_stress_payload(
    payload: &[u8],
) -> Result<V5RelationStressSink, V5RelationStressError> {
    if payload.len() != V5_RELATION_STRESS_BYTES {
        return Err(V5RelationStressError::WrongLength);
    }
    if payload[..V5_RELATION_STRESS_MAGIC.len()] != V5_RELATION_STRESS_MAGIC {
        return Err(V5RelationStressError::WrongMagic);
    }

    let mut field_index = 0usize;
    let mut decode = |offset| {
        let result = decode_qm31(payload, offset, field_index);
        field_index += 1;
        result
    };

    let mut running_claim = decode(V5_RELATION_STRESS_INITIAL_CLAIM_OFFSET)?;
    let mut circle_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; V5_RELATION_STRESS_SAMPLES];
    for (sample, point) in circle_points.iter_mut().enumerate() {
        let start = V5_RELATION_STRESS_CIRCLE_POINTS_OFFSET + sample * 2 * QM31_BYTES;
        point.x = decode(start)?;
        point.y = decode(start + QM31_BYTES)?;
    }

    let mut line_points = [[QM31::ZERO; V5_RELATION_STRESS_SAMPLES]; V5_RELATION_STRESS_ROUNDS - 1];
    for (round, points) in line_points.iter_mut().enumerate() {
        for (sample, point) in points.iter_mut().enumerate() {
            let ordinal = round * V5_RELATION_STRESS_SAMPLES + sample;
            *point = decode(V5_RELATION_STRESS_LINE_POINTS_OFFSET + ordinal * QM31_BYTES)?;
        }
    }

    let mut mixes = [[QM31::ZERO; V5_RELATION_STRESS_SAMPLES]; V5_RELATION_STRESS_ROUNDS];
    for (round, round_mixes) in mixes.iter_mut().enumerate() {
        for (sample, mix) in round_mixes.iter_mut().enumerate() {
            let ordinal = round * V5_RELATION_STRESS_SAMPLES + sample;
            *mix = decode(V5_RELATION_STRESS_MIXES_OFFSET + ordinal * QM31_BYTES)?;
        }
    }

    let mut alphas = [QM31::ZERO; V5_RELATION_STRESS_ROUNDS];
    for (round, alpha) in alphas.iter_mut().enumerate() {
        *alpha = decode(V5_RELATION_STRESS_ALPHAS_OFFSET + round * QM31_BYTES)?;
    }

    let mut ood_values = [[QM31::ZERO; V5_RELATION_STRESS_SAMPLES]; V5_RELATION_STRESS_ROUNDS];
    for (round, values) in ood_values.iter_mut().enumerate() {
        for (sample, output) in values.iter_mut().enumerate() {
            let ordinal = round * V5_RELATION_STRESS_SAMPLES + sample;
            *output = decode(V5_RELATION_STRESS_OOD_VALUES_OFFSET + ordinal * QM31_BYTES)?;
        }
    }

    let mut sumchecks = [[QM31::ZERO; SUMCHECK_COEFFICIENTS]; V5_RELATION_STRESS_ROUNDS];
    for (round, polynomial) in sumchecks.iter_mut().enumerate() {
        for (coefficient, output) in polynomial.iter_mut().enumerate() {
            let ordinal = round * SUMCHECK_COEFFICIENTS + coefficient;
            *output = decode(V5_RELATION_STRESS_SUMCHECKS_OFFSET + ordinal * QM31_BYTES)?;
        }
    }

    let mut final_coefficients = [QM31::ZERO; V5_RELATION_STRESS_FINAL_COEFFICIENTS];
    for (coefficient, output) in final_coefficients.iter_mut().enumerate() {
        *output = decode(V5_RELATION_STRESS_FINAL_OFFSET + coefficient * QM31_BYTES)?;
    }

    let mut weights = WeightAccumulator::empty(FIXED_TRACE_LOG_SIZE);
    for round in 0..V5_RELATION_STRESS_ROUNDS {
        for sample in 0..V5_RELATION_STRESS_SAMPLES {
            let mix = mixes[round][sample];
            if round == 0 {
                weights.add_circle_tensor(mix, circle_points[sample])?;
            } else {
                weights.add_line_tensor(mix, line_points[round - 1][sample])?;
            }
            running_claim = running_claim.add(mix.mul(ood_values[round][sample]));
        }

        let polynomial: SumcheckPolynomial = sumchecks[round];
        if boundary_sum(&polynomial) != running_claim {
            return Err(V5RelationStressError::BoundaryMismatch { round });
        }
        running_claim = evaluate(&polynomial, alphas[round]);
        weights.fold(alphas[round]);
    }

    let terminal_dot = weights.dot(&final_coefficients);
    if terminal_dot != running_claim {
        return Err(V5RelationStressError::TerminalMismatch);
    }
    Ok(V5RelationStressSink {
        terminal_claim: running_claim,
        terminal_dot,
    })
}

/// Build one deterministic accepting host record. The points, mixing
/// challenges, and fold challenges are all nonzero. The circle samples use
/// the same rational OOD parameterization as production. Zero claims and
/// messages make the acceptance witness transparent while retaining every
/// tensor-construction, sumcheck, fold, and final-dot operation.
#[cfg(not(target_os = "solana"))]
pub fn build_deterministic_v5_relation_stress_payload() -> Vec<u8> {
    use aspis_core::circle::secure_ood_circle_point_from_parameter;
    use aspis_core::field::{CM31, M31};

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed), M31(seed + 1)),
            c1: CM31::new(M31(seed + 2), M31(seed + 3)),
        }
    }

    fn write(output: &mut [u8], offset: usize, value: QM31) {
        value.write_le_bytes(&mut output[offset..offset + QM31_BYTES]);
    }

    let mut output = vec![0u8; V5_RELATION_STRESS_BYTES];
    output[..V5_RELATION_STRESS_MAGIC.len()].copy_from_slice(&V5_RELATION_STRESS_MAGIC);
    write(
        &mut output,
        V5_RELATION_STRESS_INITIAL_CLAIM_OFFSET,
        QM31::ZERO,
    );

    for sample in 0..V5_RELATION_STRESS_SAMPLES {
        let point = secure_ood_circle_point_from_parameter(q(100 + 20 * sample as u32))
            .expect("pinned non-singular secure OOD parameter");
        let start = V5_RELATION_STRESS_CIRCLE_POINTS_OFFSET + sample * 2 * QM31_BYTES;
        write(&mut output, start, point.x);
        write(&mut output, start + QM31_BYTES, point.y);
    }
    for ordinal in 0..LINE_POINT_VALUES {
        write(
            &mut output,
            V5_RELATION_STRESS_LINE_POINTS_OFFSET + ordinal * QM31_BYTES,
            q(1_000 + 20 * ordinal as u32),
        );
    }
    for ordinal in 0..MIX_VALUES {
        write(
            &mut output,
            V5_RELATION_STRESS_MIXES_OFFSET + ordinal * QM31_BYTES,
            q(2_000 + 20 * ordinal as u32),
        );
    }
    for round in 0..ALPHA_VALUES {
        write(
            &mut output,
            V5_RELATION_STRESS_ALPHAS_OFFSET + round * QM31_BYTES,
            q(3_000 + 20 * round as u32),
        );
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_payload_runs_every_relation_round() {
        let payload = build_deterministic_v5_relation_stress_payload();
        assert_eq!(payload.len(), V5_RELATION_STRESS_BYTES);
        assert_eq!(
            verify_v5_relation_stress_payload(&payload),
            Ok(V5RelationStressSink {
                terminal_claim: QM31::ZERO,
                terminal_dot: QM31::ZERO,
            })
        );
    }

    #[test]
    fn corrupted_sumcheck_is_rejected() {
        let mut payload = build_deterministic_v5_relation_stress_payload();
        QM31::ONE.write_le_bytes(
            &mut payload[V5_RELATION_STRESS_SUMCHECKS_OFFSET
                ..V5_RELATION_STRESS_SUMCHECKS_OFFSET + QM31_BYTES],
        );
        assert_eq!(
            verify_v5_relation_stress_payload(&payload),
            Err(V5RelationStressError::BoundaryMismatch { round: 0 })
        );
    }
}
