//! V5-only stress path for the complete four-round PCS relation algebra.
//!
//! This module deliberately owns no production dispatch.  It parses a fixed
//! payload, adds both OOD observations at each round, checks the relation
//! sumcheck boundary, advances the running claim, dual-folds the public
//! covector, and checks the disclosed final polynomial.  The local-validator
//! composite calls it after constructing the v5 relation accumulator.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::field::QM31;
use aspis_core::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
    SUMCHECK_COEFFICIENTS,
};

pub const V5_RELATION_STRESS_ROUNDS: usize = 4;
pub const V5_RELATION_STRESS_OOD_SAMPLES: usize = 2;
pub const V5_RELATION_STRESS_FINAL_COEFFICIENTS: usize = 4;
const QM31_BYTES: usize = 16;

const CIRCLE_COORDINATES: usize = 2 * V5_RELATION_STRESS_OOD_SAMPLES;
const LINE_POINTS: usize = (V5_RELATION_STRESS_ROUNDS - 1) * V5_RELATION_STRESS_OOD_SAMPLES;
const OOD_VALUES: usize = V5_RELATION_STRESS_ROUNDS * V5_RELATION_STRESS_OOD_SAMPLES;
const OOD_MIXES: usize = OOD_VALUES;
const SUMCHECK_VALUES: usize = V5_RELATION_STRESS_ROUNDS * SUMCHECK_COEFFICIENTS;

pub const V5_RELATION_STRESS_CIRCLE_OFFSET: usize = 0;
pub const V5_RELATION_STRESS_LINE_OFFSET: usize =
    V5_RELATION_STRESS_CIRCLE_OFFSET + CIRCLE_COORDINATES * QM31_BYTES;
pub const V5_RELATION_STRESS_OOD_OFFSET: usize =
    V5_RELATION_STRESS_LINE_OFFSET + LINE_POINTS * QM31_BYTES;
pub const V5_RELATION_STRESS_MIX_OFFSET: usize =
    V5_RELATION_STRESS_OOD_OFFSET + OOD_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_SUMCHECK_OFFSET: usize =
    V5_RELATION_STRESS_MIX_OFFSET + OOD_MIXES * QM31_BYTES;
pub const V5_RELATION_STRESS_FINAL_OFFSET: usize =
    V5_RELATION_STRESS_SUMCHECK_OFFSET + SUMCHECK_VALUES * QM31_BYTES;
pub const V5_RELATION_STRESS_BYTES: usize =
    V5_RELATION_STRESS_FINAL_OFFSET + V5_RELATION_STRESS_FINAL_COEFFICIENTS * QM31_BYTES;

const _: () = assert!(V5_RELATION_STRESS_BYTES == 928);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5RelationStressError {
    NonCanonicalField { offset: usize },
    InvalidCirclePoint { sample: usize },
    ZeroMix { round: usize, sample: usize },
    ZeroAlpha { round: usize },
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
pub struct VerifiedV5RelationStress {
    pub final_coefficients: [QM31; V5_RELATION_STRESS_FINAL_COEFFICIENTS],
    pub terminal_claim: QM31,
}

/// A structured public covector which shares the relation's four dual folds
/// without being materialized inside [`WeightAccumulator`].  Component B's
/// compact degree-27 weights implement this interface in the composite probe.
pub trait V5RelationStressAdditive {
    fn fold(&mut self, alpha: QM31);
    fn dot(&self, final_coefficients: &[QM31; V5_RELATION_STRESS_FINAL_COEFFICIENTS]) -> QM31;
}

#[derive(Clone, Copy, Default)]
struct NoAdditiveWeights;

impl V5RelationStressAdditive for NoAdditiveWeights {
    #[inline(always)]
    fn fold(&mut self, _alpha: QM31) {}

    #[inline(always)]
    fn dot(&self, _final_coefficients: &[QM31; V5_RELATION_STRESS_FINAL_COEFFICIENTS]) -> QM31 {
        QM31::ZERO
    }
}

fn decode_qm31(
    bytes: &[u8; V5_RELATION_STRESS_BYTES],
    offset: usize,
) -> Result<QM31, V5RelationStressError> {
    QM31::from_le_bytes(&bytes[offset..offset + QM31_BYTES])
        .ok_or(V5RelationStressError::NonCanonicalField { offset })
}

fn decode_indexed(
    bytes: &[u8; V5_RELATION_STRESS_BYTES],
    offset: usize,
    index: usize,
) -> Result<QM31, V5RelationStressError> {
    decode_qm31(bytes, offset + index * QM31_BYTES)
}

/// Decode the final polynomial without running the relation checks.  The
/// later-FRI checker uses this to consume exactly the coefficients accepted
/// by [`verify_v5_relation_stress`].
pub fn decode_v5_relation_stress_final(
    bytes: &[u8; V5_RELATION_STRESS_BYTES],
) -> Result<[QM31; V5_RELATION_STRESS_FINAL_COEFFICIENTS], V5RelationStressError> {
    let mut final_coefficients = [QM31::ZERO; V5_RELATION_STRESS_FINAL_COEFFICIENTS];
    for (index, output) in final_coefficients.iter_mut().enumerate() {
        *output = decode_indexed(bytes, V5_RELATION_STRESS_FINAL_OFFSET, index)?;
    }
    Ok(final_coefficients)
}

/// Execute the exact production relation work over caller-supplied initial
/// weights and claim.  The four alphas are transcript outputs supplied by the
/// composite; they are not proof-carried by this payload.
pub fn verify_v5_relation_stress(
    weights: WeightAccumulator,
    running_claim: QM31,
    alphas: [QM31; V5_RELATION_STRESS_ROUNDS],
    bytes: &[u8; V5_RELATION_STRESS_BYTES],
) -> Result<VerifiedV5RelationStress, V5RelationStressError> {
    verify_v5_relation_stress_with_additive(
        weights,
        running_claim,
        alphas,
        bytes,
        NoAdditiveWeights,
    )
}

/// Execute the same relation while carrying one compact additive covector
/// through the identical folds and terminal dot.  This is the exact v5
/// composition: the main point/copy weights and Component B share one set of
/// OOD additions, sumcheck checks, folds, and final coefficients.
pub fn verify_v5_relation_stress_with_additive<A: V5RelationStressAdditive>(
    mut weights: WeightAccumulator,
    mut running_claim: QM31,
    alphas: [QM31; V5_RELATION_STRESS_ROUNDS],
    bytes: &[u8; V5_RELATION_STRESS_BYTES],
    mut additive: A,
) -> Result<VerifiedV5RelationStress, V5RelationStressError> {
    let mut circle_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; V5_RELATION_STRESS_OOD_SAMPLES];
    for (sample, point) in circle_points.iter_mut().enumerate() {
        point.x = decode_indexed(bytes, V5_RELATION_STRESS_CIRCLE_OFFSET, 2 * sample)?;
        point.y = decode_indexed(bytes, V5_RELATION_STRESS_CIRCLE_OFFSET, 2 * sample + 1)?;
        if point.x.square().add(point.y.square()) != QM31::ONE {
            return Err(V5RelationStressError::InvalidCirclePoint { sample });
        }
    }
    for (round, alpha) in alphas.into_iter().enumerate() {
        for sample in 0..V5_RELATION_STRESS_OOD_SAMPLES {
            let observation = round * V5_RELATION_STRESS_OOD_SAMPLES + sample;
            let value = decode_indexed(bytes, V5_RELATION_STRESS_OOD_OFFSET, observation)?;
            let mix = decode_indexed(bytes, V5_RELATION_STRESS_MIX_OFFSET, observation)?;
            if round == 0 {
                weights.add_circle_tensor(mix, circle_points[sample])?;
            } else {
                let line_index = (round - 1) * V5_RELATION_STRESS_OOD_SAMPLES + sample;
                let point = decode_indexed(bytes, V5_RELATION_STRESS_LINE_OFFSET, line_index)?;
                weights.add_line_tensor(mix, point)?;
            }
            running_claim = running_claim.add(mix.mul(value));
        }
        let mut polynomial: SumcheckPolynomial = [QM31::ZERO; SUMCHECK_COEFFICIENTS];
        for (coefficient, output) in polynomial.iter_mut().enumerate() {
            *output = decode_indexed(
                bytes,
                V5_RELATION_STRESS_SUMCHECK_OFFSET,
                round * SUMCHECK_COEFFICIENTS + coefficient,
            )?;
        }
        if boundary_sum(&polynomial) != running_claim {
            return Err(V5RelationStressError::BoundaryMismatch { round });
        }
        running_claim = evaluate(&polynomial, alpha);
        weights.fold(alpha);
        additive.fold(alpha);
    }

    let final_coefficients = decode_v5_relation_stress_final(bytes)?;
    if weights
        .dot(&final_coefficients)
        .add(additive.dot(&final_coefficients))
        != running_claim
    {
        return Err(V5RelationStressError::TerminalMismatch);
    }
    Ok(VerifiedV5RelationStress {
        final_coefficients,
        terminal_claim: running_claim,
    })
}

#[cfg(not(target_os = "solana"))]
pub fn build_v5_relation_stress_tail_for_initial_claim(
    initial_claim: QM31,
    alphas: [QM31; V5_RELATION_STRESS_ROUNDS],
) -> [u8; V5_RELATION_STRESS_BYTES] {
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

    let mut output = [0u8; V5_RELATION_STRESS_BYTES];
    for sample in 0..V5_RELATION_STRESS_OOD_SAMPLES {
        let point = secure_ood_circle_point_from_parameter(q(17 + 8 * sample as u32))
            .expect("fixed v5 stress circle parameter is nonsingular and out of domain");
        write(
            &mut output,
            V5_RELATION_STRESS_CIRCLE_OFFSET + (2 * sample) * QM31_BYTES,
            point.x,
        );
        write(
            &mut output,
            V5_RELATION_STRESS_CIRCLE_OFFSET + (2 * sample + 1) * QM31_BYTES,
            point.y,
        );
    }
    for index in 0..LINE_POINTS {
        write(
            &mut output,
            V5_RELATION_STRESS_LINE_OFFSET + index * QM31_BYTES,
            q(101 + 8 * index as u32),
        );
    }
    for index in 0..OOD_MIXES {
        write(
            &mut output,
            V5_RELATION_STRESS_MIX_OFFSET + index * QM31_BYTES,
            q(211 + 8 * index as u32),
        );
    }

    // The relation boundary is the arity-four identity
    // `4 * (c0 + c4) = initial_claim`.  Map that claim to zero at alpha0 so
    // the remaining three messages and final4 can stay canonical zero.  The
    // alpha-zero branch uses c4 because X^4 vanishes at zero; otherwise c1
    // cancels c0 at alpha0 without changing the boundary.
    let boundary_quarter = initial_claim.half().half();
    if alphas[0].is_zero() {
        write(
            &mut output,
            V5_RELATION_STRESS_SUMCHECK_OFFSET + 4 * QM31_BYTES,
            boundary_quarter,
        );
    } else {
        write(
            &mut output,
            V5_RELATION_STRESS_SUMCHECK_OFFSET,
            boundary_quarter,
        );
        let cancellation = QM31::ZERO.sub(
            boundary_quarter.mul(
                alphas[0]
                    .try_inv()
                    .expect("nonzero QM31 alpha has an inverse"),
            ),
        );
        write(
            &mut output,
            V5_RELATION_STRESS_SUMCHECK_OFFSET + QM31_BYTES,
            cancellation,
        );
    }
    // OOD values, the later three sumcheck messages, and final4 remain zero.
    output
}

#[cfg(not(target_os = "solana"))]
pub fn build_zero_v5_relation_stress_tail() -> [u8; V5_RELATION_STRESS_BYTES] {
    build_v5_relation_stress_tail_for_initial_claim(
        QM31::ZERO,
        [QM31::ONE; V5_RELATION_STRESS_ROUNDS],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31};

    fn q(value: u32) -> QM31 {
        QM31::from_cm31(CM31::from_m31(M31(value)))
    }

    #[test]
    fn zero_stress_tail_roundtrips_and_boundary_corruption_rejects() {
        let alphas = [q(3), q(5), q(7), q(11)];
        let mut tail = build_zero_v5_relation_stress_tail();
        let verified =
            verify_v5_relation_stress(WeightAccumulator::empty(10), QM31::ZERO, alphas, &tail)
                .unwrap();
        assert_eq!(verified.final_coefficients, [QM31::ZERO; 4]);
        assert_eq!(verified.terminal_claim, QM31::ZERO);

        q(1).write_le_bytes(
            &mut tail[V5_RELATION_STRESS_SUMCHECK_OFFSET
                ..V5_RELATION_STRESS_SUMCHECK_OFFSET + QM31_BYTES],
        );
        assert_eq!(
            verify_v5_relation_stress(WeightAccumulator::empty(10), QM31::ZERO, alphas, &tail,),
            Err(V5RelationStressError::BoundaryMismatch { round: 0 })
        );
    }

    #[test]
    fn arbitrary_initial_claim_is_mapped_to_zero_for_nonzero_and_zero_alpha() {
        let initial = q(29);
        for alphas in [[q(3), q(5), q(7), q(11)], [QM31::ZERO, q(5), q(7), q(11)]] {
            let tail = build_v5_relation_stress_tail_for_initial_claim(initial, alphas);
            let verified =
                verify_v5_relation_stress(WeightAccumulator::empty(10), initial, alphas, &tail)
                    .unwrap();
            assert_eq!(verified.final_coefficients, [QM31::ZERO; 4]);
            assert_eq!(verified.terminal_claim, QM31::ZERO);
        }
    }
}
