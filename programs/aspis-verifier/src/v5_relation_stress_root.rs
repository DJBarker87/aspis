//! Isolated production-order PCS-relation stress kernel for the v5 CU probe.
//!
//! The byte payload is deliberately self-contained. It carries the two
//! circle OOD points, six later-line OOD points, eight values and mixing
//! scalars, four degree-six sumcheck messages, and the final four natural
//! coefficients. The verifier executes the same accumulator operations and
//! checks in the same order as the production state-only relation verifier.

use aspis_core::circle::SecureCirclePoint;
use aspis_core::field::QM31;
use aspis_core::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
    SUMCHECK_COEFFICIENTS,
};

pub const V5_RELATION_STRESS_ROUNDS: usize = 4;
pub const V5_RELATION_STRESS_SAMPLES: usize = 2;
pub const V5_RELATION_STRESS_POINT_VALUES: usize = 10;
pub const V5_RELATION_STRESS_OOD_VALUES: usize =
    V5_RELATION_STRESS_ROUNDS * V5_RELATION_STRESS_SAMPLES;
pub const V5_RELATION_STRESS_MIXES: usize = V5_RELATION_STRESS_OOD_VALUES;
pub const V5_RELATION_STRESS_FINAL_VALUES: usize = 4;
pub const V5_RELATION_STRESS_QM31_VALUES: usize = V5_RELATION_STRESS_POINT_VALUES
    + V5_RELATION_STRESS_OOD_VALUES
    + V5_RELATION_STRESS_MIXES
    + V5_RELATION_STRESS_ROUNDS * SUMCHECK_COEFFICIENTS
    + V5_RELATION_STRESS_FINAL_VALUES;
pub const V5_RELATION_STRESS_BYTES: usize = V5_RELATION_STRESS_QM31_VALUES * 16;

const POINT_OFFSET: usize = 0;
const OOD_VALUE_OFFSET: usize = POINT_OFFSET + V5_RELATION_STRESS_POINT_VALUES;
const MIX_OFFSET: usize = OOD_VALUE_OFFSET + V5_RELATION_STRESS_OOD_VALUES;
const SUMCHECK_OFFSET: usize = MIX_OFFSET + V5_RELATION_STRESS_MIXES;
const FINAL_OFFSET: usize =
    SUMCHECK_OFFSET + V5_RELATION_STRESS_ROUNDS * SUMCHECK_COEFFICIENTS;

const _: () = assert!(V5_RELATION_STRESS_QM31_VALUES == 58);
const _: () = assert!(V5_RELATION_STRESS_BYTES == 928);
const _: () = assert!(FINAL_OFFSET == 54);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5RelationStressError {
    WrongLength,
    NonCanonical { value: usize },
    Weight(TensorWeightError),
    BoundaryMismatch { round: usize },
    TerminalMismatch,
}

impl From<TensorWeightError> for V5RelationStressError {
    fn from(error: TensorWeightError) -> Self {
        Self::Weight(error)
    }
}

#[inline(always)]
fn decode(payload: &[u8], value: usize) -> Result<QM31, V5RelationStressError> {
    let start = value * 16;
    QM31::from_le_bytes(&payload[start..start + 16])
        .ok_or(V5RelationStressError::NonCanonical { value })
}

/// Execute the exact production-order four-round OOD/sumcheck/final relation
/// checks. The initial claim is zero for this CU stress instance; the payload
/// builder below produces a valid algebraically-zero proof while retaining
/// nonzero mixing scalars and therefore all accumulator work.
pub fn verify_v5_relation_stress(
    payload: &[u8],
    alphas: [QM31; V5_RELATION_STRESS_ROUNDS],
) -> Result<QM31, V5RelationStressError> {
    if payload.len() != V5_RELATION_STRESS_BYTES {
        return Err(V5RelationStressError::WrongLength);
    }

    // Decode the whole fixed grammar before doing relation work. This keeps
    // malformed encodings from changing which verifier operations execute.
    let mut values = [QM31::ZERO; V5_RELATION_STRESS_QM31_VALUES];
    for (index, value) in values.iter_mut().enumerate() {
        *value = decode(payload, index)?;
    }

    let mut weights = WeightAccumulator::empty(10);
    let mut running_claim = QM31::ZERO;
    for round in 0..V5_RELATION_STRESS_ROUNDS {
        for sample in 0..V5_RELATION_STRESS_SAMPLES {
            let sample_index = round * V5_RELATION_STRESS_SAMPLES + sample;
            let mix = values[MIX_OFFSET + sample_index];
            if round == 0 {
                let point_index = POINT_OFFSET + 2 * sample;
                weights.add_circle_tensor(
                    mix,
                    SecureCirclePoint {
                        x: values[point_index],
                        y: values[point_index + 1],
                    },
                )?;
            } else {
                let point_index =
                    POINT_OFFSET + 4 + (round - 1) * V5_RELATION_STRESS_SAMPLES + sample;
                weights.add_line_tensor(mix, values[point_index])?;
            }
            running_claim = running_claim.add(mix.mul(values[OOD_VALUE_OFFSET + sample_index]));
        }

        let polynomial: SumcheckPolynomial = core::array::from_fn(|coefficient| {
            values[SUMCHECK_OFFSET + round * SUMCHECK_COEFFICIENTS + coefficient]
        });
        if boundary_sum(&polynomial) != running_claim {
            return Err(V5RelationStressError::BoundaryMismatch { round });
        }
        running_claim = evaluate(&polynomial, alphas[round]);
        weights.fold(alphas[round]);
    }

    let final_values: [QM31; V5_RELATION_STRESS_FINAL_VALUES] =
        core::array::from_fn(|index| values[FINAL_OFFSET + index]);
    let terminal = weights.dot(&final_values);
    if terminal != running_claim {
        return Err(V5RelationStressError::TerminalMismatch);
    }
    Ok(terminal)
}

/// Deterministic valid payload for host tooling and unit tests. Circle points
/// are `(1, 0)`, later line points and all OOD mixing scalars are one, while
/// OOD values, sumcheck messages, and final coefficients are zero. Thus every
/// production operation runs and every checked relation is exactly zero.
pub fn build_zero_v5_relation_stress_payload() -> [u8; V5_RELATION_STRESS_BYTES] {
    let mut payload = [0u8; V5_RELATION_STRESS_BYTES];
    let mut write = |index: usize, value: QM31| {
        value.write_le_bytes(&mut payload[index * 16..index * 16 + 16]);
    };
    write(POINT_OFFSET, QM31::ONE);
    write(POINT_OFFSET + 2, QM31::ONE);
    for point in 4..V5_RELATION_STRESS_POINT_VALUES {
        write(POINT_OFFSET + point, QM31::ONE);
    }
    for mix in 0..V5_RELATION_STRESS_MIXES {
        write(MIX_OFFSET + mix, QM31::ONE);
    }
    payload
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_instance_executes_complete_relation() {
        let payload = build_zero_v5_relation_stress_payload();
        assert_eq!(payload.len(), 928);
        assert_eq!(
            verify_v5_relation_stress(&payload, [QM31::ONE; 4]),
            Ok(QM31::ZERO)
        );
    }

    #[test]
    fn changed_sumcheck_is_rejected() {
        let mut payload = build_zero_v5_relation_stress_payload();
        QM31::ONE.write_le_bytes(
            &mut payload[SUMCHECK_OFFSET * 16..SUMCHECK_OFFSET * 16 + 16],
        );
        assert_eq!(
            verify_v5_relation_stress(&payload, [QM31::ONE; 4]),
            Err(V5RelationStressError::BoundaryMismatch { round: 0 })
        );
    }
}
