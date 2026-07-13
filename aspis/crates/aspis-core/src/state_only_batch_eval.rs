//! Degree-two batch-evaluation sumcheck for the profile-21 switch word.
//!
//! The first committed line layer has 256 natural coefficients.  A disclosed
//! switch word uses only the first 35.  After the authenticated q values are
//! fixed, a fresh `zeta` batches them and an eight-round Boolean sumcheck
//! proves
//!
//! `sum_r zeta^r U(q_r) = sum_j U_j * sum_r zeta^r tensor(q_r, j)`.
//!
//! This retains direct `Enc(U)(q)` binding without evaluating all 35
//! coefficients independently at every query.

use alloc::vec::Vec;

use crate::circle_fri::{line_domain_x_for_circle, CircleFriError};
use crate::field::QM31;
use crate::transcript::{label, ChallengeSampleExhausted, Transcript};

pub const SWITCH_BATCH_EVAL_LOG_COEFFICIENTS: usize = 8;
pub const SWITCH_BATCH_EVAL_COEFFICIENTS: usize = 1usize << SWITCH_BATCH_EVAL_LOG_COEFFICIENTS;
pub const SWITCH_BATCH_EVAL_ACTIVE_COEFFICIENTS: usize = 35;
pub const SWITCH_BATCH_EVAL_ROUNDS: usize = SWITCH_BATCH_EVAL_LOG_COEFFICIENTS;
pub const SWITCH_BATCH_EVAL_ROUND_COEFFICIENTS: usize = 3;
pub const SWITCH_BATCH_EVAL_PROOF_BYTES: usize =
    SWITCH_BATCH_EVAL_ROUNDS * SWITCH_BATCH_EVAL_ROUND_COEFFICIENTS * 16;
pub const SWITCH_BATCH_EVAL_CIRCLE_DOMAIN_LOG: u32 = 19;
pub const SWITCH_BATCH_EVAL_LINE_LAYER: u8 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SwitchBatchEvalError {
    Length,
    NonCanonical,
    Boundary { round: u8 },
    Terminal,
    Challenge,
    LineDomain,
}

impl From<ChallengeSampleExhausted> for SwitchBatchEvalError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::Challenge
    }
}

impl From<CircleFriError> for SwitchBatchEvalError {
    fn from(_: CircleFriError) -> Self {
        Self::LineDomain
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SwitchBatchEvalSchedule {
    pub zeta: QM31,
    pub point: [QM31; SWITCH_BATCH_EVAL_ROUNDS],
}

#[inline(always)]
fn double_x(x: QM31) -> QM31 {
    let square = x.square();
    square.add(square).sub(QM31::ONE)
}

/// Natural line-tensor factors in the big-endian coefficient-bit order used
/// by `WeightAccumulator::add_line_tensor`.
pub fn switch_line_tensor_factors(query: u32) -> Result<[QM31; 8], SwitchBatchEvalError> {
    let mut x = QM31::from_cm31(crate::field::CM31::from_m31(line_domain_x_for_circle(
        SWITCH_BATCH_EVAL_CIRCLE_DOMAIN_LOG,
        SWITCH_BATCH_EVAL_LINE_LAYER,
        query as usize,
    )?));
    let mut ascending = [QM31::ZERO; 8];
    for (coordinate, factor) in ascending.iter_mut().enumerate() {
        *factor = x;
        if coordinate + 1 < 8 {
            x = double_x(x);
        }
    }
    Ok(core::array::from_fn(|coordinate| ascending[7 - coordinate]))
}

/// Multilinear extension, in the coefficient-index variable, of one exact
/// line-encoding row selected by `query`.
pub fn switch_line_tensor_mle(query: u32, point: &[QM31; 8]) -> Result<QM31, SwitchBatchEvalError> {
    Ok(switch_line_tensor_factors(query)?
        .into_iter()
        .zip(point)
        .fold(QM31::ONE, |product, (factor, z)| {
            product.mul(QM31::ONE.add(z.mul(factor.sub(QM31::ONE))))
        }))
}

/// MLE of the 256-entry natural coefficient table, with entries 35..255
/// fixed to zero.
pub fn switch_coefficients_mle(
    coefficients: &[QM31; SWITCH_BATCH_EVAL_ACTIVE_COEFFICIENTS],
    point: &[QM31; 8],
) -> QM31 {
    // Fold the sparse natural prefix from the low index bit upward. An odd
    // tail is paired with the implicit zero beyond the prefix. This uses 40
    // QM31 products instead of 35*8 products from explicit eq weights.
    let mut level = coefficients.to_vec();
    for z in point.iter().rev() {
        if level.len() == 1 {
            level[0] = level[0].add(z.mul(QM31::ZERO.sub(level[0])));
            continue;
        }
        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut pairs = level.chunks_exact(2);
        for pair in &mut pairs {
            next.push(pair[0].add(z.mul(pair[1].sub(pair[0]))));
        }
        if let Some(&last) = pairs.remainder().first() {
            next.push(last.add(z.mul(QM31::ZERO.sub(last))));
        }
        level = next;
    }
    level.first().copied().unwrap_or(QM31::ZERO)
}

fn absorb_opened_values(
    transcript: &mut Transcript,
    queries: &[u32],
    opened_values: &[QM31],
) -> Result<(), SwitchBatchEvalError> {
    if queries.len() != opened_values.len() || queries.len() > u16::MAX as usize {
        return Err(SwitchBatchEvalError::Length);
    }
    let mut record = Vec::with_capacity(2 + queries.len() * 20);
    record.extend_from_slice(&(queries.len() as u16).to_le_bytes());
    for (&query, value) in queries.iter().zip(opened_values) {
        record.extend_from_slice(&query.to_le_bytes());
        let start = record.len();
        record.resize(start + 16, 0);
        value.write_le_bytes(&mut record[start..]);
    }
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_QUERY_VALUES, &record);
    Ok(())
}

fn absorb_round(transcript: &mut Transcript, round: usize, polynomial: &[QM31; 3]) {
    let mut record = [0u8; 1 + 3 * 16];
    record[0] = round as u8;
    for (index, coefficient) in polynomial.iter().enumerate() {
        coefficient.write_le_bytes(&mut record[1 + 16 * index..]);
    }
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_BATCH_EVAL_SUMCHECK, &record);
}

fn evaluate_quadratic(polynomial: &[QM31; 3], point: QM31) -> QM31 {
    polynomial[2]
        .mul(point)
        .add(polynomial[1])
        .mul(point)
        .add(polynomial[0])
}

pub fn switch_batch_target(opened_values: &[QM31], zeta: QM31) -> QM31 {
    let mut power = QM31::ONE;
    opened_values
        .iter()
        .copied()
        .fold(QM31::ZERO, |sum, value| {
            let next = sum.add(power.mul(value));
            power = power.mul(zeta);
            next
        })
}

/// Verify the exact eight-round quadratic wire. `proof` must contain exactly
/// 384 bytes. The authenticated q values are absorbed before `zeta` is drawn.
pub fn verify_switch_batch_evaluation(
    transcript: &mut Transcript,
    coefficients: &[QM31; SWITCH_BATCH_EVAL_ACTIVE_COEFFICIENTS],
    queries: &[u32],
    opened_values: &[QM31],
    proof: &[u8],
) -> Result<SwitchBatchEvalSchedule, SwitchBatchEvalError> {
    if proof.len() != SWITCH_BATCH_EVAL_PROOF_BYTES {
        return Err(SwitchBatchEvalError::Length);
    }
    absorb_opened_values(transcript, queries, opened_values)?;
    let zeta = transcript.challenge_qm31()?;
    let mut running = switch_batch_target(opened_values, zeta);
    let mut point = [QM31::ZERO; 8];
    for round in 0..SWITCH_BATCH_EVAL_ROUNDS {
        let start = round * 48;
        let polynomial = core::array::from_fn(|coefficient| {
            QM31::from_le_bytes(&proof[start + 16 * coefficient..start + 16 * (coefficient + 1)])
        });
        let [Some(c0), Some(c1), Some(c2)] = polynomial else {
            return Err(SwitchBatchEvalError::NonCanonical);
        };
        let polynomial = [c0, c1, c2];
        if polynomial[0].add(polynomial[0].add(polynomial[1]).add(polynomial[2])) != running {
            return Err(SwitchBatchEvalError::Boundary { round: round as u8 });
        }
        absorb_round(transcript, round, &polynomial);
        point[round] = transcript.challenge_qm31()?;
        running = evaluate_quadratic(&polynomial, point[round]);
    }

    let mut power = QM31::ONE;
    let mut g_at_point = QM31::ZERO;
    for &query in queries {
        g_at_point = g_at_point.add(power.mul(switch_line_tensor_mle(query, &point)?));
        power = power.mul(zeta);
    }
    if running != switch_coefficients_mle(coefficients, &point).mul(g_at_point) {
        return Err(SwitchBatchEvalError::Terminal);
    }
    Ok(SwitchBatchEvalSchedule { zeta, point })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, M31, P};

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed % P), M31(seed.wrapping_mul(17) % P)),
            c1: CM31::new(
                M31(seed.wrapping_mul(31) % P),
                M31(seed.wrapping_mul(47) % P),
            ),
        }
    }

    #[test]
    fn coefficient_mle_is_exact_on_boolean_points() {
        let coefficients = core::array::from_fn(|index| q(index as u32 + 1));
        for index in 0..256usize {
            let point = core::array::from_fn(|coordinate| {
                if (index >> (7 - coordinate)) & 1 == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            });
            assert_eq!(
                switch_coefficients_mle(&coefficients, &point),
                if index < coefficients.len() {
                    coefficients[index]
                } else {
                    QM31::ZERO
                }
            );
        }
    }
}
