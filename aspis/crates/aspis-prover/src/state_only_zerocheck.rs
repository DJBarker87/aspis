//! Host prover scaffold for the ten-round degree-27 state-only zerocheck.
//!
//! This module is deliberately not wired into any payment profile.  It emits
//! the isolated 4,480-byte state-only sumcheck field consumed by
//! `aspis_core::state_only_sumcheck` and uses its distinct transcript label.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_sumcheck::{
    absorb_state_only_sumcheck_round, encode_state_only_polynomial, evaluate_state_only_polynomial,
    state_only_boundary_sum, StateOnlySumcheckPolynomial, STATE_ONLY_SUMCHECK_BYTES,
    STATE_ONLY_SUMCHECK_COEFFICIENTS, STATE_ONLY_SUMCHECK_DEGREE, STATE_ONLY_SUMCHECK_ROUNDS,
    STATE_ONLY_SUMCHECK_ROUND_BYTES,
};
use aspis_core::transcript::{ChallengeSampleExhausted, Transcript};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyZerocheckTrace {
    pub proof: [u8; STATE_ONLY_SUMCHECK_BYTES],
    pub challenges: [QM31; STATE_ONLY_SUMCHECK_ROUNDS],
    pub terminal_claim: QM31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateOnlyZerocheckProveError<E> {
    Oracle(E),
    BoundaryMismatch { round: usize },
    TerminalMismatch,
    ChallengeSampleExhausted,
}

impl<E> From<ChallengeSampleExhausted> for StateOnlyZerocheckProveError<E> {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

/// Interpolate the unique degree-at-most-27 polynomial through values at the
/// base-field points `0..=27`.  This is host prover work, so the candidate
/// verifier's CU ledger contains none of it.
fn interpolate_state_only(
    values: &[QM31; STATE_ONLY_SUMCHECK_COEFFICIENTS],
) -> StateOnlySumcheckPolynomial {
    let mut output = [QM31::ZERO; STATE_ONLY_SUMCHECK_COEFFICIENTS];
    for i in 0..=STATE_ONLY_SUMCHECK_DEGREE {
        let mut basis = [QM31::ZERO; STATE_ONLY_SUMCHECK_COEFFICIENTS];
        basis[0] = QM31::ONE;
        let mut basis_degree = 0usize;
        let mut denominator = M31::ONE;
        for j in 0..=STATE_ONLY_SUMCHECK_DEGREE {
            if i == j {
                continue;
            }
            let root = M31(j as u32);
            let previous = basis;
            for coefficient in 0..=basis_degree + 1 {
                let shifted = if coefficient == 0 {
                    QM31::ZERO
                } else {
                    previous[coefficient - 1]
                };
                let constant = if coefficient <= basis_degree {
                    previous[coefficient].mul_m31(root)
                } else {
                    QM31::ZERO
                };
                basis[coefficient] = shifted.sub(constant);
            }
            basis_degree += 1;
            denominator = denominator.mul(M31(i as u32).sub(root));
        }
        let scale = values[i].mul_m31(denominator.inv());
        for coefficient in 0..=STATE_ONLY_SUMCHECK_DEGREE {
            output[coefficient] = output[coefficient].add(scale.mul(basis[coefficient]));
        }
    }
    output
}

/// Prove a degree-at-most-27-in-each-variable oracle from a supplied Boolean
/// hypercube sum.  The caller is responsible for binding the initial claim
/// before invoking this production-neutral scaffold.
pub fn prove_state_only_sumcheck_from_claim<F, E>(
    transcript: &mut Transcript,
    mut oracle: F,
    initial_claim: QM31,
) -> Result<StateOnlyZerocheckTrace, StateOnlyZerocheckProveError<E>>
where
    F: FnMut(&[QM31; STATE_ONLY_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    let mut proof = [0u8; STATE_ONLY_SUMCHECK_BYTES];
    let mut challenges = [QM31::ZERO; STATE_ONLY_SUMCHECK_ROUNDS];
    let mut running_claim = initial_claim;
    let mut prefix = [QM31::ZERO; STATE_ONLY_SUMCHECK_ROUNDS];

    for round in 0..STATE_ONLY_SUMCHECK_ROUNDS {
        let mut samples = [QM31::ZERO; STATE_ONLY_SUMCHECK_COEFFICIENTS];
        let remaining = STATE_ONLY_SUMCHECK_ROUNDS - round - 1;
        for (sample_index, sample) in samples.iter_mut().enumerate() {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample_index as u32)));
            let mut total = QM31::ZERO;
            for assignment in 0..(1usize << remaining) {
                for offset in 0..remaining {
                    let bit = (assignment >> (remaining - 1 - offset)) & 1;
                    prefix[round + 1 + offset] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
                }
                total = total.add(oracle(&prefix).map_err(StateOnlyZerocheckProveError::Oracle)?);
            }
            *sample = total;
        }

        let polynomial = interpolate_state_only(&samples);
        if state_only_boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlyZerocheckProveError::BoundaryMismatch { round });
        }
        let encoded = encode_state_only_polynomial(&polynomial);
        let start = round * STATE_ONLY_SUMCHECK_ROUND_BYTES;
        proof[start..start + STATE_ONLY_SUMCHECK_ROUND_BYTES].copy_from_slice(&encoded);
        let challenge = absorb_state_only_sumcheck_round(transcript, round, &encoded)?;
        prefix[round] = challenge;
        challenges[round] = challenge;
        running_claim = evaluate_state_only_polynomial(&polynomial, challenge);
    }

    if oracle(&challenges).map_err(StateOnlyZerocheckProveError::Oracle)? != running_claim {
        return Err(StateOnlyZerocheckProveError::TerminalMismatch);
    }
    Ok(StateOnlyZerocheckTrace {
        proof,
        challenges,
        terminal_claim: running_claim,
    })
}

/// Ordinary zerocheck wrapper: the claimed Boolean-cube sum is zero.
pub fn prove_state_only_zerocheck<F, E>(
    transcript: &mut Transcript,
    oracle: F,
) -> Result<StateOnlyZerocheckTrace, StateOnlyZerocheckProveError<E>>
where
    F: FnMut(&[QM31; STATE_ONLY_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    prove_state_only_sumcheck_from_claim(transcript, oracle, QM31::ZERO)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HOST_HASH;
    use aspis_core::state_only_sumcheck::{
        verify_state_only_sumcheck_streaming, STATE_ONLY_VERIFY_M31_MULS,
        STATE_ONLY_VERIFY_QM31_ADDS, STATE_ONLY_VERIFY_QM31_MULS,
    };
    use aspis_core::transcript::label;

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn pow(mut base: QM31, mut exponent: usize) -> QM31 {
        let mut result = QM31::ONE;
        while exponent != 0 {
            if exponent & 1 == 1 {
                result = result.mul(base);
            }
            base = base.square();
            exponent >>= 1;
        }
        result
    }

    fn degree_27_oracle(seed: u32, point: &[QM31; STATE_ONLY_SUMCHECK_ROUNDS]) -> QM31 {
        point
            .iter()
            .enumerate()
            .fold(q(seed + 1), |value, (coordinate, x)| {
                let high =
                    pow(*x, STATE_ONLY_SUMCHECK_DEGREE).mul(q(seed + 101 + coordinate as u32));
                value.mul(
                    q(seed + 211 + coordinate as u32)
                        .add(x.mul(q(seed + 307 + coordinate as u32)))
                        .add(high),
                )
            })
    }

    fn boolean_sum(seed: u32) -> QM31 {
        (0..1usize << STATE_ONLY_SUMCHECK_ROUNDS).fold(QM31::ZERO, |sum, assignment| {
            let point = core::array::from_fn(|coordinate| {
                if (assignment >> (STATE_ONLY_SUMCHECK_ROUNDS - 1 - coordinate)) & 1 == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            });
            sum.add(degree_27_oracle(seed, &point))
        })
    }

    #[test]
    fn degree_27_prover_matches_streaming_verifier_and_terminal_oracle() {
        for seed in [7u32, 29, 83] {
            let initial_claim = boolean_sum(seed);
            let mut prover_transcript = Transcript::new(HOST_HASH);
            prover_transcript.absorb(label::STATEMENT, &seed.to_le_bytes());
            let proof = prove_state_only_sumcheck_from_claim(
                &mut prover_transcript,
                |point| Ok::<_, ()>(degree_27_oracle(seed, point)),
                initial_claim,
            )
            .unwrap();

            assert_eq!(proof.proof.len(), 4_480);
            assert_eq!(
                proof.terminal_claim,
                degree_27_oracle(seed, &proof.challenges)
            );
            let mut verifier_transcript = Transcript::new(HOST_HASH);
            verifier_transcript.absorb(label::STATEMENT, &seed.to_le_bytes());
            let verified = verify_state_only_sumcheck_streaming(
                &mut verifier_transcript,
                &proof.proof,
                initial_claim,
            )
            .unwrap();
            assert_eq!(verified.point, proof.challenges);
            assert_eq!(verified.terminal_claim, proof.terminal_claim);
            assert_eq!(
                verifier_transcript.diagnostic_state(),
                prover_transcript.diagnostic_state()
            );
        }
    }

    #[test]
    fn wrong_initial_claim_is_rejected_by_the_prover_boundary() {
        let seed = 41u32;
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::STATEMENT, &seed.to_le_bytes());
        assert_eq!(
            prove_state_only_sumcheck_from_claim(
                &mut transcript,
                |point| Ok::<_, ()>(degree_27_oracle(seed, point)),
                boolean_sum(seed).add(QM31::ONE),
            ),
            Err(StateOnlyZerocheckProveError::BoundaryMismatch { round: 0 })
        );
    }

    #[test]
    fn production_neutral_inventory_matches_core() {
        assert_eq!(STATE_ONLY_SUMCHECK_BYTES, 4_480);
        assert_eq!(STATE_ONLY_VERIFY_QM31_MULS, 270);
        assert_eq!(STATE_ONLY_VERIFY_QM31_ADDS, 550);
        assert_eq!(STATE_ONLY_VERIFY_M31_MULS, 2_430);
    }
}
