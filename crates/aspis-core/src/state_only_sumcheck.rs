//! Production-neutral degree-27 state-only zerocheck wire.
//!
//! Each of ten rounds transmits the complete polynomial `c0..c27`.  Unlike
//! the deployed degree-10 payment wire, this candidate does not elide `c1`:
//! the verifier checks the literal sumcheck boundary `p(0) + p(1)` before it
//! absorbs the round and samples its challenge.  The byte verifier decodes
//! only one 28-element round at a time.

use crate::field::{qm31_sum_products3, PreparedQm31Multiplier, QM31};
use crate::statement_sumcheck::PaymentConstraintChallenges;
use crate::transcript::{label, ChallengeSampleExhausted, Transcript};

pub const STATE_ONLY_SUMCHECK_ROUNDS: usize = 10;
pub const STATE_ONLY_SUMCHECK_DEGREE: usize = 27;
pub const STATE_ONLY_SUMCHECK_COEFFICIENTS: usize = STATE_ONLY_SUMCHECK_DEGREE + 1;
pub const STATE_ONLY_SUMCHECK_ROUND_BYTES: usize = STATE_ONLY_SUMCHECK_COEFFICIENTS * 16;
pub const STATE_ONLY_SUMCHECK_BYTES: usize =
    STATE_ONLY_SUMCHECK_ROUNDS * STATE_ONLY_SUMCHECK_ROUND_BYTES;
pub const STATE_ONLY_SUMCHECK_ABSORB_BYTES: usize = 1 + STATE_ONLY_SUMCHECK_ROUND_BYTES;
pub const STATE_ONLY_CONSTRAINT_REGISTRY_VERSION: u8 = 1;
pub const STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES: u8 = 29;
pub const STATE_ONLY_SEMANTIC_SOURCE_LANES: u16 = 95;
pub const STATE_ONLY_COPY_LINKS: u16 = 102;
pub const STATE_ONLY_COPY_TUPLE_WIDTH: u8 = 17;
pub const STATE_ONLY_LAYOUT_FINGERPRINT: u64 = 0x121d_b4ec_14af_2130;
pub const STATE_ONLY_HIDING_FACTOR_FINGERPRINT: u64 = 0x1267_2251_efe5_eafb;
pub const STATE_ONLY_CONSTRAINT_REGISTRY_BYTES: usize = 28;

/// Exact verifier arithmetic, excluding canonical decoding and transcript
/// hashing. Seven radix-four blocks use 21 fused coefficient products and
/// six `x^4` Horner products. Constructing `(x^2,x^3,x^4)` costs two
/// specialized squares and one generic product. The literal `p(0)+p(1)`
/// boundary costs another 28 adds.
pub const STATE_ONLY_VERIFY_QM31_MULS_PER_ROUND: usize = 30;
pub const STATE_ONLY_VERIFY_QM31_ADDS_PER_ROUND: usize = 41;
pub const STATE_ONLY_VERIFY_QM31_MULS: usize =
    STATE_ONLY_SUMCHECK_ROUNDS * STATE_ONLY_VERIFY_QM31_MULS_PER_ROUND;
pub const STATE_ONLY_VERIFY_QM31_ADDS: usize =
    STATE_ONLY_SUMCHECK_ROUNDS * STATE_ONLY_VERIFY_QM31_ADDS_PER_ROUND;
/// Per round the 21 fused products, six `x^4` Horner products, and one `x^3`
/// product cost 252 M31 products; the two specialized squares add fourteen.
pub const STATE_ONLY_VERIFY_M31_MULS_PER_ROUND: usize = 266;
pub const STATE_ONLY_VERIFY_M31_MULS: usize =
    STATE_ONLY_SUMCHECK_ROUNDS * STATE_ONLY_VERIFY_M31_MULS_PER_ROUND;

pub type StateOnlySumcheckPolynomial = [QM31; STATE_ONLY_SUMCHECK_COEFFICIENTS];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlySumcheckVerification {
    pub point: [QM31; STATE_ONLY_SUMCHECK_ROUNDS],
    pub terminal_claim: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlySumcheckVerifyError {
    BadLength,
    NonCanonicalValue { round: usize, coefficient: usize },
    BoundaryMismatch { round: usize },
    TerminalMismatch,
    ChallengeSampleExhausted,
}

impl From<ChallengeSampleExhausted> for StateOnlySumcheckVerifyError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

/// Bind the exact state-only algebra registry and sample theta for the 29
/// randomized lanes, a ten-coordinate zerocheck equality point, and mu for
/// the single zero-sum copy helper.
pub fn begin_state_only_zerocheck(
    transcript: &mut Transcript,
) -> Result<PaymentConstraintChallenges, ChallengeSampleExhausted> {
    let mut registry = [0u8; STATE_ONLY_CONSTRAINT_REGISTRY_BYTES];
    registry[0] = STATE_ONLY_CONSTRAINT_REGISTRY_VERSION;
    registry[1] = STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES;
    registry[2..4].copy_from_slice(&STATE_ONLY_SEMANTIC_SOURCE_LANES.to_le_bytes());
    registry[4] = STATE_ONLY_SUMCHECK_ROUNDS as u8;
    registry[5] = STATE_ONLY_SUMCHECK_DEGREE as u8;
    registry[6] = STATE_ONLY_SUMCHECK_COEFFICIENTS as u8;
    registry[7..9].copy_from_slice(&STATE_ONLY_COPY_LINKS.to_le_bytes());
    registry[9] = STATE_ONLY_COPY_TUPLE_WIDTH;
    registry[10..18].copy_from_slice(&STATE_ONLY_LAYOUT_FINGERPRINT.to_le_bytes());
    registry[18..26].copy_from_slice(&STATE_ONLY_HIDING_FACTOR_FINGERPRINT.to_le_bytes());
    transcript.absorb(label::M31_STATE_ONLY_CONSTRAINT_REGISTRY, &registry);
    transcript.absorb(label::M31_STATE_ONLY_HELPER_SUM, &[0u8; 16]);
    let theta = transcript.challenge_qm31()?;
    let mut zerocheck_point = [QM31::ZERO; STATE_ONLY_SUMCHECK_ROUNDS];
    for coordinate in &mut zerocheck_point {
        *coordinate = transcript.challenge_qm31()?;
    }
    let mu = transcript.challenge_qm31()?;
    Ok(PaymentConstraintChallenges {
        theta,
        zerocheck_point,
        mu,
    })
}

/// Literal `p(0) + p(1)` for a complete degree-27 round polynomial.
pub fn state_only_boundary_sum(polynomial: &StateOnlySumcheckPolynomial) -> QM31 {
    let at_one = polynomial.iter().copied().fold(QM31::ZERO, QM31::add);
    polynomial[0].add(at_one)
}

/// Reference degree-27 Horner evaluation using exactly 27 prepared products.
pub fn evaluate_state_only_polynomial_horner(
    polynomial: &StateOnlySumcheckPolynomial,
    challenge: QM31,
) -> QM31 {
    let prepared = PreparedQm31Multiplier::new(challenge);
    polynomial[..STATE_ONLY_SUMCHECK_DEGREE]
        .iter()
        .rev()
        .copied()
        .fold(
            polynomial[STATE_ONLY_SUMCHECK_DEGREE],
            |value, coefficient| prepared.mul(value).add(coefficient),
        )
}

/// Exact degree-27 radix-four evaluation.
///
/// The seven blocks are `c[4j] + x*c[4j+1] + x^2*c[4j+2] +
/// x^3*c[4j+3]`. Their three nonconstant products share one lazy reduction,
/// after which the block values are combined by Horner evaluation at `x^4`.
/// This preserves the polynomial while trading 23 extra M31 products for far
/// fewer extension-field reconstructions and reductions.
#[inline(never)]
pub fn evaluate_state_only_polynomial(
    polynomial: &StateOnlySumcheckPolynomial,
    challenge: QM31,
) -> QM31 {
    let x2 = challenge.square();
    let x3 = challenge.mul(x2);
    let x4 = x2.square();
    let powers = [challenge, x2, x3];
    let prepared_x4 = PreparedQm31Multiplier::new(x4);
    let block_value = |block: usize| {
        let start = 4 * block;
        polynomial[start].add(qm31_sum_products3(
            powers,
            [
                polynomial[start + 1],
                polynomial[start + 2],
                polynomial[start + 3],
            ],
        ))
    };
    (0..6).rev().fold(block_value(6), |accumulator, block| {
        prepared_x4.mul(accumulator).add(block_value(block))
    })
}

pub fn encode_state_only_polynomial(
    polynomial: &StateOnlySumcheckPolynomial,
) -> [u8; STATE_ONLY_SUMCHECK_ROUND_BYTES] {
    let mut encoded = [0u8; STATE_ONLY_SUMCHECK_ROUND_BYTES];
    for (index, coefficient) in polynomial.iter().enumerate() {
        coefficient.write_le_bytes(&mut encoded[index * 16..index * 16 + 16]);
    }
    encoded
}

pub fn decode_state_only_polynomial(
    round: usize,
    encoded: &[u8],
) -> Result<StateOnlySumcheckPolynomial, StateOnlySumcheckVerifyError> {
    if encoded.len() != STATE_ONLY_SUMCHECK_ROUND_BYTES {
        return Err(StateOnlySumcheckVerifyError::BadLength);
    }
    let mut polynomial = [QM31::ZERO; STATE_ONLY_SUMCHECK_COEFFICIENTS];
    for (coefficient, chunk) in encoded.chunks_exact(16).enumerate() {
        polynomial[coefficient] = QM31::from_le_bytes(chunk)
            .ok_or(StateOnlySumcheckVerifyError::NonCanonicalValue { round, coefficient })?;
    }
    Ok(polynomial)
}

/// Absorb one complete round under the state-only label and bind its index.
pub fn absorb_state_only_sumcheck_round(
    transcript: &mut Transcript,
    round: usize,
    encoded: &[u8; STATE_ONLY_SUMCHECK_ROUND_BYTES],
) -> Result<QM31, ChallengeSampleExhausted> {
    let mut framed = [0u8; STATE_ONLY_SUMCHECK_ABSORB_BYTES];
    framed[0] = round as u8;
    framed[1..].copy_from_slice(encoded);
    transcript.absorb(label::M31_STATE_ONLY_ZEROCHECK_SUMCHECK, &framed);
    transcript.challenge_qm31()
}

/// Verify ten complete degree-27 round polynomials directly from bytes.
///
/// Only `polynomial`, the current 448-byte slice, survives inside a round;
/// no `[QM31; 28]` array is retained between iterations.
pub fn verify_state_only_sumcheck_streaming(
    transcript: &mut Transcript,
    proof: &[u8],
    initial_claim: QM31,
) -> Result<StateOnlySumcheckVerification, StateOnlySumcheckVerifyError> {
    if proof.len() != STATE_ONLY_SUMCHECK_BYTES {
        return Err(StateOnlySumcheckVerifyError::BadLength);
    }
    let mut point = [QM31::ZERO; STATE_ONLY_SUMCHECK_ROUNDS];
    let mut running_claim = initial_claim;
    for (round, encoded) in proof
        .chunks_exact(STATE_ONLY_SUMCHECK_ROUND_BYTES)
        .enumerate()
    {
        let polynomial = decode_state_only_polynomial(round, encoded)?;
        if state_only_boundary_sum(&polynomial) != running_claim {
            return Err(StateOnlySumcheckVerifyError::BoundaryMismatch { round });
        }
        let encoded: &[u8; STATE_ONLY_SUMCHECK_ROUND_BYTES] = encoded
            .try_into()
            .expect("exact chunks preserve the state-only round width");
        let challenge = absorb_state_only_sumcheck_round(transcript, round, encoded)?;
        running_claim = evaluate_state_only_polynomial(&polynomial, challenge);
        point[round] = challenge;
    }
    Ok(StateOnlySumcheckVerification {
        point,
        terminal_claim: running_claim,
    })
}

/// Candidate integration guard: the state-only constraint oracle must equal
/// the sumcheck terminal at the derived point.
pub fn verify_state_only_sumcheck_streaming_with_terminal(
    transcript: &mut Transcript,
    proof: &[u8],
    initial_claim: QM31,
    expected_terminal: QM31,
) -> Result<StateOnlySumcheckVerification, StateOnlySumcheckVerifyError> {
    let verified = verify_state_only_sumcheck_streaming(transcript, proof, initial_claim)?;
    if verified.terminal_claim != expected_terminal {
        return Err(StateOnlySumcheckVerifyError::TerminalMismatch);
    }
    Ok(verified)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, M31, P};
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

    fn random_qm31(state: &mut u64) -> QM31 {
        let limbs: [M31; 4] = core::array::from_fn(|_| {
            *state ^= *state << 13;
            *state ^= *state >> 7;
            *state ^= *state << 17;
            M31((*state as u32) % P)
        });
        QM31 {
            c0: CM31::new(limbs[0], limbs[1]),
            c1: CM31::new(limbs[2], limbs[3]),
        }
    }

    fn valid_random_wire(seed: u64) -> ([u8; STATE_ONLY_SUMCHECK_BYTES], QM31) {
        let mut random = seed;
        let initial_claim = random_qm31(&mut random);
        let mut running_claim = initial_claim;
        let mut transcript = Transcript::new(test_hash);
        transcript.absorb(label::STATEMENT, &seed.to_le_bytes());
        let mut proof = [0u8; STATE_ONLY_SUMCHECK_BYTES];
        for round in 0..STATE_ONLY_SUMCHECK_ROUNDS {
            let mut polynomial = core::array::from_fn(|_| random_qm31(&mut random));
            let sum_without_c1 = polynomial[2..]
                .iter()
                .copied()
                .fold(polynomial[0].add(polynomial[0]), QM31::add);
            polynomial[1] = running_claim.sub(sum_without_c1);
            let encoded = encode_state_only_polynomial(&polynomial);
            proof[round * STATE_ONLY_SUMCHECK_ROUND_BYTES
                ..(round + 1) * STATE_ONLY_SUMCHECK_ROUND_BYTES]
                .copy_from_slice(&encoded);
            let challenge =
                absorb_state_only_sumcheck_round(&mut transcript, round, &encoded).unwrap();
            running_claim = evaluate_state_only_polynomial(&polynomial, challenge);
        }
        (proof, initial_claim)
    }

    fn reference_verify(
        transcript: &mut Transcript,
        proof: &[u8; STATE_ONLY_SUMCHECK_BYTES],
        initial_claim: QM31,
    ) -> StateOnlySumcheckVerification {
        let messages: [StateOnlySumcheckPolynomial; STATE_ONLY_SUMCHECK_ROUNDS] =
            core::array::from_fn(|round| {
                let start = round * STATE_ONLY_SUMCHECK_ROUND_BYTES;
                decode_state_only_polynomial(
                    round,
                    &proof[start..start + STATE_ONLY_SUMCHECK_ROUND_BYTES],
                )
                .unwrap()
            });
        let mut running_claim = initial_claim;
        let mut point = [QM31::ZERO; STATE_ONLY_SUMCHECK_ROUNDS];
        for (round, polynomial) in messages.iter().enumerate() {
            assert_eq!(state_only_boundary_sum(polynomial), running_claim);
            let encoded = encode_state_only_polynomial(polynomial);
            let challenge = absorb_state_only_sumcheck_round(transcript, round, &encoded).unwrap();
            let mut power = QM31::ONE;
            running_claim = QM31::ZERO;
            for coefficient in polynomial {
                running_claim = running_claim.add(coefficient.mul(power));
                power = power.mul(challenge);
            }
            point[round] = challenge;
        }
        StateOnlySumcheckVerification {
            point,
            terminal_claim: running_claim,
        }
    }

    #[test]
    fn streaming_matches_materialized_random_reference() {
        for seed in 1..=64u64 {
            let (proof, initial_claim) = valid_random_wire(seed * 0x9e37_79b9);
            let mut streaming = Transcript::new(test_hash);
            streaming.absorb(label::STATEMENT, &(seed * 0x9e37_79b9).to_le_bytes());
            let actual =
                verify_state_only_sumcheck_streaming(&mut streaming, &proof, initial_claim)
                    .unwrap();
            let mut reference = Transcript::new(test_hash);
            reference.absorb(label::STATEMENT, &(seed * 0x9e37_79b9).to_le_bytes());
            let expected = reference_verify(&mut reference, &proof, initial_claim);
            assert_eq!(actual, expected, "seed {seed}");
            assert_eq!(streaming.diagnostic_state(), reference.diagnostic_state());
        }
    }

    #[test]
    fn radix_four_matches_horner_at_random_off_domain_points() {
        let mut random = 0x4b5d_6f70_8192_a3b4;
        for sample in 0..256 {
            let polynomial = core::array::from_fn(|_| random_qm31(&mut random));
            let challenge = random_qm31(&mut random);
            assert_eq!(
                evaluate_state_only_polynomial(&polynomial, challenge),
                evaluate_state_only_polynomial_horner(&polynomial, challenge),
                "sample={sample}",
            );
        }
    }

    #[test]
    fn every_round_coefficient_has_a_boundary_tooth() {
        let (proof, initial_claim) = valid_random_wire(0x4755_4152_4432_37);
        for round in 0..STATE_ONLY_SUMCHECK_ROUNDS {
            for coefficient in 0..STATE_ONLY_SUMCHECK_COEFFICIENTS {
                let mut corrupted = proof;
                let start = round * STATE_ONLY_SUMCHECK_ROUND_BYTES + coefficient * 16;
                let original = QM31::from_le_bytes(&corrupted[start..start + 16]).unwrap();
                original
                    .add(QM31::ONE)
                    .write_le_bytes(&mut corrupted[start..start + 16]);
                let mut transcript = Transcript::new(test_hash);
                transcript.absorb(label::STATEMENT, &0x4755_4152_4432_37u64.to_le_bytes());
                assert_eq!(
                    verify_state_only_sumcheck_streaming(
                        &mut transcript,
                        &corrupted,
                        initial_claim
                    ),
                    Err(StateOnlySumcheckVerifyError::BoundaryMismatch { round }),
                    "round {round} coefficient {coefficient}"
                );
            }
        }
    }

    #[test]
    fn ordering_and_round_index_are_transcript_bound() {
        let seed = 0x1020_3040_5060_7080;
        let (proof, initial_claim) = valid_random_wire(seed);
        let mut baseline_transcript = Transcript::new(test_hash);
        baseline_transcript.absorb(label::STATEMENT, &seed.to_le_bytes());
        let baseline =
            verify_state_only_sumcheck_streaming(&mut baseline_transcript, &proof, initial_claim)
                .unwrap();

        // Swapping c1 and c2 preserves p(0)+p(1), so the terminal oracle
        // check, not the boundary alone, is the required ordering tooth.
        let mut reordered = proof;
        // Use the final round so no later boundary catches the changed
        // challenge before the explicit terminal-oracle tooth is exercised.
        let final_start = (STATE_ONLY_SUMCHECK_ROUNDS - 1) * STATE_ONLY_SUMCHECK_ROUND_BYTES;
        let c1_start = final_start + 16;
        let c2_start = final_start + 32;
        let c1 = reordered[c1_start..c1_start + 16].to_vec();
        let c2 = reordered[c2_start..c2_start + 16].to_vec();
        reordered[c1_start..c1_start + 16].copy_from_slice(&c2);
        reordered[c2_start..c2_start + 16].copy_from_slice(&c1);
        let mut reordered_transcript = Transcript::new(test_hash);
        reordered_transcript.absorb(label::STATEMENT, &seed.to_le_bytes());
        assert_eq!(
            verify_state_only_sumcheck_streaming_with_terminal(
                &mut reordered_transcript,
                &reordered,
                initial_claim,
                baseline.terminal_claim,
            ),
            Err(StateOnlySumcheckVerifyError::TerminalMismatch)
        );
        assert_ne!(
            reordered_transcript.diagnostic_state(),
            baseline_transcript.diagnostic_state()
        );

        let first: &[u8; STATE_ONLY_SUMCHECK_ROUND_BYTES] =
            proof[..STATE_ONLY_SUMCHECK_ROUND_BYTES].try_into().unwrap();
        let mut round0 = Transcript::new(test_hash);
        let mut round1 = Transcript::new(test_hash);
        let _ = absorb_state_only_sumcheck_round(&mut round0, 0, first).unwrap();
        let _ = absorb_state_only_sumcheck_round(&mut round1, 1, first).unwrap();
        assert_ne!(round0.diagnostic_state(), round1.diagnostic_state());
    }

    #[test]
    fn truncated_or_extended_degree_wires_are_rejected() {
        let (proof, initial_claim) = valid_random_wire(0xa11c_e5);
        let mut transcript = Transcript::new(test_hash);
        assert_eq!(
            verify_state_only_sumcheck_streaming(
                &mut transcript,
                &proof[..STATE_ONLY_SUMCHECK_BYTES - 16],
                initial_claim,
            ),
            Err(StateOnlySumcheckVerifyError::BadLength)
        );
        let mut extended = proof.to_vec();
        extended.extend_from_slice(&[0u8; 16]);
        let mut transcript = Transcript::new(test_hash);
        assert_eq!(
            verify_state_only_sumcheck_streaming(&mut transcript, &extended, initial_claim),
            Err(StateOnlySumcheckVerifyError::BadLength)
        );
    }

    #[test]
    fn exact_wire_and_arithmetic_inventory_is_frozen() {
        assert_eq!(STATE_ONLY_SUMCHECK_ROUND_BYTES, 448);
        assert_eq!(STATE_ONLY_SUMCHECK_BYTES, 4_480);
        assert_eq!(STATE_ONLY_SUMCHECK_ABSORB_BYTES, 449);
        assert_eq!(STATE_ONLY_VERIFY_QM31_MULS_PER_ROUND, 30);
        assert_eq!(STATE_ONLY_VERIFY_QM31_ADDS_PER_ROUND, 41);
        assert_eq!(STATE_ONLY_VERIFY_QM31_MULS, 300);
        assert_eq!(STATE_ONLY_VERIFY_QM31_ADDS, 410);
        assert_eq!(STATE_ONLY_VERIFY_M31_MULS_PER_ROUND, 266);
        assert_eq!(STATE_ONLY_VERIFY_M31_MULS, 2_660);
    }
}
