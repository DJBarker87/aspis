//! Degree-10 payment zerocheck sumcheck wire.
//!
//! A full round polynomial has coefficients `c_0..c_10`. The boundary
//! identity determines `c_1`, so the proof transmits
//! `c_0,c_2,c_3,...,c_10` (ten QM31 elements). This saves one element per
//! round without changing the accepted polynomial.

use crate::field::{PreparedQm31Multiplier, QM31};
use crate::transcript::{label, ChallengeSampleExhausted, Transcript};

pub const PAYMENT_SUMCHECK_ROUNDS: usize = 10;
pub const PAYMENT_SUMCHECK_DEGREE: usize = 10;
pub const PAYMENT_SUMCHECK_FULL_COEFFICIENTS: usize = PAYMENT_SUMCHECK_DEGREE + 1;
pub const PAYMENT_SUMCHECK_WIRE_COEFFICIENTS: usize = PAYMENT_SUMCHECK_DEGREE;
pub const PAYMENT_SUMCHECK_ROUND_BYTES: usize = PAYMENT_SUMCHECK_WIRE_COEFFICIENTS * 16;
pub const PAYMENT_SUMCHECK_BYTES: usize = PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_ROUND_BYTES;

pub type PaymentSumcheckFullPolynomial = [QM31; PAYMENT_SUMCHECK_FULL_COEFFICIENTS];
pub type PaymentSumcheckWirePolynomial = [QM31; PAYMENT_SUMCHECK_WIRE_COEFFICIENTS];

pub const PAYMENT_CONSTRAINT_REGISTRY_VERSION: u8 = 2;
pub const PAYMENT_CONSTRAINT_COUNT: u16 = 252;
pub const PAYMENT_RANDOMIZED_CLAIM_COUNT: u16 = 67;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentConstraintChallenges {
    pub theta: QM31,
    pub zerocheck_point: [QM31; PAYMENT_SUMCHECK_ROUNDS],
    pub mu: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentSumcheckVerification {
    pub point: [QM31; PAYMENT_SUMCHECK_ROUNDS],
    pub terminal_claim: QM31,
}

/// Bind the frozen registry and two public zero helper-sum claims, then
/// sample every challenge which precedes the first sumcheck message.
pub fn begin_payment_zerocheck(
    transcript: &mut Transcript,
) -> Result<PaymentConstraintChallenges, ChallengeSampleExhausted> {
    let mut registry = [0u8; 8];
    registry[0] = PAYMENT_CONSTRAINT_REGISTRY_VERSION;
    registry[1..3].copy_from_slice(&PAYMENT_CONSTRAINT_COUNT.to_le_bytes());
    registry[3..5].copy_from_slice(&PAYMENT_RANDOMIZED_CLAIM_COUNT.to_le_bytes());
    registry[5] = PAYMENT_SUMCHECK_ROUNDS as u8;
    registry[6] = PAYMENT_SUMCHECK_DEGREE as u8;
    registry[7] = PAYMENT_SUMCHECK_WIRE_COEFFICIENTS as u8;
    transcript.absorb(label::M31_PAYMENT_CONSTRAINT_REGISTRY, &registry);
    transcript.absorb(label::M31_PAYMENT_HELPER_SUMS, &[0u8; 32]);
    let theta = transcript.challenge_qm31()?;
    let mut zerocheck_point = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];
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

pub fn absorb_payment_sumcheck_round(
    transcript: &mut Transcript,
    round: usize,
    wire: &PaymentSumcheckWirePolynomial,
) -> Result<QM31, ChallengeSampleExhausted> {
    let encoded = encode_wire(wire);
    let mut framed = [0u8; 1 + PAYMENT_SUMCHECK_ROUND_BYTES];
    framed[0] = round as u8;
    framed[1..].copy_from_slice(&encoded);
    transcript.absorb(label::M31_PAYMENT_ZEROCHECK_SUMCHECK, &framed);
    transcript.challenge_qm31()
}

pub fn verify_payment_sumcheck_messages(
    transcript: &mut Transcript,
    messages: &[PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS],
) -> Result<PaymentSumcheckVerification, ChallengeSampleExhausted> {
    verify_payment_sumcheck_messages_from_claim(transcript, messages, QM31::ZERO)
}

/// Verify the same degree-10 wire from an explicitly bound initial claim.
/// The non-hiding protocol uses zero; the hiding protocol uses its previously
/// absorbed random mask claim.
pub fn verify_payment_sumcheck_messages_from_claim(
    transcript: &mut Transcript,
    messages: &[PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS],
    initial_claim: QM31,
) -> Result<PaymentSumcheckVerification, ChallengeSampleExhausted> {
    let mut point = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];
    let mut running_claim = initial_claim;
    for (round, wire) in messages.iter().enumerate() {
        let full = restore_polynomial(wire, running_claim);
        let challenge = absorb_payment_sumcheck_round(transcript, round, wire)?;
        running_claim = evaluate(&full, challenge);
        point[round] = challenge;
    }
    Ok(PaymentSumcheckVerification {
        point,
        terminal_claim: running_claim,
    })
}

pub fn compress_polynomial(full: &PaymentSumcheckFullPolynomial) -> PaymentSumcheckWirePolynomial {
    let mut wire = [QM31::ZERO; PAYMENT_SUMCHECK_WIRE_COEFFICIENTS];
    wire[0] = full[0];
    wire[1..].copy_from_slice(&full[2..]);
    wire
}

/// Restore `c_1` from `p(0)+p(1)=running_claim`.
pub fn restore_polynomial(
    wire: &PaymentSumcheckWirePolynomial,
    running_claim: QM31,
) -> PaymentSumcheckFullPolynomial {
    let mut full = [QM31::ZERO; PAYMENT_SUMCHECK_FULL_COEFFICIENTS];
    full[0] = wire[0];
    full[2..].copy_from_slice(&wire[1..]);
    let higher_sum = full[2..].iter().copied().fold(QM31::ZERO, QM31::add);
    full[1] = running_claim.sub(full[0].add(full[0])).sub(higher_sum);
    full
}

pub fn boundary_sum(full: &PaymentSumcheckFullPolynomial) -> QM31 {
    let at_one = full.iter().copied().fold(QM31::ZERO, QM31::add);
    full[0].add(at_one)
}

pub fn evaluate(full: &PaymentSumcheckFullPolynomial, challenge: QM31) -> QM31 {
    let prepared = PreparedQm31Multiplier::new(challenge);
    full.iter()
        .rev()
        .copied()
        .fold(QM31::ZERO, |value, coefficient| {
            prepared.mul(value).add(coefficient)
        })
}

pub fn encode_wire(wire: &PaymentSumcheckWirePolynomial) -> [u8; PAYMENT_SUMCHECK_ROUND_BYTES] {
    let mut bytes = [0u8; PAYMENT_SUMCHECK_ROUND_BYTES];
    for (index, coefficient) in wire.iter().enumerate() {
        coefficient.write_le_bytes(&mut bytes[index * 16..][..16]);
    }
    bytes
}

pub fn decode_wire(bytes: &[u8]) -> Option<PaymentSumcheckWirePolynomial> {
    if bytes.len() != PAYMENT_SUMCHECK_ROUND_BYTES {
        return None;
    }
    let mut wire = [QM31::ZERO; PAYMENT_SUMCHECK_WIRE_COEFFICIENTS];
    for (index, chunk) in bytes.chunks_exact(16).enumerate() {
        wire[index] = QM31::from_le_bytes(chunk)?;
    }
    Some(wire)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, M31};

    fn value(index: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(index * 17 + 1), M31(index * 17 + 3)),
            c1: CM31::new(M31(index * 17 + 5), M31(index * 17 + 7)),
        }
    }

    #[test]
    fn omitted_linear_coefficient_roundtrips_from_boundary() {
        let full = core::array::from_fn(|index| value(index as u32));
        let claim = boundary_sum(&full);
        let wire = compress_polynomial(&full);
        assert_eq!(restore_polynomial(&wire, claim), full);
        assert_eq!(decode_wire(&encode_wire(&wire)), Some(wire));
        for challenge in [value(19), value(23), value(29)] {
            assert_eq!(
                evaluate(&restore_polynomial(&wire, claim), challenge),
                evaluate(&full, challenge)
            );
        }
    }
}
