//! Aspis v5 masking component (B): degree-preserving chained sumcheck masks.
//!
//! The state-only sumcheck releases ten complete degree-27 polynomials. A
//! random multilinear table cannot hide coefficients of degrees 2 through 27.
//! This module instead samples, for each round, a uniformly random degree-27
//! polynomial `p_i` satisfying
//!
//! ```text
//! p_i(0) + p_i(1) = 0.
//! ```
//!
//! If `s_i` is the incoming mask claim, the mask contribution in round `i` is
//! `s_i / 2 + p_i(X)`. Its endpoint sum is exactly `s_i`; evaluating it at the
//! round challenge gives `s_{i+1}`. The resulting ten-variate mask is therefore
//! globally consistent and its Boolean-cube sum is the sampled initial claim.
//!
//! `AspisFormal/SumcheckMasking.lean` kernel-checks the corresponding algebra,
//! the exact sampler bijection, and the conditional distribution of each full
//! round polynomial.
//!
//! The production V5 host commits this mask in Component B before dependent
//! transcript challenges and authenticates the terminal evaluation. The
//! source-authentic proof connects the sampler, host flow, layout, and terminal.

use aspis_core::field::QM31;
use aspis_core::state_only_sumcheck::{
    evaluate_state_only_polynomial, state_only_boundary_sum, StateOnlySumcheckPolynomial,
    STATE_ONLY_SUMCHECK_COEFFICIENTS, STATE_ONLY_SUMCHECK_DEGREE, STATE_ONLY_SUMCHECK_ROUNDS,
};
use aspis_core::transcript::Transcript;

use crate::state_only_zerocheck::{
    prove_state_only_sumcheck_from_claim, StateOnlyZerocheckProveError, StateOnlyZerocheckTrace,
};
use crate::v5_mask::{sample_qm31, MaskSampleExhausted, Qm31WordSource};

/// One initial mask claim plus 27 free coefficients in each of ten rounds.
pub const V5_SUMCHECK_MASK_RANDOMNESS: usize =
    1 + STATE_ONLY_SUMCHECK_ROUNDS * STATE_ONLY_SUMCHECK_DEGREE;

const _: () = assert!(STATE_ONLY_SUMCHECK_ROUNDS == 10);
const _: () = assert!(STATE_ONLY_SUMCHECK_DEGREE == 27);
const _: () = assert!(STATE_ONLY_SUMCHECK_COEFFICIENTS == 28);
const _: () = assert!(V5_SUMCHECK_MASK_RANDOMNESS == 271);

/// A fixed, globally chained degree-27 mask for the ten-round sumcheck.
///
/// Each stored round has endpoint sum zero. The incoming half-claim carrier is
/// added only when that round is evaluated or emitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5SumcheckMask {
    initial_claim: QM31,
    zero_boundary_rounds: [StateOnlySumcheckPolynomial; STATE_ONLY_SUMCHECK_ROUNDS],
}

fn sample_zero_boundary_round<S: Qm31WordSource>(
    source: &mut S,
) -> Result<StateOnlySumcheckPolynomial, MaskSampleExhausted> {
    let mut polynomial = [QM31::ZERO; STATE_ONLY_SUMCHECK_COEFFICIENTS];
    let mut tail_sum = QM31::ZERO;
    let mut coefficient = 1;
    while coefficient < STATE_ONLY_SUMCHECK_COEFFICIENTS {
        let sampled = sample_qm31(source)?;
        polynomial[coefficient] = sampled;
        tail_sum = tail_sum.add(sampled);
        coefficient += 1;
    }
    polynomial[0] = tail_sum.neg().half();
    debug_assert_eq!(state_only_boundary_sum(&polynomial), QM31::ZERO);
    Ok(polynomial)
}

impl V5SumcheckMask {
    /// Sample the initial claim and all 270 free round coefficients.
    ///
    /// For each round, coefficients `c1..c27` are independent uniform QM31
    /// values and `c0 = -(c1 + ... + c27) / 2`. This is a bijection onto the
    /// full zero-boundary coefficient subspace proved in Lean.
    pub fn sample<S: Qm31WordSource>(source: &mut S) -> Result<Self, MaskSampleExhausted> {
        let initial_claim = sample_qm31(source)?;
        let mut zero_boundary_rounds =
            [[QM31::ZERO; STATE_ONLY_SUMCHECK_COEFFICIENTS]; STATE_ONLY_SUMCHECK_ROUNDS];
        let mut round = 0;
        while round < STATE_ONLY_SUMCHECK_ROUNDS {
            zero_boundary_rounds[round] = sample_zero_boundary_round(source)?;
            round += 1;
        }
        Ok(Self {
            initial_claim,
            zero_boundary_rounds,
        })
    }

    /// The Boolean-cube sum claimed for the mask oracle.
    pub const fn initial_claim(&self) -> QM31 {
        self.initial_claim
    }

    /// The invariant-carrying zero-boundary polynomial for one round.
    pub fn zero_boundary_round(&self, round: usize) -> Option<&StateOnlySumcheckPolynomial> {
        self.zero_boundary_rounds.get(round)
    }

    /// The coefficient committed by the fixed Component-B lane.  The
    /// constant coefficient is recomputed from the 27 stored tail
    /// coefficients in the same increasing order used by the original lane
    /// encoder; positive coefficients are read directly.
    pub(crate) fn commitment_coefficient(&self, round: usize, coefficient: usize) -> QM31 {
        if coefficient == 0 {
            let mut tail_sum = QM31::ZERO;
            let mut offset = 1usize;
            while offset < STATE_ONLY_SUMCHECK_COEFFICIENTS {
                tail_sum = tail_sum.add(self.zero_boundary_rounds[round][offset]);
                offset += 1;
            }
            tail_sum.neg().mul(QM31::ONE.half())
        } else {
            self.zero_boundary_rounds[round][coefficient]
        }
    }

    /// Coordinates used by the provisional component-B commitment lane.
    ///
    /// The order is the initial claim followed by `c1..c27` for rounds zero
    /// through nine. The omitted constant coefficient in each round is fixed
    /// by the zero-boundary equation.
    pub(crate) fn commitment_coordinates(&self) -> [QM31; V5_SUMCHECK_MASK_RANDOMNESS] {
        let mut coordinates = [QM31::ZERO; V5_SUMCHECK_MASK_RANDOMNESS];
        coordinates[0] = self.initial_claim;
        let mut round = 0;
        while round < STATE_ONLY_SUMCHECK_ROUNDS {
            let mut coefficient = 1;
            while coefficient < STATE_ONLY_SUMCHECK_COEFFICIENTS {
                let coordinate = 1 + round * STATE_ONLY_SUMCHECK_DEGREE + (coefficient - 1);
                coordinates[coordinate] = self.zero_boundary_rounds[round][coefficient];
                coefficient += 1;
            }
            round += 1;
        }
        coordinates
    }

    /// Form `incoming_claim / 2 + p_i(X)` for one round.
    pub fn round_polynomial(
        &self,
        round: usize,
        incoming_claim: QM31,
    ) -> Option<StateOnlySumcheckPolynomial> {
        let mut polynomial = match self.zero_boundary_rounds.get(round) {
            Some(polynomial) => *polynomial,
            None => return None,
        };
        polynomial[0] = polynomial[0].add(incoming_claim.half());
        debug_assert_eq!(state_only_boundary_sum(&polynomial), incoming_claim);
        Some(polynomial)
    }

    /// Evaluate the globally chained ten-variate mask at a field point.
    pub fn evaluate(&self, point: &[QM31; STATE_ONLY_SUMCHECK_ROUNDS]) -> QM31 {
        let mut claim = self.initial_claim;
        let mut round = 0;
        while round < STATE_ONLY_SUMCHECK_ROUNDS {
            let challenge = point[round];
            let polynomial = match self.round_polynomial(round, claim) {
                Some(polynomial) => polynomial,
                None => panic!("the fixed point has exactly ten coordinates"),
            };
            claim = evaluate_state_only_polynomial(&polynomial, challenge);
            round += 1;
        }
        claim
    }

    /// Mix one real round polynomial at a visible total incoming claim.
    ///
    /// The real polynomial's boundary determines the hidden incoming mask
    /// claim. The returned polynomial has boundary `total_claim` exactly.
    pub fn mixed_round_polynomial(
        &self,
        round: usize,
        total_claim: QM31,
        eta: QM31,
        real: &StateOnlySumcheckPolynomial,
    ) -> Option<StateOnlySumcheckPolynomial> {
        let real_claim = state_only_boundary_sum(real);
        let mask_claim = total_claim.sub(eta.mul(real_claim));
        let mut mixed = match self.round_polynomial(round, mask_claim) {
            Some(polynomial) => polynomial,
            None => return None,
        };
        let mut coefficient = 0;
        while coefficient < STATE_ONLY_SUMCHECK_COEFFICIENTS {
            mixed[coefficient] = mixed[coefficient].add(eta.mul(real[coefficient]));
            coefficient += 1;
        }
        debug_assert_eq!(state_only_boundary_sum(&mixed), total_claim);
        Some(mixed)
    }
}

#[allow(dead_code)]
fn v5_sumcheck_mask_mixing_evaluate_correspondence(
    mask: &V5SumcheckMask,
    round: usize,
    total_claim: QM31,
    eta: QM31,
    real: &StateOnlySumcheckPolynomial,
    point: &[QM31; STATE_ONLY_SUMCHECK_ROUNDS],
) -> (Option<StateOnlySumcheckPolynomial>, QM31) {
    (
        mask.mixed_round_polynomial(round, total_claim, eta, real),
        mask.evaluate(point),
    )
}

/// Exercise the ordinary state-only sumcheck on `R + eta*F`.
///
/// The caller is responsible for the transcript schedule: a binding commitment
/// to this mask and `initial_claim` must precede the sampling of nonzero `eta`.
/// This wrapper deliberately accepts an already sampled `eta` because the v5
/// commitment and verifier wire do not yet exist.
pub fn prove_v5_masked_state_only_zerocheck<F, E>(
    transcript: &mut Transcript,
    mask: &V5SumcheckMask,
    eta: QM31,
    mut original_oracle: F,
) -> Result<StateOnlyZerocheckTrace, StateOnlyZerocheckProveError<E>>
where
    F: FnMut(&[QM31; STATE_ONLY_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    prove_state_only_sumcheck_from_claim(
        transcript,
        |point| Ok(mask.evaluate(point).add(eta.mul(original_oracle(point)?))),
        mask.initial_claim,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31, P};
    use aspis_core::state_only_sumcheck::{
        decode_state_only_polynomial, encode_state_only_polynomial,
        verify_state_only_sumcheck_streaming, StateOnlySumcheckVerifyError,
        STATE_ONLY_SUMCHECK_ROUND_BYTES,
    };
    use aspis_core::transcript::label;

    use crate::HOST_HASH;

    struct XorShift(u64);

    impl Qm31WordSource for XorShift {
        fn next_word(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            (x >> 21) as u32
        }
    }

    struct AlwaysOutOfRange;

    impl Qm31WordSource for AlwaysOutOfRange {
        fn next_word(&mut self) -> u32 {
            u32::MAX
        }
    }

    fn sample(seed: u64) -> V5SumcheckMask {
        V5SumcheckMask::sample(&mut XorShift(seed)).expect("test source remains canonical")
    }

    fn sample_iterator_reference<S: Qm31WordSource>(
        source: &mut S,
    ) -> Result<V5SumcheckMask, MaskSampleExhausted> {
        let initial_claim = sample_qm31(source)?;
        let mut zero_boundary_rounds =
            [[QM31::ZERO; STATE_ONLY_SUMCHECK_COEFFICIENTS]; STATE_ONLY_SUMCHECK_ROUNDS];
        for polynomial in &mut zero_boundary_rounds {
            let mut tail_sum = QM31::ZERO;
            for coefficient in &mut polynomial[1..] {
                *coefficient = sample_qm31(source)?;
                tail_sum = tail_sum.add(*coefficient);
            }
            polynomial[0] = tail_sum.neg().half();
        }
        Ok(V5SumcheckMask {
            initial_claim,
            zero_boundary_rounds,
        })
    }

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn boolean_point(assignment: usize) -> [QM31; STATE_ONLY_SUMCHECK_ROUNDS] {
        core::array::from_fn(|coordinate| {
            if (assignment >> (STATE_ONLY_SUMCHECK_ROUNDS - 1 - coordinate)) & 1 == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        })
    }

    #[test]
    fn sampler_enforces_every_zero_boundary_and_retry_limit() {
        let mask = sample(0x5a17_c9e3_8421_6d0fu64);
        assert_eq!(V5_SUMCHECK_MASK_RANDOMNESS, 271);
        assert!(mask
            .zero_boundary_rounds
            .iter()
            .all(|polynomial| state_only_boundary_sum(polynomial) == QM31::ZERO));
        assert!(mask
            .zero_boundary_rounds
            .iter()
            .flatten()
            .any(|coefficient| *coefficient != QM31::ZERO));

        let mut bad = AlwaysOutOfRange;
        assert_eq!(V5SumcheckMask::sample(&mut bad), Err(MaskSampleExhausted));
    }

    #[test]
    fn indexed_sampler_matches_iterator_reference_exactly() {
        for seed in 0..64 {
            let seed = 0x7b51_090d_e218_43a1u64 ^ seed;
            let mut indexed_source = XorShift(seed);
            let mut iterator_source = XorShift(seed);
            assert_eq!(
                V5SumcheckMask::sample(&mut indexed_source),
                sample_iterator_reference(&mut iterator_source)
            );
            assert_eq!(indexed_source.0, iterator_source.0);
        }

        let mut indexed_bad = AlwaysOutOfRange;
        let mut iterator_bad = AlwaysOutOfRange;
        assert_eq!(
            V5SumcheckMask::sample(&mut indexed_bad),
            sample_iterator_reference(&mut iterator_bad)
        );
    }

    #[test]
    fn boolean_cube_sum_is_exactly_the_initial_claim() {
        let mask = sample(0xc001_d00d_7182_4ab9u64);
        let sum = (0..1usize << STATE_ONLY_SUMCHECK_ROUNDS)
            .fold(QM31::ZERO, |accumulator, assignment| {
                accumulator.add(mask.evaluate(&boolean_point(assignment)))
            });
        assert_eq!(sum, mask.initial_claim());
    }

    #[test]
    fn round_boundaries_chain_to_the_global_evaluation() {
        let mask = sample(0x91e1_0da5_2284_f731u64);
        let point = core::array::from_fn(|coordinate| q(17 + coordinate as u32));
        let mut claim = mask.initial_claim();
        for (round, challenge) in point.iter().copied().enumerate() {
            let polynomial = mask.round_polynomial(round, claim).unwrap();
            assert_eq!(state_only_boundary_sum(&polynomial), claim);
            claim = evaluate_state_only_polynomial(&polynomial, challenge);
        }
        assert_eq!(claim, mask.evaluate(&point));
    }

    #[test]
    fn correspondence_helper_calls_the_actual_mixing_and_evaluator() {
        let mask = sample(0x5f27_a306_410d_e9cbu64);
        let point = core::array::from_fn(|coordinate| q(401 + coordinate as u32));
        let real = *mask.zero_boundary_round(7).unwrap();
        let total_claim = q(521);
        let eta = q(523);

        for round in 0..STATE_ONLY_SUMCHECK_ROUNDS {
            assert_eq!(
                v5_sumcheck_mask_mixing_evaluate_correspondence(
                    &mask,
                    round,
                    total_claim,
                    eta,
                    &real,
                    &point,
                ),
                (
                    mask.mixed_round_polynomial(round, total_claim, eta, &real),
                    mask.evaluate(&point),
                )
            );
        }

        assert_eq!(
            v5_sumcheck_mask_mixing_evaluate_correspondence(
                &mask,
                STATE_ONLY_SUMCHECK_ROUNDS,
                total_claim,
                eta,
                &real,
                &point,
            ),
            (None, mask.evaluate(&point))
        );
    }

    #[test]
    fn masked_prover_matches_round_model_streaming_verifier_and_terminal() {
        let mask = sample(0x52bd_817c_a091_f3e5u64);
        let mut real = sample(0xa30f_6b29_11d4_88c7u64);
        real.initial_claim = QM31::ZERO;
        let eta = q(701);
        let statement = b"v5-sumcheck-mask-round-model";

        let mut prover_transcript = Transcript::new(HOST_HASH);
        prover_transcript.absorb(label::STATEMENT, statement);
        let trace =
            prove_v5_masked_state_only_zerocheck(&mut prover_transcript, &mask, eta, |point| {
                Ok::<_, ()>(real.evaluate(point))
            })
            .unwrap();

        let mut mask_claim = mask.initial_claim();
        let mut real_claim = QM31::ZERO;
        let mut total_claim = mask.initial_claim();
        for round in 0..STATE_ONLY_SUMCHECK_ROUNDS {
            let start = round * STATE_ONLY_SUMCHECK_ROUND_BYTES;
            let polynomial = decode_state_only_polynomial(
                round,
                &trace.proof[start..start + STATE_ONLY_SUMCHECK_ROUND_BYTES],
            )
            .unwrap();
            let mask_round = mask.round_polynomial(round, mask_claim).unwrap();
            let real_round = real.round_polynomial(round, real_claim).unwrap();
            let expected = mask
                .mixed_round_polynomial(round, total_claim, eta, &real_round)
                .unwrap();
            assert_eq!(polynomial, expected);
            for coefficient in 0..STATE_ONLY_SUMCHECK_COEFFICIENTS {
                assert_eq!(
                    expected[coefficient],
                    mask_round[coefficient].add(eta.mul(real_round[coefficient]))
                );
            }
            let challenge = trace.challenges[round];
            mask_claim = evaluate_state_only_polynomial(&mask_round, challenge);
            real_claim = evaluate_state_only_polynomial(&real_round, challenge);
            total_claim = evaluate_state_only_polynomial(&expected, challenge);
            assert_eq!(total_claim, mask_claim.add(eta.mul(real_claim)));
        }
        assert_eq!(trace.terminal_claim, total_claim);
        assert_eq!(
            trace.terminal_claim,
            mask.evaluate(&trace.challenges)
                .add(eta.mul(real.evaluate(&trace.challenges)))
        );

        let mut verifier_transcript = Transcript::new(HOST_HASH);
        verifier_transcript.absorb(label::STATEMENT, statement);
        let verified = verify_state_only_sumcheck_streaming(
            &mut verifier_transcript,
            &trace.proof,
            mask.initial_claim(),
        )
        .unwrap();
        assert_eq!(verified.point, trace.challenges);
        assert_eq!(verified.terminal_claim, trace.terminal_claim);
        assert_eq!(
            verifier_transcript.diagnostic_state(),
            prover_transcript.diagnostic_state()
        );

        let mut mutated = trace.proof;
        let mut first =
            decode_state_only_polynomial(0, &mutated[..STATE_ONLY_SUMCHECK_ROUND_BYTES]).unwrap();
        first[2] = first[2].add(QM31::ONE);
        mutated[..STATE_ONLY_SUMCHECK_ROUND_BYTES]
            .copy_from_slice(&encode_state_only_polynomial(&first));
        let mut mutation_transcript = Transcript::new(HOST_HASH);
        mutation_transcript.absorb(label::STATEMENT, statement);
        assert_eq!(
            verify_state_only_sumcheck_streaming(
                &mut mutation_transcript,
                &mutated,
                mask.initial_claim(),
            ),
            Err(StateOnlySumcheckVerifyError::BoundaryMismatch { round: 0 })
        );
    }

    #[test]
    fn nonzero_real_sum_cannot_use_the_mask_claim_as_the_boundary() {
        let mask = sample(0x9f04_26c1_7b8e_35dau64);
        let mut real = sample(0x0b75_18a3_c642_f91eu64);
        real.initial_claim = QM31::ONE;
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::STATEMENT, b"false-original-sum");
        assert_eq!(
            prove_v5_masked_state_only_zerocheck(
                &mut transcript,
                &mask,
                q(991),
                |point| Ok::<_, ()>(real.evaluate(point)),
            ),
            Err(StateOnlyZerocheckProveError::BoundaryMismatch { round: 0 })
        );
    }

    #[test]
    fn generated_qm31_values_are_canonical() {
        let mask = sample(0x412f_e083_91ac_77b2u64);
        for value in
            core::iter::once(&mask.initial_claim).chain(mask.zero_boundary_rounds.iter().flatten())
        {
            assert!(value.c0.a.0 < P);
            assert!(value.c0.b.0 < P);
            assert!(value.c1.a.0 < P);
            assert!(value.c1.b.0 < P);
        }
    }
}
