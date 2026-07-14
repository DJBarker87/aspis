//! Host prover for the ten-round payment zerocheck.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::statement_hiding::{
    begin_payment_hiding_sumcheck, initial_payment_mask_claim, mask_payment_sumcheck_round,
    next_payment_mask_claim, payment_sparse_mask_value, PaymentSumcheckMaskPolynomials,
};
use aspis_core::statement_sumcheck::{
    absorb_payment_sumcheck_round, begin_payment_zerocheck, boundary_sum, compress_polynomial,
    evaluate, PaymentConstraintChallenges, PaymentSumcheckFullPolynomial,
    PaymentSumcheckWirePolynomial, PAYMENT_SUMCHECK_DEGREE, PAYMENT_SUMCHECK_ROUNDS,
};
use aspis_core::transcript::{ChallengeSampleExhausted, Transcript};
use aspis_statement::{
    direct_range_hiding_trace_openings_at_point, evaluate_constraint_point,
    evaluate_direct_range_hiding_constraint_point, trace_openings_at_point, ConstraintBuildError,
    DirectRangeHidingHelpersV4, PaymentHelpersV4, SpendPublic, SpendTraceV4,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaymentZerocheckTrace {
    pub messages: [PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS],
    pub challenges: [QM31; PAYMENT_SUMCHECK_ROUNDS],
    pub terminal_claim: QM31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendPaymentZerocheck {
    pub batching: PaymentConstraintChallenges,
    pub sumcheck: PaymentZerocheckTrace,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaymentHidingZerocheckTrace {
    pub initial_mask_claim: QM31,
    pub eta: QM31,
    pub messages: [PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS],
    pub challenges: [QM31; PAYMENT_SUMCHECK_ROUNDS],
    pub masked_terminal_claim: QM31,
    /// Prover-internal audit value. This is never serialized by the hiding
    /// profile because revealing it would undo the terminal mask.
    pub original_terminal_claim: QM31,
    /// Prover-internal audit value which must be bound by the mask-oracle PCS.
    pub terminal_mask_claim: QM31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendPaymentHidingZerocheck {
    pub batching: PaymentConstraintChallenges,
    pub sumcheck: PaymentHidingZerocheckTrace,
}

/// Candidate profile-14 payment proof. The mask terminal is not a free proof
/// scalar: it is `G(z)S(z)` and is therefore checked from C2 slot one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendPaymentCommittedHidingZerocheck {
    pub batching: PaymentConstraintChallenges,
    pub initial_mask_claim: QM31,
    pub eta: QM31,
    pub sumcheck: PaymentZerocheckTrace,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PaymentZerocheckProveError<E> {
    Oracle(E),
    BoundaryMismatch { round: usize },
    TerminalMismatch,
    ChallengeSampleExhausted,
}

impl<E> From<ChallengeSampleExhausted> for PaymentZerocheckProveError<E> {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

fn interpolate(values: &[QM31; PAYMENT_SUMCHECK_DEGREE + 1]) -> PaymentSumcheckFullPolynomial {
    let mut output = [QM31::ZERO; PAYMENT_SUMCHECK_DEGREE + 1];
    for i in 0..=PAYMENT_SUMCHECK_DEGREE {
        let mut basis = [QM31::ZERO; PAYMENT_SUMCHECK_DEGREE + 1];
        basis[0] = QM31::ONE;
        let mut basis_degree = 0usize;
        let mut denominator = M31::ONE;
        for j in 0..=PAYMENT_SUMCHECK_DEGREE {
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
        for coefficient in 0..=PAYMENT_SUMCHECK_DEGREE {
            output[coefficient] = output[coefficient].add(scale.mul(basis[coefficient]));
        }
    }
    output
}

/// Prove a degree-at-most-ten polynomial oracle whose sum over the Boolean
/// cube is zero. The transcript must already have sampled theta, the
/// zerocheck point, and mu via `begin_payment_zerocheck`.
pub fn prove_payment_zerocheck<F, E>(
    transcript: &mut Transcript,
    oracle: F,
) -> Result<PaymentZerocheckTrace, PaymentZerocheckProveError<E>>
where
    F: FnMut(&[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    prove_payment_sumcheck_from_claim(transcript, oracle, QM31::ZERO)
}

/// Prove the same degree-ten oracle from an explicitly committed initial
/// claim. The hiding profile uses the public sum of its committed mask
/// polynomial; ordinary zerocheck continues to use zero.
pub fn prove_payment_sumcheck_from_claim<F, E>(
    transcript: &mut Transcript,
    mut oracle: F,
    initial_claim: QM31,
) -> Result<PaymentZerocheckTrace, PaymentZerocheckProveError<E>>
where
    F: FnMut(&[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    let mut messages = [[QM31::ZERO; PAYMENT_SUMCHECK_DEGREE]; PAYMENT_SUMCHECK_ROUNDS];
    let mut challenges = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];
    let mut running_claim = initial_claim;
    let mut prefix = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];

    for round in 0..PAYMENT_SUMCHECK_ROUNDS {
        let mut samples = [QM31::ZERO; PAYMENT_SUMCHECK_DEGREE + 1];
        let remaining = PAYMENT_SUMCHECK_ROUNDS - round - 1;
        for (sample_index, sample) in samples.iter_mut().enumerate() {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample_index as u32)));
            let mut total = QM31::ZERO;
            for assignment in 0..(1usize << remaining) {
                for offset in 0..remaining {
                    let bit = (assignment >> (remaining - 1 - offset)) & 1;
                    prefix[round + 1 + offset] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
                }
                total = total.add(oracle(&prefix).map_err(PaymentZerocheckProveError::Oracle)?);
            }
            *sample = total;
        }
        let full = interpolate(&samples);
        if boundary_sum(&full) != running_claim {
            return Err(PaymentZerocheckProveError::BoundaryMismatch { round });
        }
        let wire = compress_polynomial(&full);
        let challenge = absorb_payment_sumcheck_round(transcript, round, &wire)?;
        messages[round] = wire;
        challenges[round] = challenge;
        prefix[round] = challenge;
        running_claim = evaluate(&full, challenge);
    }

    if oracle(&challenges).map_err(PaymentZerocheckProveError::Oracle)? != running_claim {
        return Err(PaymentZerocheckProveError::TerminalMismatch);
    }
    Ok(PaymentZerocheckTrace {
        messages,
        challenges,
        terminal_claim: running_claim,
    })
}

/// Mask the complete degree-10 sumcheck transcript. This kernel is complete
/// and hides its round-polynomial coefficients, but is not independently
/// sound: the caller must bind `terminal_mask_claim` to a committed mask
/// oracle before accepting the resulting terminal equation.
pub fn prove_payment_zerocheck_hiding<F, E>(
    transcript: &mut Transcript,
    mut oracle: F,
    masks: &PaymentSumcheckMaskPolynomials,
) -> Result<PaymentHidingZerocheckTrace, PaymentZerocheckProveError<E>>
where
    F: FnMut(&[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> Result<QM31, E>,
{
    let initial_mask_claim = initial_payment_mask_claim(masks);
    let eta = begin_payment_hiding_sumcheck(transcript, initial_mask_claim)?;
    let mut messages = [[QM31::ZERO; PAYMENT_SUMCHECK_DEGREE]; PAYMENT_SUMCHECK_ROUNDS];
    let mut challenges = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];
    let mut original_running_claim = QM31::ZERO;
    let mut mask_running_claim = initial_mask_claim;
    let mut masked_running_claim = initial_mask_claim;
    let mut prefix = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];

    for round in 0..PAYMENT_SUMCHECK_ROUNDS {
        let mut samples = [QM31::ZERO; PAYMENT_SUMCHECK_DEGREE + 1];
        let remaining = PAYMENT_SUMCHECK_ROUNDS - round - 1;
        for (sample_index, sample) in samples.iter_mut().enumerate() {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample_index as u32)));
            let mut total = QM31::ZERO;
            for assignment in 0..(1usize << remaining) {
                for offset in 0..remaining {
                    let bit = (assignment >> (remaining - 1 - offset)) & 1;
                    prefix[round + 1 + offset] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
                }
                total = total.add(oracle(&prefix).map_err(PaymentZerocheckProveError::Oracle)?);
            }
            *sample = total;
        }
        let original = interpolate(&samples);
        if boundary_sum(&original) != original_running_claim {
            return Err(PaymentZerocheckProveError::BoundaryMismatch { round });
        }
        let masked =
            mask_payment_sumcheck_round(&original, &masks[round], mask_running_claim, eta, round);
        if boundary_sum(&masked) != masked_running_claim {
            return Err(PaymentZerocheckProveError::BoundaryMismatch { round });
        }
        let wire = compress_polynomial(&masked);
        let challenge = absorb_payment_sumcheck_round(transcript, round, &wire)?;
        messages[round] = wire;
        challenges[round] = challenge;
        prefix[round] = challenge;
        original_running_claim = evaluate(&original, challenge);
        masked_running_claim = evaluate(&masked, challenge);
        mask_running_claim = next_payment_mask_claim(&masked, &original, challenge, eta);
        debug_assert_eq!(
            masked_running_claim,
            mask_running_claim.add(eta.mul(original_running_claim))
        );
    }

    if oracle(&challenges).map_err(PaymentZerocheckProveError::Oracle)? != original_running_claim {
        return Err(PaymentZerocheckProveError::TerminalMismatch);
    }
    Ok(PaymentHidingZerocheckTrace {
        initial_mask_claim,
        eta,
        messages,
        challenges,
        masked_terminal_claim: masked_running_claim,
        original_terminal_claim: original_running_claim,
        terminal_mask_claim: mask_running_claim,
    })
}

fn equality_polynomial(
    left: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
    right: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> QM31 {
    left.iter()
        .zip(right)
        .fold(QM31::ONE, |product, (left, right)| {
            product.mul(
                left.mul(*right)
                    .add(QM31::ONE.sub(*left).mul(QM31::ONE.sub(*right))),
            )
        })
}

/// Production statement zerocheck. The caller must already have absorbed C1,
/// sampled `(lambda, chi)`, built/committed `helpers`, and absorbed the C2
/// root. The returned sumcheck challenges are the only admissible PCS point
/// `z`; no caller-supplied point enters this path.
pub fn prove_spend_payment_zerocheck(
    transcript: &mut Transcript,
    public: &SpendPublic,
    trace: &SpendTraceV4,
    helpers: &PaymentHelpersV4,
    lambda: QM31,
    chi: QM31,
) -> Result<SpendPaymentZerocheck, PaymentZerocheckProveError<ConstraintBuildError>> {
    let batching = begin_payment_zerocheck(transcript)?;
    let mu2 = batching.mu.square();
    let sumcheck = prove_payment_zerocheck(transcript, |point| {
        let openings =
            trace_openings_at_point(trace, helpers, point).ok_or(ConstraintBuildError::Shape)?;
        let composition =
            evaluate_constraint_point(public, &openings, point, lambda, chi, batching.theta)?;
        Ok(equality_polynomial(&batching.zerocheck_point, point)
            .mul(composition)
            .add(batching.mu.mul(openings.c2[0]))
            .add(mu2.mul(openings.c2[1])))
    })?;
    Ok(SpendPaymentZerocheck { batching, sumcheck })
}

pub fn prove_spend_payment_zerocheck_hiding(
    transcript: &mut Transcript,
    public: &SpendPublic,
    trace: &SpendTraceV4,
    helpers: &PaymentHelpersV4,
    lambda: QM31,
    chi: QM31,
    masks: &PaymentSumcheckMaskPolynomials,
) -> Result<SpendPaymentHidingZerocheck, PaymentZerocheckProveError<ConstraintBuildError>> {
    let batching = begin_payment_zerocheck(transcript)?;
    let mu2 = batching.mu.square();
    let sumcheck = prove_payment_zerocheck_hiding(
        transcript,
        |point| {
            let openings = trace_openings_at_point(trace, helpers, point)
                .ok_or(ConstraintBuildError::Shape)?;
            let composition =
                evaluate_constraint_point(public, &openings, point, lambda, chi, batching.theta)?;
            Ok(equality_polynomial(&batching.zerocheck_point, point)
                .mul(composition)
                .add(batching.mu.mul(openings.c2[0]))
                .add(mu2.mul(openings.c2[1])))
        },
        masks,
    )?;
    Ok(SpendPaymentHidingZerocheck { batching, sumcheck })
}

/// Direct-range hiding candidate with a PCS-bound terminal mask. The caller
/// must have committed `helpers.payment_mask` in C2 before entering this
/// transcript phase.
pub fn prove_spend_payment_zerocheck_committed_hiding(
    transcript: &mut Transcript,
    public: &SpendPublic,
    trace: &SpendTraceV4,
    helpers: &DirectRangeHidingHelpersV4,
    lambda: QM31,
    chi: QM31,
) -> Result<SpendPaymentCommittedHidingZerocheck, PaymentZerocheckProveError<ConstraintBuildError>>
{
    let batching = begin_payment_zerocheck(transcript)?;
    if trace.c1.len() != 49
        || trace.c1.iter().any(|column| column.len() != 1024)
        || helpers.payment_mask.len() != 1024
    {
        return Err(PaymentZerocheckProveError::Oracle(
            ConstraintBuildError::Shape,
        ));
    }
    let initial_mask_claim = (0..1024usize).fold(QM31::ZERO, |sum, row| {
        let point = core::array::from_fn(|coordinate| {
            let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
            if bit == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        });
        let c1 =
            core::array::from_fn(|column| QM31::from_cm31(CM31::from_m31(trace.c1[column][row])));
        sum.add(payment_sparse_mask_value(
            &c1,
            helpers.payment_mask[row],
            &point,
        ))
    });
    let eta = begin_payment_hiding_sumcheck(transcript, initial_mask_claim)?;
    let sumcheck = prove_payment_sumcheck_from_claim(
        transcript,
        |point| {
            let openings = direct_range_hiding_trace_openings_at_point(trace, helpers, point)
                .ok_or(ConstraintBuildError::Shape)?;
            let constraint_openings = openings.constraint_openings();
            let composition = evaluate_direct_range_hiding_constraint_point(
                public,
                &constraint_openings,
                point,
                lambda,
                chi,
                batching.theta,
            )?;
            let original = equality_polynomial(&batching.zerocheck_point, point)
                .mul(composition)
                .add(batching.mu.mul(openings.h1));
            let mask = payment_sparse_mask_value(&openings.c1, openings.payment_mask, point);
            Ok(mask.add(eta.mul(original)))
        },
        initial_mask_claim,
    )?;
    Ok(SpendPaymentCommittedHidingZerocheck {
        batching,
        initial_mask_claim,
        eta,
        sumcheck,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HOST_HASH;
    use aspis_core::statement_hiding::{
        begin_payment_hiding_sumcheck, PAYMENT_SUMCHECK_MASK_COEFFICIENTS,
    };
    use aspis_core::statement_sumcheck::{
        begin_payment_zerocheck, verify_payment_sumcheck_messages_from_claim,
    };
    use aspis_core::transcript::label;
    use aspis_statement::{
        apply_direct_range_c1_masks_v4, apply_direct_range_witness_v4,
        apply_expanded_hiding_padding_v4, build_direct_range_hiding_helpers_v4,
        build_payment_helpers_v4, build_spend_trace_v4, derive_nullifier, derive_owner_key,
        direct_range_c1_mask_cells_v4, direct_range_hiding_composition_table,
        direct_range_hiding_masked_terminal_value, direct_range_hiding_trace_openings_at_point,
        expanded_hiding_padding_cells_v4, merkle_root, note_commitment, output_commitment,
        payment_terminal_value, Digest, MerklePath, SpendWitness, COPY_HELPER_MASK_VARIABLES,
        PAYMENT_MASK_ORACLE_VALUES,
    };

    fn eq(a: &[QM31; 10], b: &[QM31; 10]) -> QM31 {
        a.iter().zip(b).fold(QM31::ONE, |product, (a, b)| {
            product.mul(a.mul(*b).add(QM31::ONE.sub(*a).mul(QM31::ONE.sub(*b))))
        })
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn spend_fixture() -> (SpendPublic, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let owner_key = derive_owner_key(&nullifier_key);
        let note = note_commitment(&owner_key, value, asset_id, &input_salt);
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
            index: 0x5_4321,
        };
        let public = SpendPublic {
            anchor: merkle_root(note, &merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee: 1,
        };
        let witness = SpendWitness {
            nullifier_key,
            input_salt,
            output_salt,
            output_owner_key,
            input_asset_id: asset_id,
            value,
            value_out,
            merkle_path,
        };
        (public, witness)
    }

    #[test]
    fn degree_ten_wire_proves_a_nontrivial_zero_polynomial() {
        let mut transcript = Transcript::new(HOST_HASH);
        let challenges = begin_payment_zerocheck(&mut transcript).unwrap();
        let r = challenges.zerocheck_point;
        // x0(x0-1) vanishes on the cube but is nonzero at the terminal.
        let trace = prove_payment_zerocheck(&mut transcript, |point| {
            Ok::<_, ()>(eq(&r, point).mul(point[0].mul(point[0].sub(QM31::ONE))))
        })
        .unwrap();
        assert_ne!(trace.terminal_claim, QM31::ZERO);
        assert_eq!(trace.challenges.len(), 10);
    }

    #[test]
    fn nonzero_boolean_claim_cannot_be_encoded_under_zero_boundary() {
        let mut transcript = Transcript::new(HOST_HASH);
        begin_payment_zerocheck(&mut transcript).unwrap();
        let error = prove_payment_zerocheck(&mut transcript, |_point| {
            Ok::<_, ()>(QM31 {
                c0: CM31::from_m31(M31::ONE),
                c1: CM31::ZERO,
            })
        })
        .unwrap_err();
        assert_eq!(
            error,
            PaymentZerocheckProveError::BoundaryMismatch { round: 0 }
        );
    }

    #[test]
    fn real_depth20_payment_constraints_drive_the_sumcheck_point() {
        let (public, witness) = spend_fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let mut prover_transcript = Transcript::new(HOST_HASH);
        prover_transcript.absorb(label::STATEMENT, &[0x51; 32]);
        prover_transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &[0x11; 33]);
        let lambda = prover_transcript.challenge_qm31().unwrap();
        let chi = prover_transcript.challenge_qm31().unwrap();
        let helpers = build_payment_helpers_v4(&trace, lambda, chi).unwrap();
        prover_transcript.absorb(label::M31_CIRCLE_C2_ROOT, &[0x22; 32]);

        let mut verifier_transcript = prover_transcript.clone();
        let proof = prove_spend_payment_zerocheck(
            &mut prover_transcript,
            &public,
            &trace,
            &helpers,
            lambda,
            chi,
        )
        .unwrap();

        let verifier_batching = begin_payment_zerocheck(&mut verifier_transcript).unwrap();
        assert_eq!(verifier_batching, proof.batching);
        let verified = aspis_core::statement_sumcheck::verify_payment_sumcheck_messages(
            &mut verifier_transcript,
            &proof.sumcheck.messages,
        )
        .unwrap();
        assert_eq!(verified.point, proof.sumcheck.challenges);
        let openings = trace_openings_at_point(&trace, &helpers, &verified.point).unwrap();
        assert_eq!(
            payment_terminal_value(
                &public,
                &openings,
                &verified.point,
                &verifier_batching,
                lambda,
                chi,
            )
            .unwrap(),
            verified.terminal_claim
        );
    }

    #[test]
    fn masked_degree_ten_wire_roundtrips_from_its_bound_initial_claim() {
        let mut prover_transcript = Transcript::new(HOST_HASH);
        let mut verifier_transcript = prover_transcript.clone();
        let prover_batching = begin_payment_zerocheck(&mut prover_transcript).unwrap();
        let verifier_batching = begin_payment_zerocheck(&mut verifier_transcript).unwrap();
        assert_eq!(prover_batching, verifier_batching);
        let masks: PaymentSumcheckMaskPolynomials = core::array::from_fn(|round| {
            core::array::from_fn(|coefficient| QM31 {
                c0: CM31::new(
                    M31(101 + round as u32 * 37 + coefficient as u32 * 3),
                    M31(211 + round as u32 * 41 + coefficient as u32 * 5),
                ),
                c1: CM31::new(
                    M31(307 + round as u32 * 43 + coefficient as u32 * 7),
                    M31(401 + round as u32 * 47 + coefficient as u32 * 11),
                ),
            })
        });
        assert_eq!(masks[0].len(), PAYMENT_SUMCHECK_MASK_COEFFICIENTS);
        let r = prover_batching.zerocheck_point;
        let proof = prove_payment_zerocheck_hiding(
            &mut prover_transcript,
            |point| Ok::<_, ()>(eq(&r, point).mul(point[0].mul(point[0].sub(QM31::ONE)))),
            &masks,
        )
        .unwrap();

        let eta = begin_payment_hiding_sumcheck(&mut verifier_transcript, proof.initial_mask_claim)
            .unwrap();
        assert_eq!(eta, proof.eta);
        let verified = verify_payment_sumcheck_messages_from_claim(
            &mut verifier_transcript,
            &proof.messages,
            proof.initial_mask_claim,
        )
        .unwrap();
        assert_eq!(verified.point, proof.challenges);
        assert_eq!(verified.terminal_claim, proof.masked_terminal_claim);
        assert_eq!(
            proof.masked_terminal_claim,
            proof
                .terminal_mask_claim
                .add(proof.eta.mul(proof.original_terminal_claim))
        );
    }

    #[test]
    fn real_depth20_statement_completes_the_masked_terminal_equation() {
        let (public, witness) = spend_fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        let padding_len = expanded_hiding_padding_cells_v4().len();
        let padding = (0..padding_len)
            .map(|index| {
                M31(
                    ((index as u64 * 1_103_515_245 + 12_345) % u64::from(aspis_core::field::P))
                        as u32,
                )
            })
            .collect::<Vec<_>>();
        apply_expanded_hiding_padding_v4(&mut trace, &padding).unwrap();

        let mut prover_transcript = Transcript::new(HOST_HASH);
        prover_transcript.absorb(label::STATEMENT, &[0x61; 32]);
        prover_transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &[0x31; 33]);
        let lambda = prover_transcript.challenge_qm31().unwrap();
        let chi = prover_transcript.challenge_qm31().unwrap();
        let helpers = build_payment_helpers_v4(&trace, lambda, chi).unwrap();
        prover_transcript.absorb(label::M31_CIRCLE_C2_ROOT, &[0x41; 32]);
        let mut verifier_transcript = prover_transcript.clone();
        let masks: PaymentSumcheckMaskPolynomials = core::array::from_fn(|round| {
            core::array::from_fn(|coefficient| QM31 {
                c0: CM31::new(
                    M31(701 + round as u32 * 31 + coefficient as u32 * 7),
                    M31(809 + round as u32 * 37 + coefficient as u32 * 11),
                ),
                c1: CM31::new(
                    M31(907 + round as u32 * 41 + coefficient as u32 * 13),
                    M31(1_009 + round as u32 * 43 + coefficient as u32 * 17),
                ),
            })
        });
        let proof = prove_spend_payment_zerocheck_hiding(
            &mut prover_transcript,
            &public,
            &trace,
            &helpers,
            lambda,
            chi,
            &masks,
        )
        .unwrap();

        let verifier_batching = begin_payment_zerocheck(&mut verifier_transcript).unwrap();
        assert_eq!(verifier_batching, proof.batching);
        let verifier_eta = begin_payment_hiding_sumcheck(
            &mut verifier_transcript,
            proof.sumcheck.initial_mask_claim,
        )
        .unwrap();
        assert_eq!(verifier_eta, proof.sumcheck.eta);
        let verified = verify_payment_sumcheck_messages_from_claim(
            &mut verifier_transcript,
            &proof.sumcheck.messages,
            proof.sumcheck.initial_mask_claim,
        )
        .unwrap();
        assert_eq!(verified.point, proof.sumcheck.challenges);
        assert_eq!(
            verified.terminal_claim,
            proof.sumcheck.masked_terminal_claim
        );

        let openings = trace_openings_at_point(&trace, &helpers, &verified.point).unwrap();
        let original_terminal = payment_terminal_value(
            &public,
            &openings,
            &verified.point,
            &verifier_batching,
            lambda,
            chi,
        )
        .unwrap();
        assert_eq!(original_terminal, proof.sumcheck.original_terminal_claim);
        assert_eq!(
            verified.terminal_claim,
            proof
                .sumcheck
                .terminal_mask_claim
                .add(verifier_eta.mul(original_terminal))
        );
        assert_ne!(verified.terminal_claim, original_terminal);
    }

    #[test]
    fn direct_range_committed_mask_roundtrips_with_no_free_terminal_scalar() {
        let (public, witness) = spend_fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        apply_direct_range_witness_v4(&mut trace).unwrap();
        let c1_masks = (0..direct_range_c1_mask_cells_v4().len())
            .map(|index| {
                M31(
                    ((index as u64 * 2_246_822_519 + 0x5a17) % u64::from(aspis_core::field::P))
                        as u32,
                )
            })
            .collect::<Vec<_>>();
        apply_direct_range_c1_masks_v4(&mut trace, &c1_masks).unwrap();

        let mut prover_transcript = Transcript::new(HOST_HASH);
        prover_transcript.absorb(label::STATEMENT, &[0x71; 32]);
        prover_transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &[0x51; 33]);
        let lambda = prover_transcript.challenge_qm31().unwrap();
        let chi = prover_transcript.challenge_qm31().unwrap();
        let helper_masks = (0..COPY_HELPER_MASK_VARIABLES)
            .map(|index| QM31 {
                c0: CM31::new(M31(11 + index as u32 * 3), M31(13 + index as u32 * 5)),
                c1: CM31::new(M31(17 + index as u32 * 7), M31(19 + index as u32 * 11)),
            })
            .collect::<Vec<_>>();
        let payment_mask = (0..PAYMENT_MASK_ORACLE_VALUES)
            .map(|index| QM31 {
                c0: CM31::new(M31(101 + index as u32 * 13), M31(103 + index as u32 * 17)),
                c1: CM31::new(M31(107 + index as u32 * 19), M31(109 + index as u32 * 23)),
            })
            .collect::<Vec<_>>();
        let helpers =
            build_direct_range_hiding_helpers_v4(&trace, lambda, chi, &helper_masks, &payment_mask)
                .unwrap();
        let theta_probe = QM31 {
            c0: CM31::new(M31(4_001), M31(4_003)),
            c1: CM31::new(M31(4_007), M31(4_009)),
        };
        let table =
            direct_range_hiding_composition_table(&public, &trace, &helpers, chi, theta_probe)
                .unwrap();
        assert!(table.iter().all(|value| *value == QM31::ZERO));
        for row in [0usize, 784, 785, 864, 865, 866, 1_023] {
            let point = core::array::from_fn(|coordinate| {
                if (row >> (9 - coordinate)) & 1 == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            });
            let openings =
                direct_range_hiding_trace_openings_at_point(&trace, &helpers, &point).unwrap();
            assert_eq!(
                evaluate_direct_range_hiding_constraint_point(
                    &public,
                    &openings.constraint_openings(),
                    &point,
                    lambda,
                    chi,
                    theta_probe,
                )
                .unwrap(),
                table[row],
                "direct-range terminal mismatch at Boolean row {row}",
            );
        }
        prover_transcript.absorb(label::M31_CIRCLE_C2_ROOT, &[0x61; 32]);
        let mut verifier_transcript = prover_transcript.clone();

        let proof = prove_spend_payment_zerocheck_committed_hiding(
            &mut prover_transcript,
            &public,
            &trace,
            &helpers,
            lambda,
            chi,
        )
        .unwrap();

        let verifier_batching = begin_payment_zerocheck(&mut verifier_transcript).unwrap();
        assert_eq!(verifier_batching, proof.batching);
        let verifier_eta =
            begin_payment_hiding_sumcheck(&mut verifier_transcript, proof.initial_mask_claim)
                .unwrap();
        assert_eq!(verifier_eta, proof.eta);
        let verified = verify_payment_sumcheck_messages_from_claim(
            &mut verifier_transcript,
            &proof.sumcheck.messages,
            proof.initial_mask_claim,
        )
        .unwrap();
        assert_eq!(verified.point, proof.sumcheck.challenges);
        let openings =
            direct_range_hiding_trace_openings_at_point(&trace, &helpers, &verified.point).unwrap();
        assert_eq!(
            direct_range_hiding_masked_terminal_value(
                &public,
                &openings,
                &verified.point,
                &verifier_batching,
                lambda,
                chi,
                verifier_eta,
            )
            .unwrap(),
            verified.terminal_claim,
        );
        assert_eq!(verified.terminal_claim, proof.sumcheck.terminal_claim);
    }

    #[test]
    fn randomized_direct_range_table_and_terminal_sumcheck_roundtrip() {
        let (public, witness) = spend_fixture();
        for seed in [31u32, 73] {
            let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
            apply_direct_range_witness_v4(&mut trace).unwrap();
            trace.c1[0][aspis_statement::DIRECT_RANGE_BIT_ROW_START] = M31(seed % 7 + 2);
            let q = |offset: u32| QM31 {
                c0: CM31::new(M31(seed * 1_003 + offset), M31(seed * 1_009 + offset + 1)),
                c1: CM31::new(
                    M31(seed * 1_021 + offset + 2),
                    M31(seed * 1_031 + offset + 3),
                ),
            };
            let lambda = q(101);
            let chi = q(211);
            let theta = q(307);
            let helper_masks = vec![QM31::ZERO; COPY_HELPER_MASK_VARIABLES];
            let payment_mask = vec![QM31::ZERO; PAYMENT_MASK_ORACLE_VALUES];
            let helpers = build_direct_range_hiding_helpers_v4(
                &trace,
                lambda,
                chi,
                &helper_masks,
                &payment_mask,
            )
            .unwrap();
            let table =
                direct_range_hiding_composition_table(&public, &trace, &helpers, chi, theta)
                    .unwrap();
            let initial_claim = table.iter().copied().fold(QM31::ZERO, QM31::add);
            assert_ne!(initial_claim, QM31::ZERO);

            let mut prover_transcript = Transcript::new(HOST_HASH);
            prover_transcript.absorb(label::STATEMENT, &[seed as u8; 32]);
            let mut verifier_transcript = prover_transcript.clone();
            let proof = prove_payment_sumcheck_from_claim(
                &mut prover_transcript,
                |point| {
                    let openings =
                        direct_range_hiding_trace_openings_at_point(&trace, &helpers, point)
                            .ok_or(ConstraintBuildError::Shape)?;
                    evaluate_direct_range_hiding_constraint_point(
                        &public,
                        &openings.constraint_openings(),
                        point,
                        lambda,
                        chi,
                        theta,
                    )
                },
                initial_claim,
            )
            .unwrap();
            let verified = verify_payment_sumcheck_messages_from_claim(
                &mut verifier_transcript,
                &proof.messages,
                initial_claim,
            )
            .unwrap();
            assert_eq!(verified.point, proof.challenges);
            let openings =
                direct_range_hiding_trace_openings_at_point(&trace, &helpers, &verified.point)
                    .unwrap();
            assert_eq!(
                evaluate_direct_range_hiding_constraint_point(
                    &public,
                    &openings.constraint_openings(),
                    &verified.point,
                    lambda,
                    chi,
                    theta,
                )
                .unwrap(),
                verified.terminal_claim,
            );
        }
    }
}
