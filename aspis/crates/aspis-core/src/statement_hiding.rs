//! Algebraic masking kernel for the degree-10 payment sumcheck.
//!
//! This module only provides the exact affine rewrite. A verifier must not
//! accept it without a separate proof binding the terminal mask contribution
//! to the committed mask/witness oracle.

use alloc::{vec, vec::Vec};

use crate::circle_fri::{
    evaluate_final_line_tensor, normalized_circle_to_line_arity4_prepared_multipliers,
    normalized_line_arity4_prepared_multipliers,
};
use crate::field::{qm31_dot, PreparedQm31Multiplier, CM31, M31, P, QM31};
use crate::merkle::{leaf_hash, node_hash4};
use crate::statement_sumcheck::{
    begin_payment_zerocheck, boundary_sum, evaluate, verify_payment_sumcheck_messages_from_claim,
    PaymentSumcheckFullPolynomial, PaymentSumcheckWirePolynomial,
    PAYMENT_SUMCHECK_FULL_COEFFICIENTS, PAYMENT_SUMCHECK_ROUNDS,
};
use crate::sumcheck::WeightAccumulator;
use crate::transcript::{label, ChallengeSampleExhausted, Transcript};
use crate::HashFn;

pub const PAYMENT_SUMCHECK_MASK_COEFFICIENTS: usize = PAYMENT_SUMCHECK_FULL_COEFFICIENTS;
pub const PAYMENT_SUMCHECK_MASK_RANDOMNESS: usize =
    PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_MASK_COEFFICIENTS;
pub const PAYMENT_HIDING_CHALLENGE_RETRY_LIMIT: usize = 3;
pub const PAYMENT_MASKING_FACTOR_DEGREE: usize = 9;
pub const PAYMENT_MASK_ORACLE_COUNT: usize = 6;
pub const PAYMENT_MASK_ORACLE_SIZE: usize = 1usize << PAYMENT_SUMCHECK_ROUNDS;
pub const PAYMENT_HIDING_PLACEMENT_QUERY_COUNT: usize = 36;
pub const PAYMENT_HIDING_IN_BATCH_LEAF_BYTES: usize = 7 * 4 * 16;
pub const PAYMENT_HIDING_SEPARATE_H1_LEAF_BYTES: usize = 4 * 16;
pub const PAYMENT_HIDING_SEPARATE_MASK_LEAF_BYTES: usize = 6 * 4 * 16;
pub const PAYMENT_SPARSE_MASK_C1_COLUMNS: usize = 49;
pub const PAYMENT_SPARSE_MASK_TOTAL_COLUMNS: usize = PAYMENT_SPARSE_MASK_C1_COLUMNS + 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentSparseMaskFactors {
    pub c1: [QM31; PAYMENT_SPARSE_MASK_C1_COLUMNS],
    pub explicit: QM31,
}

fn sparse_mask_linear(family: usize, point: &[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            let scalar = 3 + 22 * variable + family * (17 + 8 * variable);
            sum.add(value.mul_m31(M31(scalar as u32)))
        })
}

fn sparse_mask_power(linear: QM31, exponent: usize) -> QM31 {
    (0..exponent).fold(QM31::ONE, |power, _| power.mul(linear))
}

fn sparse_mask_tower_basis(coordinate: usize) -> QM31 {
    match coordinate {
        0 => QM31::ONE,
        1 => QM31 {
            c0: CM31::new(M31::ZERO, M31::ONE),
            c1: CM31::ZERO,
        },
        2 => QM31 {
            c0: CM31::ZERO,
            c1: CM31::ONE,
        },
        3 => QM31 {
            c0: CM31::ZERO,
            c1: CM31::new(M31::ZERO, M31::ONE),
        },
        _ => unreachable!(),
    }
}

#[inline(always)]
fn sparse_mask_mul_non_residue(value: CM31) -> CM31 {
    // (2+i)(a+bi) = (2a-b) + (a+2b)i.
    CM31::new(value.a.double().sub(value.b), value.a.add(value.b.double()))
}

/// Multiply by one of `(1, i, u, iu)` using only additions, negations and
/// coordinate moves. This is the same tower action as
/// `sparse_mask_tower_basis(coordinate).mul(value)`, without a generic QM31
/// multiplication.
#[inline(always)]
fn sparse_mask_mul_tower_basis(value: QM31, coordinate: usize) -> QM31 {
    match coordinate {
        0 => value,
        1 => QM31 {
            c0: value.c0.mul_i(),
            c1: value.c1.mul_i(),
        },
        2 => QM31 {
            c0: sparse_mask_mul_non_residue(value.c1),
            c1: value.c0,
        },
        3 => QM31 {
            c0: sparse_mask_mul_non_residue(value.c1).mul_i(),
            c1: value.c0.mul_i(),
        },
        _ => unreachable!(),
    }
}

#[inline(always)]
fn sparse_mask_pack_group(c1: &[QM31; PAYMENT_SPARSE_MASK_C1_COLUMNS], group: usize) -> QM31 {
    let start = group * 4;
    let end = core::cmp::min(start + 4, PAYMENT_SPARSE_MASK_C1_COLUMNS);
    c1[start..end]
        .iter()
        .copied()
        .enumerate()
        .fold(QM31::ZERO, |packed, (coordinate, value)| {
            packed.add(sparse_mask_mul_tower_basis(value, coordinate))
        })
}

#[inline(always)]
fn sparse_mask_linears(point: &[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> [QM31; 4] {
    // L_f = L_0 + f*D, where the coefficient of x_v in L_0 is 3+22v and
    // the coefficient in D is 17+8v. Computing the two scalar dots once is
    // exactly equivalent to four independent linear-form evaluations.
    let (base, delta) = point.iter().copied().enumerate().fold(
        (QM31::ZERO, QM31::ZERO),
        |(base, delta), (variable, value)| {
            (
                base.add(value.mul_m31(M31((3 + 22 * variable) as u32))),
                delta.add(value.mul_m31(M31((17 + 8 * variable) as u32))),
            )
        },
    );
    let family1 = base.add(delta);
    let family2 = family1.add(delta);
    let family3 = family2.add(delta);
    [base, family1, family2, family3]
}

/// Return `(L^2, L^4, L^5, L^6, L^9)` with one shared addition chain.
#[inline(always)]
fn sparse_mask_shared_powers(linear: QM31) -> [QM31; 5] {
    let power2 = linear.square();
    let power4 = power2.square();
    let power5 = power4.mul(linear);
    let power6 = power4.mul(power2);
    let power8 = power4.square();
    let power9 = power8.mul(linear);
    [power2, power4, power5, power6, power9]
}

/// Fixed degree-nine-or-less factors for the one-mask+C1-padding profile.
/// The schedule is frozen by the profile identifier and its layout
/// fingerprint; changing it is a protocol change, not an implementation
/// detail.
pub fn payment_sparse_mask_factors(
    point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> PaymentSparseMaskFactors {
    const EXPONENTS: [[usize; 5]; 3] = [[0, 2, 4, 6, 9], [0, 2, 4, 6, 9], [9, 0, 5, 0, 0]];
    let linears = core::array::from_fn::<_, 4, _>(|family| sparse_mask_linear(family, point));
    let c1 = core::array::from_fn(|column| {
        let group = column / 4;
        let family = group / 5;
        let exponent = EXPONENTS[family][group % 5];
        sparse_mask_tower_basis(column % 4).mul(sparse_mask_power(linears[family], exponent))
    });
    PaymentSparseMaskFactors {
        c1,
        explicit: QM31::ONE.add(sparse_mask_power(linears[3], 9)),
    }
}

/// Evaluate the exact degree-ten mask polynomial from the already committed
/// 49 C1 evaluations and one explicit QM31 mask evaluation.
pub fn payment_sparse_mask_value_with_factors(
    c1: &[QM31; PAYMENT_SPARSE_MASK_C1_COLUMNS],
    explicit_mask: QM31,
    factors: &PaymentSparseMaskFactors,
) -> QM31 {
    c1.iter()
        .copied()
        .zip(factors.c1)
        .fold(QM31::ZERO, |sum, (value, factor)| {
            sum.add(factor.mul(value))
        })
        .add(factors.explicit.mul(explicit_mask))
}

pub fn payment_sparse_mask_value(
    c1: &[QM31; PAYMENT_SPARSE_MASK_C1_COLUMNS],
    explicit_mask: QM31,
    point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> QM31 {
    let linears = sparse_mask_linears(point);
    let family0 = sparse_mask_shared_powers(linears[0]);
    let family1 = sparse_mask_shared_powers(linears[1]);
    let family2 = sparse_mask_shared_powers(linears[2]);
    let family3 = sparse_mask_shared_powers(linears[3]);

    // Regroup four adjacent C1 columns before multiplying by their shared
    // power. Commutativity gives
    //   sum_c basis(c) * L^e * C[4g+c]
    // = L^e * sum_c basis(c) * C[4g+c].
    // The three exponent-zero groups and the explicit mask's constant term
    // are additions. The remaining eleven products use the exact lazy dot
    // kernel, reducing four product channels at a time.
    let weights = [
        family0[0], family0[1], family0[3], family0[4], family1[0], family1[1], family1[3],
        family1[4], family2[4], family2[2], family3[4],
    ];
    let values = [
        sparse_mask_pack_group(c1, 1),
        sparse_mask_pack_group(c1, 2),
        sparse_mask_pack_group(c1, 3),
        sparse_mask_pack_group(c1, 4),
        sparse_mask_pack_group(c1, 6),
        sparse_mask_pack_group(c1, 7),
        sparse_mask_pack_group(c1, 8),
        sparse_mask_pack_group(c1, 9),
        sparse_mask_pack_group(c1, 10),
        sparse_mask_pack_group(c1, 12),
        explicit_mask,
    ];
    sparse_mask_pack_group(c1, 0)
        .add(sparse_mask_pack_group(c1, 5))
        .add(sparse_mask_pack_group(c1, 11))
        .add(explicit_mask)
        .add(qm31_dot(&weights, &values))
}

pub type PaymentSumcheckMaskPolynomial = [QM31; PAYMENT_SUMCHECK_MASK_COEFFICIENTS];
pub type PaymentSumcheckMaskPolynomials = [PaymentSumcheckMaskPolynomial; PAYMENT_SUMCHECK_ROUNDS];

/// Bind the mask-oracle algebra and sample its nonzero powers-generator
/// challenge after every mask root has entered the transcript.
pub fn begin_payment_mask_oracles(
    transcript: &mut Transcript,
) -> Result<QM31, ChallengeSampleExhausted> {
    transcript.absorb(
        label::M31_PAYMENT_HIDING_MASK_ORACLES,
        &[
            PAYMENT_MASK_ORACLE_COUNT as u8,
            PAYMENT_MASKING_FACTOR_DEGREE as u8,
            PAYMENT_SUMCHECK_ROUNDS as u8,
        ],
    );
    for _ in 0..PAYMENT_HIDING_CHALLENGE_RETRY_LIMIT {
        let kappa = transcript.challenge_qm31()?;
        if kappa != QM31::ZERO {
            return Ok(kappa);
        }
    }
    Err(ChallengeSampleExhausted)
}

pub fn begin_payment_mask_delta(
    transcript: &mut Transcript,
) -> Result<QM31, ChallengeSampleExhausted> {
    transcript.absorb(
        label::M31_PAYMENT_HIDING_MASK_DELTA,
        &[PAYMENT_MASK_ORACLE_COUNT as u8],
    );
    for _ in 0..PAYMENT_HIDING_CHALLENGE_RETRY_LIMIT {
        let delta = transcript.challenge_qm31()?;
        if delta != QM31::ZERO {
            return Ok(delta);
        }
    }
    Err(ChallengeSampleExhausted)
}

/// Bind `(A_delta(z), H_z(z), A_delta(xor11(z)), H_z(xor11(z)))`, then
/// derive the nonzero merge coefficient tau and the outer PCS gamma.
pub fn finish_payment_mask_column_batching(
    transcript: &mut Transcript,
    aggregates: &[QM31; 4],
) -> Result<(QM31, QM31), ChallengeSampleExhausted> {
    let mut bytes = [0u8; 4 * 16];
    for (index, value) in aggregates.iter().enumerate() {
        value.write_le_bytes(&mut bytes[index * 16..][..16]);
    }
    transcript.absorb(label::M31_PAYMENT_HIDING_MASK_AGGREGATES, &bytes);
    let mut tau = None;
    for _ in 0..PAYMENT_HIDING_CHALLENGE_RETRY_LIMIT {
        let candidate = transcript.challenge_qm31()?;
        if candidate != QM31::ZERO {
            tau = Some(candidate);
            break;
        }
    }
    let tau = tau.ok_or(ChallengeSampleExhausted)?;
    let gamma = transcript.challenge_qm31()?;
    Ok((tau, gamma))
}

/// Fixed public degree-nine factor used by the committed-oracle hiding path.
///
/// The factor is a degree-nine polynomial of a full linear form in all ten
/// variables. Multiplying it by a committed multilinear mask oracle therefore
/// has individual degree at most ten, while exposing only the single bound
/// terminal value `G(z) * S(z)`.
///
/// The concrete coefficients are protocol constants, not prover choices.
/// The accompanying rank test is the guard that this structured factor masks
/// the complete degree-ten wire rather than only its linear part.
pub fn payment_masking_factor(point: &[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> QM31 {
    payment_masking_factor_for_oracle(0, point)
}

/// Degree-nine factor for one of the independently committed mask oracles.
/// Five is the naive final-round dimension lower bound: a
/// multilinear oracle supplies only two fresh univariate coefficients after
/// nine sumcheck challenges, while the wire exposes ten coefficients. The
/// preceding running claim consumes one combination, so the exact rank guard
/// below requires six.
pub fn payment_masking_factor_for_oracle(
    oracle: usize,
    point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> QM31 {
    assert!(oracle < PAYMENT_MASK_ORACLE_COUNT);
    let linear = point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            let scalar = 3 + variable * 22;
            sum.add(value.mul_m31(M31(scalar as u32)))
        });
    if oracle < 5 {
        let even_power = (0..2 * oracle).fold(QM31::ONE, |power, _| power.mul(linear));
        even_power.mul(QM31::ONE.add(linear))
    } else {
        QM31::ONE.add(linear.square())
    }
}

/// Evaluate all six factors with one linear form and one `L^0..L^9` ladder.
/// This is the verifier path; repeated single-factor evaluation is retained
/// only as a small reference API.
pub fn payment_masking_factors(
    point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> [QM31; PAYMENT_MASK_ORACLE_COUNT] {
    let linear = point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            sum.add(value.mul_m31(M31((3 + variable * 22) as u32)))
        });
    let mut powers = [QM31::ONE; PAYMENT_MASKING_FACTOR_DEGREE + 1];
    for degree in 1..powers.len() {
        powers[degree] = powers[degree - 1].mul(linear);
    }
    [
        powers[0].add(powers[1]),
        powers[2].add(powers[3]),
        powers[4].add(powers[5]),
        powers[6].add(powers[7]),
        powers[8].add(powers[9]),
        QM31::ONE.add(powers[2]),
    ]
}

/// Evaluate the degree-ten committed-oracle mask `G(x) * S(x)`.
pub fn payment_masking_oracle_value(
    mask_mle: QM31,
    point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> QM31 {
    mask_mle.mul(payment_masking_factor(point))
}

/// Factor-weighted terminal of all six committed mask oracles. A production
/// proof exposes and binds only this aggregate, never the six evaluations
/// individually.
pub fn payment_masking_oracles_value(
    mask_mles: &[QM31; PAYMENT_MASK_ORACLE_COUNT],
    point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> QM31 {
    payment_masking_oracles_value_with_kappa(mask_mles, point, QM31::ONE)
}

pub fn payment_masking_oracles_value_with_kappa(
    mask_mles: &[QM31; PAYMENT_MASK_ORACLE_COUNT],
    point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
    kappa: QM31,
) -> QM31 {
    payment_masking_oracles_value_with_factors(mask_mles, &payment_masking_factors(point), kappa)
}

pub fn payment_masking_oracles_value_with_factors(
    mask_mles: &[QM31; PAYMENT_MASK_ORACLE_COUNT],
    factors: &[QM31; PAYMENT_MASK_ORACLE_COUNT],
    kappa: QM31,
) -> QM31 {
    let mut kappa_power = QM31::ONE;
    mask_mles
        .iter()
        .copied()
        .enumerate()
        .fold(QM31::ZERO, |sum, (oracle, value)| {
            let contribution = value.mul(factors[oracle]).mul(kappa_power);
            kappa_power = kappa_power.mul(kappa);
            sum.add(contribution)
        })
}

/// Inner six-column weights for the selected single-codeword construction.
/// `delta^k` binds the ordinary mask-column evaluation aggregate and
/// `tau * kappa^k * S_k(z)` binds the masked-sumcheck terminal in the same
/// codeword. The result enters the existing outer PCS lane under one
/// `gamma^50` coefficient.
pub fn payment_masking_merged_lane_weights(
    delta: QM31,
    tau: QM31,
    kappa: QM31,
    z: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> [QM31; PAYMENT_MASK_ORACLE_COUNT] {
    payment_masking_merged_lane_weights_with_factors(delta, tau, kappa, &payment_masking_factors(z))
}

pub fn payment_masking_merged_lane_weights_with_factors(
    delta: QM31,
    tau: QM31,
    kappa: QM31,
    factors: &[QM31; PAYMENT_MASK_ORACLE_COUNT],
) -> [QM31; PAYMENT_MASK_ORACLE_COUNT] {
    let mut delta_power = QM31::ONE;
    let mut kappa_power = QM31::ONE;
    core::array::from_fn(|oracle| {
        let terminal = kappa_power.mul(factors[oracle]);
        let weight = delta_power.add(tau.mul(terminal));
        delta_power = delta_power.mul(delta);
        kappa_power = kappa_power.mul(kappa);
        weight
    })
}

pub fn payment_masking_delta_aggregate(
    mask_mles: &[QM31; PAYMENT_MASK_ORACLE_COUNT],
    delta: QM31,
) -> QM31 {
    let mut power = QM31::ONE;
    mask_mles.iter().copied().fold(QM31::ZERO, |sum, value| {
        let contribution = power.mul(value);
        power = power.mul(delta);
        sum.add(contribution)
    })
}

pub fn payment_masking_merged_aggregate(
    mask_mles: &[QM31; PAYMENT_MASK_ORACLE_COUNT],
    delta: QM31,
    tau: QM31,
    kappa: QM31,
    factor_point: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> QM31 {
    let weights = payment_masking_merged_lane_weights(delta, tau, kappa, factor_point);
    mask_mles
        .iter()
        .copied()
        .zip(weights)
        .fold(QM31::ZERO, |sum, (value, weight)| {
            sum.add(weight.mul(value))
        })
}

/// Public initial sum of the committed masking polynomial `G(x)S(x)` over
/// the Boolean cube. Revealing this one linear form is part of the masking
/// transcript; the remaining oracle entropy masks the round messages.
pub fn payment_masking_initial_claim(mask: &[QM31]) -> Option<QM31> {
    if mask.len() != PAYMENT_MASK_ORACLE_SIZE {
        return None;
    }
    Some(
        mask.iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |sum, (row, value)| {
                let point = core::array::from_fn(|coordinate| {
                    let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                    if bit == 0 {
                        QM31::ZERO
                    } else {
                        QM31::ONE
                    }
                });
                sum.add(value.mul(payment_masking_factor(&point)))
            }),
    )
}

/// Initial Boolean-cube sum for all committed mask oracles.
pub fn payment_masking_initial_claims(
    masks: &[&[QM31]; PAYMENT_MASK_ORACLE_COUNT],
) -> Option<QM31> {
    payment_masking_initial_claims_with_kappa(masks, QM31::ONE)
}

pub fn payment_masking_initial_claims_with_kappa(
    masks: &[&[QM31]; PAYMENT_MASK_ORACLE_COUNT],
    kappa: QM31,
) -> Option<QM31> {
    let mut total = QM31::ZERO;
    let mut kappa_power = QM31::ONE;
    for (oracle, mask) in masks.iter().enumerate() {
        if mask.len() != PAYMENT_MASK_ORACLE_SIZE {
            return None;
        }
        for (row, value) in mask.iter().copied().enumerate() {
            let point = core::array::from_fn(|coordinate| {
                let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                if bit == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            });
            total = total.add(
                value
                    .mul(payment_masking_factor_for_oracle(oracle, &point))
                    .mul(kappa_power),
            );
        }
        kappa_power = kappa_power.mul(kappa);
    }
    Some(total)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentHidingPlacement {
    InBatch,
    SeparateCommitment,
}

/// Measurement-only verifier kernel for the C2 placement fork. It prices the
/// same six-mask transcript and RLC in both modes, then hashes either one
/// 448-byte q36 leaf/tree or separate 64-byte and 384-byte q36 leaf/trees.
/// The aggregate mask fold relation is intentionally excluded because it is
/// common to both placements and receives its own measurement line.
pub fn payment_hiding_placement_probe(
    hash: HashFn,
    placement: PaymentHidingPlacement,
) -> Result<QM31, ChallengeSampleExhausted> {
    let q = |seed: u32| QM31 {
        c0: CM31::new(M31(seed), M31(seed + 1)),
        c1: CM31::new(M31(seed + 2), M31(seed + 3)),
    };
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::STATEMENT, &[0x91; 32]);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &[0xa1; 33]);
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &[0xb1; 32]);
    let batching = begin_payment_zerocheck(&mut transcript)?;
    let kappa = begin_payment_mask_oracles(&mut transcript)?;
    let delta = begin_payment_mask_delta(&mut transcript)?;
    let initial_claim = q(1_001);
    let eta = begin_payment_hiding_sumcheck(&mut transcript, initial_claim)?;
    let messages: [PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS] =
        core::array::from_fn(|round| {
            core::array::from_fn(|coefficient| {
                q(2_001 + round as u32 * 401 + coefficient as u32 * 37)
            })
        });
    let verified =
        verify_payment_sumcheck_messages_from_claim(&mut transcript, &messages, initial_claim)?;

    let mut sink = verified
        .terminal_claim
        .add(batching.theta)
        .add(kappa)
        .add(delta)
        .add(eta);
    let mask_openings = core::array::from_fn(|oracle| q(10_001 + oracle as u32 * 101));
    let shifted_mask_openings = core::array::from_fn(|oracle| q(11_001 + oracle as u32 * 103));
    let factors = payment_masking_factors(&verified.point);
    let h_z = payment_masking_oracles_value_with_factors(&mask_openings, &factors, kappa);
    let h_z_xor = (0..PAYMENT_MASK_ORACLE_COUNT).fold(QM31::ZERO, |sum, oracle| {
        let kappa_power = (0..oracle).fold(QM31::ONE, |power, _| power.mul(kappa));
        sum.add(
            shifted_mask_openings[oracle]
                .mul(kappa_power)
                .mul(factors[oracle]),
        )
    });
    let aggregates = [
        payment_masking_delta_aggregate(&mask_openings, delta),
        h_z,
        payment_masking_delta_aggregate(&shifted_mask_openings, delta),
        h_z_xor,
    ];
    let (tau, gamma) = finish_payment_mask_column_batching(&mut transcript, &aggregates)?;
    sink = aggregates
        .into_iter()
        .fold(sink.add(tau).add(gamma), QM31::add);

    let inner_weights =
        payment_masking_merged_lane_weights_with_factors(delta, tau, kappa, &factors)
            .map(PreparedQm31Multiplier::new);
    let gamma_49 = (0..49).fold(QM31::ONE, |power, _| power.mul(gamma));
    let gamma_50 = gamma_49.mul(gamma);
    let gamma_49 = PreparedQm31Multiplier::new(gamma_49);
    let gamma_50 = PreparedQm31Multiplier::new(gamma_50);
    for query in 0..PAYMENT_HIDING_PLACEMENT_QUERY_COUNT {
        for slot in 0..4usize {
            let h1 = q(30_001 + query as u32 * 101 + slot as u32 * 11);
            let inner = (0..PAYMENT_MASK_ORACLE_COUNT).fold(QM31::ZERO, |sum, oracle| {
                let value =
                    q(40_001 + oracle as u32 * 10_007 + query as u32 * 101 + slot as u32 * 11);
                sum.add(inner_weights[oracle].mul(value))
            });
            sink = sink.add(gamma_49.mul(h1)).add(gamma_50.mul(inner));
        }
    }

    fn absorb_digest(sink: &mut QM31, digest: [u8; 32]) {
        for chunk in digest.chunks_exact(4) {
            let raw = u32::from_le_bytes(chunk.try_into().unwrap());
            *sink = sink.add(QM31::from_cm31(CM31::from_m31(M31(
                (u64::from(raw) % u64::from(P)) as u32,
            ))));
        }
    }

    fn authenticate_tree_shape(hash: HashFn, tag: u8, leaf_bytes: usize, sink: &mut QM31) {
        let mut leaf = vec![0u8; leaf_bytes];
        let mut indices = (0..PAYMENT_HIDING_PLACEMENT_QUERY_COUNT)
            .map(|query| ((query * 109 + 17) & 4095) as u32)
            .collect::<Vec<_>>();
        indices.sort_unstable();
        indices.dedup();
        let mut rolling = [[0u8; 32]; 4];
        for (ordinal, index) in indices.iter().copied().enumerate() {
            leaf[0..4].copy_from_slice(&index.to_le_bytes());
            let digest = leaf_hash(hash, tag, &leaf);
            rolling[ordinal & 3] = digest;
            absorb_digest(sink, digest);
        }
        for _level in 0..6u8 {
            let mut parents = indices.iter().map(|index| index >> 2).collect::<Vec<_>>();
            parents.sort_unstable();
            parents.dedup();
            for (ordinal, parent) in parents.iter().copied().enumerate() {
                rolling[(ordinal + 1) & 3][0..4].copy_from_slice(&parent.to_le_bytes());
                let digest = node_hash4(hash, &rolling);
                rolling[ordinal & 3] = digest;
                absorb_digest(sink, digest);
            }
            indices = parents;
        }
    }

    match placement {
        PaymentHidingPlacement::InBatch => {
            authenticate_tree_shape(hash, 0xd0, PAYMENT_HIDING_IN_BATCH_LEAF_BYTES, &mut sink)
        }
        PaymentHidingPlacement::SeparateCommitment => {
            authenticate_tree_shape(hash, 0xd0, PAYMENT_HIDING_SEPARATE_H1_LEAF_BYTES, &mut sink);
            authenticate_tree_shape(
                hash,
                0xd1,
                PAYMENT_HIDING_SEPARATE_MASK_LEAF_BYTES,
                &mut sink,
            );
        }
    }
    Ok(sink)
}

/// Measurement-only common mask-aggregate relation. This is the work both
/// placement rows still need after the six mask leaves are authenticated:
/// one point/OOD relation, six-column layer-zero aggregation, four prepared
/// folds, and three later-layer radix-4 trees at q36/rate-1/16.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentHidingAggregatePhase {
    EmptyControl,
    Relation,
    Layer0,
    LaterFolds,
    LaterMerkle,
    Full,
}

pub fn payment_hiding_aggregate_relation_probe(
    hash: HashFn,
) -> Result<QM31, ChallengeSampleExhausted> {
    payment_hiding_aggregate_relation_probe_phase(hash, PaymentHidingAggregatePhase::Full)
}

pub fn payment_hiding_aggregate_relation_probe_phase(
    hash: HashFn,
    phase: PaymentHidingAggregatePhase,
) -> Result<QM31, ChallengeSampleExhausted> {
    let q = |seed: u32| QM31 {
        c0: CM31::new(M31(seed), M31(seed + 1)),
        c1: CM31::new(M31(seed + 2), M31(seed + 3)),
    };
    let z = core::array::from_fn(|coordinate| q(40_001 + coordinate as u32 * 101));
    let kappa = q(41_003);
    let lane_weights: [QM31; PAYMENT_MASK_ORACLE_COUNT] = core::array::from_fn(|oracle| {
        let kappa_power = (0..oracle).fold(QM31::ONE, |power, _| power.mul(kappa));
        kappa_power.mul(payment_masking_factor_for_oracle(oracle, &z))
    });
    let alphas = [q(42_001), q(42_101), q(42_201), q(42_301)];
    let alpha_prepared = alphas.map(PreparedQm31Multiplier::new);
    let alpha_squared_prepared = alphas.map(QM31::square).map(PreparedQm31Multiplier::new);
    let prepared_lane_weights = lane_weights.map(PreparedQm31Multiplier::new);
    let base_indices = (0..PAYMENT_HIDING_PLACEMENT_QUERY_COUNT)
        .map(|query| ((query * 109 + 17) & 4095) as u32)
        .collect::<Vec<_>>();
    let final_coefficients = [q(49_001), q(49_101), q(49_201), q(49_301)];
    let mut sink = q(43_001);

    if matches!(
        phase,
        PaymentHidingAggregatePhase::Relation | PaymentHidingAggregatePhase::Full
    ) {
        let mut transcript = Transcript::new(hash);
        transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &[0x31; 320]);
        transcript.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, &[0x41; 16]);
        let mut relation_weights = WeightAccumulator::empty(10);
        relation_weights
            .add_multilinear(QM31::ONE, Vec::from(z))
            .map_err(|_| ChallengeSampleExhausted)?;
        let mut running_claim = q(43_101);
        for round in 0..4usize {
            for sample in 0..2usize {
                let mix = q(44_001 + round as u32 * 1_003 + sample as u32 * 101);
                let value = q(45_001 + round as u32 * 1_009 + sample as u32 * 103);
                let mut encoded = [0u8; 18];
                encoded[0] = round as u8;
                encoded[1] = sample as u8;
                value.write_le_bytes(&mut encoded[2..]);
                transcript.absorb(
                    if round == 0 {
                        label::M31_CIRCLE_OOD_VALUE
                    } else {
                        label::M31_LINE_OOD_VALUE
                    },
                    &encoded,
                );
                if round == 0 {
                    relation_weights
                        .add_circle_tensor(
                            mix,
                            crate::circle::SecureCirclePoint {
                                x: q(46_001 + sample as u32 * 211),
                                y: q(46_101 + sample as u32 * 223),
                            },
                        )
                        .map_err(|_| ChallengeSampleExhausted)?;
                } else {
                    relation_weights
                        .add_line_tensor(mix, q(47_001 + round as u32 * 307 + sample as u32 * 109))
                        .map_err(|_| ChallengeSampleExhausted)?;
                }
                running_claim = running_claim.add(mix.mul(value));
            }
            let polynomial: crate::sumcheck::SumcheckPolynomial =
                core::array::from_fn(|coefficient| {
                    q(48_001 + round as u32 * 2_003 + coefficient as u32 * 131)
                });
            let mut encoded = [0u8; 1 + 7 * 16];
            encoded[0] = round as u8;
            for (coefficient, value) in polynomial.iter().enumerate() {
                value.write_le_bytes(&mut encoded[1 + coefficient * 16..][..16]);
            }
            transcript.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &encoded);
            sink = sink
                .add(crate::sumcheck::boundary_sum(&polynomial))
                .add(running_claim);
            running_claim = crate::sumcheck::evaluate(&polynomial, alphas[round]);
            relation_weights.fold(alphas[round]);
        }
        sink = sink
            .add(relation_weights.dot(&final_coefficients))
            .add(running_claim);
    }

    if matches!(
        phase,
        PaymentHidingAggregatePhase::Layer0 | PaymentHidingAggregatePhase::Full
    ) {
        let mut indices = base_indices.clone();
        indices.sort_unstable();
        indices.dedup();
        for (ordinal, query) in indices.iter().copied().enumerate() {
            let aggregate = core::array::from_fn(|slot| {
                (0..PAYMENT_MASK_ORACLE_COUNT).fold(QM31::ZERO, |sum, oracle| {
                    let value = q(50_001 + oracle as u32 * 10_007 + query * 101 + slot as u32 * 11);
                    sum.add(prepared_lane_weights[oracle].mul(value))
                })
            });
            let layer1 = normalized_circle_to_line_arity4_prepared_multipliers(
                aggregate,
                alpha_prepared[0],
                alpha_squared_prepared[0],
                M31(7 + ordinal as u32 * 2),
                M31(11 + ordinal as u32 * 2),
            );
            sink = sink.add(layer1);
        }
    }

    if matches!(
        phase,
        PaymentHidingAggregatePhase::LaterFolds | PaymentHidingAggregatePhase::Full
    ) {
        let mut current = base_indices.clone();
        for layer in 0..3usize {
            current = current.iter().map(|index| index >> 2).collect();
            current.sort_unstable();
            current.dedup();
            for (ordinal, index) in current.iter().copied().enumerate() {
                let values = core::array::from_fn(|slot| {
                    q(60_001 + layer as u32 * 20_003 + index * 107 + slot as u32 * 13)
                });
                let folded = normalized_line_arity4_prepared_multipliers(
                    values,
                    alpha_prepared[layer + 1],
                    alpha_squared_prepared[layer + 1],
                    [
                        M31(101 + ordinal as u32 * 6),
                        M31(103 + ordinal as u32 * 6),
                        M31(107 + ordinal as u32 * 6),
                    ],
                );
                sink = sink.add(folded);
                if layer == 2 {
                    sink = sink.add(evaluate_final_line_tensor(
                        final_coefficients,
                        M31(109 + ordinal as u32 * 2),
                    ));
                }
            }
        }
    }

    fn hash_later_tree(hash: HashFn, tag: u8, depth: usize, seed_indices: &[u32], sink: &mut QM31) {
        let mut indices = seed_indices.to_vec();
        let mut rolling = [[0u8; 32]; 4];
        let mut leaf = [0u8; 64];
        for (ordinal, index) in indices.iter().copied().enumerate() {
            leaf[0..4].copy_from_slice(&index.to_le_bytes());
            let digest = leaf_hash(hash, tag, &leaf);
            rolling[ordinal & 3] = digest;
            *sink = sink.add(QM31::from_cm31(CM31::from_m31(M31(
                (u64::from(u32::from_le_bytes(digest[..4].try_into().unwrap())) % u64::from(P))
                    as u32,
            ))));
        }
        for _ in 0..depth {
            let mut parents = indices.iter().map(|index| index >> 2).collect::<Vec<_>>();
            parents.sort_unstable();
            parents.dedup();
            for (ordinal, parent) in parents.iter().copied().enumerate() {
                rolling[(ordinal + 1) & 3][0..4].copy_from_slice(&parent.to_le_bytes());
                let digest = node_hash4(hash, &rolling);
                rolling[ordinal & 3] = digest;
                *sink = sink.add(QM31::from_cm31(CM31::from_m31(M31(
                    (u64::from(u32::from_le_bytes(digest[..4].try_into().unwrap())) % u64::from(P))
                        as u32,
                ))));
            }
            indices = parents;
        }
    }
    if matches!(
        phase,
        PaymentHidingAggregatePhase::LaterMerkle | PaymentHidingAggregatePhase::Full
    ) {
        for (layer, depth) in [10usize, 8, 6].into_iter().enumerate() {
            let mut layer_indices = base_indices
                .iter()
                .map(|index| index >> (2 * (layer + 1)))
                .collect::<Vec<_>>();
            layer_indices.sort_unstable();
            layer_indices.dedup();
            hash_later_tree(
                hash,
                0xe1 + layer as u8,
                depth / 2,
                &layer_indices,
                &mut sink,
            );
        }
    }
    Ok(sink)
}

/// Absorb the initial mask claim after all mask-oracle roots and derive the
/// nonzero affine-combination challenge. Three zero draws are a bounded
/// completeness failure below `|QM31|^-3`.
pub fn begin_payment_hiding_sumcheck(
    transcript: &mut Transcript,
    initial_mask_claim: QM31,
) -> Result<QM31, ChallengeSampleExhausted> {
    let mut bytes = [0u8; 16];
    initial_mask_claim.write_le_bytes(&mut bytes);
    transcript.absorb(label::M31_PAYMENT_HIDING_MASK_CLAIM, &bytes);
    for _ in 0..PAYMENT_HIDING_CHALLENGE_RETRY_LIMIT {
        let eta = transcript.challenge_qm31()?;
        if eta != QM31::ZERO {
            return Ok(eta);
        }
    }
    Err(ChallengeSampleExhausted)
}

/// Initial mask claim from the upstream staggered-sumcheck identity:
/// `2^(mu-1) * sum_r (m_r(0) + m_r(1))`.
pub fn initial_payment_mask_claim(masks: &PaymentSumcheckMaskPolynomials) -> QM31 {
    let scale = M31(1 << (PAYMENT_SUMCHECK_ROUNDS - 1));
    masks.iter().fold(QM31::ZERO, |sum, mask| {
        sum.add(boundary_sum(mask).mul_m31(scale))
    })
}

/// Mask one honest round polynomial while preserving the current sumcheck
/// boundary. `mask_claim` is the mask-only component of the current running
/// claim; the full verifier claim is `mask_claim + eta * original_claim`.
pub fn mask_payment_sumcheck_round(
    original: &PaymentSumcheckFullPolynomial,
    round_mask: &PaymentSumcheckMaskPolynomial,
    mask_claim: QM31,
    eta: QM31,
    round: usize,
) -> PaymentSumcheckFullPolynomial {
    assert!(round < PAYMENT_SUMCHECK_ROUNDS);
    let remaining = PAYMENT_SUMCHECK_ROUNDS - round - 1;
    let scale = M31(1 << remaining);
    let half = M31(2).inv();
    let scaled_boundary = boundary_sum(round_mask).mul_m31(scale);
    let constant_adjustment = mask_claim.sub(scaled_boundary).mul_m31(half);
    let mut masked = core::array::from_fn(|coefficient| {
        round_mask[coefficient]
            .mul_m31(scale)
            .add(eta.mul(original[coefficient]))
    });
    masked[0] = masked[0].add(constant_adjustment);
    masked
}

/// Advance only the mask component after the verifier's round challenge.
pub fn next_payment_mask_claim(
    masked: &PaymentSumcheckFullPolynomial,
    original: &PaymentSumcheckFullPolynomial,
    challenge: QM31,
    eta: QM31,
) -> QM31 {
    evaluate(masked, challenge).sub(eta.mul(evaluate(original, challenge)))
}

#[cfg(test)]
mod tests {
    use alloc::{vec, vec::Vec};

    use super::*;
    use crate::{
        field::{CM31, P},
        statement_sumcheck::{
            compress_polynomial, PAYMENT_SUMCHECK_DEGREE, PAYMENT_SUMCHECK_WIRE_COEFFICIENTS,
        },
    };

    #[derive(Clone, Copy)]
    struct Rng(u64);

    fn host_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
            self.0
        }

        fn m31(&mut self) -> M31 {
            M31((self.next() % u64::from(P)) as u32)
        }

        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

    fn rank(mut matrix: Vec<Vec<QM31>>) -> usize {
        let rows = matrix.len();
        let columns = matrix.first().map_or(0, Vec::len);
        let mut rank = 0;
        for column in 0..columns {
            let Some(pivot) = (rank..rows).find(|&row| matrix[row][column] != QM31::ZERO) else {
                continue;
            };
            matrix.swap(rank, pivot);
            let inverse = matrix[rank][column].try_inv().unwrap();
            for value in &mut matrix[rank][column..] {
                *value = inverse.mul(*value);
            }
            let pivot_tail = matrix[rank][column..].to_vec();
            for row in 0..rows {
                if row == rank || matrix[row][column] == QM31::ZERO {
                    continue;
                }
                let scale = matrix[row][column];
                for (value, pivot_value) in matrix[row][column..].iter_mut().zip(&pivot_tail) {
                    *value = value.sub(scale.mul(*pivot_value));
                }
            }
            rank += 1;
            if rank == rows {
                break;
            }
        }
        rank
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

    fn eq_weight(point: &[QM31; PAYMENT_SUMCHECK_ROUNDS], row: usize) -> QM31 {
        point
            .iter()
            .enumerate()
            .fold(QM31::ONE, |weight, (coordinate, value)| {
                let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                weight.mul(if bit == 0 {
                    QM31::ONE.sub(*value)
                } else {
                    *value
                })
            })
    }

    type MaskSamplePoints = Vec<
        Vec<
            Vec<(
                [QM31; PAYMENT_SUMCHECK_ROUNDS],
                [QM31; PAYMENT_MASK_ORACLE_COUNT],
            )>,
        >,
    >;

    fn fixed_mask_sample_points(challenges: &[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> MaskSamplePoints {
        let mut prefix = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];
        let mut rounds = Vec::with_capacity(PAYMENT_SUMCHECK_ROUNDS);
        for round in 0..PAYMENT_SUMCHECK_ROUNDS {
            let remaining = PAYMENT_SUMCHECK_ROUNDS - round - 1;
            let mut samples = Vec::with_capacity(PAYMENT_SUMCHECK_DEGREE + 1);
            for sample in 0..=PAYMENT_SUMCHECK_DEGREE {
                prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
                let mut points = Vec::with_capacity(1usize << remaining);
                for assignment in 0..1usize << remaining {
                    for offset in 0..remaining {
                        let bit = (assignment >> (remaining - 1 - offset)) & 1;
                        prefix[round + 1 + offset] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
                    }
                    points.push((prefix, payment_masking_factors(&prefix)));
                }
                samples.push(points);
            }
            rounds.push(samples);
            prefix[round] = challenges[round];
        }
        rounds
    }

    fn committed_mask_observations(
        oracle: usize,
        row: usize,
        challenges: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
        sample_points: &MaskSamplePoints,
    ) -> Vec<QM31> {
        let boolean_point = core::array::from_fn(|coordinate| {
            let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
            if bit == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        });
        let mut running_claim = payment_masking_factor_for_oracle(oracle, &boolean_point);
        let mut observations = Vec::with_capacity(
            1 + PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_WIRE_COEFFICIENTS + 1,
        );
        observations.push(running_claim);
        for round in 0..PAYMENT_SUMCHECK_ROUNDS {
            let samples = core::array::from_fn(|sample| {
                sample_points[round][sample]
                    .iter()
                    .fold(QM31::ZERO, |sum, (point, factors)| {
                        sum.add(eq_weight(point, row).mul(factors[oracle]))
                    })
            });
            let polynomial = interpolate(&samples);
            assert_eq!(boundary_sum(&polynomial), running_claim);
            observations.extend(compress_polynomial(&polynomial));
            running_claim = evaluate(&polynomial, challenges[round]);
        }
        observations.push(eq_weight(challenges, row));
        assert_eq!(
            running_claim,
            observations
                .last()
                .copied()
                .unwrap()
                .mul(payment_masking_factor_for_oracle(oracle, challenges),)
        );
        observations
    }

    fn mask_observations(
        masks: &PaymentSumcheckMaskPolynomials,
        challenges: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
    ) -> Vec<QM31> {
        let original = [QM31::ZERO; PAYMENT_SUMCHECK_FULL_COEFFICIENTS];
        let mut mask_claim = initial_payment_mask_claim(masks);
        let mut observations =
            Vec::with_capacity(1 + PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_WIRE_COEFFICIENTS);
        observations.push(mask_claim);
        for round in 0..PAYMENT_SUMCHECK_ROUNDS {
            let masked =
                mask_payment_sumcheck_round(&original, &masks[round], mask_claim, QM31::ONE, round);
            assert_eq!(boundary_sum(&masked), mask_claim);
            observations.extend(compress_polynomial(&masked));
            mask_claim = next_payment_mask_claim(&masked, &original, challenges[round], QM31::ONE);
        }
        observations
    }

    #[test]
    fn masked_round_preserves_the_affine_boundary_and_terminal_split() {
        let mut rng = Rng(0x4d41_534b_5355_4d31);
        let masks = core::array::from_fn(|_| core::array::from_fn(|_| rng.qm31()));
        let original: PaymentSumcheckFullPolynomial = core::array::from_fn(|_| rng.qm31());
        let eta = rng.qm31();
        let original_claim = boundary_sum(&original);
        let mask_claim = initial_payment_mask_claim(&masks);
        let masked = mask_payment_sumcheck_round(&original, &masks[0], mask_claim, eta, 0);
        assert_eq!(
            boundary_sum(&masked),
            mask_claim.add(eta.mul(original_claim))
        );
        let challenge = rng.qm31();
        let next_mask = next_payment_mask_claim(&masked, &original, challenge, eta);
        assert_eq!(
            evaluate(&masked, challenge),
            next_mask.add(eta.mul(evaluate(&original, challenge)))
        );
    }

    #[test]
    fn all_101_public_sumcheck_fields_are_a_surjective_mask_image() {
        let mut rng = Rng(0x5241_4e4b_5a4b_5634);
        let challenges = core::array::from_fn(|_| rng.qm31());
        let zero_masks =
            [[QM31::ZERO; PAYMENT_SUMCHECK_MASK_COEFFICIENTS]; PAYMENT_SUMCHECK_ROUNDS];
        let observation_count = mask_observations(&zero_masks, &challenges).len();
        assert_eq!(observation_count, 101);
        assert_eq!(PAYMENT_SUMCHECK_MASK_RANDOMNESS, 110);

        let mut matrix =
            vec![vec![QM31::ZERO; PAYMENT_SUMCHECK_MASK_RANDOMNESS]; observation_count];
        for variable in 0..PAYMENT_SUMCHECK_MASK_RANDOMNESS {
            let mut masks = zero_masks;
            masks[variable / PAYMENT_SUMCHECK_MASK_COEFFICIENTS]
                [variable % PAYMENT_SUMCHECK_MASK_COEFFICIENTS] = QM31::ONE;
            for (row, value) in mask_observations(&masks, &challenges)
                .into_iter()
                .enumerate()
            {
                matrix[row][variable] = value;
            }
        }
        assert_eq!(rank(matrix), observation_count);
    }

    fn committed_oracle_ranks(row_for: impl Fn(usize, usize) -> usize) -> (usize, usize) {
        let mut rng = Rng(0x434f_4d4d_4954_5a4b);
        let challenges = core::array::from_fn(|_| rng.qm31());
        let mut shifted = challenges;
        for coordinate in [6usize, 8, 9] {
            shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
        }
        let kappa = rng.qm31();
        let delta = rng.qm31();
        assert_ne!(kappa, QM31::ZERO);
        assert_ne!(delta, QM31::ZERO);
        assert!((0..PAYMENT_MASK_ORACLE_COUNT).all(|oracle| {
            payment_masking_factor_for_oracle(oracle, &challenges) != QM31::ZERO
        }));
        let sample_points = fixed_mask_sample_points(&challenges);
        let variables_per_oracle = 32usize;
        let variables = PAYMENT_MASK_ORACLE_COUNT * variables_per_oracle;
        let observation_count = 1 + PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_WIRE_COEFFICIENTS;
        let mut matrix = vec![vec![QM31::ZERO; variables]; observation_count + 4];
        for variable in 0..variables {
            let oracle = variable / variables_per_oracle;
            let local = variable % variables_per_oracle;
            let row = row_for(oracle, local);
            let observations =
                committed_mask_observations(oracle, row, &challenges, &sample_points);
            let kappa_power = (0..oracle).fold(QM31::ONE, |power, _| power.mul(kappa));
            let delta_power = (0..oracle).fold(QM31::ONE, |power, _| power.mul(delta));
            assert_eq!(observations.len(), observation_count + 1);
            for (output, value) in observations[..observation_count]
                .iter()
                .copied()
                .enumerate()
            {
                matrix[output][variable] = kappa_power.mul(value);
            }
            matrix[observation_count][variable] = observations[observation_count]
                .mul(payment_masking_factor_for_oracle(oracle, &challenges))
                .mul(kappa_power);
            matrix[observation_count + 1][variable] = eq_weight(&shifted, row)
                .mul(payment_masking_factor_for_oracle(oracle, &challenges))
                .mul(kappa_power);
            matrix[observation_count + 2][variable] = eq_weight(&challenges, row).mul(delta_power);
            matrix[observation_count + 3][variable] = eq_weight(&shifted, row).mul(delta_power);
        }
        (rank(matrix[..observation_count].to_vec()), rank(matrix))
    }

    #[test]
    fn abstract_committed_oracles_mask_all_101_wire_fields_and_bind_terminal() {
        assert_eq!(
            committed_oracle_ranks(|oracle, local| {
                (local * 573 + oracle * 137 + 211) & (PAYMENT_MASK_ORACLE_SIZE - 1)
            }),
            (101, 104),
        );
    }

    #[test]
    fn current_c1_padding_virtual_oracles_are_rank_deficient() {
        const VIRTUAL_C1_ROWS: [[usize; 32]; PAYMENT_MASK_ORACLE_COUNT] = [
            [
                906, 821, 943, 858, 980, 895, 1017, 932, 847, 969, 884, 1006, 799, 921, 958, 873,
                995, 788, 910, 825, 947, 862, 984, 899, 1021, 936, 851, 973, 888, 1010, 803, 925,
            ],
            [
                921, 958, 873, 995, 788, 910, 825, 947, 862, 984, 899, 1021, 936, 851, 973, 888,
                1010, 803, 925, 962, 877, 999, 792, 914, 829, 951, 866, 988, 903, 940, 977, 892,
            ],
            [
                851, 973, 888, 1010, 803, 925, 962, 877, 999, 792, 914, 829, 951, 866, 988, 903,
                940, 855, 977, 892, 1014, 807, 929, 966, 881, 1003, 796, 918, 833, 955, 870, 992,
            ],
            [
                866, 988, 903, 940, 855, 977, 892, 1014, 807, 929, 966, 881, 1003, 796, 918, 833,
                955, 870, 992, 785, 907, 944, 859, 981, 896, 1018, 811, 933, 970, 885, 1007, 800,
            ],
            [
                881, 1003, 796, 918, 833, 955, 870, 992, 785, 907, 944, 859, 981, 896, 1018, 933,
                970, 885, 1007, 800, 922, 837, 959, 874, 996, 789, 911, 948, 863, 985, 900, 1022,
            ],
            [
                896, 1018, 933, 970, 885, 1007, 800, 922, 837, 959, 874, 996, 789, 911, 948, 863,
                985, 900, 1022, 815, 937, 974, 889, 1011, 804, 926, 841, 963, 878, 1000, 793, 915,
            ],
        ];
        assert_eq!(
            committed_oracle_ranks(|oracle, local| VIRTUAL_C1_ROWS[oracle][local]),
            (82, 84),
        );
        let move_high_bits_last = |row: usize| {
            let order = [2usize, 3, 4, 5, 6, 7, 8, 9, 0, 1];
            order.iter().enumerate().fold(0usize, |output, (new, old)| {
                let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - old)) & 1;
                output | (bit << (PAYMENT_SUMCHECK_ROUNDS - 1 - new))
            })
        };
        assert_eq!(
            committed_oracle_ranks(|oracle, local| {
                move_high_bits_last(VIRTUAL_C1_ROWS[oracle][local])
            }),
            (82, 84),
        );
    }

    #[test]
    fn hiding_placement_probe_prices_distinct_one_and_two_tree_shapes() {
        let in_batch =
            payment_hiding_placement_probe(host_hash, PaymentHidingPlacement::InBatch).unwrap();
        let separate =
            payment_hiding_placement_probe(host_hash, PaymentHidingPlacement::SeparateCommitment)
                .unwrap();
        assert_ne!(in_batch, QM31::ZERO);
        assert_ne!(separate, QM31::ZERO);
        assert_ne!(in_batch, separate);
        assert_ne!(
            payment_hiding_aggregate_relation_probe(host_hash).unwrap(),
            QM31::ZERO,
        );
    }
}
