//! Focused V8 research gate for the legacy six-oracle degree-10 mask.
//!
//! This is deliberately not a production protocol implementation.  It binds
//! the old `statement_hiding` linear map to one already accepted V7 transcript
//! and asks the strongest useful finite-field question available before a V8
//! wire exists: after fixing the complete gamma-combined 1024-element root
//! message, every individual q16 arity-four mask opening, and every individual
//! mask evaluation at the three V7 statement points, do the remaining mask
//! variables still span all 101 degree-10 sumcheck fields?
//!
//! The individual-opening model is conservative for a future merged-lane wire.
//! Passing one transcript is a nonzero-minor certificate, not an all-schedule
//! theorem; callers must keep that boundary explicit.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::statement_hiding::{
    payment_masking_factor_for_oracle, PAYMENT_MASK_ORACLE_COUNT, PAYMENT_MASK_ORACLE_SIZE,
};
use aspis_core::statement_sumcheck::{
    boundary_sum, compress_polynomial, evaluate, PaymentSumcheckFullPolynomial,
    PAYMENT_SUMCHECK_DEGREE, PAYMENT_SUMCHECK_ROUNDS, PAYMENT_SUMCHECK_WIRE_COEFFICIENTS,
};
use aspis_core::v6_transcript::{v6_statement_points, V6VerifiedTranscript};

use crate::circle_candidate::CircleEncoder;

const FIBER_SLOTS: usize = 4;
const V7_DOMAIN_LOG: u32 = 20;
const V7_QUERY_COUNT: usize = 16;
const QUERY_OBSERVATIONS: usize = V7_QUERY_COUNT * FIBER_SLOTS;
const POINT_OBSERVATIONS: usize = 3;
const CONDITIONING_OBSERVATIONS_PER_FREE_ORACLE: usize = QUERY_OBSERVATIONS + POINT_OBSERVATIONS;
const SUMCHECK_OBSERVATIONS: usize =
    1 + PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_WIRE_COEFFICIENTS;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V8SixMaskRankReport {
    pub mask_oracles: usize,
    pub variables_qm31: usize,
    pub complete_root_message_qm31: usize,
    pub complete_root_rank_qm31: usize,
    pub query_observations_per_oracle_qm31: usize,
    pub point_observations_per_oracle_qm31: usize,
    pub conditioning_rank_per_free_oracle_qm31: [usize; PAYMENT_MASK_ORACLE_COUNT - 1],
    pub conditioning_rank_after_root_qm31: usize,
    pub conditioned_kernel_qm31: usize,
    pub sumcheck_fields_qm31: usize,
    pub conditioned_sumcheck_rank_by_revealed_points_qm31: [usize; POINT_OBSERVATIONS + 1],
    pub conditioned_sumcheck_rank_qm31: usize,
    pub complete_view_rank_qm31: usize,
    pub complete_view_kernel_qm31: usize,
    pub universal_last_round_factor_rank: usize,
    pub universal_last_round_factor_dimension: usize,
    pub gamma_nonzero: bool,
    pub kappa_nonzero: bool,
    pub distinct_queries: bool,
    pub frozen_schedule_pass: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V8SixMaskRankError {
    Shape,
    Encoding,
    Relation,
    Singular,
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

/// The exact 101-field mask image of one unit table entry in one oracle.
fn sumcheck_column(
    oracle: usize,
    row: usize,
    challenges: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> Result<Vec<QM31>, V8SixMaskRankError> {
    let boolean_point = core::array::from_fn(|coordinate| {
        let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
        if bit == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    });
    let mut running_claim = payment_masking_factor_for_oracle(oracle, &boolean_point);
    let mut prefix = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];
    let mut observations = Vec::with_capacity(SUMCHECK_OBSERVATIONS);
    observations.push(running_claim);
    for round in 0..PAYMENT_SUMCHECK_ROUNDS {
        let samples = core::array::from_fn(|sample| {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            for coordinate in round + 1..PAYMENT_SUMCHECK_ROUNDS {
                let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                prefix[coordinate] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
            }
            eq_weight(&prefix, row).mul(payment_masking_factor_for_oracle(oracle, &prefix))
        });
        let polynomial = interpolate(&samples);
        if boundary_sum(&polynomial) != running_claim {
            return Err(V8SixMaskRankError::Relation);
        }
        observations.extend(compress_polynomial(&polynomial));
        running_claim = evaluate(&polynomial, challenges[round]);
        prefix[round] = challenges[round];
    }
    if observations.len() != SUMCHECK_OBSERVATIONS
        || running_claim
            != eq_weight(challenges, row).mul(payment_masking_factor_for_oracle(oracle, challenges))
    {
        return Err(V8SixMaskRankError::Relation);
    }
    Ok(observations)
}

fn conditioning_columns(
    encoder: &CircleEncoder,
    transcript: &V6VerifiedTranscript,
) -> Result<Vec<Vec<QM31>>, V8SixMaskRankError> {
    let points = v6_statement_points(&transcript.semantic_point);
    let mut columns = Vec::with_capacity(PAYMENT_MASK_ORACLE_SIZE);
    for row in 0..PAYMENT_MASK_ORACLE_SIZE {
        let mut column = Vec::with_capacity(CONDITIONING_OBSERVATIONS_PER_FREE_ORACLE);
        for &query in &transcript.queries {
            if query as usize >= (1usize << (V7_DOMAIN_LOG - 2)) {
                return Err(V8SixMaskRankError::Shape);
            }
            for slot in 0..FIBER_SLOTS {
                let coefficient = encoder
                    .encode_prefix_basis_value(
                        PAYMENT_SUMCHECK_ROUNDS as u32,
                        row,
                        FIBER_SLOTS * query as usize + slot,
                    )
                    .map_err(|_| V8SixMaskRankError::Encoding)?;
                column.push(QM31::from_cm31(CM31::from_m31(coefficient)));
            }
        }
        column.extend(points.iter().map(|point| eq_weight(point, row)));
        if column.len() != CONDITIONING_OBSERVATIONS_PER_FREE_ORACLE {
            return Err(V8SixMaskRankError::Shape);
        }
        columns.push(column);
    }
    Ok(columns)
}

/// Quotient one oracle's sumcheck image by all of its individual query and
/// point observations.  Columns landing in the observation kernel retain
/// their corresponding sumcheck image.
fn conditioned_kernel_images(
    raw_columns: &[Vec<QM31>],
    sumcheck_columns: impl IntoIterator<Item = Vec<QM31>>,
) -> Result<(usize, Vec<Vec<QM31>>), V8SixMaskRankError> {
    let raw_outputs = raw_columns
        .first()
        .map(Vec::len)
        .ok_or(V8SixMaskRankError::Shape)?;
    let mut pivots: Vec<Option<(Vec<QM31>, Vec<QM31>)>> = vec![None; raw_outputs];
    let mut kernel_images = Vec::new();
    for (mut raw, mut sumcheck) in raw_columns.iter().cloned().zip(sumcheck_columns) {
        if raw.len() != raw_outputs || sumcheck.len() != SUMCHECK_OBSERVATIONS {
            return Err(V8SixMaskRankError::Shape);
        }
        let mut became_pivot = false;
        for pivot in 0..raw_outputs {
            if raw[pivot] == QM31::ZERO {
                continue;
            }
            if let Some((pivot_raw, pivot_sumcheck)) = &pivots[pivot] {
                let scale = raw[pivot];
                for index in pivot..raw_outputs {
                    raw[index] = raw[index].sub(scale.mul(pivot_raw[index]));
                }
                for (value, pivot_value) in sumcheck.iter_mut().zip(pivot_sumcheck) {
                    *value = value.sub(scale.mul(*pivot_value));
                }
                continue;
            }
            let inverse = raw[pivot].try_inv().ok_or(V8SixMaskRankError::Singular)?;
            for value in &mut raw[pivot..] {
                *value = inverse.mul(*value);
            }
            for value in &mut sumcheck {
                *value = inverse.mul(*value);
            }
            // At most 67 columns per oracle take this branch.  Retaining the
            // local vectors keeps the kernel path ownership-simple without
            // materializing the 436 x 5120 dense matrix this gate replaces.
            pivots[pivot] = Some((raw.clone(), sumcheck.clone()));
            became_pivot = true;
            break;
        }
        if !became_pivot {
            if raw.iter().any(|value| *value != QM31::ZERO) {
                return Err(V8SixMaskRankError::Relation);
            }
            kernel_images.push(sumcheck);
        }
    }
    Ok((
        pivots.iter().filter(|pivot| pivot.is_some()).count(),
        kernel_images,
    ))
}

fn qm31_column_rank(
    columns: impl IntoIterator<Item = Vec<QM31>>,
    outputs: usize,
) -> Result<usize, V8SixMaskRankError> {
    let mut pivots: Vec<Option<Vec<QM31>>> = vec![None; outputs];
    for mut column in columns {
        if column.len() != outputs {
            return Err(V8SixMaskRankError::Shape);
        }
        for pivot in 0..outputs {
            if column[pivot] == QM31::ZERO {
                continue;
            }
            if let Some(pivot_column) = &pivots[pivot] {
                let scale = column[pivot];
                for index in pivot..outputs {
                    column[index] = column[index].sub(scale.mul(pivot_column[index]));
                }
                continue;
            }
            let inverse = column[pivot]
                .try_inv()
                .ok_or(V8SixMaskRankError::Singular)?;
            for value in &mut column[pivot..] {
                *value = inverse.mul(*value);
            }
            pivots[pivot] = Some(column);
            break;
        }
    }
    Ok(pivots.iter().filter(|pivot| pivot.is_some()).count())
}

/// Rank of `{f_k(t), t f_k(t)}` in the degree-at-most-ten coefficient space.
/// Translation from `t` to the last-round variable is invertible because the
/// last coefficient of L is 3 + 22*9 = 201, nonzero in M31.  This therefore
/// holds for every nine-round prefix and every nonzero kappa.
fn universal_last_round_factor_rank() -> Result<usize, V8SixMaskRankError> {
    const FACTORS: [[u8; 10]; PAYMENT_MASK_ORACLE_COUNT] = [
        [1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
        [1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ];
    let mut columns = Vec::with_capacity(2 * PAYMENT_MASK_ORACLE_COUNT);
    for factor in FACTORS {
        let base = (0..=PAYMENT_SUMCHECK_DEGREE)
            .map(|degree| M31(u32::from(factor.get(degree).copied().unwrap_or(0))))
            .map(|value| QM31::from_cm31(CM31::from_m31(value)))
            .collect::<Vec<_>>();
        let mut times_t = vec![QM31::ZERO; PAYMENT_SUMCHECK_DEGREE + 1];
        times_t[1..].copy_from_slice(&base[..PAYMENT_SUMCHECK_DEGREE]);
        columns.push(base);
        columns.push(times_t);
    }
    qm31_column_rank(columns, PAYMENT_SUMCHECK_DEGREE + 1)
}

pub fn probe_frozen_v7_six_mask_hiding_rank(
    transcript: &V6VerifiedTranscript,
) -> Result<V8SixMaskRankReport, V8SixMaskRankError> {
    if transcript.queries.len() != V7_QUERY_COUNT {
        return Err(V8SixMaskRankError::Shape);
    }
    let mut sorted_queries = transcript.queries;
    sorted_queries.sort_unstable();
    let distinct_queries = sorted_queries.windows(2).all(|pair| pair[0] != pair[1]);

    let encoder = CircleEncoder::new_for_domain_log(V7_DOMAIN_LOG);
    let all_raw_columns = conditioning_columns(&encoder, transcript)?;
    let sumcheck_by_oracle = (0..PAYMENT_MASK_ORACLE_COUNT)
        .map(|oracle| {
            (0..PAYMENT_MASK_ORACLE_SIZE)
                .map(|row| sumcheck_column(oracle, row, &transcript.semantic_point))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // The complete root target is R = sum_k gamma^k M_k.  Its first weight
    // is one, so eliminate M_0 exactly.  The five remaining tables are free.
    // Repeat the small quotient with zero through three point disclosures to
    // identify whether any deficit comes from q16 or terminal-view coupling.
    let mut rank_by_points = [0usize; POINT_OBSERVATIONS + 1];
    let mut conditioning_ranks = [0usize; PAYMENT_MASK_ORACLE_COUNT - 1];
    for revealed_points in 0..=POINT_OBSERVATIONS {
        let raw_outputs = QUERY_OBSERVATIONS + revealed_points;
        let raw_columns = all_raw_columns
            .iter()
            .map(|column| column[..raw_outputs].to_vec())
            .collect::<Vec<_>>();
        let mut gamma_power = transcript.gamma;
        let mut kappa_power = transcript.kappa;
        let mut current_conditioning_ranks = [0usize; PAYMENT_MASK_ORACLE_COUNT - 1];
        let mut all_kernel_images = Vec::new();
        for oracle in 1..PAYMENT_MASK_ORACLE_COUNT {
            let sumcheck_columns = (0..PAYMENT_MASK_ORACLE_SIZE)
                .map(|row| {
                    sumcheck_by_oracle[oracle][row]
                        .iter()
                        .copied()
                        .zip(&sumcheck_by_oracle[0][row])
                        .map(|(own, zero)| kappa_power.mul(own).sub(gamma_power.mul(*zero)))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let (rank, kernel_images) = conditioned_kernel_images(&raw_columns, sumcheck_columns)?;
            current_conditioning_ranks[oracle - 1] = rank;
            all_kernel_images.extend(kernel_images);
            gamma_power = gamma_power.mul(transcript.gamma);
            kappa_power = kappa_power.mul(transcript.kappa);
        }
        rank_by_points[revealed_points] =
            qm31_column_rank(all_kernel_images, SUMCHECK_OBSERVATIONS)?;
        if revealed_points == POINT_OBSERVATIONS {
            conditioning_ranks = current_conditioning_ranks;
        }
    }

    let conditioning_rank_after_root_qm31 = conditioning_ranks.iter().sum();
    let conditioned_kernel_qm31 = (PAYMENT_MASK_ORACLE_COUNT - 1) * PAYMENT_MASK_ORACLE_SIZE
        - conditioning_rank_after_root_qm31;
    let conditioned_sumcheck_rank_qm31 = rank_by_points[POINT_OBSERVATIONS];
    let complete_root_rank_qm31 = PAYMENT_MASK_ORACLE_SIZE;
    let complete_view_rank_qm31 = complete_root_rank_qm31
        + conditioning_rank_after_root_qm31
        + conditioned_sumcheck_rank_qm31;
    let variables_qm31 = PAYMENT_MASK_ORACLE_COUNT * PAYMENT_MASK_ORACLE_SIZE;
    let universal_last_round_factor_rank = universal_last_round_factor_rank()?;
    let kappa_nonzero = transcript.kappa != QM31::ZERO;
    let frozen_schedule_pass = distinct_queries
        && kappa_nonzero
        && conditioning_ranks
            .iter()
            .all(|rank| *rank == CONDITIONING_OBSERVATIONS_PER_FREE_ORACLE)
        && conditioned_sumcheck_rank_qm31 == SUMCHECK_OBSERVATIONS
        && universal_last_round_factor_rank == PAYMENT_SUMCHECK_DEGREE + 1;

    Ok(V8SixMaskRankReport {
        mask_oracles: PAYMENT_MASK_ORACLE_COUNT,
        variables_qm31,
        complete_root_message_qm31: PAYMENT_MASK_ORACLE_SIZE,
        complete_root_rank_qm31,
        query_observations_per_oracle_qm31: QUERY_OBSERVATIONS,
        point_observations_per_oracle_qm31: POINT_OBSERVATIONS,
        conditioning_rank_per_free_oracle_qm31: conditioning_ranks,
        conditioning_rank_after_root_qm31,
        conditioned_kernel_qm31,
        sumcheck_fields_qm31: SUMCHECK_OBSERVATIONS,
        conditioned_sumcheck_rank_by_revealed_points_qm31: rank_by_points,
        conditioned_sumcheck_rank_qm31,
        complete_view_rank_qm31,
        complete_view_kernel_qm31: variables_qm31 - complete_view_rank_qm31,
        universal_last_round_factor_rank,
        universal_last_round_factor_dimension: PAYMENT_SUMCHECK_DEGREE + 1,
        gamma_nonzero: transcript.gamma != QM31::ZERO,
        kappa_nonzero,
        distinct_queries,
        frozen_schedule_pass,
    })
}
