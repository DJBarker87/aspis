//! Host construction for the profile-14 mask-oracle aggregate.
//!
//! The six mask columns are committed before the payment sumcheck. After its
//! point `z` is derived, this module forms the only public mask evaluation
//! lane:
//!
//! `H_z(x) = sum_k kappa^k S_k(z) G_k(x)`.
//!
//! A production verifier must authenticate the layer-zero symbols from the
//! mask commitment and verify the returned fold/relation path. Merely
//! computing this host object is not an evaluation-binding proof.

use std::{vec, vec::Vec};

use aspis_core::circle_hiding_query::{PAYMENT_HIDING_C2_COLUMNS, PAYMENT_HIDING_C2_LEAF_BYTES};
use aspis_core::circle_merkle::CIRCLE_C2_LAYER0_TAG;
use aspis_core::field::{M31, QM31};
use aspis_core::merkle::{leaf_hash, node_hash4};
use aspis_core::statement_hiding::{
    payment_masking_factor_for_oracle, payment_masking_merged_lane_weights,
    PAYMENT_MASK_ORACLE_COUNT,
};
use aspis_core::HashFn;

use crate::circle_candidate::{
    build_fold_commitments_for_domain_log, CircleCandidateError, CircleEncoder,
    CircleFoldCommitments, TRACE_LEN,
};
use crate::circle_relation::{
    build_circle_relation, CircleRelationError, CircleRelationParameters, CircleRelationTrace,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaskOracleRelationError {
    OracleCount {
        expected: usize,
        actual: usize,
    },
    MessageLength {
        oracle: usize,
        expected: usize,
        actual: usize,
    },
    Candidate(CircleCandidateError),
    Relation(CircleRelationError),
    PointMismatch,
    C1ColumnCount {
        expected: usize,
        actual: usize,
    },
    H1Length {
        expected: usize,
        actual: usize,
    },
    C2ColumnCount {
        expected: usize,
        actual: usize,
    },
    CodewordLength {
        column: usize,
        expected: usize,
        actual: usize,
    },
    CodewordFiberShape {
        actual: usize,
    },
}

impl From<CircleCandidateError> for MaskOracleRelationError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Candidate(error)
    }
}

impl From<CircleRelationError> for MaskOracleRelationError {
    fn from(error: CircleRelationError) -> Self {
        Self::Relation(error)
    }
}

pub fn mask_oracle_lane_weights(z: &[QM31; 10], kappa: QM31) -> [QM31; PAYMENT_MASK_ORACLE_COUNT] {
    let mut kappa_power = QM31::ONE;
    core::array::from_fn(|oracle| {
        let weight = kappa_power.mul(payment_masking_factor_for_oracle(oracle, z));
        kappa_power = kappa_power.mul(kappa);
        weight
    })
}

fn validate_masks(masks: &[Vec<QM31>]) -> Result<(), MaskOracleRelationError> {
    if masks.len() != PAYMENT_MASK_ORACLE_COUNT {
        return Err(MaskOracleRelationError::OracleCount {
            expected: PAYMENT_MASK_ORACLE_COUNT,
            actual: masks.len(),
        });
    }
    for (oracle, mask) in masks.iter().enumerate() {
        if mask.len() != TRACE_LEN {
            return Err(MaskOracleRelationError::MessageLength {
                oracle,
                expected: TRACE_LEN,
                actual: mask.len(),
            });
        }
    }
    Ok(())
}

pub fn mask_oracle_aggregate_message(
    masks: &[Vec<QM31>],
    z: &[QM31; 10],
    kappa: QM31,
) -> Result<Vec<QM31>, MaskOracleRelationError> {
    validate_masks(masks)?;
    let weights = mask_oracle_lane_weights(z, kappa);
    let mut aggregate = vec![QM31::ZERO; TRACE_LEN];
    for (mask, weight) in masks.iter().zip(weights) {
        for (target, value) in aggregate.iter_mut().zip(mask) {
            *target = target.add(weight.mul(*value));
        }
    }
    Ok(aggregate)
}

/// Selected no-second-FRI construction. The returned mask message is folded
/// into the existing outer PCS lane under `gamma^50`.
pub fn mask_oracle_merged_message(
    masks: &[Vec<QM31>],
    z: &[QM31; 10],
    delta: QM31,
    tau: QM31,
    kappa: QM31,
) -> Result<Vec<QM31>, MaskOracleRelationError> {
    validate_masks(masks)?;
    let weights = payment_masking_merged_lane_weights(delta, tau, kappa, z);
    let mut aggregate = vec![QM31::ZERO; TRACE_LEN];
    for (mask, weight) in masks.iter().zip(weights) {
        for (target, value) in aggregate.iter_mut().zip(mask) {
            *target = target.add(weight.mul(*value));
        }
    }
    Ok(aggregate)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MergedPaymentMaskMaterial {
    pub message: Vec<QM31>,
    pub codeword: Vec<QM31>,
    /// Point-major `[A_delta, H_z]` at `z`, then at `xor11(z)`.
    pub mask_aggregates: [QM31; 4],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaymentHidingC2Commitment {
    pub encoded_columns: Vec<Vec<QM31>>,
    pub leaves: Vec<[u8; PAYMENT_HIDING_C2_LEAF_BYTES]>,
    pub root: [u8; 32],
}

fn payment_hiding_c2_leaves(
    encoded_columns: &[Vec<QM31>],
    codeword_len: usize,
) -> Result<Vec<[u8; PAYMENT_HIDING_C2_LEAF_BYTES]>, MaskOracleRelationError> {
    if encoded_columns.len() != PAYMENT_HIDING_C2_COLUMNS {
        return Err(MaskOracleRelationError::C2ColumnCount {
            expected: PAYMENT_HIDING_C2_COLUMNS,
            actual: encoded_columns.len(),
        });
    }
    if codeword_len == 0 || codeword_len % 4 != 0 {
        return Err(MaskOracleRelationError::CodewordFiberShape {
            actual: codeword_len,
        });
    }
    for (column, codeword) in encoded_columns.iter().enumerate() {
        if codeword.len() != codeword_len {
            return Err(MaskOracleRelationError::CodewordLength {
                column,
                expected: codeword_len,
                actual: codeword.len(),
            });
        }
    }
    Ok((0..codeword_len / 4)
        .map(|fiber| {
            let mut leaf = [0u8; PAYMENT_HIDING_C2_LEAF_BYTES];
            for (column, codeword) in encoded_columns.iter().enumerate() {
                for slot in 0..4 {
                    let offset = (column * 4 + slot) * 16;
                    codeword[4 * fiber + slot].write_le_bytes(&mut leaf[offset..offset + 16]);
                }
            }
            leaf
        })
        .collect())
}

fn radix4_leaf_root<const N: usize>(leaves: &[[u8; N]], tag: u8, hash: HashFn) -> Option<[u8; 32]> {
    if leaves.is_empty() || !leaves.len().is_power_of_two() || leaves.len().ilog2() % 2 != 0 {
        return None;
    }
    let mut level = leaves
        .iter()
        .map(|leaf| leaf_hash(hash, tag, leaf))
        .collect::<Vec<_>>();
    while level.len() > 1 {
        level = level
            .chunks_exact(4)
            .map(|children| node_hash4(hash, children.try_into().unwrap()))
            .collect();
    }
    Some(level[0])
}

pub fn build_payment_hiding_c2_commitment(
    encoder: &CircleEncoder,
    h1: &[QM31],
    mask: &[QM31],
    hash: HashFn,
) -> Result<PaymentHidingC2Commitment, MaskOracleRelationError> {
    if h1.len() != TRACE_LEN {
        return Err(MaskOracleRelationError::H1Length {
            expected: TRACE_LEN,
            actual: h1.len(),
        });
    }
    if mask.len() != TRACE_LEN {
        return Err(MaskOracleRelationError::MessageLength {
            oracle: 0,
            expected: TRACE_LEN,
            actual: mask.len(),
        });
    }
    let mut encoded_columns = Vec::with_capacity(PAYMENT_HIDING_C2_COLUMNS);
    encoded_columns.push(encoder.encode_c2_message(h1)?);
    encoded_columns.push(encoder.encode_c2_message(mask)?);
    let leaves = payment_hiding_c2_leaves(&encoded_columns, encoder.codeword_len())?;
    let root = radix4_leaf_root(&leaves, CIRCLE_C2_LAYER0_TAG, hash).ok_or(
        MaskOracleRelationError::CodewordFiberShape {
            actual: encoder.codeword_len(),
        },
    )?;
    Ok(PaymentHidingC2Commitment {
        encoded_columns,
        leaves,
        root,
    })
}

pub fn payment_mask_aggregates(
    masks: &[Vec<QM31>],
    z: &[QM31; 10],
    delta: QM31,
    kappa: QM31,
) -> Result<[QM31; 4], MaskOracleRelationError> {
    validate_masks(masks)?;
    let mut shifted = *z;
    for coordinate in [6usize, 8, 9] {
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    let h_weights = mask_oracle_lane_weights(z, kappa);
    let mut delta_weights = [QM31::ZERO; PAYMENT_MASK_ORACLE_COUNT];
    let mut power = QM31::ONE;
    for weight in &mut delta_weights {
        *weight = power;
        power = power.mul(delta);
    }
    let mut output = [QM31::ZERO; 4];
    for (point_index, point) in [z, &shifted].into_iter().enumerate() {
        for oracle in 0..PAYMENT_MASK_ORACLE_COUNT {
            let evaluation = crate::multilinear_eval_extension(&masks[oracle], point);
            output[2 * point_index] =
                output[2 * point_index].add(delta_weights[oracle].mul(evaluation));
            output[2 * point_index + 1] =
                output[2 * point_index + 1].add(h_weights[oracle].mul(evaluation));
        }
    }
    Ok(output)
}

/// Build the selected single-codeword natural message and rate-1/16 codeword.
/// C1 uses gamma powers 0..48, h1 uses gamma^49, and the nested mask lane uses
/// gamma^50.
pub fn build_merged_payment_mask_material(
    encoder: &CircleEncoder,
    c1: &[Vec<M31>],
    h1: &[QM31],
    masks: &[Vec<QM31>],
    z: &[QM31; 10],
    delta: QM31,
    tau: QM31,
    kappa: QM31,
    gamma: QM31,
) -> Result<MergedPaymentMaskMaterial, MaskOracleRelationError> {
    const C1_COLUMNS: usize = 49;
    if c1.len() != C1_COLUMNS {
        return Err(MaskOracleRelationError::C1ColumnCount {
            expected: C1_COLUMNS,
            actual: c1.len(),
        });
    }
    if h1.len() != TRACE_LEN {
        return Err(MaskOracleRelationError::H1Length {
            expected: TRACE_LEN,
            actual: h1.len(),
        });
    }
    validate_masks(masks)?;
    let mask_message = mask_oracle_merged_message(masks, z, delta, tau, kappa)?;
    let mask_codeword = mask_oracle_aggregate_codeword_with_weights(
        encoder,
        masks,
        payment_masking_merged_lane_weights(delta, tau, kappa, z),
    )?;
    let mut message = vec![QM31::ZERO; TRACE_LEN];
    let mut codeword = vec![QM31::ZERO; encoder.codeword_len()];
    let mut gamma_power = QM31::ONE;
    for column in c1 {
        if column.len() != TRACE_LEN {
            return Err(MaskOracleRelationError::MessageLength {
                oracle: usize::MAX,
                expected: TRACE_LEN,
                actual: column.len(),
            });
        }
        let encoded = encoder.encode_c1_message(column)?;
        for (target, value) in message.iter_mut().zip(column) {
            *target = target.add(gamma_power.mul_m31(*value));
        }
        for (target, value) in codeword.iter_mut().zip(encoded) {
            *target = target.add(gamma_power.mul_m31(value));
        }
        gamma_power = gamma_power.mul(gamma);
    }
    let encoded_h1 = encoder.encode_c2_message(h1)?;
    for (target, value) in message.iter_mut().zip(h1) {
        *target = target.add(gamma_power.mul(*value));
    }
    for (target, value) in codeword.iter_mut().zip(encoded_h1) {
        *target = target.add(gamma_power.mul(value));
    }
    gamma_power = gamma_power.mul(gamma);
    for (target, value) in message.iter_mut().zip(mask_message) {
        *target = target.add(gamma_power.mul(value));
    }
    for (target, value) in codeword.iter_mut().zip(mask_codeword) {
        *target = target.add(gamma_power.mul(value));
    }
    Ok(MergedPaymentMaskMaterial {
        message,
        codeword,
        mask_aggregates: payment_mask_aggregates(masks, z, delta, kappa)?,
    })
}

fn mask_oracle_aggregate_codeword_with_weights(
    encoder: &CircleEncoder,
    masks: &[Vec<QM31>],
    weights: [QM31; PAYMENT_MASK_ORACLE_COUNT],
) -> Result<Vec<QM31>, MaskOracleRelationError> {
    validate_masks(masks)?;
    let mut aggregate = vec![QM31::ZERO; encoder.codeword_len()];
    for (mask, weight) in masks.iter().zip(weights) {
        let encoded = encoder.encode_c2_message(mask)?;
        for (target, value) in aggregate.iter_mut().zip(encoded) {
            *target = target.add(weight.mul(value));
        }
    }
    Ok(aggregate)
}

pub fn mask_oracle_aggregate_codeword(
    encoder: &CircleEncoder,
    masks: &[Vec<QM31>],
    z: &[QM31; 10],
    kappa: QM31,
) -> Result<Vec<QM31>, MaskOracleRelationError> {
    validate_masks(masks)?;
    let weights = mask_oracle_lane_weights(z, kappa);
    let mut aggregate = vec![QM31::ZERO; encoder.codeword_len()];
    for (mask, weight) in masks.iter().zip(weights) {
        let encoded = encoder.encode_c2_message(mask)?;
        for (target, value) in aggregate.iter_mut().zip(encoded) {
            *target = target.add(weight.mul(value));
        }
    }
    Ok(aggregate)
}

pub fn build_mask_oracle_fold_commitments(
    encoder: &CircleEncoder,
    masks: &[Vec<QM31>],
    z: &[QM31; 10],
    kappa: QM31,
    alphas: [QM31; 4],
    hash: HashFn,
) -> Result<CircleFoldCommitments, MaskOracleRelationError> {
    let message = mask_oracle_aggregate_message(masks, z, kappa)?;
    let codeword = mask_oracle_aggregate_codeword(encoder, masks, z, kappa)?;
    Ok(build_fold_commitments_for_domain_log(
        &codeword,
        &message,
        alphas,
        encoder.domain_log_size(),
        hash,
    )?)
}

pub fn build_mask_oracle_circle_relation(
    masks: &[Vec<QM31>],
    z: &[QM31; 10],
    kappa: QM31,
    parameters: &CircleRelationParameters,
) -> Result<CircleRelationTrace, MaskOracleRelationError> {
    if parameters.z != *z {
        return Err(MaskOracleRelationError::PointMismatch);
    }
    let message = mask_oracle_aggregate_message(masks, z, kappa)?;
    Ok(build_circle_relation(&message, parameters)?)
}

#[cfg(test)]
mod tests {
    use aspis_core::circle::secure_ood_circle_point_from_parameter;
    use aspis_core::field::{CM31, M31};

    use super::*;
    use crate::circle_relation::CircleRelationPointRule;
    use crate::{multilinear_eval_extension, HOST_HASH};

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed), M31(seed + 1)),
            c1: CM31::new(M31(seed + 2), M31(seed + 3)),
        }
    }

    #[test]
    fn aggregate_message_binds_exactly_the_masked_terminal() {
        let masks = (0..PAYMENT_MASK_ORACLE_COUNT)
            .map(|oracle| {
                (0..TRACE_LEN)
                    .map(|row| q(1_000 + oracle as u32 * 20_000 + row as u32 * 7))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let z = core::array::from_fn(|coordinate| q(300 + coordinate as u32 * 19));
        let kappa = q(901);
        let aggregate = mask_oracle_aggregate_message(&masks, &z, kappa).unwrap();
        let direct = mask_oracle_lane_weights(&z, kappa)
            .into_iter()
            .zip(&masks)
            .fold(QM31::ZERO, |sum, (weight, mask)| {
                sum.add(weight.mul(multilinear_eval_extension(mask, &z)))
            });
        assert_eq!(multilinear_eval_extension(&aggregate, &z), direct);

        let delta = q(947);
        let tau = q(977);
        let merged = mask_oracle_merged_message(&masks, &z, delta, tau, kappa).unwrap();
        let delta_at_z = masks
            .iter()
            .fold((QM31::ZERO, QM31::ONE), |(sum, power), mask| {
                (
                    sum.add(power.mul(multilinear_eval_extension(mask, &z))),
                    power.mul(delta),
                )
            })
            .0;
        assert_eq!(
            multilinear_eval_extension(&merged, &z),
            delta_at_z.add(tau.mul(direct)),
        );
        let c1 = (0..49usize)
            .map(|column| {
                (0..TRACE_LEN)
                    .map(|row| M31(17 + column as u32 * 10_007 + row as u32 * 13))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let h1 = (0..TRACE_LEN)
            .map(|row| q(80_001 + row as u32 * 17))
            .collect::<Vec<_>>();
        let gamma = q(991);
        let encoder = CircleEncoder::new_for_domain_log(14);
        let commitment =
            build_payment_hiding_c2_commitment(&encoder, &h1, &masks[0], HOST_HASH).unwrap();
        assert_eq!(commitment.encoded_columns.len(), PAYMENT_HIDING_C2_COLUMNS);
        assert_eq!(commitment.leaves.len(), 1 << 12);
        for column in 0..PAYMENT_HIDING_C2_COLUMNS {
            for slot in 0..4 {
                let offset = (column * 4 + slot) * 16;
                assert_eq!(
                    QM31::from_le_bytes(&commitment.leaves[0][offset..offset + 16]).unwrap(),
                    commitment.encoded_columns[column][slot],
                );
            }
        }
        let material = build_merged_payment_mask_material(
            &encoder, &c1, &h1, &masks, &z, delta, tau, kappa, gamma,
        )
        .unwrap();
        let mut expected_claim = QM31::ZERO;
        let mut gamma_power = QM31::ONE;
        for column in &c1 {
            expected_claim =
                expected_claim.add(gamma_power.mul(crate::multilinear_eval(column, &z)));
            gamma_power = gamma_power.mul(gamma);
        }
        expected_claim = expected_claim.add(gamma_power.mul(multilinear_eval_extension(&h1, &z)));
        gamma_power = gamma_power.mul(gamma);
        expected_claim = expected_claim.add(
            gamma_power.mul(material.mask_aggregates[0].add(tau.mul(material.mask_aggregates[1]))),
        );
        assert_eq!(
            multilinear_eval_extension(&material.message, &z),
            expected_claim,
        );
        assert_eq!(
            encoder.encode_c2_message(&material.message).unwrap(),
            material.codeword,
        );

        let folds = build_mask_oracle_fold_commitments(
            &encoder,
            &masks,
            &z,
            kappa,
            [q(1_101), q(1_201), q(1_301), q(1_401)],
            HOST_HASH,
        )
        .unwrap();
        assert_eq!(folds.final_coefficients.len(), 4);
        assert_eq!(folds.committed_evaluations[0].len(), 1 << 12);

        let mut xor11_z = z;
        for coordinate in &mut xor11_z[8..] {
            *coordinate = QM31::ONE.sub(*coordinate);
        }
        let parameters = CircleRelationParameters {
            z,
            xor11_z,
            point_rule: CircleRelationPointRule::LegacyLowBits2,
            point_scales: [QM31::ONE, QM31::ZERO],
            layer0_ood_points: [
                secure_ood_circle_point_from_parameter(q(1_501)).unwrap(),
                secure_ood_circle_point_from_parameter(q(1_601)).unwrap(),
            ],
            later_ood_x: [
                [q(1_701), q(1_801)],
                [q(1_901), q(2_001)],
                [q(2_101), q(2_201)],
            ],
            ood_mixes: [
                [q(2_301), q(2_401)],
                [q(2_501), q(2_601)],
                [q(2_701), q(2_801)],
                [q(2_901), q(3_001)],
            ],
            alphas: [q(3_101), q(3_201), q(3_301), q(3_401)],
        };
        let relation = build_mask_oracle_circle_relation(&masks, &z, kappa, &parameters).unwrap();
        assert_eq!(relation.point_claims[0], direct);
    }
}
