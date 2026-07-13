//! Prover for the direct-binding profile-21 batch-evaluation sumcheck.

use aspis_core::field::QM31;
use aspis_core::state_only_batch_eval::{
    switch_line_tensor_factors, SwitchBatchEvalError, SwitchBatchEvalSchedule,
    SWITCH_BATCH_EVAL_ACTIVE_COEFFICIENTS, SWITCH_BATCH_EVAL_COEFFICIENTS,
    SWITCH_BATCH_EVAL_ROUNDS,
};
use aspis_core::transcript::{label, Transcript};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuiltSwitchBatchEvaluation {
    pub bytes: Vec<u8>,
    pub schedule: SwitchBatchEvalSchedule,
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
    let mut record = [0u8; 49];
    record[0] = round as u8;
    for (index, coefficient) in polynomial.iter().enumerate() {
        coefficient.write_le_bytes(&mut record[1 + 16 * index..]);
    }
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_BATCH_EVAL_SUMCHECK, &record);
}

fn tensor_basis_value(factors: &[QM31; 8], index: usize) -> QM31 {
    factors
        .iter()
        .enumerate()
        .filter(|(coordinate, _)| (index >> (7 - coordinate)) & 1 != 0)
        .fold(QM31::ONE, |product, (_, factor)| product.mul(*factor))
}

pub fn build_switch_batch_evaluation(
    transcript: &mut Transcript,
    coefficients: &[QM31; SWITCH_BATCH_EVAL_ACTIVE_COEFFICIENTS],
    queries: &[u32],
    opened_values: &[QM31],
) -> Result<BuiltSwitchBatchEvaluation, SwitchBatchEvalError> {
    absorb_opened_values(transcript, queries, opened_values)?;
    let zeta = transcript.challenge_qm31()?;

    let mut left = vec![QM31::ZERO; SWITCH_BATCH_EVAL_COEFFICIENTS];
    left[..coefficients.len()].copy_from_slice(coefficients);
    let mut right = vec![QM31::ZERO; SWITCH_BATCH_EVAL_COEFFICIENTS];
    let mut power = QM31::ONE;
    for &query in queries {
        let factors = switch_line_tensor_factors(query)?;
        for (index, value) in right.iter_mut().enumerate() {
            *value = value.add(power.mul(tensor_basis_value(&factors, index)));
        }
        power = power.mul(zeta);
    }

    let mut bytes = Vec::with_capacity(SWITCH_BATCH_EVAL_ROUNDS * 48);
    let mut point = [QM31::ZERO; SWITCH_BATCH_EVAL_ROUNDS];
    for round in 0..SWITCH_BATCH_EVAL_ROUNDS {
        let half = left.len() / 2;
        let (left_zero, left_one) = left.split_at(half);
        let (right_zero, right_one) = right.split_at(half);
        let mut polynomial = [QM31::ZERO; 3];
        for index in 0..half {
            let a0 = left_zero[index];
            let da = left_one[index].sub(a0);
            let b0 = right_zero[index];
            let db = right_one[index].sub(b0);
            polynomial[0] = polynomial[0].add(a0.mul(b0));
            polynomial[1] = polynomial[1].add(a0.mul(db).add(da.mul(b0)));
            polynomial[2] = polynomial[2].add(da.mul(db));
        }
        for coefficient in polynomial {
            let start = bytes.len();
            bytes.resize(start + 16, 0);
            coefficient.write_le_bytes(&mut bytes[start..]);
        }
        absorb_round(transcript, round, &polynomial);
        point[round] = transcript.challenge_qm31()?;
        left = (0..half)
            .map(|index| {
                left_zero[index].add(point[round].mul(left_one[index].sub(left_zero[index])))
            })
            .collect();
        right = (0..half)
            .map(|index| {
                right_zero[index].add(point[round].mul(right_one[index].sub(right_zero[index])))
            })
            .collect();
    }
    Ok(BuiltSwitchBatchEvaluation {
        bytes,
        schedule: SwitchBatchEvalSchedule { zeta, point },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31};
    use aspis_core::state_only_batch_eval::verify_switch_batch_evaluation;
    use aspis_core::state_only_masked_switch::{
        evaluate_masked_switch_line, masked_switch_query_point,
    };
    use aspis_core::HashFn;
    use sha2::{Digest, Sha256};

    fn hash(parts: &[&[u8]]) -> [u8; 32] {
        let mut state = Sha256::new();
        for part in parts {
            state.update(part);
        }
        state.finalize().into()
    }

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed + 1), M31(3 * seed + 5)),
            c1: CM31::new(M31(7 * seed + 11), M31(13 * seed + 17)),
        }
    }

    fn transcript_for(coefficients: &[QM31; 35]) -> Transcript {
        let mut transcript = Transcript::new(hash as HashFn);
        transcript.absorb(91, b"batch-eval-test");
        let mut bytes = [0u8; 35 * 16];
        for (index, coefficient) in coefficients.iter().enumerate() {
            coefficient.write_le_bytes(&mut bytes[16 * index..]);
        }
        transcript.absorb(label::M31_STATE_ONLY_SWITCH_U, &bytes);
        transcript
    }

    #[test]
    fn prover_verifier_and_direct_line_values_agree() {
        // Exact sorted q16 schedule from the packed profile-21 fixture.
        let queries = [
            237u32, 844, 12_677, 17_807, 27_037, 36_889, 37_750, 43_725, 48_161, 54_052, 55_238,
            55_970, 57_425, 70_782, 73_579, 127_428,
        ];
        for seed in 0..8u32 {
            let coefficients = core::array::from_fn(|index| q(index as u32 + 101 + seed * 997));
            let opened = queries
                .iter()
                .map(|&query| {
                    evaluate_masked_switch_line(
                        &coefficients,
                        masked_switch_query_point(query).unwrap(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let mut prover = transcript_for(&coefficients);
            let built =
                build_switch_batch_evaluation(&mut prover, &coefficients, &queries, &opened)
                    .unwrap();
            let mut verifier = transcript_for(&coefficients);
            assert_eq!(
                verify_switch_batch_evaluation(
                    &mut verifier,
                    &coefficients,
                    &queries,
                    &opened,
                    &built.bytes,
                )
                .unwrap(),
                built.schedule,
            );

            if seed == 0 {
                for opened_index in 0..opened.len() {
                    let mut corrupt = opened.clone();
                    corrupt[opened_index] = corrupt[opened_index].add(QM31::ONE);
                    let mut verifier = transcript_for(&coefficients);
                    assert!(verify_switch_batch_evaluation(
                        &mut verifier,
                        &coefficients,
                        &queries,
                        &corrupt,
                        &built.bytes,
                    )
                    .is_err());
                }
                for round in 0..8 {
                    for coefficient in 0..3 {
                        let mut corrupt = built.bytes.clone();
                        corrupt[48 * round + 16 * coefficient] ^= 1;
                        let mut verifier = transcript_for(&coefficients);
                        assert!(verify_switch_batch_evaluation(
                            &mut verifier,
                            &coefficients,
                            &queries,
                            &opened,
                            &corrupt,
                        )
                        .is_err());
                    }
                }
                let mut corrupt_coefficients = coefficients;
                corrupt_coefficients[17] = corrupt_coefficients[17].add(QM31::ONE);
                let mut verifier = transcript_for(&corrupt_coefficients);
                assert!(verify_switch_batch_evaluation(
                    &mut verifier,
                    &corrupt_coefficients,
                    &queries,
                    &opened,
                    &built.bytes,
                )
                .is_err());
                let mut reordered_queries = queries;
                reordered_queries.swap(3, 12);
                let mut verifier = transcript_for(&coefficients);
                assert!(verify_switch_batch_evaluation(
                    &mut verifier,
                    &coefficients,
                    &reordered_queries,
                    &opened,
                    &built.bytes,
                )
                .is_err());
            }
        }
    }
}
