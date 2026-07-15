//! Host commitment/recombination helpers for spend's H/G/D C2 leaf.

use aspis_core::field::{qm31_power_table, M31, QM31};
use aspis_core::state_only_query::{STATE_ONLY_C1_COLUMNS, STATE_ONLY_FIBER_SLOTS};
use aspis_core::state_only_spend_query::{
    SPEND_C2_COLUMNS, SPEND_C2_LEAF_BYTES, SPEND_TOTAL_COLUMNS,
};

use crate::circle_candidate::{CircleCandidateError, CircleEncoder};

fn validate<T>(
    columns: &[Vec<T>],
    expected: usize,
    codeword_len: usize,
) -> Result<(), CircleCandidateError> {
    if columns.len() != expected {
        return Err(CircleCandidateError::ColumnCount {
            expected,
            actual: columns.len(),
        });
    }
    for (column, values) in columns.iter().enumerate() {
        if values.len() != codeword_len {
            return Err(CircleCandidateError::CodewordLength {
                column,
                expected: codeword_len,
                actual: values.len(),
            });
        }
    }
    Ok(())
}

pub fn encode_state_only_spend_c2_columns(
    encoder: &CircleEncoder,
    messages: &[Vec<QM31>],
) -> Result<Vec<Vec<QM31>>, CircleCandidateError> {
    if messages.len() != SPEND_C2_COLUMNS {
        return Err(CircleCandidateError::ColumnCount {
            expected: SPEND_C2_COLUMNS,
            actual: messages.len(),
        });
    }
    messages
        .iter()
        .map(|message| encoder.encode_c2_message(message))
        .collect()
}

pub fn state_only_spend_c2_layer0_leaves(
    encoded: &[Vec<QM31>],
    codeword_len: usize,
) -> Result<Vec<[u8; SPEND_C2_LEAF_BYTES]>, CircleCandidateError> {
    validate(encoded, SPEND_C2_COLUMNS, codeword_len)?;
    Ok((0..codeword_len / STATE_ONLY_FIBER_SLOTS)
        .map(|fiber| {
            let mut leaf = [0u8; SPEND_C2_LEAF_BYTES];
            let mut offset = 0;
            for helper in encoded {
                for slot in 0..STATE_ONLY_FIBER_SLOTS {
                    let index = STATE_ONLY_FIBER_SLOTS * fiber + slot;
                    helper[index].write_le_bytes(&mut leaf[offset..offset + 16]);
                    offset += 16;
                }
            }
            leaf
        })
        .collect())
}

pub fn gamma_combine_state_only_spend_codewords(
    c1: &[Vec<M31>],
    c2: &[Vec<QM31>],
    gamma: QM31,
    codeword_len: usize,
) -> Result<Vec<QM31>, CircleCandidateError> {
    validate(c1, STATE_ONLY_C1_COLUMNS, codeword_len)?;
    validate(c2, SPEND_C2_COLUMNS, codeword_len)?;
    let powers = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma);
    let mut combined = vec![QM31::ZERO; codeword_len];
    for (column, power) in c1
        .iter()
        .zip(powers[..STATE_ONLY_C1_COLUMNS].iter().copied())
    {
        for (target, value) in combined.iter_mut().zip(column) {
            *target = target.add(power.mul_m31(*value));
        }
    }
    for (helper, power) in c2
        .iter()
        .zip(powers[STATE_ONLY_C1_COLUMNS..].iter().copied())
    {
        for (target, value) in combined.iter_mut().zip(helper) {
            *target = target.add(power.mul(*value));
        }
    }
    Ok(combined)
}

pub fn gamma_combine_state_only_spend_messages(
    c1: &[Vec<M31>],
    c2: &[Vec<QM31>],
    gamma: QM31,
) -> Result<Vec<QM31>, CircleCandidateError> {
    gamma_combine_state_only_spend_codewords(c1, c2, gamma, 1 << 10)
}
