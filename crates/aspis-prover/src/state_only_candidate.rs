//! Host commitment primitives for the width-18 state-only profile.
//!
//! These helpers deliberately reuse the ordinary circle encoder and fold;
//! only the layer-zero leaf width and the powers-generator length change.

use aspis_core::field::{qm31_power_table, M31, QM31};
use aspis_core::merkle::{leaf_hash, node_hash, node_hash4};
use aspis_core::proof::{M31_CIRCLE_C2_LAYER_TAG, M31_CIRCLE_COMBINED_LAYER_TAG_BASE};
use aspis_core::state_only_query::{
    STATE_ONLY_C1_COLUMNS, STATE_ONLY_C1_LEAF_BYTES, STATE_ONLY_C2_COLUMNS,
    STATE_ONLY_C2_LEAF_BYTES, STATE_ONLY_FIBER_SLOTS, STATE_ONLY_TOTAL_COLUMNS,
};
use aspis_core::HashFn;

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

pub fn encode_state_only_c1_columns(
    encoder: &CircleEncoder,
    messages: &[Vec<M31>],
) -> Result<Vec<Vec<M31>>, CircleCandidateError> {
    if messages.len() != STATE_ONLY_C1_COLUMNS {
        return Err(CircleCandidateError::ColumnCount {
            expected: STATE_ONLY_C1_COLUMNS,
            actual: messages.len(),
        });
    }
    messages
        .iter()
        .map(|message| encoder.encode_c1_message(message))
        .collect()
}

pub fn encode_state_only_c2_columns(
    encoder: &CircleEncoder,
    messages: &[Vec<QM31>],
) -> Result<Vec<Vec<QM31>>, CircleCandidateError> {
    if messages.len() != STATE_ONLY_C2_COLUMNS {
        return Err(CircleCandidateError::ColumnCount {
            expected: STATE_ONLY_C2_COLUMNS,
            actual: messages.len(),
        });
    }
    messages
        .iter()
        .map(|message| encoder.encode_c2_message(message))
        .collect()
}

pub fn state_only_c1_layer0_leaves(
    encoded: &[Vec<M31>],
    codeword_len: usize,
) -> Result<Vec<[u8; STATE_ONLY_C1_LEAF_BYTES]>, CircleCandidateError> {
    validate(encoded, STATE_ONLY_C1_COLUMNS, codeword_len)?;
    Ok((0..codeword_len / STATE_ONLY_FIBER_SLOTS)
        .map(|fiber| {
            let mut leaf = [0u8; STATE_ONLY_C1_LEAF_BYTES];
            let mut offset = 0;
            for slot in 0..STATE_ONLY_FIBER_SLOTS {
                let index = STATE_ONLY_FIBER_SLOTS * fiber + slot;
                for column in encoded {
                    leaf[offset..offset + 4].copy_from_slice(&column[index].to_le_bytes());
                    offset += 4;
                }
            }
            leaf
        })
        .collect())
}

pub fn state_only_c2_layer0_leaves(
    encoded: &[Vec<QM31>],
    codeword_len: usize,
) -> Result<Vec<[u8; STATE_ONLY_C2_LEAF_BYTES]>, CircleCandidateError> {
    validate(encoded, STATE_ONLY_C2_COLUMNS, codeword_len)?;
    Ok((0..codeword_len / STATE_ONLY_FIBER_SLOTS)
        .map(|fiber| {
            let mut leaf = [0u8; STATE_ONLY_C2_LEAF_BYTES];
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

fn hybrid_root<const N: usize>(leaves: &[[u8; N]], tag: u8, hash: HashFn) -> [u8; 32] {
    debug_assert!(!leaves.is_empty() && leaves.len().is_power_of_two());
    let mut level = leaves
        .iter()
        .map(|leaf| leaf_hash(hash, tag, leaf))
        .collect::<Vec<_>>();
    while level.len() > 1 {
        level = if level.len() == 2 {
            vec![node_hash(hash, &level[0], &level[1])]
        } else {
            level
                .chunks_exact(4)
                .map(|children| node_hash4(hash, children.try_into().unwrap()))
                .collect()
        };
    }
    level[0]
}

pub fn state_only_layer0_roots(
    c1_leaves: &[[u8; STATE_ONLY_C1_LEAF_BYTES]],
    c2_leaves: &[[u8; STATE_ONLY_C2_LEAF_BYTES]],
    hash: HashFn,
) -> Result<([u8; 32], [u8; 32]), CircleCandidateError> {
    if c1_leaves.is_empty()
        || c1_leaves.len() != c2_leaves.len()
        || !c1_leaves.len().is_power_of_two()
    {
        return Err(CircleCandidateError::CombinedLength {
            expected: c1_leaves.len(),
            actual: c2_leaves.len(),
        });
    }
    Ok((
        hybrid_root(c1_leaves, M31_CIRCLE_COMBINED_LAYER_TAG_BASE, hash),
        hybrid_root(c2_leaves, M31_CIRCLE_C2_LAYER_TAG, hash),
    ))
}

pub fn gamma_combine_state_only_codewords(
    c1: &[Vec<M31>],
    c2: &[Vec<QM31>],
    gamma: QM31,
    codeword_len: usize,
) -> Result<Vec<QM31>, CircleCandidateError> {
    validate(c1, STATE_ONLY_C1_COLUMNS, codeword_len)?;
    validate(c2, STATE_ONLY_C2_COLUMNS, codeword_len)?;
    let powers = qm31_power_table::<STATE_ONLY_TOTAL_COLUMNS>(gamma);
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

pub fn gamma_combine_state_only_messages(
    c1: &[Vec<M31>],
    c2: &[Vec<QM31>],
    gamma: QM31,
) -> Result<Vec<QM31>, CircleCandidateError> {
    gamma_combine_state_only_codewords(c1, c2, gamma, 1 << 10)
}
