//! Transcript-order-correct construction of the real v5 layer-zero trees.
//!
//! The monolithic [`super::spend_messages::build_v5_spend_messages`] helper
//! accepts `lambda` and `chi` before either layer-zero root exists. That is
//! useful for isolated encoding tests, but it cannot be called in the real
//! Fiat--Shamir order: `lambda` and `chi` are sampled immediately after the
//! C1 root is absorbed, and the Hcopy lane that uses them lives in C2.
//!
//! This module exposes that missing seam without changing any atomic-v3 or v4
//! source:
//!
//! 1. build the real witness trace, apply Component A, encode C1, and commit;
//! 2. absorb [`V5CommittedC1::root`] and sample `lambda, chi`;
//! 3. build Hcopy plus Components B/C, encode C2, and commit.
//!
//! Both artifacts retain their messages, codewords, packed leaf values, and
//! Merkle trees. A later transcript/proof builder can therefore form claims,
//! gamma-combine the nineteen lanes, and serialize q18 openings without
//! rebuilding or trusting proof-carried roots.

use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::field::{M31, QM31};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::HashFn;
use aspis_statement::atomic_state_only_registry::build_atomic_state_only_copy_helper_v3;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::atomic_state_only_trace::build_atomic_state_only_trace_v3;
use aspis_statement::{
    binary_successor_point, state_only_copy_helper_sum, xor12_point, AtomicPaymentStatementV4,
    SpendWitness, StateOnlyTraceFoundation,
};

use super::component_c::{v5_c_inactive_functional, V5ComponentCLane};
use super::spend_messages::{
    V5SpendMessageError, V5SpendMessages, V5StructuredBLane, V5_C1_LANES, V5_C1_LEAF_BYTES,
    V5_C2_LANES, V5_C2_LEAF_BYTES, V5_FIBRE_SLOTS, V5_LAYER_ZERO_BINARY_DEPTH,
    V5_LAYER_ZERO_LEAVES,
};
use super::{
    atomic_m31_block_mask_coefficient_sum, mask_m31_column, M31BlockMask, V5_CODEWORD_LEN,
    V5_DOMAIN_LOG, V5_TRACE_ROWS,
};
use crate::circle_candidate::CircleEncoder;
use crate::state_only_hiding::apply_atomic_state_only_h1_padding_mask_v3;
use crate::state_only_private_openings::{
    build_state_only_private_merkle_tree, StateOnlyPrivateMerkleTree,
};

const _: () = assert!(V5_C1_LANES == 16);
const _: () = assert!(V5_C2_LANES == 3);
const _: () = assert!(V5_LAYER_ZERO_LEAVES * V5_C1_LEAF_BYTES == (1 << 17) * 256);
const _: () = assert!(V5_LAYER_ZERO_LEAVES * V5_C2_LEAF_BYTES == (1 << 17) * 192);

pub const V5_RELATION_POINT_CLAIMS: usize = 3;
pub const V5_RELATION_CLAIMS_PER_LANE: usize = 4;
pub const V5_RELATION_LANES: usize = V5_C1_LANES + V5_C2_LANES;
pub const V5_RELATION_CLAIM_VALUES: usize = V5_RELATION_CLAIMS_PER_LANE * V5_RELATION_LANES;
pub const V5_RELATION_CLAIM_BYTES: usize = V5_RELATION_CLAIM_VALUES * 16;

const _: () = assert!(V5_RELATION_LANES == 19);
const _: () = assert!(V5_RELATION_CLAIM_VALUES == 76);
const _: () = assert!(V5_RELATION_CLAIM_BYTES == 1_216);

/// Real masked semantic trace and its authenticated C1 codewords.
///
/// Keeping the trace is intentional: Hcopy must be constructed from these
/// exact masked semantic columns only after the transcript supplies
/// `lambda, chi`.
pub struct V5CommittedC1 {
    pub trace: StateOnlyTraceFoundation,
    pub encoded: Vec<Vec<M31>>,
    pub packed_values: Vec<u8>,
    pub tree: StateOnlyPrivateMerkleTree,
}

impl V5CommittedC1 {
    pub fn root(&self) -> [u8; 32] {
        self.tree.root()
    }

    pub fn messages(&self) -> &[Vec<M31>; V5_C1_LANES] {
        &self.trace.c1
    }
}

/// Post-`lambda, chi` Hcopy/B/C messages and their authenticated C2 codewords.
pub struct V5CommittedC2 {
    pub messages: [Vec<QM31>; V5_C2_LANES],
    pub encoded: Vec<Vec<QM31>>,
    pub packed_values: Vec<u8>,
    pub tree: StateOnlyPrivateMerkleTree,
}

impl V5CommittedC2 {
    pub fn root(&self) -> [u8; 32] {
        self.tree.root()
    }
}

/// Both real layer-zero commitments in transcript construction order.
pub struct V5SplitLayerZero {
    pub c1: V5CommittedC1,
    pub c2: V5CommittedC2,
}

impl V5SplitLayerZero {
    pub fn roots(&self) -> ([u8; 32], [u8; 32]) {
        (self.c1.root(), self.c2.root())
    }

    /// Clone the complete nineteen message words into the existing PCS API.
    /// The split artifacts remain alive so their Merkle trees can later emit
    /// openings for transcript-derived queries.
    pub fn messages(&self) -> V5SpendMessages {
        V5SpendMessages {
            c1: self.c1.trace.c1.clone(),
            c2: self.c2.messages.clone(),
        }
    }
}

/// The four authenticated linear claims for each real v5 lane.
///
/// The first three rows are MLE values at `z`, `successor(z)`, and
/// `xor12(z)`. The fourth row is the structured degree-27 Component-B
/// terminal functional. Applying that same public functional to every lane
/// lets one gamma-combined PCS relation authenticate all nineteen fourth
/// claims without a separate opening pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5RelationClaims {
    pub points: [[QM31; 10]; V5_RELATION_POINT_CLAIMS],
    pub terminal_covector: Vec<QM31>,
    /// Canonical wire order: `point * 19 + lane`.
    pub point_major: [[QM31; V5_RELATION_LANES]; V5_RELATION_CLAIMS_PER_LANE],
}

impl V5RelationClaims {
    pub fn encode_point_major(&self) -> [u8; V5_RELATION_CLAIM_BYTES] {
        let mut bytes = [0u8; V5_RELATION_CLAIM_BYTES];
        for point in 0..V5_RELATION_CLAIMS_PER_LANE {
            for lane in 0..V5_RELATION_LANES {
                let index = point * V5_RELATION_LANES + lane;
                self.point_major[point][lane]
                    .write_le_bytes(&mut bytes[index * 16..index * 16 + 16]);
            }
        }
        bytes
    }
}

/// Row-basis functional whose value on Component B is the chained mask's
/// terminal evaluation at `point`.
pub fn v5_structured_terminal_covector(point: &[QM31; 10]) -> Vec<QM31> {
    use super::spend_messages::{
        V5_B_INITIAL_CLAIM_ROW, V5_B_ROUND_BLOCKS, V5_B_ROUND_BLOCK_ROWS, V5_B_ROUND_COEFFICIENTS,
    };

    let half = QM31::ONE.half();
    let mut half_powers = [QM31::ONE; 11];
    let mut exponent = 1usize;
    while exponent < half_powers.len() {
        half_powers[exponent] = half_powers[exponent - 1].mul(half);
        exponent += 1;
    }
    let mut covector = vec![QM31::ZERO; V5_TRACE_ROWS];
    covector[V5_B_INITIAL_CLAIM_ROW] = half_powers[10];
    let mut round = 0usize;
    while round < point.len() {
        let challenge = point[round];
        let scale = half_powers[9 - round];
        let start = V5_B_ROUND_BLOCKS[round] * V5_B_ROUND_BLOCK_ROWS;
        let mut power = QM31::ONE;
        let mut offset = 0usize;
        while offset < V5_B_ROUND_COEFFICIENTS {
            covector[start + offset] = scale.mul(power);
            power = power.mul(challenge);
            offset += 1;
        }
        round += 1;
    }
    covector
}

/// Evaluate the four authenticated claims for the committed Component-B
/// message.  This is kept as a small production helper so the exact consumer
/// of the shared MLE evaluator can be extracted independently of the Merkle
/// and transcript containers around [`V5SplitLayerZero`].
fn evaluate_component_b_relation_claims(
    c2_messages: &[Vec<QM31>; V5_C2_LANES],
    points: &[[QM31; 10]; V5_RELATION_POINT_CLAIMS],
    terminal_covector: &[QM31],
) -> [QM31; V5_RELATION_CLAIMS_PER_LANE] {
    let message = &c2_messages[1];
    let mut claims = [QM31::ZERO; V5_RELATION_CLAIMS_PER_LANE];
    claims[0] = crate::multilinear_eval_extension(message, &points[0]);
    claims[1] = crate::multilinear_eval_extension(message, &points[1]);
    claims[2] = crate::multilinear_eval_extension(message, &points[2]);

    let mut terminal = QM31::ZERO;
    let mut row = 0usize;
    while row < message.len() && row < terminal_covector.len() {
        terminal = terminal.add(terminal_covector[row].mul(message[row]));
        row += 1;
    }
    claims[V5_RELATION_POINT_CLAIMS] = terminal;
    claims
}

/// Evaluate the complete point-major 4x19 claim table from retained real
/// messages. No claim is supplied by the proof builder independently of the
/// committed words.
pub fn build_v5_relation_claims(layer_zero: &V5SplitLayerZero, z: &[QM31; 10]) -> V5RelationClaims {
    let points = [*z, binary_successor_point(z), xor12_point(z)];
    let terminal_covector = v5_structured_terminal_covector(z);
    let mut point_major = [[QM31::ZERO; V5_RELATION_LANES]; V5_RELATION_CLAIMS_PER_LANE];

    for (lane, message) in layer_zero.c1.messages().iter().enumerate() {
        for point in 0..V5_RELATION_POINT_CLAIMS {
            point_major[point][lane] = crate::multilinear_eval(message, &points[point]);
        }
        point_major[V5_RELATION_POINT_CLAIMS][lane] = message
            .iter()
            .copied()
            .zip(terminal_covector.iter().copied())
            .fold(QM31::ZERO, |sum, (value, weight)| {
                sum.add(weight.mul_m31(value))
            });
    }
    for (helper, message) in layer_zero.c2.messages.iter().enumerate() {
        let lane = V5_C1_LANES + helper;
        if helper == 1 {
            let component_b_claims = evaluate_component_b_relation_claims(
                &layer_zero.c2.messages,
                &points,
                &terminal_covector,
            );
            for claim in 0..V5_RELATION_CLAIMS_PER_LANE {
                point_major[claim][lane] = component_b_claims[claim];
            }
        } else {
            for point in 0..V5_RELATION_POINT_CLAIMS {
                point_major[point][lane] =
                    crate::multilinear_eval_extension(message, &points[point]);
            }
            point_major[V5_RELATION_POINT_CLAIMS][lane] = message
                .iter()
                .copied()
                .zip(terminal_covector.iter().copied())
                .fold(QM31::ZERO, |sum, (value, weight)| {
                    sum.add(weight.mul(value))
                });
        }
    }

    V5RelationClaims {
        points,
        terminal_covector,
        point_major,
    }
}

fn atomic_inactive(row: usize) -> bool {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    masks[row >> 4] & (1 << (row & 15)) != 0
}

fn atomic_inactive_sum_m31(values: &[M31]) -> Option<M31> {
    (values.len() == V5_TRACE_ROWS).then(|| {
        values
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| atomic_inactive(*row))
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value))
    })
}

fn atomic_inactive_sum_qm31(values: &[QM31]) -> Option<QM31> {
    (values.len() == V5_TRACE_ROWS).then(|| {
        values
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| atomic_inactive(*row))
            .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
    })
}

fn apply_component_a(
    trace: &mut StateOnlyTraceFoundation,
    masks: &[M31BlockMask; V5_C1_LANES],
) -> Result<(), V5SpendMessageError> {
    for (lane, mask) in masks.iter().enumerate() {
        if atomic_m31_block_mask_coefficient_sum(mask) != M31::ZERO {
            return Err(V5SpendMessageError::ComponentARelation { lane });
        }
        let before =
            atomic_inactive_sum_m31(&trace.c1[lane]).ok_or(V5SpendMessageError::MessageShape)?;
        let masked = mask_m31_column(&trace.c1[lane], mask)?;
        let after = atomic_inactive_sum_m31(&masked).ok_or(V5SpendMessageError::MessageShape)?;
        if before != after {
            return Err(V5SpendMessageError::ComponentARelation { lane });
        }
        trace.c1[lane] = masked;
    }
    Ok(())
}

fn encode_c1(messages: &[Vec<M31>; V5_C1_LANES]) -> Result<Vec<Vec<M31>>, V5SpendMessageError> {
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    messages
        .iter()
        .map(|message| encoder.encode_c1_message(message).map_err(Into::into))
        .collect()
}

fn encode_c2(messages: &[Vec<QM31>; V5_C2_LANES]) -> Result<Vec<Vec<QM31>>, V5SpendMessageError> {
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    messages
        .iter()
        .map(|message| encoder.encode_c2_message(message).map_err(Into::into))
        .collect()
}

fn pack_c1(encoded: &[Vec<M31>]) -> Result<Vec<u8>, V5SpendMessageError> {
    if encoded.len() != V5_C1_LANES || encoded.iter().any(|column| column.len() != V5_CODEWORD_LEN)
    {
        return Err(V5SpendMessageError::MessageShape);
    }
    let mut values = Vec::with_capacity(V5_LAYER_ZERO_LEAVES * V5_C1_LEAF_BYTES);
    for fibre in 0..V5_LAYER_ZERO_LEAVES {
        for slot in 0..V5_FIBRE_SLOTS {
            let index = V5_FIBRE_SLOTS * fibre + slot;
            for column in encoded {
                values.extend_from_slice(&column[index].to_le_bytes());
            }
        }
    }
    Ok(values)
}

fn pack_c2(encoded: &[Vec<QM31>]) -> Result<Vec<u8>, V5SpendMessageError> {
    if encoded.len() != V5_C2_LANES || encoded.iter().any(|column| column.len() != V5_CODEWORD_LEN)
    {
        return Err(V5SpendMessageError::MessageShape);
    }
    let mut values = Vec::with_capacity(V5_LAYER_ZERO_LEAVES * V5_C2_LEAF_BYTES);
    for fibre in 0..V5_LAYER_ZERO_LEAVES {
        for helper in encoded {
            for slot in 0..V5_FIBRE_SLOTS {
                let index = V5_FIBRE_SLOTS * fibre + slot;
                let start = values.len();
                values.resize(start + 16, 0);
                helper[index].write_le_bytes(&mut values[start..start + 16]);
            }
        }
    }
    Ok(values)
}

/// Build and commit the real atomic-v3 semantic columns before `lambda, chi`.
pub fn build_and_commit_v5_c1(
    statement: &AtomicPaymentStatementV4,
    witness: &SpendWitness,
    component_a: &[M31BlockMask; V5_C1_LANES],
    salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    hash: HashFn,
) -> Result<V5CommittedC1, V5SpendMessageError> {
    let mut atomic = build_atomic_state_only_trace_v3(statement, witness)?;
    let mut trace = core::mem::take(&mut atomic.trace);
    apply_component_a(&mut trace, component_a)?;
    let encoded = encode_c1(&trace.c1)?;
    let packed_values = pack_c1(&encoded)?;
    let tree = build_state_only_private_merkle_tree(
        hash,
        V5_LAYER_ZERO_BINARY_DEPTH,
        CIRCLE_C1_LAYER0_TAG,
        V5_C1_LEAF_BYTES,
        &packed_values,
        salts,
    )?;
    Ok(V5CommittedC1 {
        trace,
        encoded,
        packed_values,
        tree,
    })
}

/// Build and commit Hcopy/B/C after the transcript has sampled `lambda, chi`.
pub fn build_and_commit_v5_c2(
    c1: &V5CommittedC1,
    hcopy_padding: &[QM31; V5_TRACE_ROWS],
    component_b: &V5StructuredBLane,
    component_c: &V5ComponentCLane,
    lambda: QM31,
    chi: QM31,
    salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    hash: HashFn,
) -> Result<V5CommittedC2, V5SpendMessageError> {
    let mut hcopy = build_atomic_state_only_copy_helper_v3(&c1.trace, lambda, chi)?;
    apply_atomic_state_only_h1_padding_mask_v3(&mut hcopy, hcopy_padding)?;
    if state_only_copy_helper_sum(&hcopy) != Some(QM31::ZERO)
        || atomic_inactive_sum_qm31(&hcopy) != Some(QM31::ZERO)
    {
        return Err(V5SpendMessageError::HcopyRelation);
    }
    if atomic_inactive_sum_qm31(component_b.values()) != Some(component_b.pivot_pad()) {
        return Err(V5SpendMessageError::ComponentBRelation);
    }
    if v5_c_inactive_functional(component_c.values()) != QM31::ZERO {
        return Err(V5SpendMessageError::ComponentCRelation);
    }
    let messages = [
        hcopy,
        component_b.values().to_vec(),
        component_c.values().to_vec(),
    ];
    let encoded = encode_c2(&messages)?;
    let packed_values = pack_c2(&encoded)?;
    let tree = build_state_only_private_merkle_tree(
        hash,
        V5_LAYER_ZERO_BINARY_DEPTH,
        CIRCLE_C2_LAYER0_TAG,
        V5_C2_LEAF_BYTES,
        &packed_values,
        salts,
    )?;
    Ok(V5CommittedC2 {
        messages,
        encoded,
        packed_values,
        tree,
    })
}

/// Convenience wrapper for callers that have already replayed the C1-root
/// transcript boundary and now hold `lambda, chi`.
#[allow(clippy::too_many_arguments)]
pub fn finish_v5_split_layer_zero(
    c1: V5CommittedC1,
    hcopy_padding: &[QM31; V5_TRACE_ROWS],
    component_b: &V5StructuredBLane,
    component_c: &V5ComponentCLane,
    lambda: QM31,
    chi: QM31,
    c2_salts: &[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]],
    hash: HashFn,
) -> Result<V5SplitLayerZero, V5SpendMessageError> {
    let c2 = build_and_commit_v5_c2(
        &c1,
        hcopy_padding,
        component_b,
        component_c,
        lambda,
        chi,
        c2_salts,
        hash,
    )?;
    Ok(V5SplitLayerZero { c1, c2 })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, P};
    use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment, Digest, MerklePath,
        SpendPublic,
    };

    use crate::v5_mask::spend_messages::{build_v5_spend_messages, V5_B_PAD_COORDINATES};
    use crate::v5_mask::{sample_atomic_m31_lane_masks, Qm31WordSource};
    use crate::v5_sumcheck_mask::V5SumcheckMask;
    use crate::HOST_HASH;

    struct XorShift(u64);

    impl Qm31WordSource for XorShift {
        fn next_word(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            (x >> 21) as u32 % P
        }
    }

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture() -> (AtomicPaymentStatementV4, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
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
        let input = note_commitment(
            &derive_owner_key(&nullifier_key),
            value,
            asset_id,
            &input_salt,
        );
        let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
        let statement = AtomicPaymentStatementV4 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
            deployment_domain: [0x5d; 32],
        };
        (statement, witness)
    }

    fn hcopy_padding() -> [QM31; V5_TRACE_ROWS] {
        let mut active = [false; V5_TRACE_ROWS];
        for &row in atomic_state_only_copy_active_rows_v3() {
            active[usize::from(row)] = true;
        }
        let pivot = (0..V5_TRACE_ROWS).find(|row| !active[*row]).unwrap();
        let mut padding = [QM31::ZERO; V5_TRACE_ROWS];
        let mut sum = QM31::ZERO;
        for row in 0..V5_TRACE_ROWS {
            if !active[row] && row != pivot {
                padding[row] = q(10_000 + row as u32);
                sum = sum.add(padding[row]);
            }
        }
        padding[pivot] = sum.neg();
        padding
    }

    fn salts(domain: u8) -> Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]> {
        (0..V5_LAYER_ZERO_LEAVES)
            .map(|leaf| {
                core::array::from_fn(|byte| {
                    domain
                        .wrapping_add((leaf as u8).wrapping_mul(37))
                        .wrapping_add((byte as u8).wrapping_mul(19))
                })
            })
            .collect()
    }

    #[test]
    fn component_b_relation_claims_select_exact_c2_lane_one() {
        let lane_zero = q(71_001);
        let lane_one = q(71_002);
        let lane_two = q(71_003);
        let mut messages: [Vec<QM31>; V5_C2_LANES] =
            core::array::from_fn(|_| vec![QM31::ZERO; V5_TRACE_ROWS]);
        messages[0][0] = lane_zero;
        messages[1][0] = lane_one;
        messages[2][0] = lane_two;
        let points = [[QM31::ZERO; 10]; V5_RELATION_POINT_CLAIMS];
        let terminal_covector = vec![QM31::ZERO; V5_TRACE_ROWS];

        let claims = evaluate_component_b_relation_claims(&messages, &points, &terminal_covector);
        assert_eq!(claims[0], lane_one);
        assert_eq!(claims[1], lane_one);
        assert_eq!(claims[2], lane_one);
        assert_eq!(claims[3], QM31::ZERO);

        messages.swap(0, 1);
        let wrong_lane =
            evaluate_component_b_relation_claims(&messages, &points, &terminal_covector);
        assert_eq!(wrong_lane[0], lane_zero);
        assert_ne!(wrong_lane[0], claims[0]);
    }

    #[test]
    fn split_order_matches_monolithic_messages_and_real_tree_widths() {
        let (statement, witness) = fixture();
        let mut a_sources: [XorShift; V5_C1_LANES] =
            core::array::from_fn(|lane| XorShift(0xa531_0000_0000_0001 ^ lane as u64));
        let component_a = sample_atomic_m31_lane_masks(&mut a_sources).unwrap();
        let padding = hcopy_padding();
        let b_mask = V5SumcheckMask::sample(&mut XorShift(0xb500_0000_0000_0001)).unwrap();
        let b_pads: [QM31; V5_B_PAD_COORDINATES] =
            core::array::from_fn(|index| q(20_000 + index as u32));
        let component_b = V5StructuredBLane::encode(&b_mask, &b_pads, q(29_999)).unwrap();
        let component_c = V5ComponentCLane::sample(&mut XorShift(0xc500_0000_0000_0001)).unwrap();
        let c1_salts = salts(0xc1);
        let c2_salts = salts(0xc2);

        // This root exists before either challenge is supplied to C2.
        let c1 = build_and_commit_v5_c1(&statement, &witness, &component_a, &c1_salts, HOST_HASH)
            .unwrap();
        let c1_root = c1.root();
        assert_ne!(c1_root, [0u8; 32]);
        let lambda = q(40_001);
        let chi = q(40_002);
        let split = finish_v5_split_layer_zero(
            c1,
            &padding,
            &component_b,
            &component_c,
            lambda,
            chi,
            &c2_salts,
            HOST_HASH,
        )
        .unwrap();

        let monolithic = build_v5_spend_messages(
            &statement,
            &witness,
            &component_a,
            &padding,
            &component_b,
            &component_c,
            lambda,
            chi,
        )
        .unwrap();
        assert_eq!(split.messages(), monolithic);
        assert_eq!(split.c1.root(), c1_root);
        assert_ne!(split.c2.root(), [0u8; 32]);
        assert_eq!(split.c1.encoded.len(), V5_C1_LANES);
        assert_eq!(split.c2.encoded.len(), V5_C2_LANES);
        assert_eq!(
            split.c1.packed_values.len(),
            V5_LAYER_ZERO_LEAVES * V5_C1_LEAF_BYTES
        );
        assert_eq!(
            split.c2.packed_values.len(),
            V5_LAYER_ZERO_LEAVES * V5_C2_LEAF_BYTES
        );
        assert_eq!(split.c1.tree.value_width(), V5_C1_LEAF_BYTES);
        assert_eq!(split.c2.tree.value_width(), V5_C2_LEAF_BYTES);

        let z = core::array::from_fn(|coordinate| q(50_000 + coordinate as u32));
        let claims = build_v5_relation_claims(&split, &z);
        assert_eq!(claims.encode_point_major().len(), V5_RELATION_CLAIM_BYTES);
        assert_eq!(claims.points[0], z);
        assert_eq!(claims.points[1], binary_successor_point(&z));
        assert_eq!(claims.points[2], xor12_point(&z));
        assert_eq!(claims.point_major[3][V5_C1_LANES + 1], b_mask.evaluate(&z));

        // The affine pivot direction is committed by C2 and changes the
        // inactive claim by exactly gamma^17 * delta at fixed gamma, while the
        // compact structured terminal remains blind to row 993.
        let replacement_pad = q(30_000);
        let replacement_b = V5StructuredBLane::encode(&b_mask, &b_pads, replacement_pad).unwrap();
        let replacement_c2 = build_and_commit_v5_c2(
            &split.c1,
            &padding,
            &replacement_b,
            &component_c,
            lambda,
            chi,
            &c2_salts,
            HOST_HASH,
        )
        .unwrap();
        assert_ne!(replacement_c2.root(), split.c2.root());

        let replacement_messages = build_v5_spend_messages(
            &statement,
            &witness,
            &component_a,
            &padding,
            &replacement_b,
            &component_c,
            lambda,
            chi,
        )
        .unwrap();
        let gamma = q(60_001);
        let original_combined =
            crate::v5_mask::spend_messages::gamma_combine_v5_messages(&monolithic, gamma).unwrap();
        let replacement_combined =
            crate::v5_mask::spend_messages::gamma_combine_v5_messages(&replacement_messages, gamma)
                .unwrap();
        let original_claim = atomic_inactive_sum_qm31(&original_combined).unwrap();
        let replacement_claim = atomic_inactive_sum_qm31(&replacement_combined).unwrap();
        let delta = replacement_pad.add(component_b.pivot_pad().neg());
        assert_eq!(
            replacement_claim.add(original_claim.neg()),
            gamma.pow((V5_C1_LANES + 1) as u64).mul(delta)
        );

        let terminal = |values: &[QM31]| {
            values
                .iter()
                .copied()
                .zip(claims.terminal_covector.iter().copied())
                .fold(QM31::ZERO, |sum, (value, weight)| {
                    sum.add(weight.mul(value))
                })
        };
        assert_eq!(
            terminal(component_b.values()),
            terminal(replacement_b.values())
        );
    }
}
