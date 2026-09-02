//! Host-side builder for the V6 26+3 one-fold proof.
//!
//! The production API always mines all three work witnesses. The lower-level
//! unmined fixture API is compiled only for tests or the explicitly insecure
//! fixture feature.

use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::merkle::node_hash;
use aspis_core::proof::M31_CIRCLE_BASIS_DISCRIMINATOR;
use aspis_core::state_only_hiding::{
    begin_state_only_hiding_precommit, begin_state_only_masked_sumcheck, StateOnlyHidingContext,
    PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
};
use aspis_core::state_only_private_merkle::private_leaf_hash;
use aspis_core::state_only_sumcheck::{
    begin_state_only_zerocheck, evaluate_state_only_polynomial, state_only_boundary_sum,
    StateOnlySumcheckPolynomial,
};
use aspis_core::sumcheck::{
    boundary_sum, evaluate, polynomial_for_extension, SumcheckPolynomial, WeightAccumulator,
};
use aspis_core::transcript::{label, Transcript};
use aspis_core::v6_onefold::{
    binary_frontier_nodes, fold_v6_onefold_queries, prepare_v6_onefold_coordinates,
    verify_and_gamma_combine_v6_binary_openings_prepared, V6OneFoldWire, V6WireError,
    V6_BODY_WITHOUT_FRONTIERS, V6_C1_PACKED_BYTES_PER_QUERY, V6_C1_TREE_TAG,
    V6_C2_PACKED_BYTES_PER_QUERY, V6_C2_TREE_TAG, V6_FINAL_QM31_OFFSET, V6_FINAL_QM31_VALUES,
    V6_FIXED_M31_LIMBS, V6_FIXED_PACKED_FIELD_BYTES, V6_FRONTIER_CAP_PER_TREE, V6_HARD_BODY_LIMIT,
    V6_INACTIVE_CLAIM_QM31_OFFSET, V6_INITIAL_CLAIM_OFFSET, V6_OOD_QM31_OFFSET,
    V6_POINT_CLAIMS_QM31_OFFSET, V6_POINT_CLAIM_ROWS, V6_QUERY_COUNT, V6_RELATION_QM31_OFFSET,
    V6_RELATION_ROUNDS, V6_RELATION_SENT_VALUES, V6_SEMANTIC_QM31_OFFSET, V6_SEMANTIC_ROUNDS,
    V6_SEMANTIC_SENT_VALUES, V6_TOTAL_COLUMNS,
};
use aspis_core::v6_query_batch::{
    add_v6_final256_query_batch, add_v7_final256_query_batch_shifted, V6AuthenticatedQueryBatch,
};
use aspis_core::v6_transcript::{
    v6_statement_points, verify_v6_transcript_and_relation,
    verify_v7_compact_transcript_and_relation_prepared,
    verify_v7_compact_transcript_and_relation_prepared_with_hiding_context, V6SemanticView,
    V6TranscriptContext, V6VerifiedTranscript, V6_BATCH_WORK_BITS, V6_COMPACT_DRAW_CAP,
    V6_FINAL_WORK_BITS, V6_FOLD_WORK_BITS, V6_PROFILE_BINDING, V6_QUERY_DRAW_LIMIT,
    V6_QUERY_SELECTOR_COUNT, V6_TREE_DEPTH,
};
use aspis_core::v7_merkle208::{
    node_hash_v7, private_leaf_hash_v7, V7Digest, V7_C1_TREE_TAG, V7_C2_TREE_TAG,
};
use aspis_core::v7_onefold::{
    derive_first_v7_compact_queries, verify_and_gamma_combine_v7_openings, V7CompactOneFoldWire,
    V7_COMPACT_BATCH_WORK_BITS, V7_COMPACT_BODY_WITHOUT_FRONTIERS, V7_COMPACT_DIGEST_BYTES,
    V7_COMPACT_FINAL_WORK_BITS, V7_COMPACT_FOLD_WORK_BITS, V7_COMPACT_MAX_BODY_BYTES,
    V7_COMPACT_PROFILE_BINDING,
};
use aspis_core::HashFn;
use aspis_statement::atomic_state_only_registry::build_atomic_state_only_copy_helper_v3;
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_group_masks_v3, atomic_state_only_copy_inactive_row_groups_v3,
    atomic_state_only_copy_inactive_row_masks_v3,
    atomic_state_only_selected_masked_terminal_value_compiled_tag73,
    atomic_state_only_selected_masked_terminal_value_compiled_v3,
    atomic_state_only_selected_unmasked_terminal_value_compiled_tag73,
    atomic_state_only_selected_unmasked_terminal_value_compiled_v3,
};
use aspis_statement::atomic_state_only_trace::build_atomic_state_only_trace_v3;
use aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1;
use aspis_statement::pool_v1::payment_semantic_oracle::{
    build_pool_v1_payment_copy_helper_v1, prepare_pool_v1_payment_semantic_oracle_v1,
};
use aspis_statement::{
    atomic_payment_statement_digest_v4, multilinear_evaluate_qm31,
    pool_v1::{
        build_pool_v1_private_transfer_trace_v1, build_pool_v1_withdrawal_trace_v1,
        compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
        compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
        evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_private_transfer_selected_unmasked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1,
        evaluate_pool_v1_withdrawal_selected_unmasked_terminal_compiled_tag73_v1,
        pool_v1_pair_forest_copy_active_row_masks_v1,
        pool_v1_private_transfer_copy_active_row_masks_compiled_v1,
        pool_v1_withdrawal_copy_active_row_masks_compiled_v1,
        PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairForestTraceV1,
        PoolV1PairForestWithdrawalWitnessV1, PoolV1PairLatePublicStatementV1,
        PoolV1PaymentRelationContextV1, PoolV1PaymentTraceVariantV1, PoolV1PrivateTransferPublicV1,
        PoolV1PrivateTransferWitnessV1, PoolV1WithdrawalPublicV1, PoolV1WithdrawalWitnessV1,
    },
    state_only_copy_helper_sum, AtomicPaymentStatementV4, SpendWitness,
};

use crate::circle_candidate::{
    fold_adjacent_natural_arity4, fold_candidate_codeword_round_for_domain_log, CircleEncoder,
};
use crate::state_only_candidate::encode_state_only_c1_columns;
use crate::state_only_candidate_prefix::{statement_evaluations, StateOnlyPowMode};
use crate::state_only_entropy::{ReservedStateOnlyAttemptSecrets, StateOnlyAttemptSecrets};
use crate::state_only_hiding::{
    apply_atomic_state_only_h1_padding_mask_v3, apply_atomic_state_only_mask_material_v3,
    apply_pool_v1_pair_forest_h1_padding_mask_v1, apply_pool_v1_pair_forest_mask_material_v1,
    apply_pool_v1_private_transfer_h1_padding_mask_v1,
    apply_pool_v1_private_transfer_mask_material_v1, apply_pool_v1_withdrawal_h1_padding_mask_v1,
    apply_pool_v1_withdrawal_mask_material_v1, state_only_initial_mask_claim,
    state_only_mask_oracle_value, StateOnlyMaskNonceStore,
};
use crate::state_only_spend_candidate::{
    encode_state_only_spend_c2_columns, gamma_combine_state_only_spend_codewords,
    gamma_combine_state_only_spend_messages,
};

const V6_DOMAIN_LOG: u32 = 20;
const V6_LEAF_COUNT: usize = 1usize << V6_TREE_DEPTH;
const V6_ROOT_SALT_DOMAIN: &[u8] = b"aspis-v6-public-root-salt-v1";
const V7_ROOT_SALT_DOMAIN: &[u8] = b"aspis-v7-public-root-salt-v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V6ProverContext {
    pub program_id: [u8; 32],
    pub release_binding: [u8; 32],
    pub attempt_id: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6ProverError {
    AttemptIdMismatch,
    Stage(&'static str),
    NoCompactSchedule,
    Wire(V6WireError),
}

impl From<V6WireError> for V6ProverError {
    fn from(error: V6WireError) -> Self {
        Self::Wire(error)
    }
}

#[derive(Clone, Debug)]
pub struct BuiltV6OneFoldProof {
    pub bytes: Vec<u8>,
    pub selector: u8,
    pub compact_counter: u8,
    pub frontier_nodes: usize,
    pub queries: [u32; V6_QUERY_COUNT],
    pub work_nonces: [u64; 3],
    pub pow_valid: bool,
    pub transcript_state_after_queries: [u8; 32],
}

pub type V7ProverContext = V6ProverContext;

#[derive(Clone, Debug)]
pub struct BuiltV7CompactOneFoldProof {
    pub bytes: Vec<u8>,
    pub compact_counter: u8,
    pub frontier_nodes: usize,
    pub queries: [u32; V6_QUERY_COUNT],
    pub work_nonces: [u64; 3],
    pub pow_valid: bool,
    pub transcript_state_after_queries: [u8; 32],
    /// Number of ordinary valid final-work nonces inspected by the
    /// measurement-only cutoff policy. One on the production path.
    pub final_work_valid_nonces_tested: u32,
    /// Explicit audit cutoff when final-nonce selection was enabled.
    pub final_work_counter_cutoff: Option<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OneFoldBuildProfile {
    V6,
    V7Compact,
}

#[derive(Clone, Copy)]
enum OneFoldRelation<'a> {
    Atomic {
        statement: &'a AtomicPaymentStatementV4,
        witness: &'a SpendWitness,
    },
    PoolPrivateTransfer {
        public: &'a PoolV1PrivateTransferPublicV1,
        witness: &'a PoolV1PrivateTransferWitnessV1,
        context: PoolV1PaymentRelationContextV1<'a>,
        statement_digest: [u8; 32],
    },
    PoolWithdrawal {
        public: &'a PoolV1WithdrawalPublicV1,
        witness: &'a PoolV1WithdrawalWitnessV1,
        context: PoolV1PaymentRelationContextV1<'a>,
        statement_digest: [u8; 32],
    },
    PoolForestPrivateTransfer {
        public: &'a PoolV1PrivateTransferPublicV1,
        witness: &'a PoolV1PairForestPrivateTransferWitnessV1,
        context: PoolV1PaymentRelationContextV1<'a>,
        transition: &'a PoolV1PairLatePublicStatementV1,
        statement_digest: [u8; 32],
    },
    PoolForestWithdrawal {
        public: &'a PoolV1WithdrawalPublicV1,
        witness: &'a PoolV1PairForestWithdrawalWitnessV1,
        context: PoolV1PaymentRelationContextV1<'a>,
        transition: &'a PoolV1PairLatePublicStatementV1,
        statement_digest: [u8; 32],
    },
}

#[derive(Clone, Debug)]
struct BuiltOneFoldProof {
    bytes: Vec<u8>,
    selector: u8,
    compact_counter: u8,
    frontier_nodes: usize,
    queries: [u32; V6_QUERY_COUNT],
    work_nonces: [u64; 3],
    pow_valid: bool,
    transcript_state_after_queries: [u8; 32],
    final_work_valid_nonces_tested: u32,
    final_work_counter_cutoff: Option<u8>,
}

impl From<BuiltOneFoldProof> for BuiltV6OneFoldProof {
    fn from(proof: BuiltOneFoldProof) -> Self {
        Self {
            bytes: proof.bytes,
            selector: proof.selector,
            compact_counter: proof.compact_counter,
            frontier_nodes: proof.frontier_nodes,
            queries: proof.queries,
            work_nonces: proof.work_nonces,
            pow_valid: proof.pow_valid,
            transcript_state_after_queries: proof.transcript_state_after_queries,
        }
    }
}

impl From<BuiltOneFoldProof> for BuiltV7CompactOneFoldProof {
    fn from(proof: BuiltOneFoldProof) -> Self {
        debug_assert_eq!(proof.selector, 0);
        Self {
            bytes: proof.bytes,
            compact_counter: proof.compact_counter,
            frontier_nodes: proof.frontier_nodes,
            queries: proof.queries,
            work_nonces: proof.work_nonces,
            pow_valid: proof.pow_valid,
            transcript_state_after_queries: proof.transcript_state_after_queries,
            final_work_valid_nonces_tested: proof.final_work_valid_nonces_tested,
            final_work_counter_cutoff: proof.final_work_counter_cutoff,
        }
    }
}

#[derive(Debug)]
struct BinaryMerkleTree {
    levels: Vec<Vec<[u8; 32]>>,
}

impl BinaryMerkleTree {
    fn from_leaf_hashes(hash: HashFn, leaves: Vec<[u8; 32]>) -> Result<Self, V6ProverError> {
        if leaves.len() != V6_LEAF_COUNT {
            return Err(V6ProverError::Stage("binary leaf count"));
        }
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let next = levels
                .last()
                .unwrap()
                .chunks_exact(2)
                .map(|pair| node_hash(hash, &pair[0], &pair[1]))
                .collect();
            levels.push(next);
        }
        Ok(Self { levels })
    }

    fn root(&self) -> [u8; 32] {
        self.levels.last().unwrap()[0]
    }

    fn frontier(&self, queries: [u32; V6_QUERY_COUNT]) -> Result<Vec<[u8; 32]>, V6ProverError> {
        let mut current = queries.to_vec();
        current.sort_unstable();
        if current.windows(2).any(|pair| pair[0] == pair[1])
            || current.last().copied().unwrap_or(u32::MAX) >= V6_LEAF_COUNT as u32
        {
            return Err(V6ProverError::Stage("binary query schedule"));
        }
        let mut frontier = Vec::new();
        for level in &self.levels[..self.levels.len() - 1] {
            let mut next = Vec::with_capacity(current.len());
            let mut index = 0usize;
            while index < current.len() {
                let node = current[index];
                if node & 1 == 0 && index + 1 < current.len() && current[index + 1] == node + 1 {
                    next.push(node >> 1);
                    index += 2;
                } else {
                    frontier.push(level[(node ^ 1) as usize]);
                    next.push(node >> 1);
                    index += 1;
                }
            }
            next.dedup();
            current = next;
        }
        if current != [0] {
            return Err(V6ProverError::Stage("binary frontier terminal"));
        }
        Ok(frontier)
    }
}

#[derive(Debug)]
struct BinaryMerkleTree216 {
    levels: Vec<Vec<V7Digest>>,
}

impl BinaryMerkleTree216 {
    fn from_leaf_hashes(hash: HashFn, leaves: Vec<V7Digest>) -> Result<Self, V6ProverError> {
        if leaves.len() != V6_LEAF_COUNT {
            return Err(V6ProverError::Stage("V7 binary leaf count"));
        }
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let next = levels
                .last()
                .unwrap()
                .chunks_exact(2)
                .map(|pair| node_hash_v7(hash, &pair[0], &pair[1]))
                .collect();
            levels.push(next);
        }
        Ok(Self { levels })
    }

    fn root(&self) -> V7Digest {
        self.levels.last().unwrap()[0]
    }

    fn frontier(&self, queries: [u32; V6_QUERY_COUNT]) -> Result<Vec<V7Digest>, V6ProverError> {
        let mut current = queries.to_vec();
        current.sort_unstable();
        if current.windows(2).any(|pair| pair[0] == pair[1])
            || current.last().copied().unwrap_or(u32::MAX) >= V6_LEAF_COUNT as u32
        {
            return Err(V6ProverError::Stage("V7 binary query schedule"));
        }
        let mut frontier = Vec::new();
        for level in &self.levels[..self.levels.len() - 1] {
            let mut next = Vec::with_capacity(current.len());
            let mut index = 0usize;
            while index < current.len() {
                let node = current[index];
                if node & 1 == 0 && index + 1 < current.len() && current[index + 1] == node + 1 {
                    next.push(node >> 1);
                    index += 2;
                } else {
                    frontier.push(level[(node ^ 1) as usize]);
                    next.push(node >> 1);
                    index += 1;
                }
            }
            next.dedup();
            current = next;
        }
        if current != [0] {
            return Err(V6ProverError::Stage("V7 binary frontier terminal"));
        }
        Ok(frontier)
    }
}

#[derive(Debug)]
enum ProfiledBinaryMerkleTree {
    V6(BinaryMerkleTree),
    V7Compact(BinaryMerkleTree216),
}

impl ProfiledBinaryMerkleTree {
    fn append_root(&self, output: &mut Vec<u8>) {
        match self {
            Self::V6(tree) => output.extend_from_slice(&tree.root()),
            Self::V7Compact(tree) => output.extend_from_slice(&tree.root()),
        }
    }

    fn frontier_bytes(&self, queries: [u32; V6_QUERY_COUNT]) -> Result<Vec<u8>, V6ProverError> {
        Ok(match self {
            Self::V6(tree) => tree
                .frontier(queries)?
                .into_iter()
                .flat_map(|node| node.into_iter())
                .collect(),
            Self::V7Compact(tree) => tree
                .frontier(queries)?
                .into_iter()
                .flat_map(|node| node.into_iter())
                .collect(),
        })
    }
}

fn pack_m31_words(words: impl IntoIterator<Item = u32>, count: usize) -> Vec<u8> {
    let mut output = Vec::with_capacity((31 * count + 7) / 8);
    let mut buffer = 0u64;
    let mut buffered = 0u32;
    let mut actual = 0usize;
    for word in words {
        debug_assert!(word < P);
        buffer |= u64::from(word) << buffered;
        buffered += 31;
        actual += 1;
        while buffered >= 8 {
            output.push(buffer as u8);
            buffer >>= 8;
            buffered -= 8;
        }
    }
    if buffered != 0 {
        output.push(buffer as u8);
    }
    debug_assert_eq!(actual, count);
    debug_assert_eq!(output.len(), (31 * count + 7) / 8);
    output
}

fn qm31_words(value: QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

fn pack_qm31_fields(fields: &[QM31]) -> Vec<u8> {
    pack_m31_words(
        fields.iter().copied().flat_map(qm31_words),
        4 * fields.len(),
    )
}

fn packed_c1_fiber(encoded: &[Vec<M31>], fiber: usize) -> Result<Vec<u8>, V6ProverError> {
    if encoded.len() != 26 || fiber >= V6_LEAF_COUNT {
        return Err(V6ProverError::Stage("C1 packed fibre shape"));
    }
    let words = (0..4).flat_map(|slot| {
        let codeword_index = 4 * fiber + slot;
        encoded.iter().map(move |column| column[codeword_index].0)
    });
    let packed = pack_m31_words(words, 4 * 26);
    if packed.len() != V6_C1_PACKED_BYTES_PER_QUERY {
        return Err(V6ProverError::Stage("C1 packed fibre width"));
    }
    Ok(packed)
}

fn packed_c2_fiber(encoded: &[Vec<QM31>], fiber: usize) -> Result<Vec<u8>, V6ProverError> {
    if encoded.len() != 3 || fiber >= V6_LEAF_COUNT {
        return Err(V6ProverError::Stage("C2 packed fibre shape"));
    }
    let words = encoded
        .iter()
        .flat_map(|helper| (0..4).flat_map(move |slot| qm31_words(helper[4 * fiber + slot])));
    let packed = pack_m31_words(words, 4 * 4 * 3);
    if packed.len() != V6_C2_PACKED_BYTES_PER_QUERY {
        return Err(V6ProverError::Stage("C2 packed fibre width"));
    }
    Ok(packed)
}

fn profile_root_salt(
    hash: HashFn,
    domain: &[u8],
    profile_binding: &[u8; 32],
    context: &V6TranscriptContext,
    tree_tag: u8,
) -> [u8; 32] {
    hash(&[
        domain,
        profile_binding,
        &context.program_id,
        &context.release_binding,
        &context.statement_digest,
        &context.attempt_id,
        &[tree_tag],
    ])
}

fn public_root_salt(hash: HashFn, context: &V6TranscriptContext, tree_tag: u8) -> [u8; 32] {
    profile_root_salt(
        hash,
        V6_ROOT_SALT_DOMAIN,
        &V6_PROFILE_BINDING,
        context,
        tree_tag,
    )
}

fn v7_public_root_salt(hash: HashFn, context: &V6TranscriptContext, tree_tag: u8) -> [u8; 32] {
    profile_root_salt(
        hash,
        V7_ROOT_SALT_DOMAIN,
        &V7_COMPACT_PROFILE_BINDING,
        context,
        tree_tag,
    )
}

fn begin_transcript_and_precommit(
    hash: HashFn,
    context: &V6TranscriptContext,
) -> Result<(Transcript, [u8; 32]), V6ProverError> {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &V6_PROFILE_BINDING);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    let mut deployment = [0u8; 64];
    deployment[..32].copy_from_slice(&context.program_id);
    deployment[32..].copy_from_slice(&context.release_binding);
    transcript.absorb(label::V6_DEPLOYMENT_CONTEXT, &deployment);
    transcript.absorb(label::STATEMENT, &context.statement_digest);
    let binding = begin_state_only_hiding_precommit(
        &mut transcript,
        StateOnlyHidingContext::atomic_spend_v3(context.statement_digest, context.attempt_id),
    )
    .map_err(|_| V6ProverError::Stage("V6 hiding precommit"))?;
    Ok((transcript, binding))
}

fn begin_v7_transcript_and_precommit(
    hash: HashFn,
    context: &V6TranscriptContext,
    hiding_context: StateOnlyHidingContext,
) -> Result<(Transcript, [u8; 32]), V6ProverError> {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &V7_COMPACT_PROFILE_BINDING);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    let mut deployment = [0u8; 64];
    deployment[..32].copy_from_slice(&context.program_id);
    deployment[32..].copy_from_slice(&context.release_binding);
    transcript.absorb(label::V7_DEPLOYMENT_CONTEXT, &deployment);
    transcript.absorb(label::STATEMENT, &context.statement_digest);
    let binding = begin_state_only_hiding_precommit(&mut transcript, hiding_context)
        .map_err(|_| V6ProverError::Stage("V7 hiding precommit"))?;
    Ok((transcript, binding))
}

fn absorb_c1_and_sample_copy_challenges(
    transcript: &mut Transcript,
    hash: HashFn,
    context: &V6TranscriptContext,
    c1_root: [u8; 32],
) -> Result<(QM31, QM31), V6ProverError> {
    let c1_salt = public_root_salt(hash, context, V6_C1_TREE_TAG);
    let mut c1_record = [0u8; 65];
    c1_record[0] = 0;
    c1_record[1..33].copy_from_slice(&c1_root);
    c1_record[33..].copy_from_slice(&c1_salt);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &c1_record);
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| V6ProverError::Stage("V6 lambda"))?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| V6ProverError::Stage("V6 chi"))?;

    Ok((lambda, chi))
}

fn absorb_c2_and_sample_batching(
    transcript: &mut Transcript,
    hash: HashFn,
    context: &V6TranscriptContext,
    c2_root: [u8; 32],
) -> Result<aspis_core::statement_sumcheck::PaymentConstraintChallenges, V6ProverError> {
    let c2_salt = public_root_salt(hash, context, V6_C2_TREE_TAG);
    let mut c2_record = [0u8; 64];
    c2_record[..32].copy_from_slice(&c2_root);
    c2_record[32..].copy_from_slice(&c2_salt);
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2_record);
    let batching = begin_state_only_zerocheck(transcript)
        .map_err(|_| V6ProverError::Stage("V6 zerocheck challenges"))?;
    Ok(batching)
}

fn absorb_v7_c1_and_sample_copy_challenges(
    transcript: &mut Transcript,
    hash: HashFn,
    context: &V6TranscriptContext,
    c1_root: V7Digest,
) -> Result<(QM31, QM31), V6ProverError> {
    let c1_salt = v7_public_root_salt(hash, context, V7_C1_TREE_TAG);
    let mut c1_record = [0u8; 1 + V7_COMPACT_DIGEST_BYTES + 32];
    c1_record[0] = 0;
    c1_record[1..1 + V7_COMPACT_DIGEST_BYTES].copy_from_slice(&c1_root);
    c1_record[1 + V7_COMPACT_DIGEST_BYTES..].copy_from_slice(&c1_salt);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &c1_record);
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| V6ProverError::Stage("V7 lambda"))?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| V6ProverError::Stage("V7 chi"))?;
    Ok((lambda, chi))
}

fn absorb_v7_c2_and_sample_batching(
    transcript: &mut Transcript,
    hash: HashFn,
    context: &V6TranscriptContext,
    c2_root: V7Digest,
) -> Result<aspis_core::statement_sumcheck::PaymentConstraintChallenges, V6ProverError> {
    let c2_salt = v7_public_root_salt(hash, context, V7_C2_TREE_TAG);
    let mut c2_record = [0u8; V7_COMPACT_DIGEST_BYTES + 32];
    c2_record[..V7_COMPACT_DIGEST_BYTES].copy_from_slice(&c2_root);
    c2_record[V7_COMPACT_DIGEST_BYTES..].copy_from_slice(&c2_salt);
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2_record);
    begin_state_only_zerocheck(transcript)
        .map_err(|_| V6ProverError::Stage("V7 zerocheck challenges"))
}

fn interpolate_degree27(values: &[QM31; 28]) -> StateOnlySumcheckPolynomial {
    let mut output = [QM31::ZERO; 28];
    for i in 0..28 {
        let mut basis = [QM31::ZERO; 28];
        basis[0] = QM31::ONE;
        let mut basis_degree = 0usize;
        let mut denominator = M31::ONE;
        for j in 0..28 {
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
        for coefficient in 0..28 {
            output[coefficient] = output[coefficient].add(scale.mul(basis[coefficient]));
        }
    }
    output
}

fn absorb_compact_semantic_round(
    transcript: &mut Transcript,
    round: usize,
    polynomial: &StateOnlySumcheckPolynomial,
) {
    let mut framed = [0u8; 1 + V6_SEMANTIC_SENT_VALUES * 16];
    framed[0] = round as u8;
    for sent in 0..V6_SEMANTIC_SENT_VALUES {
        let coefficient = if sent == 0 { 0 } else { sent + 1 };
        polynomial[coefficient].write_le_bytes(&mut framed[1 + sent * 16..][..16]);
    }
    transcript.absorb(label::V6_COMPACT_SEMANTIC_ROUND, &framed);
}

fn write_compact_semantic_fields(
    fields: &mut [QM31],
    round: usize,
    polynomial: &StateOnlySumcheckPolynomial,
) {
    let base = V6_SEMANTIC_QM31_OFFSET + round * V6_SEMANTIC_SENT_VALUES;
    fields[base] = polynomial[0];
    for sent in 1..V6_SEMANTIC_SENT_VALUES {
        fields[base + sent] = polynomial[sent + 1];
    }
}

fn evaluate_qm31_table(table: &[QM31], point: &[QM31; 10]) -> Result<QM31, V6ProverError> {
    multilinear_evaluate_qm31(table, point)
        .ok_or(V6ProverError::Stage("V6 D multilinear evaluation"))
}

fn point_claim_rows(
    trace: &aspis_statement::StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; 10],
    h1: &[QM31],
    g: &[QM31],
    d: &[QM31],
    point: &[QM31; 10],
) -> Result<[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS], V6ProverError> {
    let base = statement_evaluations(trace, mask_only_c1, h1, g, point)
        .map_err(|_| V6ProverError::Stage("V6 point claims"))?;
    let points = v6_statement_points(point);
    let mut claims = [[QM31::ZERO; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS];
    for row in 0..V6_POINT_CLAIM_ROWS {
        claims[row][..28].copy_from_slice(&base[row * 28..(row + 1) * 28]);
        claims[row][28] = evaluate_qm31_table(d, &points[row])?;
    }
    Ok(claims)
}

fn absorb_point_claims(
    transcript: &mut Transcript,
    fields: &mut [QM31],
    claims: &[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS],
) {
    let mut encoded = vec![0u8; V6_POINT_CLAIM_ROWS * V6_TOTAL_COLUMNS * 16];
    for row in 0..V6_POINT_CLAIM_ROWS {
        for column in 0..V6_TOTAL_COLUMNS {
            let ordinal = row * V6_TOTAL_COLUMNS + column;
            fields[V6_POINT_CLAIMS_QM31_OFFSET + ordinal] = claims[row][column];
            claims[row][column].write_le_bytes(&mut encoded[ordinal * 16..][..16]);
        }
    }
    transcript.absorb(label::V6_POINT_CLAIMS, &encoded);
}

fn absorb_work(transcript: &mut Transcript, stage: usize, nonce: u64) {
    match stage {
        0 => transcript.absorb(label::M31_PAYMENT_BATCH_POW_NONCE, &nonce.to_le_bytes()),
        1 => {
            let mut record = [0u8; 9];
            record[0] = 0;
            record[1..].copy_from_slice(&nonce.to_le_bytes());
            transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
        }
        2 => transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes()),
        _ => unreachable!(),
    }
}

fn work_nonce(
    transcript: &Transcript,
    bits: u8,
    mode: StateOnlyPowMode,
) -> Result<u64, V6ProverError> {
    match mode {
        StateOnlyPowMode::UnminedZero => Ok(0),
        StateOnlyPowMode::Mine => crate::pow::find_grinding_nonce_unpublished(transcript, bits)
            .map_err(|_| V6ProverError::Stage("V6 work mining")),
    }
}

#[cfg(feature = "v7-final-nonce-cutoff-audit")]
const V7_FINAL_NONCE_CUTOFF_ACK: &str = "I_ACKNOWLEDGE_MEASUREMENT_ONLY_FINAL_NONCE_SELECTION";

#[cfg(feature = "v7-final-nonce-cutoff-audit")]
fn requested_v7_final_nonce_cutoff() -> Result<Option<u8>, V6ProverError> {
    let Some(raw) = std::env::var_os("ASPIS_V7_EXPERIMENTAL_MAX_COMPACT_COUNTER") else {
        return Ok(None);
    };
    if std::env::var("ASPIS_V7_EXPERIMENTAL_FINAL_NONCE_CUTOFF_ACK").as_deref()
        != Ok(V7_FINAL_NONCE_CUTOFF_ACK)
    {
        return Err(V6ProverError::Stage(
            "V7 final nonce cutoff acknowledgement",
        ));
    }
    let cutoff = raw
        .to_str()
        .ok_or(V6ProverError::Stage("V7 final nonce cutoff UTF-8"))?
        .parse::<u8>()
        .map_err(|_| V6ProverError::Stage("V7 final nonce cutoff parse"))?;
    if usize::from(cutoff) >= aspis_core::v7_onefold::V7_COMPACT_QUERY_CANDIDATES {
        return Err(V6ProverError::Stage("V7 final nonce cutoff range"));
    }
    Ok(Some(cutoff))
}

#[cfg(feature = "v7-final-nonce-cutoff-audit")]
fn select_v7_final_nonce_at_counter_cutoff(
    transcript: &Transcript,
    bits: u8,
    cutoff: u8,
) -> Result<(u64, u32), V6ProverError> {
    let mut start = 0u64;
    let mut valid_nonces_tested = 0u32;
    loop {
        let nonce = crate::pow::find_grinding_nonce_unpublished_from(transcript, bits, start)
            .map_err(|_| V6ProverError::Stage("V7 cutoff final work mining"))?;
        valid_nonces_tested = valid_nonces_tested
            .checked_add(1)
            .ok_or(V6ProverError::Stage("V7 cutoff valid nonce count"))?;
        let mut post_nonce = transcript.clone();
        absorb_work(&mut post_nonce, 2, nonce);
        if derive_first_v7_compact_queries(&post_nonce)
            .map(|schedule| schedule.counter <= cutoff)
            .unwrap_or(false)
        {
            return Ok((nonce, valid_nonces_tested));
        }
        start = nonce
            .checked_add(1)
            .ok_or(V6ProverError::Stage("V7 cutoff nonce space exhausted"))?;
    }
}

fn inactive_claim(values: &[QM31], masks: [u16; 64]) -> Result<QM31, V6ProverError> {
    if values.len() != 1 << 10 {
        return Err(V6ProverError::Stage("V6 inactive claim shape"));
    }
    Ok(values
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| masks[row >> 4] & (1 << (row & 15)) != 0)
        .fold(QM31::ZERO, |sum, (_, value)| sum.add(value)))
}

fn gamma_claims(
    gamma: QM31,
    claims: &[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS],
) -> [QM31; V6_POINT_CLAIM_ROWS] {
    let powers = aspis_core::field::qm31_power_table::<V6_TOTAL_COLUMNS>(gamma);
    core::array::from_fn(|row| {
        (0..V6_TOTAL_COLUMNS).fold(QM31::ZERO, |sum, column| {
            sum.add(powers[column].mul(claims[row][column]))
        })
    })
}

fn absorb_circle_ood(transcript: &mut Transcript, sample: usize, value: QM31) {
    let mut record = [0u8; 17];
    record[0] = sample as u8;
    value.write_le_bytes(&mut record[1..]);
    transcript.absorb(label::V6_CIRCLE_OOD_VALUE, &record);
}

fn write_and_absorb_compact_relation(
    transcript: &mut Transcript,
    fields: &mut [QM31],
    round: usize,
    polynomial: &SumcheckPolynomial,
) {
    let coefficients = [0usize, 1, 2, 3, 5, 6];
    let base = V6_RELATION_QM31_OFFSET + round * V6_RELATION_SENT_VALUES;
    let mut framed = [0u8; 1 + V6_RELATION_SENT_VALUES * 16];
    framed[0] = round as u8;
    for (sent, coefficient) in coefficients.into_iter().enumerate() {
        fields[base + sent] = polynomial[coefficient];
        polynomial[coefficient].write_le_bytes(&mut framed[1 + sent * 16..][..16]);
    }
    transcript.absorb(label::V6_COMPACT_RELATION_ROUND, &framed);
}

fn absorb_final256(transcript: &mut Transcript, fields: &mut [QM31], values: &[QM31]) {
    debug_assert_eq!(values.len(), V6_FINAL_QM31_VALUES);
    let mut encoded = vec![0u8; V6_FINAL_QM31_VALUES * 16];
    for (index, value) in values.iter().copied().enumerate() {
        fields[V6_FINAL_QM31_OFFSET + index] = value;
        value.write_le_bytes(&mut encoded[index * 16..][..16]);
    }
    transcript.absorb(label::V6_FINAL256, &encoded);
}

fn derive_compact_queries(
    transcript: &Transcript,
) -> Result<(u8, u8, [u32; V6_QUERY_COUNT], usize, [u8; 32], Transcript), V6ProverError> {
    for selector in 0..V6_QUERY_SELECTOR_COUNT {
        for counter in 0..V6_COMPACT_DRAW_CAP {
            let mut candidate_transcript = transcript.clone();
            candidate_transcript.absorb(label::V6_QUERY_CANDIDATE, &[selector, counter]);
            let candidate = candidate_transcript
                .challenge_queries_without_replacement(
                    V6_QUERY_COUNT,
                    1u32 << V6_TREE_DEPTH,
                    V6_QUERY_DRAW_LIMIT,
                )
                .map_err(|_| V6ProverError::Stage("V6 query sampling"))?;
            let candidate: [u32; V6_QUERY_COUNT] = candidate
                .try_into()
                .map_err(|_| V6ProverError::Stage("V6 query count"))?;
            let frontier = binary_frontier_nodes(candidate, V6_TREE_DEPTH)?;
            if frontier <= V6_FRONTIER_CAP_PER_TREE {
                let state_after_queries = candidate_transcript.diagnostic_state();
                return Ok((
                    selector,
                    counter,
                    candidate,
                    frontier,
                    state_after_queries,
                    candidate_transcript,
                ));
            }
        }
    }
    Err(V6ProverError::NoCompactSchedule)
}

fn derive_v7_queries(
    transcript: &Transcript,
) -> Result<(u8, u8, [u32; V6_QUERY_COUNT], usize, [u8; 32], Transcript), V6ProverError> {
    let schedule = derive_first_v7_compact_queries(transcript)
        .map_err(|_| V6ProverError::NoCompactSchedule)?;
    Ok((
        0,
        schedule.counter,
        schedule.queries,
        schedule.frontier_nodes,
        schedule.transcript_state,
        schedule.accepted_transcript,
    ))
}

fn pool_inactive_row_masks(active: &[u16; 64]) -> [u16; 64] {
    core::array::from_fn(|group| !active[group])
}

fn derive_leaf_salt(
    reserved: &ReservedStateOnlyAttemptSecrets,
    hash: HashFn,
    hiding_context: StateOnlyHidingContext,
    fiber: usize,
) -> Result<[u8; 32], V6ProverError> {
    reserved
        .derive_spend_leaf_salt(hash, hiding_context, 0x76, fiber as u32)
        .map_err(|_| V6ProverError::Stage("V6 shared leaf salt"))
}

fn derive_v7_leaf_salt(
    reserved: &ReservedStateOnlyAttemptSecrets,
    hash: HashFn,
    hiding_context: StateOnlyHidingContext,
    fiber: usize,
) -> Result<[u8; 32], V6ProverError> {
    let salt = if hiding_context.mask_layout_fingerprint
        == PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
    {
        reserved.derive_pool_v1_leaf_salt(hash, hiding_context, 0x77, fiber as u32)
    } else {
        reserved.derive_spend_leaf_salt(hash, hiding_context, 0x77, fiber as u32)
    };
    salt.map_err(|_| V6ProverError::Stage("V7 shared leaf salt"))
}

fn build_c1_tree(
    hash: HashFn,
    reserved: &ReservedStateOnlyAttemptSecrets,
    hiding_context: StateOnlyHidingContext,
    encoded_c1: &[Vec<M31>],
) -> Result<BinaryMerkleTree, V6ProverError> {
    let mut c1_hashes = Vec::with_capacity(V6_LEAF_COUNT);
    for fiber in 0..V6_LEAF_COUNT {
        let salt = derive_leaf_salt(reserved, hash, hiding_context, fiber)?;
        let c1 = packed_c1_fiber(encoded_c1, fiber)?;
        c1_hashes.push(private_leaf_hash(hash, V6_C1_TREE_TAG, &c1, &salt));
    }
    BinaryMerkleTree::from_leaf_hashes(hash, c1_hashes)
}

fn build_c2_tree(
    hash: HashFn,
    reserved: &ReservedStateOnlyAttemptSecrets,
    hiding_context: StateOnlyHidingContext,
    encoded_c2: &[Vec<QM31>],
) -> Result<BinaryMerkleTree, V6ProverError> {
    let mut c2_hashes = Vec::with_capacity(V6_LEAF_COUNT);
    for fiber in 0..V6_LEAF_COUNT {
        let salt = derive_leaf_salt(reserved, hash, hiding_context, fiber)?;
        let c2 = packed_c2_fiber(encoded_c2, fiber)?;
        c2_hashes.push(private_leaf_hash(hash, V6_C2_TREE_TAG, &c2, &salt));
    }
    BinaryMerkleTree::from_leaf_hashes(hash, c2_hashes)
}

fn build_v7_c1_tree(
    hash: HashFn,
    reserved: &ReservedStateOnlyAttemptSecrets,
    hiding_context: StateOnlyHidingContext,
    encoded_c1: &[Vec<M31>],
) -> Result<BinaryMerkleTree216, V6ProverError> {
    let mut c1_hashes = Vec::with_capacity(V6_LEAF_COUNT);
    for fiber in 0..V6_LEAF_COUNT {
        let salt = derive_v7_leaf_salt(reserved, hash, hiding_context, fiber)?;
        let c1 = packed_c1_fiber(encoded_c1, fiber)?;
        c1_hashes.push(private_leaf_hash_v7(hash, V7_C1_TREE_TAG, &c1, &salt));
    }
    BinaryMerkleTree216::from_leaf_hashes(hash, c1_hashes)
}

fn build_v7_c2_tree(
    hash: HashFn,
    reserved: &ReservedStateOnlyAttemptSecrets,
    hiding_context: StateOnlyHidingContext,
    encoded_c2: &[Vec<QM31>],
) -> Result<BinaryMerkleTree216, V6ProverError> {
    let mut c2_hashes = Vec::with_capacity(V6_LEAF_COUNT);
    for fiber in 0..V6_LEAF_COUNT {
        let salt = derive_v7_leaf_salt(reserved, hash, hiding_context, fiber)?;
        let c2 = packed_c2_fiber(encoded_c2, fiber)?;
        c2_hashes.push(private_leaf_hash_v7(hash, V7_C2_TREE_TAG, &c2, &salt));
    }
    BinaryMerkleTree216::from_leaf_hashes(hash, c2_hashes)
}

/// Shared semantic/relation implementation for the frozen V6 proof and its
/// compact V7 wire successor. Production callers fix `pow_mode` to `Mine`.
/// A failed build consumes the unpublished attempt and its durable nonce
/// reservation; callers must never retry it with the same secrets.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn build_onefold_proof_with_pow_mode(
    relation: OneFoldRelation<'_>,
    prover_context: V6ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
    profile: OneFoldBuildProfile,
) -> Result<BuiltOneFoldProof, V6ProverError> {
    if attempt.mask_nonce() != prover_context.attempt_id {
        return Err(V6ProverError::AttemptIdMismatch);
    }
    if profile == OneFoldBuildProfile::V6 && !matches!(relation, OneFoldRelation::Atomic { .. }) {
        return Err(V6ProverError::Stage("Pool relation requires V7"));
    }
    let statement_digest = match relation {
        OneFoldRelation::Atomic { statement, .. } => {
            atomic_payment_statement_digest_v4(statement, hash)
                .map_err(|_| V6ProverError::Stage("V6 statement digest"))?
        }
        OneFoldRelation::PoolPrivateTransfer {
            statement_digest, ..
        }
        | OneFoldRelation::PoolWithdrawal {
            statement_digest, ..
        }
        | OneFoldRelation::PoolForestPrivateTransfer {
            statement_digest, ..
        }
        | OneFoldRelation::PoolForestWithdrawal {
            statement_digest, ..
        } => statement_digest,
    };
    let transcript_context = V6TranscriptContext {
        program_id: prover_context.program_id,
        release_binding: prover_context.release_binding,
        statement_digest,
        attempt_id: prover_context.attempt_id,
    };
    let hiding_context = match relation {
        OneFoldRelation::Atomic { .. } => {
            StateOnlyHidingContext::atomic_spend_v3(statement_digest, prover_context.attempt_id)
        }
        OneFoldRelation::PoolPrivateTransfer { .. } => {
            StateOnlyHidingContext::pool_v1_private_transfer(
                statement_digest,
                prover_context.attempt_id,
            )
        }
        OneFoldRelation::PoolWithdrawal { .. } => {
            StateOnlyHidingContext::pool_v1_withdrawal(statement_digest, prover_context.attempt_id)
        }
        OneFoldRelation::PoolForestPrivateTransfer { .. }
        | OneFoldRelation::PoolForestWithdrawal { .. } => {
            StateOnlyHidingContext::pool_v1_pair_forest_v1(
                statement_digest,
                prover_context.attempt_id,
            )
        }
    };
    let (mut transcript, precommit_binding) = match profile {
        OneFoldBuildProfile::V6 => begin_transcript_and_precommit(hash, &transcript_context)?,
        OneFoldBuildProfile::V7Compact => {
            begin_v7_transcript_and_precommit(hash, &transcript_context, hiding_context)?
        }
    };
    let (reserved, mask_material) = match relation {
        OneFoldRelation::Atomic { .. } => attempt.reserve_and_build_atomic_mask_material_v3(
            hash,
            precommit_binding,
            hiding_context,
            nonce_store,
        ),
        OneFoldRelation::PoolPrivateTransfer { .. } => attempt
            .reserve_and_build_pool_v1_private_transfer_mask_material_v1(
                hash,
                precommit_binding,
                hiding_context,
                nonce_store,
            ),
        OneFoldRelation::PoolWithdrawal { .. } => attempt
            .reserve_and_build_pool_v1_withdrawal_mask_material_v1(
                hash,
                precommit_binding,
                hiding_context,
                nonce_store,
            ),
        OneFoldRelation::PoolForestPrivateTransfer { .. }
        | OneFoldRelation::PoolForestWithdrawal { .. } => attempt
            .reserve_and_build_pool_v1_pair_forest_mask_material_v1(
                hash,
                precommit_binding,
                hiding_context,
                nonce_store,
            ),
    }
    .map_err(|_| V6ProverError::Stage("V6 mask reservation"))?;
    let d = match relation {
        OneFoldRelation::Atomic { .. } => reserved.derive_spend_zero_factor_d(hash, hiding_context),
        OneFoldRelation::PoolPrivateTransfer { .. } => {
            reserved.derive_pool_v1_private_transfer_zero_factor_d(hash, hiding_context)
        }
        OneFoldRelation::PoolWithdrawal { .. } => {
            reserved.derive_pool_v1_withdrawal_zero_factor_d(hash, hiding_context)
        }
        OneFoldRelation::PoolForestPrivateTransfer { .. }
        | OneFoldRelation::PoolForestWithdrawal { .. } => {
            reserved.derive_pool_v1_pair_forest_zero_factor_d(hash, hiding_context)
        }
    }
    .map_err(|_| V6ProverError::Stage("V6 D derivation"))?;
    let (mut trace, forest_trace): (_, Option<PoolV1PairForestTraceV1>) = match relation {
        OneFoldRelation::Atomic { statement, witness } => {
            let mut atomic = build_atomic_state_only_trace_v3(statement, witness)
                .map_err(|_| V6ProverError::Stage("V6 atomic trace"))?;
            (core::mem::take(&mut atomic.trace), None)
        }
        OneFoldRelation::PoolPrivateTransfer {
            public,
            witness,
            context,
            ..
        } => {
            let mut payment = build_pool_v1_private_transfer_trace_v1(public, witness, context)
                .map_err(|_| V6ProverError::Stage("V7 Pool transfer trace"))?;
            (core::mem::take(&mut payment.trace), None)
        }
        OneFoldRelation::PoolWithdrawal {
            public,
            witness,
            context,
            ..
        } => {
            let mut payment = build_pool_v1_withdrawal_trace_v1(public, witness, context)
                .map_err(|_| V6ProverError::Stage("V7 Pool withdrawal trace"))?;
            (core::mem::take(&mut payment.trace), None)
        }
        OneFoldRelation::PoolForestPrivateTransfer {
            public,
            witness,
            context,
            transition,
            ..
        } => {
            let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
                public,
                witness,
                context,
                transition.live_snapshot,
            )
            .map_err(|_| V6ProverError::Stage("V7 Pool forest transfer trace"))?;
            if compiled.public_statement != *transition {
                return Err(V6ProverError::Stage("V7 Pool forest transfer transition"));
            }
            (compiled.semantic_c1, Some(compiled.trace))
        }
        OneFoldRelation::PoolForestWithdrawal {
            public,
            witness,
            context,
            transition,
            ..
        } => {
            let compiled = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
                public,
                witness,
                context,
                transition.live_snapshot,
            )
            .map_err(|_| V6ProverError::Stage("V7 Pool forest withdrawal trace"))?;
            if compiled.public_statement != *transition {
                return Err(V6ProverError::Stage("V7 Pool forest withdrawal transition"));
            }
            (compiled.semantic_c1, Some(compiled.trace))
        }
    };
    let applied = match relation {
        OneFoldRelation::Atomic { .. } => {
            apply_atomic_state_only_mask_material_v3(&mut trace, mask_material)
        }
        OneFoldRelation::PoolPrivateTransfer { .. } => {
            apply_pool_v1_private_transfer_mask_material_v1(&mut trace, mask_material)
        }
        OneFoldRelation::PoolWithdrawal { .. } => {
            apply_pool_v1_withdrawal_mask_material_v1(&mut trace, mask_material)
        }
        OneFoldRelation::PoolForestPrivateTransfer { .. }
        | OneFoldRelation::PoolForestWithdrawal { .. } => {
            apply_pool_v1_pair_forest_mask_material_v1(&mut trace, mask_material)
        }
    }
    .map_err(|_| V6ProverError::Stage("V6 mask application"))?;

    let selected_c1 = trace
        .c1
        .iter()
        .cloned()
        .chain(applied.mask_only_c1.iter().cloned())
        .collect::<Vec<_>>();
    let encoder = CircleEncoder::new_for_domain_log(V6_DOMAIN_LOG);
    let encoded_c1 = encode_state_only_c1_columns(&encoder, &selected_c1)
        .map_err(|_| V6ProverError::Stage("V6 C1 encoding"))?;
    let c1_tree =
        match profile {
            OneFoldBuildProfile::V6 => ProfiledBinaryMerkleTree::V6(build_c1_tree(
                hash,
                &reserved,
                hiding_context,
                &encoded_c1,
            )?),
            OneFoldBuildProfile::V7Compact => ProfiledBinaryMerkleTree::V7Compact(
                build_v7_c1_tree(hash, &reserved, hiding_context, &encoded_c1)?,
            ),
        };
    let (lambda, chi) = match &c1_tree {
        ProfiledBinaryMerkleTree::V6(tree) => absorb_c1_and_sample_copy_challenges(
            &mut transcript,
            hash,
            &transcript_context,
            tree.root(),
        )?,
        ProfiledBinaryMerkleTree::V7Compact(tree) => absorb_v7_c1_and_sample_copy_challenges(
            &mut transcript,
            hash,
            &transcript_context,
            tree.root(),
        )?,
    };

    let mut h1 = match relation {
        OneFoldRelation::Atomic { .. } => {
            build_atomic_state_only_copy_helper_v3(&trace, lambda, chi)
                .map_err(|_| V6ProverError::Stage("V6 copy helper"))?
        }
        OneFoldRelation::PoolPrivateTransfer { .. } => {
            let prepared = prepare_pool_v1_payment_semantic_oracle_v1(
                PoolV1PaymentTraceVariantV1::PrivateTransfer,
            )
            .map_err(|_| V6ProverError::Stage("V7 Pool transfer registry"))?;
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace, lambda, chi)
                .map_err(|_| V6ProverError::Stage("V7 Pool transfer copy helper"))?
        }
        OneFoldRelation::PoolWithdrawal { .. } => {
            let prepared =
                prepare_pool_v1_payment_semantic_oracle_v1(PoolV1PaymentTraceVariantV1::Withdrawal)
                    .map_err(|_| V6ProverError::Stage("V7 Pool withdrawal registry"))?;
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace, lambda, chi)
                .map_err(|_| V6ProverError::Stage("V7 Pool withdrawal copy helper"))?
        }
        OneFoldRelation::PoolForestPrivateTransfer { transition, .. }
        | OneFoldRelation::PoolForestWithdrawal { transition, .. } => {
            build_pool_v1_pair_forest_copy_helper_v1(
                forest_trace
                    .as_ref()
                    .ok_or(V6ProverError::Stage("V7 Pool forest trace source"))?,
                transition.live_snapshot.next_pair_index,
                lambda,
                chi,
            )
            .map_err(|_| V6ProverError::Stage("V7 Pool forest copy helper"))?
        }
    };
    match relation {
        OneFoldRelation::Atomic { .. } => {
            apply_atomic_state_only_h1_padding_mask_v3(&mut h1, &applied.h1_padding)
        }
        OneFoldRelation::PoolPrivateTransfer { .. } => {
            apply_pool_v1_private_transfer_h1_padding_mask_v1(&mut h1, &applied.h1_padding)
        }
        OneFoldRelation::PoolWithdrawal { .. } => {
            apply_pool_v1_withdrawal_h1_padding_mask_v1(&mut h1, &applied.h1_padding)
        }
        OneFoldRelation::PoolForestPrivateTransfer { .. }
        | OneFoldRelation::PoolForestWithdrawal { .. } => {
            apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h1, &applied.h1_padding)
        }
    }
    .map_err(|_| V6ProverError::Stage("V6 H padding mask"))?;
    if state_only_copy_helper_sum(&h1) != Some(QM31::ZERO) {
        return Err(V6ProverError::Stage("V6 H sum"));
    }
    let c2_messages = vec![h1.clone(), applied.g.clone(), d.clone()];
    let encoded_c2 = encode_state_only_spend_c2_columns(&encoder, &c2_messages)
        .map_err(|_| V6ProverError::Stage("V6 C2 encoding"))?;
    let c2_tree =
        match profile {
            OneFoldBuildProfile::V6 => ProfiledBinaryMerkleTree::V6(build_c2_tree(
                hash,
                &reserved,
                hiding_context,
                &encoded_c2,
            )?),
            OneFoldBuildProfile::V7Compact => ProfiledBinaryMerkleTree::V7Compact(
                build_v7_c2_tree(hash, &reserved, hiding_context, &encoded_c2)?,
            ),
        };
    let batching = match &c2_tree {
        ProfiledBinaryMerkleTree::V6(tree) => {
            absorb_c2_and_sample_batching(&mut transcript, hash, &transcript_context, tree.root())?
        }
        ProfiledBinaryMerkleTree::V7Compact(tree) => absorb_v7_c2_and_sample_batching(
            &mut transcript,
            hash,
            &transcript_context,
            tree.root(),
        )?,
    };

    let mut fields = vec![QM31::ZERO; V6_FIXED_M31_LIMBS / 4];
    let initial_claim = state_only_initial_mask_claim(&trace, &applied.mask_only_c1, &applied.g)
        .map_err(|_| V6ProverError::Stage("V6 initial mask claim"))?;
    fields[V6_INITIAL_CLAIM_OFFSET] = initial_claim;
    let eta = begin_state_only_masked_sumcheck(&mut transcript, initial_claim)
        .map_err(|_| V6ProverError::Stage("V6 eta"))?;
    let mut semantic_point = [QM31::ZERO; V6_SEMANTIC_ROUNDS];
    let mut prefix = [QM31::ZERO; V6_SEMANTIC_ROUNDS];
    let mut semantic_claim = initial_claim;

    let semantic_oracle = |point: &[QM31; V6_SEMANTIC_ROUNDS]| -> Result<QM31, V6ProverError> {
        let mask = state_only_mask_oracle_value(&trace, &applied.mask_only_c1, &applied.g, point)
            .map_err(|_| V6ProverError::Stage("V6 mask oracle"))?;
        let claims = statement_evaluations(&trace, &applied.mask_only_c1, &h1, &applied.g, point)
            .map_err(|_| V6ProverError::Stage("V6 semantic claims"))?;
        let original = match relation {
            OneFoldRelation::Atomic { statement, .. } => match profile {
            OneFoldBuildProfile::V6 => {
                atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
            statement,
            &claims,
            point,
            lambda,
            chi,
            batching.theta,
            &batching.zerocheck_point,
            batching.mu,
        )
            }
                .map_err(|_| ()),
            OneFoldBuildProfile::V7Compact => {
                atomic_state_only_selected_unmasked_terminal_value_compiled_tag73(
                    statement,
                    &claims,
                    point,
                    lambda,
                    chi,
                    batching.theta,
                    &batching.zerocheck_point,
                    batching.mu,
                )
            }
                .map_err(|_| ()),
            },
            OneFoldRelation::PoolPrivateTransfer { public, .. } => {
                evaluate_pool_v1_private_transfer_selected_unmasked_terminal_compiled_tag73_v1(
                    public,
                    &claims,
                    point,
                    lambda,
                    chi,
                    batching.theta,
                    &batching.zerocheck_point,
                    batching.mu,
                )
                .map_err(|_| ())
            }
            OneFoldRelation::PoolWithdrawal { public, .. } => {
                evaluate_pool_v1_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(
                    public,
                    &claims,
                    point,
                    lambda,
                    chi,
                    batching.theta,
                    &batching.zerocheck_point,
                    batching.mu,
                )
                .map_err(|_| ())
            }
            OneFoldRelation::PoolForestPrivateTransfer {
                public, transition, ..
            } => evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1(
                public,
                transition,
                &claims,
                point,
                lambda,
                chi,
                batching.theta,
                &batching.zerocheck_point,
                batching.mu,
            )
            .map_err(|_| ()),
            OneFoldRelation::PoolForestWithdrawal {
                public, transition, ..
            } => evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(
                public,
                transition,
                &claims,
                point,
                lambda,
                chi,
                batching.theta,
                &batching.zerocheck_point,
                batching.mu,
            )
            .map_err(|_| ()),
        }
        .map_err(|_| V6ProverError::Stage("V6 semantic oracle"))?;
        Ok(mask.add(eta.mul(original)))
    };

    for round in 0..V6_SEMANTIC_ROUNDS {
        let remaining = V6_SEMANTIC_ROUNDS - round - 1;
        let mut samples = [QM31::ZERO; 28];
        for (sample_index, sample) in samples.iter_mut().enumerate() {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample_index as u32)));
            let mut total = QM31::ZERO;
            for assignment in 0..(1usize << remaining) {
                for offset in 0..remaining {
                    let bit = (assignment >> (remaining - 1 - offset)) & 1;
                    prefix[round + 1 + offset] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
                }
                total = total.add(semantic_oracle(&prefix)?);
            }
            *sample = total;
        }
        let polynomial = interpolate_degree27(&samples);
        if state_only_boundary_sum(&polynomial) != semantic_claim {
            return Err(V6ProverError::Stage("V6 semantic boundary"));
        }
        write_compact_semantic_fields(&mut fields, round, &polynomial);
        absorb_compact_semantic_round(&mut transcript, round, &polynomial);
        let challenge = transcript
            .challenge_qm31()
            .map_err(|_| V6ProverError::Stage("V6 semantic challenge"))?;
        semantic_claim = evaluate_state_only_polynomial(&polynomial, challenge);
        semantic_point[round] = challenge;
        prefix[round] = challenge;
    }
    if semantic_oracle(&semantic_point)? != semantic_claim {
        return Err(V6ProverError::Stage("V6 semantic terminal"));
    }

    let point_claims = point_claim_rows(
        &trace,
        &applied.mask_only_c1,
        &h1,
        &applied.g,
        &d,
        &semantic_point,
    )?;
    absorb_point_claims(&mut transcript, &mut fields, &point_claims);
    let work_bits = match profile {
        OneFoldBuildProfile::V6 => [V6_BATCH_WORK_BITS, V6_FOLD_WORK_BITS, V6_FINAL_WORK_BITS],
        OneFoldBuildProfile::V7Compact => [
            V7_COMPACT_BATCH_WORK_BITS,
            V7_COMPACT_FOLD_WORK_BITS,
            V7_COMPACT_FINAL_WORK_BITS,
        ],
    };
    let batch_nonce = work_nonce(&transcript, work_bits[0], pow_mode)?;
    let mut pow_valid = transcript.grinding_ok(batch_nonce, work_bits[0]);
    absorb_work(&mut transcript, 0, batch_nonce);
    let gamma = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V6ProverError::Stage("V6 gamma"))?;

    let combined_message =
        gamma_combine_state_only_spend_messages(&selected_c1, &c2_messages, gamma)
            .map_err(|_| V6ProverError::Stage("V6 combined message"))?;
    let combined_codeword = gamma_combine_state_only_spend_codewords(
        &encoded_c1,
        &encoded_c2,
        gamma,
        encoder.codeword_len(),
    )
    .map_err(|_| V6ProverError::Stage("V6 combined codeword"))?;
    let inactive_masks = match relation {
        OneFoldRelation::Atomic { .. } => atomic_state_only_copy_inactive_row_masks_v3(),
        OneFoldRelation::PoolPrivateTransfer { .. } => {
            pool_inactive_row_masks(pool_v1_private_transfer_copy_active_row_masks_compiled_v1())
        }
        OneFoldRelation::PoolWithdrawal { .. } => {
            pool_inactive_row_masks(pool_v1_withdrawal_copy_active_row_masks_compiled_v1())
        }
        OneFoldRelation::PoolForestPrivateTransfer { .. }
        | OneFoldRelation::PoolForestWithdrawal { .. } => pool_inactive_row_masks(
            &pool_v1_pair_forest_copy_active_row_masks_v1()
                .map_err(|_| V6ProverError::Stage("V7 Pool forest inactive rows"))?,
        ),
    };
    let inactive = inactive_claim(&combined_message, inactive_masks)?;
    fields[V6_INACTIVE_CLAIM_QM31_OFFSET] = inactive;
    let mut inactive_bytes = [0u8; 16];
    inactive.write_le_bytes(&mut inactive_bytes);
    transcript.absorb(label::V6_INACTIVE_CLAIM, &inactive_bytes);
    let kappa = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V6ProverError::Stage("V6 kappa"))?;

    let points = v6_statement_points(&semantic_point);
    let point_scales = [QM31::ONE, kappa, kappa.square()];
    let combined_claims = gamma_claims(gamma, &point_claims);
    let mut running_claim = inactive;
    let mut weights = WeightAccumulator::empty(10);
    for row in 0..V6_POINT_CLAIM_ROWS {
        running_claim = running_claim.add(point_scales[row].mul(combined_claims[row]));
        weights
            .add_multilinear(point_scales[row], points[row].to_vec())
            .map_err(|_| V6ProverError::Stage("V6 relation point weight"))?;
    }
    weights
        .add_grouped_64x16_binary_masks_deferred(inactive_masks)
        .map_err(|_| V6ProverError::Stage("V6 relation inactive weight"))?;

    for sample in 0..2 {
        let point = transcript
            .challenge_secure_circle_point()
            .map_err(|_| V6ProverError::Stage("V6 circle OOD point"))?;
        let mut evaluation = WeightAccumulator::empty(10);
        evaluation
            .add_circle_tensor(QM31::ONE, point)
            .map_err(|_| V6ProverError::Stage("V6 circle OOD weight"))?;
        let value = evaluation.dot(&combined_message);
        fields[V6_OOD_QM31_OFFSET + sample] = value;
        absorb_circle_ood(&mut transcript, sample, value);
        let mix = transcript
            .challenge_qm31()
            .map_err(|_| V6ProverError::Stage("V6 circle OOD mix"))?;
        weights
            .add_circle_tensor(mix, point)
            .map_err(|_| V6ProverError::Stage("V6 mixed circle OOD weight"))?;
        running_claim = running_claim.add(mix.mul(value));
    }

    let mut relation_values = combined_message;
    let first = polynomial_for_extension(&relation_values, &weights);
    if boundary_sum(&first) != running_claim {
        return Err(V6ProverError::Stage("V6 first relation boundary"));
    }
    write_and_absorb_compact_relation(&mut transcript, &mut fields, 0, &first);
    let fold_nonce = work_nonce(&transcript, work_bits[1], pow_mode)?;
    pow_valid &= transcript.grinding_ok(fold_nonce, work_bits[1]);
    absorb_work(&mut transcript, 1, fold_nonce);
    let alpha0 = transcript
        .challenge_qm31()
        .map_err(|_| V6ProverError::Stage("V6 alpha0"))?;
    running_claim = evaluate(&first, alpha0);
    weights.fold_deferred_relation_arity4(alpha0);
    relation_values = fold_adjacent_natural_arity4(&relation_values, alpha0);
    if relation_values.len() != V6_FINAL_QM31_VALUES
        || weights.dot(&relation_values) != running_claim
    {
        return Err(V6ProverError::Stage("V6 first relation fold"));
    }
    let folded_codeword =
        fold_candidate_codeword_round_for_domain_log(&combined_codeword, alpha0, 0, V6_DOMAIN_LOG)
            .map_err(|_| V6ProverError::Stage("V6 codeword fold"))?;
    if folded_codeword.len() != V6_LEAF_COUNT {
        return Err(V6ProverError::Stage("V6 folded codeword length"));
    }
    absorb_final256(&mut transcript, &mut fields, &relation_values);

    #[cfg(feature = "v7-final-nonce-cutoff-audit")]
    let (final_nonce, final_work_valid_nonces_tested, final_work_counter_cutoff) = {
        let cutoff = requested_v7_final_nonce_cutoff()?;
        match (profile, pow_mode, cutoff) {
            (OneFoldBuildProfile::V7Compact, StateOnlyPowMode::Mine, Some(cutoff)) => {
                let (nonce, tested) =
                    select_v7_final_nonce_at_counter_cutoff(&transcript, work_bits[2], cutoff)?;
                (nonce, tested, Some(cutoff))
            }
            (_, _, Some(_)) => {
                return Err(V6ProverError::Stage(
                    "V7 final nonce cutoff requires mined compact V7",
                ));
            }
            (_, _, None) => (work_nonce(&transcript, work_bits[2], pow_mode)?, 1, None),
        }
    };
    #[cfg(not(feature = "v7-final-nonce-cutoff-audit"))]
    let (final_nonce, final_work_valid_nonces_tested, final_work_counter_cutoff) =
        (work_nonce(&transcript, work_bits[2], pow_mode)?, 1, None);
    pow_valid &= transcript.grinding_ok(final_nonce, work_bits[2]);
    absorb_work(&mut transcript, 2, final_nonce);
    let (
        selector,
        compact_counter,
        queries,
        frontier_nodes,
        state_after_queries,
        accepted_query_transcript,
    ) = match profile {
        OneFoldBuildProfile::V6 => derive_compact_queries(&transcript)?,
        OneFoldBuildProfile::V7Compact => derive_v7_queries(&transcript)?,
    };
    transcript = accepted_query_transcript;
    let expected_frontier = binary_frontier_nodes(queries, V6_TREE_DEPTH)?;
    if expected_frontier != frontier_nodes {
        return Err(V6ProverError::Stage("V6 frontier count"));
    }

    let query_batch_labels = match profile {
        OneFoldBuildProfile::V6 => (label::V6_QUERY_BATCH_CHALLENGE, label::V6_QUERY_BATCH_CLAIM),
        OneFoldBuildProfile::V7Compact => {
            (label::V7_QUERY_BATCH_CHALLENGE, label::V7_QUERY_BATCH_CLAIM)
        }
    };
    transcript.absorb(query_batch_labels.0, &[]);
    let query_batch_challenge = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V6ProverError::Stage("V6 query batch challenge"))?;
    let folded_query_values =
        core::array::from_fn(|ordinal| folded_codeword[queries[ordinal] as usize]);
    let query_coordinates = prepare_v6_onefold_coordinates(queries)
        .map_err(|_| V6ProverError::Stage("one-fold query coordinates"))?;
    let query_line_x = query_coordinates.line_x;
    let authenticated_query_batch = V6AuthenticatedQueryBatch {
        values: folded_query_values,
        line_x: query_line_x,
    };
    let query_claim = match profile {
        OneFoldBuildProfile::V6 => add_v6_final256_query_batch(
            &mut weights,
            &mut running_claim,
            queries,
            authenticated_query_batch,
            query_batch_challenge,
        ),
        OneFoldBuildProfile::V7Compact => add_v7_final256_query_batch_shifted(
            &mut weights,
            &mut running_claim,
            queries,
            authenticated_query_batch,
            query_batch_challenge,
        ),
    }
    .map_err(|_| V6ProverError::Stage("V6 query batch relation"))?;
    let mut query_claim_bytes = [0u8; 16];
    query_claim.write_le_bytes(&mut query_claim_bytes);
    transcript.absorb(query_batch_labels.1, &query_claim_bytes);

    let mut alphas = [QM31::ZERO; V6_RELATION_ROUNDS];
    alphas[0] = alpha0;
    for round in 1..V6_RELATION_ROUNDS {
        let polynomial = polynomial_for_extension(&relation_values, &weights);
        if boundary_sum(&polynomial) != running_claim {
            return Err(V6ProverError::Stage("V6 later relation boundary"));
        }
        write_and_absorb_compact_relation(&mut transcript, &mut fields, round, &polynomial);
        let alpha = transcript
            .challenge_qm31()
            .map_err(|_| V6ProverError::Stage("V6 later alpha"))?;
        alphas[round] = alpha;
        running_claim = evaluate(&polynomial, alpha);
        weights.fold_deferred_relation_arity4(alpha);
        relation_values = fold_adjacent_natural_arity4(&relation_values, alpha);
    }
    if relation_values.len() != 4 || weights.dot(&relation_values) != running_claim {
        return Err(V6ProverError::Stage("V6 relation terminal"));
    }

    let frontier_digest_bytes = match profile {
        OneFoldBuildProfile::V6 => 32,
        OneFoldBuildProfile::V7Compact => V7_COMPACT_DIGEST_BYTES,
    };
    let c1_frontier = c1_tree.frontier_bytes(queries)?;
    let c2_frontier = c2_tree.frontier_bytes(queries)?;
    if c1_frontier.len() != frontier_nodes * frontier_digest_bytes
        || c2_frontier.len() != frontier_nodes * frontier_digest_bytes
    {
        return Err(V6ProverError::Stage("V6 frontier serialization"));
    }
    let fixed_fields = pack_qm31_fields(&fields);
    if fixed_fields.len() != V6_FIXED_PACKED_FIELD_BYTES {
        return Err(V6ProverError::Stage("V6 fixed-field packing"));
    }
    let body_without_frontiers = match profile {
        OneFoldBuildProfile::V6 => V6_BODY_WITHOUT_FRONTIERS,
        OneFoldBuildProfile::V7Compact => V7_COMPACT_BODY_WITHOUT_FRONTIERS,
    };
    let expected_body_bytes = body_without_frontiers + 2 * frontier_digest_bytes * frontier_nodes;
    let mut body = Vec::with_capacity(expected_body_bytes);
    body.extend_from_slice(&fixed_fields);
    c1_tree.append_root(&mut body);
    c2_tree.append_root(&mut body);
    body.extend_from_slice(&batch_nonce.to_le_bytes());
    body.extend_from_slice(&fold_nonce.to_le_bytes());
    body.extend_from_slice(&final_nonce.to_le_bytes());
    for query in queries {
        let fiber = query as usize;
        body.extend_from_slice(&packed_c1_fiber(&encoded_c1, fiber)?);
        match profile {
            OneFoldBuildProfile::V6 => {
                body.extend_from_slice(&packed_c2_fiber(&encoded_c2, fiber)?);
                body.extend_from_slice(&derive_leaf_salt(&reserved, hash, hiding_context, fiber)?);
            }
            OneFoldBuildProfile::V7Compact => {
                body.extend_from_slice(&packed_c2_fiber(&encoded_c2, fiber)?);
                body.extend_from_slice(&derive_v7_leaf_salt(
                    &reserved,
                    hash,
                    hiding_context,
                    fiber,
                )?);
            }
        }
    }
    body.extend_from_slice(&c1_frontier);
    body.extend_from_slice(&c2_frontier);
    let body_within_profile_limit = match profile {
        OneFoldBuildProfile::V6 => body.len() < V6_HARD_BODY_LIMIT,
        OneFoldBuildProfile::V7Compact => body.len() <= V7_COMPACT_MAX_BODY_BYTES,
    };
    if body.len() != expected_body_bytes || !body_within_profile_limit {
        return Err(V6ProverError::Stage("V6 body length"));
    }

    // An independent prover-side equality catches an encoder/fold ordering
    // mistake before handing the body to the verifier.
    for &query in &queries {
        let expected = aspis_core::v6_onefold::evaluate_final256_coefficients(
            &fields[V6_FINAL_QM31_OFFSET..V6_FINAL_QM31_OFFSET + V6_FINAL_QM31_VALUES],
            aspis_core::circle_fri::line_domain_x_for_circle(V6_DOMAIN_LOG, 1, query as usize)
                .map_err(|_| V6ProverError::Stage("V6 terminal query point"))?,
        )?;
        if folded_codeword[query as usize] != expected {
            return Err(V6ProverError::Stage("V6 encoder/final equality"));
        }
    }

    Ok(BuiltOneFoldProof {
        bytes: body,
        selector,
        compact_counter,
        frontier_nodes,
        queries,
        work_nonces: [batch_nonce, fold_nonce, final_nonce],
        pow_valid,
        transcript_state_after_queries: state_after_queries,
        final_work_valid_nonces_tested,
        final_work_counter_cutoff,
    })
}

/// Build a production V6 proof with every work witness mined and checked.
/// There is intentionally no production argument that can disable grinding.
#[allow(clippy::too_many_arguments)]
pub fn build_v6_onefold_proof_production(
    statement: &AtomicPaymentStatementV4,
    witness: &SpendWitness,
    prover_context: V6ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
) -> Result<BuiltV6OneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::Atomic { statement, witness },
        prover_context,
        attempt,
        nonce_store,
        hash,
        StateOnlyPowMode::Mine,
        OneFoldBuildProfile::V6,
    )
    .map(Into::into)
}

/// Build a diagnostic V6 proof with an explicit work mode.
///
/// This symbol does not exist in an ordinary production build.
#[cfg(any(test, feature = "insecure-spend-fixture"))]
#[allow(clippy::too_many_arguments)]
pub fn build_v6_onefold_proof(
    statement: &AtomicPaymentStatementV4,
    witness: &SpendWitness,
    prover_context: V6ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltV6OneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::Atomic { statement, witness },
        prover_context,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        OneFoldBuildProfile::V6,
    )
    .map(Into::into)
}

/// Build a production compact V7 proof with all three work witnesses mined.
#[allow(clippy::too_many_arguments)]
pub fn build_v7_compact_onefold_proof_production(
    statement: &AtomicPaymentStatementV4,
    witness: &SpendWitness,
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::Atomic { statement, witness },
        prover_context,
        attempt,
        nonce_store,
        hash,
        StateOnlyPowMode::Mine,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

/// Diagnostic compact V7 fixture builder with explicit work mode.
#[cfg(any(test, feature = "insecure-spend-fixture"))]
#[allow(clippy::too_many_arguments)]
pub fn build_v7_compact_onefold_proof(
    statement: &AtomicPaymentStatementV4,
    witness: &SpendWitness,
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::Atomic { statement, witness },
        prover_context,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

/// Build a production native Pool V1 private-transfer proof.  The statement
/// digest must be the exact digest in the surrounding 600-byte ASVQ binding;
/// it is committed before C1 and checked by the selected verifier profile.
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_private_transfer_onefold_proof_production(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PrivateTransferWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolPrivateTransfer {
            public,
            witness,
            context: relation_context,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        StateOnlyPowMode::Mine,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

/// Build a production native Pool V1 withdrawal proof.
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_withdrawal_onefold_proof_production(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1WithdrawalWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolWithdrawal {
            public,
            witness,
            context: relation_context,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        StateOnlyPowMode::Mine,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

/// Build the inactive eight-lane one-transaction private-transfer proof.
/// `transition` is the exact account-derived selected-lane before/after image
/// already committed by the surrounding ASF8 statement digest.
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_pair_forest_private_transfer_onefold_proof_production(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairForestPrivateTransferWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolForestPrivateTransfer {
            public,
            witness,
            context: relation_context,
            transition,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        StateOnlyPowMode::Mine,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

/// Build the inactive eight-lane one-transaction withdrawal proof.
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_pair_forest_withdrawal_onefold_proof_production(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairForestWithdrawalWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolForestWithdrawal {
            public,
            witness,
            context: relation_context,
            transition,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        StateOnlyPowMode::Mine,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

#[cfg(any(test, feature = "insecure-spend-fixture"))]
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_private_transfer_onefold_proof(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PrivateTransferWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolPrivateTransfer {
            public,
            witness,
            context: relation_context,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

#[cfg(any(test, feature = "insecure-spend-fixture"))]
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_withdrawal_onefold_proof(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1WithdrawalWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolWithdrawal {
            public,
            witness,
            context: relation_context,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

#[cfg(any(test, feature = "insecure-spend-fixture"))]
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_pair_forest_private_transfer_onefold_proof(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairForestPrivateTransferWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolForestPrivateTransfer {
            public,
            witness,
            context: relation_context,
            transition,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

#[cfg(any(test, feature = "insecure-spend-fixture"))]
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pool_pair_forest_withdrawal_onefold_proof(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairForestWithdrawalWitnessV1,
    relation_context: PoolV1PaymentRelationContextV1<'_>,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltV7CompactOneFoldProof, V6ProverError> {
    build_onefold_proof_with_pow_mode(
        OneFoldRelation::PoolForestWithdrawal {
            public,
            witness,
            context: relation_context,
            transition,
            statement_digest,
        },
        prover_context,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        OneFoldBuildProfile::V7Compact,
    )
    .map(Into::into)
}

fn terminal_claims(view: &V6SemanticView<'_>) -> [QM31; 84] {
    core::array::from_fn(|index| view.point_claims[index / 28][index % 28])
}

/// Host replay of every proof-dependent component used by the read-only V6
/// program wrapper. Keeping this beside the builder catches transcript,
/// packing, Merkle and sole-fold disagreement without depending on the
/// Solana program crate.
#[allow(clippy::too_many_arguments)]
pub fn verify_v6_onefold_proof_core(
    proof: &BuiltV6OneFoldProof,
    statement: &AtomicPaymentStatementV4,
    prover_context: V6ProverContext,
    hash: HashFn,
    check_pow: bool,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    let wire = V6OneFoldWire::parse_deferred_canonicality(
        &proof.bytes,
        proof.frontier_nodes,
        proof.frontier_nodes,
    )?;
    let statement_digest = atomic_payment_statement_digest_v4(statement, hash)
        .map_err(|_| V6ProverError::Stage("V6 replay statement digest"))?;
    let context = V6TranscriptContext {
        program_id: prover_context.program_id,
        release_binding: prover_context.release_binding,
        statement_digest,
        attempt_id: prover_context.attempt_id,
    };
    let transcript = verify_v6_transcript_and_relation(
        hash,
        &wire,
        &context,
        proof.selector,
        atomic_state_only_copy_inactive_row_masks_v3(),
        check_pow,
        |view| {
            atomic_state_only_selected_masked_terminal_value_compiled_v3(
                statement,
                &terminal_claims(view),
                &view.point,
                view.lambda,
                view.chi,
                view.batching.theta,
                &view.batching.zerocheck_point,
                view.batching.mu,
                view.eta,
            )
            .is_ok_and(|expected| expected == view.terminal_claim)
        },
        |view| {
            let combined = verify_and_gamma_combine_v6_binary_openings_prepared(
                hash,
                &wire,
                view.queries,
                view.gamma_powers,
            )?;
            let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
            Ok(V6AuthenticatedQueryBatch {
                values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
                line_x: coordinates.line_x,
            })
        },
    )
    .map_err(|_| V6ProverError::Stage("V6 transcript replay"))?;
    if transcript.queries != proof.queries
        || transcript.compact_counter != proof.compact_counter
        || transcript.transcript_state_after_queries != proof.transcript_state_after_queries
    {
        return Err(V6ProverError::Stage("V6 query replay"));
    }
    Ok(transcript)
}

/// Host replay of the complete compact V7 proof-dependent path.
#[allow(clippy::too_many_arguments)]
pub fn verify_v7_compact_onefold_proof_core(
    proof: &BuiltV7CompactOneFoldProof,
    statement: &AtomicPaymentStatementV4,
    prover_context: V7ProverContext,
    hash: HashFn,
    check_pow: bool,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    let wire =
        V7CompactOneFoldWire::parse_deferred_canonicality(&proof.bytes, proof.frontier_nodes)?;
    let statement_digest = atomic_payment_statement_digest_v4(statement, hash)
        .map_err(|_| V6ProverError::Stage("V7 replay statement digest"))?;
    let context = V6TranscriptContext {
        program_id: prover_context.program_id,
        release_binding: prover_context.release_binding,
        statement_digest,
        attempt_id: prover_context.attempt_id,
    };
    let transcript = verify_v7_compact_transcript_and_relation_prepared(
        hash,
        &wire,
        &context,
        atomic_state_only_copy_inactive_row_groups_v3(),
        atomic_state_only_copy_inactive_group_masks_v3(),
        check_pow,
        |view| {
            atomic_state_only_selected_masked_terminal_value_compiled_tag73(
                statement,
                &terminal_claims(view),
                &view.point,
                view.lambda,
                view.chi,
                view.batching.theta,
                &view.batching.zerocheck_point,
                view.batching.mu,
                view.eta,
            )
            .is_ok_and(|expected| expected == view.terminal_claim)
        },
        |view| {
            let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
            let combined =
                verify_and_gamma_combine_v7_openings(hash, &wire, view.queries, view.gamma_powers)?;
            Ok(V6AuthenticatedQueryBatch {
                values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
                line_x: coordinates.line_x,
            })
        },
    )
    .map_err(|_| V6ProverError::Stage("V7 transcript replay"))?;
    if transcript.queries != proof.queries
        || transcript.selector != 0
        || transcript.compact_counter != proof.compact_counter
        || transcript.transcript_state_after_queries != proof.transcript_state_after_queries
    {
        return Err(V6ProverError::Stage("V7 query replay"));
    }
    Ok(transcript)
}

#[derive(Clone, Copy)]
enum PoolV1ProofPublic<'a> {
    PrivateTransfer(&'a PoolV1PrivateTransferPublicV1),
    Withdrawal(&'a PoolV1WithdrawalPublicV1),
    ForestPrivateTransfer(
        &'a PoolV1PrivateTransferPublicV1,
        &'a PoolV1PairLatePublicStatementV1,
    ),
    ForestWithdrawal(
        &'a PoolV1WithdrawalPublicV1,
        &'a PoolV1PairLatePublicStatementV1,
    ),
}

#[allow(clippy::too_many_arguments)]
fn verify_v7_pool_onefold_proof_core(
    proof: &BuiltV7CompactOneFoldProof,
    public: PoolV1ProofPublic<'_>,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
    check_pow: bool,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    let wire =
        V7CompactOneFoldWire::parse_deferred_canonicality(&proof.bytes, proof.frontier_nodes)?;
    let context = V6TranscriptContext {
        program_id: prover_context.program_id,
        release_binding: prover_context.release_binding,
        statement_digest,
        attempt_id: prover_context.attempt_id,
    };
    let inactive_group_masks = match public {
        PoolV1ProofPublic::PrivateTransfer(_) => {
            pool_inactive_row_masks(pool_v1_private_transfer_copy_active_row_masks_compiled_v1())
        }
        PoolV1ProofPublic::Withdrawal(_) => {
            pool_inactive_row_masks(pool_v1_withdrawal_copy_active_row_masks_compiled_v1())
        }
        PoolV1ProofPublic::ForestPrivateTransfer(_, _)
        | PoolV1ProofPublic::ForestWithdrawal(_, _) => pool_inactive_row_masks(
            &pool_v1_pair_forest_copy_active_row_masks_v1()
                .map_err(|_| V6ProverError::Stage("V7 Pool forest inactive rows"))?,
        ),
    };
    let inactive_row_groups: [u8; 64] = core::array::from_fn(|group| group as u8);
    let hiding_context = match public {
        PoolV1ProofPublic::PrivateTransfer(_) => StateOnlyHidingContext::pool_v1_private_transfer(
            statement_digest,
            prover_context.attempt_id,
        ),
        PoolV1ProofPublic::Withdrawal(_) => {
            StateOnlyHidingContext::pool_v1_withdrawal(statement_digest, prover_context.attempt_id)
        }
        PoolV1ProofPublic::ForestPrivateTransfer(_, _)
        | PoolV1ProofPublic::ForestWithdrawal(_, _) => {
            StateOnlyHidingContext::pool_v1_pair_forest_v1(
                statement_digest,
                prover_context.attempt_id,
            )
        }
    };
    let transcript = verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
        hash,
        &wire,
        &context,
        hiding_context,
        &inactive_row_groups,
        &inactive_group_masks,
        check_pow,
        |view| {
            let claims = terminal_claims(view);
            let expected = match public {
                PoolV1ProofPublic::PrivateTransfer(public) => {
                    evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                        public,
                        &claims,
                        &view.point,
                        view.lambda,
                        view.chi,
                        view.batching.theta,
                        &view.batching.zerocheck_point,
                        view.batching.mu,
                        view.eta,
                    )
                    .ok()
                }
                PoolV1ProofPublic::Withdrawal(public) => {
                    evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1(
                        public,
                        &claims,
                        &view.point,
                        view.lambda,
                        view.chi,
                        view.batching.theta,
                        &view.batching.zerocheck_point,
                        view.batching.mu,
                        view.eta,
                    )
                    .ok()
                }
                PoolV1ProofPublic::ForestPrivateTransfer(public, transition) => {
                    evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                        public,
                        transition,
                        &claims,
                        &view.point,
                        view.lambda,
                        view.chi,
                        view.batching.theta,
                        &view.batching.zerocheck_point,
                        view.batching.mu,
                        view.eta,
                    )
                    .ok()
                }
                PoolV1ProofPublic::ForestWithdrawal(public, transition) => {
                    evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(
                        public,
                        transition,
                        &claims,
                        &view.point,
                        view.lambda,
                        view.chi,
                        view.batching.theta,
                        &view.batching.zerocheck_point,
                        view.batching.mu,
                        view.eta,
                    )
                    .ok()
                }
            };
            expected.is_some_and(|expected| expected == view.terminal_claim)
        },
        |view| {
            let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
            let combined =
                verify_and_gamma_combine_v7_openings(hash, &wire, view.queries, view.gamma_powers)?;
            Ok(V6AuthenticatedQueryBatch {
                values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
                line_x: coordinates.line_x,
            })
        },
    )
    .map_err(|_| V6ProverError::Stage("V7 Pool transcript replay"))?;
    if transcript.queries != proof.queries
        || transcript.selector != 0
        || transcript.compact_counter != proof.compact_counter
        || transcript.transcript_state_after_queries != proof.transcript_state_after_queries
    {
        return Err(V6ProverError::Stage("V7 Pool query replay"));
    }
    Ok(transcript)
}

pub fn verify_v7_pool_private_transfer_onefold_proof_core(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1PrivateTransferPublicV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
    check_pow: bool,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_onefold_proof_core(
        proof,
        PoolV1ProofPublic::PrivateTransfer(public),
        statement_digest,
        prover_context,
        hash,
        check_pow,
    )
}

pub fn verify_v7_pool_withdrawal_onefold_proof_core(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1WithdrawalPublicV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
    check_pow: bool,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_onefold_proof_core(
        proof,
        PoolV1ProofPublic::Withdrawal(public),
        statement_digest,
        prover_context,
        hash,
        check_pow,
    )
}

pub fn verify_v7_pool_pair_forest_private_transfer_onefold_proof_core(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1PrivateTransferPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
    check_pow: bool,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_onefold_proof_core(
        proof,
        PoolV1ProofPublic::ForestPrivateTransfer(public, transition),
        statement_digest,
        prover_context,
        hash,
        check_pow,
    )
}

pub fn verify_v7_pool_pair_forest_withdrawal_onefold_proof_core(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1WithdrawalPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
    check_pow: bool,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_onefold_proof_core(
        proof,
        PoolV1ProofPublic::ForestWithdrawal(public, transition),
        statement_digest,
        prover_context,
        hash,
        check_pow,
    )
}

/// Replay a V6 proof through the full host verifier with work checks enabled.
pub fn verify_v6_onefold_proof_production(
    proof: &BuiltV6OneFoldProof,
    statement: &AtomicPaymentStatementV4,
    prover_context: V6ProverContext,
    hash: HashFn,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v6_onefold_proof_core(proof, statement, prover_context, hash, true)
}

/// Replay a compact V7 proof through the full host verifier with work checks.
pub fn verify_v7_compact_onefold_proof_production(
    proof: &BuiltV7CompactOneFoldProof,
    statement: &AtomicPaymentStatementV4,
    prover_context: V7ProverContext,
    hash: HashFn,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_compact_onefold_proof_core(proof, statement, prover_context, hash, true)
}

pub fn verify_v7_pool_private_transfer_onefold_proof_production(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1PrivateTransferPublicV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_private_transfer_onefold_proof_core(
        proof,
        public,
        statement_digest,
        prover_context,
        hash,
        true,
    )
}

pub fn verify_v7_pool_withdrawal_onefold_proof_production(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1WithdrawalPublicV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_withdrawal_onefold_proof_core(
        proof,
        public,
        statement_digest,
        prover_context,
        hash,
        true,
    )
}

pub fn verify_v7_pool_pair_forest_private_transfer_onefold_proof_production(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1PrivateTransferPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_pair_forest_private_transfer_onefold_proof_core(
        proof,
        public,
        transition,
        statement_digest,
        prover_context,
        hash,
        true,
    )
}

pub fn verify_v7_pool_pair_forest_withdrawal_onefold_proof_production(
    proof: &BuiltV7CompactOneFoldProof,
    public: &PoolV1WithdrawalPublicV1,
    transition: &PoolV1PairLatePublicStatementV1,
    statement_digest: [u8; 32],
    prover_context: V7ProverContext,
    hash: HashFn,
) -> Result<V6VerifiedTranscript, V6ProverError> {
    verify_v7_pool_pair_forest_withdrawal_onefold_proof_core(
        proof,
        public,
        transition,
        statement_digest,
        prover_context,
        hash,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
    use crate::state_only_hiding_rank::probe_v6_onefold_atomic_root_message_hiding_rank;
    use crate::HOST_HASH;
    use aspis_core::circle::SecureCirclePoint;
    use aspis_core::state_only_prefix::{
        StateOnlyPrefixScheduleResult, StateOnlyTranscriptScheduleResult,
        STATE_ONLY_MAX_QUERY_COUNT,
    };
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment,
        pool_v1::{
            encode_pool_v1_pair_forest_terminal_statement_v1,
            encode_pool_v1_private_transfer_public_v1, pool_v1_membership_root_v1,
            pool_v1_note_commitment, pool_v1_nullifier, pool_v1_pair_forest_output_lane_v1,
            pool_v1_tree_parent, v7_pool_pair_forest_tag73_statement_digest_v1,
            verifier_statement_payload_digest_v1, IncrementalMerkleTreeV1,
            PoolV1InputNoteWitnessV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
            PoolV1PairForestInputNoteWitnessV1, PoolV1PairForestTerminalCommonV1,
            PoolV1PairForestTerminalStatementV1, PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1,
            PoolV1PaymentRuntimeBindingV1, POOL_V1_HISTORICAL_ANCHOR_VERSION,
            POOL_V1_PAIR_TREE_DEPTH, V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
            V7_POOL_NATIVE_TAG73_RELEASE_BINDING, V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        },
        Digest, MerklePath, SpendPublic,
    };

    #[cfg(feature = "v7-final-nonce-cutoff-audit")]
    #[test]
    fn v7_final_nonce_selector_returns_ordinary_bounded_schedule() {
        let mut transcript = Transcript::new(HOST_HASH);
        transcript.absorb(label::PROFILE, b"aspis-v7-cutoff-selector-kat-v1");
        transcript.absorb(label::STATEMENT, &[0x5a; 32]);

        let cutoff = 20;
        let (nonce, tested) =
            select_v7_final_nonce_at_counter_cutoff(&transcript, 8, cutoff).unwrap();
        assert!(tested >= 1);
        assert!(transcript.grinding_ok(nonce, 8));

        let mut post_nonce = transcript;
        absorb_work(&mut post_nonce, 2, nonce);
        let schedule = derive_first_v7_compact_queries(&post_nonce).unwrap();
        assert!(schedule.counter <= cutoff);
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

    fn pool_transfer_fixture() -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PrivateTransferWitnessV1,
        PoolV1PaymentRelationContextV1<'static>,
    ) {
        let input = PoolV1InputNoteWitnessV1 {
            nullifier_key: digest(10),
            salt: digest(100),
            value: 1_000,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|level| digest(1_000 + level as u32 * 100)),
                index: 0x5_4321,
            },
        };
        let recipient = PoolV1OutputNoteWitnessV1 {
            owner_key: digest(300),
            salt: digest(400),
            value: 600,
        };
        let change = PoolV1OutputNoteWitnessV1 {
            owner_key: digest(500),
            salt: digest(600),
            value: 400,
        };
        let witness = PoolV1PrivateTransferWitnessV1 {
            input,
            recipient,
            change,
        };
        let asset_id = M31(77);
        let leaf = pool_v1_note_commitment(
            &derive_owner_key(&witness.input.nullifier_key),
            witness.input.value,
            asset_id,
            &witness.input.salt,
        );
        let anchor_root = pool_v1_membership_root_v1(leaf, &witness.input.membership).unwrap();
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root,
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            recipient_commitment: pool_v1_note_commitment(
                &witness.recipient.owner_key,
                witness.recipient.value,
                asset_id,
                &witness.recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        let context = PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: &[],
        };
        (public, witness, context)
    }

    fn pair_forest_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
        let zero = [M31::ZERO; 8];
        let mut roots = [zero; POOL_V1_PAIR_TREE_DEPTH + 1];
        roots[0] = pool_v1_tree_parent(&zero, &zero);
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
        }
        roots
    }

    fn pair_forest_snapshot_at(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        index: u64,
    ) -> PoolV1PairLiveSnapshotV1 {
        let empty = pair_forest_empty_roots();
        let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            empty[POOL_V1_PAIR_TREE_DEPTH],
            core::array::from_fn(|level| empty[level]),
            &empty,
        )
        .unwrap();
        for leaf in 0..index {
            tree = tree
                .append_one_with_empty_roots(digest(20_000 + 32 * leaf as u32), &empty)
                .unwrap()
                .0;
        }
        PoolV1PairLiveSnapshotV1 {
            pool,
            deployment_domain,
            sequence: index,
            next_pair_index: index,
            current_root: tree.root,
            frontier: tree.frontier,
        }
    }

    fn pair_forest_global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
        let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            let sibling = input.pair.membership.siblings[level];
            current = if ((input.pair.membership.index >> level) & 1) == 0 {
                pool_v1_tree_parent(&current, &sibling)
            } else {
                pool_v1_tree_parent(&sibling, &current)
            };
        }
        for level in 0..3 {
            current = if input.super_root_directions[level] {
                pool_v1_tree_parent(&input.super_root_siblings[level], &current)
            } else {
                pool_v1_tree_parent(&current, &input.super_root_siblings[level])
            };
        }
        current
    }

    fn pool_forest_transfer_fixture() -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PairForestPrivateTransferWitnessV1,
        PoolV1PaymentRelationContextV1<'static>,
        PoolV1PairLatePublicStatementV1,
        [u8; 32],
        [u8; 32],
    ) {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset_id = M31(77);
        let input_commitment =
            pool_v1_note_commitment(&derive_owner_key(&nullifier_key), 1_000, asset_id, &salt);
        let input = PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt,
                value: 1_000,
                pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
                    .unwrap(),
                selected_second: false,
                membership: PoolV1MembershipWitnessV1 {
                    siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                    index: 0x5_4321,
                },
            },
            super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
            super_root_directions: [true, false, true],
        };
        let recipient = PoolV1OutputNoteWitnessV1 {
            owner_key: digest(300),
            salt: digest(400),
            value: 600,
        };
        let change = PoolV1OutputNoteWitnessV1 {
            owner_key: digest(500),
            salt: digest(600),
            value: 400,
        };
        let witness = PoolV1PairForestPrivateTransferWitnessV1 {
            input,
            recipient,
            change,
        };
        let anchor = pair_forest_global_anchor(&witness.input);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(
                &witness.input.pair.nullifier_key,
                &witness.input.pair.salt,
            ),
            asset_id,
            recipient_commitment: pool_v1_note_commitment(
                &witness.recipient.owner_key,
                witness.recipient.value,
                asset_id,
                &witness.recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        let relation_context = PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: &[],
        };
        let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
            &public,
            &witness,
            relation_context,
            pair_forest_snapshot_at(public.pool, public.deployment_domain, 13),
        )
        .unwrap();
        let statement = PoolV1PairForestTerminalStatementV1::PrivateTransfer {
            common: PoolV1PairForestTerminalCommonV1 {
                master_account: public.pool,
                checkpoint_account: [3; 32],
                selected_lane_account: [4; 32],
                output_lane: pool_v1_pair_forest_output_lane_v1(&public.nullifier).unwrap(),
                checkpoint_sequence: public.anchor_sequence,
                historical_global_anchor: public.anchor_root,
                lane_transition: compiled.public_statement,
            },
            public,
        };
        let payload = encode_pool_v1_pair_forest_terminal_statement_v1(&statement).unwrap();
        let release_binding = V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING;
        let statement_digest = v7_pool_pair_forest_tag73_statement_digest_v1(&payload, HOST_HASH);
        (
            public,
            witness,
            relation_context,
            compiled.public_statement,
            statement_digest,
            release_binding,
        )
    }

    #[test]
    fn exact_unmined_fixture_is_accepted_and_below_hard_limit() {
        let (statement, witness) = fixture();
        let context = V6ProverContext {
            program_id: [0x11; 32],
            release_binding: [0x22; 32],
            attempt_id: [0x23; 32],
        };
        let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            context.attempt_id,
            [0x45; 32],
            [0x67; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let proof = build_v6_onefold_proof(
            &statement,
            &witness,
            context,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        assert!(proof.bytes.len() < V6_HARD_BODY_LIMIT);
        assert_eq!(
            proof.bytes.len(),
            V6_BODY_WITHOUT_FRONTIERS + 64 * proof.frontier_nodes
        );
        assert!(proof.frontier_nodes <= V6_FRONTIER_CAP_PER_TREE);
        assert!(!proof.pow_valid);
        let replay =
            verify_v6_onefold_proof_core(&proof, &statement, context, HOST_HASH, false).unwrap();
        assert_eq!(replay.queries, proof.queries);
        assert_eq!(replay.frontier_nodes, proof.frontier_nodes);

        let query_section = V6_FIXED_PACKED_FIELD_BYTES + 64 + 24;
        let mut changed_opening = proof.clone();
        changed_opening.bytes[query_section] ^= 1;
        assert!(verify_v6_onefold_proof_core(
            &changed_opening,
            &statement,
            context,
            HOST_HASH,
            false,
        )
        .is_err());

        let mut changed_fixed_field = proof.clone();
        changed_fixed_field.bytes[0] ^= 1;
        assert!(verify_v6_onefold_proof_core(
            &changed_fixed_field,
            &statement,
            context,
            HOST_HASH,
            false,
        )
        .is_err());

        let mut changed_statement = statement.clone();
        changed_statement.pool[0] ^= 1;
        assert!(verify_v6_onefold_proof_core(
            &proof,
            &changed_statement,
            context,
            HOST_HASH,
            false,
        )
        .is_err());
        eprintln!(
            "V6 honest fixture: body={} selector={} compact_counter={} frontier={}",
            proof.bytes.len(),
            proof.selector,
            proof.compact_counter,
            proof.frontier_nodes
        );
    }

    #[test]
    fn v7_compact_unmined_fixture_is_accepted_below_thirty_kib() {
        let (statement, witness) = fixture();
        let context = V7ProverContext {
            program_id: [0x11; 32],
            release_binding: [0x72; 32],
            attempt_id: [0x25; 32],
        };
        let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            context.attempt_id,
            [0x47; 32],
            [0x69; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let proof = build_v7_compact_onefold_proof(
            &statement,
            &witness,
            context,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        assert_eq!(
            proof.bytes.len(),
            V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * V7_COMPACT_DIGEST_BYTES * proof.frontier_nodes
        );
        assert!(proof.bytes.len() <= V7_COMPACT_MAX_BODY_BYTES);
        assert!(proof.frontier_nodes <= 203);
        assert!(!proof.pow_valid);
        let replay =
            verify_v7_compact_onefold_proof_core(&proof, &statement, context, HOST_HASH, false)
                .unwrap();
        assert_eq!(replay.queries, proof.queries);
        assert_eq!(replay.frontier_nodes, proof.frontier_nodes);

        let query_section = V6_FIXED_PACKED_FIELD_BYTES + 2 * V7_COMPACT_DIGEST_BYTES + 24;
        let mut changed_opening = proof.clone();
        changed_opening.bytes[query_section + V6_C1_PACKED_BYTES_PER_QUERY] ^= 1;
        assert!(verify_v7_compact_onefold_proof_core(
            &changed_opening,
            &statement,
            context,
            HOST_HASH,
            false,
        )
        .is_err());
        eprintln!(
            "V7 compact honest fixture: body={} counter={} frontier={}",
            proof.bytes.len(),
            proof.compact_counter,
            proof.frontier_nodes
        );
    }

    #[test]
    #[ignore = "RAM-intensive native Pool proof gate; run on the NUC"]
    fn v7_pool_private_transfer_unmined_proof_replays_end_to_end() {
        let (public, witness, relation_context) = pool_transfer_fixture();
        let profile_binding = V7_POOL_NATIVE_TAG73_PROFILE_BINDING;
        let release_binding = V7_POOL_NATIVE_TAG73_RELEASE_BINDING;
        let payload = encode_pool_v1_private_transfer_public_v1(&public).unwrap();
        let statement_digest = verifier_statement_payload_digest_v1(
            POOL_V1_HISTORICAL_ANCHOR_VERSION,
            &profile_binding,
            &release_binding,
            &payload,
            HOST_HASH,
        )
        .unwrap();
        let context = V7ProverContext {
            program_id: [0x11; 32],
            release_binding,
            attempt_id: [0x27; 32],
        };
        let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            context.attempt_id,
            [0x49; 32],
            [0x6b; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let proof = build_v7_pool_private_transfer_onefold_proof(
            &public,
            &witness,
            relation_context,
            statement_digest,
            context,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        assert_eq!(
            proof.bytes.len(),
            V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * V7_COMPACT_DIGEST_BYTES * proof.frontier_nodes
        );
        assert!(proof.bytes.len() <= V7_COMPACT_MAX_BODY_BYTES);
        let replay = verify_v7_pool_private_transfer_onefold_proof_core(
            &proof,
            &public,
            statement_digest,
            context,
            HOST_HASH,
            false,
        )
        .unwrap();
        assert_eq!(replay.queries, proof.queries);
        assert_eq!(replay.frontier_nodes, proof.frontier_nodes);
        eprintln!(
            "V7 Pool transfer fixture: body={} counter={} frontier={}",
            proof.bytes.len(),
            proof.compact_counter,
            proof.frontier_nodes,
        );
    }

    #[test]
    #[ignore = "RAM-intensive eight-lane Pool proof gate; run on the NUC"]
    fn v7_pool_pair_forest_transfer_unmined_proof_replays_end_to_end() {
        let (public, witness, relation_context, transition, statement_digest, release_binding) =
            pool_forest_transfer_fixture();
        let context = V7ProverContext {
            program_id: [0x11; 32],
            release_binding,
            attempt_id: [0x29; 32],
        };
        let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            context.attempt_id,
            [0x4b; 32],
            [0x6d; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let proof = build_v7_pool_pair_forest_private_transfer_onefold_proof(
            &public,
            &witness,
            relation_context,
            &transition,
            statement_digest,
            context,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        assert_eq!(
            proof.bytes.len(),
            V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * V7_COMPACT_DIGEST_BYTES * proof.frontier_nodes
        );
        assert!(proof.bytes.len() <= V7_COMPACT_MAX_BODY_BYTES);
        assert!(proof.frontier_nodes <= 203);
        let replay = verify_v7_pool_pair_forest_private_transfer_onefold_proof_core(
            &proof,
            &public,
            &transition,
            statement_digest,
            context,
            HOST_HASH,
            false,
        )
        .unwrap();
        assert_eq!(replay.queries, proof.queries);
        assert_eq!(replay.frontier_nodes, proof.frontier_nodes);
        eprintln!(
            "V7 eight-lane Pool transfer fixture: body={} counter={} frontier={}",
            proof.bytes.len(),
            proof.compact_counter,
            proof.frontier_nodes,
        );
    }

    /// RAM-intensive release gate.  It binds the exact V6 transcript's
    /// gamma, kappa, eta, semantic point and q16 schedule to the conservative
    /// log-20 root-message rank model.  OOD-only fields are intentionally
    /// neutral because this target stops at the complete gamma-batched root
    /// message, before any linear PCS/OOD post-processing.
    #[test]
    #[ignore = "release rank gate; run on the NUC"]
    fn v6_log20_root_message_hiding_rank_gate() {
        let (statement, witness) = fixture();
        let context = V6ProverContext {
            program_id: [0x11; 32],
            release_binding: [0x22; 32],
            attempt_id: [0x24; 32],
        };
        let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            context.attempt_id,
            [0x46; 32],
            [0x68; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let proof = build_v6_onefold_proof(
            &statement,
            &witness,
            context,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        let wire = V6OneFoldWire::parse_deferred_canonicality(
            &proof.bytes,
            proof.frontier_nodes,
            proof.frontier_nodes,
        )
        .unwrap();
        let statement_digest = atomic_payment_statement_digest_v4(&statement, HOST_HASH).unwrap();
        let transcript_context = V6TranscriptContext {
            program_id: context.program_id,
            release_binding: context.release_binding,
            statement_digest,
            attempt_id: context.attempt_id,
        };
        let mut semantic_schedule = None;
        let transcript = verify_v6_transcript_and_relation(
            HOST_HASH,
            &wire,
            &transcript_context,
            proof.selector,
            atomic_state_only_copy_inactive_row_masks_v3(),
            false,
            |view| {
                semantic_schedule = Some((
                    view.lambda,
                    view.chi,
                    view.batching,
                    view.eta,
                    view.point,
                    view.terminal_claim,
                ));
                atomic_state_only_selected_masked_terminal_value_compiled_v3(
                    &statement,
                    &terminal_claims(view),
                    &view.point,
                    view.lambda,
                    view.chi,
                    view.batching.theta,
                    &view.batching.zerocheck_point,
                    view.batching.mu,
                    view.eta,
                )
                .is_ok_and(|expected| expected == view.terminal_claim)
            },
            |view| {
                let combined = verify_and_gamma_combine_v6_binary_openings_prepared(
                    HOST_HASH,
                    &wire,
                    view.queries,
                    view.gamma_powers,
                )?;
                let coordinates = prepare_v6_onefold_coordinates(view.queries)?;
                Ok(V6AuthenticatedQueryBatch {
                    values: fold_v6_onefold_queries(&combined, &coordinates, view.alpha0),
                    line_x: coordinates.line_x,
                })
            },
        )
        .unwrap();
        let (lambda, chi, batching, eta, z, masked_terminal_claim) =
            semantic_schedule.expect("accepted V6 transcript must invoke terminal callback");
        let mut rank_queries = [0u32; STATE_ONLY_MAX_QUERY_COUNT];
        rank_queries[..V6_QUERY_COUNT].copy_from_slice(&transcript.queries);
        let initial_mask_claim = aspis_core::v6_onefold::packed_qm31_at(
            wire.fixed_fields_packed,
            V6_INITIAL_CLAIM_OFFSET,
        )
        .expect("accepted V6 wire has a canonical initial mask claim");
        let neutral_circle_point = SecureCirclePoint {
            x: QM31::ONE,
            y: QM31::ZERO,
        };
        let schedule = StateOnlyTranscriptScheduleResult {
            prefix: StateOnlyPrefixScheduleResult {
                lambda,
                chi,
                batching,
                initial_mask_claim,
                eta,
                z,
                masked_terminal_claim,
                gamma: transcript.gamma,
                point_scale: transcript.kappa,
                state_after_gamma: [0u8; 32],
            },
            circle_ood_points: [neutral_circle_point; 2],
            line_ood_points: [[QM31::ZERO; 2]; 3],
            mu: [[QM31::ZERO; 2]; 4],
            alpha: transcript.alpha,
            state_before_grinding: [0u8; 32],
            queries: rank_queries,
            query_count: V6_QUERY_COUNT,
            state_after_queries: transcript.transcript_state_after_queries,
        };
        let report = probe_v6_onefold_atomic_root_message_hiding_rank(&schedule).unwrap();
        eprintln!(
            "V6 hiding rank: pcs={} q={} raw={} sc={}/{} pcs={}/{} ambient_deficit={} coupled_physical={:?} coupled_legal={:?} coupled_helper={:?} elapsed_ms={}",
            report.pcs_schedule,
            report.query_count,
            report.raw_opening_minor.source_columns.len(),
            report.masked_sumcheck_rank,
            report.masked_sumcheck_m31,
            report.joint_pcs_rank,
            report.joint_pcs_declared_rank,
            report.baseline_ambient_deficit_m31,
            report.witness_coupled_physical_contained,
            report.witness_coupled_legal_contained,
            report.witness_coupled_helper_contained,
            report.elapsed_millis,
        );
        assert_eq!(report.pcs_schedule, "v6_log20_root_message_exact_sequence");
        assert_eq!(report.query_count, V6_QUERY_COUNT);
        assert!(!report.tail_qm31_probe);
        assert!(!report.shared_linear_factor_probe);
        assert_eq!(report.coordinate_factored_mask_columns, 0);
        assert!(!report.late_switch_probe);
        assert!(report.witness_difference_probe);
        assert!(report.baseline_valid_witness_containment);
        assert_eq!(report.witness_coupled_physical_contained, Some(true));
        assert_eq!(report.witness_coupled_legal_contained, Some(true));
        assert_eq!(report.witness_coupled_helper_contained, Some(true));
        assert!(report.witness_coupled_terminal_identity_guard);
        assert!(report.witness_mask_raw_kernel_terminal_zero_guard);
        assert!(report.witness_h_zero_sumcheck_terminal_guard);
        assert!(report.witness_mask_sumcheck_equals_terminal_kernel);
        assert!(report.witness_semantic_sparse_dense_guard);
    }
}
