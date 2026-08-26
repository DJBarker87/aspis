//! Exact transcript and relation driver for the V6 26+3 one-fold profile and
//! its compact V7 wire successor.
//!
//! The driver consumes every fixed packed field exactly once, reconstructs
//! the two omitted sumcheck coefficients from their checked boundaries,
//! checks all three work witnesses in protocol order, and derives the first
//! compact q16 schedule for one of three public selector domains.  It does
//! not authenticate the query records or perform the circle fold; those use
//! the returned `gamma`, first `alpha`, query schedule, and decoded final
//! vector in [`crate::v6_onefold`].

use alloc::{boxed::Box, vec, vec::Vec};

use crate::field::{
    qm31_add_sum_products3_prepared, qm31_dot3, qm31_power_table, qm31_sum_products3,
    PreparedQm31Multiplier, CM31, M31, M31_QUARTER, QM31,
};
use crate::proof::M31_CIRCLE_BASIS_DISCRIMINATOR;
use crate::state_only_hiding::{
    begin_state_only_hiding_precommit, begin_state_only_masked_sumcheck, StateOnlyHidingContext,
};
use crate::state_only_spend_query::{
    StateOnlySpendQueryPowers, SPEND_D_GENERATOR_INDEX, SPEND_TOTAL_COLUMNS,
};
use crate::state_only_sumcheck::{
    begin_state_only_zerocheck, evaluate_state_only_polynomial, StateOnlySumcheckPolynomial,
};
use crate::statement_sumcheck::PaymentConstraintChallenges;
use crate::sumcheck::{boundary_sum, evaluate, SumcheckPolynomial, WeightAccumulator};
use crate::transcript::{label, Transcript};
use crate::v6_onefold::{
    binary_frontier_nodes, V6FixedFieldReader, V6OneFoldWire, V6WireError, V6_C1_TREE_TAG,
    V6_C2_TREE_TAG, V6_FINAL_QM31_VALUES, V6_FRONTIER_CAP_PER_TREE, V6_POINT_CLAIM_ROWS,
    V6_QUERY_COUNT, V6_RELATION_ROUNDS, V6_RELATION_SENT_VALUES, V6_SEMANTIC_ROUNDS,
    V6_SEMANTIC_SENT_VALUES, V6_TOTAL_COLUMNS,
};
use crate::v6_query_batch::{add_v6_final256_query_batch, V6AuthenticatedQueryBatch};
use crate::v7_onefold::{
    derive_first_v7_compact_queries, V7CompactOneFoldWire, V7_COMPACT_BATCH_WORK_BITS,
    V7_COMPACT_FINAL_WORK_BITS, V7_COMPACT_FOLD_WORK_BITS, V7_COMPACT_PROFILE_BINDING,
};
use crate::v7_merkle208::{V7_C1_TREE_TAG, V7_C2_TREE_TAG, V7_MERKLE_DIGEST_BYTES};
use crate::HashFn;

pub const V6_BATCH_WORK_BITS: u8 = 34;
pub const V6_FOLD_WORK_BITS: u8 = 31;
pub const V6_FINAL_WORK_BITS: u8 = 34;
pub const V6_QUERY_SELECTOR_COUNT: u8 = 3;
pub const V6_COMPACT_DRAW_CAP: u8 = 8;
pub const V6_QUERY_DRAW_LIMIT: usize = 64;
pub const V6_TREE_DEPTH: u8 = 18;

/// Frozen byte-level profile description absorbed before every deployment,
/// statement, root, or challenge. Multi-byte integers are little-endian.
pub const V6_PROFILE_BINDING: [u8; 32] = [
    b'A', b'V', b'6', b'O', b'F', b'0', b'0', b'1', // magic/version
    26, 3, 10, 16, 0xd1, 0x00, 3, 10, // width, B, q, cap, claim rows, rounds
    27, 4, 6, 34, 31, 34, 0x70, 0xf0, // compact widths, work, tree tags
    0x81, 0x02, 0x00, 0x01, 20, 18, 1, 0, // 641 fields, final256, logs, rev
];

const V6_ROOT_SALT_DOMAIN: &[u8] = b"aspis-v6-public-root-salt-v1";
const V7_ROOT_SALT_DOMAIN: &[u8] = b"aspis-v7-public-root-salt-v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V6TranscriptContext {
    pub program_id: [u8; 32],
    /// Frozen release identifier supplied by the compiled verifier, not by
    /// proof data. It is finalized together with the deployed program.
    pub release_binding: [u8; 32],
    pub statement_digest: [u8; 32],
    /// The proof account address. It is fixed before masks and roots exist and
    /// doubles as the public one-attempt mask nonce.
    pub attempt_id: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6WorkStage {
    Batch,
    Fold,
    Final,
}

/// Probe-only checkpoints inside the relation tail. Production verification
/// supplies an inlinable no-op callback, so these checkpoints do not alter
/// the accepted transcript or its arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6RelationDiagnosticPhase {
    Start,
    PreparedWeights,
    CircleSamples,
    RelationFields,
    RoundZero,
    Final256,
    Queries,
    QueryBatch,
    RoundOnePolynomial,
    RoundOneWeights,
    RoundOne,
    RoundTwoPolynomial,
    RoundTwoWeights,
    RoundTwo,
    RoundThreePolynomial,
    RoundThreeWeights,
    RoundThree,
    Terminal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6TranscriptError {
    Wire(V6WireError),
    HidingContext,
    ChallengeSampling,
    SemanticBoundary {
        round: usize,
    },
    TerminalRejected,
    WorkRejected {
        stage: V6WorkStage,
    },
    RelationShape,
    RelationBoundary {
        round: usize,
    },
    RelationTerminal,
    QuerySelector,
    CompactCandidatesExhausted,
    FrontierCountMismatch {
        expected: usize,
        c1: usize,
        c2: usize,
    },
}

impl From<V6WireError> for V6TranscriptError {
    fn from(error: V6WireError) -> Self {
        Self::Wire(error)
    }
}

#[derive(Debug)]
pub struct V6SemanticView<'a> {
    pub lambda: QM31,
    pub chi: QM31,
    pub batching: PaymentConstraintChallenges,
    pub eta: QM31,
    pub point: [QM31; V6_SEMANTIC_ROUNDS],
    pub terminal_claim: QM31,
    pub point_claims: &'a [[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS],
}

#[derive(Debug)]
pub struct V6VerifiedTranscript {
    pub gamma: QM31,
    pub kappa: QM31,
    pub alpha: [QM31; V6_RELATION_ROUNDS],
    pub queries: [u32; V6_QUERY_COUNT],
    pub selector: u8,
    pub compact_counter: u8,
    pub frontier_nodes: usize,
    pub semantic_point: [QM31; V6_SEMANTIC_ROUNDS],
    pub query_batch_challenge: QM31,
    pub folded_query_sum: QM31,
    pub transcript_state_after_queries: [u8; 32],
}

/// Inputs needed to authenticate and fold the selected layer-zero fibres.
/// The caller computes these values from the two committed Merkle trees; the
/// relation tail then proves their random linear combination equals the
/// disclosed final-256 object.
#[derive(Clone, Copy, Debug)]
pub struct V6QueryBatchView<'a> {
    pub gamma: QM31,
    pub gamma_powers: &'a StateOnlySpendQueryPowers,
    pub d_power: QM31,
    pub alpha0: QM31,
    /// Reserved for profiles that need direct access to the final object. V6
    /// and the selected full-C2 V7 wire both keep this `None`.
    pub final256_coefficients: Option<&'a [QM31; V6_FINAL_QM31_VALUES]>,
    pub queries: [u32; V6_QUERY_COUNT],
    pub selector: u8,
    pub compact_counter: u8,
    pub frontier_nodes: usize,
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

fn absorb_c1_root(transcript: &mut Transcript, root: &[u8; 32], salt: &[u8; 32]) {
    let mut record = [0u8; 65];
    record[0] = 0;
    record[1..33].copy_from_slice(root);
    record[33..].copy_from_slice(salt);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn absorb_c2_root(transcript: &mut Transcript, root: &[u8; 32], salt: &[u8; 32]) {
    let mut record = [0u8; 64];
    record[..32].copy_from_slice(root);
    record[32..].copy_from_slice(salt);
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &record);
}

fn absorb_v7_c1_root(
    transcript: &mut Transcript,
    root: &[u8; V7_MERKLE_DIGEST_BYTES],
    salt: &[u8; 32],
) {
    let mut record = [0u8; 1 + V7_MERKLE_DIGEST_BYTES + 32];
    record[0] = 0;
    record[1..1 + V7_MERKLE_DIGEST_BYTES].copy_from_slice(root);
    record[1 + V7_MERKLE_DIGEST_BYTES..].copy_from_slice(salt);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn absorb_v7_c2_root(
    transcript: &mut Transcript,
    root: &[u8; V7_MERKLE_DIGEST_BYTES],
    salt: &[u8; 32],
) {
    let mut record = [0u8; V7_MERKLE_DIGEST_BYTES + 32];
    record[..V7_MERKLE_DIGEST_BYTES].copy_from_slice(root);
    record[V7_MERKLE_DIGEST_BYTES..].copy_from_slice(salt);
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &record);
}

#[inline(never)]
fn begin_v6_transcript(
    hash: HashFn,
    context: &V6TranscriptContext,
    wire: &V6OneFoldWire<'_>,
) -> Result<(Transcript, QM31, QM31, PaymentConstraintChallenges), V6TranscriptError> {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &V6_PROFILE_BINDING);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    let mut deployment = [0u8; 64];
    deployment[..32].copy_from_slice(&context.program_id);
    deployment[32..].copy_from_slice(&context.release_binding);
    transcript.absorb(label::V6_DEPLOYMENT_CONTEXT, &deployment);
    transcript.absorb(label::STATEMENT, &context.statement_digest);
    begin_state_only_hiding_precommit(
        &mut transcript,
        StateOnlyHidingContext::atomic_spend_v3(context.statement_digest, context.attempt_id),
    )
    .map_err(|_| V6TranscriptError::HidingContext)?;

    let c1_salt = public_root_salt(hash, context, V6_C1_TREE_TAG);
    absorb_c1_root(&mut transcript, wire.c1_root, &c1_salt);
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;

    let c2_salt = public_root_salt(hash, context, V6_C2_TREE_TAG);
    absorb_c2_root(&mut transcript, wire.c2_root, &c2_salt);
    let batching = begin_state_only_zerocheck(&mut transcript)
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    Ok((transcript, lambda, chi, batching))
}

#[inline(never)]
fn begin_v7_compact_transcript_with_hiding_context(
    hash: HashFn,
    context: &V6TranscriptContext,
    wire: &V7CompactOneFoldWire<'_>,
    hiding_context: StateOnlyHidingContext,
) -> Result<(Transcript, QM31, QM31, PaymentConstraintChallenges), V6TranscriptError> {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &V7_COMPACT_PROFILE_BINDING);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    let mut deployment = [0u8; 64];
    deployment[..32].copy_from_slice(&context.program_id);
    deployment[32..].copy_from_slice(&context.release_binding);
    transcript.absorb(label::V7_DEPLOYMENT_CONTEXT, &deployment);
    transcript.absorb(label::STATEMENT, &context.statement_digest);
    begin_state_only_hiding_precommit(&mut transcript, hiding_context)
    .map_err(|_| V6TranscriptError::HidingContext)?;

    let c1_salt = v7_public_root_salt(hash, context, V7_C1_TREE_TAG);
    absorb_v7_c1_root(&mut transcript, wire.c1_root, &c1_salt);
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;

    let c2_salt = v7_public_root_salt(hash, context, V7_C2_TREE_TAG);
    absorb_v7_c2_root(&mut transcript, wire.c2_root, &c2_salt);
    let batching = begin_state_only_zerocheck(&mut transcript)
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    Ok((transcript, lambda, chi, batching))
}

#[inline(never)]
fn verify_compact_semantic_sumcheck(
    transcript: &mut Transcript,
    fields: &mut V6FixedFieldReader<'_>,
) -> Result<(QM31, [QM31; V6_SEMANTIC_ROUNDS], QM31), V6TranscriptError> {
    let initial_claim = fields.next_qm31()?;
    let eta = begin_state_only_masked_sumcheck(transcript, initial_claim)
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    let mut point = [QM31::ZERO; V6_SEMANTIC_ROUNDS];
    let mut running_claim = initial_claim;

    for round in 0..V6_SEMANTIC_ROUNDS {
        let mut polynomial: StateOnlySumcheckPolynomial = [QM31::ZERO; 28];
        let mut framed = [0u8; 1 + V6_SEMANTIC_SENT_VALUES * 16];
        framed[0] = round as u8;
        polynomial[0] = fields.next_qm31()?;
        polynomial[0].write_le_bytes(&mut framed[1..17]);
        let first = polynomial[0];
        let mut tail_limbs = [
            2 * u64::from(first.c0.a.0),
            2 * u64::from(first.c0.b.0),
            2 * u64::from(first.c1.a.0),
            2 * u64::from(first.c1.b.0),
        ];
        for sent in 1..V6_SEMANTIC_SENT_VALUES {
            let coefficient = sent + 1;
            let value = fields.next_qm31()?;
            polynomial[coefficient] = value;
            value.write_le_bytes(&mut framed[1 + sent * 16..][..16]);
            tail_limbs[0] += u64::from(value.c0.a.0);
            tail_limbs[1] += u64::from(value.c0.b.0);
            tail_limbs[2] += u64::from(value.c1.a.0);
            tail_limbs[3] += u64::from(value.c1.b.0);
        }
        let tail_sum = QM31 {
            c0: CM31::new(
                M31::reduce_u64(tail_limbs[0]),
                M31::reduce_u64(tail_limbs[1]),
            ),
            c1: CM31::new(
                M31::reduce_u64(tail_limbs[2]),
                M31::reduce_u64(tail_limbs[3]),
            ),
        };
        polynomial[1] = running_claim.sub(tail_sum);

        // c1 is absent from the compact wire and is defined by this exact
        // boundary equation. Recomputing p(0)+p(1) would therefore be a
        // tautological second scan, not an additional proof check.
        debug_assert_eq!(
            crate::state_only_sumcheck::state_only_boundary_sum(&polynomial),
            running_claim
        );
        transcript.absorb(label::V6_COMPACT_SEMANTIC_ROUND, &framed);
        let challenge = transcript
            .challenge_qm31()
            .map_err(|_| V6TranscriptError::ChallengeSampling)?;
        running_claim = evaluate_state_only_polynomial(&polynomial, challenge);
        point[round] = challenge;
    }
    Ok((eta, point, running_claim))
}

#[inline(never)]
fn decode_and_absorb_point_claims(
    transcript: &mut Transcript,
    fields: &mut V6FixedFieldReader<'_>,
) -> Result<Box<[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS]>, V6TranscriptError> {
    let mut claims = Box::new([[QM31::ZERO; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS]);
    let mut encoded = vec![0u8; V6_POINT_CLAIM_ROWS * V6_TOTAL_COLUMNS * 16];
    for row in 0..V6_POINT_CLAIM_ROWS {
        for column in 0..V6_TOTAL_COLUMNS {
            let ordinal = row * V6_TOTAL_COLUMNS + column;
            let value = fields.next_qm31()?;
            claims[row][column] = value;
            value.write_le_bytes(&mut encoded[ordinal * 16..][..16]);
        }
    }
    transcript.absorb(label::V6_POINT_CLAIMS, &encoded);
    Ok(claims)
}

fn work_nonce_bytes(work_nonces: &[u8; 24], stage: V6WorkStage) -> u64 {
    let offset = match stage {
        V6WorkStage::Batch => 0,
        V6WorkStage::Fold => 8,
        V6WorkStage::Final => 16,
    };
    u64::from_le_bytes(work_nonces[offset..offset + 8].try_into().unwrap())
}

fn check_and_absorb_work(
    transcript: &mut Transcript,
    nonce: u64,
    bits: u8,
    stage: V6WorkStage,
    check_pow: bool,
) -> Result<(), V6TranscriptError> {
    if check_pow && !transcript.grinding_ok(nonce, bits) {
        return Err(V6TranscriptError::WorkRejected { stage });
    }
    match stage {
        V6WorkStage::Batch => {
            transcript.absorb(label::M31_PAYMENT_BATCH_POW_NONCE, &nonce.to_le_bytes())
        }
        V6WorkStage::Fold => {
            let mut record = [0u8; 9];
            record[0] = 0;
            record[1..].copy_from_slice(&nonce.to_le_bytes());
            transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
        }
        V6WorkStage::Final => transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes()),
    }
    Ok(())
}

fn gamma_point_claims_and_query_powers(
    gamma: QM31,
    claims: &[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS],
) -> ([QM31; V6_POINT_CLAIM_ROWS], StateOnlySpendQueryPowers, QM31) {
    debug_assert_eq!(V6_TOTAL_COLUMNS, SPEND_TOTAL_COLUMNS);
    let powers = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma);
    (
        qm31_dot3(&powers, [&claims[0], &claims[1], &claims[2]]),
        StateOnlySpendQueryPowers::from_full_table(&powers),
        powers[SPEND_D_GENERATOR_INDEX],
    )
}

/// The exact three PCS points consumed by the maintained selected-hiding
/// terminal: `z`, binary successor modulo 1024, and low-bit XOR 12.
pub fn v6_statement_points(z: &[QM31; V6_SEMANTIC_ROUNDS]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let last = z.len() - 1;
    successor[last] = QM31::ONE.sub(z[last]);
    let mut carry = z[last];
    for coordinate in (0..last).rev() {
        let bit = z[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    let mut xor12 = *z;
    for coordinate in [7usize, 6] {
        xor12[coordinate] = QM31::ONE.sub(xor12[coordinate]);
    }
    [*z, successor, xor12]
}

fn decode_compact_relation_polynomial(
    sent: &[QM31; V6_RELATION_SENT_VALUES],
    running_claim: QM31,
) -> SumcheckPolynomial {
    let mut polynomial = [QM31::ZERO; 7];
    polynomial[0] = sent[0];
    polynomial[1] = sent[1];
    polynomial[2] = sent[2];
    polynomial[3] = sent[3];
    polynomial[5] = sent[4];
    polynomial[6] = sent[5];
    polynomial[4] = running_claim.mul_m31(M31_QUARTER).sub(polynomial[0]);
    // c4 is the compact wire's omitted boundary coefficient, so the check is
    // true by construction just as it is for semantic c1 above.
    debug_assert_eq!(boundary_sum(&polynomial), running_claim);
    polynomial
}

#[inline(never)]
fn decode_compact_relation_fields(
    fields: &mut V6FixedFieldReader<'_>,
) -> Result<Box<[[QM31; V6_RELATION_SENT_VALUES]; V6_RELATION_ROUNDS]>, V6TranscriptError> {
    let mut decoded = Box::new([[QM31::ZERO; V6_RELATION_SENT_VALUES]; V6_RELATION_ROUNDS]);
    for round in decoded.iter_mut() {
        for value in round {
            *value = fields.next_qm31()?;
        }
    }
    Ok(decoded)
}

fn absorb_compact_relation_polynomial(
    transcript: &mut Transcript,
    round: usize,
    polynomial: &SumcheckPolynomial,
) {
    let mut framed = [0u8; 1 + V6_RELATION_SENT_VALUES * 16];
    framed[0] = round as u8;
    for (sent, coefficient) in [0usize, 1, 2, 3, 5, 6].into_iter().enumerate() {
        polynomial[coefficient].write_le_bytes(&mut framed[1 + sent * 16..][..16]);
    }
    transcript.absorb(label::V6_COMPACT_RELATION_ROUND, &framed);
}

fn fold_values_prefix<const INPUT: usize>(values: &mut [QM31; V6_FINAL_QM31_VALUES], alpha: QM31) {
    debug_assert!(INPUT <= V6_FINAL_QM31_VALUES && INPUT % 4 == 0);
    let alpha2 = alpha.square();
    let alpha3 = alpha2.mul(alpha);
    let prepared = [
        PreparedQm31Multiplier::new(alpha),
        PreparedQm31Multiplier::new(alpha2),
        PreparedQm31Multiplier::new(alpha3),
    ];
    let next_len = INPUT / 4;
    for index in 0..next_len {
        let offset = 4 * index;
        values[index] = qm31_add_sum_products3_prepared(
            values[offset],
            &prepared,
            &[values[offset + 1], values[offset + 2], values[offset + 3]],
        );
    }
}

#[inline(never)]
fn decode_and_absorb_final256(
    transcript: &mut Transcript,
    fields: &mut V6FixedFieldReader<'_>,
) -> Result<Box<[QM31; V6_FINAL_QM31_VALUES]>, V6TranscriptError> {
    let mut decoded = Vec::with_capacity(V6_FINAL_QM31_VALUES);
    let mut encoded = vec![0u8; V6_FINAL_QM31_VALUES * 16];
    for index in 0..V6_FINAL_QM31_VALUES {
        let value = fields.next_qm31()?;
        decoded.push(value);
        value.write_le_bytes(&mut encoded[index * 16..][..16]);
    }
    transcript.absorb(label::V6_FINAL256, &encoded);
    Ok(decoded
        .into_boxed_slice()
        .try_into()
        .expect("the fixed V6 final vector has 256 entries"))
}

#[inline(never)]
fn derive_first_compact_queries(
    transcript: &Transcript,
    selector: u8,
) -> Result<([u32; V6_QUERY_COUNT], u8, usize, [u8; 32], Transcript), V6TranscriptError> {
    if selector >= V6_QUERY_SELECTOR_COUNT {
        return Err(V6TranscriptError::QuerySelector);
    }
    for counter in 0..V6_COMPACT_DRAW_CAP {
        let mut candidate_transcript = transcript.clone();
        candidate_transcript.absorb(label::V6_QUERY_CANDIDATE, &[selector, counter]);
        let candidate = candidate_transcript
            .challenge_queries_without_replacement(
                V6_QUERY_COUNT,
                1u32 << V6_TREE_DEPTH,
                V6_QUERY_DRAW_LIMIT,
            )
            .map_err(|_| V6TranscriptError::ChallengeSampling)?;
        let candidate: [u32; V6_QUERY_COUNT] = candidate
            .try_into()
            .map_err(|_| V6TranscriptError::ChallengeSampling)?;
        let frontier = binary_frontier_nodes(candidate, V6_TREE_DEPTH)?;
        if frontier <= V6_FRONTIER_CAP_PER_TREE {
            return Ok((
                candidate,
                counter,
                frontier,
                candidate_transcript.diagnostic_state(),
                candidate_transcript,
            ));
        }
    }
    Err(V6TranscriptError::CompactCandidatesExhausted)
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn finish_onefold_relation<QueryFold, DeriveQueries, Trace>(
    mut transcript: Transcript,
    work_nonces: &[u8; 24],
    c1_frontier: &[u8],
    c2_frontier: &[u8],
    work_bits: [u8; 3],
    selector: u8,
    frontier_node_bytes: usize,
    query_batch_labels: (u8, u8),
    expose_final256_to_query_fold: bool,
    derive_queries: DeriveQueries,
    mut fields: V6FixedFieldReader<'_>,
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
    semantic_point: [QM31; V6_SEMANTIC_ROUNDS],
    point_claims: &[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS],
    query_fold: QueryFold,
    mut trace: Trace,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
    DeriveQueries: FnOnce(
        &Transcript,
    ) -> Result<
        ([u32; V6_QUERY_COUNT], u8, usize, [u8; 32], Transcript),
        V6TranscriptError,
    >,
    Trace: FnMut(V6RelationDiagnosticPhase),
{
    trace(V6RelationDiagnosticPhase::Start);
    check_and_absorb_work(
        &mut transcript,
        work_nonce_bytes(work_nonces, V6WorkStage::Batch),
        work_bits[0],
        V6WorkStage::Batch,
        check_pow,
    )?;
    let gamma = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    let inactive_claim = fields.next_qm31()?;
    let mut inactive_bytes = [0u8; 16];
    inactive_claim.write_le_bytes(&mut inactive_bytes);
    transcript.absorb(label::V6_INACTIVE_CLAIM, &inactive_bytes);
    let kappa = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;

    let points = v6_statement_points(&semantic_point);
    let point_scales = [QM31::ONE, kappa, kappa.square()];
    let (combined_claims, gamma_powers, d_power) =
        gamma_point_claims_and_query_powers(gamma, point_claims);
    let gamma_powers = Box::new(gamma_powers);
    let mut running_claim = inactive_claim.add(qm31_sum_products3(point_scales, combined_claims));
    let mut weights = WeightAccumulator::empty(10);
    for row in 0..V6_POINT_CLAIM_ROWS {
        weights
            .add_multilinear(point_scales[row], points[row].to_vec())
            .map_err(|_| V6TranscriptError::RelationShape)?;
    }
    weights
        .add_grouped_64x16_binary_masks_deferred_prepared(inactive_row_groups, inactive_group_masks)
        .map_err(|_| V6TranscriptError::RelationShape)?;
    trace(V6RelationDiagnosticPhase::PreparedWeights);

    for sample in 0..2 {
        let point = transcript
            .challenge_secure_circle_point()
            .map_err(|_| V6TranscriptError::ChallengeSampling)?;
        let value = fields.next_qm31()?;
        let mut record = [0u8; 17];
        record[0] = sample as u8;
        value.write_le_bytes(&mut record[1..]);
        transcript.absorb(label::V6_CIRCLE_OOD_VALUE, &record);
        let mix = transcript
            .challenge_qm31()
            .map_err(|_| V6TranscriptError::ChallengeSampling)?;
        weights
            .add_circle_tensor(mix, point)
            .map_err(|_| V6TranscriptError::RelationShape)?;
        running_claim = running_claim.add(mix.mul(value));
    }
    trace(V6RelationDiagnosticPhase::CircleSamples);

    // Relation rounds precede final256 in the packed wire, whereas the
    // transcript consumes only round zero before final256. Decode this tiny
    // crossing buffer once so every packed field still follows one streaming
    // pass.
    let relation_fields = decode_compact_relation_fields(&mut fields)?;
    trace(V6RelationDiagnosticPhase::RelationFields);

    let mut alpha = [QM31::ZERO; V6_RELATION_ROUNDS];
    let first = decode_compact_relation_polynomial(&relation_fields[0], running_claim);
    absorb_compact_relation_polynomial(&mut transcript, 0, &first);
    check_and_absorb_work(
        &mut transcript,
        work_nonce_bytes(work_nonces, V6WorkStage::Fold),
        work_bits[1],
        V6WorkStage::Fold,
        check_pow,
    )?;
    alpha[0] = transcript
        .challenge_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    running_claim = evaluate(&first, alpha[0]);
    weights.fold_deferred_relation_arity4(alpha[0]);
    trace(V6RelationDiagnosticPhase::RoundZero);

    let mut folded_values = decode_and_absorb_final256(&mut transcript, &mut fields)?;
    fields.finish()?;
    trace(V6RelationDiagnosticPhase::Final256);

    check_and_absorb_work(
        &mut transcript,
        work_nonce_bytes(work_nonces, V6WorkStage::Final),
        work_bits[2],
        V6WorkStage::Final,
        check_pow,
    )?;
    let (
        queries,
        compact_counter,
        frontier_nodes,
        transcript_state_after_queries,
        accepted_query_transcript,
    ) = derive_queries(&transcript)?;
    transcript = accepted_query_transcript;
    if frontier_node_bytes == 0
        || c1_frontier.len() % frontier_node_bytes != 0
        || c2_frontier.len() % frontier_node_bytes != 0
    {
        return Err(V6TranscriptError::Wire(V6WireError::WrongLength));
    }
    let c1_nodes = c1_frontier.len() / frontier_node_bytes;
    let c2_nodes = c2_frontier.len() / frontier_node_bytes;
    if c1_nodes != frontier_nodes || c2_nodes != frontier_nodes {
        return Err(V6TranscriptError::FrontierCountMismatch {
            expected: frontier_nodes,
            c1: c1_nodes,
            c2: c2_nodes,
        });
    }
    transcript.absorb(query_batch_labels.0, &[]);
    let query_batch_challenge = transcript
        .challenge_nonzero_qm31()
        .map_err(|_| V6TranscriptError::ChallengeSampling)?;
    trace(V6RelationDiagnosticPhase::Queries);
    let authenticated_queries = {
        let query_view = V6QueryBatchView {
            gamma,
            gamma_powers: &gamma_powers,
            d_power,
            alpha0: alpha[0],
            final256_coefficients: if expose_final256_to_query_fold {
                Some(folded_values.as_ref())
            } else {
                None
            },
            queries,
            selector,
            compact_counter,
            frontier_nodes,
        };
        query_fold(&query_view).map_err(V6TranscriptError::Wire)?
    };
    let query_claim = add_v6_final256_query_batch(
        &mut weights,
        &mut running_claim,
        queries,
        authenticated_queries,
        query_batch_challenge,
    )
    .map_err(|_| V6TranscriptError::RelationShape)?;
    let mut query_claim_bytes = [0u8; 16];
    query_claim.write_le_bytes(&mut query_claim_bytes);
    transcript.absorb(query_batch_labels.1, &query_claim_bytes);
    trace(V6RelationDiagnosticPhase::QueryBatch);

    for round in 1..V6_RELATION_ROUNDS {
        let polynomial = decode_compact_relation_polynomial(&relation_fields[round], running_claim);
        absorb_compact_relation_polynomial(&mut transcript, round, &polynomial);
        alpha[round] = transcript
            .challenge_qm31()
            .map_err(|_| V6TranscriptError::ChallengeSampling)?;
        running_claim = evaluate(&polynomial, alpha[round]);
        trace(match round {
            1 => V6RelationDiagnosticPhase::RoundOnePolynomial,
            2 => V6RelationDiagnosticPhase::RoundTwoPolynomial,
            _ => V6RelationDiagnosticPhase::RoundThreePolynomial,
        });
        weights.fold_deferred_relation_arity4(alpha[round]);
        if round == 1 && !weights.merge_equal_multilinear_components(0, 2) {
            return Err(V6TranscriptError::RelationShape);
        }
        trace(match round {
            1 => V6RelationDiagnosticPhase::RoundOneWeights,
            2 => V6RelationDiagnosticPhase::RoundTwoWeights,
            _ => V6RelationDiagnosticPhase::RoundThreeWeights,
        });
        match round {
            1 => fold_values_prefix::<256>(&mut folded_values, alpha[round]),
            2 => fold_values_prefix::<64>(&mut folded_values, alpha[round]),
            _ => fold_values_prefix::<16>(&mut folded_values, alpha[round]),
        }
        trace(match round {
            1 => V6RelationDiagnosticPhase::RoundOne,
            2 => V6RelationDiagnosticPhase::RoundTwo,
            _ => V6RelationDiagnosticPhase::RoundThree,
        });
    }
    if weights.dot(&folded_values[..4]) != running_claim {
        return Err(V6TranscriptError::RelationTerminal);
    }
    trace(V6RelationDiagnosticPhase::Terminal);
    let folded_query_sum = authenticated_queries
        .values
        .into_iter()
        .fold(QM31::ZERO, QM31::add);

    Ok(V6VerifiedTranscript {
        gamma,
        kappa,
        alpha,
        queries,
        selector,
        compact_counter,
        frontier_nodes,
        semantic_point,
        query_batch_challenge,
        folded_query_sum,
        transcript_state_after_queries,
    })
}

#[allow(clippy::too_many_arguments)]
#[inline(always)]
fn finish_v6_relation<QueryFold, Trace>(
    transcript: Transcript,
    wire: &V6OneFoldWire<'_>,
    fields: V6FixedFieldReader<'_>,
    selector: u8,
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
    semantic_point: [QM31; V6_SEMANTIC_ROUNDS],
    point_claims: &[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS],
    query_fold: QueryFold,
    trace: Trace,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
    Trace: FnMut(V6RelationDiagnosticPhase),
{
    finish_onefold_relation(
        transcript,
        wire.work_nonces,
        wire.c1_frontier,
        wire.c2_frontier,
        [V6_BATCH_WORK_BITS, V6_FOLD_WORK_BITS, V6_FINAL_WORK_BITS],
        selector,
        32,
        (label::V6_QUERY_BATCH_CHALLENGE, label::V6_QUERY_BATCH_CLAIM),
        false,
        |candidate_transcript| derive_first_compact_queries(candidate_transcript, selector),
        fields,
        inactive_row_groups,
        inactive_group_masks,
        check_pow,
        semantic_point,
        point_claims,
        query_fold,
        trace,
    )
}

#[allow(clippy::too_many_arguments)]
#[inline(always)]
fn finish_v7_compact_relation<QueryFold, Trace>(
    transcript: Transcript,
    wire: &V7CompactOneFoldWire<'_>,
    fields: V6FixedFieldReader<'_>,
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
    semantic_point: [QM31; V6_SEMANTIC_ROUNDS],
    point_claims: &[[QM31; V6_TOTAL_COLUMNS]; V6_POINT_CLAIM_ROWS],
    query_fold: QueryFold,
    trace: Trace,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
    Trace: FnMut(V6RelationDiagnosticPhase),
{
    finish_onefold_relation(
        transcript,
        wire.work_nonces,
        wire.c1_frontier,
        wire.c2_frontier,
        [
            V7_COMPACT_BATCH_WORK_BITS,
            V7_COMPACT_FOLD_WORK_BITS,
            V7_COMPACT_FINAL_WORK_BITS,
        ],
        0,
        V7_MERKLE_DIGEST_BYTES,
        (label::V7_QUERY_BATCH_CHALLENGE, label::V7_QUERY_BATCH_CLAIM),
        false,
        |candidate_transcript| {
            let schedule = derive_first_v7_compact_queries(candidate_transcript)
                .map_err(V6TranscriptError::Wire)?;
            Ok((
                schedule.queries,
                schedule.counter,
                schedule.frontier_nodes,
                schedule.transcript_state,
                schedule.accepted_transcript,
            ))
        },
        fields,
        inactive_row_groups,
        inactive_group_masks,
        check_pow,
        semantic_point,
        point_claims,
        query_fold,
        trace,
    )
}

/// Verify the complete fixed-field transcript and its four-round relation.
///
/// `terminal_check` is called before `gamma` exists. The production caller
/// must recompute the maintained atomic selected-hiding terminal from the
/// supplied view and return true only when it equals `terminal_claim`.
/// `query_fold` authenticates and folds the sixteen selected layer-zero
/// fibres. Their random linear combination is proved against `final256` by
/// the three relation rounds that remain after the sole PCS fold.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn verify_v6_transcript_and_relation<TerminalCheck, QueryFold>(
    hash: HashFn,
    wire: &V6OneFoldWire<'_>,
    context: &V6TranscriptContext,
    selector: u8,
    inactive_masks: [u16; 64],
    check_pow: bool,
    terminal_check: TerminalCheck,
    query_fold: QueryFold,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    TerminalCheck: FnOnce(&V6SemanticView<'_>) -> bool,
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
{
    let mut group_masks = Vec::<u16>::new();
    let mut row_groups = [0u8; 64];
    for (high, mask) in inactive_masks.into_iter().enumerate() {
        let group = group_masks
            .iter()
            .position(|&candidate| candidate == mask)
            .unwrap_or_else(|| {
                group_masks.push(mask);
                group_masks.len() - 1
            });
        row_groups[high] = group as u8;
    }
    verify_v6_transcript_and_relation_prepared(
        hash,
        wire,
        context,
        selector,
        &row_groups,
        &group_masks,
        check_pow,
        terminal_check,
        query_fold,
    )
}

/// Verify V6 using an already deduplicated inactive-mask schedule.
///
/// The fixed atomic-v3 verifier supplies generated public constants here;
/// this is algebraically identical to [`verify_v6_transcript_and_relation`]
/// while removing registry traversal and mask deduplication from the SBF hot
/// path.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn verify_v6_transcript_and_relation_prepared<TerminalCheck, QueryFold>(
    hash: HashFn,
    wire: &V6OneFoldWire<'_>,
    context: &V6TranscriptContext,
    selector: u8,
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
    terminal_check: TerminalCheck,
    query_fold: QueryFold,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    TerminalCheck: FnOnce(&V6SemanticView<'_>) -> bool,
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
{
    let mut fields = V6FixedFieldReader::new(wire.fixed_fields_packed)?;
    let (mut transcript, lambda, chi, batching) = begin_v6_transcript(hash, context, wire)?;
    let (eta, semantic_point, semantic_terminal) =
        verify_compact_semantic_sumcheck(&mut transcript, &mut fields)?;
    let point_claims = decode_and_absorb_point_claims(&mut transcript, &mut fields)?;
    let semantic_view = V6SemanticView {
        lambda,
        chi,
        batching,
        eta,
        point: semantic_point,
        terminal_claim: semantic_terminal,
        point_claims: &point_claims,
    };
    if !terminal_check(&semantic_view) {
        return Err(V6TranscriptError::TerminalRejected);
    }

    finish_v6_relation(
        transcript,
        wire,
        fields,
        selector,
        inactive_row_groups,
        inactive_group_masks,
        check_pow,
        semantic_point,
        &point_claims,
        query_fold,
        |_| {},
    )
}

/// Verify the compact V7 transcript while reusing the frozen V6 semantic and
/// relation algebra.  V7 has its own profile/deployment/root encodings, work
/// allocation, first-success query stream and query-batch labels; no V6 proof
/// can enter this wrapper and no V7 proof can enter the V6 wrapper.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn verify_v7_compact_transcript_and_relation_prepared<TerminalCheck, QueryFold>(
    hash: HashFn,
    wire: &V7CompactOneFoldWire<'_>,
    context: &V6TranscriptContext,
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
    terminal_check: TerminalCheck,
    query_fold: QueryFold,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    TerminalCheck: FnOnce(&V6SemanticView<'_>) -> bool,
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
{
    verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
        hash,
        wire,
        context,
        StateOnlyHidingContext::atomic_spend_v3(context.statement_digest, context.attempt_id),
        inactive_row_groups,
        inactive_group_masks,
        check_pow,
        terminal_check,
        query_fold,
    )
}

/// Pool/native-profile entrypoint for the compact V7 transcript.  The caller
/// supplies a typed hiding context whose statement digest and nonce are
/// checked by the hiding precommit.  The legacy wrapper above remains pinned
/// to the atomic-spend context and therefore keeps its exact transcript.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn verify_v7_compact_transcript_and_relation_prepared_with_hiding_context<
    TerminalCheck,
    QueryFold,
>(
    hash: HashFn,
    wire: &V7CompactOneFoldWire<'_>,
    context: &V6TranscriptContext,
    hiding_context: StateOnlyHidingContext,
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
    terminal_check: TerminalCheck,
    query_fold: QueryFold,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    TerminalCheck: FnOnce(&V6SemanticView<'_>) -> bool,
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
{
    let mut fields = V6FixedFieldReader::new(wire.fixed_fields_packed)?;
    let (mut transcript, lambda, chi, batching) =
        begin_v7_compact_transcript_with_hiding_context(hash, context, wire, hiding_context)?;
    let (eta, semantic_point, semantic_terminal) =
        verify_compact_semantic_sumcheck(&mut transcript, &mut fields)?;
    let point_claims = decode_and_absorb_point_claims(&mut transcript, &mut fields)?;
    let semantic_view = V6SemanticView {
        lambda,
        chi,
        batching,
        eta,
        point: semantic_point,
        terminal_claim: semantic_terminal,
        point_claims: &point_claims,
    };
    if !terminal_check(&semantic_view) {
        return Err(V6TranscriptError::TerminalRejected);
    }

    finish_v7_compact_relation(
        transcript,
        wire,
        fields,
        inactive_row_groups,
        inactive_group_masks,
        check_pow,
        semantic_point,
        &point_claims,
        query_fold,
        |_| {},
    )
}

/// Diagnostic twin of [`verify_v6_transcript_and_relation_prepared`]. It is
/// intended only for CU probes and reports checkpoints after the semantic
/// terminal without changing any cryptographic operation or transcript byte.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn verify_v6_transcript_and_relation_prepared_with_diagnostic_trace<
    TerminalCheck,
    QueryFold,
    Trace,
>(
    hash: HashFn,
    wire: &V6OneFoldWire<'_>,
    context: &V6TranscriptContext,
    selector: u8,
    inactive_row_groups: &[u8; 64],
    inactive_group_masks: &[u16],
    check_pow: bool,
    terminal_check: TerminalCheck,
    query_fold: QueryFold,
    trace: Trace,
) -> Result<V6VerifiedTranscript, V6TranscriptError>
where
    TerminalCheck: FnOnce(&V6SemanticView<'_>) -> bool,
    QueryFold: FnOnce(&V6QueryBatchView<'_>) -> Result<V6AuthenticatedQueryBatch, V6WireError>,
    Trace: FnMut(V6RelationDiagnosticPhase),
{
    let mut fields = V6FixedFieldReader::new(wire.fixed_fields_packed)?;
    let (mut transcript, lambda, chi, batching) = begin_v6_transcript(hash, context, wire)?;
    let (eta, semantic_point, semantic_terminal) =
        verify_compact_semantic_sumcheck(&mut transcript, &mut fields)?;
    let point_claims = decode_and_absorb_point_claims(&mut transcript, &mut fields)?;
    let semantic_view = V6SemanticView {
        lambda,
        chi,
        batching,
        eta,
        point: semantic_point,
        terminal_claim: semantic_terminal,
        point_claims: &point_claims,
    };
    if !terminal_check(&semantic_view) {
        return Err(V6TranscriptError::TerminalRejected);
    }

    finish_v6_relation(
        transcript,
        wire,
        fields,
        selector,
        inactive_row_groups,
        inactive_group_masks,
        check_pow,
        semantic_point,
        &point_claims,
        query_fold,
        trace,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v6_onefold::V6_BODY_WITHOUT_FRONTIERS;
    use crate::v7_onefold::V7_COMPACT_BODY_WITHOUT_FRONTIERS;
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn context() -> V6TranscriptContext {
        V6TranscriptContext {
            program_id: [0x11; 32],
            release_binding: [0x22; 32],
            statement_digest: [0x33; 32],
            attempt_id: [0x44; 32],
        }
    }

    fn zero_body(frontier: usize) -> Vec<u8> {
        vec![0u8; V6_BODY_WITHOUT_FRONTIERS + 2 * frontier * 32]
    }

    fn zero_query_batch() -> V6AuthenticatedQueryBatch {
        V6AuthenticatedQueryBatch {
            values: [QM31::ZERO; V6_QUERY_COUNT],
            line_x: [crate::field::M31::ZERO; V6_QUERY_COUNT],
        }
    }

    fn v7_zero_body(frontier: usize) -> Vec<u8> {
        vec![0u8; V7_COMPACT_BODY_WITHOUT_FRONTIERS + 2 * frontier * V7_MERKLE_DIGEST_BYTES]
    }

    fn expected_v7_frontier() -> Result<usize, V6TranscriptError> {
        let body = v7_zero_body(0);
        let wire = V7CompactOneFoldWire::parse(&body, 0).unwrap();
        match verify_v7_compact_transcript_and_relation_prepared(
            test_hash,
            &wire,
            &context(),
            &[0u8; 64],
            &[u16::MAX],
            false,
            |_| true,
            |_| Ok(zero_query_batch()),
        ) {
            Err(V6TranscriptError::FrontierCountMismatch { expected, .. }) => Ok(expected),
            Err(error) => Err(error),
            Ok(_) => panic!("zero-frontier V7 fixture unexpectedly matched"),
        }
    }

    fn expected_v7_frontier_with_hiding_context(
        hiding_context: StateOnlyHidingContext,
    ) -> Result<usize, V6TranscriptError> {
        let body = v7_zero_body(0);
        let wire = V7CompactOneFoldWire::parse(&body, 0).unwrap();
        match verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
            test_hash,
            &wire,
            &context(),
            hiding_context,
            &[0u8; 64],
            &[u16::MAX],
            false,
            |_| true,
            |_| Ok(zero_query_batch()),
        ) {
            Err(V6TranscriptError::FrontierCountMismatch { expected, .. }) => Ok(expected),
            Err(error) => Err(error),
            Ok(_) => panic!("zero-frontier typed V7 fixture unexpectedly matched"),
        }
    }

    fn expected_frontier_for_selector(selector: u8) -> Result<usize, V6TranscriptError> {
        let body = zero_body(0);
        let wire = V6OneFoldWire::parse(&body, 0, 0).unwrap();
        match verify_v6_transcript_and_relation(
            test_hash,
            &wire,
            &context(),
            selector,
            [u16::MAX; 64],
            false,
            |_| true,
            |_| Ok(zero_query_batch()),
        ) {
            Err(V6TranscriptError::FrontierCountMismatch { expected, .. }) => Ok(expected),
            Err(error) => Err(error),
            Ok(_) => panic!("zero-frontier fixture unexpectedly matched"),
        }
    }

    #[test]
    fn selected_profile_binding_is_exact() {
        assert_eq!(&V6_PROFILE_BINDING[..8], b"AV6OF001");
        assert_eq!(V6_PROFILE_BINDING[8], 26);
        assert_eq!(V6_PROFILE_BINDING[9], 3);
        assert_eq!(
            u16::from_le_bytes([V6_PROFILE_BINDING[12], V6_PROFILE_BINDING[13]]),
            209
        );
        assert_eq!(V6_PROFILE_BINDING[14], 3);
        assert_eq!(
            u16::from_le_bytes([V6_PROFILE_BINDING[24], V6_PROFILE_BINDING[25]]),
            641
        );
    }

    #[test]
    fn typed_v7_hiding_context_preserves_atomic_wrapper_and_separates_pool_variants() {
        let context = context();
        let verify_typed = |hiding_context| {
            let frontier = expected_v7_frontier_with_hiding_context(hiding_context).unwrap();
            let body = v7_zero_body(frontier);
            let wire = V7CompactOneFoldWire::parse(&body, frontier).unwrap();
            verify_v7_compact_transcript_and_relation_prepared_with_hiding_context(
                test_hash,
                &wire,
                &context,
                hiding_context,
                &[0u8; 64],
                &[u16::MAX],
                false,
                |_| true,
                |_| Ok(zero_query_batch()),
            )
            .unwrap()
        };
        let atomic =
            StateOnlyHidingContext::atomic_spend_v3(context.statement_digest, context.attempt_id);
        let atomic_frontier = expected_v7_frontier().unwrap();
        let atomic_body = v7_zero_body(atomic_frontier);
        let atomic_wire = V7CompactOneFoldWire::parse(&atomic_body, atomic_frontier).unwrap();
        let wrapped = verify_v7_compact_transcript_and_relation_prepared(
            test_hash,
            &atomic_wire,
            &context,
            &[0u8; 64],
            &[u16::MAX],
            false,
            |_| true,
            |_| Ok(zero_query_batch()),
        )
        .unwrap();
        let typed_atomic = verify_typed(atomic);
        assert_eq!(wrapped.gamma, typed_atomic.gamma);
        assert_eq!(wrapped.kappa, typed_atomic.kappa);
        assert_eq!(wrapped.alpha, typed_atomic.alpha);
        assert_eq!(wrapped.queries, typed_atomic.queries);
        assert_eq!(wrapped.selector, typed_atomic.selector);
        assert_eq!(wrapped.compact_counter, typed_atomic.compact_counter);
        assert_eq!(wrapped.frontier_nodes, typed_atomic.frontier_nodes);
        assert_eq!(wrapped.semantic_point, typed_atomic.semantic_point);
        assert_eq!(
            wrapped.query_batch_challenge,
            typed_atomic.query_batch_challenge,
        );
        assert_eq!(wrapped.folded_query_sum, typed_atomic.folded_query_sum);
        assert_eq!(
            wrapped.transcript_state_after_queries,
            typed_atomic.transcript_state_after_queries,
        );

        let transfer = verify_typed(StateOnlyHidingContext::pool_v1_private_transfer(
            context.statement_digest,
            context.attempt_id,
        ));
        let withdrawal = verify_typed(StateOnlyHidingContext::pool_v1_withdrawal(
            context.statement_digest,
            context.attempt_id,
        ));
        assert_ne!(
            transfer.transcript_state_after_queries,
            withdrawal.transcript_state_after_queries,
        );
    }

    #[test]
    fn zero_relation_runs_end_to_end_and_first_compact_is_deterministic() {
        let mut selected = None;
        for selector in 0..V6_QUERY_SELECTOR_COUNT {
            if let Ok(frontier) = expected_frontier_for_selector(selector) {
                selected = Some((selector, frontier));
                break;
            }
        }
        let (selector, frontier) = selected.expect("one selector has a compact schedule");
        let body = zero_body(frontier);
        let wire = V6OneFoldWire::parse(&body, frontier, frontier).unwrap();
        let first = verify_v6_transcript_and_relation(
            test_hash,
            &wire,
            &context(),
            selector,
            [u16::MAX; 64],
            false,
            |_| true,
            |_| Ok(zero_query_batch()),
        )
        .unwrap();
        let second = verify_v6_transcript_and_relation(
            test_hash,
            &wire,
            &context(),
            selector,
            [u16::MAX; 64],
            false,
            |_| true,
            |_| Ok(zero_query_batch()),
        )
        .unwrap();
        assert_eq!(first.queries, second.queries);
        assert_eq!(first.compact_counter, second.compact_counter);
        assert_eq!(first.frontier_nodes, frontier);
        assert_eq!(first.alpha, second.alpha);
        assert_eq!(
            first.transcript_state_after_queries,
            second.transcript_state_after_queries
        );
    }

    #[test]
    fn v7_zero_relation_uses_its_first_cap203_schedule_and_profile() {
        let frontier = expected_v7_frontier().unwrap();
        assert!(frontier <= 203);
        let body = v7_zero_body(frontier);
        let wire = V7CompactOneFoldWire::parse(&body, frontier).unwrap();
        let verify = || {
            verify_v7_compact_transcript_and_relation_prepared(
                test_hash,
                &wire,
                &context(),
                &[0u8; 64],
                &[u16::MAX],
                false,
                |_| true,
                |_| Ok(zero_query_batch()),
            )
            .unwrap()
        };
        let first = verify();
        let second = verify();
        assert_eq!(first.selector, 0);
        assert_eq!(first.queries, second.queries);
        assert_eq!(first.compact_counter, second.compact_counter);
        assert_eq!(first.frontier_nodes, frontier);
        assert_eq!(first.alpha, second.alpha);
        assert_eq!(
            first.transcript_state_after_queries,
            second.transcript_state_after_queries
        );
    }

    #[test]
    fn terminal_callback_is_mandatory_and_precedes_batch_challenges() {
        let selector = (0..V6_QUERY_SELECTOR_COUNT)
            .find(|selector| expected_frontier_for_selector(*selector).is_ok())
            .unwrap();
        let frontier = expected_frontier_for_selector(selector).unwrap();
        let body = zero_body(frontier);
        let wire = V6OneFoldWire::parse(&body, frontier, frontier).unwrap();
        assert!(matches!(
            verify_v6_transcript_and_relation(
                test_hash,
                &wire,
                &context(),
                selector,
                [u16::MAX; 64],
                false,
                |_| false,
                |_| Ok(zero_query_batch()),
            ),
            Err(V6TranscriptError::TerminalRejected)
        ));
    }

    #[test]
    fn statement_point_map_matches_boolean_successor_and_xor12() {
        for row in [0usize, 1, 11, 12, 511, 1023] {
            let point: [QM31; 10] = core::array::from_fn(|coordinate| {
                let bit = (row >> (9 - coordinate)) & 1;
                if bit == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            });
            let points = v6_statement_points(&point);
            let decode = |value: &[QM31; 10]| {
                value.iter().fold(0usize, |acc, bit| {
                    (acc << 1) | usize::from(*bit == QM31::ONE)
                })
            };
            assert_eq!(decode(&points[0]), row);
            assert_eq!(decode(&points[1]), (row + 1) & 1023);
            assert_eq!(decode(&points[2]), row ^ 12);
        }
    }
}
