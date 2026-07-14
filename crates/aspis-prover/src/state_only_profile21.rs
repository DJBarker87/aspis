//! Literal atomic state-only profile-21 proof builder.
//!
//! The main gamma word remains the frozen 28-column word. X and F are two
//! source-only C2 lanes in the same pre-gamma private Merkle root. Immediately
//! after the first fold, the builder discloses logical U=F+delta*X, injects
//! its full natural image into the relation and codeword, and commits W1.

use aspis_core::circle_fri::normalized_circle_to_line_arity4_at_fiber_for_domain_log;
use aspis_core::circle_line_merkle::CIRCLE_LINE_TAGS;
use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
    RATE16_HARDENED_FOLD_POW_BITS,
};
use aspis_core::field::QM31;
use aspis_core::proof::{HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR};
use aspis_core::state_only_hiding::{begin_state_only_hiding_precommit, StateOnlyHidingContext};
use aspis_core::state_only_masked_switch::{
    evaluate_masked_switch_logical, masked_switch_query_point,
};
use aspis_core::state_only_masked_switch_basis::{
    masked_switch_logical_to_natural, MASKED_SWITCH_UNIVERSAL_DIMENSION,
    MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION,
};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_prefix_schedule_host_v3,
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix, StateOnlyProfile21Prefix, StateOnlyProfile21TranscriptScheduleResult,
    STATE_ONLY_LOG_ROWS, STATE_ONLY_PROFILE21_SHAPE,
};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_profile21_openings::StateOnlyProfile21OpeningRoots;
use aspis_core::state_only_relation::prepare_state_only_relation;
use aspis_core::state_only_sumcheck::begin_state_only_zerocheck;
use aspis_core::sumcheck::{SumcheckPolynomial, SUMCHECK_COEFFICIENTS};
use aspis_core::transcript::{label, Transcript};
use aspis_core::HashFn;
use aspis_statement::state_only_poseidon::{successor_point, xor12_point};
use aspis_statement::{
    atomic_payment_statement_digest_v3,
    atomic_state_only_registry::build_atomic_state_only_copy_helper_v3,
    atomic_state_only_terminal::{
        atomic_state_only_copy_inactive_row_masks_v3,
        atomic_state_only_selected_unmasked_terminal_value_compiled_v3,
    },
    atomic_state_only_trace::{build_atomic_state_only_trace_v3, AtomicStateOnlyTraceV3Error},
    state_only_copy_helper_sum, AtomicPaymentStatementV3, AtomicStatementError, SpendWitness,
    StateOnlyConstraintError,
};

use crate::circle_candidate::{
    combined_layer_leaves, fold_candidate_codeword_round_for_domain_log, CircleCandidateError,
    CircleEncoder,
};
use crate::circle_candidate_prefix::CandidatePrefixBuildError;
use crate::state_only_candidate::{
    encode_state_only_c1_columns, gamma_combine_state_only_codewords,
    gamma_combine_state_only_messages, state_only_c1_layer0_leaves,
};
use crate::state_only_candidate_prefix::{
    serialize_state_only_prefix, state_only_header, statement_evaluations, StateOnlyPowMode,
    StateOnlyPrefixBuildError, StateOnlyPrefixMaterial,
};
use crate::state_only_circle_relation::{
    StateOnlyCircleRelationTrace, StateOnlyIncrementalRelation,
};
use crate::state_only_entropy::{ReservedStateOnlyAttemptSecrets, StateOnlyAttemptSecrets};
use crate::state_only_hiding::{
    apply_atomic_state_only_h1_padding_mask_v3, apply_atomic_state_only_mask_material_v3,
    prove_masked_state_only_zerocheck, StateOnlyMaskBuildError, StateOnlyMaskNonceStore,
};
use crate::state_only_private_openings::{
    build_state_only_private_merkle_tree, StateOnlyPrivateOpeningBuildError,
};
use crate::state_only_profile21_openings::{
    serialize_state_only_profile21_openings, BuiltStateOnlyProfile21Openings,
    StateOnlyProfile21OpeningBuildError, StateOnlyProfile21OpeningInputs,
    StateOnlyProfile21TreeInput,
};

pub const PROFILE21_C1_VALUE_WIDTH: usize = 416;
pub const PROFILE21_C2_VALUE_WIDTH: usize = 256;

#[derive(Debug)]
pub enum StateOnlyProfile21BuildError {
    AtomicTrace(AtomicStateOnlyTraceV3Error),
    AtomicStatement(AtomicStatementError),
    Front(StateOnlyPrefixBuildError),
    Candidate(CandidatePrefixBuildError),
    Circle(CircleCandidateError),
    Mask(StateOnlyMaskBuildError),
    Private(StateOnlyPrivateOpeningBuildError),
    Openings(StateOnlyProfile21OpeningBuildError),
    Consistency(&'static str),
}

impl From<AtomicStateOnlyTraceV3Error> for StateOnlyProfile21BuildError {
    fn from(value: AtomicStateOnlyTraceV3Error) -> Self {
        Self::AtomicTrace(value)
    }
}
impl From<AtomicStatementError> for StateOnlyProfile21BuildError {
    fn from(value: AtomicStatementError) -> Self {
        Self::AtomicStatement(value)
    }
}
impl From<StateOnlyPrefixBuildError> for StateOnlyProfile21BuildError {
    fn from(value: StateOnlyPrefixBuildError) -> Self {
        Self::Front(value)
    }
}
impl From<CandidatePrefixBuildError> for StateOnlyProfile21BuildError {
    fn from(value: CandidatePrefixBuildError) -> Self {
        Self::Candidate(value)
    }
}
impl From<CircleCandidateError> for StateOnlyProfile21BuildError {
    fn from(value: CircleCandidateError) -> Self {
        Self::Circle(value)
    }
}
impl From<StateOnlyMaskBuildError> for StateOnlyProfile21BuildError {
    fn from(value: StateOnlyMaskBuildError) -> Self {
        Self::Mask(value)
    }
}
impl From<StateOnlyPrivateOpeningBuildError> for StateOnlyProfile21BuildError {
    fn from(value: StateOnlyPrivateOpeningBuildError) -> Self {
        Self::Private(value)
    }
}
impl From<StateOnlyProfile21OpeningBuildError> for StateOnlyProfile21BuildError {
    fn from(value: StateOnlyProfile21OpeningBuildError) -> Self {
        Self::Openings(value)
    }
}

pub struct BuiltAtomicStateOnlyProfile21Proof {
    pub bytes: Vec<u8>,
    pub schedule: StateOnlyProfile21TranscriptScheduleResult,
    pub relation: StateOnlyCircleRelationTrace,
    pub roots: StateOnlyProfile21OpeningRoots,
    pub openings: BuiltStateOnlyProfile21Openings,
    pub logical_x: [QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    pub logical_f: [QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    pub logical_u: [QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    pub tau: QM31,
    pub source_nonce: u64,
    pub pow_valid: bool,
}

fn pow_nonce(transcript: &Transcript, bits: u8, mode: StateOnlyPowMode) -> u64 {
    match mode {
        StateOnlyPowMode::UnminedZero => 0,
        StateOnlyPowMode::Mine => crate::find_grinding_nonce(transcript, bits),
    }
}

fn absorb_round_root(transcript: &mut Transcript, layer: usize, root: &[u8; 32]) {
    let mut record = [0u8; 33];
    record[0] = layer as u8;
    record[1..].copy_from_slice(root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn absorb_ood(
    transcript: &mut Transcript,
    ood_label: u8,
    layer: usize,
    sample: usize,
    value: QM31,
) {
    let mut record = [0u8; 18];
    record[0] = layer as u8;
    record[1] = sample as u8;
    value.write_le_bytes(&mut record[2..]);
    transcript.absorb(ood_label, &record);
}

fn absorb_relation_sumcheck(
    transcript: &mut Transcript,
    layer: usize,
    polynomial: &SumcheckPolynomial,
) {
    let mut record = [0u8; 1 + SUMCHECK_COEFFICIENTS * 16];
    record[0] = layer as u8;
    for (index, value) in polynomial.iter().enumerate() {
        value.write_le_bytes(&mut record[1 + index * 16..][..16]);
    }
    transcript.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &record);
}

fn absorb_fold_pow(transcript: &mut Transcript, layer: usize, nonce: u64) {
    let mut record = [0u8; 1 + CANDIDATE_NONCE_LEN];
    record[0] = layer as u8;
    record[1..].copy_from_slice(&nonce.to_le_bytes());
    transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
}

fn absorb_final(transcript: &mut Transcript, coefficients: &[QM31; CANDIDATE_FINAL_POLY_LEN]) {
    let mut bytes = [0u8; CANDIDATE_FINAL_POLY_LEN * 16];
    for (index, value) in coefficients.iter().enumerate() {
        value.write_le_bytes(&mut bytes[index * 16..][..16]);
    }
    transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, &bytes);
}

fn logical_source_message(logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION]) -> Vec<QM31> {
    let natural = masked_switch_logical_to_natural(logical);
    let mut message = vec![QM31::ZERO; 1 << STATE_ONLY_LOG_ROWS];
    for (index, value) in natural.into_iter().enumerate() {
        message[4 * index] = value;
    }
    message
}

fn flatten<const N: usize>(leaves: &[[u8; N]]) -> Vec<u8> {
    let mut values = Vec::with_capacity(leaves.len() * N);
    for leaf in leaves {
        values.extend_from_slice(leaf);
    }
    values
}

fn widened_c2_values(
    encoded: &[Vec<QM31>],
    codeword_len: usize,
) -> Result<Vec<u8>, StateOnlyProfile21BuildError> {
    if encoded.len() != 4 || encoded.iter().any(|column| column.len() != codeword_len) {
        return Err(StateOnlyProfile21BuildError::Consistency(
            "profile21 C2 source shape",
        ));
    }
    let mut values = vec![0u8; (codeword_len / 4) * PROFILE21_C2_VALUE_WIDTH];
    for fiber in 0..codeword_len / 4 {
        let leaf = &mut values[fiber * PROFILE21_C2_VALUE_WIDTH..][..PROFILE21_C2_VALUE_WIDTH];
        for (lane, column) in encoded.iter().enumerate() {
            for slot in 0..4 {
                let offset = (4 * lane + slot) * 16;
                column[4 * fiber + slot].write_le_bytes(&mut leaf[offset..offset + 16]);
            }
        }
    }
    Ok(values)
}

fn derive_salts(
    reserved: &ReservedStateOnlyAttemptSecrets,
    context: StateOnlyHidingContext,
    hash: HashFn,
    tag: u8,
    count: usize,
) -> Result<Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>, StateOnlyProfile21BuildError> {
    (0..count)
        .map(|index| {
            reserved
                .derive_profile21_leaf_salt(hash, context, tag, index as u32)
                .map_err(StateOnlyProfile21BuildError::from)
        })
        .collect()
}

fn decode_source_fiber(c2_values: &[u8], query: u32, lane: usize) -> Option<[QM31; 4]> {
    let leaf = c2_values.get(
        query as usize * PROFILE21_C2_VALUE_WIDTH..(query as usize + 1) * PROFILE21_C2_VALUE_WIDTH,
    )?;
    let mut result = [QM31::ZERO; 4];
    for (slot, value) in result.iter_mut().enumerate() {
        let start = (4 * lane + slot) * 16;
        *value = QM31::from_le_bytes(&leaf[start..start + 16])?;
    }
    Some(result)
}

/// Build a literal unmined or mined profile-21 proof. Production callers
/// should create `attempt` with OS entropy; every private salt is unavailable
/// until the nonce store has durably accepted the attempt.
#[allow(clippy::too_many_lines)]
pub fn build_hiding_atomic_state_only_profile21_proof_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltAtomicStateOnlyProfile21Proof, StateOnlyProfile21BuildError> {
    build_hiding_atomic_state_only_profile21_proof_inner_v3(
        statement,
        witness,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        QM31::ZERO,
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn build_hiding_atomic_state_only_profile21_proof_inner_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
    seam_error: QM31,
) -> Result<BuiltAtomicStateOnlyProfile21Proof, StateOnlyProfile21BuildError> {
    let mut atomic = build_atomic_state_only_trace_v3(statement, witness)?;
    let mut trace = core::mem::take(&mut atomic.trace);
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)?;
    let mask_nonce = attempt.mask_nonce();
    let context = StateOnlyHidingContext::atomic_v3(statement_digest, mask_nonce);
    let mut header_bytes = [0u8; HEADER_LEN];
    state_only_header(STATE_ONLY_PROFILE21_SHAPE).write(&mut header_bytes);
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, &statement_digest);
    let precommit_binding = begin_state_only_hiding_precommit(&mut transcript, context)
        .map_err(StateOnlyPrefixBuildError::Hiding)?;
    let (reserved, mask_material) = attempt.reserve_and_build_atomic_mask_material_v3(
        hash,
        precommit_binding,
        context,
        nonce_store,
    )?;
    let applied = apply_atomic_state_only_mask_material_v3(&mut trace, mask_material)?;
    let (logical_x, logical_f) = reserved.derive_profile21_source_masks(hash, context)?;

    let domain_log = STATE_ONLY_LOG_ROWS + STATE_ONLY_PROFILE21_SHAPE.log_blowup;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let selected_c1 = trace
        .c1
        .iter()
        .cloned()
        .chain(applied.mask_only_c1.iter().cloned())
        .collect::<Vec<_>>();
    let encoded_c1 = encode_state_only_c1_columns(&encoder, &selected_c1)?;
    let c1_leaves = state_only_c1_layer0_leaves(&encoded_c1, encoder.codeword_len())?;
    let c1_values = flatten(&c1_leaves);
    let c1_salts = derive_salts(
        &reserved,
        context,
        hash,
        CIRCLE_C1_LAYER0_TAG,
        c1_leaves.len(),
    )?;
    let c1_tree = build_state_only_private_merkle_tree(
        hash,
        17,
        CIRCLE_C1_LAYER0_TAG,
        PROFILE21_C1_VALUE_WIDTH,
        &c1_values,
        &c1_salts,
    )?;
    let c1_root = c1_tree.root();
    absorb_round_root(&mut transcript, 0, &c1_root);
    let lambda = transcript
        .challenge_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    let mut h1 = build_atomic_state_only_copy_helper_v3(&trace, lambda, chi)
        .map_err(|_| StateOnlyPrefixBuildError::Shape)?;
    apply_atomic_state_only_h1_padding_mask_v3(&mut h1, &applied.h1_padding)?;
    if state_only_copy_helper_sum(&h1) != Some(QM31::ZERO) {
        return Err(StateOnlyProfile21BuildError::Consistency(
            "profile21 h1 sum",
        ));
    }

    let c2_messages = [
        h1.clone(),
        applied.g.clone(),
        logical_source_message(&logical_x),
        logical_source_message(&logical_f),
    ];
    let encoded_c2 = c2_messages
        .iter()
        .map(|message| encoder.encode_c2_message(message))
        .collect::<Result<Vec<_>, _>>()?;
    let c2_values = widened_c2_values(&encoded_c2, encoder.codeword_len())?;
    let c2_leaf_count = encoder.codeword_len() / 4;
    let c2_salts = derive_salts(
        &reserved,
        context,
        hash,
        CIRCLE_C2_LAYER0_TAG,
        c2_leaf_count,
    )?;
    let c2_tree = build_state_only_private_merkle_tree(
        hash,
        17,
        CIRCLE_C2_LAYER0_TAG,
        PROFILE21_C2_VALUE_WIDTH,
        &c2_values,
        &c2_salts,
    )?;
    let c2_root = c2_tree.root();
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2_root);
    let batching =
        begin_state_only_zerocheck(&mut transcript).map_err(StateOnlyPrefixBuildError::from)?;
    let masked = prove_masked_state_only_zerocheck(
        &mut transcript,
        precommit_binding,
        &trace,
        &applied.mask_only_c1,
        &applied.g,
        |point| {
            let claims =
                statement_evaluations(&trace, &applied.mask_only_c1, &h1, &applied.g, point)
                    .map_err(|_| StateOnlyConstraintError::Shape)?;
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
            .map_err(|_| StateOnlyConstraintError::Shape)
        },
    )
    .map_err(StateOnlyPrefixBuildError::from)?;
    let evaluations = statement_evaluations(
        &trace,
        &applied.mask_only_c1,
        &h1,
        &applied.g,
        &masked.sumcheck.challenges,
    )?;
    let mut material = StateOnlyPrefixMaterial::front(
        STATE_ONLY_PROFILE21_SHAPE,
        mask_nonce,
        c1_root,
        c2_root,
        masked.initial_mask_claim,
        &masked.sumcheck,
        evaluations,
    );
    transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &{
        let points = [
            masked.sumcheck.challenges,
            successor_point(&masked.sumcheck.challenges),
            xor12_point(&masked.sumcheck.challenges),
        ];
        let mut bytes = [0u8; 480];
        for (point, coordinates) in points.iter().enumerate() {
            for (coordinate, value) in coordinates.iter().enumerate() {
                value.write_le_bytes(&mut bytes[(point * 10 + coordinate) * 16..][..16]);
            }
        }
        bytes
    });
    let mut base_prefix = serialize_state_only_prefix(&material);
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        &base_prefix[aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS
            .statement_evaluations_start..]
            [..aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_EVALUATIONS_LEN],
    );
    material.batch_nonce = pow_nonce(
        &transcript,
        STATE_ONLY_PROFILE21_SHAPE.batch_grinding_bits,
        pow_mode,
    );
    let mut pow_valid = transcript.grinding_ok(
        material.batch_nonce,
        STATE_ONLY_PROFILE21_SHAPE.batch_grinding_bits,
    );
    transcript.absorb(
        label::M31_PAYMENT_BATCH_POW_NONCE,
        &material.batch_nonce.to_le_bytes(),
    );
    let gamma = transcript
        .challenge_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    let point_scale = transcript
        .challenge_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    base_prefix = serialize_state_only_prefix(&material);
    let parsed_front = StateOnlyCandidatePrefix::parse_exact(&base_prefix)
        .map_err(StateOnlyPrefixBuildError::from)?;
    let front_schedule =
        run_atomic_state_only_prefix_schedule_host_v3(hash, &parsed_front, &statement_digest)
            .map_err(StateOnlyPrefixBuildError::from)?;
    if front_schedule.gamma != gamma
        || front_schedule.point_scale != point_scale
        || front_schedule.lambda != lambda
        || front_schedule.chi != chi
        || front_schedule.z != masked.sumcheck.challenges
    {
        return Err(StateOnlyProfile21BuildError::Consistency(
            "profile21 front replay",
        ));
    }

    let main_c2 = [encoded_c2[0].clone(), encoded_c2[1].clone()];
    let main_c2_messages = [h1.clone(), applied.g.clone()];
    let original_message =
        gamma_combine_state_only_messages(&selected_c1, &main_c2_messages, gamma)?;
    let original_codeword =
        gamma_combine_state_only_codewords(&encoded_c1, &main_c2, gamma, encoder.codeword_len())?;
    let z = front_schedule.z;
    let points = [z, successor_point(&z), xor12_point(&z)];
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks(
        original_message.clone(),
        &points,
        [QM31::ONE, point_scale, point_scale.square()],
        atomic_state_only_copy_inactive_row_masks_v3(),
    )?;
    let prepared = prepare_state_only_relation(
        gamma,
        &base_prefix[aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS
            .statement_evaluations_start..]
            [..aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_EVALUATIONS_LEN],
    )
    .ok_or(StateOnlyProfile21BuildError::Consistency(
        "profile21 fused relation",
    ))?;

    let mut combined_codeword = original_codeword;
    let mut fold_nonces = [0u64; CANDIDATE_ROUND_COUNT];
    let mut alphas = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    let mut later_values = Vec::with_capacity(3);
    let mut later_salts = Vec::with_capacity(3);
    let mut later_trees = Vec::with_capacity(3);
    let mut logical_u = [QM31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    let mut tau = QM31::ZERO;
    let mut source_nonce = 0u64;
    let mut delta = QM31::ZERO;

    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = transcript
                    .challenge_secure_circle_point()
                    .map_err(CandidatePrefixBuildError::from)?;
                let value = relation.evaluate_circle_ood(point)?;
                absorb_ood(
                    &mut transcript,
                    label::M31_CIRCLE_OOD_VALUE,
                    round,
                    sample,
                    value,
                );
                let mix = transcript
                    .challenge_qm31()
                    .map_err(CandidatePrefixBuildError::from)?;
                relation.add_circle_ood(point, value, mix)?;
            } else {
                let point = transcript
                    .challenge_ood_qm31()
                    .map_err(CandidatePrefixBuildError::from)?;
                let value = relation.evaluate_line_ood(point)?;
                absorb_ood(
                    &mut transcript,
                    label::M31_LINE_OOD_VALUE,
                    round,
                    sample,
                    value,
                );
                let mix = transcript
                    .challenge_qm31()
                    .map_err(CandidatePrefixBuildError::from)?;
                relation.add_line_ood(point, value, mix)?;
            }
        }
        let polynomial = relation.polynomial()?;
        absorb_relation_sumcheck(&mut transcript, round, &polynomial);
        fold_nonces[round] = pow_nonce(&transcript, RATE16_HARDENED_FOLD_POW_BITS[round], pow_mode);
        pow_valid &=
            transcript.grinding_ok(fold_nonces[round], RATE16_HARDENED_FOLD_POW_BITS[round]);
        absorb_fold_pow(&mut transcript, round, fold_nonces[round]);
        alphas[round] = transcript
            .challenge_qm31()
            .map_err(CandidatePrefixBuildError::from)?;
        relation.fold(alphas[round])?;
        combined_codeword = fold_candidate_codeword_round_for_domain_log(
            &combined_codeword,
            alphas[round],
            round,
            domain_log,
        )?;

        if round == 0 {
            source_nonce = pow_nonce(
                &transcript,
                aspis_core::state_only_masked_switch::MASKED_SWITCH_SOURCE_WORK_BITS,
                pow_mode,
            );
            pow_valid &= transcript.grinding_ok(
                source_nonce,
                aspis_core::state_only_masked_switch::MASKED_SWITCH_SOURCE_WORK_BITS,
            );
            transcript.absorb(
                label::M31_STATE_ONLY_SWITCH_SOURCE_POW_NONCE,
                &source_nonce.to_le_bytes(),
            );
            for _ in 0..3 {
                let candidate = transcript
                    .challenge_qm31()
                    .map_err(CandidatePrefixBuildError::from)?;
                if candidate != QM31::ZERO {
                    delta = candidate;
                    break;
                }
            }
            if delta == QM31::ZERO {
                return Err(StateOnlyProfile21BuildError::Consistency(
                    "profile21 delta retry",
                ));
            }
            logical_u =
                core::array::from_fn(|index| logical_f[index].add(delta.mul(logical_x[index])));
            let mut u_bytes = [0u8; MASKED_SWITCH_UNIVERSAL_DIMENSION * 16];
            for (index, value) in logical_u.iter().enumerate() {
                value.write_le_bytes(&mut u_bytes[index * 16..][..16]);
            }
            transcript.absorb(label::M31_STATE_ONLY_SWITCH_U, &u_bytes);
            // `seam_error` is zero in every public builder call. The private
            // nonzero path constructs a fully committed W1/relation seam
            // inconsistent with disclosed U, solely for the end-to-end q16
            // rejection tooth below.
            let mut injected_logical_u = logical_u;
            injected_logical_u[MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION] =
                injected_logical_u[MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION].add(seam_error);
            tau = relation.inject_profile21_first_later_u(&injected_logical_u)?;
            let mut tau_bytes = [0u8; 16];
            tau.write_le_bytes(&mut tau_bytes);
            transcript.absorb(label::M31_STATE_ONLY_SWITCH_TAU, &tau_bytes);
            let encoded_u =
                encoder.encode_c2_message(&logical_source_message(&injected_logical_u))?;
            let u_line =
                fold_candidate_codeword_round_for_domain_log(&encoded_u, alphas[0], 0, domain_log)?;
            for (value, translation) in combined_codeword.iter_mut().zip(u_line) {
                *value = value.add(translation);
            }
        }

        if round + 1 < CANDIDATE_ROUND_COUNT {
            let leaves = combined_layer_leaves(&combined_codeword);
            let values = flatten(&leaves);
            let tag = CIRCLE_LINE_TAGS[round];
            let salts = derive_salts(&reserved, context, hash, tag, leaves.len())?;
            let depth = 15 - 2 * round as u32;
            let tree = build_state_only_private_merkle_tree(hash, depth, tag, 64, &values, &salts)?;
            material.later_roots[round] = tree.root();
            if round == 0 {
                transcript.absorb(
                    label::M31_STATE_ONLY_SWITCH_TRANSLATED_ROOT,
                    &material.later_roots[round],
                );
            } else {
                absorb_round_root(&mut transcript, round + 1, &material.later_roots[round]);
            }
            later_values.push(values);
            later_salts.push(salts);
            later_trees.push(tree);
        }
    }

    let relation = relation.finish()?;
    if relation.point_claims != prepared.claims {
        return Err(StateOnlyProfile21BuildError::Consistency(
            "profile21 point claims",
        ));
    }
    absorb_final(&mut transcript, &relation.final_coefficients);
    material.nonce = pow_nonce(
        &transcript,
        aspis_core::state_only_prefix::STATE_ONLY_PROFILE21_GRINDING_BITS,
        pow_mode,
    );
    pow_valid &= transcript.grinding_ok(
        material.nonce,
        aspis_core::state_only_prefix::STATE_ONLY_PROFILE21_GRINDING_BITS,
    );
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_FINAL_POW_NONCE,
        &material.nonce.to_le_bytes(),
    );
    let queries = transcript
        .challenge_queries_without_replacement(
            STATE_ONLY_PROFILE21_SHAPE.query_count as usize,
            (encoder.codeword_len() / 4) as u32,
            aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT,
        )
        .map_err(|_| StateOnlyProfile21BuildError::Consistency("profile21 q sampler"))?;

    // Differential tooth for the most order-sensitive seam: authenticate the
    // exact widened-C2 layout, fold each raw four-slot source fiber with the
    // production circle normalization, and compare it to both the full
    // encoded line word and an independent logical-polynomial evaluation.
    let x_line =
        fold_candidate_codeword_round_for_domain_log(&encoded_c2[2], alphas[0], 0, domain_log)?;
    let f_line =
        fold_candidate_codeword_round_for_domain_log(&encoded_c2[3], alphas[0], 0, domain_log)?;
    for &query in &queries {
        let raw_x = decode_source_fiber(&c2_values, query, 2).ok_or(
            StateOnlyProfile21BuildError::Consistency("profile21 raw X decode"),
        )?;
        let raw_f = decode_source_fiber(&c2_values, query, 3).ok_or(
            StateOnlyProfile21BuildError::Consistency("profile21 raw F decode"),
        )?;
        let folded_x = normalized_circle_to_line_arity4_at_fiber_for_domain_log(
            raw_x,
            alphas[0],
            domain_log,
            query as usize,
        )
        .map_err(|_| StateOnlyProfile21BuildError::Consistency("profile21 raw X fold"))?;
        let folded_f = normalized_circle_to_line_arity4_at_fiber_for_domain_log(
            raw_f,
            alphas[0],
            domain_log,
            query as usize,
        )
        .map_err(|_| StateOnlyProfile21BuildError::Consistency("profile21 raw F fold"))?;
        let point = masked_switch_query_point(query)
            .map_err(|_| StateOnlyProfile21BuildError::Consistency("profile21 q point"))?;
        let direct_x = evaluate_masked_switch_logical(&logical_x, point);
        let direct_f = evaluate_masked_switch_logical(&logical_f, point);
        let direct_u = evaluate_masked_switch_logical(&logical_u, point);
        if folded_x != x_line[query as usize]
            || folded_f != f_line[query as usize]
            || folded_x != direct_x
            || folded_f != direct_f
            || folded_f.add(delta.mul(folded_x)) != direct_u
        {
            return Err(StateOnlyProfile21BuildError::Consistency(
                "profile21 raw-source differential",
            ));
        }
    }

    material.ood_values = relation.ood_values;
    material.relation_sumchecks = relation.sumchecks;
    material.final_coefficients = relation.final_coefficients;
    material.fold_nonces = fold_nonces;
    base_prefix = serialize_state_only_prefix(&material);
    let mut profile_prefix =
        Vec::with_capacity(aspis_core::state_only_prefix::STATE_ONLY_PROFILE21_PREFIX_LEN);
    profile_prefix.extend_from_slice(&base_prefix);
    profile_prefix.extend_from_slice(&source_nonce.to_le_bytes());
    let mut field = [0u8; 16];
    for value in logical_u {
        value.write_le_bytes(&mut field);
        profile_prefix.extend_from_slice(&field);
    }
    tau.write_le_bytes(&mut field);
    profile_prefix.extend_from_slice(&field);
    let parsed = StateOnlyProfile21Prefix::parse_exact(&profile_prefix)
        .map_err(StateOnlyPrefixBuildError::from)?;
    let schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            hash,
            &parsed,
            &statement_digest,
        )
        .map_err(StateOnlyPrefixBuildError::from)?;
    if schedule.delta != delta
        || schedule.base.alpha != alphas
        || schedule.base.queries[..schedule.base.query_count] != queries
    {
        return Err(StateOnlyProfile21BuildError::Consistency(
            "profile21 full replay",
        ));
    }

    let opening_inputs = StateOnlyProfile21OpeningInputs {
        c1: StateOnlyProfile21TreeInput {
            tree: &c1_tree,
            values: &c1_values,
            salts: &c1_salts,
        },
        c2: StateOnlyProfile21TreeInput {
            tree: &c2_tree,
            values: &c2_values,
            salts: &c2_salts,
        },
        later: [
            StateOnlyProfile21TreeInput {
                tree: &later_trees[0],
                values: &later_values[0],
                salts: &later_salts[0],
            },
            StateOnlyProfile21TreeInput {
                tree: &later_trees[1],
                values: &later_values[1],
                salts: &later_salts[1],
            },
            StateOnlyProfile21TreeInput {
                tree: &later_trees[2],
                values: &later_values[2],
                salts: &later_salts[2],
            },
        ],
    };
    let openings = serialize_state_only_profile21_openings(&queries, &opening_inputs)?;
    let roots = StateOnlyProfile21OpeningRoots {
        c1: material.c1_root,
        c2: material.c2_root,
        later: material.later_roots,
    };
    let mut bytes = Vec::with_capacity(profile_prefix.len() + openings.bytes.len());
    bytes.extend_from_slice(&profile_prefix);
    bytes.extend_from_slice(&openings.bytes);
    Ok(BuiltAtomicStateOnlyProfile21Proof {
        bytes,
        schedule,
        relation,
        roots,
        openings,
        logical_x,
        logical_f,
        logical_u,
        tau,
        source_nonce,
        pow_valid,
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_core::state_only_prefix::StateOnlyProfile21Prefix;
    use aspis_core::state_only_prefix::{
        STATE_ONLY_PREFIX_LEN, STATE_ONLY_PROFILE21_PREFIX_LEN, STATE_ONLY_PROFILE21_U_BYTES,
    };
    use aspis_core::state_only_profile21_openings::verify_state_only_profile21_openings;
    use aspis_core::sumcheck::evaluate;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::state_only_profile21::{
        verify_atomic_state_only_profile21_unmined_for_diagnostics_v3, Profile21VerifyError,
    };
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment, Digest, MerklePath,
        SpendPublic,
    };

    use super::*;
    use crate::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
    use crate::HOST_HASH;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture() -> (AtomicPaymentStatementV3, SpendWitness) {
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
        let statement = AtomicPaymentStatementV3 {
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
        };
        (statement, witness)
    }

    #[test]
    fn literal_profile21_builder_emits_canonical_private_five_tree_proof() {
        let (statement, witness) = fixture();
        let attempt = StateOnlyAttemptSecrets::deterministic_profile21_fixture(
            [0x21; 32], [0x43; 32], [0x65; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let built = build_hiding_atomic_state_only_profile21_proof_v3(
            &statement,
            &witness,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        assert!(!built.pow_valid);
        let (prefix, suffix) = StateOnlyProfile21Prefix::parse_from_proof(&built.bytes).unwrap();
        assert_eq!(prefix.logical_u(), built.logical_u);
        assert_eq!(prefix.tau(), built.tau);
        let verified = verify_state_only_profile21_openings(
            HOST_HASH,
            &built.roots,
            &built.schedule.base.queries[..built.schedule.base.query_count],
            suffix,
        )
        .unwrap();
        assert_eq!(verified.end, suffix.len());
        verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
            &built.bytes,
            &statement,
            HOST_HASH,
            None,
        )
        .unwrap();

        // Honest differential: serialized tau is exactly both the old
        // <weights,phi(U)> result retained by the prover and the scalar
        // recoverable from round one's boundary after subtracting its two
        // authenticated OOD additions.
        let after_round_zero = evaluate(&built.relation.sumchecks[0], built.schedule.base.alpha[0]);
        let explicit_seam_target = built.relation.running_claims[1].sub(after_round_zero);
        let round_one_ood = built.schedule.base.mu[1]
            .iter()
            .copied()
            .zip(built.relation.ood_values[1])
            .fold(QM31::ZERO, |sum, (mix, value)| sum.add(mix.mul(value)));
        let inferred_seam_target = built.relation.boundary_claims[1]
            .sub(round_one_ood)
            .sub(after_round_zero);
        assert_eq!(inferred_seam_target, explicit_seam_target);
        assert_eq!(explicit_seam_target, built.tau);
        assert!(
            aspis_statement::state_only_profile21::verify_atomic_state_only_profile21_v3(
                &built.bytes,
                &statement,
                HOST_HASH,
                None,
            )
            .is_err()
        );

        // Full-boundary teeth. Each mutation is after construction, so no
        // reference path can accidentally regenerate the same bad object.
        let tau_start = STATE_ONLY_PREFIX_LEN + CANDIDATE_NONCE_LEN + STATE_ONLY_PROFILE21_U_BYTES;
        let mut changed_tau = built.bytes.clone();
        changed_tau[tau_start] ^= 1;
        assert!(
            verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
                &changed_tau,
                &statement,
                HOST_HASH,
                None,
            )
            .is_err()
        );

        let logical_u_start = STATE_ONLY_PREFIX_LEN + CANDIDATE_NONCE_LEN;
        let mut changed_u = built.bytes.clone();
        changed_u[logical_u_start] ^= 1;
        assert!(
            verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
                &changed_u, &statement, HOST_HASH, None,
            )
            .is_err()
        );

        let c2_start = STATE_ONLY_PROFILE21_PREFIX_LEN + built.openings.section_bytes[0];
        let mut changed_source_leaf = built.bytes.clone();
        changed_source_leaf[c2_start + 2 + 128] ^= 1;
        assert!(
            verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
                &changed_source_leaf,
                &statement,
                HOST_HASH,
                None,
            )
            .is_err()
        );

        let w1_start = c2_start + built.openings.section_bytes[1];
        let mut changed_w1 = built.bytes.clone();
        changed_w1[w1_start + 2] ^= 1;
        assert!(
            verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
                &changed_w1,
                &statement,
                HOST_HASH,
                None,
            )
            .is_err()
        );

        let mut trailing = built.bytes.clone();
        trailing.push(0xa5);
        assert!(
            verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
                &trailing, &statement, HOST_HASH, None,
            )
            .is_err()
        );

        // Build an internally self-consistent ordinary relation and W1 from
        // U plus a nonzero randomness-coordinate seam, while disclosing the
        // original U. Its serialized tau and relation boundary accept that seam; the
        // authenticated q16 W1-Fold(W0)=Enc(U) equality must reject it.
        let seam_attempt = StateOnlyAttemptSecrets::deterministic_profile21_fixture(
            [0x22; 32], [0x44; 32], [0x66; 32],
        );
        let seam_bad = build_hiding_atomic_state_only_profile21_proof_inner_v3(
            &statement,
            &witness,
            seam_attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
            QM31::ONE,
        )
        .unwrap();
        assert!(matches!(
            verify_atomic_state_only_profile21_unmined_for_diagnostics_v3(
                &seam_bad.bytes,
                &statement,
                HOST_HASH,
                None,
            ),
            Err(Profile21VerifyError::TranslatedSpliceMismatch { .. })
        ));
        eprintln!(
            "profile21 bytes={} sha256={} section_bytes={:?} frontier_nodes={:?}",
            built.bytes.len(),
            HOST_HASH(&[&built.bytes])
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>(),
            built.openings.section_bytes,
            built.openings.frontier_nodes,
        );
    }
}
