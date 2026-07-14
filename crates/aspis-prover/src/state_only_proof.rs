//! Completion of a state-only prefix into a full serialized circle proof.
//!
//! This is separate from the front builder so transcript/front semantics stay
//! frozen.  The selected C1 order is semantic `0..16`, mask-only `16..26`,
//! followed by C2 `(h1,G)` at generator indices `26,27`.

use aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT;
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
    RATE16_HARDENED_FOLD_POW_BITS,
};
use aspis_core::field::QM31;
use aspis_core::proof::{HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR};
use aspis_core::state_only_hiding::{begin_state_only_hiding_precommit, StateOnlyHidingContext};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_state_only_transcript_schedule_host_unmined_for_diagnostics, StateOnlyCandidatePrefix,
    StateOnlyProfileShape, StateOnlyTranscriptScheduleResult, STATE_ONLY_LOG_ROWS,
};
use aspis_core::state_only_relation::prepare_state_only_relation;
use aspis_core::sumcheck::{SumcheckPolynomial, SUMCHECK_COEFFICIENTS};
use aspis_core::transcript::{label, QuerySampleError, Transcript};
use aspis_core::HashFn;
use aspis_statement::{
    atomic_payment_statement_digest_v3,
    atomic_state_only_trace::{build_atomic_state_only_trace_v3, AtomicStateOnlyTraceV3Error},
    verify_atomic_state_only_candidate_unmined_for_diagnostics_v3,
    verify_state_only_candidate_unmined_for_diagnostics, AtomicPaymentStatementV3,
    AtomicStatementError, SpendPublic, SpendWitness, StateOnlyCandidateVerifyError,
};

use crate::circle_candidate::{
    build_fold_commitments_for_domain_log, combined_candidate_layer_root_for_domain_log,
    fold_candidate_codeword_round_for_domain_log, CircleEncoder,
};
use crate::circle_candidate_openings::serialize_candidate_openings_for_fiber_count_with_leaf_bytes;
use crate::circle_candidate_prefix::CandidatePrefixBuildError;
use crate::state_only_candidate::{
    gamma_combine_state_only_codewords, gamma_combine_state_only_messages,
};
use crate::state_only_candidate_prefix::{
    build_atomic_state_only_prefix_front_selected_with_h1_padding_v3,
    build_state_only_prefix_front_selected_with_h1_padding, serialize_state_only_prefix,
    state_only_header, BuiltStateOnlyPrefixFront, StateOnlyPowMode, StateOnlyPrefixBuildError,
    StateOnlyPrefixMaterial,
};
use crate::state_only_circle_relation::{
    StateOnlyCircleRelationTrace, StateOnlyIncrementalRelation,
};
use crate::state_only_hiding::{
    apply_atomic_state_only_mask_material_v3, apply_state_only_mask_material,
    build_atomic_state_only_mask_material_v3, build_state_only_mask_material,
    StateOnlyMaskNonceStore,
};
use aspis_statement::StateOnlyTraceFoundation;

#[derive(Debug)]
pub enum StateOnlyProofBuildError {
    Front(StateOnlyPrefixBuildError),
    Candidate(CandidatePrefixBuildError),
    Query(QuerySampleError),
    Verifier(StateOnlyCandidateVerifyError),
    AtomicTrace(AtomicStateOnlyTraceV3Error),
    AtomicStatement(AtomicStatementError),
}

impl From<AtomicStateOnlyTraceV3Error> for StateOnlyProofBuildError {
    fn from(error: AtomicStateOnlyTraceV3Error) -> Self {
        Self::AtomicTrace(error)
    }
}

impl From<AtomicStatementError> for StateOnlyProofBuildError {
    fn from(error: AtomicStatementError) -> Self {
        Self::AtomicStatement(error)
    }
}

impl From<StateOnlyPrefixBuildError> for StateOnlyProofBuildError {
    fn from(error: StateOnlyPrefixBuildError) -> Self {
        Self::Front(error)
    }
}

impl From<CandidatePrefixBuildError> for StateOnlyProofBuildError {
    fn from(error: CandidatePrefixBuildError) -> Self {
        Self::Candidate(error)
    }
}

impl From<QuerySampleError> for StateOnlyProofBuildError {
    fn from(error: QuerySampleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone)]
pub struct BuiltStateOnlyProof {
    pub bytes: Vec<u8>,
    pub material: StateOnlyPrefixMaterial,
    pub relation: StateOnlyCircleRelationTrace,
    pub schedule: StateOnlyTranscriptScheduleResult,
    pub pow_valid: bool,
    pub front: BuiltStateOnlyPrefixFront,
}

fn absorb_round_root(transcript: &mut Transcript, layer: usize, root: &[u8; 32]) {
    let mut record = [0u8; 33];
    record[0] = layer as u8;
    record[1..].copy_from_slice(root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn absorb_ood_value(
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
    for (coefficient, value) in polynomial.iter().enumerate() {
        value.write_le_bytes(&mut record[1 + coefficient * 16..][..16]);
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

fn pow_nonce(transcript: &Transcript, bits: u8, mode: StateOnlyPowMode) -> u64 {
    match mode {
        StateOnlyPowMode::UnminedZero => 0,
        StateOnlyPowMode::Mine => crate::find_grinding_nonce(transcript, bits),
    }
}

/// Build the actual hiding construction from private one-time entropy, apply
/// all semantic relation-free masks, append the ten full-domain mask-only C1
/// columns, and complete the serialized proof.
#[allow(clippy::too_many_arguments)]
pub fn build_hiding_state_only_proof(
    public: &SpendPublic,
    mut trace: StateOnlyTraceFoundation,
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    shape: StateOnlyProfileShape,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyProof, StateOnlyProofBuildError> {
    let context = StateOnlyHidingContext::pinned(statement_digest, mask_nonce);
    let mut header_bytes = [0u8; HEADER_LEN];
    state_only_header(shape).write(&mut header_bytes);
    let mut precommit = Transcript::new(hash);
    precommit.absorb(label::PROFILE, &header_bytes);
    precommit.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    precommit.absorb(label::STATEMENT, &statement_digest);
    let binding = begin_state_only_hiding_precommit(&mut precommit, context)
        .map_err(StateOnlyPrefixBuildError::Hiding)?;
    let material =
        build_state_only_mask_material(hash, binding, context, private_entropy, nonce_store)
            .map_err(StateOnlyPrefixBuildError::Mask)?;
    let applied = apply_state_only_mask_material(&mut trace, material)
        .map_err(StateOnlyPrefixBuildError::Mask)?;
    let front = build_state_only_prefix_front_selected_with_h1_padding(
        public,
        &trace,
        &applied.mask_only_c1,
        &applied.g,
        &applied.h1_padding,
        statement_digest,
        applied.mask_nonce,
        shape,
        hash,
        pow_mode,
    )?;
    complete_state_only_proof(public, statement_digest, front, hash, pow_mode)
}

/// Build the actual atomic-v3 trace, apply the atomic-pinned relation-free
/// masks, bind every atomic public field through the statement digest, and
/// complete one read-only profile-20 proof.  Account mutation is deliberately
/// outside this API.
#[allow(clippy::too_many_arguments)]
pub fn build_hiding_atomic_state_only_proof_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    mask_nonce: [u8; 32],
    private_entropy: [u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    shape: StateOnlyProfileShape,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyProof, StateOnlyProofBuildError> {
    let mut atomic = build_atomic_state_only_trace_v3(statement, witness)?;
    let mut trace = core::mem::take(&mut atomic.trace);
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)?;
    let context = StateOnlyHidingContext::atomic_v3(statement_digest, mask_nonce);
    let mut header_bytes = [0u8; HEADER_LEN];
    state_only_header(shape).write(&mut header_bytes);
    let mut precommit = Transcript::new(hash);
    precommit.absorb(label::PROFILE, &header_bytes);
    precommit.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    precommit.absorb(label::STATEMENT, &statement_digest);
    let binding = begin_state_only_hiding_precommit(&mut precommit, context)
        .map_err(StateOnlyPrefixBuildError::Hiding)?;
    let material = build_atomic_state_only_mask_material_v3(
        hash,
        binding,
        context,
        private_entropy,
        nonce_store,
    )
    .map_err(StateOnlyPrefixBuildError::Mask)?;
    let applied = apply_atomic_state_only_mask_material_v3(&mut trace, material)
        .map_err(StateOnlyPrefixBuildError::Mask)?;
    let front = build_atomic_state_only_prefix_front_selected_with_h1_padding_v3(
        statement,
        &trace,
        &applied.mask_only_c1,
        &applied.g,
        &applied.h1_padding,
        statement_digest,
        applied.mask_nonce,
        shape,
        hash,
        pow_mode,
    )?;
    complete_atomic_state_only_proof_v3(statement, statement_digest, front, hash, pow_mode)
}

/// Finish a previously constructed front without changing its causal order.
pub fn complete_state_only_proof(
    public: &SpendPublic,
    statement_digest: [u8; 32],
    front: BuiltStateOnlyPrefixFront,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyProof, StateOnlyProofBuildError> {
    complete_state_only_proof_with_registry(
        public,
        statement_digest,
        front,
        hash,
        pow_mode,
        aspis_statement::state_only_copy_inactive_row_masks_v4(),
        None,
    )
}

pub fn complete_atomic_state_only_proof_v3(
    statement: &AtomicPaymentStatementV3,
    statement_digest: [u8; 32],
    front: BuiltStateOnlyPrefixFront,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyProof, StateOnlyProofBuildError> {
    complete_state_only_proof_with_registry(
        &statement.spend,
        statement_digest,
        front,
        hash,
        pow_mode,
        aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3(),
        Some(statement),
    )
}

#[allow(clippy::too_many_arguments)]
fn complete_state_only_proof_with_registry(
    public: &SpendPublic,
    statement_digest: [u8; 32],
    mut front: BuiltStateOnlyPrefixFront,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
    inactive_masks: [u16; 64],
    atomic_statement: Option<&AtomicPaymentStatementV3>,
) -> Result<BuiltStateOnlyProof, StateOnlyProofBuildError> {
    let domain_log = STATE_ONLY_LOG_ROWS + front.material.shape.log_blowup;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let selected_c1 = front
        .trace
        .c1
        .iter()
        .cloned()
        .chain(front.mask_only_c1.iter().cloned())
        .collect::<Vec<_>>();
    let c2_messages = [front.h1.clone(), front.g.clone()];
    let original_message =
        gamma_combine_state_only_messages(&selected_c1, &c2_messages, front.schedule.gamma)
            .map_err(CandidatePrefixBuildError::from)?;
    let original_codeword = gamma_combine_state_only_codewords(
        &front.encoded_c1,
        &front.encoded_c2,
        front.schedule.gamma,
        encoder.codeword_len(),
    )
    .map_err(CandidatePrefixBuildError::from)?;
    let z = front.schedule.z;
    let points = [
        z,
        aspis_statement::state_only_poseidon::successor_point(&z),
        aspis_statement::state_only_poseidon::xor12_point(&z),
    ];
    let kappa = front.schedule.point_scale;
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks(
        original_message.clone(),
        &points,
        [QM31::ONE, kappa, kappa.square()],
        inactive_masks,
    )?;
    let prepared = prepare_state_only_relation(
        front.schedule.gamma,
        &front.bytes[aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS
            .statement_evaluations_start..]
            [..aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_EVALUATIONS_LEN],
    )
    .ok_or(CandidatePrefixBuildError::Consistency(
        "state-only statement values failed fused preparation",
    ))?;
    let mut transcript = front.transcript_after_gamma.clone();
    let mut combined_codeword = original_codeword.clone();
    let mut later_roots = [[0u8; 32]; CANDIDATE_ROUND_COUNT - 1];
    let mut fold_nonces = [0u64; CANDIDATE_ROUND_COUNT];
    let mut alphas = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    let mut pow_valid = front.batch_pow_valid;
    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = transcript
                    .challenge_secure_circle_point()
                    .map_err(CandidatePrefixBuildError::from)?;
                let value = relation.evaluate_circle_ood(point)?;
                absorb_ood_value(
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
                absorb_ood_value(
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
        )
        .map_err(CandidatePrefixBuildError::from)?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            later_roots[round] = combined_candidate_layer_root_for_domain_log(
                &combined_codeword,
                round + 1,
                domain_log,
                hash,
            )
            .map_err(CandidatePrefixBuildError::from)?;
            absorb_round_root(&mut transcript, round + 1, &later_roots[round]);
        }
    }
    let relation = relation.finish()?;
    if relation.point_claims != prepared.claims {
        return Err(CandidatePrefixBuildError::Consistency(
            "state-only relation claims differ from the fused statement block",
        )
        .into());
    }
    absorb_final(&mut transcript, &relation.final_coefficients);
    // Final work is fixed at 36 bits for the append-only profile-20 proof.
    // Profile 21 defines its g38 header/schedule separately.
    let nonce = pow_nonce(&transcript, 36, pow_mode);
    pow_valid &= transcript.grinding_ok(nonce, 36);
    transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes());
    let queries = transcript.challenge_queries_without_replacement(
        front.material.shape.query_count as usize,
        encoder.codeword_len() as u32 / 4,
        PAYMENT_HIDING_QUERY_DRAW_LIMIT,
    )?;

    let mut material = front.material.clone();
    material.later_roots = later_roots;
    material.ood_values = relation.ood_values;
    material.relation_sumchecks = relation.sumchecks;
    material.final_coefficients = relation.final_coefficients;
    material.nonce = nonce;
    material.fold_nonces = fold_nonces;
    let prefix_bytes = serialize_state_only_prefix(&material);
    let folds = build_fold_commitments_for_domain_log(
        &original_codeword,
        &original_message,
        alphas,
        domain_log,
        hash,
    )
    .map_err(CandidatePrefixBuildError::from)?;
    if folds.roots != later_roots || folds.final_coefficients != relation.final_coefficients {
        return Err(CandidatePrefixBuildError::Consistency(
            "state-only opening commitments differ from sequential relation",
        )
        .into());
    }
    let suffix = serialize_candidate_openings_for_fiber_count_with_leaf_bytes(
        &queries,
        &front.c1_leaves,
        &front.c2_leaves,
        &folds,
        encoder.codeword_len() / 4,
        hash,
    )
    .map_err(CandidatePrefixBuildError::from)?;
    let mut bytes = Vec::with_capacity(prefix_bytes.len() + suffix.len());
    bytes.extend_from_slice(&prefix_bytes);
    bytes.extend_from_slice(&suffix);
    let parsed = StateOnlyCandidatePrefix::parse_exact(&prefix_bytes)
        .map_err(CandidatePrefixBuildError::from)?;
    let schedule = if atomic_statement.is_some() {
        run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
            hash,
            &parsed,
            &statement_digest,
        )
    } else {
        run_state_only_transcript_schedule_host_unmined_for_diagnostics(
            hash,
            &parsed,
            &statement_digest,
        )
    }
    .map_err(|_| CandidatePrefixBuildError::Consistency("state-only replay failed"))?;
    if schedule.alpha != alphas || schedule.queries[..schedule.query_count] != queries {
        return Err(CandidatePrefixBuildError::Consistency(
            "state-only transcript completion diverged",
        )
        .into());
    }
    if let Some(statement) = atomic_statement {
        verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
            &bytes, statement, hash, None,
        )
        .map_err(StateOnlyProofBuildError::Verifier)?;
    } else {
        verify_state_only_candidate_unmined_for_diagnostics(
            &bytes,
            public,
            &statement_digest,
            hash,
        )
        .map_err(StateOnlyProofBuildError::Verifier)?;
    }
    front.transcript_after_gamma = Transcript::new(hash);
    Ok(BuiltStateOnlyProof {
        bytes,
        material,
        relation,
        schedule,
        pow_valid,
        front,
    })
}
