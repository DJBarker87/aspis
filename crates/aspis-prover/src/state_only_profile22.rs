//! Atomic profile-22 builder: profile-20 algebra with five private Merkle trees.

use aspis_core::circle_line_merkle::CIRCLE_LINE_TAGS;
use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::circle_prefix::{
    CandidatePrefixError, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES,
    CANDIDATE_ROUND_COUNT, RATE16_HARDENED_FOLD_POW_BITS,
};
use aspis_core::field::QM31;
use aspis_core::proof::{HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR};
use aspis_core::state_only_hiding::{begin_state_only_hiding_precommit, StateOnlyHidingContext};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_prefix_schedule_host_v3,
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix, StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult,
    STATE_ONLY_LOG_ROWS, STATE_ONLY_PROFILE22_GRINDING_BITS, STATE_ONLY_PROFILE22_PRIVATE_SHAPE,
};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_profile22_openings::StateOnlyProfile22OpeningRoots;
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
use zeroize::Zeroize;

use crate::circle_candidate::{
    combined_layer_leaves, fold_candidate_codeword_round_for_domain_log, CircleCandidateError,
    CircleEncoder,
};
use crate::circle_candidate_prefix::CandidatePrefixBuildError;
use crate::pow::UnpublishedPowError;
use crate::state_only_candidate::{
    encode_state_only_c1_columns, encode_state_only_c2_columns, gamma_combine_state_only_codewords,
    gamma_combine_state_only_messages, state_only_c1_layer0_leaves, state_only_c2_layer0_leaves,
};
use crate::state_only_candidate_prefix::{
    serialize_state_only_prefix, state_only_header, statement_evaluations, StateOnlyPowMode,
    StateOnlyPrefixBuildError, StateOnlyPrefixMaterial,
};
use crate::state_only_circle_relation::{
    StateOnlyCircleRelationTrace, StateOnlyIncrementalRelation,
};
use crate::state_only_entropy::{
    DurableStateOnlyMaskNonceStore, ReservedStateOnlyAttemptSecrets, StateOnlyAttemptSecrets,
};
use crate::state_only_good22::{
    evaluate_profile22_strong_good_schedule, run_profile22_first_good, Profile22AttemptsExhausted,
};
use crate::state_only_hiding::{
    apply_atomic_state_only_h1_padding_mask_v3, apply_atomic_state_only_mask_material_v3,
    prove_masked_state_only_zerocheck, StateOnlyMaskBuildError, StateOnlyMaskNonceStore,
};
use crate::state_only_private_openings::{
    build_state_only_private_merkle_tree, StateOnlyPrivateOpeningBuildError,
};
use crate::state_only_profile22_openings::{
    serialize_state_only_profile22_openings, BuiltStateOnlyProfile22Openings,
    StateOnlyProfile22OpeningBuildError, StateOnlyProfile22OpeningInputs,
    StateOnlyProfile22TreeInput,
};

pub const PROFILE22_C1_VALUE_WIDTH: usize = 416;
pub const PROFILE22_C2_VALUE_WIDTH: usize = 128;

#[derive(Debug)]
pub enum StateOnlyProfile22BuildError {
    AtomicTrace(AtomicStateOnlyTraceV3Error),
    AtomicStatement(AtomicStatementError),
    Front(StateOnlyPrefixBuildError),
    Candidate(CandidatePrefixBuildError),
    Circle(CircleCandidateError),
    Mask(StateOnlyMaskBuildError),
    Private(StateOnlyPrivateOpeningBuildError),
    Openings(StateOnlyProfile22OpeningBuildError),
    Prefix(CandidatePrefixError),
    Transcript(StateOnlyTranscriptError),
    Pow(UnpublishedPowError),
    Consistency(&'static str),
}

impl From<AtomicStateOnlyTraceV3Error> for StateOnlyProfile22BuildError {
    fn from(value: AtomicStateOnlyTraceV3Error) -> Self {
        Self::AtomicTrace(value)
    }
}
impl From<AtomicStatementError> for StateOnlyProfile22BuildError {
    fn from(value: AtomicStatementError) -> Self {
        Self::AtomicStatement(value)
    }
}
impl From<StateOnlyPrefixBuildError> for StateOnlyProfile22BuildError {
    fn from(value: StateOnlyPrefixBuildError) -> Self {
        Self::Front(value)
    }
}
impl From<CandidatePrefixBuildError> for StateOnlyProfile22BuildError {
    fn from(value: CandidatePrefixBuildError) -> Self {
        Self::Candidate(value)
    }
}
impl From<CircleCandidateError> for StateOnlyProfile22BuildError {
    fn from(value: CircleCandidateError) -> Self {
        Self::Circle(value)
    }
}
impl From<StateOnlyMaskBuildError> for StateOnlyProfile22BuildError {
    fn from(value: StateOnlyMaskBuildError) -> Self {
        Self::Mask(value)
    }
}
impl From<StateOnlyPrivateOpeningBuildError> for StateOnlyProfile22BuildError {
    fn from(value: StateOnlyPrivateOpeningBuildError) -> Self {
        Self::Private(value)
    }
}
impl From<StateOnlyProfile22OpeningBuildError> for StateOnlyProfile22BuildError {
    fn from(value: StateOnlyProfile22OpeningBuildError) -> Self {
        Self::Openings(value)
    }
}
impl From<CandidatePrefixError> for StateOnlyProfile22BuildError {
    fn from(value: CandidatePrefixError) -> Self {
        Self::Prefix(value)
    }
}
impl From<StateOnlyTranscriptError> for StateOnlyProfile22BuildError {
    fn from(value: StateOnlyTranscriptError) -> Self {
        Self::Transcript(value)
    }
}
impl From<UnpublishedPowError> for StateOnlyProfile22BuildError {
    fn from(value: UnpublishedPowError) -> Self {
        Self::Pow(value)
    }
}

pub struct BuiltAtomicStateOnlyProfile22Proof {
    pub bytes: Vec<u8>,
    pub schedule: StateOnlyTranscriptScheduleResult,
    pub relation: StateOnlyCircleRelationTrace,
    pub roots: StateOnlyProfile22OpeningRoots,
    pub openings: BuiltStateOnlyProfile22Openings,
    pub pow_valid: bool,
}

impl BuiltAtomicStateOnlyProfile22Proof {
    pub(crate) fn scrub_rejected(&mut self) {
        // These buffers contain the complete rejected candidate view. Use
        // `Zeroize`, rather than ordinary fills that an optimizer may remove
        // immediately before drop.
        self.bytes.zeroize();
        self.openings.bytes.zeroize();
        self.openings.indices.layer0.zeroize();
        for indices in &mut self.openings.indices.later {
            indices.zeroize();
        }
        self.roots.c1.zeroize();
        self.roots.c2.zeroize();
        for root in &mut self.roots.later {
            root.zeroize();
        }
        self.relation.point_claims.fill(QM31::ZERO);
        for values in &mut self.relation.ood_values {
            values.fill(QM31::ZERO);
        }
        self.relation.boundary_claims.fill(QM31::ZERO);
        for polynomial in &mut self.relation.sumchecks {
            polynomial.fill(QM31::ZERO);
        }
        self.relation.running_claims.fill(QM31::ZERO);
        self.relation.final_coefficients.fill(QM31::ZERO);
        self.relation.terminal_claim = QM31::ZERO;
        self.schedule.prefix.lambda = QM31::ZERO;
        self.schedule.prefix.chi = QM31::ZERO;
        self.schedule.prefix.batching.theta = QM31::ZERO;
        self.schedule
            .prefix
            .batching
            .zerocheck_point
            .fill(QM31::ZERO);
        self.schedule.prefix.batching.mu = QM31::ZERO;
        self.schedule.prefix.initial_mask_claim = QM31::ZERO;
        self.schedule.prefix.eta = QM31::ZERO;
        self.schedule.prefix.z.fill(QM31::ZERO);
        self.schedule.prefix.masked_terminal_claim = QM31::ZERO;
        self.schedule.prefix.gamma = QM31::ZERO;
        self.schedule.prefix.point_scale = QM31::ZERO;
        self.schedule.prefix.state_after_gamma.zeroize();
        for point in &mut self.schedule.circle_ood_points {
            point.x = QM31::ZERO;
            point.y = QM31::ZERO;
        }
        for points in &mut self.schedule.line_ood_points {
            points.fill(QM31::ZERO);
        }
        for mixes in &mut self.schedule.mu {
            mixes.fill(QM31::ZERO);
        }
        self.schedule.alpha.fill(QM31::ZERO);
        self.schedule.state_before_grinding.zeroize();
        self.schedule.queries.zeroize();
        self.schedule.query_count = 0;
        self.schedule.state_after_queries.zeroize();
        self.pow_valid = false;
    }

    /// Consume a locally buffered, production-mined candidate into the only
    /// proof payload the fixed-release channel may publish.  Non-wire
    /// metadata is scrubbed before it is dropped.
    pub(crate) fn into_released_bytes(mut self) -> Vec<u8> {
        let bytes = core::mem::take(&mut self.bytes);
        self.scrub_rejected();
        bytes
    }
}

/// Opaque output of the production first-good worker.  It can be created only
/// by the fixed-cap, mined Good22 path and consumed only by the fixed-release
/// controller.  Dropping it before publication scrubs the buffered candidate.
pub struct Profile22FirstGoodCandidate {
    candidate: Option<BuiltAtomicStateOnlyProfile22Proof>,
}

impl Profile22FirstGoodCandidate {
    fn new(candidate: BuiltAtomicStateOnlyProfile22Proof) -> Self {
        Self {
            candidate: Some(candidate),
        }
    }

    pub(crate) fn production_ready(&self) -> bool {
        self.candidate
            .as_ref()
            .is_some_and(|candidate| candidate.pow_valid)
    }

    pub(crate) fn scrub(&mut self) {
        if let Some(mut candidate) = self.candidate.take() {
            candidate.scrub_rejected();
        }
    }

    pub(crate) fn into_released_bytes(mut self) -> Vec<u8> {
        self.candidate
            .take()
            .expect("first-good candidate consumed once")
            .into_released_bytes()
    }
}

impl Drop for Profile22FirstGoodCandidate {
    fn drop(&mut self) {
        self.scrub();
    }
}

fn pow_nonce(
    transcript: &Transcript,
    bits: u8,
    mode: StateOnlyPowMode,
) -> Result<u64, StateOnlyProfile22BuildError> {
    match mode {
        StateOnlyPowMode::UnminedZero => Ok(0),
        StateOnlyPowMode::Mine => {
            crate::pow::find_grinding_nonce_unpublished(transcript, bits).map_err(Into::into)
        }
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

fn flatten<const N: usize>(leaves: &[[u8; N]]) -> Vec<u8> {
    let mut values = Vec::with_capacity(leaves.len() * N);
    for leaf in leaves {
        values.extend_from_slice(leaf);
    }
    values
}

fn derive_salts(
    reserved: &ReservedStateOnlyAttemptSecrets,
    context: StateOnlyHidingContext,
    hash: HashFn,
    tag: u8,
    count: usize,
) -> Result<Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>, StateOnlyProfile22BuildError> {
    (0..count)
        .map(|index| {
            reserved
                .derive_profile22_leaf_salt(hash, context, tag, index as u32)
                .map_err(StateOnlyProfile22BuildError::from)
        })
        .collect()
}

/// Build the no-switch profile with the same algebra and FS order as profile
/// 20, but private-salted roots and openings from the first commitment.
#[allow(clippy::too_many_lines)]
fn build_hiding_atomic_state_only_profile22_one_attempt_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltAtomicStateOnlyProfile22Proof, StateOnlyProfile22BuildError> {
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)?;
    let mask_nonce = attempt.mask_nonce();
    let context = StateOnlyHidingContext::atomic_v3(statement_digest, mask_nonce);
    let mut header_bytes = [0u8; HEADER_LEN];
    state_only_header(STATE_ONLY_PROFILE22_PRIVATE_SHAPE).write(&mut header_bytes);
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
    // The public nonce is durably burned before private mask/salt derivation,
    // witness validation, mask application, commitment construction or mining.
    let mut atomic = build_atomic_state_only_trace_v3(statement, witness)?;
    let mut trace = core::mem::take(&mut atomic.trace);
    let applied = apply_atomic_state_only_mask_material_v3(&mut trace, mask_material)?;

    let domain_log = STATE_ONLY_LOG_ROWS + STATE_ONLY_PROFILE22_PRIVATE_SHAPE.log_blowup;
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
        PROFILE22_C1_VALUE_WIDTH,
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
        return Err(StateOnlyProfile22BuildError::Consistency(
            "profile22 h1 sum",
        ));
    }

    let c2_messages = [h1.clone(), applied.g.clone()];
    let encoded_c2 = encode_state_only_c2_columns(&encoder, &c2_messages)?;
    let c2_leaves = state_only_c2_layer0_leaves(&encoded_c2, encoder.codeword_len())?;
    let c2_values = flatten(&c2_leaves);
    let c2_salts = derive_salts(
        &reserved,
        context,
        hash,
        CIRCLE_C2_LAYER0_TAG,
        c2_leaves.len(),
    )?;
    let c2_tree = build_state_only_private_merkle_tree(
        hash,
        17,
        CIRCLE_C2_LAYER0_TAG,
        PROFILE22_C2_VALUE_WIDTH,
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
        STATE_ONLY_PROFILE22_PRIVATE_SHAPE,
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
    let mut prefix_bytes = serialize_state_only_prefix(&material);
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        &prefix_bytes[aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS
            .statement_evaluations_start..]
            [..aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_EVALUATIONS_LEN],
    );
    material.batch_nonce = pow_nonce(
        &transcript,
        STATE_ONLY_PROFILE22_PRIVATE_SHAPE.batch_grinding_bits,
        pow_mode,
    )?;
    let mut pow_valid = transcript.grinding_ok(
        material.batch_nonce,
        STATE_ONLY_PROFILE22_PRIVATE_SHAPE.batch_grinding_bits,
    );
    transcript.absorb(
        label::M31_PAYMENT_BATCH_POW_NONCE,
        &material.batch_nonce.to_le_bytes(),
    );
    let gamma = transcript
        .challenge_nonzero_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    let point_scale = transcript
        .challenge_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    prefix_bytes = serialize_state_only_prefix(&material);
    let parsed_front = StateOnlyCandidatePrefix::parse_exact(&prefix_bytes)?;
    let front_schedule =
        run_atomic_state_only_prefix_schedule_host_v3(hash, &parsed_front, &statement_digest)?;
    if front_schedule.gamma != gamma
        || front_schedule.point_scale != point_scale
        || front_schedule.lambda != lambda
        || front_schedule.chi != chi
        || front_schedule.z != masked.sumcheck.challenges
    {
        return Err(StateOnlyProfile22BuildError::Consistency(
            "profile22 front replay",
        ));
    }

    let original_message = gamma_combine_state_only_messages(&selected_c1, &c2_messages, gamma)?;
    let original_codeword = gamma_combine_state_only_codewords(
        &encoded_c1,
        &encoded_c2,
        gamma,
        encoder.codeword_len(),
    )?;
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
        &prefix_bytes[aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS
            .statement_evaluations_start..]
            [..aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_EVALUATIONS_LEN],
    )
    .ok_or(StateOnlyProfile22BuildError::Consistency(
        "profile22 fused relation",
    ))?;

    let mut combined_codeword = original_codeword;
    let mut fold_nonces = [0u64; CANDIDATE_ROUND_COUNT];
    let mut alphas = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    let mut later_values = Vec::with_capacity(3);
    let mut later_salts = Vec::with_capacity(3);
    let mut later_trees = Vec::with_capacity(3);
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
        fold_nonces[round] =
            pow_nonce(&transcript, RATE16_HARDENED_FOLD_POW_BITS[round], pow_mode)?;
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
        if round + 1 < CANDIDATE_ROUND_COUNT {
            let leaves = combined_layer_leaves(&combined_codeword);
            let values = flatten(&leaves);
            let tag = CIRCLE_LINE_TAGS[round];
            let salts = derive_salts(&reserved, context, hash, tag, leaves.len())?;
            let depth = 15 - 2 * round as u32;
            let tree = build_state_only_private_merkle_tree(hash, depth, tag, 64, &values, &salts)?;
            material.later_roots[round] = tree.root();
            absorb_round_root(&mut transcript, round + 1, &material.later_roots[round]);
            later_values.push(values);
            later_salts.push(salts);
            later_trees.push(tree);
        }
    }

    let relation = relation.finish()?;
    if relation.point_claims != prepared.claims {
        return Err(StateOnlyProfile22BuildError::Consistency(
            "profile22 point claims",
        ));
    }
    absorb_final(&mut transcript, &relation.final_coefficients);
    material.nonce = pow_nonce(&transcript, STATE_ONLY_PROFILE22_GRINDING_BITS, pow_mode)?;
    pow_valid &= transcript.grinding_ok(material.nonce, STATE_ONLY_PROFILE22_GRINDING_BITS);
    transcript.absorb(label::GRIND_NONCE, &material.nonce.to_le_bytes());
    let queries = transcript
        .challenge_queries_without_replacement(
            STATE_ONLY_PROFILE22_PRIVATE_SHAPE.query_count as usize,
            (encoder.codeword_len() / 4) as u32,
            aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT,
        )
        .map_err(|_| StateOnlyProfile22BuildError::Consistency("profile22 q sampler"))?;

    material.ood_values = relation.ood_values;
    material.relation_sumchecks = relation.sumchecks;
    material.final_coefficients = relation.final_coefficients;
    material.fold_nonces = fold_nonces;
    prefix_bytes = serialize_state_only_prefix(&material);
    let parsed = StateOnlyCandidatePrefix::parse_exact(&prefix_bytes)?;
    let schedule = run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
        hash,
        &parsed,
        &statement_digest,
    )?;
    if schedule.alpha != alphas || schedule.queries[..schedule.query_count] != queries {
        return Err(StateOnlyProfile22BuildError::Consistency(
            "profile22 full replay",
        ));
    }

    let opening_inputs = StateOnlyProfile22OpeningInputs {
        c1: StateOnlyProfile22TreeInput {
            tree: &c1_tree,
            values: &c1_values,
            salts: &c1_salts,
        },
        c2: StateOnlyProfile22TreeInput {
            tree: &c2_tree,
            values: &c2_values,
            salts: &c2_salts,
        },
        later: [
            StateOnlyProfile22TreeInput {
                tree: &later_trees[0],
                values: &later_values[0],
                salts: &later_salts[0],
            },
            StateOnlyProfile22TreeInput {
                tree: &later_trees[1],
                values: &later_values[1],
                salts: &later_salts[1],
            },
            StateOnlyProfile22TreeInput {
                tree: &later_trees[2],
                values: &later_values[2],
                salts: &later_salts[2],
            },
        ],
    };
    let openings = serialize_state_only_profile22_openings(&queries, &opening_inputs)?;
    let roots = StateOnlyProfile22OpeningRoots {
        c1: material.c1_root,
        c2: material.c2_root,
        later: material.later_roots,
    };
    let mut bytes = Vec::with_capacity(prefix_bytes.len() + openings.bytes.len());
    bytes.extend_from_slice(&prefix_bytes);
    bytes.extend_from_slice(&openings.bytes);
    Ok(BuiltAtomicStateOnlyProfile22Proof {
        bytes,
        schedule,
        relation,
        roots,
        openings,
        pow_valid,
    })
}

/// Production bounded unpublished-attempt entry point.  It owns fresh OS
/// entropy generation, performs at most sixteen complete locally mined
/// attempts, evaluates the schedule-only strong Good22 gate, scrubs rejected
/// candidate buffers, and returns only the first good proof or one generic
/// failure.  It emits no rank reason, retry count, partial proof, progress log
/// or checkpoint.  This return value is private worker output: production
/// publication must pass it to `Profile22FixedReleaseController` in
/// `state_only_profile22_release`. Controlled returned errors collapse to
/// `Profile22AttemptsExhausted`; Rust invariant panics remain process faults
/// outside this API boundary.
pub fn build_hiding_atomic_state_only_profile22_first_good_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    nonce_store: &mut DurableStateOnlyMaskNonceStore,
) -> Result<Profile22FirstGoodCandidate, Profile22AttemptsExhausted> {
    let hash = crate::HOST_HASH;
    run_profile22_first_good(
        || StateOnlyAttemptSecrets::generate().map_err(|_| ()),
        |attempt| {
            build_hiding_atomic_state_only_profile22_one_attempt_v3(
                statement,
                witness,
                attempt,
                nonce_store,
                hash,
                StateOnlyPowMode::Mine,
            )
            .map_err(|_| ())
        },
        |candidate| {
            evaluate_profile22_strong_good_schedule(&candidate.schedule)
                .map(|decision| decision.accepted)
                .map_err(|_| ())
        },
        BuiltAtomicStateOnlyProfile22Proof::scrub_rejected,
    )
    .map(Profile22FirstGoodCandidate::new)
}

/// Raw one-attempt construction exists only for deterministic fixtures and
/// internal tests.  Production callers must use the bounded first-good API.
#[cfg(any(test, feature = "insecure-profile22-fixture"))]
pub fn build_hiding_atomic_state_only_profile22_proof_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltAtomicStateOnlyProfile22Proof, StateOnlyProfile22BuildError> {
    build_hiding_atomic_state_only_profile22_one_attempt_v3(
        statement,
        witness,
        attempt,
        nonce_store,
        hash,
        pow_mode,
    )
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_core::state_only_prefix::{
        StateOnlyCandidatePrefix, STATE_ONLY_PREFIX_LEN, STATE_ONLY_PREFIX_OFFSETS,
        STATE_ONLY_PROFILE22_PRIVATE_SHAPE,
    };
    use aspis_core::state_only_profile22_openings::{
        verify_state_only_profile22_openings, PROFILE22_PRIVATE_VALUE_WIDTHS,
    };
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::state_only_profile22::{
        verify_atomic_state_only_profile22_unmined_for_diagnostics_v3,
        verify_atomic_state_only_profile22_v3,
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

    fn rejects(proof: &[u8], statement: &AtomicPaymentStatementV3) {
        assert!(
            verify_atomic_state_only_profile22_unmined_for_diagnostics_v3(
                proof, statement, HOST_HASH, None,
            )
            .is_err()
        );
    }

    #[test]
    fn profile22_private_profile20_roundtrip_and_boundary_teeth() {
        let (statement, witness) = fixture();
        let attempt = StateOnlyAttemptSecrets::deterministic_profile22_fixture(
            [0x22; 32], [0x44; 32], [0x66; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let built = build_hiding_atomic_state_only_profile22_proof_v3(
            &statement,
            &witness,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        assert!(!built.pow_valid);

        let (prefix, suffix) = StateOnlyCandidatePrefix::parse_from_proof(&built.bytes).unwrap();
        assert_eq!(prefix.shape, STATE_ONLY_PROFILE22_PRIVATE_SHAPE);
        assert_eq!(prefix.header.grinding_bits, 38);
        assert_eq!(prefix.shape.batch_grinding_bits, 38);
        assert_eq!(suffix.len(), built.openings.bytes.len());
        let openings = verify_state_only_profile22_openings(
            HOST_HASH,
            &built.roots,
            &built.schedule.queries[..built.schedule.query_count],
            suffix,
        )
        .unwrap();
        assert_eq!(openings.end, suffix.len());
        assert_eq!(
            [
                openings.c1.value_width,
                openings.c2.value_width,
                openings.later[0].value_width,
                openings.later[1].value_width,
                openings.later[2].value_width,
            ],
            PROFILE22_PRIVATE_VALUE_WIDTHS,
        );
        verify_atomic_state_only_profile22_unmined_for_diagnostics_v3(
            &built.bytes,
            &statement,
            HOST_HASH,
            None,
        )
        .unwrap();
        assert!(
            verify_atomic_state_only_profile22_v3(&built.bytes, &statement, HOST_HASH, None,)
                .is_err()
        );

        let mut changed_root = built.bytes.clone();
        changed_root[STATE_ONLY_PREFIX_OFFSETS.c1_root_start] ^= 1;
        rejects(&changed_root, &statement);

        let c1_start = STATE_ONLY_PREFIX_LEN;
        let mut changed_c1_value = built.bytes.clone();
        changed_c1_value[c1_start + 2] ^= 1;
        rejects(&changed_c1_value, &statement);

        let mut changed_c1_salt = built.bytes.clone();
        changed_c1_salt[c1_start + 2 + PROFILE22_PRIVATE_VALUE_WIDTHS[0]] ^= 1;
        rejects(&changed_c1_salt, &statement);

        let c1_frontier = c1_start
            + 2
            + openings.c1.count
                * (PROFILE22_PRIVATE_VALUE_WIDTHS[0]
                    + aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES)
            + 4;
        assert!(built.openings.frontier_nodes[0] > 0);
        let mut changed_c1_frontier = built.bytes.clone();
        changed_c1_frontier[c1_frontier] ^= 1;
        rejects(&changed_c1_frontier, &statement);

        let c2_start = c1_start + built.openings.section_bytes[0];
        let mut changed_c2_value = built.bytes.clone();
        changed_c2_value[c2_start + 2] ^= 1;
        rejects(&changed_c2_value, &statement);

        let mut changed_c2_salt = built.bytes.clone();
        changed_c2_salt[c2_start + 2 + PROFILE22_PRIVATE_VALUE_WIDTHS[1]] ^= 1;
        rejects(&changed_c2_salt, &statement);

        let w1_start = c2_start + built.openings.section_bytes[1];
        let mut changed_w1_value = built.bytes.clone();
        changed_w1_value[w1_start + 2] ^= 1;
        rejects(&changed_w1_value, &statement);

        let w3_start =
            STATE_ONLY_PREFIX_LEN + built.openings.section_bytes[..4].iter().sum::<usize>();
        let mut changed_w3_salt = built.bytes.clone();
        changed_w3_salt[w3_start + 2 + PROFILE22_PRIVATE_VALUE_WIDTHS[4]] ^= 1;
        rejects(&changed_w3_salt, &statement);

        let mut trailing = built.bytes.clone();
        trailing.push(0xa5);
        rejects(&trailing, &statement);

        let sha256 = HOST_HASH(&[&built.bytes])
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        assert_eq!(built.bytes.len(), 56_686);
        assert_eq!(
            sha256,
            "77736f0ea30ae9e2516537213e7dce386c9be69e3c772e5b50f03c57892136f8"
        );
        assert_eq!(
            built.openings.section_bytes,
            [16_134, 11_526, 8_966, 7_430, 5_894]
        );
        assert_eq!(built.openings.frontier_nodes, [280, 280, 232, 184, 136]);
        eprintln!(
            "profile22 bytes={} sha256={} section_bytes={:?} frontier_nodes={:?}",
            built.bytes.len(),
            sha256,
            built.openings.section_bytes,
            built.openings.frontier_nodes,
        );
    }
}
