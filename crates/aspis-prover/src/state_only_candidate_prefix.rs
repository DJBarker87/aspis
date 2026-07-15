//! Sequential state-only builder through the pre-gamma prefix.

use aspis_core::circle_prefix::{
    CandidatePrefixError, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES,
    CANDIDATE_ROUND_COUNT,
};
#[cfg(test)]
use aspis_core::field::CM31;
use aspis_core::field::{M31, QM31};
use aspis_core::params::{FoldPayload, MerkleMode};
use aspis_core::proof::{Header, HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR, VERSION_V4_S2};
use aspis_core::state_only_hiding::{
    begin_state_only_hiding_precommit, StateOnlyHidingContext, StateOnlyHidingScheduleError,
    STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_prefix_schedule_host_v3, run_state_only_prefix_schedule_host,
    state_only_final_grinding_bits, StateOnlyCandidatePrefix, StateOnlyPrefixScheduleResult,
    StateOnlyProfileShape, StateOnlyTranscriptError, STATE_ONLY_FLAGS, STATE_ONLY_LOG_ROWS,
    STATE_ONLY_PREFIX_LEN, STATE_ONLY_PREFIX_OFFSETS, STATE_ONLY_RATE512_SHAPE,
    STATE_ONLY_STATEMENT_VALUE_COUNT, STATE_ONLY_VALUES_PER_POINT,
};
use aspis_core::state_only_query::{STATE_ONLY_C1_LEAF_BYTES, STATE_ONLY_C2_LEAF_BYTES};
use aspis_core::state_only_sumcheck::{begin_state_only_zerocheck, STATE_ONLY_SUMCHECK_BYTES};
use aspis_core::sumcheck::SUMCHECK_COEFFICIENTS;
use aspis_core::transcript::{label, ChallengeSampleExhausted, HashFn, Transcript};
use aspis_statement::state_only_poseidon::{successor_point, xor12_point};
use aspis_statement::{
    atomic_payment_statement_digest_v4,
    atomic_state_only_registry::build_atomic_state_only_copy_helper_v3,
    atomic_state_only_terminal::atomic_state_only_selected_unmasked_terminal_value_compiled_v3,
    build_state_only_copy_helper_v4, multilinear_evaluate, multilinear_evaluate_qm31,
    state_only_copy_helper_sum, state_only_point_openings, state_only_unmasked_terminal_value,
    AtomicPaymentStatementV4, SpendPublic, StateOnlyConstraintError, StateOnlySemanticError,
    StateOnlyTraceFoundation,
};

use crate::circle_candidate::{CircleCandidateError, CircleEncoder};
use crate::state_only_candidate::{
    encode_state_only_c1_columns, encode_state_only_c2_columns, state_only_c1_layer0_leaves,
    state_only_c2_layer0_leaves, state_only_layer0_roots,
};
use crate::state_only_hiding::{
    apply_atomic_state_only_h1_padding_mask_v3, apply_state_only_h1_padding_mask,
    prove_masked_state_only_zerocheck, MaskedStateOnlyZerocheckError, StateOnlyMaskBuildError,
};
use crate::state_only_zerocheck::{StateOnlyZerocheckProveError, StateOnlyZerocheckTrace};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyPrefixMaterial {
    pub shape: StateOnlyProfileShape,
    pub mask_nonce: [u8; 32],
    pub c1_root: [u8; 32],
    pub c2_root: [u8; 32],
    pub initial_mask_claim: QM31,
    pub sumcheck: [u8; STATE_ONLY_SUMCHECK_BYTES],
    pub statement_evaluations: [QM31; STATE_ONLY_STATEMENT_VALUE_COUNT],
    pub later_roots: [[u8; 32]; CANDIDATE_ROUND_COUNT - 1],
    pub ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub relation_sumchecks: [[QM31; SUMCHECK_COEFFICIENTS]; CANDIDATE_ROUND_COUNT],
    pub final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN],
    pub nonce: u64,
    pub fold_nonces: [u64; CANDIDATE_ROUND_COUNT],
    pub batch_nonce: u64,
}

impl StateOnlyPrefixMaterial {
    pub(crate) fn front(
        shape: StateOnlyProfileShape,
        mask_nonce: [u8; 32],
        c1_root: [u8; 32],
        c2_root: [u8; 32],
        initial_mask_claim: QM31,
        zerocheck: &StateOnlyZerocheckTrace,
        statement_evaluations: [QM31; STATE_ONLY_STATEMENT_VALUE_COUNT],
    ) -> Self {
        Self {
            shape,
            mask_nonce,
            c1_root,
            c2_root,
            initial_mask_claim,
            sumcheck: zerocheck.proof,
            statement_evaluations,
            later_roots: [[0u8; 32]; CANDIDATE_ROUND_COUNT - 1],
            ood_values: [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
            relation_sumchecks: [[QM31::ZERO; SUMCHECK_COEFFICIENTS]; CANDIDATE_ROUND_COUNT],
            final_coefficients: [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN],
            nonce: 0,
            fold_nonces: [0; CANDIDATE_ROUND_COUNT],
            batch_nonce: 0,
        }
    }
}

#[derive(Clone)]
pub struct BuiltStateOnlyPrefixFront {
    pub bytes: Vec<u8>,
    pub material: StateOnlyPrefixMaterial,
    pub schedule: StateOnlyPrefixScheduleResult,
    pub trace: StateOnlyTraceFoundation,
    pub h1: Vec<QM31>,
    pub g: Vec<QM31>,
    pub mask_only_c1: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    pub encoded_c1: Vec<Vec<M31>>,
    pub encoded_c2: Vec<Vec<QM31>>,
    pub c1_leaves: Vec<[u8; STATE_ONLY_C1_LEAF_BYTES]>,
    pub c2_leaves: Vec<[u8; STATE_ONLY_C2_LEAF_BYTES]>,
    pub zerocheck: StateOnlyZerocheckTrace,
    pub transcript_after_gamma: Transcript,
    pub batch_pow_valid: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyPowMode {
    UnminedZero,
    Mine,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StateOnlyPrefixBuildError {
    Candidate(CircleCandidateError),
    Semantic(StateOnlySemanticError),
    Constraint(StateOnlyConstraintError),
    Zerocheck(StateOnlyZerocheckProveError<StateOnlyConstraintError>),
    Hiding(StateOnlyHidingScheduleError),
    Mask(StateOnlyMaskBuildError),
    MaskedZerocheck(MaskedStateOnlyZerocheckError<StateOnlyConstraintError>),
    Transcript(StateOnlyTranscriptError),
    Prefix(CandidatePrefixError),
    ChallengeSampleExhausted,
    Shape,
}

impl From<CircleCandidateError> for StateOnlyPrefixBuildError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Candidate(error)
    }
}
impl From<StateOnlySemanticError> for StateOnlyPrefixBuildError {
    fn from(error: StateOnlySemanticError) -> Self {
        Self::Semantic(error)
    }
}
impl From<StateOnlyConstraintError> for StateOnlyPrefixBuildError {
    fn from(error: StateOnlyConstraintError) -> Self {
        Self::Constraint(error)
    }
}
impl From<StateOnlyZerocheckProveError<StateOnlyConstraintError>> for StateOnlyPrefixBuildError {
    fn from(error: StateOnlyZerocheckProveError<StateOnlyConstraintError>) -> Self {
        Self::Zerocheck(error)
    }
}
impl From<StateOnlyHidingScheduleError> for StateOnlyPrefixBuildError {
    fn from(error: StateOnlyHidingScheduleError) -> Self {
        Self::Hiding(error)
    }
}
impl From<StateOnlyMaskBuildError> for StateOnlyPrefixBuildError {
    fn from(error: StateOnlyMaskBuildError) -> Self {
        Self::Mask(error)
    }
}
impl From<MaskedStateOnlyZerocheckError<StateOnlyConstraintError>> for StateOnlyPrefixBuildError {
    fn from(error: MaskedStateOnlyZerocheckError<StateOnlyConstraintError>) -> Self {
        Self::MaskedZerocheck(error)
    }
}
impl From<StateOnlyTranscriptError> for StateOnlyPrefixBuildError {
    fn from(error: StateOnlyTranscriptError) -> Self {
        Self::Transcript(error)
    }
}
impl From<CandidatePrefixError> for StateOnlyPrefixBuildError {
    fn from(error: CandidatePrefixError) -> Self {
        Self::Prefix(error)
    }
}
impl From<ChallengeSampleExhausted> for StateOnlyPrefixBuildError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

pub fn state_only_header(shape: StateOnlyProfileShape) -> Header {
    Header {
        version: VERSION_V4_S2,
        profile_id: shape.profile_id,
        log_rows: STATE_ONLY_LOG_ROWS,
        log_blowup: shape.log_blowup,
        query_count: shape.query_count,
        grinding_bits: state_only_final_grinding_bits(shape),
        fold_payload: FoldPayload::RawFibers as u8,
        merkle_mode: MerkleMode::Radix4MinimalSubtree as u8,
        num_rounds: CANDIDATE_ROUND_COUNT as u32,
        final_poly_log_len: 2,
        flags: STATE_ONLY_FLAGS,
    }
}

pub fn serialize_state_only_prefix(material: &StateOnlyPrefixMaterial) -> Vec<u8> {
    let mut bytes = vec![0u8; STATE_ONLY_PREFIX_LEN];
    state_only_header(material.shape).write(&mut bytes[..HEADER_LEN]);
    bytes[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start..][..32].copy_from_slice(&material.mask_nonce);
    bytes[STATE_ONLY_PREFIX_OFFSETS.c1_root_start..][..32].copy_from_slice(&material.c1_root);
    bytes[STATE_ONLY_PREFIX_OFFSETS.c2_root_start..][..32].copy_from_slice(&material.c2_root);
    material
        .initial_mask_claim
        .write_le_bytes(&mut bytes[STATE_ONLY_PREFIX_OFFSETS.initial_mask_claim_start..][..16]);
    bytes[STATE_ONLY_PREFIX_OFFSETS.sumcheck_start..][..STATE_ONLY_SUMCHECK_BYTES]
        .copy_from_slice(&material.sumcheck);
    for (index, value) in material.statement_evaluations.iter().enumerate() {
        value.write_le_bytes(
            &mut bytes[STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start + index * 16..][..16],
        );
    }
    for round in 0..CANDIDATE_ROUND_COUNT {
        let offsets = STATE_ONLY_PREFIX_OFFSETS.rounds[round];
        if let Some(start) = offsets.root_start {
            bytes[start..start + 32].copy_from_slice(&material.later_roots[round - 1]);
        }
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            material.ood_values[round][sample]
                .write_le_bytes(&mut bytes[offsets.ood_values_start + sample * 16..][..16]);
        }
        for coefficient in 0..SUMCHECK_COEFFICIENTS {
            material.relation_sumchecks[round][coefficient]
                .write_le_bytes(&mut bytes[offsets.sumcheck_start + coefficient * 16..][..16]);
        }
    }
    for (coefficient, value) in material.final_coefficients.iter().enumerate() {
        value.write_le_bytes(
            &mut bytes[STATE_ONLY_PREFIX_OFFSETS.final_polynomial_start + coefficient * 16..][..16],
        );
    }
    bytes[STATE_ONLY_PREFIX_OFFSETS.nonce_start..][..CANDIDATE_NONCE_LEN]
        .copy_from_slice(&material.nonce.to_le_bytes());
    for (round, nonce) in material.fold_nonces.iter().enumerate() {
        let start = STATE_ONLY_PREFIX_OFFSETS.fold_nonces_start + round * CANDIDATE_NONCE_LEN;
        bytes[start..start + CANDIDATE_NONCE_LEN].copy_from_slice(&nonce.to_le_bytes());
    }
    bytes[STATE_ONLY_PREFIX_OFFSETS.batch_nonce_start..][..CANDIDATE_NONCE_LEN]
        .copy_from_slice(&material.batch_nonce.to_le_bytes());
    bytes
}

pub(crate) fn statement_evaluations(
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    h1: &[QM31],
    g: &[QM31],
    z: &[QM31; 10],
) -> Result<[QM31; STATE_ONLY_STATEMENT_VALUE_COUNT], StateOnlyPrefixBuildError> {
    let points = [*z, successor_point(z), xor12_point(z)];
    let mut output = [QM31::ZERO; STATE_ONLY_STATEMENT_VALUE_COUNT];
    for (point_index, point) in points.iter().enumerate() {
        let base = point_index * STATE_ONLY_VALUES_PER_POINT;
        for column in 0..16 {
            output[base + column] = multilinear_evaluate(&trace.c1[column], point)
                .ok_or(StateOnlyPrefixBuildError::Shape)?;
        }
        for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
            output[base + 16 + column] = multilinear_evaluate(&mask_only_c1[column], point)
                .ok_or(StateOnlyPrefixBuildError::Shape)?;
        }
        output[base + 26] =
            multilinear_evaluate_qm31(h1, point).ok_or(StateOnlyPrefixBuildError::Shape)?;
        output[base + 27] =
            multilinear_evaluate_qm31(g, point).ok_or(StateOnlyPrefixBuildError::Shape)?;
    }
    Ok(output)
}

#[cfg(test)]
fn statement_evaluations_reference(
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    h1: &[QM31],
    g: &[QM31],
    z: &[QM31; 10],
) -> Result<[QM31; STATE_ONLY_STATEMENT_VALUE_COUNT], StateOnlyPrefixBuildError> {
    fn dense_m31(table: &[M31], point: &[QM31; 10]) -> Option<QM31> {
        if table.len() != 1024 {
            return None;
        }
        let mut layer = table
            .iter()
            .copied()
            .map(|value| QM31::from_cm31(CM31::from_m31(value)))
            .collect::<Vec<_>>();
        for coordinate in point.iter().rev() {
            for index in 0..layer.len() / 2 {
                let left = layer[2 * index];
                layer[index] = left.add(coordinate.mul(layer[2 * index + 1].sub(left)));
            }
            layer.truncate(layer.len() / 2);
        }
        Some(layer[0])
    }

    let points = [*z, successor_point(z), xor12_point(z)];
    let mut output = [QM31::ZERO; STATE_ONLY_STATEMENT_VALUE_COUNT];
    for (point_index, point) in points.iter().enumerate() {
        let openings = state_only_point_openings(trace, h1, g, point)?;
        let base = point_index * STATE_ONLY_VALUES_PER_POINT;
        output[base..base + 16].copy_from_slice(&openings.semantic.c1.z);
        for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
            output[base + 16 + column] =
                dense_m31(&mask_only_c1[column], point).ok_or(StateOnlyPrefixBuildError::Shape)?;
        }
        output[base + 26] = openings.semantic.h1_z;
        output[base + 27] = openings.g_z;
    }
    Ok(output)
}

pub fn build_state_only_prefix_front(
    public: &SpendPublic,
    trace: &StateOnlyTraceFoundation,
    g: &[QM31],
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    shape: StateOnlyProfileShape,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyPrefixFront, StateOnlyPrefixBuildError> {
    let mask_only_c1 = core::array::from_fn(|_| vec![M31::ZERO; 1024]);
    build_state_only_prefix_front_selected(
        public,
        trace,
        &mask_only_c1,
        g,
        statement_digest,
        mask_nonce,
        shape,
        hash,
        pow_mode,
    )
}

pub fn build_state_only_prefix_front_selected(
    public: &SpendPublic,
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    shape: StateOnlyProfileShape,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyPrefixFront, StateOnlyPrefixBuildError> {
    let h1_padding = vec![QM31::ZERO; 1024];
    build_state_only_prefix_front_selected_with_h1_padding(
        public,
        trace,
        mask_only_c1,
        g,
        &h1_padding,
        statement_digest,
        mask_nonce,
        shape,
        hash,
        pow_mode,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn build_state_only_prefix_front_selected_with_h1_padding(
    public: &SpendPublic,
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    h1_padding: &[QM31],
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    shape: StateOnlyProfileShape,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyPrefixFront, StateOnlyPrefixBuildError> {
    build_state_only_prefix_front_selected_with_h1_padding_mode(
        StateOnlyFrontMode::Base(public),
        trace,
        mask_only_c1,
        g,
        h1_padding,
        statement_digest,
        mask_nonce,
        shape,
        hash,
        pow_mode,
    )
}

pub fn build_atomic_state_only_prefix_front_selected_with_h1_padding_v3(
    statement: &AtomicPaymentStatementV4,
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    h1_padding: &[QM31],
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    shape: StateOnlyProfileShape,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyPrefixFront, StateOnlyPrefixBuildError> {
    if shape != STATE_ONLY_RATE512_SHAPE
        || atomic_payment_statement_digest_v4(statement, hash)
            .map_err(|_| StateOnlyPrefixBuildError::Shape)?
            != statement_digest
    {
        return Err(StateOnlyPrefixBuildError::Shape);
    }
    build_state_only_prefix_front_selected_with_h1_padding_mode(
        StateOnlyFrontMode::Atomic(statement),
        trace,
        mask_only_c1,
        g,
        h1_padding,
        statement_digest,
        mask_nonce,
        shape,
        hash,
        pow_mode,
    )
}

#[derive(Clone, Copy)]
enum StateOnlyFrontMode<'a> {
    Base(&'a SpendPublic),
    Atomic(&'a AtomicPaymentStatementV4),
}

#[allow(clippy::too_many_arguments)]
fn build_state_only_prefix_front_selected_with_h1_padding_mode(
    mode: StateOnlyFrontMode<'_>,
    trace: &StateOnlyTraceFoundation,
    mask_only_c1: &[Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    g: &[QM31],
    h1_padding: &[QM31],
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    shape: StateOnlyProfileShape,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
) -> Result<BuiltStateOnlyPrefixFront, StateOnlyPrefixBuildError> {
    if trace.c1.len() != 16
        || trace.c1.iter().any(|column| column.len() != 1024)
        || g.len() != 1024
        || h1_padding.len() != 1024
        || mask_only_c1.iter().any(|column| column.len() != 1024)
    {
        return Err(StateOnlyPrefixBuildError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + shape.log_blowup;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let selected_c1 = trace
        .c1
        .iter()
        .cloned()
        .chain(mask_only_c1.iter().cloned())
        .collect::<Vec<_>>();
    let encoded_c1 = encode_state_only_c1_columns(&encoder, &selected_c1)?;
    let c1_leaves = state_only_c1_layer0_leaves(&encoded_c1, encoder.codeword_len())?;
    let mut header_bytes = [0u8; HEADER_LEN];
    state_only_header(shape).write(&mut header_bytes);
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, &statement_digest);
    let precommit_binding = begin_state_only_hiding_precommit(
        &mut transcript,
        match mode {
            StateOnlyFrontMode::Base(_) => {
                StateOnlyHidingContext::pinned(statement_digest, mask_nonce)
            }
            StateOnlyFrontMode::Atomic(_) => {
                StateOnlyHidingContext::atomic_v3(statement_digest, mask_nonce)
            }
        },
    )?;
    let (_, temporary_c2_root) = state_only_layer0_roots(
        &c1_leaves,
        &state_only_c2_layer0_leaves(
            &encode_state_only_c2_columns(&encoder, &[vec![QM31::ZERO; 1024], g.to_vec()])?,
            encoder.codeword_len(),
        )?,
        hash,
    )?;
    // C1 and C2 use separate roots; the temporary C2 root is deliberately
    // discarded after obtaining the C1 root without another root helper.
    let (c1_root, _) = state_only_layer0_roots(
        &c1_leaves,
        &state_only_c2_layer0_leaves(
            &encode_state_only_c2_columns(&encoder, &[vec![QM31::ZERO; 1024], g.to_vec()])?,
            encoder.codeword_len(),
        )?,
        hash,
    )?;
    let _ = temporary_c2_root;
    let mut c1_record = [0u8; 33];
    c1_record[1..].copy_from_slice(&c1_root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &c1_record);
    let lambda = transcript.challenge_qm31()?;
    let chi = transcript.challenge_qm31()?;
    let mut h1 = match mode {
        StateOnlyFrontMode::Base(_) => build_state_only_copy_helper_v4(trace, lambda, chi)?,
        StateOnlyFrontMode::Atomic(_) => build_atomic_state_only_copy_helper_v3(trace, lambda, chi)
            .map_err(|_| StateOnlyPrefixBuildError::Shape)?,
    };
    match mode {
        StateOnlyFrontMode::Base(_) => apply_state_only_h1_padding_mask(&mut h1, h1_padding)?,
        StateOnlyFrontMode::Atomic(_) => {
            apply_atomic_state_only_h1_padding_mask_v3(&mut h1, h1_padding)?
        }
    }
    if state_only_copy_helper_sum(&h1) != Some(QM31::ZERO) {
        return Err(StateOnlyPrefixBuildError::Shape);
    }
    let c2_messages = [h1.clone(), g.to_vec()];
    let encoded_c2 = encode_state_only_c2_columns(&encoder, &c2_messages)?;
    let c2_leaves = state_only_c2_layer0_leaves(&encoded_c2, encoder.codeword_len())?;
    let (_, c2_root) = state_only_layer0_roots(&c1_leaves, &c2_leaves, hash)?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2_root);
    let batching = begin_state_only_zerocheck(&mut transcript)?;
    let masked = prove_masked_state_only_zerocheck(
        &mut transcript,
        precommit_binding,
        trace,
        mask_only_c1,
        g,
        |point| match mode {
            StateOnlyFrontMode::Base(public) => {
                let openings = state_only_point_openings(trace, &h1, g, point)?;
                state_only_unmasked_terminal_value(public, &openings, point, &batching, lambda, chi)
            }
            StateOnlyFrontMode::Atomic(statement) => {
                let claims = statement_evaluations(trace, mask_only_c1, &h1, g, point)
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
            }
        },
    )?;
    let initial_mask_claim = masked.initial_mask_claim;
    let eta = masked.eta;
    let zerocheck = masked.sumcheck;
    let evaluations = statement_evaluations(trace, mask_only_c1, &h1, g, &zerocheck.challenges)?;
    let mut material = StateOnlyPrefixMaterial::front(
        shape,
        mask_nonce,
        c1_root,
        c2_root,
        initial_mask_claim,
        &zerocheck,
        evaluations,
    );
    let mut bytes = serialize_state_only_prefix(&material);
    transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &{
        let points = [
            zerocheck.challenges,
            successor_point(&zerocheck.challenges),
            xor12_point(&zerocheck.challenges),
        ];
        let mut encoded = [0u8; 480];
        for (point, coordinates) in points.iter().enumerate() {
            for (coordinate, value) in coordinates.iter().enumerate() {
                value.write_le_bytes(&mut encoded[(point * 10 + coordinate) * 16..][..16]);
            }
        }
        encoded
    });
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        &bytes[STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start
            ..STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start
                + STATE_ONLY_STATEMENT_VALUE_COUNT * 16],
    );
    material.batch_nonce = match pow_mode {
        StateOnlyPowMode::UnminedZero => 0,
        StateOnlyPowMode::Mine => {
            crate::find_grinding_nonce(&transcript, shape.batch_grinding_bits)
        }
    };
    let batch_pow_valid = transcript.grinding_ok(material.batch_nonce, shape.batch_grinding_bits);
    transcript.absorb(
        label::M31_PAYMENT_BATCH_POW_NONCE,
        &material.batch_nonce.to_le_bytes(),
    );
    let _gamma = transcript.challenge_qm31()?;
    let _point_scale = transcript.challenge_qm31()?;
    bytes = serialize_state_only_prefix(&material);
    let parsed = StateOnlyCandidatePrefix::parse_exact(&bytes)?;
    let schedule = match mode {
        StateOnlyFrontMode::Base(_) => {
            run_state_only_prefix_schedule_host(hash, &parsed, &statement_digest)?
        }
        StateOnlyFrontMode::Atomic(_) => {
            run_atomic_state_only_prefix_schedule_host_v3(hash, &parsed, &statement_digest)?
        }
    };
    if schedule.lambda != lambda
        || schedule.chi != chi
        || schedule.batching != batching
        || schedule.eta != eta
        || schedule.z != zerocheck.challenges
        || schedule.masked_terminal_claim != zerocheck.terminal_claim
    {
        return Err(StateOnlyPrefixBuildError::Shape);
    }
    Ok(BuiltStateOnlyPrefixFront {
        bytes,
        material,
        schedule,
        trace: trace.clone(),
        h1,
        g: g.to_vec(),
        mask_only_c1: mask_only_c1.clone(),
        encoded_c1,
        encoded_c2,
        c1_leaves,
        c2_leaves,
        zerocheck,
        transcript_after_gamma: transcript,
        batch_pow_valid,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 17 + 1), M31(seed * 19 + 3)),
            c1: CM31::new(M31(seed * 23 + 5), M31(seed * 29 + 7)),
        }
    }

    #[test]
    fn direct_statement_evaluations_match_the_previous_nested_opening_path() {
        let trace = StateOnlyTraceFoundation {
            c1: core::array::from_fn(|column| {
                (0..1024)
                    .map(|row| M31((row * 131 + column * 17 + 1) as u32))
                    .collect()
            }),
        };
        let mask_only_c1 = core::array::from_fn(|column| {
            (0..1024)
                .map(|row| M31((row * 43 + column * 211 + 9) as u32))
                .collect()
        });
        let h1 = (0..1024)
            .map(|row| q(row as u32 + 1_000))
            .collect::<Vec<_>>();
        let g = (0..1024)
            .map(|row| q(row as u32 + 3_000))
            .collect::<Vec<_>>();

        let points = [
            core::array::from_fn(|coordinate| q(coordinate as u32 + 11)),
            core::array::from_fn(|coordinate| {
                if coordinate == 0 {
                    q(101)
                } else if coordinate & 1 == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            }),
            core::array::from_fn(|coordinate| {
                if coordinate < 5 {
                    q(coordinate as u32 + 211)
                } else if coordinate & 1 == 0 {
                    QM31::ONE
                } else {
                    QM31::ZERO
                }
            }),
            core::array::from_fn(|coordinate| {
                if coordinate & 1 == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            }),
        ];

        for point in points {
            assert_eq!(
                statement_evaluations(&trace, &mask_only_c1, &h1, &g, &point).unwrap(),
                statement_evaluations_reference(&trace, &mask_only_c1, &h1, &g, &point).unwrap(),
            );
        }
    }
}
