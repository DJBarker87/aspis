//! Quarantined atomic spend builder.
//!
//! This is an append-only, nondefault integration of one zero-factor QM31 D
//! lane behind H26/G27. Its production builder retains one common attempt,
//! evaluates three post-final selector schedules, and retries all-bad attempts
//! behind an opaque bounded API. Fixed-boundary release remains a separate
//! integration step. Deterministic/raw construction is available only to
//! tests and the explicitly insecure spend fixture feature.

use aspis_core::circle_line_merkle::CIRCLE_LINE_TAGS;
use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::circle_prefix::{
    CandidatePrefixError, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES,
    CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::QM31;
use aspis_core::proof::{HEADER_LEN, M31_CIRCLE_BASIS_DISCRIMINATOR};
use aspis_core::state_only_hiding::{begin_state_only_hiding_precommit, StateOnlyHidingContext};
use aspis_core::state_only_prefix::{
    run_atomic_state_only_spend_prefix_schedule_host_v3,
    run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlySpendPrefix, StateOnlyTranscriptError, StateOnlyTranscriptScheduleResult,
    STATE_ONLY_LOG_ROWS, STATE_ONLY_SPEND_D_CLAIMS_LEN, STATE_ONLY_SPEND_FOLD_GRINDING_BITS,
    STATE_ONLY_SPEND_GRINDING_BITS, STATE_ONLY_SPEND_PREFIX_LEN, STATE_ONLY_SPEND_QUERY_COUNT,
    STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE,
};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_spend_openings::StateOnlySpendOpeningRoots;
use aspis_core::state_only_spend_relation::prepare_state_only_spend_relation;
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
use zeroize::{Zeroize, Zeroizing};

use crate::circle_candidate::CandidatePrefixBuildError;
use crate::circle_candidate::{
    combined_layer_leaves, fold_candidate_codeword_round_for_domain_log, CircleCandidateError,
    CircleEncoder,
};
use crate::pow::UnpublishedPowError;
use crate::state_only_candidate::{encode_state_only_c1_columns, state_only_c1_layer0_leaves};
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
use crate::state_only_good_spend::{
    evaluate_spend_candidate_schedules_host, run_spend_first_good, SpendAttemptBuild,
    SpendAttemptsExhausted,
};
use crate::state_only_hiding::{
    apply_atomic_state_only_h1_padding_mask_v3, apply_atomic_state_only_mask_material_v3,
    prove_masked_state_only_zerocheck, StateOnlyMaskBuildError, StateOnlyMaskNonceStore,
};
use crate::state_only_private_openings::{
    build_state_only_private_merkle_tree, StateOnlyPrivateOpeningBuildError,
};
use crate::state_only_spend_candidate::{
    encode_state_only_spend_c2_columns, gamma_combine_state_only_spend_codewords,
    gamma_combine_state_only_spend_messages, state_only_spend_c2_layer0_leaves,
};
use crate::state_only_spend_openings::{
    serialize_state_only_spend_openings, BuiltStateOnlySpendOpenings,
    StateOnlySpendOpeningBuildError, StateOnlySpendOpeningInputs, StateOnlySpendTreeInput,
};

pub const SPEND_C1_VALUE_WIDTH: usize = 416;
pub const SPEND_C2_VALUE_WIDTH: usize = 192;

fn volatile_clear<T: Copy>(values: &mut [T], zero: T) {
    for value in values {
        // SAFETY: `value` is a valid, uniquely borrowed cell. Volatile stores
        // keep attempt-secret clearing from being removed as a dead write.
        unsafe { core::ptr::write_volatile(value, zero) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Attempt-local witness/mask material that must not survive either a
/// rejected branch or a successful serialization.  Keeping the allocations
/// under one drop guard covers every `?` after the durable nonce reservation.
#[derive(Default)]
struct SpendAttemptScratch {
    selected_c1: Vec<Vec<aspis_core::field::M31>>,
    encoded_c1: Vec<Vec<aspis_core::field::M31>>,
    c1_leaves: Vec<[u8; SPEND_C1_VALUE_WIDTH]>,
    c1_values: Vec<u8>,
    c1_salts: Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>,
    h1: Vec<QM31>,
    d: Vec<QM31>,
    c2_messages: Vec<Vec<QM31>>,
    encoded_c2: Vec<Vec<QM31>>,
    c2_leaves: Vec<[u8; SPEND_C2_VALUE_WIDTH]>,
    c2_values: Vec<u8>,
    c2_salts: Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>,
    combined_codeword: Vec<QM31>,
    later_leaves: Vec<Vec<[u8; 64]>>,
    later_values: Vec<Vec<u8>>,
    later_salts: Vec<Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>>,
    prefix_bytes: Vec<u8>,
}

impl Drop for SpendAttemptScratch {
    fn drop(&mut self) {
        for column in &mut self.selected_c1 {
            volatile_clear(column, aspis_core::field::M31::ZERO);
        }
        for column in &mut self.encoded_c1 {
            volatile_clear(column, aspis_core::field::M31::ZERO);
        }
        self.c1_leaves.zeroize();
        self.c1_values.zeroize();
        self.c1_salts.zeroize();
        volatile_clear(&mut self.h1, QM31::ZERO);
        volatile_clear(&mut self.d, QM31::ZERO);
        for column in &mut self.c2_messages {
            volatile_clear(column, QM31::ZERO);
        }
        for column in &mut self.encoded_c2 {
            volatile_clear(column, QM31::ZERO);
        }
        self.c2_leaves.zeroize();
        self.c2_values.zeroize();
        self.c2_salts.zeroize();
        volatile_clear(&mut self.combined_codeword, QM31::ZERO);
        for leaves in &mut self.later_leaves {
            leaves.zeroize();
        }
        for values in &mut self.later_values {
            values.zeroize();
        }
        for salts in &mut self.later_salts {
            salts.zeroize();
        }
        self.prefix_bytes.zeroize();
    }
}

#[derive(Debug)]
pub enum StateOnlySpendBuildError {
    AtomicTrace(AtomicStateOnlyTraceV3Error),
    AtomicStatement(AtomicStatementError),
    Front(StateOnlyPrefixBuildError),
    Candidate(CandidatePrefixBuildError),
    Circle(CircleCandidateError),
    Mask(StateOnlyMaskBuildError),
    Private(StateOnlyPrivateOpeningBuildError),
    Openings(StateOnlySpendOpeningBuildError),
    Prefix(CandidatePrefixError),
    Transcript(StateOnlyTranscriptError),
    Pow(UnpublishedPowError),
    NoGoodQuerySchedule,
    GoodGate,
    Consistency(&'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SpendGoodSelectionError;

macro_rules! from_error {
    ($source:ty, $variant:ident) => {
        impl From<$source> for StateOnlySpendBuildError {
            fn from(value: $source) -> Self {
                Self::$variant(value)
            }
        }
    };
}
from_error!(AtomicStateOnlyTraceV3Error, AtomicTrace);
from_error!(AtomicStatementError, AtomicStatement);
from_error!(StateOnlyPrefixBuildError, Front);
from_error!(CandidatePrefixBuildError, Candidate);
from_error!(CircleCandidateError, Circle);
from_error!(StateOnlyMaskBuildError, Mask);
from_error!(StateOnlyPrivateOpeningBuildError, Private);
from_error!(StateOnlySpendOpeningBuildError, Openings);
from_error!(CandidatePrefixError, Prefix);
from_error!(StateOnlyTranscriptError, Transcript);
from_error!(UnpublishedPowError, Pow);

pub struct BuiltAtomicStateOnlySpendProof {
    pub bytes: Vec<u8>,
    pub schedule: StateOnlyTranscriptScheduleResult,
    pub relation: StateOnlyCircleRelationTrace,
    pub roots: StateOnlySpendOpeningRoots,
    pub openings: BuiltStateOnlySpendOpenings,
    pub d: Vec<QM31>,
    pub d_claims: [QM31; 3],
    pub query_selector: u8,
    pub pow_valid: bool,
}

impl BuiltAtomicStateOnlySpendProof {
    /// Scrub every candidate-owned buffer before a rejected unpublished
    /// attempt is dropped.  Spend has the same private transcript view
    /// as profile 22 plus the full D word and its three claims.
    pub(crate) fn scrub_rejected(&mut self) {
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
        volatile_clear(&mut self.relation.point_claims, QM31::ZERO);
        for values in &mut self.relation.ood_values {
            volatile_clear(values, QM31::ZERO);
        }
        volatile_clear(&mut self.relation.boundary_claims, QM31::ZERO);
        for polynomial in &mut self.relation.sumchecks {
            volatile_clear(polynomial, QM31::ZERO);
        }
        volatile_clear(&mut self.relation.running_claims, QM31::ZERO);
        volatile_clear(&mut self.relation.final_coefficients, QM31::ZERO);
        volatile_clear(
            core::slice::from_mut(&mut self.relation.terminal_claim),
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.lambda),
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.chi),
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.batching.theta),
            QM31::ZERO,
        );
        volatile_clear(
            &mut self.schedule.prefix.batching.zerocheck_point,
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.batching.mu),
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.initial_mask_claim),
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.eta),
            QM31::ZERO,
        );
        volatile_clear(&mut self.schedule.prefix.z, QM31::ZERO);
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.masked_terminal_claim),
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.gamma),
            QM31::ZERO,
        );
        volatile_clear(
            core::slice::from_mut(&mut self.schedule.prefix.point_scale),
            QM31::ZERO,
        );
        self.schedule.prefix.state_after_gamma.zeroize();
        for point in &mut self.schedule.circle_ood_points {
            volatile_clear(core::slice::from_mut(&mut point.x), QM31::ZERO);
            volatile_clear(core::slice::from_mut(&mut point.y), QM31::ZERO);
        }
        for points in &mut self.schedule.line_ood_points {
            volatile_clear(points, QM31::ZERO);
        }
        for mixes in &mut self.schedule.mu {
            volatile_clear(mixes, QM31::ZERO);
        }
        volatile_clear(&mut self.schedule.alpha, QM31::ZERO);
        self.schedule.state_before_grinding.zeroize();
        self.schedule.queries.zeroize();
        self.schedule.query_count = 0;
        self.schedule.state_after_queries.zeroize();
        volatile_clear(&mut self.d, QM31::ZERO);
        volatile_clear(&mut self.d_claims, QM31::ZERO);
        self.query_selector = 0;
        self.pow_valid = false;
    }

    pub(crate) fn into_released_bytes(mut self) -> Vec<u8> {
        let bytes = core::mem::take(&mut self.bytes);
        self.scrub_rejected();
        bytes
    }
}

/// Opaque output of the production GoodSpend worker. Construction is
/// crate-private so a raw fixture or caller-selected selector cannot be
/// laundered into the fixed-release path.
enum SpendFirstGoodCandidateInner {
    Production(BuiltAtomicStateOnlySpendProof),
    #[cfg(test)]
    SyntheticReleaseTest {
        bytes: Vec<u8>,
        ready: bool,
        scrub_count: std::rc::Rc<std::cell::Cell<usize>>,
    },
}

pub struct SpendFirstGoodCandidate {
    candidate: Option<SpendFirstGoodCandidateInner>,
}

impl SpendFirstGoodCandidate {
    pub(crate) fn new(candidate: BuiltAtomicStateOnlySpendProof) -> Self {
        Self {
            candidate: Some(SpendFirstGoodCandidateInner::Production(candidate)),
        }
    }

    #[cfg(test)]
    pub(crate) fn synthetic_release_test(
        bytes: Vec<u8>,
        ready: bool,
        scrub_count: std::rc::Rc<std::cell::Cell<usize>>,
    ) -> Self {
        Self {
            candidate: Some(SpendFirstGoodCandidateInner::SyntheticReleaseTest {
                bytes,
                ready,
                scrub_count,
            }),
        }
    }

    pub(crate) fn production_ready(&self) -> bool {
        match self.candidate.as_ref() {
            Some(SpendFirstGoodCandidateInner::Production(candidate)) => candidate.pow_valid,
            #[cfg(test)]
            Some(SpendFirstGoodCandidateInner::SyntheticReleaseTest { ready, .. }) => *ready,
            None => false,
        }
    }

    pub(crate) fn scrub(&mut self) {
        match self.candidate.take() {
            Some(SpendFirstGoodCandidateInner::Production(mut candidate)) => {
                candidate.scrub_rejected();
            }
            #[cfg(test)]
            Some(SpendFirstGoodCandidateInner::SyntheticReleaseTest {
                mut bytes,
                scrub_count,
                ..
            }) => {
                bytes.zeroize();
                scrub_count.set(scrub_count.get() + 1);
            }
            None => {}
        }
    }

    pub(crate) fn into_released_bytes(mut self) -> Vec<u8> {
        match self
            .candidate
            .take()
            .expect("first-good candidate consumed once")
        {
            SpendFirstGoodCandidateInner::Production(candidate) => candidate.into_released_bytes(),
            #[cfg(test)]
            SpendFirstGoodCandidateInner::SyntheticReleaseTest {
                bytes, scrub_count, ..
            } => {
                scrub_count.set(scrub_count.get() + 1);
                bytes
            }
        }
    }
}

impl Drop for SpendFirstGoodCandidate {
    fn drop(&mut self) {
        self.scrub();
    }
}

fn pow_nonce(
    transcript: &Transcript,
    bits: u8,
    mode: StateOnlyPowMode,
) -> Result<u64, StateOnlySpendBuildError> {
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
) -> Result<Vec<[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]>, StateOnlySpendBuildError> {
    let mut salts = Vec::with_capacity(count);
    for index in 0..count {
        match reserved.derive_spend_leaf_salt(hash, context, tag, index as u32) {
            Ok(salt) => salts.push(salt),
            Err(error) => {
                salts.zeroize();
                return Err(StateOnlySpendBuildError::from(error));
            }
        }
    }
    Ok(salts)
}

fn evaluate_qm31_table(table: &[QM31], point: &[QM31; 10]) -> Option<QM31> {
    if table.len() != 1 << 10 {
        return None;
    }
    let mut layer = table.to_vec();
    for coordinate in point.iter().rev() {
        for index in 0..layer.len() / 2 {
            let left = layer[2 * index];
            layer[index] = left.add(coordinate.mul(layer[2 * index + 1].sub(left)));
        }
        layer.truncate(layer.len() / 2);
    }
    Some(layer[0])
}

fn encode_d_claims(d: &[QM31], z: &[QM31; 10]) -> Option<([QM31; 3], [u8; 48])> {
    let points = [*z, successor_point(z), xor12_point(z)];
    let claims = core::array::from_fn(|point| evaluate_qm31_table(d, &points[point]).unwrap());
    let mut bytes = [0u8; 48];
    for (point, value) in claims.iter().enumerate() {
        value.write_le_bytes(&mut bytes[point * 16..][..16]);
    }
    Some((claims, bytes))
}

fn serialize_spend_prefix(
    material: &StateOnlyPrefixMaterial,
    d_claims: &[u8; STATE_ONLY_SPEND_D_CLAIMS_LEN],
    query_selector: u8,
) -> Result<Vec<u8>, StateOnlySpendBuildError> {
    if material.shape != STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE || query_selector >= 3 {
        return Err(StateOnlySpendBuildError::Consistency("spend prefix shape"));
    }
    let mut bytes = serialize_state_only_prefix(material);
    bytes.extend_from_slice(d_claims);
    bytes.push(query_selector);
    if bytes.len() != STATE_ONLY_SPEND_PREFIX_LEN {
        return Err(StateOnlySpendBuildError::Consistency("spend prefix length"));
    }
    Ok(bytes)
}

#[allow(clippy::too_many_lines)]
fn build_one_attempt<Select>(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
    select_query_schedule: Select,
) -> Result<BuiltAtomicStateOnlySpendProof, StateOnlySpendBuildError>
where
    Select: FnOnce(
        &[StateOnlyTranscriptScheduleResult; 3],
    ) -> Result<Option<usize>, SpendGoodSelectionError>,
{
    let statement_digest = atomic_payment_statement_digest_v3(statement, hash)?;
    let mask_nonce = attempt.mask_nonce();
    let context = StateOnlyHidingContext::atomic_spend_v3(statement_digest, mask_nonce);
    let mut header_bytes = [0u8; HEADER_LEN];
    state_only_header(STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE).write(&mut header_bytes);
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
    let mut scratch = SpendAttemptScratch::default();
    scratch.d = reserved.derive_spend_zero_factor_d(hash, context)?;
    let mut atomic = build_atomic_state_only_trace_v3(statement, witness)?;
    let mut trace = core::mem::take(&mut atomic.trace);
    let applied = apply_atomic_state_only_mask_material_v3(&mut trace, mask_material)?;

    let domain_log = STATE_ONLY_LOG_ROWS + STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE.log_blowup;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    scratch.selected_c1 = trace
        .c1
        .iter()
        .cloned()
        .chain(applied.mask_only_c1.iter().cloned())
        .collect::<Vec<_>>();
    scratch.encoded_c1 = encode_state_only_c1_columns(&encoder, &scratch.selected_c1)?;
    scratch.c1_leaves = state_only_c1_layer0_leaves(&scratch.encoded_c1, encoder.codeword_len())?;
    scratch.c1_values = flatten(&scratch.c1_leaves);
    scratch.c1_salts = derive_salts(
        &reserved,
        context,
        hash,
        CIRCLE_C1_LAYER0_TAG,
        scratch.c1_leaves.len(),
    )?;
    let c1_tree = build_state_only_private_merkle_tree(
        hash,
        17,
        CIRCLE_C1_LAYER0_TAG,
        SPEND_C1_VALUE_WIDTH,
        &scratch.c1_values,
        &scratch.c1_salts,
    )?;
    let c1_root = c1_tree.root();
    absorb_round_root(&mut transcript, 0, &c1_root);
    let lambda = transcript
        .challenge_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(StateOnlyPrefixBuildError::from)?;
    scratch.h1 = build_atomic_state_only_copy_helper_v3(&trace, lambda, chi)
        .map_err(|_| StateOnlyPrefixBuildError::Shape)?;
    apply_atomic_state_only_h1_padding_mask_v3(&mut scratch.h1, &applied.h1_padding)?;
    if state_only_copy_helper_sum(&scratch.h1) != Some(QM31::ZERO) {
        return Err(StateOnlySpendBuildError::Consistency("spend h1 sum"));
    }

    scratch.c2_messages = vec![scratch.h1.clone(), applied.g.clone(), scratch.d.clone()];
    scratch.encoded_c2 = encode_state_only_spend_c2_columns(&encoder, &scratch.c2_messages)?;
    scratch.c2_leaves =
        state_only_spend_c2_layer0_leaves(&scratch.encoded_c2, encoder.codeword_len())?;
    scratch.c2_values = flatten(&scratch.c2_leaves);
    scratch.c2_salts = derive_salts(
        &reserved,
        context,
        hash,
        CIRCLE_C2_LAYER0_TAG,
        scratch.c2_leaves.len(),
    )?;
    let c2_tree = build_state_only_private_merkle_tree(
        hash,
        17,
        CIRCLE_C2_LAYER0_TAG,
        SPEND_C2_VALUE_WIDTH,
        &scratch.c2_values,
        &scratch.c2_salts,
    )?;
    let c2_root = c2_tree.root();
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2_root);

    let batching =
        begin_state_only_zerocheck(&mut transcript).map_err(StateOnlyPrefixBuildError::from)?;
    // D is intentionally absent from this call and from the terminal oracle.
    let masked = prove_masked_state_only_zerocheck(
        &mut transcript,
        precommit_binding,
        &trace,
        &applied.mask_only_c1,
        &applied.g,
        |point| {
            let claims = statement_evaluations(
                &trace,
                &applied.mask_only_c1,
                &scratch.h1,
                &applied.g,
                point,
            )
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
        &scratch.h1,
        &applied.g,
        &masked.sumcheck.challenges,
    )?;
    let (d_claims, d_claim_bytes) = encode_d_claims(&scratch.d, &masked.sumcheck.challenges)
        .ok_or(StateOnlySpendBuildError::Consistency("spend D claims"))?;
    let mut material = StateOnlyPrefixMaterial::front(
        STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE,
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
    // The selector is not absorbed until after the final grinding nonce.  A
    // temporary canonical value is sufficient for the prefix-only replay.
    scratch.prefix_bytes = serialize_spend_prefix(&material, &d_claim_bytes, 0)?;
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        &scratch.prefix_bytes[aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS
            .statement_evaluations_start..]
            [..aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_EVALUATIONS_LEN],
    );
    transcript.absorb(label::M31_STATE_ONLY_ZERO_FACTOR_D_CLAIMS, &d_claim_bytes);
    material.batch_nonce = pow_nonce(
        &transcript,
        STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE.batch_grinding_bits,
        pow_mode,
    )?;
    let mut pow_valid = transcript.grinding_ok(
        material.batch_nonce,
        STATE_ONLY_SPEND_ZERO_FACTOR_SHAPE.batch_grinding_bits,
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
    scratch.prefix_bytes = serialize_spend_prefix(&material, &d_claim_bytes, 0)?;
    let parsed_front = StateOnlySpendPrefix::parse_exact(&scratch.prefix_bytes)?;
    let front_schedule = run_atomic_state_only_spend_prefix_schedule_host_v3(
        hash,
        &parsed_front,
        &statement_digest,
    )?;
    if front_schedule.gamma != gamma
        || front_schedule.point_scale != point_scale
        || front_schedule.lambda != lambda
        || front_schedule.chi != chi
        || front_schedule.z != masked.sumcheck.challenges
    {
        return Err(StateOnlySpendBuildError::Consistency("spend front replay"));
    }

    let original_message =
        gamma_combine_state_only_spend_messages(&scratch.selected_c1, &scratch.c2_messages, gamma)?;
    scratch.combined_codeword = gamma_combine_state_only_spend_codewords(
        &scratch.encoded_c1,
        &scratch.encoded_c2,
        gamma,
        encoder.codeword_len(),
    )?;
    let z = front_schedule.z;
    let points = [z, successor_point(&z), xor12_point(&z)];
    let mut relation = StateOnlyIncrementalRelation::new_with_inactive_masks(
        original_message,
        &points,
        [QM31::ONE, point_scale, point_scale.square()],
        atomic_state_only_copy_inactive_row_masks_v3(),
    )?;
    let prepared = prepare_state_only_spend_relation(
        gamma,
        parsed_front.base.statement_evaluations_bytes,
        parsed_front.d_claims_bytes,
    )
    .ok_or(StateOnlySpendBuildError::Consistency(
        "spend fused relation",
    ))?;

    let mut fold_nonces = [0u64; CANDIDATE_ROUND_COUNT];
    let mut alphas = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    scratch.later_values = Vec::with_capacity(3);
    scratch.later_salts = Vec::with_capacity(3);
    scratch.later_leaves = Vec::with_capacity(3);
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
        fold_nonces[round] = pow_nonce(
            &transcript,
            STATE_ONLY_SPEND_FOLD_GRINDING_BITS[round],
            pow_mode,
        )?;
        pow_valid &= transcript.grinding_ok(
            fold_nonces[round],
            STATE_ONLY_SPEND_FOLD_GRINDING_BITS[round],
        );
        absorb_fold_pow(&mut transcript, round, fold_nonces[round]);
        alphas[round] = transcript
            .challenge_qm31()
            .map_err(CandidatePrefixBuildError::from)?;
        relation.fold(alphas[round])?;
        scratch.combined_codeword = fold_candidate_codeword_round_for_domain_log(
            &scratch.combined_codeword,
            alphas[round],
            round,
            domain_log,
        )?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            scratch
                .later_leaves
                .push(combined_layer_leaves(&scratch.combined_codeword));
            let values = flatten(scratch.later_leaves.last().unwrap());
            let tag = CIRCLE_LINE_TAGS[round];
            let salts = derive_salts(
                &reserved,
                context,
                hash,
                tag,
                scratch.later_leaves.last().unwrap().len(),
            )?;
            let depth = 15 - 2 * round as u32;
            let tree = build_state_only_private_merkle_tree(hash, depth, tag, 64, &values, &salts)?;
            material.later_roots[round] = tree.root();
            absorb_round_root(&mut transcript, round + 1, &material.later_roots[round]);
            scratch.later_values.push(values);
            scratch.later_salts.push(salts);
            later_trees.push(tree);
        }
    }

    let relation = relation.finish()?;
    if relation.point_claims != prepared.relation.claims {
        return Err(StateOnlySpendBuildError::Consistency("spend point claims"));
    }
    absorb_final(&mut transcript, &relation.final_coefficients);
    material.nonce = pow_nonce(&transcript, STATE_ONLY_SPEND_GRINDING_BITS, pow_mode)?;
    pow_valid &= transcript.grinding_ok(material.nonce, STATE_ONLY_SPEND_GRINDING_BITS);
    transcript.absorb(label::GRIND_NONCE, &material.nonce.to_le_bytes());
    material.ood_values = relation.ood_values;
    material.relation_sumchecks = relation.sumchecks;
    material.final_coefficients = relation.final_coefficients;
    material.fold_nonces = fold_nonces;

    // Complete all three post-final-nonce query branches before selecting a
    // public branch.  Commitments, claims, folds and PoW are shared.  The
    // callback sees only public schedules and returns the canonical branch;
    // production supplies the frozen complete-Good predicate, while the raw
    // fixture API below supplies an explicitly forced branch.
    let mut candidate_schedules = Vec::with_capacity(3);
    for selector in 0..3u8 {
        let candidate_prefix =
            Zeroizing::new(serialize_spend_prefix(&material, &d_claim_bytes, selector)?);
        let parsed = StateOnlySpendPrefix::parse_exact(candidate_prefix.as_slice())?;
        let schedule =
            run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3(
                hash,
                &parsed,
                &statement_digest,
            )?;
        if schedule.alpha != alphas
            || schedule.query_count != usize::from(STATE_ONLY_SPEND_QUERY_COUNT)
        {
            return Err(StateOnlySpendBuildError::Consistency(
                "spend candidate replay",
            ));
        }
        candidate_schedules.push(schedule);
    }
    let candidate_schedules: [StateOnlyTranscriptScheduleResult; 3] = candidate_schedules
        .try_into()
        .map_err(|_| StateOnlySpendBuildError::Consistency("spend candidate count"))?;
    let common = candidate_schedules[0];
    for candidate in &candidate_schedules[1..] {
        if candidate.prefix != common.prefix
            || candidate.circle_ood_points != common.circle_ood_points
            || candidate.line_ood_points != common.line_ood_points
            || candidate.mu != common.mu
            || candidate.alpha != common.alpha
            || candidate.state_before_grinding != common.state_before_grinding
            || candidate.query_count != common.query_count
        {
            return Err(StateOnlySpendBuildError::Consistency(
                "spend selector changed the pre-query schedule",
            ));
        }
    }
    let selected = select_query_schedule(&candidate_schedules)
        .map_err(|_| StateOnlySpendBuildError::GoodGate)?
        .filter(|&selector| selector < candidate_schedules.len())
        .ok_or(StateOnlySpendBuildError::NoGoodQuerySchedule)?;
    let query_selector = selected as u8;
    let schedule = candidate_schedules[selected];
    let queries = &schedule.queries[..schedule.query_count];
    scratch.prefix_bytes = serialize_spend_prefix(&material, &d_claim_bytes, query_selector)?;

    let opening_inputs = StateOnlySpendOpeningInputs {
        c1: StateOnlySpendTreeInput {
            tree: &c1_tree,
            values: &scratch.c1_values,
            salts: &scratch.c1_salts,
        },
        c2: StateOnlySpendTreeInput {
            tree: &c2_tree,
            values: &scratch.c2_values,
            salts: &scratch.c2_salts,
        },
        later: [
            StateOnlySpendTreeInput {
                tree: &later_trees[0],
                values: &scratch.later_values[0],
                salts: &scratch.later_salts[0],
            },
            StateOnlySpendTreeInput {
                tree: &later_trees[1],
                values: &scratch.later_values[1],
                salts: &scratch.later_salts[1],
            },
            StateOnlySpendTreeInput {
                tree: &later_trees[2],
                values: &scratch.later_values[2],
                salts: &scratch.later_salts[2],
            },
        ],
    };
    let openings = serialize_state_only_spend_openings(queries, &opening_inputs)?;
    let roots = StateOnlySpendOpeningRoots {
        c1: material.c1_root,
        c2: material.c2_root,
        later: material.later_roots,
    };
    let mut bytes = Vec::with_capacity(scratch.prefix_bytes.len() + openings.bytes.len());
    bytes.extend_from_slice(&scratch.prefix_bytes);
    bytes.extend_from_slice(&openings.bytes);
    Ok(BuiltAtomicStateOnlySpendProof {
        bytes,
        schedule,
        relation,
        roots,
        openings,
        d: scratch.d.clone(),
        d_claims,
        query_selector,
        pow_valid,
    })
}

#[cfg(any(test, feature = "insecure-spend-fixture"))]
pub fn build_hiding_atomic_state_only_spend_proof_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    attempt: StateOnlyAttemptSecrets,
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    hash: HashFn,
    pow_mode: StateOnlyPowMode,
    query_selector: u8,
) -> Result<BuiltAtomicStateOnlySpendProof, StateOnlySpendBuildError> {
    if query_selector >= 3 {
        return Err(StateOnlySpendBuildError::Consistency("spend selector"));
    }
    build_one_attempt(
        statement,
        witness,
        attempt,
        nonce_store,
        hash,
        pow_mode,
        move |_| Ok(Some(query_selector as usize)),
    )
}

/// Production bounded unpublished-attempt entry point. One attempt builds a
/// single common commitment/fold transcript, derives all three independent
/// post-final selector schedules, evaluates the complete frozen GoodSpend
/// product on every branch, and serializes only the least good branch. At
/// most seventeen complete locally-mined attempts are made. Rejected candidate
/// buffers are scrubbed and every controlled failure is collapsed to one
/// opaque error.
pub fn build_hiding_atomic_state_only_spend_first_good_v3(
    statement: &AtomicPaymentStatementV3,
    witness: &SpendWitness,
    nonce_store: &mut DurableStateOnlyMaskNonceStore,
) -> Result<SpendFirstGoodCandidate, SpendAttemptsExhausted> {
    let hash = crate::HOST_HASH;
    run_spend_first_good(
        || StateOnlyAttemptSecrets::generate().map_err(|_| ()),
        |attempt| match build_one_attempt(
            statement,
            witness,
            attempt,
            nonce_store,
            hash,
            StateOnlyPowMode::Mine,
            |schedules| {
                let evaluation = evaluate_spend_candidate_schedules_host(schedules)
                    .map_err(|_| SpendGoodSelectionError)?;
                Ok(evaluation.selected_selector.map(usize::from))
            },
        ) {
            Ok(candidate) => Ok(SpendAttemptBuild::Candidate(candidate)),
            Err(StateOnlySpendBuildError::NoGoodQuerySchedule) => Ok(SpendAttemptBuild::Retry),
            Err(_) => Err(()),
        },
        |candidate| Ok(candidate.pow_valid),
        BuiltAtomicStateOnlySpendProof::scrub_rejected,
    )
    .map(SpendFirstGoodCandidate::new)
}
