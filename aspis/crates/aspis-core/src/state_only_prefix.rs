//! Exact prefix and Fiat--Shamir schedule for the width-28 state-only proof.

use crate::circle::SecureCirclePoint;
use crate::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT;
use crate::circle_prefix::{
    CandidatePrefixError, CandidateRoundOffsets, CandidateRoundRecord,
    CandidateTranscriptScheduleError, CANDIDATE_FINAL_POLY_BYTES, CANDIDATE_FINAL_POLY_LEN,
    CANDIDATE_NONCE_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
    CANDIDATE_STATEMENT_POINT_COORDINATES, ENCODED_QM31_LEN, RATE16_HARDENED_FOLD_POW_BITS,
};
use crate::field::QM31;
use crate::params::{FoldPayload, MerkleMode};
use crate::proof::{
    Header, FLAG_EVALUATION_CLAIM, FLAG_M31_CIRCLE_C1_DIAGNOSTIC, FLAG_SECOND_PHASE, HEADER_LEN,
    M31_CIRCLE_BASIS_DISCRIMINATOR, ROOT_LEN, VERSION_V4_S2,
};
use crate::state_only_hiding::{
    begin_state_only_hiding_precommit, begin_state_only_masked_sumcheck, StateOnlyHidingContext,
    StateOnlyHidingScheduleError, STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH,
};
use crate::state_only_masked_switch::{
    MASKED_SWITCH_COEFFICIENTS, MASKED_SWITCH_FINAL_WORK_BITS, MASKED_SWITCH_SOURCE_WORK_BITS,
};
use crate::state_only_sumcheck::{
    begin_state_only_zerocheck, verify_state_only_sumcheck_streaming, StateOnlySumcheckVerifyError,
    STATE_ONLY_SUMCHECK_BYTES,
};
use crate::statement_sumcheck::PaymentConstraintChallenges;
use crate::sumcheck::{SUMCHECK_BYTES, SUMCHECK_COEFFICIENTS};
use crate::transcript::{label, HashFn, QuerySampleError, Transcript};

pub const STATE_ONLY_RATE16_PROFILE_ID: u8 = 18;
pub const STATE_ONLY_RATE32_PROFILE_ID: u8 = 19;
/// Verifier-cost research profile.  The message remains 2^10 coefficients;
/// only the evaluation domain grows, so this is an ordinary rate-1/512
/// instance of the same four-round arity-four PCS.
pub const STATE_ONLY_RATE512_PROFILE_ID: u8 = 20;
/// Integrated atomic-v3 state-only proof with the post-round-zero masked
/// switch, private leaf salts, and positioned source/final work witnesses.
pub const STATE_ONLY_PROFILE21_PROFILE_ID: u8 = 21;
/// Private-salted, no-switch successor to profile 20.  The PCS and
/// Fiat--Shamir schedule are otherwise the ordinary rate-1/512 schedule.
pub const STATE_ONLY_PROFILE22_PRIVATE_PROFILE_ID: u8 = 22;
/// Quarantined zero-factor-D successor. It is never selected by the frozen
/// profile-22 entry points or program tags.
pub const STATE_ONLY_PROFILE23_ZERO_FACTOR_PROFILE_ID: u8 = 23;
pub const STATE_ONLY_LOG_ROWS: u32 = 10;
pub const STATE_ONLY_RATE16_LOG_BLOWUP: u32 = 4;
pub const STATE_ONLY_RATE32_LOG_BLOWUP: u32 = 5;
pub const STATE_ONLY_RATE512_LOG_BLOWUP: u32 = 9;
pub const STATE_ONLY_RATE16_QUERY_COUNT: u16 = 36;
pub const STATE_ONLY_RATE32_QUERY_COUNT: u16 = 29;
pub const STATE_ONLY_RATE512_QUERY_COUNT: u16 = 16;
pub const STATE_ONLY_MAX_QUERY_COUNT: usize = STATE_ONLY_RATE16_QUERY_COUNT as usize;
pub const STATE_ONLY_GRINDING_BITS: u8 = 36;
pub const STATE_ONLY_RATE16_BATCH_GRINDING_BITS: u8 = 24;
pub const STATE_ONLY_RATE32_BATCH_GRINDING_BITS: u8 = 26;
pub const STATE_ONLY_RATE512_BATCH_GRINDING_BITS: u8 = 36;
pub const STATE_ONLY_PROFILE21_GRINDING_BITS: u8 = MASKED_SWITCH_FINAL_WORK_BITS;
pub const STATE_ONLY_PROFILE21_BATCH_GRINDING_BITS: u8 = 38;
/// Profile-22 work factors are deliberately independent of profile 20 so the
/// soundness ledger can freeze them without changing any older wire profile.
/// The frozen profile-22 ledger uses g38 for both batch and final work.
pub const STATE_ONLY_PROFILE22_GRINDING_BITS: u8 = 38;
pub const STATE_ONLY_PROFILE22_BATCH_GRINDING_BITS: u8 = 38;
pub const STATE_ONLY_PROFILE23_GRINDING_BITS: u8 = 38;
pub const STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS: u8 = 38;
pub const STATE_ONLY_VALUES_PER_POINT: usize = STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH;
pub const STATE_ONLY_STATEMENT_POINT_COUNT: usize = 3;
pub const STATE_ONLY_STATEMENT_VALUE_COUNT: usize =
    STATE_ONLY_STATEMENT_POINT_COUNT * STATE_ONLY_VALUES_PER_POINT;
pub const STATE_ONLY_STATEMENT_EVALUATIONS_LEN: usize =
    STATE_ONLY_STATEMENT_VALUE_COUNT * ENCODED_QM31_LEN;
pub const STATE_ONLY_FLAGS: u8 =
    FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyProfileShape {
    pub profile_id: u8,
    pub log_blowup: u32,
    pub query_count: u16,
    pub batch_grinding_bits: u8,
}

pub const STATE_ONLY_RATE16_SHAPE: StateOnlyProfileShape = StateOnlyProfileShape {
    profile_id: STATE_ONLY_RATE16_PROFILE_ID,
    log_blowup: STATE_ONLY_RATE16_LOG_BLOWUP,
    query_count: STATE_ONLY_RATE16_QUERY_COUNT,
    batch_grinding_bits: STATE_ONLY_RATE16_BATCH_GRINDING_BITS,
};
pub const STATE_ONLY_RATE32_SHAPE: StateOnlyProfileShape = StateOnlyProfileShape {
    profile_id: STATE_ONLY_RATE32_PROFILE_ID,
    log_blowup: STATE_ONLY_RATE32_LOG_BLOWUP,
    query_count: STATE_ONLY_RATE32_QUERY_COUNT,
    batch_grinding_bits: STATE_ONLY_RATE32_BATCH_GRINDING_BITS,
};
pub const STATE_ONLY_RATE512_SHAPE: StateOnlyProfileShape = StateOnlyProfileShape {
    profile_id: STATE_ONLY_RATE512_PROFILE_ID,
    log_blowup: STATE_ONLY_RATE512_LOG_BLOWUP,
    query_count: STATE_ONLY_RATE512_QUERY_COUNT,
    batch_grinding_bits: STATE_ONLY_RATE512_BATCH_GRINDING_BITS,
};
pub const STATE_ONLY_PROFILE21_SHAPE: StateOnlyProfileShape = StateOnlyProfileShape {
    profile_id: STATE_ONLY_PROFILE21_PROFILE_ID,
    log_blowup: STATE_ONLY_RATE512_LOG_BLOWUP,
    query_count: STATE_ONLY_RATE512_QUERY_COUNT,
    batch_grinding_bits: STATE_ONLY_PROFILE21_BATCH_GRINDING_BITS,
};
pub const STATE_ONLY_PROFILE22_PRIVATE_SHAPE: StateOnlyProfileShape = StateOnlyProfileShape {
    profile_id: STATE_ONLY_PROFILE22_PRIVATE_PROFILE_ID,
    log_blowup: STATE_ONLY_RATE512_LOG_BLOWUP,
    query_count: STATE_ONLY_RATE512_QUERY_COUNT,
    batch_grinding_bits: STATE_ONLY_PROFILE22_BATCH_GRINDING_BITS,
};
pub const STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE: StateOnlyProfileShape = StateOnlyProfileShape {
    profile_id: STATE_ONLY_PROFILE23_ZERO_FACTOR_PROFILE_ID,
    log_blowup: STATE_ONLY_RATE512_LOG_BLOWUP,
    query_count: STATE_ONLY_RATE512_QUERY_COUNT,
    batch_grinding_bits: STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS,
};

pub const fn state_only_final_grinding_bits(shape: StateOnlyProfileShape) -> u8 {
    match shape.profile_id {
        STATE_ONLY_PROFILE21_PROFILE_ID => STATE_ONLY_PROFILE21_GRINDING_BITS,
        STATE_ONLY_PROFILE22_PRIVATE_PROFILE_ID => STATE_ONLY_PROFILE22_GRINDING_BITS,
        STATE_ONLY_PROFILE23_ZERO_FACTOR_PROFILE_ID => STATE_ONLY_PROFILE23_GRINDING_BITS,
        _ => STATE_ONLY_GRINDING_BITS,
    }
}

/// Profile 21 serializes its switch claims after the byte-compatible base
/// prefix. Their physical position does not determine Fiat--Shamir order:
/// replay absorbs the source work nonce after the round-zero fold challenge,
/// then samples delta and absorbs logical U followed by its one claimed seam
/// target tau before the translated W1 root.
pub const STATE_ONLY_PROFILE21_TAU_BYTES: usize = ENCODED_QM31_LEN;
pub const STATE_ONLY_PROFILE21_U_BYTES: usize = MASKED_SWITCH_COEFFICIENTS * ENCODED_QM31_LEN;
pub const STATE_ONLY_PROFILE21_EXTENSION_LEN: usize =
    CANDIDATE_NONCE_LEN + STATE_ONLY_PROFILE21_U_BYTES + STATE_ONLY_PROFILE21_TAU_BYTES;
pub const STATE_ONLY_PROFILE21_PREFIX_LEN: usize =
    STATE_ONLY_PREFIX_LEN + STATE_ONLY_PROFILE21_EXTENSION_LEN;

/// Append-only profile-23 extension. D's three point claims are physically
/// after the frozen 6,736-byte base prefix but are absorbed logically beside
/// the base statement claims, before batch grinding and gamma. The selector
/// byte is physically last and is absorbed after the final nonce.
pub const STATE_ONLY_PROFILE23_D_CLAIM_COUNT: usize = 3;
pub const STATE_ONLY_PROFILE23_D_CLAIMS_LEN: usize =
    STATE_ONLY_PROFILE23_D_CLAIM_COUNT * ENCODED_QM31_LEN;
pub const STATE_ONLY_PROFILE23_QUERY_SELECTOR_LEN: usize = 1;
pub const STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT: u8 = 3;
pub const STATE_ONLY_PROFILE23_EXTENSION_LEN: usize =
    STATE_ONLY_PROFILE23_D_CLAIMS_LEN + STATE_ONLY_PROFILE23_QUERY_SELECTOR_LEN;
pub const STATE_ONLY_PROFILE23_PREFIX_LEN: usize =
    STATE_ONLY_PREFIX_LEN + STATE_ONLY_PROFILE23_EXTENSION_LEN;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyPrefixOffsets {
    pub header_start: usize,
    pub mask_nonce_start: usize,
    pub c1_root_start: usize,
    pub c2_root_start: usize,
    pub initial_mask_claim_start: usize,
    pub sumcheck_start: usize,
    pub statement_evaluations_start: usize,
    pub rounds: [CandidateRoundOffsets; CANDIDATE_ROUND_COUNT],
    pub final_polynomial_start: usize,
    pub nonce_start: usize,
    pub fold_nonces_start: usize,
    pub batch_nonce_start: usize,
    pub openings_start: usize,
}

pub const STATE_ONLY_PREFIX_OFFSETS: StateOnlyPrefixOffsets = StateOnlyPrefixOffsets {
    header_start: 0,
    mask_nonce_start: 16,
    c1_root_start: 48,
    c2_root_start: 80,
    initial_mask_claim_start: 112,
    sumcheck_start: 128,
    statement_evaluations_start: 4_608,
    rounds: [
        CandidateRoundOffsets {
            record_start: 5_952,
            root_start: None,
            ood_values_start: 5_952,
            sumcheck_start: 5_984,
            record_end: 6_096,
        },
        CandidateRoundOffsets {
            record_start: 6_096,
            root_start: Some(6_096),
            ood_values_start: 6_128,
            sumcheck_start: 6_160,
            record_end: 6_272,
        },
        CandidateRoundOffsets {
            record_start: 6_272,
            root_start: Some(6_272),
            ood_values_start: 6_304,
            sumcheck_start: 6_336,
            record_end: 6_448,
        },
        CandidateRoundOffsets {
            record_start: 6_448,
            root_start: Some(6_448),
            ood_values_start: 6_480,
            sumcheck_start: 6_512,
            record_end: 6_624,
        },
    ],
    final_polynomial_start: 6_624,
    nonce_start: 6_688,
    fold_nonces_start: 6_696,
    batch_nonce_start: 6_728,
    openings_start: 6_736,
};
pub const STATE_ONLY_PREFIX_LEN: usize = STATE_ONLY_PREFIX_OFFSETS.openings_start;

#[derive(Clone, Copy, Debug)]
pub struct StateOnlyCandidatePrefix<'a> {
    pub shape: StateOnlyProfileShape,
    pub header: Header,
    pub header_bytes: &'a [u8; HEADER_LEN],
    pub mask_nonce: &'a [u8; 32],
    pub c1_root: &'a [u8; ROOT_LEN],
    pub c2_root: &'a [u8; ROOT_LEN],
    pub initial_mask_claim_bytes: &'a [u8; ENCODED_QM31_LEN],
    pub sumcheck_bytes: &'a [u8; STATE_ONLY_SUMCHECK_BYTES],
    pub statement_evaluations_bytes: &'a [u8; STATE_ONLY_STATEMENT_EVALUATIONS_LEN],
    pub rounds: [CandidateRoundRecord<'a>; CANDIDATE_ROUND_COUNT],
    pub final_polynomial_bytes: &'a [u8; CANDIDATE_FINAL_POLY_BYTES],
    pub nonce: u64,
    pub fold_nonces: [u64; CANDIDATE_ROUND_COUNT],
    pub batch_nonce: u64,
}

fn array_at<const N: usize>(bytes: &[u8], start: usize) -> &[u8; N] {
    bytes[start..start + N].try_into().unwrap()
}

fn validate_field_block(
    bytes: &[u8],
    start: usize,
    count: usize,
) -> Result<(), CandidatePrefixError> {
    for index in 0..count {
        let offset = start + index * ENCODED_QM31_LEN;
        if QM31::from_le_bytes(&bytes[offset..offset + ENCODED_QM31_LEN]).is_none() {
            return Err(CandidatePrefixError::NonCanonicalFieldElement { offset });
        }
    }
    Ok(())
}

fn shape_from_header(header: &Header) -> Option<StateOnlyProfileShape> {
    [
        STATE_ONLY_RATE16_SHAPE,
        STATE_ONLY_RATE32_SHAPE,
        STATE_ONLY_RATE512_SHAPE,
        STATE_ONLY_PROFILE21_SHAPE,
        STATE_ONLY_PROFILE22_PRIVATE_SHAPE,
        STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE,
    ]
    .into_iter()
    .find(|shape| {
        header.version == VERSION_V4_S2
            && header.profile_id == shape.profile_id
            && header.log_rows == STATE_ONLY_LOG_ROWS
            && header.log_blowup == shape.log_blowup
            && header.query_count == shape.query_count
            && header.grinding_bits == state_only_final_grinding_bits(*shape)
            && header.fold_payload == FoldPayload::RawFibers as u8
            && header.merkle_mode == MerkleMode::Radix4MinimalSubtree as u8
            && header.num_rounds == CANDIDATE_ROUND_COUNT as u32
            && header.final_poly_log_len == 2
            && header.flags == STATE_ONLY_FLAGS
    })
}

impl<'a> StateOnlyCandidatePrefix<'a> {
    pub fn parse_exact(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        match bytes.len().cmp(&STATE_ONLY_PREFIX_LEN) {
            core::cmp::Ordering::Less => return Err(CandidatePrefixError::Truncated),
            core::cmp::Ordering::Greater => return Err(CandidatePrefixError::TrailingBytes),
            core::cmp::Ordering::Equal => {}
        }
        Self::parse_prefix(bytes)
    }

    pub fn parse_from_proof(bytes: &'a [u8]) -> Result<(Self, &'a [u8]), CandidatePrefixError> {
        if bytes.len() < STATE_ONLY_PREFIX_LEN {
            return Err(CandidatePrefixError::Truncated);
        }
        let (prefix, openings) = bytes.split_at(STATE_ONLY_PREFIX_LEN);
        Ok((Self::parse_prefix(prefix)?, openings))
    }

    fn parse_prefix(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        let header_bytes = array_at::<HEADER_LEN>(bytes, STATE_ONLY_PREFIX_OFFSETS.header_start);
        let header = Header::parse(header_bytes).ok_or(CandidatePrefixError::BadHeader)?;
        let shape = shape_from_header(&header).ok_or(CandidatePrefixError::BadHeader)?;
        if array_at::<32>(bytes, STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start) == &[0u8; 32] {
            return Err(CandidatePrefixError::BadHeader);
        }
        validate_field_block(bytes, STATE_ONLY_PREFIX_OFFSETS.initial_mask_claim_start, 1)?;
        for round in STATE_ONLY_PREFIX_OFFSETS.rounds {
            validate_field_block(bytes, round.ood_values_start, CANDIDATE_OOD_SAMPLES)?;
            validate_field_block(bytes, round.sumcheck_start, SUMCHECK_COEFFICIENTS)?;
        }
        validate_field_block(
            bytes,
            STATE_ONLY_PREFIX_OFFSETS.final_polynomial_start,
            CANDIDATE_FINAL_POLY_LEN,
        )?;
        let rounds = core::array::from_fn(|layer| {
            let offsets = STATE_ONLY_PREFIX_OFFSETS.rounds[layer];
            CandidateRoundRecord {
                layer: layer as u8,
                start_offset: offsets.record_start,
                root: offsets.root_start.map(|start| array_at(bytes, start)),
                ood_value_bytes: array_at(bytes, offsets.ood_values_start),
                sumcheck_bytes: array_at(bytes, offsets.sumcheck_start),
                record_bytes: &bytes[offsets.record_start..offsets.record_end],
            }
        });
        Ok(Self {
            shape,
            header,
            header_bytes,
            mask_nonce: array_at(bytes, STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start),
            c1_root: array_at(bytes, STATE_ONLY_PREFIX_OFFSETS.c1_root_start),
            c2_root: array_at(bytes, STATE_ONLY_PREFIX_OFFSETS.c2_root_start),
            initial_mask_claim_bytes: array_at(
                bytes,
                STATE_ONLY_PREFIX_OFFSETS.initial_mask_claim_start,
            ),
            sumcheck_bytes: array_at(bytes, STATE_ONLY_PREFIX_OFFSETS.sumcheck_start),
            statement_evaluations_bytes: array_at(
                bytes,
                STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start,
            ),
            rounds,
            final_polynomial_bytes: array_at(
                bytes,
                STATE_ONLY_PREFIX_OFFSETS.final_polynomial_start,
            ),
            nonce: u64::from_le_bytes(
                bytes[STATE_ONLY_PREFIX_OFFSETS.nonce_start
                    ..STATE_ONLY_PREFIX_OFFSETS.nonce_start + CANDIDATE_NONCE_LEN]
                    .try_into()
                    .unwrap(),
            ),
            fold_nonces: core::array::from_fn(|round| {
                let start =
                    STATE_ONLY_PREFIX_OFFSETS.fold_nonces_start + round * CANDIDATE_NONCE_LEN;
                u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap())
            }),
            batch_nonce: u64::from_le_bytes(
                bytes[STATE_ONLY_PREFIX_OFFSETS.batch_nonce_start
                    ..STATE_ONLY_PREFIX_OFFSETS.batch_nonce_start + 8]
                    .try_into()
                    .unwrap(),
            ),
        })
    }

    pub fn initial_mask_claim(&self) -> QM31 {
        QM31::from_le_bytes(self.initial_mask_claim_bytes).unwrap()
    }

    pub fn statement_evaluation(&self, index: usize) -> Option<QM31> {
        if index >= STATE_ONLY_STATEMENT_VALUE_COUNT {
            return None;
        }
        let start = index * ENCODED_QM31_LEN;
        QM31::from_le_bytes(&self.statement_evaluations_bytes[start..start + 16])
    }

    pub fn final_coefficient(&self, index: usize) -> Option<QM31> {
        let start = index.checked_mul(ENCODED_QM31_LEN)?;
        QM31::from_le_bytes(self.final_polynomial_bytes.get(start..start + 16)?)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StateOnlyProfile21Prefix<'a> {
    pub base: StateOnlyCandidatePrefix<'a>,
    pub source_nonce: u64,
    pub logical_u_bytes: &'a [u8; STATE_ONLY_PROFILE21_U_BYTES],
    pub tau_bytes: &'a [u8; STATE_ONLY_PROFILE21_TAU_BYTES],
}

impl<'a> StateOnlyProfile21Prefix<'a> {
    pub fn parse_exact(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        match bytes.len().cmp(&STATE_ONLY_PROFILE21_PREFIX_LEN) {
            core::cmp::Ordering::Less => return Err(CandidatePrefixError::Truncated),
            core::cmp::Ordering::Greater => return Err(CandidatePrefixError::TrailingBytes),
            core::cmp::Ordering::Equal => {}
        }
        Self::parse_prefix(bytes)
    }

    pub fn parse_from_proof(bytes: &'a [u8]) -> Result<(Self, &'a [u8]), CandidatePrefixError> {
        if bytes.len() < STATE_ONLY_PROFILE21_PREFIX_LEN {
            return Err(CandidatePrefixError::Truncated);
        }
        let (prefix, openings) = bytes.split_at(STATE_ONLY_PROFILE21_PREFIX_LEN);
        Ok((Self::parse_prefix(prefix)?, openings))
    }

    fn parse_prefix(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        let base = StateOnlyCandidatePrefix::parse_exact(&bytes[..STATE_ONLY_PREFIX_LEN])?;
        if base.shape != STATE_ONLY_PROFILE21_SHAPE {
            return Err(CandidatePrefixError::BadHeader);
        }
        let source_nonce_start = STATE_ONLY_PREFIX_LEN;
        let logical_u_start = source_nonce_start + CANDIDATE_NONCE_LEN;
        let tau_start = logical_u_start + STATE_ONLY_PROFILE21_U_BYTES;
        validate_field_block(bytes, logical_u_start, MASKED_SWITCH_COEFFICIENTS)?;
        let tau_bytes = array_at(bytes, tau_start);
        if QM31::from_le_bytes(tau_bytes).is_none() {
            return Err(CandidatePrefixError::NonCanonicalFieldElement { offset: tau_start });
        }
        Ok(Self {
            base,
            source_nonce: u64::from_le_bytes(
                bytes[source_nonce_start..source_nonce_start + CANDIDATE_NONCE_LEN]
                    .try_into()
                    .unwrap(),
            ),
            logical_u_bytes: array_at(bytes, logical_u_start),
            tau_bytes,
        })
    }

    pub fn tau(&self) -> QM31 {
        QM31::from_le_bytes(self.tau_bytes).unwrap()
    }

    pub fn logical_u(&self) -> [QM31; MASKED_SWITCH_COEFFICIENTS] {
        core::array::from_fn(|index| {
            let start = index * ENCODED_QM31_LEN;
            QM31::from_le_bytes(&self.logical_u_bytes[start..start + ENCODED_QM31_LEN]).unwrap()
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StateOnlyProfile23Prefix<'a> {
    pub base: StateOnlyCandidatePrefix<'a>,
    pub d_claims_bytes: &'a [u8; STATE_ONLY_PROFILE23_D_CLAIMS_LEN],
    pub query_selector: u8,
}

impl<'a> StateOnlyProfile23Prefix<'a> {
    pub fn parse_exact(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        match bytes.len().cmp(&STATE_ONLY_PROFILE23_PREFIX_LEN) {
            core::cmp::Ordering::Less => return Err(CandidatePrefixError::Truncated),
            core::cmp::Ordering::Greater => return Err(CandidatePrefixError::TrailingBytes),
            core::cmp::Ordering::Equal => {}
        }
        Self::parse_prefix(bytes)
    }

    pub fn parse_from_proof(bytes: &'a [u8]) -> Result<(Self, &'a [u8]), CandidatePrefixError> {
        if bytes.len() < STATE_ONLY_PROFILE23_PREFIX_LEN {
            return Err(CandidatePrefixError::Truncated);
        }
        let (prefix, openings) = bytes.split_at(STATE_ONLY_PROFILE23_PREFIX_LEN);
        Ok((Self::parse_prefix(prefix)?, openings))
    }

    fn parse_prefix(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        let base = StateOnlyCandidatePrefix::parse_exact(&bytes[..STATE_ONLY_PREFIX_LEN])?;
        if base.shape != STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE {
            return Err(CandidatePrefixError::BadHeader);
        }
        let d_claims_start = STATE_ONLY_PREFIX_LEN;
        validate_field_block(bytes, d_claims_start, STATE_ONLY_PROFILE23_D_CLAIM_COUNT)?;
        let selector = bytes[d_claims_start + STATE_ONLY_PROFILE23_D_CLAIMS_LEN];
        if selector >= STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT {
            return Err(CandidatePrefixError::BadHeader);
        }
        Ok(Self {
            base,
            d_claims_bytes: array_at(bytes, d_claims_start),
            query_selector: selector,
        })
    }

    pub fn d_claim(&self, point: usize) -> Option<QM31> {
        if point >= STATE_ONLY_PROFILE23_D_CLAIM_COUNT {
            return None;
        }
        let start = point * ENCODED_QM31_LEN;
        QM31::from_le_bytes(&self.d_claims_bytes[start..start + ENCODED_QM31_LEN])
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyTranscriptError {
    Candidate(CandidateTranscriptScheduleError),
    Sumcheck(StateOnlySumcheckVerifyError),
    Hiding(StateOnlyHidingScheduleError),
    Query(QuerySampleError),
    ProfileMismatch,
    SourceGrindingRejected,
    DeltaZeroExhausted,
}

impl From<CandidateTranscriptScheduleError> for StateOnlyTranscriptError {
    fn from(error: CandidateTranscriptScheduleError) -> Self {
        Self::Candidate(error)
    }
}
impl From<StateOnlySumcheckVerifyError> for StateOnlyTranscriptError {
    fn from(error: StateOnlySumcheckVerifyError) -> Self {
        Self::Sumcheck(error)
    }
}
impl From<StateOnlyHidingScheduleError> for StateOnlyTranscriptError {
    fn from(error: StateOnlyHidingScheduleError) -> Self {
        Self::Hiding(error)
    }
}
impl From<QuerySampleError> for StateOnlyTranscriptError {
    fn from(error: QuerySampleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyPrefixScheduleResult {
    pub lambda: QM31,
    pub chi: QM31,
    pub batching: PaymentConstraintChallenges,
    pub initial_mask_claim: QM31,
    pub eta: QM31,
    pub z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    pub masked_terminal_claim: QM31,
    pub gamma: QM31,
    pub point_scale: QM31,
    pub state_after_gamma: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyTranscriptScheduleResult {
    pub prefix: StateOnlyPrefixScheduleResult,
    pub circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    pub line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    pub mu: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub alpha: [QM31; CANDIDATE_ROUND_COUNT],
    pub state_before_grinding: [u8; 32],
    pub queries: [u32; STATE_ONLY_MAX_QUERY_COUNT],
    pub query_count: usize,
    pub state_after_queries: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyProfile21TranscriptScheduleResult {
    pub base: StateOnlyTranscriptScheduleResult,
    pub delta: QM31,
}

fn absorb_round_root(transcript: &mut Transcript, layer: usize, root: &[u8; ROOT_LEN]) {
    let mut record = [0u8; 1 + ROOT_LEN];
    record[0] = layer as u8;
    record[1..].copy_from_slice(root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    for coordinate in (0..z.len()).rev() {
        let bit = z[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    let mut absorption = *z;
    for coordinate in [7usize, 6] {
        absorption[coordinate] = QM31::ONE.sub(absorption[coordinate]);
    }
    [*z, successor, absorption]
}

fn encode_statement_points(z: &[QM31; 10]) -> [u8; 3 * 10 * 16] {
    let points = state_only_statement_points(z);
    let mut bytes = [0u8; 3 * 10 * 16];
    for (point, coordinates) in points.iter().enumerate() {
        for (coordinate, value) in coordinates.iter().enumerate() {
            value.write_le_bytes(&mut bytes[(point * 10 + coordinate) * 16..][..16]);
        }
    }
    bytes
}

fn begin_schedule_with_context(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
    hiding_context: StateOnlyHidingContext,
    profile23_d_claims: Option<&[u8; STATE_ONLY_PROFILE23_D_CLAIMS_LEN]>,
) -> Result<(Transcript, StateOnlyPrefixScheduleResult), StateOnlyTranscriptError> {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, prefix.header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);
    begin_state_only_hiding_precommit(&mut transcript, hiding_context)?;
    absorb_round_root(&mut transcript, 0, prefix.c1_root);
    let lambda = transcript
        .challenge_qm31()
        .map_err(CandidateTranscriptScheduleError::from)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(CandidateTranscriptScheduleError::from)?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, prefix.c2_root);
    let batching = begin_state_only_zerocheck(&mut transcript)
        .map_err(CandidateTranscriptScheduleError::from)?;
    let initial_mask_claim = prefix.initial_mask_claim();
    let eta = begin_state_only_masked_sumcheck(&mut transcript, initial_mask_claim)?;
    let verified = verify_state_only_sumcheck_streaming(
        &mut transcript,
        prefix.sumcheck_bytes,
        initial_mask_claim,
    )?;
    let z = verified.point;
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_POINTS,
        &encode_statement_points(&z),
    );
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        prefix.statement_evaluations_bytes,
    );
    if let Some(d_claims) = profile23_d_claims {
        transcript.absorb(label::M31_STATE_ONLY_ZERO_FACTOR_D_CLAIMS, d_claims);
    }
    let batch_ok = transcript.grinding_ok(prefix.batch_nonce, prefix.shape.batch_grinding_bits);
    if check_pow && !batch_ok {
        return Err(CandidateTranscriptScheduleError::BatchGrindingRejected.into());
    }
    transcript.absorb(
        label::M31_PAYMENT_BATCH_POW_NONCE,
        &prefix.batch_nonce.to_le_bytes(),
    );
    // Profile 22 excludes gamma=0. At zero, the exact production PCS
    // continuation loses physical/legal affine containment even though the
    // raw and masked-sumcheck blocks retain full rank. Older frozen profiles
    // keep their original sampler.
    let gamma = if prefix.shape == STATE_ONLY_PROFILE22_PRIVATE_SHAPE
        || prefix.shape == STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE
    {
        transcript.challenge_nonzero_qm31()
    } else {
        transcript.challenge_qm31()
    }
    .map_err(CandidateTranscriptScheduleError::from)?;
    let point_scale = transcript
        .challenge_qm31()
        .map_err(CandidateTranscriptScheduleError::from)?;
    let state_after_gamma = transcript.diagnostic_state();
    Ok((
        transcript,
        StateOnlyPrefixScheduleResult {
            lambda,
            chi,
            batching,
            initial_mask_claim,
            eta,
            z,
            masked_terminal_claim: verified.terminal_claim,
            gamma,
            point_scale,
            state_after_gamma,
        },
    ))
}

fn begin_schedule(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<(Transcript, StateOnlyPrefixScheduleResult), StateOnlyTranscriptError> {
    // Profile 23 has three additional D claims before the batching challenge.
    // A caller holding only the base prefix cannot replay that transcript and
    // must use the typed profile-23 API instead.
    if prefix.shape == STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE {
        return Err(StateOnlyTranscriptError::ProfileMismatch);
    }
    begin_schedule_with_context(
        hash,
        prefix,
        statement_digest,
        check_pow,
        StateOnlyHidingContext::pinned(*statement_digest, *prefix.mask_nonce),
        None,
    )
}

fn begin_atomic_schedule_v3(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<(Transcript, StateOnlyPrefixScheduleResult), StateOnlyTranscriptError> {
    if prefix.shape == STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE {
        return Err(StateOnlyTranscriptError::ProfileMismatch);
    }
    begin_schedule_with_context(
        hash,
        prefix,
        statement_digest,
        check_pow,
        StateOnlyHidingContext::atomic_v3(*statement_digest, *prefix.mask_nonce),
        None,
    )
}

fn begin_atomic_profile23_schedule_v3(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<(Transcript, StateOnlyPrefixScheduleResult), StateOnlyTranscriptError> {
    if prefix.base.shape != STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE {
        return Err(StateOnlyTranscriptError::ProfileMismatch);
    }
    begin_schedule_with_context(
        hash,
        &prefix.base,
        statement_digest,
        check_pow,
        StateOnlyHidingContext::atomic_profile23_v3(*statement_digest, *prefix.base.mask_nonce),
        Some(prefix.d_claims_bytes),
    )
}

pub fn run_state_only_prefix_schedule_host(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyPrefixScheduleResult, StateOnlyTranscriptError> {
    Ok(begin_schedule(hash, prefix, statement_digest, false)?.1)
}

pub fn run_atomic_state_only_prefix_schedule_host_v3(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyPrefixScheduleResult, StateOnlyTranscriptError> {
    Ok(begin_atomic_schedule_v3(hash, prefix, statement_digest, false)?.1)
}

pub fn run_atomic_state_only_profile23_prefix_schedule_host_v3(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyPrefixScheduleResult, StateOnlyTranscriptError> {
    Ok(begin_atomic_profile23_schedule_v3(hash, prefix, statement_digest, false)?.1)
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

fn absorb_relation_sumcheck(transcript: &mut Transcript, record: &CandidateRoundRecord<'_>) {
    let mut bytes = [0u8; 1 + SUMCHECK_BYTES];
    bytes[0] = record.layer;
    bytes[1..].copy_from_slice(record.sumcheck_bytes);
    transcript.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &bytes);
}

fn sample_profile21_nonzero_delta(
    transcript: &mut Transcript,
) -> Result<QM31, StateOnlyTranscriptError> {
    // Three independent exact-uniform attempts leave completeness failure
    // below 2^-372 while making the affine source multiplier invertible.
    for _ in 0..3 {
        let candidate = transcript
            .challenge_qm31()
            .map_err(CandidateTranscriptScheduleError::from)?;
        if candidate != QM31::ZERO {
            return Ok(candidate);
        }
    }
    Err(StateOnlyTranscriptError::DeltaZeroExhausted)
}

fn sample_queries(
    transcript: &mut Transcript,
    shape: StateOnlyProfileShape,
) -> Result<([u32; STATE_ONLY_MAX_QUERY_COUNT], usize), QuerySampleError> {
    sample_queries_for_count(transcript, shape, shape.query_count as usize)
}

fn sample_queries_for_count(
    transcript: &mut Transcript,
    shape: StateOnlyProfileShape,
    query_count: usize,
) -> Result<([u32; STATE_ONLY_MAX_QUERY_COUNT], usize), QuerySampleError> {
    if query_count > STATE_ONLY_MAX_QUERY_COUNT {
        return Err(QuerySampleError::CountExceedsBound {
            count: query_count,
            bound: STATE_ONLY_MAX_QUERY_COUNT as u32,
        });
    }
    let values = transcript.challenge_queries_without_replacement(
        query_count,
        1u32 << (STATE_ONLY_LOG_ROWS + shape.log_blowup - 2),
        PAYMENT_HIDING_QUERY_DRAW_LIMIT,
    )?;
    let mut queries = [0u32; STATE_ONLY_MAX_QUERY_COUNT];
    queries[..values.len()].copy_from_slice(&values);
    Ok((queries, values.len()))
}

fn run_full_with_context(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
    atomic_v3: bool,
    profile23: Option<&StateOnlyProfile23Prefix<'_>>,
) -> Result<StateOnlyTranscriptScheduleResult, StateOnlyTranscriptError> {
    if prefix.shape == STATE_ONLY_PROFILE21_SHAPE
        || (prefix.shape == STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE && profile23.is_none())
        || (profile23.is_some() && !atomic_v3)
    {
        return Err(StateOnlyTranscriptError::ProfileMismatch);
    }
    let (mut transcript, prefix_result) = if let Some(profile23) = profile23 {
        if profile23.base.shape != prefix.shape {
            return Err(StateOnlyTranscriptError::ProfileMismatch);
        }
        begin_atomic_profile23_schedule_v3(hash, profile23, statement_digest, check_pow)?
    } else if atomic_v3 {
        begin_atomic_schedule_v3(hash, prefix, statement_digest, check_pow)?
    } else {
        begin_schedule(hash, prefix, statement_digest, check_pow)?
    };
    let mut circle_ood_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES];
    let mut line_ood_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut mu = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut alpha = [QM31::ZERO; CANDIDATE_ROUND_COUNT];
    for sample in 0..CANDIDATE_OOD_SAMPLES {
        circle_ood_points[sample] = transcript
            .challenge_secure_circle_point()
            .map_err(CandidateTranscriptScheduleError::from)?;
        absorb_ood(
            &mut transcript,
            label::M31_CIRCLE_OOD_VALUE,
            0,
            sample,
            prefix.rounds[0].ood_value(sample).unwrap(),
        );
        mu[0][sample] = transcript
            .challenge_qm31()
            .map_err(CandidateTranscriptScheduleError::from)?;
    }
    absorb_relation_sumcheck(&mut transcript, &prefix.rounds[0]);
    for round in 0..CANDIDATE_ROUND_COUNT {
        if round != 0 {
            absorb_round_root(&mut transcript, round, prefix.rounds[round].root.unwrap());
            for sample in 0..CANDIDATE_OOD_SAMPLES {
                line_ood_points[round - 1][sample] = transcript
                    .challenge_ood_qm31()
                    .map_err(CandidateTranscriptScheduleError::from)?;
                absorb_ood(
                    &mut transcript,
                    label::M31_LINE_OOD_VALUE,
                    round,
                    sample,
                    prefix.rounds[round].ood_value(sample).unwrap(),
                );
                mu[round][sample] = transcript
                    .challenge_qm31()
                    .map_err(CandidateTranscriptScheduleError::from)?;
            }
            absorb_relation_sumcheck(&mut transcript, &prefix.rounds[round]);
        }
        let fold_ok = transcript.grinding_ok(
            prefix.fold_nonces[round],
            RATE16_HARDENED_FOLD_POW_BITS[round],
        );
        if check_pow && !fold_ok {
            return Err(CandidateTranscriptScheduleError::FoldGrindingRejected { round }.into());
        }
        let mut record = [0u8; 9];
        record[0] = round as u8;
        record[1..].copy_from_slice(&prefix.fold_nonces[round].to_le_bytes());
        transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
        alpha[round] = transcript
            .challenge_qm31()
            .map_err(CandidateTranscriptScheduleError::from)?;
    }
    transcript.absorb(
        label::M31_CIRCLE_FINAL_TENSOR_POLY,
        prefix.final_polynomial_bytes,
    );
    let state_before_grinding = transcript.diagnostic_state();
    let final_ok =
        transcript.grinding_ok(prefix.nonce, state_only_final_grinding_bits(prefix.shape));
    if check_pow && !final_ok {
        return Err(CandidateTranscriptScheduleError::GrindingRejected.into());
    }
    transcript.absorb(label::GRIND_NONCE, &prefix.nonce.to_le_bytes());
    if let Some(profile23) = profile23 {
        transcript.absorb(
            label::M31_STATE_ONLY_QUERY_CANDIDATE,
            &[profile23.query_selector],
        );
    }
    let (queries, query_count) = sample_queries(&mut transcript, prefix.shape)?;
    Ok(StateOnlyTranscriptScheduleResult {
        prefix: prefix_result,
        circle_ood_points,
        line_ood_points,
        mu,
        alpha,
        state_before_grinding,
        queries,
        query_count,
        state_after_queries: transcript.diagnostic_state(),
    })
}

fn run_atomic_profile21_full(
    hash: HashFn,
    prefix: &StateOnlyProfile21Prefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
    diagnostic_query_count: Option<usize>,
) -> Result<StateOnlyProfile21TranscriptScheduleResult, StateOnlyTranscriptError> {
    if prefix.base.shape != STATE_ONLY_PROFILE21_SHAPE {
        return Err(StateOnlyTranscriptError::ProfileMismatch);
    }
    let (mut transcript, prefix_result) =
        begin_atomic_schedule_v3(hash, &prefix.base, statement_digest, check_pow)?;
    let mut circle_ood_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES];
    let mut line_ood_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut mu = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut alpha = [QM31::ZERO; CANDIDATE_ROUND_COUNT];

    // The base codeword and relation are unchanged through round zero.
    for sample in 0..CANDIDATE_OOD_SAMPLES {
        circle_ood_points[sample] = transcript
            .challenge_secure_circle_point()
            .map_err(CandidateTranscriptScheduleError::from)?;
        absorb_ood(
            &mut transcript,
            label::M31_CIRCLE_OOD_VALUE,
            0,
            sample,
            prefix.base.rounds[0].ood_value(sample).unwrap(),
        );
        mu[0][sample] = transcript
            .challenge_qm31()
            .map_err(CandidateTranscriptScheduleError::from)?;
    }
    absorb_relation_sumcheck(&mut transcript, &prefix.base.rounds[0]);
    let fold_ok =
        transcript.grinding_ok(prefix.base.fold_nonces[0], RATE16_HARDENED_FOLD_POW_BITS[0]);
    if check_pow && !fold_ok {
        return Err(CandidateTranscriptScheduleError::FoldGrindingRejected { round: 0 }.into());
    }
    let mut fold_record = [0u8; 9];
    fold_record[0] = 0;
    fold_record[1..].copy_from_slice(&prefix.base.fold_nonces[0].to_le_bytes());
    transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &fold_record);
    alpha[0] = transcript
        .challenge_qm31()
        .map_err(CandidateTranscriptScheduleError::from)?;

    // Source work is positioned before delta. U and its complete claimed
    // round-zero-to-W1 seam target tau are then disclosed in that order, and
    // the already-serialized W1 root becomes binding only afterward.
    let source_ok = transcript.grinding_ok(prefix.source_nonce, MASKED_SWITCH_SOURCE_WORK_BITS);
    if check_pow && !source_ok {
        return Err(StateOnlyTranscriptError::SourceGrindingRejected);
    }
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_SOURCE_POW_NONCE,
        &prefix.source_nonce.to_le_bytes(),
    );
    let delta = sample_profile21_nonzero_delta(&mut transcript)?;
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_U, prefix.logical_u_bytes);
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_TAU, prefix.tau_bytes);
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_TRANSLATED_ROOT,
        prefix.base.rounds[1].root.unwrap(),
    );

    // W1 is the translated layer. W2 and W3 use the ordinary round-root
    // label after their preceding fold challenges.
    for round in 1..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            line_ood_points[round - 1][sample] = transcript
                .challenge_ood_qm31()
                .map_err(CandidateTranscriptScheduleError::from)?;
            absorb_ood(
                &mut transcript,
                label::M31_LINE_OOD_VALUE,
                round,
                sample,
                prefix.base.rounds[round].ood_value(sample).unwrap(),
            );
            mu[round][sample] = transcript
                .challenge_qm31()
                .map_err(CandidateTranscriptScheduleError::from)?;
        }
        absorb_relation_sumcheck(&mut transcript, &prefix.base.rounds[round]);
        let fold_ok = transcript.grinding_ok(
            prefix.base.fold_nonces[round],
            RATE16_HARDENED_FOLD_POW_BITS[round],
        );
        if check_pow && !fold_ok {
            return Err(CandidateTranscriptScheduleError::FoldGrindingRejected { round }.into());
        }
        fold_record[0] = round as u8;
        fold_record[1..].copy_from_slice(&prefix.base.fold_nonces[round].to_le_bytes());
        transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &fold_record);
        alpha[round] = transcript
            .challenge_qm31()
            .map_err(CandidateTranscriptScheduleError::from)?;
        if round + 1 < CANDIDATE_ROUND_COUNT {
            absorb_round_root(
                &mut transcript,
                round + 1,
                prefix.base.rounds[round + 1].root.unwrap(),
            );
        }
    }

    transcript.absorb(
        label::M31_CIRCLE_FINAL_TENSOR_POLY,
        prefix.base.final_polynomial_bytes,
    );
    let state_before_grinding = transcript.diagnostic_state();
    let final_ok = transcript.grinding_ok(prefix.base.nonce, STATE_ONLY_PROFILE21_GRINDING_BITS);
    if check_pow && !final_ok {
        return Err(CandidateTranscriptScheduleError::GrindingRejected.into());
    }
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_FINAL_POW_NONCE,
        &prefix.base.nonce.to_le_bytes(),
    );
    let (queries, query_count) = match diagnostic_query_count {
        Some(query_count) => {
            sample_queries_for_count(&mut transcript, prefix.base.shape, query_count)?
        }
        None => sample_queries(&mut transcript, prefix.base.shape)?,
    };
    Ok(StateOnlyProfile21TranscriptScheduleResult {
        base: StateOnlyTranscriptScheduleResult {
            prefix: prefix_result,
            circle_ood_points,
            line_ood_points,
            mu,
            alpha,
            state_before_grinding,
            queries,
            query_count,
            state_after_queries: transcript.diagnostic_state(),
        },
        delta,
    })
}

pub fn run_atomic_state_only_profile21_transcript_schedule_host_v3(
    hash: HashFn,
    prefix: &StateOnlyProfile21Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyProfile21TranscriptScheduleResult, StateOnlyTranscriptError> {
    run_atomic_profile21_full(hash, prefix, statement_digest, true, None)
}

pub fn run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
    hash: HashFn,
    prefix: &StateOnlyProfile21Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyProfile21TranscriptScheduleResult, StateOnlyTranscriptError> {
    run_atomic_profile21_full(hash, prefix, statement_digest, false, None)
}

/// Host-only replay with a diagnostic number of post-grinding queries.
///
/// This samples from the literal profile-21 post-nonce Fiat--Shamir state and
/// the literal log-19 query universe. It does not define a production profile:
/// a promoted query count still needs a distinct header/shape pin and KAT.
pub fn run_atomic_state_only_profile21_transcript_schedule_host_unmined_with_query_count_for_diagnostics_v3(
    hash: HashFn,
    prefix: &StateOnlyProfile21Prefix<'_>,
    statement_digest: &[u8; 32],
    query_count: usize,
) -> Result<StateOnlyProfile21TranscriptScheduleResult, StateOnlyTranscriptError> {
    run_atomic_profile21_full(hash, prefix, statement_digest, false, Some(query_count))
}

pub fn run_state_only_transcript_schedule_host(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyTranscriptScheduleResult, StateOnlyTranscriptError> {
    run_full_with_context(hash, prefix, statement_digest, true, false, None)
}

pub fn run_state_only_transcript_schedule_host_unmined_for_diagnostics(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyTranscriptScheduleResult, StateOnlyTranscriptError> {
    run_full_with_context(hash, prefix, statement_digest, false, false, None)
}

pub fn run_atomic_state_only_transcript_schedule_host_v3(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyTranscriptScheduleResult, StateOnlyTranscriptError> {
    run_full_with_context(hash, prefix, statement_digest, true, true, None)
}

pub fn run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
    hash: HashFn,
    prefix: &StateOnlyCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyTranscriptScheduleResult, StateOnlyTranscriptError> {
    run_full_with_context(hash, prefix, statement_digest, false, true, None)
}

pub fn run_atomic_state_only_profile23_transcript_schedule_host_v3(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyTranscriptScheduleResult, StateOnlyTranscriptError> {
    run_full_with_context(
        hash,
        &prefix.base,
        statement_digest,
        true,
        true,
        Some(prefix),
    )
}

pub fn run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
    hash: HashFn,
    prefix: &StateOnlyProfile23Prefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<StateOnlyTranscriptScheduleResult, StateOnlyTranscriptError> {
    run_full_with_context(
        hash,
        &prefix.base,
        statement_digest,
        false,
        true,
        Some(prefix),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::P;
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

    fn header(shape: StateOnlyProfileShape) -> Header {
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

    #[test]
    fn offsets_and_all_profile_headers_are_exact() {
        assert_eq!(STATE_ONLY_PREFIX_LEN, 6_736);
        assert_eq!(STATE_ONLY_PREFIX_OFFSETS.sumcheck_start, 128);
        assert_eq!(STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start, 4_608);
        assert_eq!(STATE_ONLY_PREFIX_OFFSETS.batch_nonce_start, 6_728);
        assert_eq!(STATE_ONLY_PROFILE22_PRIVATE_SHAPE.batch_grinding_bits, 38);
        assert_eq!(header(STATE_ONLY_PROFILE22_PRIVATE_SHAPE).grinding_bits, 38);
        for shape in [
            STATE_ONLY_RATE16_SHAPE,
            STATE_ONLY_RATE32_SHAPE,
            STATE_ONLY_RATE512_SHAPE,
            STATE_ONLY_PROFILE22_PRIVATE_SHAPE,
        ] {
            let mut bytes = [0u8; STATE_ONLY_PREFIX_LEN];
            header(shape).write(&mut bytes[..HEADER_LEN]);
            bytes[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] = 1;
            let parsed = StateOnlyCandidatePrefix::parse_exact(&bytes).unwrap();
            assert_eq!(parsed.shape, shape);
            assert_eq!(parsed.statement_evaluation(83), Some(QM31::ZERO));
            assert_eq!(parsed.statement_evaluation(84), None);
        }

        let mut wrong_profile22_work = [0u8; STATE_ONLY_PREFIX_LEN];
        header(STATE_ONLY_PROFILE22_PRIVATE_SHAPE).write(&mut wrong_profile22_work[..HEADER_LEN]);
        wrong_profile22_work[10] = STATE_ONLY_GRINDING_BITS;
        wrong_profile22_work[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] = 1;
        assert_eq!(
            StateOnlyCandidatePrefix::parse_exact(&wrong_profile22_work).unwrap_err(),
            CandidatePrefixError::BadHeader
        );
    }

    #[test]
    fn zero_mask_nonce_and_noncanonical_fields_reject() {
        let mut bytes = [0u8; STATE_ONLY_PREFIX_LEN];
        header(STATE_ONLY_RATE16_SHAPE).write(&mut bytes[..HEADER_LEN]);
        assert_eq!(
            StateOnlyCandidatePrefix::parse_exact(&bytes).unwrap_err(),
            CandidatePrefixError::BadHeader
        );
        bytes[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] = 1;
        bytes[STATE_ONLY_PREFIX_OFFSETS.initial_mask_claim_start..][..4]
            .copy_from_slice(&P.to_le_bytes());
        assert!(matches!(
            StateOnlyCandidatePrefix::parse_exact(&bytes),
            Err(CandidatePrefixError::NonCanonicalFieldElement { .. })
        ));
    }

    fn zero_fixture(shape: StateOnlyProfileShape) -> [u8; STATE_ONLY_PREFIX_LEN] {
        let mut bytes = [0u8; STATE_ONLY_PREFIX_LEN];
        header(shape).write(&mut bytes[..HEADER_LEN]);
        bytes[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] = shape.profile_id;
        bytes
    }

    #[test]
    fn all_profiles_replay_the_complete_unmined_schedule_and_bind_order() {
        let statement = [0x51u8; 32];
        for shape in [
            STATE_ONLY_RATE16_SHAPE,
            STATE_ONLY_RATE32_SHAPE,
            STATE_ONLY_RATE512_SHAPE,
            STATE_ONLY_PROFILE22_PRIVATE_SHAPE,
        ] {
            let bytes = zero_fixture(shape);
            let prefix = StateOnlyCandidatePrefix::parse_exact(&bytes).unwrap();
            let schedule = run_state_only_transcript_schedule_host_unmined_for_diagnostics(
                test_hash, &prefix, &statement,
            )
            .unwrap();
            assert_eq!(schedule.query_count, shape.query_count as usize);
            let mut sorted = schedule.queries[..schedule.query_count].to_vec();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), schedule.query_count);

            let mut changed_eval = bytes;
            changed_eval[STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start] = 1;
            let changed = StateOnlyCandidatePrefix::parse_exact(&changed_eval).unwrap();
            let changed_schedule =
                run_state_only_prefix_schedule_host(test_hash, &changed, &statement).unwrap();
            assert_eq!(changed_schedule.z, schedule.prefix.z);
            assert_ne!(changed_schedule.gamma, schedule.prefix.gamma);

            let mut changed_nonce = bytes;
            changed_nonce[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] ^= 0x80;
            let changed = StateOnlyCandidatePrefix::parse_exact(&changed_nonce).unwrap();
            let changed_schedule =
                run_state_only_prefix_schedule_host(test_hash, &changed, &statement).unwrap();
            assert_ne!(changed_schedule.lambda, schedule.prefix.lambda);
        }
    }

    fn profile21_zero_fixture() -> [u8; STATE_ONLY_PROFILE21_PREFIX_LEN] {
        let mut bytes = [0u8; STATE_ONLY_PROFILE21_PREFIX_LEN];
        header(STATE_ONLY_PROFILE21_SHAPE).write(&mut bytes[..HEADER_LEN]);
        bytes[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] = STATE_ONLY_PROFILE21_PROFILE_ID;
        bytes
    }

    #[test]
    fn profile21_extension_is_exact_canonical_and_beta_free() {
        assert_eq!(STATE_ONLY_PROFILE21_EXTENSION_LEN, 584);
        assert_eq!(STATE_ONLY_PROFILE21_PREFIX_LEN, 7_320);
        let bytes = profile21_zero_fixture();
        let parsed = StateOnlyProfile21Prefix::parse_exact(&bytes).unwrap();
        assert_eq!(parsed.base.shape, STATE_ONLY_PROFILE21_SHAPE);
        assert_eq!(parsed.tau(), QM31::ZERO);
        assert_eq!(parsed.logical_u(), [QM31::ZERO; MASKED_SWITCH_COEFFICIENTS]);
        assert_eq!(parsed.source_nonce, 0);
        assert_eq!(
            StateOnlyProfile21Prefix::parse_exact(&bytes[..bytes.len() - 1]).unwrap_err(),
            CandidatePrefixError::Truncated
        );

        let mut noncanonical = bytes;
        let logical_u_start = STATE_ONLY_PREFIX_LEN + CANDIDATE_NONCE_LEN;
        noncanonical[logical_u_start..logical_u_start + 4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            StateOnlyProfile21Prefix::parse_exact(&noncanonical).unwrap_err(),
            CandidatePrefixError::NonCanonicalFieldElement {
                offset: logical_u_start
            }
        );
    }

    #[test]
    fn profile21_schedule_binds_u_tau_and_translated_root_before_q16() {
        let statement = [0x71; 32];
        let bytes = profile21_zero_fixture();
        let parsed = StateOnlyProfile21Prefix::parse_exact(&bytes).unwrap();
        let schedule =
            run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &parsed, &statement,
            )
            .unwrap();
        assert_eq!(schedule.base.query_count, 16);
        let mut unique = schedule.base.queries[..schedule.base.query_count].to_vec();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(unique.len(), 16);
        assert_ne!(schedule.delta, QM31::ZERO);

        let tau_start = STATE_ONLY_PREFIX_LEN + CANDIDATE_NONCE_LEN + STATE_ONLY_PROFILE21_U_BYTES;
        let mut changed_tau = bytes;
        changed_tau[tau_start] = 1;
        let changed = StateOnlyProfile21Prefix::parse_exact(&changed_tau).unwrap();
        let changed_schedule =
            run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &changed, &statement,
            )
            .unwrap();
        assert_eq!(changed_schedule.delta, schedule.delta);
        assert_ne!(
            changed_schedule.base.line_ood_points[0],
            schedule.base.line_ood_points[0]
        );

        let mut changed_u = bytes;
        let logical_u_start = STATE_ONLY_PREFIX_LEN + CANDIDATE_NONCE_LEN;
        changed_u[logical_u_start] = 1;
        let changed = StateOnlyProfile21Prefix::parse_exact(&changed_u).unwrap();
        let changed_schedule =
            run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &changed, &statement,
            )
            .unwrap();
        assert_ne!(
            changed_schedule.base.state_after_queries,
            schedule.base.state_after_queries
        );

        let mut changed_w1 = bytes;
        changed_w1[STATE_ONLY_PREFIX_OFFSETS.rounds[1].root_start.unwrap()] ^= 1;
        let changed = StateOnlyProfile21Prefix::parse_exact(&changed_w1).unwrap();
        let changed_schedule =
            run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &changed, &statement,
            )
            .unwrap();
        assert_ne!(
            changed_schedule.base.line_ood_points[0],
            schedule.base.line_ood_points[0]
        );

        assert_eq!(
            run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash,
                &parsed.base,
                &statement
            )
            .unwrap_err(),
            StateOnlyTranscriptError::ProfileMismatch
        );
    }

    #[test]
    fn profile21_diagnostic_q18_extends_the_literal_post_nonce_schedule() {
        let statement = [0x71; 32];
        let bytes = profile21_zero_fixture();
        let parsed = StateOnlyProfile21Prefix::parse_exact(&bytes).unwrap();
        let q16 =
            run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &parsed, &statement,
            )
            .unwrap();
        let q18 = run_atomic_state_only_profile21_transcript_schedule_host_unmined_with_query_count_for_diagnostics_v3(
            test_hash,
            &parsed,
            &statement,
            18,
        )
        .unwrap();
        assert_eq!(q18.base.query_count, 18);
        assert_eq!(q18.delta, q16.delta);
        assert_eq!(q18.base.prefix, q16.base.prefix);
        assert_eq!(q18.base.circle_ood_points, q16.base.circle_ood_points);
        assert_eq!(q18.base.line_ood_points, q16.base.line_ood_points);
        assert_eq!(q18.base.mu, q16.base.mu);
        assert_eq!(q18.base.alpha, q16.base.alpha);
        assert_eq!(q18.base.queries[..16], q16.base.queries[..16]);
        let mut unique = q18.base.queries[..18].to_vec();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(unique.len(), 18);
    }

    fn profile23_zero_fixture(selector: u8) -> [u8; STATE_ONLY_PROFILE23_PREFIX_LEN] {
        let mut bytes = [0u8; STATE_ONLY_PROFILE23_PREFIX_LEN];
        header(STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE).write(&mut bytes[..HEADER_LEN]);
        bytes[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] =
            STATE_ONLY_PROFILE23_ZERO_FACTOR_PROFILE_ID;
        bytes[STATE_ONLY_PREFIX_LEN + STATE_ONLY_PROFILE23_D_CLAIMS_LEN] = selector;
        bytes
    }

    #[test]
    fn profile23_extension_and_old_new_replay_paths_fail_closed() {
        assert_eq!(STATE_ONLY_PROFILE23_EXTENSION_LEN, 49);
        assert_eq!(STATE_ONLY_PROFILE23_PREFIX_LEN, 6_785);
        let statement = [0x73; 32];
        let bytes = profile23_zero_fixture(0);
        let parsed = StateOnlyProfile23Prefix::parse_exact(&bytes).unwrap();
        assert_eq!(parsed.base.shape, STATE_ONLY_PROFILE23_ZERO_FACTOR_SHAPE);
        assert_eq!(parsed.d_claim(0), Some(QM31::ZERO));
        assert_eq!(parsed.query_selector, 0);
        let schedule =
            run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &parsed, &statement,
            )
            .unwrap();
        assert_eq!(schedule.query_count, 16);

        // The generic p22-style prefix and full replay APIs must not accept a
        // p23 base while silently omitting the dedicated D-claim absorb.
        assert_eq!(
            run_state_only_prefix_schedule_host(test_hash, &parsed.base, &statement).unwrap_err(),
            StateOnlyTranscriptError::ProfileMismatch
        );
        assert_eq!(
            run_atomic_state_only_prefix_schedule_host_v3(test_hash, &parsed.base, &statement,)
                .unwrap_err(),
            StateOnlyTranscriptError::ProfileMismatch
        );
        assert_eq!(
            run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash,
                &parsed.base,
                &statement,
            )
            .unwrap_err(),
            StateOnlyTranscriptError::ProfileMismatch
        );

        let p22_base = zero_fixture(STATE_ONLY_PROFILE22_PRIVATE_SHAPE);
        let mut wrong_profile = [0u8; STATE_ONLY_PROFILE23_PREFIX_LEN];
        wrong_profile[..STATE_ONLY_PREFIX_LEN].copy_from_slice(&p22_base);
        assert_eq!(
            StateOnlyProfile23Prefix::parse_exact(&wrong_profile).unwrap_err(),
            CandidatePrefixError::BadHeader
        );
    }

    #[test]
    fn profile23_d_claims_bind_gamma_and_q3_selector_binds_only_queries() {
        let statement = [0x73; 32];
        let base_bytes = profile23_zero_fixture(0);
        let base = StateOnlyProfile23Prefix::parse_exact(&base_bytes).unwrap();
        let schedule =
            run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &base, &statement,
            )
            .unwrap();

        let mut changed_d = base_bytes;
        changed_d[STATE_ONLY_PREFIX_LEN] = 1;
        let changed_d = StateOnlyProfile23Prefix::parse_exact(&changed_d).unwrap();
        let d_schedule =
            run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &changed_d, &statement,
            )
            .unwrap();
        assert_ne!(d_schedule.prefix.gamma, schedule.prefix.gamma);

        let selector_bytes = profile23_zero_fixture(1);
        let selector = StateOnlyProfile23Prefix::parse_exact(&selector_bytes).unwrap();
        let selector_schedule =
            run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
                test_hash, &selector, &statement,
            )
            .unwrap();
        assert_eq!(selector_schedule.prefix.gamma, schedule.prefix.gamma);
        assert_ne!(
            selector_schedule.queries[..selector_schedule.query_count],
            schedule.queries[..schedule.query_count]
        );
        assert_eq!(
            StateOnlyProfile23Prefix::parse_exact(&profile23_zero_fixture(3)).unwrap_err(),
            CandidatePrefixError::BadHeader
        );
    }
}
