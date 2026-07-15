//! Exact parser and transcript-prefix schedule for the fixed M31 circle candidate.
//!
//! The prefix entry point stops immediately after deriving `gamma`. A separate
//! host diagnostic can continue the same transcript through either of the two
//! still-unselected one-lane batching shapes and the remaining fixed schedule.
//! Neither entry point parses openings, authenticates a root, checks an
//! algebraic relation, executes a fold, or accepts a proof.

use crate::circle::SecureCirclePoint;
use crate::field::QM31;
use crate::params::{FoldPayload, MerkleMode};
use crate::proof::{
    Header, FLAG_EVALUATION_CLAIM, FLAG_M31_CIRCLE_C1_DIAGNOSTIC, FLAG_SECOND_PHASE, HEADER_LEN,
    M31_CIRCLE_BASIS_DISCRIMINATOR, ROOT_LEN, VERSION_V4_S2,
};
use crate::statement_sumcheck::{
    begin_payment_zerocheck, decode_wire, verify_payment_sumcheck_messages,
    PaymentConstraintChallenges, PaymentSumcheckWirePolynomial, PAYMENT_SUMCHECK_BYTES,
    PAYMENT_SUMCHECK_ROUNDS, PAYMENT_SUMCHECK_ROUND_BYTES,
};
use crate::sumcheck::{SUMCHECK_BYTES, SUMCHECK_COEFFICIENTS};
use crate::transcript::{
    label, ChallengeSampleExhausted, CirclePointSampleError, HashFn, OodSampleError,
    QuerySampleError, Transcript,
};

pub const CANDIDATE_PROFILE_ID: u8 = 6;
pub const CANDIDATE_LOG_ROWS: u32 = 10;
pub const CANDIDATE_LOG_BLOWUP: u32 = 2;
pub const CANDIDATE_QUERY_COUNT: u16 = 36;
pub const CANDIDATE_GRINDING_BITS: u8 = 16;
/// Measurement-only Johnson-radius profile. This is deliberately separate
/// from the selected q36/g16 candidate so its expensive literal g32 fixture
/// cannot silently re-pin the selected proof.
pub const JOHNSON_CANDIDATE_PROFILE_ID: u8 = 10;
pub const JOHNSON_CANDIDATE_QUERY_COUNT: u16 = 74;
pub const JOHNSON_CANDIDATE_GRINDING_BITS: u8 = 32;
pub const RATE16_CANDIDATE_PROFILE_ID: u8 = 11;
pub const RATE16_CANDIDATE_LOG_BLOWUP: u32 = 4;
pub const RATE16_CANDIDATE_QUERY_COUNT: u16 = 36;
pub const RATE16_CANDIDATE_GRINDING_BITS: u8 = 32;
pub const RATE16_HARDENED_CANDIDATE_PROFILE_ID: u8 = 12;
pub const RATE16_HARDENED_CANDIDATE_GRINDING_BITS: u8 = 36;
pub const RATE16_HARDENED_FOLD_POW_BITS: [u8; 4] = [39, 35, 31, 27];
pub const RATE16_PAYMENT_CANDIDATE_PROFILE_ID: u8 = 13;
pub const CANDIDATE_ROUND_COUNT: usize = 4;
pub const CANDIDATE_FINAL_POLY_LOG_LEN: u32 = 2;
pub const CANDIDATE_OOD_SAMPLES: usize = 2;
pub const CANDIDATE_STATEMENT_VALUE_COUNT: usize = 102;
pub const CANDIDATE_STATEMENT_POINT_COORDINATES: usize = 10;
pub const CANDIDATE_STATEMENT_POINT_COUNT: usize = 2;
pub const ENCODED_QM31_LEN: usize = 16;
pub const CANDIDATE_STATEMENT_EVALUATIONS_LEN: usize =
    CANDIDATE_STATEMENT_VALUE_COUNT * ENCODED_QM31_LEN;
pub const CANDIDATE_OOD_VALUES_LEN: usize = CANDIDATE_OOD_SAMPLES * ENCODED_QM31_LEN;
pub const CANDIDATE_FINAL_POLY_LEN: usize = 1 << CANDIDATE_FINAL_POLY_LOG_LEN;
pub const CANDIDATE_FINAL_POLY_BYTES: usize = CANDIDATE_FINAL_POLY_LEN * ENCODED_QM31_LEN;
pub const CANDIDATE_NONCE_LEN: usize = 8;
pub const CANDIDATE_FOLD_NONCES_LEN: usize = CANDIDATE_ROUND_COUNT * CANDIDATE_NONCE_LEN;
pub const PAYMENT_CANDIDATE_PREFIX_EXTRA_LEN: usize = PAYMENT_SUMCHECK_BYTES;
pub const CANDIDATE_STATEMENT_EVALUATIONS_DIGEST_DOMAIN: &[u8] =
    b"aspis:m31-circle:statement-evaluations:v0";

pub const CANDIDATE_FLAGS: u8 =
    FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidateProfileShape {
    pub profile_id: u8,
    pub log_blowup: u32,
    pub query_count: u16,
    pub grinding_bits: u8,
    pub fold_pow_bits: [u8; CANDIDATE_ROUND_COUNT],
}

impl CandidateProfileShape {
    pub const fn prefix_len(self) -> usize {
        CANDIDATE_PREFIX_LEN
            + if self.has_fold_pow() {
                CANDIDATE_FOLD_NONCES_LEN
            } else {
                0
            }
    }

    pub const fn has_fold_pow(self) -> bool {
        let mut round = 0;
        while round < CANDIDATE_ROUND_COUNT {
            if self.fold_pow_bits[round] != 0 {
                return true;
            }
            round += 1;
        }
        false
    }
}

pub const SELECTED_CANDIDATE_SHAPE: CandidateProfileShape = CandidateProfileShape {
    profile_id: CANDIDATE_PROFILE_ID,
    log_blowup: CANDIDATE_LOG_BLOWUP,
    query_count: CANDIDATE_QUERY_COUNT,
    grinding_bits: CANDIDATE_GRINDING_BITS,
    fold_pow_bits: [0; CANDIDATE_ROUND_COUNT],
};

pub const JOHNSON_CANDIDATE_SHAPE: CandidateProfileShape = CandidateProfileShape {
    profile_id: JOHNSON_CANDIDATE_PROFILE_ID,
    log_blowup: CANDIDATE_LOG_BLOWUP,
    query_count: JOHNSON_CANDIDATE_QUERY_COUNT,
    grinding_bits: JOHNSON_CANDIDATE_GRINDING_BITS,
    fold_pow_bits: [0; CANDIDATE_ROUND_COUNT],
};

pub const RATE16_CANDIDATE_SHAPE: CandidateProfileShape = CandidateProfileShape {
    profile_id: RATE16_CANDIDATE_PROFILE_ID,
    log_blowup: RATE16_CANDIDATE_LOG_BLOWUP,
    query_count: RATE16_CANDIDATE_QUERY_COUNT,
    grinding_bits: RATE16_CANDIDATE_GRINDING_BITS,
    fold_pow_bits: [0; CANDIDATE_ROUND_COUNT],
};

pub const RATE16_HARDENED_CANDIDATE_SHAPE: CandidateProfileShape = CandidateProfileShape {
    profile_id: RATE16_HARDENED_CANDIDATE_PROFILE_ID,
    log_blowup: RATE16_CANDIDATE_LOG_BLOWUP,
    query_count: RATE16_CANDIDATE_QUERY_COUNT,
    grinding_bits: RATE16_HARDENED_CANDIDATE_GRINDING_BITS,
    fold_pow_bits: RATE16_HARDENED_FOLD_POW_BITS,
};

pub const RATE16_PAYMENT_CANDIDATE_SHAPE: CandidateProfileShape = CandidateProfileShape {
    profile_id: RATE16_PAYMENT_CANDIDATE_PROFILE_ID,
    log_blowup: RATE16_CANDIDATE_LOG_BLOWUP,
    query_count: RATE16_CANDIDATE_QUERY_COUNT,
    grinding_bits: RATE16_HARDENED_CANDIDATE_GRINDING_BITS,
    fold_pow_bits: RATE16_HARDENED_FOLD_POW_BITS,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidateRoundOffsets {
    pub record_start: usize,
    pub root_start: Option<usize>,
    pub ood_values_start: usize,
    pub sumcheck_start: usize,
    pub record_end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidatePrefixOffsets {
    pub header_start: usize,
    pub c1_root_start: usize,
    pub c2_root_start: usize,
    pub statement_evaluations_start: usize,
    pub rounds: [CandidateRoundOffsets; CANDIDATE_ROUND_COUNT],
    pub final_polynomial_start: usize,
    pub nonce_start: usize,
    pub openings_start: usize,
}

pub const CANDIDATE_PREFIX_OFFSETS: CandidatePrefixOffsets = CandidatePrefixOffsets {
    header_start: 0,
    c1_root_start: 16,
    c2_root_start: 48,
    statement_evaluations_start: 80,
    rounds: [
        CandidateRoundOffsets {
            record_start: 1_712,
            root_start: None,
            ood_values_start: 1_712,
            sumcheck_start: 1_744,
            record_end: 1_856,
        },
        CandidateRoundOffsets {
            record_start: 1_856,
            root_start: Some(1_856),
            ood_values_start: 1_888,
            sumcheck_start: 1_920,
            record_end: 2_032,
        },
        CandidateRoundOffsets {
            record_start: 2_032,
            root_start: Some(2_032),
            ood_values_start: 2_064,
            sumcheck_start: 2_096,
            record_end: 2_208,
        },
        CandidateRoundOffsets {
            record_start: 2_208,
            root_start: Some(2_208),
            ood_values_start: 2_240,
            sumcheck_start: 2_272,
            record_end: 2_384,
        },
    ],
    final_polynomial_start: 2_384,
    nonce_start: 2_448,
    openings_start: 2_456,
};

pub const CANDIDATE_PREFIX_LEN: usize = CANDIDATE_PREFIX_OFFSETS.openings_start;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidatePrefixError {
    Truncated,
    TrailingBytes,
    BadHeader,
    NonCanonicalFieldElement { offset: usize },
}

#[derive(Clone, Copy, Debug)]
pub struct CandidateRoundRecord<'a> {
    pub layer: u8,
    pub start_offset: usize,
    pub root: Option<&'a [u8; ROOT_LEN]>,
    pub ood_value_bytes: &'a [u8; CANDIDATE_OOD_VALUES_LEN],
    pub sumcheck_bytes: &'a [u8; SUMCHECK_BYTES],
    pub record_bytes: &'a [u8],
}

impl CandidateRoundRecord<'_> {
    pub fn ood_value(&self, sample: usize) -> Option<QM31> {
        let start = sample.checked_mul(ENCODED_QM31_LEN)?;
        QM31::from_le_bytes(self.ood_value_bytes.get(start..start + ENCODED_QM31_LEN)?)
    }

    pub fn sumcheck_coefficient(&self, coefficient: usize) -> Option<QM31> {
        if coefficient >= SUMCHECK_COEFFICIENTS {
            return None;
        }
        let start = coefficient * ENCODED_QM31_LEN;
        QM31::from_le_bytes(&self.sumcheck_bytes[start..start + ENCODED_QM31_LEN])
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CandidatePrefix<'a> {
    pub header: Header,
    pub header_bytes: &'a [u8; HEADER_LEN],
    pub c1_root: &'a [u8; ROOT_LEN],
    pub c2_root: &'a [u8; ROOT_LEN],
    pub statement_evaluations_bytes: &'a [u8; CANDIDATE_STATEMENT_EVALUATIONS_LEN],
    pub rounds: [CandidateRoundRecord<'a>; CANDIDATE_ROUND_COUNT],
    pub final_polynomial_bytes: &'a [u8; CANDIDATE_FINAL_POLY_BYTES],
    pub nonce: u64,
    pub fold_nonces: [u64; CANDIDATE_ROUND_COUNT],
}

#[derive(Clone, Copy, Debug)]
pub struct PaymentCandidatePrefix<'a> {
    pub candidate: CandidatePrefix<'a>,
    pub payment_sumcheck_bytes: &'a [u8; PAYMENT_SUMCHECK_BYTES],
}

impl<'a> PaymentCandidatePrefix<'a> {
    pub const fn prefix_len() -> usize {
        RATE16_PAYMENT_CANDIDATE_SHAPE.prefix_len() + PAYMENT_CANDIDATE_PREFIX_EXTRA_LEN
    }

    pub fn parse_from_proof(bytes: &'a [u8]) -> Result<(Self, &'a [u8]), CandidatePrefixError> {
        let base_len = RATE16_PAYMENT_CANDIDATE_SHAPE.prefix_len();
        let prefix_len = Self::prefix_len();
        if bytes.len() < prefix_len {
            return Err(CandidatePrefixError::Truncated);
        }
        let candidate = CandidatePrefix::parse_exact_for_shape(
            &bytes[..base_len],
            RATE16_PAYMENT_CANDIDATE_SHAPE,
        )?;
        let payment_sumcheck_bytes: &[u8; PAYMENT_SUMCHECK_BYTES] =
            bytes[base_len..prefix_len].try_into().unwrap();
        for round in 0..PAYMENT_SUMCHECK_ROUNDS {
            let start = round * PAYMENT_SUMCHECK_ROUND_BYTES;
            if decode_wire(&payment_sumcheck_bytes[start..start + PAYMENT_SUMCHECK_ROUND_BYTES])
                .is_none()
            {
                return Err(CandidatePrefixError::NonCanonicalFieldElement {
                    offset: base_len + start,
                });
            }
        }
        Ok((
            Self {
                candidate,
                payment_sumcheck_bytes,
            },
            &bytes[prefix_len..],
        ))
    }

    pub fn payment_sumcheck_messages(
        &self,
    ) -> Option<[PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS]> {
        let mut messages = [[QM31::ZERO;
            crate::statement_sumcheck::PAYMENT_SUMCHECK_WIRE_COEFFICIENTS];
            PAYMENT_SUMCHECK_ROUNDS];
        for (round, message) in messages.iter_mut().enumerate() {
            let start = round * PAYMENT_SUMCHECK_ROUND_BYTES;
            *message = decode_wire(
                &self.payment_sumcheck_bytes[start..start + PAYMENT_SUMCHECK_ROUND_BYTES],
            )?;
        }
        Some(messages)
    }
}

impl<'a> CandidatePrefix<'a> {
    /// Parse exactly the candidate prefix. Any opening bytes are trailing data
    /// here and reject; use [`Self::parse_from_proof`] to expose them without
    /// interpreting or authenticating them.
    pub fn parse_exact(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        Self::parse_exact_for_shape(bytes, SELECTED_CANDIDATE_SHAPE)
    }

    /// Parse a candidate prefix under an explicitly selected diagnostic
    /// profile shape. The fixed algebraic layout remains identical; only the
    /// transcript-bound profile id, query count, and grinding threshold vary.
    pub fn parse_exact_for_shape(
        bytes: &'a [u8],
        shape: CandidateProfileShape,
    ) -> Result<Self, CandidatePrefixError> {
        match bytes.len().cmp(&shape.prefix_len()) {
            core::cmp::Ordering::Less => return Err(CandidatePrefixError::Truncated),
            core::cmp::Ordering::Greater => return Err(CandidatePrefixError::TrailingBytes),
            core::cmp::Ordering::Equal => {}
        }
        Self::parse_prefix(bytes, shape)
    }

    /// Parse the fixed prefix from a larger candidate byte string and return
    /// the uninterpreted remainder. This function does not validate openings.
    pub fn parse_from_proof(bytes: &'a [u8]) -> Result<(Self, &'a [u8]), CandidatePrefixError> {
        Self::parse_from_proof_for_shape(bytes, SELECTED_CANDIDATE_SHAPE)
    }

    pub fn parse_from_proof_for_shape(
        bytes: &'a [u8],
        shape: CandidateProfileShape,
    ) -> Result<(Self, &'a [u8]), CandidatePrefixError> {
        let prefix_len = shape.prefix_len();
        if bytes.len() < prefix_len {
            return Err(CandidatePrefixError::Truncated);
        }
        let (prefix, openings) = bytes.split_at(prefix_len);
        Ok((Self::parse_prefix(prefix, shape)?, openings))
    }

    fn parse_prefix(
        bytes: &'a [u8],
        shape: CandidateProfileShape,
    ) -> Result<Self, CandidatePrefixError> {
        debug_assert_eq!(bytes.len(), shape.prefix_len());
        let header_bytes = array_at::<HEADER_LEN>(bytes, CANDIDATE_PREFIX_OFFSETS.header_start);
        let header = Header::parse(header_bytes).ok_or(CandidatePrefixError::BadHeader)?;
        if !is_exact_candidate_header(&header, shape) {
            return Err(CandidatePrefixError::BadHeader);
        }

        validate_field_block(
            bytes,
            CANDIDATE_PREFIX_OFFSETS.statement_evaluations_start,
            CANDIDATE_STATEMENT_VALUE_COUNT,
        )?;
        for round in CANDIDATE_PREFIX_OFFSETS.rounds {
            validate_field_block(bytes, round.ood_values_start, CANDIDATE_OOD_SAMPLES)?;
            validate_field_block(bytes, round.sumcheck_start, SUMCHECK_COEFFICIENTS)?;
        }
        validate_field_block(
            bytes,
            CANDIDATE_PREFIX_OFFSETS.final_polynomial_start,
            CANDIDATE_FINAL_POLY_LEN,
        )?;

        let rounds = core::array::from_fn(|layer| {
            let offsets = CANDIDATE_PREFIX_OFFSETS.rounds[layer];
            CandidateRoundRecord {
                layer: layer as u8,
                start_offset: offsets.record_start,
                root: offsets.root_start.map(|start| array_at(bytes, start)),
                ood_value_bytes: array_at(bytes, offsets.ood_values_start),
                sumcheck_bytes: array_at(bytes, offsets.sumcheck_start),
                record_bytes: &bytes[offsets.record_start..offsets.record_end],
            }
        });

        let fold_nonces = if shape.has_fold_pow() {
            core::array::from_fn(|round| {
                let start = CANDIDATE_PREFIX_LEN + round * CANDIDATE_NONCE_LEN;
                u64::from_le_bytes(
                    bytes[start..start + CANDIDATE_NONCE_LEN]
                        .try_into()
                        .unwrap(),
                )
            })
        } else {
            [0; CANDIDATE_ROUND_COUNT]
        };

        Ok(Self {
            header,
            header_bytes,
            c1_root: array_at(bytes, CANDIDATE_PREFIX_OFFSETS.c1_root_start),
            c2_root: array_at(bytes, CANDIDATE_PREFIX_OFFSETS.c2_root_start),
            statement_evaluations_bytes: array_at(
                bytes,
                CANDIDATE_PREFIX_OFFSETS.statement_evaluations_start,
            ),
            rounds,
            final_polynomial_bytes: array_at(
                bytes,
                CANDIDATE_PREFIX_OFFSETS.final_polynomial_start,
            ),
            nonce: u64::from_le_bytes(
                bytes[CANDIDATE_PREFIX_OFFSETS.nonce_start
                    ..CANDIDATE_PREFIX_OFFSETS.nonce_start + CANDIDATE_NONCE_LEN]
                    .try_into()
                    .unwrap(),
            ),
            fold_nonces,
        })
    }

    pub fn statement_evaluation(&self, index: usize) -> Option<QM31> {
        let start = index.checked_mul(ENCODED_QM31_LEN)?;
        QM31::from_le_bytes(
            self.statement_evaluations_bytes
                .get(start..start + ENCODED_QM31_LEN)?,
        )
    }

    pub fn final_coefficient(&self, index: usize) -> Option<QM31> {
        let start = index.checked_mul(ENCODED_QM31_LEN)?;
        QM31::from_le_bytes(
            self.final_polynomial_bytes
                .get(start..start + ENCODED_QM31_LEN)?,
        )
    }
}

fn array_at<const N: usize>(bytes: &[u8], start: usize) -> &[u8; N] {
    bytes[start..start + N].try_into().unwrap()
}

fn is_exact_candidate_header(header: &Header, shape: CandidateProfileShape) -> bool {
    header.version == VERSION_V4_S2
        && header.profile_id == shape.profile_id
        && header.log_rows == CANDIDATE_LOG_ROWS
        && header.log_blowup == shape.log_blowup
        && header.query_count == shape.query_count
        && header.grinding_bits == shape.grinding_bits
        && header.fold_payload == FoldPayload::RawFibers as u8
        && header.merkle_mode == MerkleMode::Radix4MinimalSubtree as u8
        && header.num_rounds == CANDIDATE_ROUND_COUNT as u32
        && header.final_poly_log_len == CANDIDATE_FINAL_POLY_LOG_LEN
        && header.flags == CANDIDATE_FLAGS
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidatePrefixScheduleResult {
    pub lambda: QM31,
    pub chi: QM31,
    pub gamma: QM31,
    /// Diagnostic evidence only. This is not a wire field or a KAT pin.
    pub state_after_gamma: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentCandidatePrefixScheduleResult {
    pub lambda: QM31,
    pub chi: QM31,
    pub batching: PaymentConstraintChallenges,
    pub z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    pub payment_terminal_claim: QM31,
    pub gamma: QM31,
    pub state_after_gamma: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentCandidateTranscriptScheduleResult<
    const QUERY_COUNT: usize = { RATE16_CANDIDATE_QUERY_COUNT as usize },
> {
    pub prefix: PaymentCandidatePrefixScheduleResult,
    pub kappa: QM31,
    pub second_point_scale: QM31,
    pub circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    pub line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    pub mu: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub alpha: [QM31; CANDIDATE_ROUND_COUNT],
    pub state_before_grinding: [u8; 32],
    pub queries: [u32; QUERY_COUNT],
    pub state_after_queries: [u8; 32],
}

struct CandidatePrefixTranscript {
    transcript: Transcript,
    result: CandidatePrefixScheduleResult,
}

/// Run the candidate host transcript only through `gamma`.
///
/// The function intentionally has no batching challenge and consumes no OOD,
/// sumcheck, final-polynomial, nonce, or opening bytes.
pub fn run_candidate_prefix_schedule_host(
    hash: HashFn,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> Result<CandidatePrefixScheduleResult, ChallengeSampleExhausted> {
    Ok(begin_candidate_prefix_schedule_host(hash, prefix, statement_digest, z)?.result)
}

fn begin_candidate_prefix_schedule_host(
    hash: HashFn,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> Result<CandidatePrefixTranscript, ChallengeSampleExhausted> {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, prefix.header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);

    let mut c1_root_record = [0u8; 1 + ROOT_LEN];
    c1_root_record[1..].copy_from_slice(prefix.c1_root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &c1_root_record);

    let lambda = transcript.challenge_qm31()?;
    let chi = transcript.challenge_qm31()?;

    transcript.absorb(label::M31_CIRCLE_C2_ROOT, prefix.c2_root);

    let points = encode_statement_points(z);
    transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &points);
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        prefix.statement_evaluations_bytes,
    );
    let gamma = transcript.challenge_qm31()?;

    let result = CandidatePrefixScheduleResult {
        lambda,
        chi,
        gamma,
        state_after_gamma: transcript.diagnostic_state(),
    };
    Ok(CandidatePrefixTranscript { transcript, result })
}

pub fn encode_payment_statement_points(
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> [u8; CANDIDATE_STATEMENT_POINT_COUNT * CANDIDATE_STATEMENT_POINT_COORDINATES * ENCODED_QM31_LEN]
{
    let mut shifted = *z;
    for bit in [0usize, 1, 3] {
        let coordinate = CANDIDATE_STATEMENT_POINT_COORDINATES - 1 - bit;
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    let points = [*z, shifted];
    let mut bytes = [0u8; CANDIDATE_STATEMENT_POINT_COUNT
        * CANDIDATE_STATEMENT_POINT_COORDINATES
        * ENCODED_QM31_LEN];
    for (point, coordinates) in points.iter().enumerate() {
        for (coordinate, value) in coordinates.iter().enumerate() {
            let index = point * CANDIDATE_STATEMENT_POINT_COORDINATES + coordinate;
            value.write_le_bytes(&mut bytes[index * ENCODED_QM31_LEN..][..ENCODED_QM31_LEN]);
        }
    }
    bytes
}

/// Production prefix schedule: C1 -> (lambda,chi) -> C2 -> payment
/// zerocheck -> derived z -> 102 values -> gamma.
#[cfg(not(target_os = "solana"))]
pub fn run_payment_candidate_prefix_schedule_host(
    hash: HashFn,
    prefix: &PaymentCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<PaymentCandidatePrefixScheduleResult, ChallengeSampleExhausted> {
    Ok(begin_payment_candidate_prefix_schedule_host(hash, prefix, statement_digest)?.1)
}

#[cfg(not(target_os = "solana"))]
fn begin_payment_candidate_prefix_schedule_host(
    hash: HashFn,
    prefix: &PaymentCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<(Transcript, PaymentCandidatePrefixScheduleResult), ChallengeSampleExhausted> {
    let candidate = &prefix.candidate;
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, candidate.header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);
    let mut c1_root_record = [0u8; 1 + ROOT_LEN];
    c1_root_record[1..].copy_from_slice(candidate.c1_root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &c1_root_record);
    let lambda = transcript.challenge_qm31()?;
    let chi = transcript.challenge_qm31()?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, candidate.c2_root);
    let batching = begin_payment_zerocheck(&mut transcript)?;
    let messages = prefix
        .payment_sumcheck_messages()
        .expect("parser validated payment sumcheck fields");
    let verified = verify_payment_sumcheck_messages(&mut transcript, &messages)?;
    let z = verified.point;
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_POINTS,
        &encode_payment_statement_points(&z),
    );
    transcript.absorb(
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        candidate.statement_evaluations_bytes,
    );
    let gamma = transcript.challenge_qm31()?;
    let result = PaymentCandidatePrefixScheduleResult {
        lambda,
        chi,
        batching,
        z,
        payment_terminal_claim: verified.terminal_claim,
        gamma,
        state_after_gamma: transcript.diagnostic_state(),
    };
    Ok((transcript, result))
}

#[cfg(not(target_os = "solana"))]
pub fn run_payment_candidate_transcript_schedule_host<const QUERY_COUNT: usize>(
    hash: HashFn,
    prefix: &PaymentCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<PaymentCandidateTranscriptScheduleResult<QUERY_COUNT>, CandidateTranscriptScheduleError>
{
    if QUERY_COUNT != usize::from(RATE16_PAYMENT_CANDIDATE_SHAPE.query_count) {
        return Err(CandidateTranscriptScheduleError::ChallengeSampleExhausted);
    }
    let (mut transcript, prefix_result) =
        begin_payment_candidate_prefix_schedule_host(hash, prefix, statement_digest)?;
    let kappa = transcript.challenge_qm31()?;
    let second_point_scale = kappa;
    let candidate = &prefix.candidate;
    let mut circle_ood_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES];
    let mut line_ood_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut mu = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut alpha = [QM31::ZERO; CANDIDATE_ROUND_COUNT];

    for sample in 0..CANDIDATE_OOD_SAMPLES {
        circle_ood_points[sample] = transcript.challenge_secure_circle_point()?;
        absorb_candidate_ood_value(
            &mut transcript,
            label::M31_CIRCLE_OOD_VALUE,
            0,
            sample,
            candidate.rounds[0].ood_value(sample).unwrap(),
        );
        mu[0][sample] = transcript.challenge_qm31()?;
    }
    absorb_candidate_sumcheck(&mut transcript, &candidate.rounds[0]);
    check_and_absorb_candidate_fold_pow(
        &mut transcript,
        candidate,
        CandidateOneLaneBatchingMode::FreshKappa,
        0,
    )?;
    alpha[0] = transcript.challenge_qm31()?;

    for layer in 1..CANDIDATE_ROUND_COUNT {
        absorb_candidate_round_root(
            &mut transcript,
            layer,
            candidate.rounds[layer].root.unwrap(),
        );
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            line_ood_points[layer - 1][sample] = transcript.challenge_ood_qm31()?;
            absorb_candidate_ood_value(
                &mut transcript,
                label::M31_LINE_OOD_VALUE,
                layer,
                sample,
                candidate.rounds[layer].ood_value(sample).unwrap(),
            );
            mu[layer][sample] = transcript.challenge_qm31()?;
        }
        absorb_candidate_sumcheck(&mut transcript, &candidate.rounds[layer]);
        check_and_absorb_candidate_fold_pow(
            &mut transcript,
            candidate,
            CandidateOneLaneBatchingMode::FreshKappa,
            layer,
        )?;
        alpha[layer] = transcript.challenge_qm31()?;
    }
    absorb_candidate_final(&mut transcript, candidate);
    let state_before_grinding = transcript.diagnostic_state();
    if !transcript.grinding_ok(
        candidate.nonce,
        RATE16_PAYMENT_CANDIDATE_SHAPE.grinding_bits,
    ) {
        return Err(CandidateTranscriptScheduleError::GrindingRejected);
    }
    transcript.absorb(label::GRIND_NONCE, &candidate.nonce.to_le_bytes());
    let query_log_size = candidate.header.log_rows + candidate.header.log_blowup - 2;
    let queries: [u32; QUERY_COUNT] = transcript
        .challenge_queries(QUERY_COUNT, 1u32 << query_log_size)
        .try_into()
        .unwrap();
    Ok(PaymentCandidateTranscriptScheduleResult {
        prefix: prefix_result,
        kappa,
        second_point_scale,
        circle_ood_points,
        line_ood_points,
        mu,
        alpha,
        state_before_grinding,
        queries,
        state_after_queries: transcript.diagnostic_state(),
    })
}

/// The two one-lane shapes retained for transcript-tail comparison. Their
/// presence here is diagnostic evidence, not a protocol selection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidateOneLaneBatchingMode {
    FreshKappa,
    DisjointGamma51,
}

impl CandidateOneLaneBatchingMode {
    pub const ALL: [Self; 2] = [Self::FreshKappa, Self::DisjointGamma51];
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidateTranscriptScheduleError {
    ChallengeSampleExhausted,
    CirclePointSample(CirclePointSampleError),
    LinePointSample(OodSampleError),
    QuerySample(QuerySampleError),
    BatchGrindingRejected,
    GrindingRejected,
    FoldGrindingRejected { round: usize },
}

impl From<ChallengeSampleExhausted> for CandidateTranscriptScheduleError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

impl From<CirclePointSampleError> for CandidateTranscriptScheduleError {
    fn from(error: CirclePointSampleError) -> Self {
        Self::CirclePointSample(error)
    }
}

impl From<OodSampleError> for CandidateTranscriptScheduleError {
    fn from(error: OodSampleError) -> Self {
        Self::LinePointSample(error)
    }
}

impl From<QuerySampleError> for CandidateTranscriptScheduleError {
    fn from(error: QuerySampleError) -> Self {
        Self::QuerySample(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidateTranscriptScheduleResult<
    const QUERY_COUNT: usize = { CANDIDATE_QUERY_COUNT as usize },
> {
    pub prefix: CandidatePrefixScheduleResult,
    pub batching_mode: CandidateOneLaneBatchingMode,
    /// Present only for the fresh-kappa diagnostic shape.
    pub kappa: Option<QM31>,
    /// `kappa` or `gamma^51`, according to the diagnostic shape.
    pub second_point_scale: QM31,
    pub circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    pub line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    pub mu: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub alpha: [QM31; CANDIDATE_ROUND_COUNT],
    pub state_before_grinding: [u8; 32],
    pub queries: [u32; QUERY_COUNT],
    pub state_after_queries: [u8; 32],
}

#[derive(Clone, Copy)]
struct CandidateTailChallenges {
    prefix: CandidatePrefixScheduleResult,
    batching_mode: CandidateOneLaneBatchingMode,
    kappa: Option<QM31>,
    second_point_scale: QM31,
    circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    mu: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    alpha: [QM31; CANDIDATE_ROUND_COUNT],
}

/// Continue the candidate host transcript through the complete fixed schedule.
///
/// This is transcript evidence only. It verifies the grinding witness because
/// query positions are unavailable before that check, but performs no Merkle,
/// OOD-value, sumcheck, fold, terminal, or statement relation verification.
pub fn run_candidate_transcript_schedule_host(
    hash: HashFn,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    batching_mode: CandidateOneLaneBatchingMode,
) -> Result<CandidateTranscriptScheduleResult, CandidateTranscriptScheduleError> {
    run_candidate_transcript_schedule_host_for_shape::<{ CANDIDATE_QUERY_COUNT as usize }>(
        hash,
        prefix,
        statement_digest,
        z,
        batching_mode,
        CANDIDATE_GRINDING_BITS,
    )
}

pub fn run_candidate_transcript_schedule_host_for_shape<const QUERY_COUNT: usize>(
    hash: HashFn,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    batching_mode: CandidateOneLaneBatchingMode,
    grinding_bits: u8,
) -> Result<CandidateTranscriptScheduleResult<QUERY_COUNT>, CandidateTranscriptScheduleError> {
    let (mut transcript, challenges) =
        candidate_transcript_before_grinding(hash, prefix, statement_digest, z, batching_mode)?;
    let state_before_grinding = transcript.diagnostic_state();
    if !transcript.grinding_ok(prefix.nonce, grinding_bits) {
        return Err(CandidateTranscriptScheduleError::GrindingRejected);
    }
    transcript.absorb(label::GRIND_NONCE, &prefix.nonce.to_le_bytes());
    let query_log_size = prefix
        .header
        .log_rows
        .checked_add(prefix.header.log_blowup)
        .and_then(|value| value.checked_sub(2))
        .unwrap();
    let queries: [u32; QUERY_COUNT] = transcript
        .challenge_queries(QUERY_COUNT, 1u32 << query_log_size)
        .try_into()
        .unwrap();

    Ok(CandidateTranscriptScheduleResult {
        prefix: challenges.prefix,
        batching_mode: challenges.batching_mode,
        kappa: challenges.kappa,
        second_point_scale: challenges.second_point_scale,
        circle_ood_points: challenges.circle_ood_points,
        line_ood_points: challenges.line_ood_points,
        mu: challenges.mu,
        alpha: challenges.alpha,
        state_before_grinding,
        queries,
        state_after_queries: transcript.diagnostic_state(),
    })
}

fn candidate_transcript_before_grinding(
    hash: HashFn,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    batching_mode: CandidateOneLaneBatchingMode,
) -> Result<(Transcript, CandidateTailChallenges), CandidateTranscriptScheduleError> {
    let CandidatePrefixTranscript {
        mut transcript,
        result: prefix_result,
    } = begin_candidate_prefix_schedule_host(hash, prefix, statement_digest, z)?;

    let kappa = match batching_mode {
        CandidateOneLaneBatchingMode::FreshKappa => Some(transcript.challenge_qm31()?),
        CandidateOneLaneBatchingMode::DisjointGamma51 => None,
    };
    let second_point_scale = kappa.unwrap_or_else(|| prefix_result.gamma.pow(51));

    let mut circle_ood_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES];
    let mut line_ood_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut mu = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut alpha = [QM31::ZERO; CANDIDATE_ROUND_COUNT];

    for sample in 0..CANDIDATE_OOD_SAMPLES {
        circle_ood_points[sample] = transcript.challenge_secure_circle_point()?;
        absorb_candidate_ood_value(
            &mut transcript,
            label::M31_CIRCLE_OOD_VALUE,
            0,
            sample,
            prefix.rounds[0].ood_value(sample).unwrap(),
        );
        mu[0][sample] = transcript.challenge_qm31()?;
    }
    absorb_candidate_sumcheck(&mut transcript, &prefix.rounds[0]);
    check_and_absorb_candidate_fold_pow(&mut transcript, prefix, batching_mode, 0)?;
    alpha[0] = transcript.challenge_qm31()?;

    for layer in 1..CANDIDATE_ROUND_COUNT {
        absorb_candidate_round_root(&mut transcript, layer, prefix.rounds[layer].root.unwrap());
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            line_ood_points[layer - 1][sample] = transcript.challenge_ood_qm31()?;
            absorb_candidate_ood_value(
                &mut transcript,
                label::M31_LINE_OOD_VALUE,
                layer,
                sample,
                prefix.rounds[layer].ood_value(sample).unwrap(),
            );
            mu[layer][sample] = transcript.challenge_qm31()?;
        }
        absorb_candidate_sumcheck(&mut transcript, &prefix.rounds[layer]);
        check_and_absorb_candidate_fold_pow(&mut transcript, prefix, batching_mode, layer)?;
        alpha[layer] = transcript.challenge_qm31()?;
    }

    absorb_candidate_final(&mut transcript, prefix);
    Ok((
        transcript,
        CandidateTailChallenges {
            prefix: prefix_result,
            batching_mode,
            kappa,
            second_point_scale,
            circle_ood_points,
            line_ood_points,
            mu,
            alpha,
        },
    ))
}

fn check_and_absorb_candidate_fold_pow(
    transcript: &mut Transcript,
    prefix: &CandidatePrefix<'_>,
    _batching_mode: CandidateOneLaneBatchingMode,
    round: usize,
) -> Result<(), CandidateTranscriptScheduleError> {
    // The profile id in the already-absorbed header uniquely selects this
    // difficulty schedule. A zero-difficulty legacy shape carries no nonce
    // record, preserving every historical transcript byte-for-byte.
    let shape = match prefix.header.profile_id {
        RATE16_HARDENED_CANDIDATE_PROFILE_ID => RATE16_HARDENED_CANDIDATE_SHAPE,
        RATE16_PAYMENT_CANDIDATE_PROFILE_ID => RATE16_PAYMENT_CANDIDATE_SHAPE,
        _ => return Ok(()),
    };
    let bits = shape.fold_pow_bits[round];
    let nonce = prefix.fold_nonces[round];
    if !transcript.grinding_ok(nonce, bits) {
        return Err(CandidateTranscriptScheduleError::FoldGrindingRejected { round });
    }
    absorb_candidate_fold_pow(transcript, round, nonce);
    Ok(())
}

fn absorb_candidate_fold_pow(transcript: &mut Transcript, round: usize, nonce: u64) {
    let mut record = [0u8; 1 + CANDIDATE_NONCE_LEN];
    record[0] = round as u8;
    record[1..].copy_from_slice(&nonce.to_le_bytes());
    transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
}

fn absorb_candidate_round_root(transcript: &mut Transcript, layer: usize, root: &[u8; ROOT_LEN]) {
    let mut record = [0u8; 1 + ROOT_LEN];
    record[0] = layer as u8;
    record[1..].copy_from_slice(root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
}

fn absorb_candidate_ood_value(
    transcript: &mut Transcript,
    ood_label: u8,
    layer: usize,
    sample: usize,
    value: QM31,
) {
    let mut record = [0u8; 2 + ENCODED_QM31_LEN];
    record[0] = layer as u8;
    record[1] = sample as u8;
    value.write_le_bytes(&mut record[2..]);
    transcript.absorb(ood_label, &record);
}

fn absorb_candidate_sumcheck(transcript: &mut Transcript, round: &CandidateRoundRecord<'_>) {
    let mut record = [0u8; 1 + SUMCHECK_BYTES];
    record[0] = round.layer;
    for coefficient in 0..SUMCHECK_COEFFICIENTS {
        round
            .sumcheck_coefficient(coefficient)
            .unwrap()
            .write_le_bytes(
                &mut record
                    [1 + coefficient * ENCODED_QM31_LEN..1 + (coefficient + 1) * ENCODED_QM31_LEN],
            );
    }
    transcript.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &record);
}

fn absorb_candidate_final(transcript: &mut Transcript, prefix: &CandidatePrefix<'_>) {
    let mut coefficients = [0u8; CANDIDATE_FINAL_POLY_BYTES];
    for index in 0..CANDIDATE_FINAL_POLY_LEN {
        prefix.final_coefficient(index).unwrap().write_le_bytes(
            &mut coefficients[index * ENCODED_QM31_LEN..(index + 1) * ENCODED_QM31_LEN],
        );
    }
    transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, &coefficients);
}

fn encode_statement_points(
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> [u8; CANDIDATE_STATEMENT_POINT_COUNT * CANDIDATE_STATEMENT_POINT_COORDINATES * ENCODED_QM31_LEN]
{
    let mut points = [0u8; CANDIDATE_STATEMENT_POINT_COUNT
        * CANDIDATE_STATEMENT_POINT_COORDINATES
        * ENCODED_QM31_LEN];
    for (index, value) in z.iter().enumerate() {
        value.write_le_bytes(&mut points[index * ENCODED_QM31_LEN..][..ENCODED_QM31_LEN]);
    }
    for (index, value) in z.iter().enumerate() {
        let value = if index >= CANDIDATE_STATEMENT_POINT_COORDINATES - 2 {
            QM31::ONE.sub(*value)
        } else {
            *value
        };
        let point_index = CANDIDATE_STATEMENT_POINT_COORDINATES + index;
        value.write_le_bytes(&mut points[point_index * ENCODED_QM31_LEN..][..ENCODED_QM31_LEN]);
    }
    points
}

/// Bind the external point pair and the proof-carried 102-value block to the
/// tag-24 instruction argument. This diagnostic digest is not a payment
/// statement and does not replace transcript absorption of the same bytes.
pub fn candidate_statement_evaluations_digest(
    hash: HashFn,
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    statement_evaluations_bytes: &[u8; CANDIDATE_STATEMENT_EVALUATIONS_LEN],
) -> [u8; 32] {
    let points = encode_statement_points(z);
    hash(&[
        CANDIDATE_STATEMENT_EVALUATIONS_DIGEST_DOMAIN,
        &points,
        statement_evaluations_bytes,
    ])
}
