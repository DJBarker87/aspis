//! Fixed one-mask+C1-padding prefix and Fiat--Shamir schedule.
//!
//! Profile 15 commits `(h1,G)` in one 128-byte C2 fiber. At each statement
//! point it exposes the ordinary 49 C1 evaluations followed by `h1` and `G`.

use crate::circle::SecureCirclePoint;
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
use crate::statement_hiding::begin_payment_hiding_sumcheck;
use crate::statement_sumcheck::{
    begin_payment_zerocheck, decode_wire, verify_payment_sumcheck_messages_from_claim,
    PaymentConstraintChallenges, PaymentSumcheckWirePolynomial, PAYMENT_SUMCHECK_BYTES,
    PAYMENT_SUMCHECK_ROUNDS, PAYMENT_SUMCHECK_ROUND_BYTES,
};
use crate::sumcheck::{SUMCHECK_BYTES, SUMCHECK_COEFFICIENTS};
use crate::transcript::{label, HashFn, QuerySampleError, Transcript};

pub const PAYMENT_HIDING_PROFILE_ID: u8 = 15;
pub const PAYMENT_HIDING_LOG_ROWS: u32 = 10;
pub const PAYMENT_HIDING_LOG_BLOWUP: u32 = 4;
pub const PAYMENT_HIDING_QUERY_COUNT: u16 = 36;
/// Maximum candidate words consumed to obtain 36 distinct positions from the
/// 4096-fiber rate-1/16 domain. Exhaustion requires at least 29 collisions.
/// Since every pre-completion collision has conditional probability at most
/// 35/4096, the union bound is
/// `C(64,29) * (35/4096)^29 < 2^-138`.
pub const PAYMENT_HIDING_QUERY_DRAW_LIMIT: usize = 64;
pub const PAYMENT_HIDING_QUERY_ABORT_BOUND_BITS: u32 = 138;
pub const PAYMENT_HIDING_GRINDING_BITS: u8 = 36;
/// Work attached to the powers-generator batching round.  The current
/// 51-column rate-1/16 Johnson ledger has 81.9795 unground bits; 25 bits
/// raises this isolated round to 106.9795 before the global BCS factor.
pub const PAYMENT_HIDING_BATCH_GRINDING_BITS: u8 = 25;
pub const PAYMENT_HIDING_VALUES_PER_POINT: usize = 51;
pub const PAYMENT_HIDING_STATEMENT_VALUE_COUNT: usize = 2 * PAYMENT_HIDING_VALUES_PER_POINT;
pub const PAYMENT_HIDING_STATEMENT_EVALUATIONS_LEN: usize =
    PAYMENT_HIDING_STATEMENT_VALUE_COUNT * ENCODED_QM31_LEN;
pub const PAYMENT_HIDING_FLAGS: u8 =
    FLAG_EVALUATION_CLAIM | FLAG_SECOND_PHASE | FLAG_M31_CIRCLE_C1_DIAGNOSTIC;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentHidingPrefixOffsets {
    pub header_start: usize,
    pub c1_root_start: usize,
    pub c2_root_start: usize,
    pub initial_mask_claim_start: usize,
    pub payment_sumcheck_start: usize,
    pub statement_evaluations_start: usize,
    pub rounds: [CandidateRoundOffsets; CANDIDATE_ROUND_COUNT],
    pub final_polynomial_start: usize,
    pub nonce_start: usize,
    pub fold_nonces_start: usize,
    pub batch_nonce_start: usize,
    pub openings_start: usize,
}

pub const PAYMENT_HIDING_PREFIX_OFFSETS: PaymentHidingPrefixOffsets = PaymentHidingPrefixOffsets {
    header_start: 0,
    c1_root_start: 16,
    c2_root_start: 48,
    initial_mask_claim_start: 80,
    payment_sumcheck_start: 96,
    statement_evaluations_start: 1_696,
    rounds: [
        CandidateRoundOffsets {
            record_start: 3_328,
            root_start: None,
            ood_values_start: 3_328,
            sumcheck_start: 3_360,
            record_end: 3_472,
        },
        CandidateRoundOffsets {
            record_start: 3_472,
            root_start: Some(3_472),
            ood_values_start: 3_504,
            sumcheck_start: 3_536,
            record_end: 3_648,
        },
        CandidateRoundOffsets {
            record_start: 3_648,
            root_start: Some(3_648),
            ood_values_start: 3_680,
            sumcheck_start: 3_712,
            record_end: 3_824,
        },
        CandidateRoundOffsets {
            record_start: 3_824,
            root_start: Some(3_824),
            ood_values_start: 3_856,
            sumcheck_start: 3_888,
            record_end: 4_000,
        },
    ],
    final_polynomial_start: 4_000,
    nonce_start: 4_064,
    fold_nonces_start: 4_072,
    batch_nonce_start: 4_104,
    openings_start: 4_112,
};

pub const PAYMENT_HIDING_PREFIX_LEN: usize = PAYMENT_HIDING_PREFIX_OFFSETS.openings_start;

#[derive(Clone, Copy, Debug)]
pub struct PaymentHidingCandidatePrefix<'a> {
    pub header: Header,
    pub header_bytes: &'a [u8; HEADER_LEN],
    pub c1_root: &'a [u8; ROOT_LEN],
    pub c2_root: &'a [u8; ROOT_LEN],
    pub initial_mask_claim_bytes: &'a [u8; ENCODED_QM31_LEN],
    pub payment_sumcheck_bytes: &'a [u8; PAYMENT_SUMCHECK_BYTES],
    /// Raw statement values are transcript-bound here, but their canonical
    /// QM31 decoding is deliberately deferred to the fused relation kernel.
    /// That kernel needs the same values and rejects any noncanonical limb
    /// before the relation can accept, avoiding a duplicate 1,632-byte scan.
    pub statement_evaluations_bytes: &'a [u8; PAYMENT_HIDING_STATEMENT_EVALUATIONS_LEN],
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

fn exact_header(header: &Header) -> bool {
    header.version == VERSION_V4_S2
        && header.profile_id == PAYMENT_HIDING_PROFILE_ID
        && header.log_rows == PAYMENT_HIDING_LOG_ROWS
        && header.log_blowup == PAYMENT_HIDING_LOG_BLOWUP
        && header.query_count == PAYMENT_HIDING_QUERY_COUNT
        && header.grinding_bits == PAYMENT_HIDING_GRINDING_BITS
        && header.fold_payload == FoldPayload::RawFibers as u8
        && header.merkle_mode == MerkleMode::Radix4MinimalSubtree as u8
        && header.num_rounds == CANDIDATE_ROUND_COUNT as u32
        && header.final_poly_log_len == 2
        && header.flags == PAYMENT_HIDING_FLAGS
}

impl<'a> PaymentHidingCandidatePrefix<'a> {
    pub fn parse_exact(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        match bytes.len().cmp(&PAYMENT_HIDING_PREFIX_LEN) {
            core::cmp::Ordering::Less => return Err(CandidatePrefixError::Truncated),
            core::cmp::Ordering::Greater => return Err(CandidatePrefixError::TrailingBytes),
            core::cmp::Ordering::Equal => {}
        }
        Self::parse_prefix(bytes)
    }

    pub fn parse_from_proof(bytes: &'a [u8]) -> Result<(Self, &'a [u8]), CandidatePrefixError> {
        if bytes.len() < PAYMENT_HIDING_PREFIX_LEN {
            return Err(CandidatePrefixError::Truncated);
        }
        let (prefix, openings) = bytes.split_at(PAYMENT_HIDING_PREFIX_LEN);
        Ok((Self::parse_prefix(prefix)?, openings))
    }

    fn parse_prefix(bytes: &'a [u8]) -> Result<Self, CandidatePrefixError> {
        let header_bytes =
            array_at::<HEADER_LEN>(bytes, PAYMENT_HIDING_PREFIX_OFFSETS.header_start);
        let header = Header::parse(header_bytes).ok_or(CandidatePrefixError::BadHeader)?;
        if !exact_header(&header) {
            return Err(CandidatePrefixError::BadHeader);
        }
        validate_field_block(
            bytes,
            PAYMENT_HIDING_PREFIX_OFFSETS.initial_mask_claim_start,
            1,
        )?;
        validate_field_block(
            bytes,
            PAYMENT_HIDING_PREFIX_OFFSETS.payment_sumcheck_start,
            PAYMENT_SUMCHECK_BYTES / ENCODED_QM31_LEN,
        )?;
        // The statement-evaluation block is the sole deferred field block.
        // It is absorbed byte-exact before gamma, then canonically decoded
        // and checked once by the fused relation/query-power kernel. Every
        // other field block remains validated here.
        for round in PAYMENT_HIDING_PREFIX_OFFSETS.rounds {
            validate_field_block(bytes, round.ood_values_start, CANDIDATE_OOD_SAMPLES)?;
            validate_field_block(bytes, round.sumcheck_start, SUMCHECK_COEFFICIENTS)?;
        }
        validate_field_block(
            bytes,
            PAYMENT_HIDING_PREFIX_OFFSETS.final_polynomial_start,
            CANDIDATE_FINAL_POLY_LEN,
        )?;
        let rounds = core::array::from_fn(|layer| {
            let offsets = PAYMENT_HIDING_PREFIX_OFFSETS.rounds[layer];
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
            header,
            header_bytes,
            c1_root: array_at(bytes, PAYMENT_HIDING_PREFIX_OFFSETS.c1_root_start),
            c2_root: array_at(bytes, PAYMENT_HIDING_PREFIX_OFFSETS.c2_root_start),
            initial_mask_claim_bytes: array_at(
                bytes,
                PAYMENT_HIDING_PREFIX_OFFSETS.initial_mask_claim_start,
            ),
            payment_sumcheck_bytes: array_at(
                bytes,
                PAYMENT_HIDING_PREFIX_OFFSETS.payment_sumcheck_start,
            ),
            statement_evaluations_bytes: array_at(
                bytes,
                PAYMENT_HIDING_PREFIX_OFFSETS.statement_evaluations_start,
            ),
            rounds,
            final_polynomial_bytes: array_at(
                bytes,
                PAYMENT_HIDING_PREFIX_OFFSETS.final_polynomial_start,
            ),
            nonce: u64::from_le_bytes(
                bytes[PAYMENT_HIDING_PREFIX_OFFSETS.nonce_start
                    ..PAYMENT_HIDING_PREFIX_OFFSETS.nonce_start + CANDIDATE_NONCE_LEN]
                    .try_into()
                    .unwrap(),
            ),
            fold_nonces: core::array::from_fn(|round| {
                let start =
                    PAYMENT_HIDING_PREFIX_OFFSETS.fold_nonces_start + round * CANDIDATE_NONCE_LEN;
                u64::from_le_bytes(
                    bytes[start..start + CANDIDATE_NONCE_LEN]
                        .try_into()
                        .unwrap(),
                )
            }),
            batch_nonce: u64::from_le_bytes(
                bytes[PAYMENT_HIDING_PREFIX_OFFSETS.batch_nonce_start
                    ..PAYMENT_HIDING_PREFIX_OFFSETS.batch_nonce_start + CANDIDATE_NONCE_LEN]
                    .try_into()
                    .unwrap(),
            ),
        })
    }

    pub fn initial_mask_claim(&self) -> QM31 {
        QM31::from_le_bytes(self.initial_mask_claim_bytes).unwrap()
    }

    pub fn payment_sumcheck_messages(
        &self,
    ) -> [PaymentSumcheckWirePolynomial; PAYMENT_SUMCHECK_ROUNDS] {
        core::array::from_fn(|round| {
            let start = round * PAYMENT_SUMCHECK_ROUND_BYTES;
            decode_wire(&self.payment_sumcheck_bytes[start..start + PAYMENT_SUMCHECK_ROUND_BYTES])
                .expect("profile parser validated the complete sumcheck field block")
        })
    }

    pub fn statement_evaluation(&self, index: usize) -> Option<QM31> {
        if index >= PAYMENT_HIDING_STATEMENT_VALUE_COUNT {
            return None;
        }
        let start = index * ENCODED_QM31_LEN;
        QM31::from_le_bytes(&self.statement_evaluations_bytes[start..start + ENCODED_QM31_LEN])
    }

    pub fn final_coefficient(&self, index: usize) -> Option<QM31> {
        let start = index.checked_mul(ENCODED_QM31_LEN)?;
        QM31::from_le_bytes(
            self.final_polynomial_bytes
                .get(start..start + ENCODED_QM31_LEN)?,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentHidingPrefixScheduleResult {
    pub lambda: QM31,
    pub chi: QM31,
    pub batching: PaymentConstraintChallenges,
    pub initial_mask_claim: QM31,
    pub eta: QM31,
    pub z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
    pub masked_terminal_claim: QM31,
    pub gamma: QM31,
    pub second_point_scale: QM31,
    pub state_after_gamma: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaymentHidingTranscriptScheduleResult {
    pub prefix: PaymentHidingPrefixScheduleResult,
    pub circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    pub line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    pub mu: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub alpha: [QM31; CANDIDATE_ROUND_COUNT],
    pub state_before_grinding: [u8; 32],
    pub queries: [u32; PAYMENT_HIDING_QUERY_COUNT as usize],
    pub state_after_queries: [u8; 32],
}

fn encode_statement_points(
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> [u8; 2 * CANDIDATE_STATEMENT_POINT_COORDINATES * ENCODED_QM31_LEN] {
    let mut shifted = *z;
    for coordinate in [6usize, 8, 9] {
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    let points = [*z, shifted];
    let mut bytes = [0u8; 2 * CANDIDATE_STATEMENT_POINT_COORDINATES * ENCODED_QM31_LEN];
    for (point, coordinates) in points.iter().enumerate() {
        for (coordinate, value) in coordinates.iter().enumerate() {
            let index = point * CANDIDATE_STATEMENT_POINT_COORDINATES + coordinate;
            value.write_le_bytes(&mut bytes[index * ENCODED_QM31_LEN..][..ENCODED_QM31_LEN]);
        }
    }
    bytes
}

fn absorb_round_root(transcript: &mut Transcript, layer: usize, root: &[u8; ROOT_LEN]) {
    let mut record = [0u8; 1 + ROOT_LEN];
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
    let mut record = [0u8; 2 + ENCODED_QM31_LEN];
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

fn absorb_fold_pow(transcript: &mut Transcript, round: usize, nonce: u64) {
    let mut record = [0u8; 1 + CANDIDATE_NONCE_LEN];
    record[0] = round as u8;
    record[1..].copy_from_slice(&nonce.to_le_bytes());
    transcript.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
}

fn absorb_batch_pow(transcript: &mut Transcript, nonce: u64) {
    transcript.absorb(label::M31_PAYMENT_BATCH_POW_NONCE, &nonce.to_le_bytes());
}

fn absorb_final(transcript: &mut Transcript, prefix: &PaymentHidingCandidatePrefix<'_>) {
    transcript.absorb(
        label::M31_CIRCLE_FINAL_TENSOR_POLY,
        prefix.final_polynomial_bytes,
    );
}

fn begin_schedule(
    hash: HashFn,
    prefix: &PaymentHidingCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_batch_pow: bool,
) -> Result<(Transcript, PaymentHidingPrefixScheduleResult), CandidateTranscriptScheduleError> {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, prefix.header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);
    absorb_round_root(&mut transcript, 0, prefix.c1_root);
    let lambda = transcript.challenge_qm31()?;
    let chi = transcript.challenge_qm31()?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, prefix.c2_root);
    let batching = begin_payment_zerocheck(&mut transcript)?;
    let initial_mask_claim = prefix.initial_mask_claim();
    let eta = begin_payment_hiding_sumcheck(&mut transcript, initial_mask_claim)?;
    let verified = verify_payment_sumcheck_messages_from_claim(
        &mut transcript,
        &prefix.payment_sumcheck_messages(),
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
    let batch_pow_ok =
        transcript.grinding_ok(prefix.batch_nonce, PAYMENT_HIDING_BATCH_GRINDING_BITS);
    if check_batch_pow && !batch_pow_ok {
        return Err(CandidateTranscriptScheduleError::BatchGrindingRejected);
    }
    absorb_batch_pow(&mut transcript, prefix.batch_nonce);
    let gamma = transcript.challenge_qm31()?;
    let second_point_scale = transcript.challenge_qm31()?;
    let result = PaymentHidingPrefixScheduleResult {
        lambda,
        chi,
        batching,
        initial_mask_claim,
        eta,
        z,
        masked_terminal_claim: verified.terminal_claim,
        gamma,
        second_point_scale,
        state_after_gamma: transcript.diagnostic_state(),
    };
    Ok((transcript, result))
}

pub fn run_payment_hiding_prefix_schedule_host(
    hash: HashFn,
    prefix: &PaymentHidingCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<PaymentHidingPrefixScheduleResult, CandidateTranscriptScheduleError> {
    Ok(begin_schedule(hash, prefix, statement_digest, false)?.1)
}

pub fn run_payment_hiding_transcript_schedule_host(
    hash: HashFn,
    prefix: &PaymentHidingCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<PaymentHidingTranscriptScheduleResult, CandidateTranscriptScheduleError> {
    run_payment_hiding_transcript_schedule_host_with_pow_check(hash, prefix, statement_digest, true)
}

/// Measurement-only replay which absorbs the exact proof-carried nonce
/// records but does not require them to meet their configured difficulties.
/// It must never gate production acceptance.
pub fn run_payment_hiding_transcript_schedule_host_unmined_for_diagnostics(
    hash: HashFn,
    prefix: &PaymentHidingCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) -> Result<PaymentHidingTranscriptScheduleResult, CandidateTranscriptScheduleError> {
    run_payment_hiding_transcript_schedule_host_with_pow_check(
        hash,
        prefix,
        statement_digest,
        false,
    )
}

/// Draw the fixed profile-15 query tuple with exactly the same bounded,
/// without-replacement policy on both prover and verifier paths.
pub fn sample_payment_hiding_queries(
    transcript: &mut Transcript,
) -> Result<[u32; PAYMENT_HIDING_QUERY_COUNT as usize], QuerySampleError> {
    Ok(transcript
        .challenge_queries_without_replacement(
            PAYMENT_HIDING_QUERY_COUNT as usize,
            1u32 << (PAYMENT_HIDING_LOG_ROWS + PAYMENT_HIDING_LOG_BLOWUP - 2),
            PAYMENT_HIDING_QUERY_DRAW_LIMIT,
        )?
        .try_into()
        .unwrap())
}

fn run_payment_hiding_transcript_schedule_host_with_pow_check(
    hash: HashFn,
    prefix: &PaymentHidingCandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    check_pow: bool,
) -> Result<PaymentHidingTranscriptScheduleResult, CandidateTranscriptScheduleError> {
    let (mut transcript, prefix_result) =
        begin_schedule(hash, prefix, statement_digest, check_pow)?;
    let mut circle_ood_points = [SecureCirclePoint {
        x: QM31::ZERO,
        y: QM31::ZERO,
    }; CANDIDATE_OOD_SAMPLES];
    let mut line_ood_points = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1];
    let mut mu = [[QM31::ZERO; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT];
    let mut alpha = [QM31::ZERO; CANDIDATE_ROUND_COUNT];

    for sample in 0..CANDIDATE_OOD_SAMPLES {
        circle_ood_points[sample] = transcript.challenge_secure_circle_point()?;
        absorb_ood(
            &mut transcript,
            label::M31_CIRCLE_OOD_VALUE,
            0,
            sample,
            prefix.rounds[0].ood_value(sample).unwrap(),
        );
        mu[0][sample] = transcript.challenge_qm31()?;
    }
    absorb_relation_sumcheck(&mut transcript, &prefix.rounds[0]);
    // Diagnostic replay skips only rejection, never verifier work: the hash
    // call is part of the production CU object even when the fixture nonce is
    // intentionally unmined.
    let fold_pow_ok =
        transcript.grinding_ok(prefix.fold_nonces[0], RATE16_HARDENED_FOLD_POW_BITS[0]);
    if check_pow && !fold_pow_ok {
        return Err(CandidateTranscriptScheduleError::FoldGrindingRejected { round: 0 });
    }
    absorb_fold_pow(&mut transcript, 0, prefix.fold_nonces[0]);
    alpha[0] = transcript.challenge_qm31()?;

    for layer in 1..CANDIDATE_ROUND_COUNT {
        absorb_round_root(&mut transcript, layer, prefix.rounds[layer].root.unwrap());
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            line_ood_points[layer - 1][sample] = transcript.challenge_ood_qm31()?;
            absorb_ood(
                &mut transcript,
                label::M31_LINE_OOD_VALUE,
                layer,
                sample,
                prefix.rounds[layer].ood_value(sample).unwrap(),
            );
            mu[layer][sample] = transcript.challenge_qm31()?;
        }
        absorb_relation_sumcheck(&mut transcript, &prefix.rounds[layer]);
        let fold_pow_ok = transcript.grinding_ok(
            prefix.fold_nonces[layer],
            RATE16_HARDENED_FOLD_POW_BITS[layer],
        );
        if check_pow && !fold_pow_ok {
            return Err(CandidateTranscriptScheduleError::FoldGrindingRejected { round: layer });
        }
        absorb_fold_pow(&mut transcript, layer, prefix.fold_nonces[layer]);
        alpha[layer] = transcript.challenge_qm31()?;
    }

    absorb_final(&mut transcript, prefix);
    let state_before_grinding = transcript.diagnostic_state();
    let final_pow_ok = transcript.grinding_ok(prefix.nonce, PAYMENT_HIDING_GRINDING_BITS);
    if check_pow && !final_pow_ok {
        return Err(CandidateTranscriptScheduleError::GrindingRejected);
    }
    transcript.absorb(label::GRIND_NONCE, &prefix.nonce.to_le_bytes());
    let queries = sample_payment_hiding_queries(&mut transcript)?;
    Ok(PaymentHidingTranscriptScheduleResult {
        prefix: prefix_result,
        circle_ood_points,
        line_ood_points,
        mu,
        alpha,
        state_before_grinding,
        queries,
        state_after_queries: transcript.diagnostic_state(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::P;

    fn header() -> Header {
        Header {
            version: VERSION_V4_S2,
            profile_id: PAYMENT_HIDING_PROFILE_ID,
            log_rows: PAYMENT_HIDING_LOG_ROWS,
            log_blowup: PAYMENT_HIDING_LOG_BLOWUP,
            query_count: PAYMENT_HIDING_QUERY_COUNT,
            grinding_bits: PAYMENT_HIDING_GRINDING_BITS,
            fold_payload: FoldPayload::RawFibers as u8,
            merkle_mode: MerkleMode::Radix4MinimalSubtree as u8,
            num_rounds: CANDIDATE_ROUND_COUNT as u32,
            final_poly_log_len: 2,
            flags: PAYMENT_HIDING_FLAGS,
        }
    }

    #[test]
    fn exact_offsets_and_profile_header_are_pinned() {
        assert_eq!(PAYMENT_HIDING_PREFIX_LEN, 4_112);
        assert_eq!(PAYMENT_HIDING_QUERY_DRAW_LIMIT, 64);
        assert_eq!(PAYMENT_HIDING_QUERY_ABORT_BOUND_BITS, 138);
        assert_eq!(PAYMENT_HIDING_PREFIX_OFFSETS.payment_sumcheck_start, 96);
        assert_eq!(
            PAYMENT_HIDING_PREFIX_OFFSETS.statement_evaluations_start,
            1_696
        );
        assert_eq!(PAYMENT_HIDING_PREFIX_OFFSETS.rounds[0].record_start, 3_328);
        assert_eq!(PAYMENT_HIDING_PREFIX_OFFSETS.batch_nonce_start, 4_104);
        let mut bytes = [0u8; PAYMENT_HIDING_PREFIX_LEN];
        header().write(&mut bytes[..HEADER_LEN]);
        let parsed = PaymentHidingCandidatePrefix::parse_exact(&bytes).unwrap();
        assert_eq!(parsed.header.profile_id, PAYMENT_HIDING_PROFILE_ID);
        assert_eq!(parsed.initial_mask_claim(), QM31::ZERO);
        assert_eq!(parsed.statement_evaluation(101), Some(QM31::ZERO));
        assert_eq!(parsed.statement_evaluation(102), None);
    }

    #[test]
    fn parser_rejects_wrong_profile_and_noncanonical_new_fields() {
        let mut bytes = [0u8; PAYMENT_HIDING_PREFIX_LEN];
        header().write(&mut bytes[..HEADER_LEN]);
        bytes[5] = 13;
        assert!(matches!(
            PaymentHidingCandidatePrefix::parse_exact(&bytes),
            Err(CandidatePrefixError::BadHeader)
        ));
        header().write(&mut bytes[..HEADER_LEN]);
        bytes[PAYMENT_HIDING_PREFIX_OFFSETS.initial_mask_claim_start..][..4]
            .copy_from_slice(&P.to_le_bytes());
        assert!(matches!(
            PaymentHidingCandidatePrefix::parse_exact(&bytes),
            Err(CandidatePrefixError::NonCanonicalFieldElement { offset })
                if offset == PAYMENT_HIDING_PREFIX_OFFSETS.initial_mask_claim_start
        ));
    }

    fn all_zero_hash(_inputs: &[&[u8]]) -> [u8; 32] {
        [0u8; 32]
    }

    #[test]
    fn payment_query_helper_propagates_bounded_duplicate_exhaustion() {
        let mut transcript = Transcript::new(all_zero_hash);
        assert_eq!(
            sample_payment_hiding_queries(&mut transcript),
            Err(QuerySampleError::DrawLimitExhausted {
                accepted: 1,
                max_draws: PAYMENT_HIDING_QUERY_DRAW_LIMIT,
            })
        );
    }
}
