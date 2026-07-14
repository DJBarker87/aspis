use super::*;

use crate::field::{CM31, M31, P};
use crate::proof::Header;
use alloc::vec;
use alloc::vec::Vec;
use sha2::{Digest, Sha256};

fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}

fn fixture_value(seed: u32) -> QM31 {
    QM31 {
        c0: CM31 {
            a: M31((seed * 4 + 1) % P),
            b: M31((seed * 4 + 2) % P),
        },
        c1: CM31 {
            a: M31((seed * 4 + 3) % P),
            b: M31((seed * 4 + 4) % P),
        },
    }
}

fn write_value(bytes: &mut [u8], offset: usize, value: QM31) {
    value.write_le_bytes(&mut bytes[offset..offset + ENCODED_QM31_LEN]);
}

fn candidate_field_offsets() -> Vec<usize> {
    let mut offsets = Vec::new();
    for index in 0..CANDIDATE_STATEMENT_VALUE_COUNT {
        offsets
            .push(CANDIDATE_PREFIX_OFFSETS.statement_evaluations_start + index * ENCODED_QM31_LEN);
    }
    for round in CANDIDATE_PREFIX_OFFSETS.rounds {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            offsets.push(round.ood_values_start + sample * ENCODED_QM31_LEN);
        }
        for coefficient in 0..SUMCHECK_COEFFICIENTS {
            offsets.push(round.sumcheck_start + coefficient * ENCODED_QM31_LEN);
        }
    }
    for coefficient in 0..CANDIDATE_FINAL_POLY_LEN {
        offsets
            .push(CANDIDATE_PREFIX_OFFSETS.final_polynomial_start + coefficient * ENCODED_QM31_LEN);
    }
    offsets
}

fn candidate_fixture() -> Vec<u8> {
    let mut bytes = vec![0u8; CANDIDATE_PREFIX_LEN];
    Header {
        version: VERSION_V4_S2,
        profile_id: CANDIDATE_PROFILE_ID,
        log_rows: CANDIDATE_LOG_ROWS,
        log_blowup: CANDIDATE_LOG_BLOWUP,
        query_count: CANDIDATE_QUERY_COUNT,
        grinding_bits: CANDIDATE_GRINDING_BITS,
        fold_payload: FoldPayload::RawFibers as u8,
        merkle_mode: MerkleMode::Radix4MinimalSubtree as u8,
        num_rounds: CANDIDATE_ROUND_COUNT as u32,
        final_poly_log_len: CANDIDATE_FINAL_POLY_LOG_LEN,
        flags: CANDIDATE_FLAGS,
    }
    .write(&mut bytes[..HEADER_LEN]);

    for (index, byte) in bytes
        [CANDIDATE_PREFIX_OFFSETS.c1_root_start..CANDIDATE_PREFIX_OFFSETS.c1_root_start + ROOT_LEN]
        .iter_mut()
        .enumerate()
    {
        *byte = 0x20u8.wrapping_add(index as u8);
    }
    for (index, byte) in bytes
        [CANDIDATE_PREFIX_OFFSETS.c2_root_start..CANDIDATE_PREFIX_OFFSETS.c2_root_start + ROOT_LEN]
        .iter_mut()
        .enumerate()
    {
        *byte = 0x80u8.wrapping_add(index as u8);
    }
    for (layer, round) in CANDIDATE_PREFIX_OFFSETS.rounds.iter().enumerate() {
        if let Some(root_start) = round.root_start {
            for (index, byte) in bytes[root_start..root_start + ROOT_LEN]
                .iter_mut()
                .enumerate()
            {
                *byte = 0xa0u8
                    .wrapping_add((layer as u8) << 4)
                    .wrapping_add(index as u8);
            }
        }
    }

    for (index, offset) in candidate_field_offsets().into_iter().enumerate() {
        write_value(&mut bytes, offset, fixture_value(index as u32 + 1));
    }
    bytes[CANDIDATE_PREFIX_OFFSETS.nonce_start..CANDIDATE_PREFIX_LEN]
        .copy_from_slice(&0x8877_6655_4433_2211u64.to_le_bytes());
    bytes
}

fn fixture_z() -> [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES] {
    core::array::from_fn(|index| fixture_value(1_000 + index as u32))
}

#[test]
fn label_allocation_is_exactly_append_only_11_through_19() {
    assert_eq!(
        [
            label::M31_CIRCLE_BASIS,
            label::M31_CIRCLE_ROUND_ROOT,
            label::M31_CIRCLE_C2_ROOT,
            label::M31_CIRCLE_STATEMENT_POINTS,
            label::M31_CIRCLE_STATEMENT_EVALUATIONS,
            label::M31_CIRCLE_OOD_VALUE,
            label::M31_LINE_OOD_VALUE,
            label::M31_CIRCLE_RELATION_SUMCHECK,
            label::M31_CIRCLE_FINAL_TENSOR_POLY,
        ],
        [11, 12, 13, 14, 15, 16, 17, 18, 19]
    );
}

#[test]
fn exact_parser_exposes_fixed_offsets_and_borrowed_records() {
    let bytes = candidate_fixture();
    let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();

    assert_eq!(CANDIDATE_PREFIX_LEN, 2_456);
    assert_eq!(CANDIDATE_PREFIX_OFFSETS.c1_root_start, HEADER_LEN);
    assert_eq!(CANDIDATE_PREFIX_OFFSETS.c2_root_start, 48);
    assert_eq!(CANDIDATE_PREFIX_OFFSETS.statement_evaluations_start, 80);
    assert_eq!(CANDIDATE_PREFIX_OFFSETS.final_polynomial_start, 2_384);
    assert_eq!(CANDIDATE_PREFIX_OFFSETS.nonce_start, 2_448);
    assert_eq!(prefix.header.version, VERSION_V4_S2);
    assert_eq!(prefix.header.flags, CANDIDATE_FLAGS);
    assert_eq!(prefix.c1_root.as_slice(), &bytes[16..48]);
    assert_eq!(prefix.c2_root.as_slice(), &bytes[48..80]);
    assert_eq!(prefix.nonce, 0x8877_6655_4433_2211);

    assert!(prefix.rounds[0].root.is_none());
    assert_eq!(prefix.rounds[0].record_bytes.len(), 144);
    for layer in 1..CANDIDATE_ROUND_COUNT {
        let offsets = CANDIDATE_PREFIX_OFFSETS.rounds[layer];
        assert_eq!(prefix.rounds[layer].layer, layer as u8);
        assert_eq!(prefix.rounds[layer].start_offset, offsets.record_start);
        assert_eq!(prefix.rounds[layer].record_bytes.len(), 176);
        assert_eq!(
            prefix.rounds[layer].root.unwrap().as_slice(),
            &bytes[offsets.root_start.unwrap()..offsets.root_start.unwrap() + ROOT_LEN]
        );
    }

    assert_eq!(prefix.statement_evaluation(0), Some(fixture_value(1)));
    assert_eq!(
        prefix.statement_evaluation(CANDIDATE_STATEMENT_VALUE_COUNT - 1),
        Some(fixture_value(CANDIDATE_STATEMENT_VALUE_COUNT as u32))
    );
    assert_eq!(prefix.statement_evaluation(102), None);
    assert!(prefix.rounds[0].ood_value(0).is_some());
    assert!(prefix.rounds[3].ood_value(1).is_some());
    assert_eq!(prefix.rounds[0].ood_value(2), None);
    assert!(prefix.rounds[2].sumcheck_coefficient(6).is_some());
    assert_eq!(prefix.rounds[2].sumcheck_coefficient(7), None);
    assert!(prefix.final_coefficient(3).is_some());
    assert_eq!(prefix.final_coefficient(4), None);
}

#[test]
fn exact_parser_rejects_every_truncation_and_trailing_byte() {
    let bytes = candidate_fixture();
    for length in 0..CANDIDATE_PREFIX_LEN {
        assert_eq!(
            CandidatePrefix::parse_exact(&bytes[..length]).unwrap_err(),
            CandidatePrefixError::Truncated,
            "length {length}"
        );
    }

    let mut extended = bytes.clone();
    extended.extend_from_slice(&[0xaa, 0xbb]);
    assert_eq!(
        CandidatePrefix::parse_exact(&extended).unwrap_err(),
        CandidatePrefixError::TrailingBytes
    );
    let (parsed, openings) = CandidatePrefix::parse_from_proof(&extended).unwrap();
    assert_eq!(parsed.nonce, 0x8877_6655_4433_2211);
    assert_eq!(openings, [0xaa, 0xbb]);
}

#[test]
fn every_prefix_field_element_is_canonical_checked_at_its_offset() {
    let bytes = candidate_fixture();
    let offsets = candidate_field_offsets();
    assert_eq!(offsets.len(), 102 + 4 * (2 + 7) + 4);
    for offset in offsets {
        for limb in 0..4 {
            let mut corrupted = bytes.clone();
            let limb_offset = offset + limb * 4;
            corrupted[limb_offset..limb_offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                CandidatePrefix::parse_exact(&corrupted).unwrap_err(),
                CandidatePrefixError::NonCanonicalFieldElement { offset },
                "field offset {offset}, limb {limb}"
            );
        }
    }
}

#[test]
fn roots_are_opaque_bytes_but_header_shape_is_exact() {
    let bytes = candidate_fixture();
    for header_offset in [0usize, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15] {
        let mut corrupted = bytes.clone();
        corrupted[header_offset] = corrupted[header_offset].wrapping_add(1);
        assert_eq!(
            CandidatePrefix::parse_exact(&corrupted).unwrap_err(),
            CandidatePrefixError::BadHeader,
            "header offset {header_offset}"
        );
    }

    let mut opaque_roots = bytes;
    let mut root_offsets = vec![
        CANDIDATE_PREFIX_OFFSETS.c1_root_start,
        CANDIDATE_PREFIX_OFFSETS.c2_root_start,
    ];
    root_offsets.extend(
        CANDIDATE_PREFIX_OFFSETS
            .rounds
            .iter()
            .filter_map(|round| round.root_start),
    );
    for offset in root_offsets {
        opaque_roots[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
    }
    CandidatePrefix::parse_exact(&opaque_roots).unwrap();
}

#[test]
fn canonical_prefix_schedule_stops_immediately_after_gamma() {
    let bytes = candidate_fixture();
    let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();
    let digest = [0x5au8; 32];
    let z = fixture_z();
    let baseline = run_candidate_prefix_schedule_host(test_hash, &prefix, &digest, &z).unwrap();

    let mut changed = bytes;
    write_value(
        &mut changed,
        CANDIDATE_PREFIX_OFFSETS.rounds[0].ood_values_start,
        fixture_value(5_001),
    );
    changed[CANDIDATE_PREFIX_OFFSETS.rounds[1].root_start.unwrap()] ^= 0x55;
    write_value(
        &mut changed,
        CANDIDATE_PREFIX_OFFSETS.final_polynomial_start,
        fixture_value(5_002),
    );
    changed[CANDIDATE_PREFIX_OFFSETS.nonce_start] ^= 0xff;
    let changed = CandidatePrefix::parse_exact(&changed).unwrap();
    assert_eq!(
        run_candidate_prefix_schedule_host(test_hash, &changed, &digest, &z).unwrap(),
        baseline
    );
}

#[test]
fn canonical_prefix_schedule_binds_each_available_input_class() {
    let bytes = candidate_fixture();
    let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();
    let digest = [0x5au8; 32];
    let z = fixture_z();
    let baseline = run_candidate_prefix_schedule_host(test_hash, &prefix, &digest, &z).unwrap();

    let mut changed_digest = digest;
    changed_digest[0] ^= 1;
    assert_ne!(
        run_candidate_prefix_schedule_host(test_hash, &prefix, &changed_digest, &z).unwrap(),
        baseline
    );
    let mut changed_z = z;
    changed_z[9] = changed_z[9].add(QM31::ONE);
    assert_ne!(
        run_candidate_prefix_schedule_host(test_hash, &prefix, &digest, &changed_z).unwrap(),
        baseline
    );

    for offset in [
        CANDIDATE_PREFIX_OFFSETS.c1_root_start,
        CANDIDATE_PREFIX_OFFSETS.c2_root_start,
        CANDIDATE_PREFIX_OFFSETS.statement_evaluations_start,
    ] {
        let mut changed = bytes.clone();
        if offset == CANDIDATE_PREFIX_OFFSETS.statement_evaluations_start {
            write_value(&mut changed, offset, fixture_value(6_000));
        } else {
            changed[offset] ^= 1;
        }
        let changed = CandidatePrefix::parse_exact(&changed).unwrap();
        assert_ne!(
            run_candidate_prefix_schedule_host(test_hash, &changed, &digest, &z).unwrap(),
            baseline,
            "offset {offset}"
        );
    }
}

#[test]
fn statement_evaluations_digest_binds_both_points_and_all_102_values() {
    let bytes = candidate_fixture();
    let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();
    let z = fixture_z();
    let digest =
        candidate_statement_evaluations_digest(test_hash, &z, prefix.statement_evaluations_bytes);
    assert_eq!(
        digest,
        [
            0x6d, 0x20, 0xde, 0x1b, 0xa4, 0x64, 0xdd, 0x75, 0x43, 0x74, 0x80, 0xbf, 0x86, 0x70,
            0x94, 0x21, 0xf8, 0xa0, 0x67, 0x48, 0xb8, 0x01, 0xd2, 0xe6, 0xbe, 0xec, 0x61, 0x4c,
            0x06, 0x9c, 0x3b, 0xec,
        ]
    );

    let mut changed_z = z;
    changed_z[8] = changed_z[8].add(QM31::ONE);
    assert_ne!(
        candidate_statement_evaluations_digest(
            test_hash,
            &changed_z,
            prefix.statement_evaluations_bytes,
        ),
        digest
    );
    let mut changed_values = *prefix.statement_evaluations_bytes;
    write_value(
        &mut changed_values,
        101 * ENCODED_QM31_LEN,
        fixture_value(9_999),
    );
    assert_ne!(
        candidate_statement_evaluations_digest(test_hash, &z, &changed_values),
        digest
    );
}

#[derive(Clone, Copy, Debug)]
enum WeakenedSchedule {
    GammaBeforeC2,
    GammaBeforePoints,
    GammaAfter51Values,
    GammaAfter101Values,
    SwappedRoots,
    UnlabeledRoots,
    OmittedC2H2Values,
    SwappedC2ValueOrder,
}

fn absorb_common_prefix(
    transcript: &mut Transcript,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
) {
    transcript.absorb(label::PROFILE, prefix.header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);
}

fn absorb_layer_zero_root(transcript: &mut Transcript, root: &[u8; ROOT_LEN]) {
    let mut root_record = [0u8; 1 + ROOT_LEN];
    root_record[1..].copy_from_slice(root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &root_record);
}

fn weakened_schedule(
    mode: WeakenedSchedule,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> CandidatePrefixScheduleResult {
    let mut transcript = Transcript::new(test_hash);
    absorb_common_prefix(&mut transcript, prefix, statement_digest);

    match mode {
        WeakenedSchedule::SwappedRoots => absorb_layer_zero_root(&mut transcript, prefix.c2_root),
        WeakenedSchedule::UnlabeledRoots => transcript.absorb(label::ROOT, prefix.c1_root),
        _ => absorb_layer_zero_root(&mut transcript, prefix.c1_root),
    }
    let lambda = transcript.challenge_qm31().unwrap();
    let chi = transcript.challenge_qm31().unwrap();

    if matches!(mode, WeakenedSchedule::GammaBeforeC2) {
        let gamma = transcript.challenge_qm31().unwrap();
        return CandidatePrefixScheduleResult {
            lambda,
            chi,
            gamma,
            state_after_gamma: transcript.diagnostic_state(),
        };
    }

    match mode {
        WeakenedSchedule::SwappedRoots => {
            transcript.absorb(label::M31_CIRCLE_C2_ROOT, prefix.c1_root)
        }
        WeakenedSchedule::UnlabeledRoots => transcript.absorb(label::ROOT, prefix.c2_root),
        _ => transcript.absorb(label::M31_CIRCLE_C2_ROOT, prefix.c2_root),
    }

    if matches!(mode, WeakenedSchedule::GammaBeforePoints) {
        let gamma = transcript.challenge_qm31().unwrap();
        return CandidatePrefixScheduleResult {
            lambda,
            chi,
            gamma,
            state_after_gamma: transcript.diagnostic_state(),
        };
    }

    let points = encode_statement_points(z);
    transcript.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &points);
    match mode {
        WeakenedSchedule::GammaAfter51Values => transcript.absorb(
            label::M31_CIRCLE_STATEMENT_EVALUATIONS,
            &prefix.statement_evaluations_bytes[..51 * ENCODED_QM31_LEN],
        ),
        WeakenedSchedule::GammaAfter101Values => transcript.absorb(
            label::M31_CIRCLE_STATEMENT_EVALUATIONS,
            &prefix.statement_evaluations_bytes[..101 * ENCODED_QM31_LEN],
        ),
        WeakenedSchedule::OmittedC2H2Values => {
            let mut values = [0u8; 100 * ENCODED_QM31_LEN];
            let mut output_index = 0usize;
            for point in 0..2 {
                // Keep all 49 C1 values and h1; omit only h2 (column 50).
                for column in 0..50 {
                    let input_index = point * 51 + column;
                    let source = &prefix.statement_evaluations_bytes
                        [input_index * ENCODED_QM31_LEN..(input_index + 1) * ENCODED_QM31_LEN];
                    values[output_index * ENCODED_QM31_LEN..(output_index + 1) * ENCODED_QM31_LEN]
                        .copy_from_slice(source);
                    output_index += 1;
                }
            }
            transcript.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, &values);
        }
        WeakenedSchedule::SwappedC2ValueOrder => {
            let mut values = [0u8; CANDIDATE_STATEMENT_EVALUATIONS_LEN];
            values.copy_from_slice(prefix.statement_evaluations_bytes);
            for point in 0..2 {
                let h1 = (point * 51 + 49) * ENCODED_QM31_LEN;
                let h2 = (point * 51 + 50) * ENCODED_QM31_LEN;
                for byte in 0..ENCODED_QM31_LEN {
                    values.swap(h1 + byte, h2 + byte);
                }
            }
            transcript.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, &values);
        }
        _ => transcript.absorb(
            label::M31_CIRCLE_STATEMENT_EVALUATIONS,
            prefix.statement_evaluations_bytes,
        ),
    }
    let gamma = transcript.challenge_qm31().unwrap();
    CandidatePrefixScheduleResult {
        lambda,
        chi,
        gamma,
        state_after_gamma: transcript.diagnostic_state(),
    }
}

fn weakened_accepts(
    mode: WeakenedSchedule,
    vector: CandidatePrefixScheduleResult,
    prefix: &CandidatePrefix<'_>,
    statement_digest: &[u8; 32],
    z: &[QM31; CANDIDATE_STATEMENT_POINT_COORDINATES],
) -> bool {
    weakened_schedule(mode, prefix, statement_digest, z) == vector
}

#[test]
fn every_prefix_ordering_vector_has_weakened_acceptance_and_canonical_rejection() {
    let bytes = candidate_fixture();
    let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();
    let digest = [0x5au8; 32];
    let z = fixture_z();
    let canonical = run_candidate_prefix_schedule_host(test_hash, &prefix, &digest, &z).unwrap();

    for mode in [
        WeakenedSchedule::GammaBeforeC2,
        WeakenedSchedule::GammaBeforePoints,
        WeakenedSchedule::GammaAfter51Values,
        WeakenedSchedule::GammaAfter101Values,
        WeakenedSchedule::SwappedRoots,
        WeakenedSchedule::UnlabeledRoots,
        WeakenedSchedule::OmittedC2H2Values,
        WeakenedSchedule::SwappedC2ValueOrder,
    ] {
        let adversarial_vector = weakened_schedule(mode, &prefix, &digest, &z);
        assert!(
            weakened_accepts(mode, adversarial_vector, &prefix, &digest, &z),
            "weakened {mode:?} did not accept its paired vector"
        );
        assert_ne!(
            canonical, adversarial_vector,
            "canonical schedule accepted weakened {mode:?} vector"
        );
    }
}

fn write_nonce(bytes: &mut [u8], nonce: u64) {
    bytes[CANDIDATE_PREFIX_OFFSETS.nonce_start..CANDIDATE_PREFIX_LEN]
        .copy_from_slice(&nonce.to_le_bytes());
}

fn first_satisfying_nonce(transcript: &Transcript) -> u64 {
    (0..u64::MAX)
        .find(|nonce| transcript.grinding_ok(*nonce, CANDIDATE_GRINDING_BITS))
        .expect("a 16-bit grinding fixture nonce must exist")
}

fn canonical_nonce(mode: CandidateOneLaneBatchingMode) -> u64 {
    let bytes = candidate_fixture();
    let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();
    let (transcript, _) =
        candidate_transcript_before_grinding(test_hash, &prefix, &[0x5a; 32], &fixture_z(), mode)
            .unwrap();
    first_satisfying_nonce(&transcript)
}

#[test]
fn full_tail_supports_only_the_two_unselected_one_lane_shapes() {
    assert_eq!(
        CandidateOneLaneBatchingMode::ALL,
        [
            CandidateOneLaneBatchingMode::FreshKappa,
            CandidateOneLaneBatchingMode::DisjointGamma51,
        ]
    );
    let fresh_nonce = canonical_nonce(CandidateOneLaneBatchingMode::FreshKappa);
    let disjoint_nonce = canonical_nonce(CandidateOneLaneBatchingMode::DisjointGamma51);
    // These are fixture nonces, not transcript digests or production KATs.
    assert_eq!((fresh_nonce, disjoint_nonce), (33_623, 56_640));

    for (mode, nonce) in [
        (CandidateOneLaneBatchingMode::FreshKappa, fresh_nonce),
        (
            CandidateOneLaneBatchingMode::DisjointGamma51,
            disjoint_nonce,
        ),
    ] {
        let mut bad_nonce_bytes = candidate_fixture();
        write_nonce(&mut bad_nonce_bytes, 0);
        let bad_nonce_prefix = CandidatePrefix::parse_exact(&bad_nonce_bytes).unwrap();
        assert_eq!(
            run_candidate_transcript_schedule_host(
                test_hash,
                &bad_nonce_prefix,
                &[0x5a; 32],
                &fixture_z(),
                mode,
            ),
            Err(CandidateTranscriptScheduleError::GrindingRejected)
        );

        let mut bytes = candidate_fixture();
        write_nonce(&mut bytes, nonce);
        let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();
        let result = run_candidate_transcript_schedule_host(
            test_hash,
            &prefix,
            &[0x5a; 32],
            &fixture_z(),
            mode,
        )
        .unwrap();

        assert_eq!(result.batching_mode, mode);
        match mode {
            CandidateOneLaneBatchingMode::FreshKappa => {
                assert_eq!(result.second_point_scale, result.kappa.unwrap())
            }
            CandidateOneLaneBatchingMode::DisjointGamma51 => {
                assert_eq!(result.kappa, None);
                assert_eq!(result.second_point_scale, result.prefix.gamma.pow(51));
            }
        }
        for point in result.circle_ood_points {
            assert_eq!(point.x.square().add(point.y.square()), QM31::ONE);
            assert!(point.x.c1 != CM31::ZERO || point.y.c1 != CM31::ZERO);
        }
        for point in result.line_ood_points.into_iter().flatten() {
            assert_ne!(point.c1, CM31::ZERO);
        }
        assert!(result.queries.iter().all(|query| *query < 1_024));
    }
}

#[derive(Clone, Copy, Debug)]
enum TailWeakening {
    LaterRootAfterOod,
    AlphaBeforeYMu,
    OmittedSecondOod,
    SwappedOodValues,
    LayerZeroUsesLineSamplerAndLabel,
    LaterLayerUsesCircleSamplerAndLabel,
    FinalBeforeLastAlpha,
    NonceBeforeFinal,
    QueriesBeforeGrinding,
}

struct WeakTailPrepared {
    transcript: Transcript,
    challenges: CandidateTailChallenges,
    queries_before_grinding: Option<[u32; CANDIDATE_QUERY_COUNT as usize]>,
    final_after_nonce: bool,
}

fn prepare_weakened_tail(
    weakening: TailWeakening,
    prefix: &CandidatePrefix<'_>,
    mode: CandidateOneLaneBatchingMode,
) -> WeakTailPrepared {
    let CandidatePrefixTranscript {
        mut transcript,
        result: prefix_result,
    } = begin_candidate_prefix_schedule_host(test_hash, prefix, &[0x5a; 32], &fixture_z()).unwrap();
    let kappa = match mode {
        CandidateOneLaneBatchingMode::FreshKappa => Some(transcript.challenge_qm31().unwrap()),
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
    let mut final_absorbed = false;

    for layer in 0..CANDIDATE_ROUND_COUNT {
        let root_is_delayed = matches!(weakening, TailWeakening::LaterRootAfterOod) && layer == 1;
        if layer > 0 && !root_is_delayed {
            absorb_candidate_round_root(&mut transcript, layer, prefix.rounds[layer].root.unwrap());
        }

        if matches!(weakening, TailWeakening::AlphaBeforeYMu) && layer == 0 {
            for point in &mut circle_ood_points {
                *point = transcript.challenge_secure_circle_point().unwrap();
            }
            absorb_candidate_sumcheck(&mut transcript, &prefix.rounds[layer]);
            alpha[layer] = transcript.challenge_qm31().unwrap();
            for (sample, mix) in mu[layer].iter_mut().enumerate() {
                absorb_candidate_ood_value(
                    &mut transcript,
                    label::M31_CIRCLE_OOD_VALUE,
                    layer,
                    sample,
                    prefix.rounds[layer].ood_value(sample).unwrap(),
                );
                *mix = transcript.challenge_qm31().unwrap();
            }
            continue;
        }

        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if matches!(weakening, TailWeakening::OmittedSecondOod) && layer == 0 && sample == 1 {
                continue;
            }

            let ood_label = if layer == 0 {
                if matches!(weakening, TailWeakening::LayerZeroUsesLineSamplerAndLabel) {
                    let point = transcript.challenge_ood_qm31().unwrap();
                    circle_ood_points[sample] = SecureCirclePoint {
                        x: point,
                        y: QM31::ZERO,
                    };
                    label::M31_LINE_OOD_VALUE
                } else {
                    let point = transcript.challenge_secure_circle_point().unwrap();
                    circle_ood_points[sample] = point;
                    label::M31_CIRCLE_OOD_VALUE
                }
            } else if matches!(
                weakening,
                TailWeakening::LaterLayerUsesCircleSamplerAndLabel
            ) && layer == 1
            {
                let point = transcript.challenge_secure_circle_point().unwrap();
                line_ood_points[layer - 1][sample] = point.x;
                label::M31_CIRCLE_OOD_VALUE
            } else {
                let point = transcript.challenge_ood_qm31().unwrap();
                line_ood_points[layer - 1][sample] = point;
                label::M31_LINE_OOD_VALUE
            };

            let value_sample = if matches!(weakening, TailWeakening::SwappedOodValues) && layer == 0
            {
                1 - sample
            } else {
                sample
            };
            absorb_candidate_ood_value(
                &mut transcript,
                ood_label,
                layer,
                sample,
                prefix.rounds[layer].ood_value(value_sample).unwrap(),
            );
            mu[layer][sample] = transcript.challenge_qm31().unwrap();
        }

        if root_is_delayed {
            absorb_candidate_round_root(&mut transcript, layer, prefix.rounds[layer].root.unwrap());
        }
        absorb_candidate_sumcheck(&mut transcript, &prefix.rounds[layer]);
        if matches!(weakening, TailWeakening::FinalBeforeLastAlpha)
            && layer == CANDIDATE_ROUND_COUNT - 1
        {
            absorb_candidate_final(&mut transcript, prefix);
            final_absorbed = true;
        }
        alpha[layer] = transcript.challenge_qm31().unwrap();
    }

    let final_after_nonce = matches!(weakening, TailWeakening::NonceBeforeFinal);
    if !final_absorbed && !final_after_nonce {
        absorb_candidate_final(&mut transcript, prefix);
    }
    let queries_before_grinding = if matches!(weakening, TailWeakening::QueriesBeforeGrinding) {
        Some(
            transcript
                .challenge_queries(CANDIDATE_QUERY_COUNT as usize, 1 << CANDIDATE_LOG_ROWS)
                .try_into()
                .unwrap(),
        )
    } else {
        None
    };

    WeakTailPrepared {
        transcript,
        challenges: CandidateTailChallenges {
            prefix: prefix_result,
            batching_mode: mode,
            kappa,
            second_point_scale,
            circle_ood_points,
            line_ood_points,
            mu,
            alpha,
        },
        queries_before_grinding,
        final_after_nonce,
    }
}

fn finish_weakened_tail(
    mut prepared: WeakTailPrepared,
    prefix: &CandidatePrefix<'_>,
) -> Result<CandidateTranscriptScheduleResult, CandidateTranscriptScheduleError> {
    let state_before_grinding = prepared.transcript.diagnostic_state();
    if !prepared
        .transcript
        .grinding_ok(prefix.nonce, CANDIDATE_GRINDING_BITS)
    {
        return Err(CandidateTranscriptScheduleError::GrindingRejected);
    }
    prepared
        .transcript
        .absorb(label::GRIND_NONCE, &prefix.nonce.to_le_bytes());
    if prepared.final_after_nonce {
        absorb_candidate_final(&mut prepared.transcript, prefix);
    }
    let queries = prepared.queries_before_grinding.unwrap_or_else(|| {
        prepared
            .transcript
            .challenge_queries(CANDIDATE_QUERY_COUNT as usize, 1 << CANDIDATE_LOG_ROWS)
            .try_into()
            .unwrap()
    });
    Ok(CandidateTranscriptScheduleResult {
        prefix: prepared.challenges.prefix,
        batching_mode: prepared.challenges.batching_mode,
        kappa: prepared.challenges.kappa,
        second_point_scale: prepared.challenges.second_point_scale,
        circle_ood_points: prepared.challenges.circle_ood_points,
        line_ood_points: prepared.challenges.line_ood_points,
        mu: prepared.challenges.mu,
        alpha: prepared.challenges.alpha,
        state_before_grinding,
        queries,
        state_after_queries: prepared.transcript.diagnostic_state(),
    })
}

fn weakened_tail_nonce(weakening: TailWeakening, prefix: &CandidatePrefix<'_>) -> u64 {
    let prepared =
        prepare_weakened_tail(weakening, prefix, CandidateOneLaneBatchingMode::FreshKappa);
    first_satisfying_nonce(&prepared.transcript)
}

#[test]
fn every_tail_ordering_vector_has_weakened_acceptance_and_canonical_rejection() {
    for weakening in [
        TailWeakening::LaterRootAfterOod,
        TailWeakening::AlphaBeforeYMu,
        TailWeakening::OmittedSecondOod,
        TailWeakening::SwappedOodValues,
        TailWeakening::LayerZeroUsesLineSamplerAndLabel,
        TailWeakening::LaterLayerUsesCircleSamplerAndLabel,
        TailWeakening::FinalBeforeLastAlpha,
        TailWeakening::NonceBeforeFinal,
        TailWeakening::QueriesBeforeGrinding,
    ] {
        let base_bytes = candidate_fixture();
        let base_prefix = CandidatePrefix::parse_exact(&base_bytes).unwrap();
        let nonce = weakened_tail_nonce(weakening, &base_prefix);
        let mut bytes = base_bytes;
        write_nonce(&mut bytes, nonce);
        let prefix = CandidatePrefix::parse_exact(&bytes).unwrap();

        let adversarial_vector = finish_weakened_tail(
            prepare_weakened_tail(weakening, &prefix, CandidateOneLaneBatchingMode::FreshKappa),
            &prefix,
        )
        .unwrap();
        let weakened_rerun = finish_weakened_tail(
            prepare_weakened_tail(weakening, &prefix, CandidateOneLaneBatchingMode::FreshKappa),
            &prefix,
        )
        .unwrap();
        assert_eq!(
            weakened_rerun, adversarial_vector,
            "weakened {weakening:?} did not accept its paired vector"
        );

        let canonical = run_candidate_transcript_schedule_host(
            test_hash,
            &prefix,
            &[0x5a; 32],
            &fixture_z(),
            CandidateOneLaneBatchingMode::FreshKappa,
        );
        assert!(
            canonical.is_err() || canonical.unwrap() != adversarial_vector,
            "canonical schedule accepted weakened {weakening:?} vector"
        );
    }
}
