//! Wire-surface privacy regressions for quarantined spend.
//!
//! These are teeth, not the HVZK proof: the complete affine-containment and
//! EPRO arguments remain primary.  This inventory makes every public byte
//! explicit and catches accidental raw-witness serialization or an untracked
//! receipt/opening surface.

use std::collections::BTreeSet;
use std::ops::Range;

use aspis_core::field::M31;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlySpendPrefix, StateOnlyTranscriptScheduleResult, STATE_ONLY_PREFIX_LEN,
    STATE_ONLY_PREFIX_OFFSETS, STATE_ONLY_SPEND_D_CLAIMS_LEN, STATE_ONLY_SPEND_PREFIX_LEN,
};
use aspis_core::state_only_private_openings::StateOnlyPrivateOpening;
use aspis_core::state_only_spend_openings::{
    verify_state_only_spend_openings, StateOnlySpendOpeningRoots, VerifiedStateOnlySpendOpenings,
    SPEND_PRIVATE_SECTION_COUNT,
};
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::state_only_spend::{
    verify_atomic_state_only_spend_unmined_for_diagnostics_v3, VerifiedAtomicSpend,
};
use aspis_statement::{
    atomic_payment_statement_digest_v3, derive_nullifier, derive_owner_key, note_commitment,
    output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic, SpendWitness,
};

use crate::state_only_candidate_prefix::StateOnlyPowMode;
use crate::state_only_entropy::StateOnlyAttemptSecrets;
use crate::state_only_hiding::{InMemoryStateOnlyMaskNonceStore, StateOnlyMaskBuildError};
use crate::state_only_spend::{
    build_hiding_atomic_state_only_spend_proof_v3, StateOnlySpendBuildError,
};
use crate::HOST_HASH;

const ACTUAL_SPEND_PROOF: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/fixtures/atomic_state_only_spend_v3_unmined.bin"
));

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

fn actual_verified() -> VerifiedAtomicSpend<'static> {
    let (statement, _) = fixture();
    verify_atomic_state_only_spend_unmined_for_diagnostics_v3(
        ACTUAL_SPEND_PROOF,
        &statement,
        HOST_HASH,
        None,
    )
    .unwrap()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
enum PublicByteKind {
    Header,
    MaskNonce,
    MerkleRoot,
    InitialMaskClaim,
    MaskedSumcheck,
    StatementEvaluations,
    OodValues,
    RelationSumchecks,
    FinalPolynomial,
    WorkNonces,
    DClaims,
    QuerySelector,
    OpeningCounts,
    OpenedValues,
    OpenedSalts,
    MerkleFrontier,
}

const PUBLIC_BYTE_KIND_COUNT: usize = 16;

fn mark(
    coverage: &mut [Option<PublicByteKind>],
    totals: &mut [usize; PUBLIC_BYTE_KIND_COUNT],
    kind: PublicByteKind,
    range: Range<usize>,
) {
    assert!(range.start <= range.end && range.end <= coverage.len());
    for (offset, slot) in coverage[range.clone()].iter_mut().enumerate() {
        assert!(
            slot.replace(kind).is_none(),
            "overlapping spend public byte at {}",
            range.start + offset
        );
    }
    totals[kind as usize] += range.len();
}

fn absolute_offset(slice: &[u8]) -> usize {
    let base = ACTUAL_SPEND_PROOF.as_ptr() as usize;
    let pointer = slice.as_ptr() as usize;
    let offset = pointer.checked_sub(base).expect("slice begins in proof");
    assert!(offset + slice.len() <= ACTUAL_SPEND_PROOF.len());
    offset
}

fn opening_sections<'a>(
    openings: &'a VerifiedStateOnlySpendOpenings<'a>,
) -> [&'a StateOnlyPrivateOpening<'a>; SPEND_PRIVATE_SECTION_COUNT] {
    [
        &openings.c1,
        &openings.c2,
        &openings.later[0],
        &openings.later[1],
        &openings.later[2],
    ]
}

fn inventory_opening(
    coverage: &mut [Option<PublicByteKind>],
    totals: &mut [usize; PUBLIC_BYTE_KIND_COUNT],
    opening: &StateOnlyPrivateOpening<'_>,
) {
    let records_start = absolute_offset(opening.records);
    mark(
        coverage,
        totals,
        PublicByteKind::OpeningCounts,
        records_start - 2..records_start,
    );
    for ordinal in 0..opening.count {
        let record_start = records_start + ordinal * opening.record_width();
        mark(
            coverage,
            totals,
            PublicByteKind::OpenedValues,
            record_start..record_start + opening.value_width,
        );
        mark(
            coverage,
            totals,
            PublicByteKind::OpenedSalts,
            record_start + opening.value_width..record_start + opening.record_width(),
        );
    }
    let frontier_start = absolute_offset(opening.frontier);
    mark(
        coverage,
        totals,
        PublicByteKind::OpeningCounts,
        frontier_start - 4..frontier_start,
    );
    mark(
        coverage,
        totals,
        PublicByteKind::MerkleFrontier,
        frontier_start..frontier_start + opening.frontier.len(),
    );
}

#[test]
fn spend_public_proof_byte_inventory_is_gap_and_overlap_free() {
    let verified = actual_verified();
    let mut coverage = vec![None; ACTUAL_SPEND_PROOF.len()];
    let mut totals = [0usize; PUBLIC_BYTE_KIND_COUNT];
    let offsets = STATE_ONLY_PREFIX_OFFSETS;

    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::Header,
        offsets.header_start..offsets.mask_nonce_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::MaskNonce,
        offsets.mask_nonce_start..offsets.c1_root_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::MerkleRoot,
        offsets.c1_root_start..offsets.c2_root_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::MerkleRoot,
        offsets.c2_root_start..offsets.initial_mask_claim_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::InitialMaskClaim,
        offsets.initial_mask_claim_start..offsets.sumcheck_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::MaskedSumcheck,
        offsets.sumcheck_start..offsets.statement_evaluations_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::StatementEvaluations,
        offsets.statement_evaluations_start..offsets.rounds[0].record_start,
    );
    for round in offsets.rounds {
        if let Some(root_start) = round.root_start {
            mark(
                &mut coverage,
                &mut totals,
                PublicByteKind::MerkleRoot,
                root_start..round.ood_values_start,
            );
        }
        mark(
            &mut coverage,
            &mut totals,
            PublicByteKind::OodValues,
            round.ood_values_start..round.sumcheck_start,
        );
        mark(
            &mut coverage,
            &mut totals,
            PublicByteKind::RelationSumchecks,
            round.sumcheck_start..round.record_end,
        );
    }
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::FinalPolynomial,
        offsets.final_polynomial_start..offsets.nonce_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::WorkNonces,
        offsets.nonce_start..offsets.openings_start,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::DClaims,
        STATE_ONLY_PREFIX_LEN..STATE_ONLY_PREFIX_LEN + STATE_ONLY_SPEND_D_CLAIMS_LEN,
    );
    mark(
        &mut coverage,
        &mut totals,
        PublicByteKind::QuerySelector,
        STATE_ONLY_PREFIX_LEN + STATE_ONLY_SPEND_D_CLAIMS_LEN..STATE_ONLY_SPEND_PREFIX_LEN,
    );
    for opening in opening_sections(&verified.openings) {
        inventory_opening(&mut coverage, &mut totals, opening);
    }

    assert_eq!(ACTUAL_SPEND_PROOF.len(), 67_327);
    assert!(coverage.iter().all(Option::is_some));
    assert_eq!(totals[PublicByteKind::Header as usize], 16);
    assert_eq!(totals[PublicByteKind::MaskNonce as usize], 32);
    assert_eq!(totals[PublicByteKind::MerkleRoot as usize], 160);
    assert_eq!(totals[PublicByteKind::InitialMaskClaim as usize], 16);
    assert_eq!(totals[PublicByteKind::MaskedSumcheck as usize], 4_480);
    assert_eq!(totals[PublicByteKind::StatementEvaluations as usize], 1_344);
    assert_eq!(totals[PublicByteKind::OodValues as usize], 128);
    assert_eq!(totals[PublicByteKind::RelationSumchecks as usize], 448);
    assert_eq!(totals[PublicByteKind::FinalPolynomial as usize], 64);
    assert_eq!(totals[PublicByteKind::WorkNonces as usize], 48);
    assert_eq!(totals[PublicByteKind::DClaims as usize], 48);
    assert_eq!(totals[PublicByteKind::QuerySelector as usize], 1);
    assert_eq!(totals[PublicByteKind::OpeningCounts as usize], 30);
    assert_eq!(totals[PublicByteKind::OpenedValues as usize], 14_400);
    assert_eq!(totals[PublicByteKind::OpenedSalts as usize], 2_880);
    assert_eq!(totals[PublicByteKind::MerkleFrontier as usize], 43_232);
    assert_eq!(totals.iter().sum::<usize>(), ACTUAL_SPEND_PROOF.len());
}

fn digest_bytes(value: &Digest) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, limb) in value.iter().enumerate() {
        bytes[4 * index..4 * index + 4].copy_from_slice(&limb.0.to_le_bytes());
    }
    bytes
}

#[test]
fn spend_fixture_never_literally_serializes_private_witness_blocks() {
    let (_, witness) = fixture();
    let mut secret_digests = vec![
        witness.nullifier_key,
        witness.input_salt,
        witness.output_salt,
        witness.output_owner_key,
    ];
    secret_digests.extend_from_slice(&witness.merkle_path.siblings);
    for (index, secret) in secret_digests.iter().enumerate() {
        let bytes = digest_bytes(secret);
        assert!(
            !ACTUAL_SPEND_PROOF
                .windows(bytes.len())
                .any(|window| window == bytes),
            "literal private digest {index} appeared in spend"
        );
    }
    for bytes in [
        witness.value.to_le_bytes().to_vec(),
        witness.value_out.to_le_bytes().to_vec(),
        (witness.merkle_path.index as u64).to_le_bytes().to_vec(),
    ] {
        assert!(!ACTUAL_SPEND_PROOF
            .windows(bytes.len())
            .any(|window| window == bytes));
    }
}

fn spend_roots(verified: &VerifiedAtomicSpend<'_>) -> StateOnlySpendOpeningRoots {
    StateOnlySpendOpeningRoots {
        c1: *verified.prefix.base.c1_root,
        c2: *verified.prefix.base.c2_root,
        later: core::array::from_fn(|index| *verified.prefix.base.rounds[index + 1].root.unwrap()),
    }
}

fn mutate_root(roots: &mut StateOnlySpendOpeningRoots, section: usize) {
    match section {
        0 => roots.c1[0] ^= 1,
        1 => roots.c2[0] ^= 1,
        2..=4 => roots.later[section - 2][0] ^= 1,
        _ => unreachable!(),
    }
}

#[test]
fn spend_all_five_sections_bind_roots_values_salts_and_frontiers() {
    let verified = actual_verified();
    let roots = spend_roots(&verified);
    let queries = &verified.schedule.queries[..verified.schedule.query_count];
    let suffix = &ACTUAL_SPEND_PROOF[STATE_ONLY_SPEND_PREFIX_LEN..];

    for (section, opening) in opening_sections(&verified.openings).into_iter().enumerate() {
        let records = absolute_offset(opening.records) - STATE_ONLY_SPEND_PREFIX_LEN;
        let frontier = absolute_offset(opening.frontier) - STATE_ONLY_SPEND_PREFIX_LEN;
        for relative_offset in [records, records + opening.value_width, frontier] {
            let mut changed = suffix.to_vec();
            changed[relative_offset] ^= 1;
            assert!(
                verify_state_only_spend_openings(HOST_HASH, &roots, queries, &changed).is_err(),
                "spend section {section} mutation at {relative_offset} accepted"
            );
        }

        let mut changed_roots = roots;
        mutate_root(&mut changed_roots, section);
        assert!(
            verify_state_only_spend_openings(HOST_HASH, &changed_roots, queries, suffix).is_err(),
            "spend section {section} accepted against a changed root"
        );
    }
}

fn replay(proof: &[u8]) -> StateOnlyTranscriptScheduleResult {
    let (statement, _) = fixture();
    let statement_digest = atomic_payment_statement_digest_v3(&statement, HOST_HASH).unwrap();
    let (prefix, _) = StateOnlySpendPrefix::parse_from_proof(proof).unwrap();
    run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &statement_digest,
    )
    .unwrap()
}

fn zero_spend_prefix() -> [u8; STATE_ONLY_SPEND_PREFIX_LEN] {
    // Early-root mutations necessarily invalidate the real masked-sumcheck
    // proof. Use a parser-valid zero-polynomial spend prefix to isolate
    // transcript dependency boundaries.
    let mut bytes = [0u8; STATE_ONLY_SPEND_PREFIX_LEN];
    bytes[..STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start]
        .copy_from_slice(&ACTUAL_SPEND_PROOF[..STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start]);
    bytes[STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start] = 0x23;
    bytes
}

#[test]
fn spend_transcript_order_binds_d_claims_selector_and_work_before_challenges() {
    let baseline = replay(ACTUAL_SPEND_PROOF);

    let zero = zero_spend_prefix();
    let zero_baseline = replay(&zero);
    let mut changed_c1 = zero;
    changed_c1[STATE_ONLY_PREFIX_OFFSETS.c1_root_start] ^= 1;
    let c1 = replay(&changed_c1);
    assert_ne!(c1.prefix.lambda, zero_baseline.prefix.lambda);

    let mut changed_c2 = zero;
    changed_c2[STATE_ONLY_PREFIX_OFFSETS.c2_root_start] ^= 1;
    let c2 = replay(&changed_c2);
    assert_eq!(c2.prefix.lambda, zero_baseline.prefix.lambda);
    assert_eq!(c2.prefix.chi, zero_baseline.prefix.chi);
    assert_ne!(
        c2.prefix.batching.theta,
        zero_baseline.prefix.batching.theta
    );

    let mut changed_d_claim = ACTUAL_SPEND_PROOF.to_vec();
    changed_d_claim[STATE_ONLY_PREFIX_LEN] ^= 1;
    let d_claim = replay(&changed_d_claim);
    assert_eq!(d_claim.prefix.z, baseline.prefix.z);
    assert_ne!(d_claim.prefix.gamma, baseline.prefix.gamma);

    let mut changed_batch_nonce = ACTUAL_SPEND_PROOF.to_vec();
    changed_batch_nonce[STATE_ONLY_PREFIX_OFFSETS.batch_nonce_start] ^= 1;
    let batch_nonce = replay(&changed_batch_nonce);
    assert_eq!(batch_nonce.prefix.z, baseline.prefix.z);
    assert_ne!(batch_nonce.prefix.gamma, baseline.prefix.gamma);

    let mut changed_round0_ood = ACTUAL_SPEND_PROOF.to_vec();
    changed_round0_ood[STATE_ONLY_PREFIX_OFFSETS.rounds[0].ood_values_start] ^= 1;
    let round0_ood = replay(&changed_round0_ood);
    assert_eq!(
        round0_ood.circle_ood_points[0],
        baseline.circle_ood_points[0]
    );
    assert_ne!(round0_ood.mu[0][0], baseline.mu[0][0]);

    let mut changed_w1_root = ACTUAL_SPEND_PROOF.to_vec();
    changed_w1_root[STATE_ONLY_PREFIX_OFFSETS.rounds[1].root_start.unwrap()] ^= 1;
    let w1_root = replay(&changed_w1_root);
    assert_eq!(w1_root.alpha[0], baseline.alpha[0]);
    assert_ne!(
        w1_root.line_ood_points[0][0],
        baseline.line_ood_points[0][0]
    );

    let mut changed_final = ACTUAL_SPEND_PROOF.to_vec();
    changed_final[STATE_ONLY_PREFIX_OFFSETS.final_polynomial_start] ^= 1;
    let final_polynomial = replay(&changed_final);
    assert_eq!(final_polynomial.alpha, baseline.alpha);
    assert_ne!(
        final_polynomial.state_before_grinding,
        baseline.state_before_grinding
    );
    assert_ne!(
        &final_polynomial.queries[..final_polynomial.query_count],
        &baseline.queries[..baseline.query_count]
    );

    let mut changed_final_nonce = ACTUAL_SPEND_PROOF.to_vec();
    changed_final_nonce[STATE_ONLY_PREFIX_OFFSETS.nonce_start] ^= 1;
    let final_nonce = replay(&changed_final_nonce);
    assert_eq!(
        final_nonce.state_before_grinding,
        baseline.state_before_grinding
    );
    assert_ne!(
        &final_nonce.queries[..final_nonce.query_count],
        &baseline.queries[..baseline.query_count]
    );

    let selector_offset = STATE_ONLY_PREFIX_LEN + STATE_ONLY_SPEND_D_CLAIMS_LEN;
    let mut changed_selector = ACTUAL_SPEND_PROOF.to_vec();
    changed_selector[selector_offset] = 1;
    let selector = replay(&changed_selector);
    assert_eq!(
        selector.state_before_grinding,
        baseline.state_before_grinding
    );
    assert_ne!(
        &selector.queries[..selector.query_count],
        &baseline.queries[..baseline.query_count]
    );
}

fn opened_salts(openings: &VerifiedStateOnlySpendOpenings<'_>) -> BTreeSet<[u8; 32]> {
    let mut salts = BTreeSet::new();
    for opening in opening_sections(openings) {
        for ordinal in 0..opening.count {
            assert!(salts.insert(*opening.salt(ordinal).unwrap()));
        }
    }
    salts
}

#[test]
#[ignore = "full rate-1/512 Spend rerandomization; run explicitly in release mode"]
fn spend_fresh_attempt_rerandomizes_the_complete_public_view_and_burns_nonce() {
    let (statement, witness) = fixture();
    let alternate_attempt =
        StateOnlyAttemptSecrets::deterministic_spend_fixture([0x24; 32], [0x46; 32], [0x68; 32]);
    let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
    let alternate = build_hiding_atomic_state_only_spend_proof_v3(
        &statement,
        &witness,
        alternate_attempt,
        &mut nonces,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
        0,
    )
    .unwrap();
    assert_ne!(alternate.bytes, ACTUAL_SPEND_PROOF);
    assert_eq!(
        &alternate.bytes[..STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start],
        &ACTUAL_SPEND_PROOF[..STATE_ONLY_PREFIX_OFFSETS.mask_nonce_start]
    );
    let differing_positions = alternate
        .bytes
        .iter()
        .zip(ACTUAL_SPEND_PROOF)
        .filter(|(left, right)| left != right)
        .count();
    assert!(differing_positions > ACTUAL_SPEND_PROOF.len() / 2);

    let baseline = actual_verified();
    assert_ne!(alternate.roots.c1, *baseline.prefix.base.c1_root);
    assert_ne!(alternate.roots.c2, *baseline.prefix.base.c2_root);
    for (alternate_root, baseline_round) in alternate
        .roots
        .later
        .iter()
        .zip(baseline.prefix.base.rounds[1..].iter())
    {
        assert_ne!(alternate_root, baseline_round.root.unwrap());
    }
    let alternate_openings = verify_state_only_spend_openings(
        HOST_HASH,
        &alternate.roots,
        &alternate.schedule.queries[..alternate.schedule.query_count],
        &alternate.openings.bytes,
    )
    .unwrap();
    assert!(opened_salts(&baseline.openings).is_disjoint(&opened_salts(&alternate_openings)));

    let reused =
        StateOnlyAttemptSecrets::deterministic_spend_fixture([0x24; 32], [0x89; 32], [0xab; 32]);
    assert!(matches!(
        build_hiding_atomic_state_only_spend_proof_v3(
            &statement,
            &witness,
            reused,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
            0,
        ),
        Err(StateOnlySpendBuildError::Mask(
            StateOnlyMaskBuildError::ReusedMaskNonce
        ))
    ));
}
