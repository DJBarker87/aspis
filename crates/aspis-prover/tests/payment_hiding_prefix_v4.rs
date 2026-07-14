use aspis_core::circle_hiding_prefix::{
    run_payment_hiding_prefix_schedule_host,
    run_payment_hiding_transcript_schedule_host_unmined_for_diagnostics,
    PaymentHidingCandidatePrefix, PAYMENT_HIDING_PREFIX_LEN, PAYMENT_HIDING_PREFIX_OFFSETS,
};
use aspis_core::circle_hiding_verify::{
    verify_payment_hiding_candidate_segment,
    verify_payment_hiding_candidate_with_schedule_for_diagnostics, PaymentHidingVerifyError,
};
use aspis_core::circle_openings::CircleQuerySegment;
use aspis_core::circle_prefix::CandidateTranscriptScheduleError;
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_prover::payment_hiding_candidate_prefix::{
    build_payment_hiding_proof, PaymentHidingPowMode,
};
use aspis_prover::HOST_HASH;
use aspis_statement::{
    apply_direct_range_c1_masks_v4, apply_direct_range_witness_v4, build_spend_trace_v4,
    derive_nullifier, derive_owner_key, direct_range_c1_mask_cells_v4, merkle_root,
    note_commitment, output_commitment, Digest, MerklePath, SpendPublic, SpendWitness,
    COPY_HELPER_MASK_VARIABLES, PAYMENT_MASK_ORACLE_VALUES,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + index as u32 * 17))
}

fn spend_fixture() -> (SpendPublic, SpendWitness) {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let owner_key = derive_owner_key(&nullifier_key);
    let note = note_commitment(&owner_key, value, asset_id, &input_salt);
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
        index: 0x5_4321,
    };
    let public = SpendPublic {
        anchor: merkle_root(note, &merkle_path).unwrap(),
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output_commitment(&output_owner_key, value_out, asset_id, &output_salt),
        asset_id,
        fee: 1,
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
    (public, witness)
}

fn q(seed: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(seed), M31(seed + 1)),
        c1: CM31::new(M31(seed + 2), M31(seed + 3)),
    }
}

#[test]
fn real_depth20_profile15_one_mask_front_replays() {
    let (public, witness) = spend_fixture();
    let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
    apply_direct_range_witness_v4(&mut trace).unwrap();
    let c1_masks = (0..direct_range_c1_mask_cells_v4().len())
        .map(|index| M31(((index as u64 * 2_246_822_519 + 0x5a17) % u64::from(P)) as u32))
        .collect::<Vec<_>>();
    apply_direct_range_c1_masks_v4(&mut trace, &c1_masks).unwrap();
    let helper_masks = (0..COPY_HELPER_MASK_VARIABLES)
        .map(|index| q(11 + index as u32 * 29))
        .collect::<Vec<_>>();
    let payment_mask = (0..PAYMENT_MASK_ORACLE_VALUES)
        .map(|row| q(101 + row as u32 * 31))
        .collect::<Vec<_>>();
    let statement_digest = [0x74; 32];
    let built = build_payment_hiding_proof(
        &public,
        &trace,
        &helper_masks,
        &payment_mask,
        statement_digest,
        HOST_HASH,
        PaymentHidingPowMode::UnminedZero,
    )
    .unwrap();
    // This zero-nonce profile fixture has no query collisions. Together with
    // `no_collision_without_replacement_sampling_is_legacy_byte_and_state_identical`,
    // this pins the condition under which the protocol change preserves its
    // old query bytes and post-query transcript state exactly.
    for (index, query) in built.schedule.queries.iter().enumerate() {
        assert!(!built.schedule.queries[..index].contains(query));
    }

    assert!(built.bytes.len() > PAYMENT_HIDING_PREFIX_LEN);
    assert!(!built.pow_valid);
    assert_eq!(built.front.c2.leaves[0].len(), 128);
    assert_eq!(built.front.c2.encoded_columns.len(), 2);
    assert_eq!(built.material.statement_evaluations.len(), 102);
    assert_eq!(
        built.schedule.prefix.masked_terminal_claim,
        built.front.zerocheck.sumcheck.terminal_claim,
    );
    let parsed =
        PaymentHidingCandidatePrefix::parse_exact(&built.bytes[..PAYMENT_HIDING_PREFIX_LEN])
            .unwrap();
    let replay =
        run_payment_hiding_prefix_schedule_host(HOST_HASH, &parsed, &statement_digest).unwrap();
    assert_eq!(replay, built.schedule.prefix);
    let full_replay = run_payment_hiding_transcript_schedule_host_unmined_for_diagnostics(
        HOST_HASH,
        &parsed,
        &statement_digest,
    )
    .unwrap();
    assert_eq!(full_replay, built.schedule);

    let verified = verify_payment_hiding_candidate_with_schedule_for_diagnostics(
        &built.bytes,
        built.schedule,
        HOST_HASH,
        CircleQuerySegment::Full,
    )
    .unwrap();
    let c2_offset = PAYMENT_HIDING_PREFIX_LEN + verified.openings.layer0.offsets.c2_leaves;
    assert!(matches!(
        verify_payment_hiding_candidate_segment(
            &built.bytes,
            &statement_digest,
            HOST_HASH,
            CircleQuerySegment::Full,
        ),
        Err(PaymentHidingVerifyError::Transcript(
            CandidateTranscriptScheduleError::BatchGrindingRejected
        ))
    ));
    let mut corrupted_leaf = built.bytes.clone();
    corrupted_leaf[c2_offset] ^= 1;
    assert!(matches!(
        verify_payment_hiding_candidate_with_schedule_for_diagnostics(
            &corrupted_leaf,
            built.schedule,
            HOST_HASH,
            CircleQuerySegment::Full,
        ),
        Err(PaymentHidingVerifyError::Openings(_))
    ));

    let mut changed = built.bytes[..PAYMENT_HIDING_PREFIX_LEN].to_vec();
    changed[PAYMENT_HIDING_PREFIX_OFFSETS.statement_evaluations_start + 101 * 16] ^= 1;
    let parsed_changed = PaymentHidingCandidatePrefix::parse_exact(&changed).unwrap();
    let replay_changed =
        run_payment_hiding_prefix_schedule_host(HOST_HASH, &parsed_changed, &statement_digest)
            .unwrap();
    assert_ne!(replay_changed.gamma, replay.gamma);

    // The batching nonce is a distinct, transcript-bound record immediately
    // before gamma. Changing only that field must change gamma while leaving
    // every earlier derived object fixed.
    let mut changed_nonce = built.bytes[..PAYMENT_HIDING_PREFIX_LEN].to_vec();
    changed_nonce[PAYMENT_HIDING_PREFIX_OFFSETS.batch_nonce_start] ^= 1;
    let parsed_nonce = PaymentHidingCandidatePrefix::parse_exact(&changed_nonce).unwrap();
    let nonce_replay =
        run_payment_hiding_prefix_schedule_host(HOST_HASH, &parsed_nonce, &statement_digest)
            .unwrap();
    assert_eq!(nonce_replay.z, replay.z);
    assert_eq!(
        nonce_replay.masked_terminal_claim,
        replay.masked_terminal_claim
    );
    assert_ne!(nonce_replay.gamma, replay.gamma);
}
