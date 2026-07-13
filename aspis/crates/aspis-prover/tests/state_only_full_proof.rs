use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
use aspis_core::state_only_prefix::{
    STATE_ONLY_PREFIX_OFFSETS, STATE_ONLY_RATE16_SHAPE, STATE_ONLY_RATE32_SHAPE,
    STATE_ONLY_RATE512_SHAPE,
};
use aspis_prover::state_only_candidate_prefix::{
    build_state_only_prefix_front_selected, StateOnlyPowMode,
};
use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
use aspis_prover::state_only_hiding_rank::{
    check_state_only_complete_hiding_rank, check_state_only_sparse_row_map_reference,
    probe_state_only_full_shared_hiding_rank, probe_state_only_hybrid_arity8_rank,
    probe_state_only_late_switch_rank, probe_state_only_masked_single_switch_joint_rank,
    StateOnlyHidingRankGateError,
};
use aspis_prover::state_only_proof::{build_hiding_state_only_proof, complete_state_only_proof};
use aspis_prover::HOST_HASH;
use aspis_statement::state_only_verify::verify_state_only_relation_with_inactive_masks_legacy_reference;
use aspis_statement::{
    build_spend_trace_v4, derive_nullifier, derive_owner_key, merkle_root, note_commitment,
    output_commitment, project_state_only_trace_v4, state_only_copy_inactive_row_masks_v4,
    verify_state_only_candidate, verify_state_only_candidate_unmined_for_diagnostics,
    verify_state_only_relation, Digest, MerklePath, SpendPublic, SpendWitness,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + index as u32 * 17))
}

fn fixture() -> (SpendPublic, SpendWitness) {
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

fn masks() -> (
    [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    Vec<QM31>,
) {
    let mut state = 0x5345_4c45_4354_3238u64;
    let mut next = || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31((state % u64::from(P)) as u32)
    };
    let mask_only = core::array::from_fn(|_| (0..1024).map(|_| next()).collect());
    let g = (0..1024)
        .map(|_| QM31 {
            c0: CM31::new(next(), next()),
            c1: CM31::new(next(), next()),
        })
        .collect();
    (mask_only, g)
}

fn build(shape: aspis_core::state_only_prefix::StateOnlyProfileShape) -> (SpendPublic, Vec<u8>) {
    let (public, witness) = fixture();
    let old = build_spend_trace_v4(&public, &witness).unwrap();
    let trace = project_state_only_trace_v4(&old).unwrap();
    let (mask_only, g) = masks();
    let front = build_state_only_prefix_front_selected(
        &public,
        &trace,
        &mask_only,
        &g,
        [0x51; 32],
        [shape.profile_id; 32],
        shape,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    let proof = complete_state_only_proof(
        &public,
        [0x51; 32],
        front,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    assert!(!proof.pow_valid);
    (public, proof.bytes)
}

fn build_with_private_entropy(
    shape: aspis_core::state_only_prefix::StateOnlyProfileShape,
) -> (SpendPublic, Vec<u8>) {
    let (public, witness) = fixture();
    let old = build_spend_trace_v4(&public, &witness).unwrap();
    let trace = project_state_only_trace_v4(&old).unwrap();
    let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
    let proof = build_hiding_state_only_proof(
        &public,
        trace,
        [0x51; 32],
        [shape.profile_id; 32],
        [0xd3; 32],
        &mut nonce_store,
        shape,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    assert!(!proof.pow_valid);
    (public, proof.bytes)
}

#[test]
fn rate16_width28_full_serialized_roundtrip_and_corruption_teeth() {
    let (public, proof) = build_with_private_entropy(STATE_ONLY_RATE16_SHAPE);
    verify_state_only_candidate_unmined_for_diagnostics(&proof, &public, &[0x51; 32], HOST_HASH)
        .unwrap();
    assert!(verify_state_only_candidate(&proof, &public, &[0x51; 32], HOST_HASH).is_err());

    for offset in [
        STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start,
        STATE_ONLY_PREFIX_OFFSETS.rounds[0].ood_values_start,
        STATE_ONLY_PREFIX_OFFSETS.rounds[2].sumcheck_start,
        STATE_ONLY_PREFIX_OFFSETS.final_polynomial_start,
        STATE_ONLY_PREFIX_OFFSETS.openings_start + 2,
        proof.len() - 1,
    ] {
        let mut corrupt = proof.clone();
        corrupt[offset] ^= 1;
        assert!(
            verify_state_only_candidate_unmined_for_diagnostics(
                &corrupt,
                &public,
                &[0x51; 32],
                HOST_HASH,
            )
            .is_err(),
            "accepted corruption at {offset}"
        );
    }
    for value in 0..aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_VALUE_COUNT {
        let mut corrupt = proof.clone();
        let offset = STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start + value * 16;
        corrupt[offset] ^= 1;
        assert!(
            verify_state_only_candidate_unmined_for_diagnostics(
                &corrupt,
                &public,
                &[0x51; 32],
                HOST_HASH,
            )
            .is_err(),
            "accepted statement value {value}"
        );
    }
    let mut changed_public = public.clone();
    changed_public.fee += 1;
    assert!(verify_state_only_candidate_unmined_for_diagnostics(
        &proof,
        &changed_public,
        &[0x51; 32],
        HOST_HASH,
    )
    .is_err());
}

#[test]
fn rate32_q29_width28_full_serialized_roundtrip() {
    let (public, proof) = build_with_private_entropy(STATE_ONLY_RATE32_SHAPE);
    let verified = verify_state_only_candidate_unmined_for_diagnostics(
        &proof,
        &public,
        &[0x51; 32],
        HOST_HASH,
    )
    .unwrap();
    assert_eq!(verified.schedule.query_count, 29);
}

#[test]
fn rate512_q16_width28_full_serialized_roundtrip() {
    let (public, proof) = build_with_private_entropy(STATE_ONLY_RATE512_SHAPE);
    let verified = verify_state_only_candidate_unmined_for_diagnostics(
        &proof,
        &public,
        &[0x51; 32],
        HOST_HASH,
    )
    .unwrap();
    assert_eq!(verified.schedule.query_count, 16);
    assert_eq!(verified.prefix.shape, STATE_ONLY_RATE512_SHAPE);

    assert_eq!(
        verify_state_only_relation_with_inactive_masks_legacy_reference(
            &verified.prefix,
            &verified.schedule,
            &verified.relation,
            state_only_copy_inactive_row_masks_v4(),
        ),
        Ok(())
    );
    for claim in 0..3 {
        let mut corrupted = *verified.relation;
        corrupted.claims[claim] = corrupted.claims[claim].add(QM31::ONE);
        let optimized =
            verify_state_only_relation(&verified.prefix, &verified.schedule, &corrupted);
        let legacy = verify_state_only_relation_with_inactive_masks_legacy_reference(
            &verified.prefix,
            &verified.schedule,
            &corrupted,
            state_only_copy_inactive_row_masks_v4(),
        );
        assert_eq!(optimized, legacy, "claim corruption {claim} diverged");
        assert!(optimized.is_err(), "accepted claim corruption {claim}");
    }

    for offset in [
        STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start,
        STATE_ONLY_PREFIX_OFFSETS.rounds[0].ood_values_start,
        STATE_ONLY_PREFIX_OFFSETS.rounds[1].sumcheck_start,
    ] {
        let mut corrupt = proof.clone();
        corrupt[offset] ^= 1;
        assert!(
            verify_state_only_candidate_unmined_for_diagnostics(
                &corrupt,
                &public,
                &[0x51; 32],
                HOST_HASH,
            )
            .is_err(),
            "optimized production relation accepted corruption at {offset}"
        );
    }
}

/// Expensive exact host gate measurement. Production proof completion calls
/// the same gate after the complete transcript/query schedule is known; this
/// ignored target keeps the matrix dimensions and runtime directly probeable.
#[test]
#[ignore]
fn rate32_q29_complete_joint_hiding_rank_gate() {
    let (public, witness) = fixture();
    let old = build_spend_trace_v4(&public, &witness).unwrap();
    let trace = project_state_only_trace_v4(&old).unwrap();
    let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
    let proof = build_hiding_state_only_proof(
        &public,
        trace,
        [0x51; 32],
        [0xe9; 32],
        [0xc7; 32],
        &mut nonce_store,
        STATE_ONLY_RATE32_SHAPE,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    std::fs::write(
        std::env::temp_dir().join("state_only_rank_q29_current.bin"),
        &proof.bytes,
    )
    .unwrap();
    check_state_only_sparse_row_map_reference(&proof.schedule).unwrap();
    assert!(matches!(
        check_state_only_complete_hiding_rank(&proof.schedule),
        Err(StateOnlyHidingRankGateError::JointPcsRank {
            got: 1024,
            want: 1144,
            ..
        })
    ));
    let report = probe_state_only_late_switch_rank(&proof.schedule, false).unwrap();
    std::eprintln!("strict-root1 rerandomization rank probe: {report:#?}");
    assert!(report.baseline_valid_witness_containment);
    assert_eq!(report.baseline_ambient_deficit_m31, 120);
    assert_eq!(report.late_switch_variables_qm31, 31);
    assert_eq!(report.late_switch_conditioned_kernel_qm31, 30);
    assert_eq!(report.late_switch_conditioned_rank, 1136);
    assert_eq!(report.late_switch_ambient_deficit_m31, 8);
    assert!(!report.complete_ambient_rank);
    let mut expected_rows = vec![1, 2];
    expected_rows.extend((1..=28).map(|index| 4 * index));
    expected_rows.push(3); // dependent variable fixed by the dense switch claim
    assert_eq!(report.late_switch_source_rows, expected_rows);
    assert_eq!(report.late_switch_complement_pivots_later_m31, 112);
    assert_eq!(report.late_switch_complement_pivots_relation_m31, 0);

    let joint = probe_state_only_masked_single_switch_joint_rank(&proof.schedule).unwrap();
    assert!(joint.masked_switch_joint_probe);
    assert_eq!(joint.masked_switch_variables_qm31, 122);
    assert_eq!(joint.masked_switch_observation_rank_qm31, 91);
    assert_eq!(joint.masked_switch_kernel_qm31, 31);
    assert_eq!(joint.masked_switch_q_randomness_rank_qm31, 29);
    assert_eq!(joint.masked_switch_q_coopening_rank_qm31, 29);
    assert_eq!(joint.masked_switch_otp_rank_qm31, 61);
    assert_eq!(joint.masked_switch_u_rank_qm31, 61);
    assert_eq!(
        joint.masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31,
        61
    );
    assert_eq!(joint.masked_switch_shared_root_increment_bytes, 1_920);
    assert_eq!(
        joint.masked_switch_standalone_increment_bytes,
        1_956 + 32 * joint.masked_switch_standalone_frontier_nodes
    );
    assert_eq!(joint.late_switch_conditioned_rank, 1144);
    assert_eq!(joint.late_switch_ambient_deficit_m31, 0);
    assert!(joint.complete_ambient_rank);
}

#[test]
#[ignore]
fn rate512_q16_slot_zero_masked_switch_complete_view_rank_gate() {
    let (public, witness) = fixture();
    let old = build_spend_trace_v4(&public, &witness).unwrap();
    let trace = project_state_only_trace_v4(&old).unwrap();
    let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
    let proof = build_hiding_state_only_proof(
        &public,
        trace,
        [0x51; 32],
        [0xf1; 32],
        [0xc8; 32],
        &mut nonce_store,
        STATE_ONLY_RATE512_SHAPE,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    let baseline = probe_state_only_full_shared_hiding_rank(&proof.schedule).unwrap();
    assert_eq!(baseline.masked_sumcheck_rank, 1080);
    assert_eq!(baseline.joint_pcs_rank, 712);
    assert_eq!(baseline.joint_pcs_declared_rank, 780);
    assert_eq!(baseline.baseline_ambient_deficit_m31, 68);
    assert!(!baseline.complete_ambient_rank);

    let joint = probe_state_only_masked_single_switch_joint_rank(&proof.schedule).unwrap();
    assert_eq!(joint.late_switch_source_rows[0], 4);
    assert_eq!(joint.late_switch_source_rows[1], 0);
    assert_eq!(joint.masked_switch_variables_qm31, 70);
    assert_eq!(joint.masked_switch_observation_rank_qm31, 52);
    assert_eq!(joint.masked_switch_kernel_qm31, 18);
    assert_eq!(joint.masked_switch_q_randomness_rank_qm31, 16);
    assert_eq!(joint.masked_switch_q_coopening_rank_qm31, 16);
    assert_eq!(joint.masked_switch_otp_rank_qm31, 35);
    assert_eq!(
        joint.masked_switch_u_plus_legacy_ood_diagnostic_rank_qm31,
        35
    );
    assert_eq!(joint.late_switch_complement_pivots_later_m31, 64);
    assert_eq!(joint.late_switch_complement_pivots_relation_m31, 4);
    assert_eq!(joint.late_switch_conditioned_rank, 780);
    assert_eq!(joint.masked_switch_shared_root_increment_bytes, 1088);
    assert_eq!(joint.masked_switch_standalone_increment_bytes, 10180);
    assert!(joint.complete_ambient_rank);
}

#[test]
#[ignore]
fn rate32_q29_hybrid_arity4_arity8_complete_view_rank_probe() {
    let (public, witness) = fixture();
    let old = build_spend_trace_v4(&public, &witness).unwrap();
    let trace = project_state_only_trace_v4(&old).unwrap();
    let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
    let proof = build_hiding_state_only_proof(
        &public,
        trace,
        [0x51; 32],
        [0xe9; 32],
        [0xc7; 32],
        &mut nonce_store,
        STATE_ONLY_RATE32_SHAPE,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .unwrap();
    let report = probe_state_only_hybrid_arity8_rank(&proof.schedule).unwrap();
    assert_eq!(report.pcs_schedule, "arity4_then_arity8_final32");
    assert!(report.baseline_valid_witness_containment);
    assert!(!report.complete_ambient_rank);
    assert_eq!(report.joint_pcs_m31, 1_636);
    assert_eq!(report.joint_pcs_declared_rank, 1_512);
    assert_eq!(report.joint_pcs_rank, 1_392);
    assert_eq!(report.baseline_ambient_deficit_m31, 120);
    std::eprintln!("hybrid arity-4/arity-8 rank probe: {report:#?}");
}
