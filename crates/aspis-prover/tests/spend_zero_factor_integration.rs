use aspis_core::field::{M31, QM31};
use aspis_core::state_only_prefix::{
    StateOnlySpendPrefix, STATE_ONLY_PREFIX_LEN, STATE_ONLY_SPEND_D_CLAIMS_LEN,
    STATE_ONLY_SPEND_PREFIX_LEN,
};
use aspis_prover::state_only_candidate_prefix::StateOnlyPowMode;
use aspis_prover::state_only_entropy::StateOnlyAttemptSecrets;
use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
use aspis_prover::state_only_spend::build_hiding_atomic_state_only_spend_proof_v3;
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_active_rows_v3, atomic_state_only_copy_inactive_row_masks_v3,
};
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::state_only_spend::{
    verify_atomic_state_only_spend_unmined_for_diagnostics_v4, SpendVerifyError,
};
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn fixture() -> (AtomicPaymentStatementV4, SpendWitness) {
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
    let statement = AtomicPaymentStatementV4 {
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
        deployment_domain: [0x5d; 32],
    };
    (statement, witness)
}

fn rejects(proof: &[u8], statement: &AtomicPaymentStatementV4) {
    assert!(verify_atomic_state_only_spend_unmined_for_diagnostics_v4(
        proof, statement, HOST_HASH, None,
    )
    .is_err());
}

#[test]
fn spend_d_tail_roundtrip_and_corruption_teeth() {
    let (statement, witness) = fixture();
    let attempt =
        StateOnlyAttemptSecrets::deterministic_spend_fixture([0x23; 32], [0x45; 32], [0x67; 32]);
    let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
    let built = build_hiding_atomic_state_only_spend_proof_v3(
        &statement,
        &witness,
        attempt,
        &mut nonces,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
        0,
    )
    .unwrap();
    assert!(!built.pow_valid);
    assert_eq!(built.query_selector, 0);
    assert_eq!(built.d.len(), 1024);
    assert_eq!(
        built.bytes.len(),
        STATE_ONLY_SPEND_PREFIX_LEN + built.openings.bytes.len()
    );

    let parsed = StateOnlySpendPrefix::parse_from_proof(&built.bytes)
        .unwrap()
        .0;
    assert_eq!(parsed.d_claims_bytes.len(), STATE_ONLY_SPEND_D_CLAIMS_LEN);
    assert_eq!(parsed.query_selector, 0);
    let verified = verify_atomic_state_only_spend_unmined_for_diagnostics_v4(
        &built.bytes,
        &statement,
        HOST_HASH,
        None,
    )
    .unwrap();
    assert_eq!(verified.relation.d_claims, built.d_claims);
    assert_eq!(verified.schedule.queries, built.schedule.queries);

    let mut active = [false; 1024];
    for &row in atomic_state_only_copy_active_rows_v3() {
        active[usize::from(row)] = true;
    }
    let inactive_sum = built
        .d
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| !active[*row])
        .fold(QM31::ZERO, |sum, value| sum.add(value.1));
    assert_eq!(inactive_sum, QM31::ZERO);
    // D is not one of the 64 deferred binary-copy masks used by H.
    assert_eq!(atomic_state_only_copy_inactive_row_masks_v3().len(), 64);

    let mut changed_d_claim = built.bytes.clone();
    changed_d_claim[STATE_ONLY_PREFIX_LEN] ^= 1;
    rejects(&changed_d_claim, &statement);

    let selector_offset = STATE_ONLY_PREFIX_LEN + STATE_ONLY_SPEND_D_CLAIMS_LEN;
    let mut changed_selector = built.bytes.clone();
    changed_selector[selector_offset] = 1;
    rejects(&changed_selector, &statement);
    let mut invalid_selector = built.bytes.clone();
    invalid_selector[selector_offset] = 3;
    assert!(matches!(
        verify_atomic_state_only_spend_unmined_for_diagnostics_v4(
            &invalid_selector,
            &statement,
            HOST_HASH,
            None,
        ),
        Err(SpendVerifyError::Prefix(_))
    ));

    // First C2 record: u16 count, then the 192-byte value. Mutate D's first
    // symbol at byte 128 without touching H/G.
    let c2_start = STATE_ONLY_SPEND_PREFIX_LEN + built.openings.section_bytes[0];
    let mut changed_d_opening = built.bytes.clone();
    changed_d_opening[c2_start + 2 + 128] ^= 1;
    rejects(&changed_d_opening, &statement);

    let mut trailing = built.bytes.clone();
    trailing.push(0xa5);
    rejects(&trailing, &statement);

    let sha256 = HOST_HASH(&[&built.bytes])
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert_eq!(built.bytes.len(), 64_447);
    assert_eq!(
        sha256,
        "cf3ba127153e726e0e6eb5e4f546b6562a9c57d1ae6ee6a0df6b25aac0863b3b"
    );
    assert_eq!(
        built.openings.section_bytes,
        [18_214, 14_182, 10_150, 8_422, 6_694]
    );
    assert_eq!(built.openings.frontier_nodes, [317, 317, 263, 209, 155]);
    eprintln!("spend_len={} sha256={sha256}", built.bytes.len());
}

#[test]
#[ignore = "slow: builds and verifies one complete unmined proof for each q3 selector"]
fn spend_all_three_selectors_build_and_verify() {
    let (statement, witness) = fixture();
    for selector in 0..3u8 {
        let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            [0x23; 32], [0x45; 32], [0x67; 32],
        );
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let built = build_hiding_atomic_state_only_spend_proof_v3(
            &statement,
            &witness,
            attempt,
            &mut nonces,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
            selector,
        )
        .unwrap();
        assert_eq!(built.query_selector, selector);

        let (parsed, _) = StateOnlySpendPrefix::parse_from_proof(&built.bytes).unwrap();
        assert_eq!(parsed.query_selector, selector);
        let verified = verify_atomic_state_only_spend_unmined_for_diagnostics_v4(
            &built.bytes,
            &statement,
            HOST_HASH,
            None,
        )
        .unwrap();
        assert_eq!(verified.schedule.queries, built.schedule.queries);
        assert_eq!(verified.schedule.query_count, 18);
    }
}
