use std::sync::OnceLock;

use aspis_core::field::M31;
use aspis_core::state_only_prefix::{STATE_ONLY_PREFIX_OFFSETS, STATE_ONLY_RATE512_SHAPE};
use aspis_prover::state_only_candidate_prefix::StateOnlyPowMode;
use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
use aspis_prover::state_only_proof::build_hiding_atomic_state_only_proof_v3;
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    verify_atomic_state_only_candidate_unmined_for_diagnostics_v3,
    verify_atomic_state_only_candidate_v3, AtomicPaymentStatementV3, Digest, MerklePath,
    SpendPublic, SpendWitness,
};

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

fn built() -> &'static (AtomicPaymentStatementV3, Vec<u8>) {
    static BUILT: OnceLock<(AtomicPaymentStatementV3, Vec<u8>)> = OnceLock::new();
    BUILT.get_or_init(|| {
        let (statement, witness) = fixture();
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let proof = build_hiding_atomic_state_only_proof_v3(
            &statement,
            &witness,
            [20; 32],
            [0xd3; 32],
            &mut nonces,
            STATE_ONLY_RATE512_SHAPE,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .unwrap();
        assert!(!proof.pow_valid);
        (statement, proof.bytes)
    })
}

#[test]
fn atomic_profile20_roundtrip_binds_the_sumcheck_terminal() {
    let (statement, proof) = built();
    let verified = verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
        proof, statement, HOST_HASH, None,
    )
    .unwrap();
    assert_eq!(verified.prefix.shape, STATE_ONLY_RATE512_SHAPE);
    assert_eq!(verified.schedule.query_count, 16);
    assert_eq!(proof.len(), 56_044);
    assert!(verify_atomic_state_only_candidate_v3(proof, statement, HOST_HASH).is_err());
}

#[test]
fn every_atomic_public_field_is_in_the_fiat_shamir_binding() {
    let (statement, proof) = built();
    let mut variants = Vec::new();
    let mut changed = statement.clone();
    changed.pool[0] ^= 1;
    variants.push(changed);
    let mut changed = statement.clone();
    changed.sequence += 1;
    variants.push(changed);
    for selector in 0..4 {
        let mut changed = statement.clone();
        let digest = match selector {
            0 => &mut changed.spend.anchor,
            1 => &mut changed.spend.nullifier,
            2 => &mut changed.spend.output_commitment,
            _ => &mut changed.output_anchor,
        };
        digest[0] = digest[0].add(M31::ONE);
        variants.push(changed);
    }
    let mut changed = statement.clone();
    changed.spend.asset_id = changed.spend.asset_id.add(M31::ONE);
    variants.push(changed);
    let mut changed = statement.clone();
    changed.spend.fee += 1;
    variants.push(changed);

    for (index, changed) in variants.iter().enumerate() {
        assert!(
            verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
                proof, changed, HOST_HASH, None,
            )
            .is_err(),
            "accepted changed atomic public field {index}"
        );
    }
}

#[test]
fn atomic_proof_corruption_teeth_cover_terminal_relation_and_openings() {
    let (statement, proof) = built();
    for offset in [
        STATE_ONLY_PREFIX_OFFSETS.initial_mask_claim_start,
        STATE_ONLY_PREFIX_OFFSETS.sumcheck_start,
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
            verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
                &corrupt, statement, HOST_HASH, None,
            )
            .is_err(),
            "accepted corruption at {offset}"
        );
    }
}
