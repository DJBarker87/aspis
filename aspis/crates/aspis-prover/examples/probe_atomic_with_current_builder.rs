use aspis_core::field::M31;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix, STATE_ONLY_RATE512_SHAPE,
};
use aspis_prover::state_only_candidate_prefix::StateOnlyPowMode;
use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
use aspis_prover::state_only_hiding_rank::probe_atomic_state_only_masked_single_switch_joint_rank;
use aspis_prover::state_only_proof::build_hiding_atomic_state_only_proof_v3;
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic, SpendWitness,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn main() {
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let path = MerklePath {
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
        merkle_path: path,
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
    let statement_digest =
        aspis_statement::atomic_payment_statement_digest_v3(&statement, HOST_HASH).unwrap();
    println!(
        "statement_digest={}",
        statement_digest
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    );
    let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
    let result = build_hiding_atomic_state_only_proof_v3(
        &statement,
        &witness,
        [20; 32],
        [0xd3; 32],
        &mut nonces,
        STATE_ONLY_RATE512_SHAPE,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    );
    match result {
        Ok(proof) => {
            println!("accepted bytes={}", proof.bytes.len());
            let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(&proof.bytes).unwrap();
            let schedule =
                run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
                    HOST_HASH,
                    &prefix,
                    &statement_digest,
                )
                .unwrap();
            let rank = probe_atomic_state_only_masked_single_switch_joint_rank(&schedule).unwrap();
            println!("masked_switch_rank={rank:#?}");
            if let Some(path) = std::env::var_os("ASPIS_WRITE_CURRENT_ATOMIC_PROOF") {
                std::fs::write(path, &proof.bytes).unwrap();
            }
        }
        Err(error) => println!("rejected: {error:?}"),
    }
}
