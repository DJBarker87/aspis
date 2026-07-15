//! Reproduce the quarantined, unmined spend integration fixture.
//!
//! Fixed entropy and caller-selected query schedules are test-only. This
//! executable must never be enabled for production proof generation.

#[cfg(not(feature = "insecure-spend-fixture"))]
compile_error!(
    "spend_fixture requires --features insecure-spend-fixture; never enable it in production"
);

use std::{env, fs};

use aspis_core::field::M31;
use aspis_prover::state_only_candidate_prefix::StateOnlyPowMode;
use aspis_prover::state_only_entropy::StateOnlyAttemptSecrets;
use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
use aspis_prover::state_only_spend::build_hiding_atomic_state_only_spend_proof_v3;
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::state_only_spend::verify_atomic_state_only_spend_unmined_for_diagnostics_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic, SpendWitness,
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

fn main() {
    let output = env::args().nth(1).unwrap_or_else(|| {
        "crates/aspis-prover/fixtures/atomic_state_only_spend_v3_unmined.bin".into()
    });
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
    .expect("build deterministic spend fixture");

    verify_atomic_state_only_spend_unmined_for_diagnostics_v3(
        &built.bytes,
        &statement,
        HOST_HASH,
        None,
    )
    .expect("verify deterministic spend fixture");

    let sha256 = HOST_HASH(&[&built.bytes])
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert_eq!(built.bytes.len(), 67_327);
    assert_eq!(
        sha256,
        "a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238"
    );
    fs::write(&output, &built.bytes).expect("write spend fixture");
    println!("proof={output}");
    println!("bytes={}", built.bytes.len());
    println!("sha256={sha256}");
    println!("section_bytes={:?}", built.openings.section_bytes);
    println!("frontier_nodes={:?}", built.openings.frontier_nodes);
}
