//! Audit one mined Profile-23 proof against the fixed atomic fixture.
//!
//! This is deliberately a verifier-only executable. It first runs the
//! production host verifier (including every PoW check), then independently
//! replays selector branches 0/1/2, evaluates the exact complete-Good23
//! predicate on all three, and requires the proof to carry the least good
//! selector. The on-chain verifier does not enforce that honest-prover
//! selection policy; its soundness ledger instead permits any of the three
//! branches.

use std::{env, fs};

use aspis_core::field::M31;
use aspis_core::state_only_prefix::StateOnlyProfile23Prefix;
use aspis_prover::state_only_good23::evaluate_profile23_query_candidates_host;
use aspis_prover::HOST_HASH;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::state_only_profile23::verify_atomic_state_only_profile23_v3;
use aspis_statement::{
    atomic_payment_statement_digest_v3, derive_nullifier, derive_owner_key, note_commitment,
    output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic,
};

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn fixture_statement() -> AtomicPaymentStatementV3 {
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
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    AtomicPaymentStatementV3 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &path).expect("derive fixture input root"),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &path).expect("derive fixture output root"),
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() {
    let mut args = env::args().skip(1);
    let proof_path = args.next().unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile23_v3_mined.bin".to_owned()
    });
    assert!(
        args.next().is_none(),
        "usage: profile23_mined_proof_audit [proof]"
    );

    let proof = fs::read(&proof_path).expect("read Profile23 proof");
    let statement = fixture_statement();

    // This is the production verifier, not the unmined diagnostic path.
    verify_atomic_state_only_profile23_v3(&proof, &statement, HOST_HASH, None)
        .expect("production Profile23 verification (including PoW)");

    let statement_digest =
        atomic_payment_statement_digest_v3(&statement, HOST_HASH).expect("statement digest");
    let (prefix, suffix) =
        StateOnlyProfile23Prefix::parse_from_proof(&proof).expect("parse Profile23 prefix");
    assert!(!suffix.is_empty(), "proof has no private-opening suffix");

    // This call performs three independent production-PoW transcript replays,
    // evaluates every complete-Good predicate, and only then chooses least.
    let evaluation =
        evaluate_profile23_query_candidates_host(HOST_HASH, &prefix, &statement_digest)
            .expect("recompute exact q3 complete-Good predicates");
    let least_good = evaluation
        .selected_selector
        .expect("all three Profile23 selector branches are bad");
    assert_eq!(
        prefix.query_selector, least_good,
        "proof selector is good/noncanonical but is not the least good selector"
    );

    println!("proof={proof_path}");
    println!("bytes={}", proof.len());
    println!("sha256={}", hex(&HOST_HASH(&[&proof])));
    println!("production_pow_and_full_verifier=green");
    println!("serialized_selector={}", prefix.query_selector);
    println!("least_good_selector={least_good}");
    for (selector, decision) in evaluation.decisions.iter().enumerate() {
        println!(
            "selector={selector} accepted={} root_rank={} gd_query_rank={} gd_terminal_rank={} h1_query_rank={} h1_terminal_rank={} product_fingerprint=0x{:016x}",
            decision.accepted,
            decision.root_neutral_rank_m31,
            decision.remaining_gd_query_rank_m31,
            decision.remaining_gd_terminal_rank_m31,
            decision.h1_query_rank_m31,
            decision.h1_terminal_rank_m31,
            decision.dynamic_product_fingerprint,
        );
    }
    println!("least_good_policy=green");
}
