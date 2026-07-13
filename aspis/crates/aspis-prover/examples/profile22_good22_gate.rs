//! Host-only strong-Good22 evaluator for a complete profile-22 candidate.
//!
//! This tool never publishes a proof and is not called by the production
//! builder.  It exists to freeze and independently replay the schedule-only
//! predicate before an unpublished retry manager is considered.

use std::{env, fs};

use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix,
};
use aspis_prover::state_only_good22::{
    evaluate_profile22_strong_good_schedule, profile22_good_schedule_definition_fingerprint,
};
use aspis_prover::HOST_HASH;

fn decode_digest(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64, "statement digest must be 64 hex digits");
    core::array::from_fn(|index| {
        u8::from_str_radix(&value[2 * index..2 * index + 2], 16).expect("statement digest hex")
    })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() {
    let proof_path = env::args()
        .nth(1)
        .expect("usage: profile22_good22_gate <profile22-proof> <statement-digest-hex>");
    let statement_digest =
        decode_digest(&env::args().nth(2).expect("missing statement digest hex"));
    let proof = fs::read(proof_path).expect("read profile22 proof");
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(&proof).expect("parse profile22");
    let schedule = run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &statement_digest,
    )
    .expect("replay profile22 schedule");
    let decision = evaluate_profile22_strong_good_schedule(&schedule)
        .expect("canonical strong-Good22 rank builder");
    println!(
        "definition_fingerprint={}",
        hex(&profile22_good_schedule_definition_fingerprint(HOST_HASH))
    );
    println!("accepted={}", decision.accepted);
    println!("rejection={:?}", decision.rejection);
    println!("mask_rank_m31={}", decision.mask_rank_m31);
    println!(
        "physical_augmented_rank_m31={}",
        decision.physical_augmented_rank_m31
    );
    println!(
        "legal_sumcheck_augmented_rank_m31={}",
        decision.legal_sumcheck_augmented_rank_m31
    );
}
