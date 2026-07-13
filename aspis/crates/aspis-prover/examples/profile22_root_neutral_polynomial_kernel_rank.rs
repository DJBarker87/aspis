use std::{env, fs};

use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix,
};
use aspis_prover::state_only_hiding_rank::probe_profile22_root_neutral_polynomial_kernel_rank;
use aspis_prover::HOST_HASH;

fn decode_digest(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64, "statement digest must be 32-byte hex");
    let mut digest = [0u8; 32];
    for (index, byte) in digest.iter_mut().enumerate() {
        *byte =
            u8::from_str_radix(&value[2 * index..2 * index + 2], 16).expect("statement digest hex");
    }
    digest
}

fn main() {
    let path = env::args().nth(1).expect(
        "usage: profile22_root_neutral_polynomial_kernel_rank <profile22-proof> <statement-digest-hex>",
    );
    let statement_digest =
        decode_digest(&env::args().nth(2).expect("statement digest hex argument"));
    let proof = fs::read(path).expect("read profile22 proof");
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(&proof).expect("parse prefix");
    let schedule = run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &statement_digest,
    )
    .expect("replay profile22 schedule");
    let report = probe_profile22_root_neutral_polynomial_kernel_rank(&schedule)
        .expect("root-neutral polynomial-kernel rank probe");
    println!("{report:#?}");
}
