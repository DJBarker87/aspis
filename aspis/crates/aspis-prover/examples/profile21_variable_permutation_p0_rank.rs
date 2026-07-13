//! Exact cached p0-only screen over the ten possible first sumcheck bits.

use std::fs;

use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::AtomicProfile21VariablePermutationP0Probe;
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn main() {
    let proof_path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".into()
    });
    let first = std::env::args()
        .nth(2)
        .map(|value| value.parse::<usize>().expect("first variable"))
        .unwrap_or(0);
    let end = std::env::args()
        .nth(3)
        .map(|value| value.parse::<usize>().expect("exclusive end variable"))
        .unwrap_or(10);
    assert!(first < end && end <= 10);

    let proof = fs::read(proof_path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("parse profile-21 prefix");
    let schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("replay profile-21 schedule");
    let probe = AtomicProfile21VariablePermutationP0Probe::new(&schedule.base)
        .expect("build cached p0 probe");

    for variable in first..end {
        let report = probe
            .probe_first_variable(&schedule.base, variable)
            .expect("permutation p0 rank");
        println!(
            "b={} pi={:?} guard={}/{} groups={}/{} group_same={} raw_c1={} raw_g={} sc={} p0_view={} mask={} semantic={} semantic_pivots={:?} legal={} legal_pivots={:?} green={} elapsed_ms={}",
            report.first_logical_variable,
            report.physical_to_logical_coordinates,
            report.conjugation_guard_run,
            report.conjugation_guard_passed,
            report.inactive_low_mask_groups,
            report.baseline_inactive_low_mask_groups,
            report.preserves_grouped_inactive_shape,
            report.raw_c1_rank_m31,
            report.raw_g_rank_m31,
            report.masked_sumcheck_rank_m31,
            report.p0_view_m31,
            report.p0_mask_rank_m31,
            report.p0_semantic_augmented_rank_m31,
            report.p0_semantic_new_pivots_m31,
            report.p0_legal_sumcheck_augmented_rank_m31,
            report.p0_legal_sumcheck_new_pivots_m31,
            report.p0_contains_conservative_semantic_and_legal_sumcheck,
            report.elapsed_millis,
        );
    }
}
