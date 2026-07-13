//! Exact current-log10 rank checkpoint for the compact claim construction.

use std::fs;

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::probe_atomic_state_only_profile21_compact_claim_rank;
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn parse_tau(label: &str) -> QM31 {
    match label {
        "u" => state_only_mask_tower_basis(2),
        "1+u" => QM31::ONE.add(state_only_mask_tower_basis(2)),
        value => QM31::from_cm31(CM31::from_m31(M31(value.parse::<u32>().expect("M31 tau")))),
    }
}

fn main() {
    let proof_path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".into()
    });
    let tau_label = std::env::args().nth(2).unwrap_or_else(|| "1+u".into());
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
    let report =
        probe_atomic_state_only_profile21_compact_claim_rank(&schedule, parse_tau(&tau_label))
            .expect("compact-claim rank probe");
    println!(
        "tau={} coords={:?} q={} rate=1/{} claims={}->{} saved={}B raw={}/{} raw_kernel={} sc={} pcs={} helper={} helper_pivots={:?} semantic={} semantic_pivots={:?} legal={} legal_pivots={:?} green={} helper_fp=0x{:016x} semantic_fp=0x{:016x} legal_fp=0x{:016x} ms={}",
        tau_label,
        report.tau_coordinates_m31,
        report.query_count,
        report.rate_denominator,
        report.old_claims_qm31,
        report.compact_claims_qm31,
        report.saved_claim_bytes,
        report.shared_unused_raw_rank_m31,
        report.shared_unused_raw_rows_m31,
        report.shared_unused_raw_kernel_m31,
        report.masked_sumcheck_rank_m31,
        report.baseline_pcs_rank_m31,
        report.helper_augmented_rank_m31,
        report.helper_new_pivots_m31,
        report.semantic_augmented_rank_m31,
        report.semantic_new_pivots_m31,
        report.legal_sumcheck_augmented_rank_m31,
        report.legal_sumcheck_new_pivots_m31,
        report.contains_helper_semantic_and_legal_sumcheck,
        report.helper_minor.fingerprint,
        report.semantic_minor.fingerprint,
        report.legal_sumcheck_minor.fingerprint,
        report.elapsed_millis,
    );
}
