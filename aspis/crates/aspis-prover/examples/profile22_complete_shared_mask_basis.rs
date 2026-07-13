//! Host-only complete shared-factor mask-only basis screen.

use std::{env, fs};

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_complete_shared_mask_basis_rank, CompleteSharedMaskBasisRankReport,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn print_report(label: &str, report: &CompleteSharedMaskBasisRankReport) {
    let selected = report
        .minimum_complete_prefix_lanes
        .map(|count| &report.deterministic_missing_lanes[..count]);
    println!(
        "schedule={label} baseline={} prefix={:?} minimum={:?} processed={} selected={selected:?} full_grid={} missing={} raw={} factor_fp={:#018x} c1_leaf={}+{}n q16_values={}n terminal={}n opening_at_min={:?} width_at_min={:?} elapsed_ms={}",
        report.prefix_masked_sumcheck_ranks_m31[0],
        report.prefix_masked_sumcheck_ranks_m31,
        report.minimum_complete_prefix_lanes,
        report.processed_missing_lanes,
        report.complete_full_domain_lanes,
        report.missing_full_domain_lanes,
        report.every_processed_extra_raw_rank_m31,
        report.factor_schedule_fingerprint,
        report.c1_leaf_bytes_before,
        report.c1_leaf_delta_bytes_per_lane,
        report.q16_opened_value_delta_bytes_per_lane,
        report.three_terminal_delta_bytes_per_lane,
        report.serialized_opening_delta_bytes_at_minimum,
        report.generator_width_at_minimum,
        report.elapsed_millis,
    );
}

fn main() {
    let proof_path = env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".to_owned()
    });
    let proof = fs::read(proof_path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("profile-21 prefix");
    let schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("profile-21 schedule")
        .base;

    let frozen = probe_atomic_state_only_complete_shared_mask_basis_rank(&schedule)
        .expect("frozen complete shared-mask rank");
    print_report("frozen", &frozen);

    let i = state_only_mask_tower_basis(1);
    let u = state_only_mask_tower_basis(2);
    let mut nonzero_last = schedule;
    nonzero_last.prefix.z.fill(QM31::ONE);
    nonzero_last.prefix.z[6] = QM31::ZERO;
    nonzero_last.prefix.z[8] = i;
    nonzero_last.prefix.z[9] = u;
    let nonzero_last_report =
        probe_atomic_state_only_complete_shared_mask_basis_rank(&nonzero_last)
            .expect("nonzero-last-determinant complete shared-mask rank");
    print_report("nonzero_last_determinant", &nonzero_last_report);

    let mut affine = nonzero_last;
    let thirty_two = QM31::from_cm31(CM31::from_m31(M31(32)));
    affine.prefix.z[0] = QM31::ZERO.sub(thirty_two.add(i).mul_m31(M31(9).inv()));
    let affine_report = probe_atomic_state_only_complete_shared_mask_basis_rank(&affine)
        .expect("affine-degenerate complete shared-mask rank");
    print_report("last_round_affine_degenerate", &affine_report);
}
