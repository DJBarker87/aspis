//! Host-only integration-valid zero-factor C1 prefix screen.

use std::{env, fs};

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral,
    Profile22ZeroFactorQm31TailRootNeutralReport,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn print_report(label: &str, report: &Profile22ZeroFactorQm31TailRootNeutralReport) {
    println!(
        "schedule={label} H={} G={} D={} pairing={} baseline={} rank={}/{} D_raw={} H1_inactive_raw={}/{} terminal={} checked={} minor={:#018x} c2_leaf={}+{} opening_delta={} width={}->{} complete={} elapsed_ms={}",
        report.production_h_generator_index,
        report.production_g_generator_index,
        report.tail_generator_index,
        report.g_delta_from_tail,
        report.baseline_existing_rank_m31,
        report.conditional_rank_m31,
        report.conditional_target_m31,
        report.tail_raw_rank_m31,
        report.h1_inactive_padding_raw_rank_m31,
        report.qm31_raw_target_m31,
        report.every_post_raw_source_terminal_zero,
        report.terminal_zero_sources_checked_m31,
        report.conditional_minor.fingerprint,
        report.c2_leaf_bytes_before,
        report.c2_leaf_delta_bytes,
        report.serialized_opening_delta_bytes_q16,
        report.generator_width_before,
        report.generator_width_after,
        report.complete,
        report.elapsed_millis,
    );
}

fn main() {
    let proof_path = env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin".to_owned()
    });
    let proof = fs::read(proof_path).expect("read profile-22 fixture");
    let (prefix, _) =
        StateOnlyCandidatePrefix::parse_from_proof(&proof).expect("profile-22 prefix");
    let schedule = run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &STATEMENT_DIGEST,
    )
    .expect("profile-22 schedule");

    let frozen = probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(&schedule)
        .expect("frozen zero-factor prefix rank");
    print_report("frozen", &frozen);

    let i = state_only_mask_tower_basis(1);
    let u = state_only_mask_tower_basis(2);
    let mut terminal_certificate = schedule;
    terminal_certificate.prefix.z.fill(QM31::ONE);
    terminal_certificate.prefix.z[6] = QM31::ZERO;
    terminal_certificate.prefix.z[8] = i;
    terminal_certificate.prefix.z[9] = u;
    let terminal =
        probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(&terminal_certificate)
            .expect("terminal-certificate zero-factor prefix rank");
    print_report("terminal_certificate", &terminal);

    let mut affine = terminal_certificate;
    let thirty_two = QM31::from_cm31(CM31::from_m31(M31(32)));
    affine.prefix.z[0] = QM31::ZERO.sub(thirty_two.add(i).mul_m31(M31(9).inv()));
    let affine = probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(&affine)
        .expect("affine-degenerate zero-factor prefix rank");
    print_report("last_round_affine_degenerate", &affine);
}
