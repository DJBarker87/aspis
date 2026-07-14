//! Executable provenance for the prospective profile-23 complete Good
//! liveness polynomial.

use std::{env, fs};

use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile23Prefix,
};
use aspis_prover::state_only_hiding_rank::{
    bind_profile23_complete_good_product_provenance,
    probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral,
    probe_profile22_root_neutral_polynomial_kernel_rank,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn main() {
    let proof_path = env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile23_v3_unmined.bin".to_owned()
    });
    let proof = fs::read(proof_path).expect("read profile-23 fixture");
    let (prefix, _) =
        StateOnlyProfile23Prefix::parse_from_proof(&proof).expect("profile-23 prefix");
    let schedule =
        run_atomic_state_only_profile23_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("profile-23 schedule");

    let root = probe_profile22_root_neutral_polynomial_kernel_rank(&schedule)
        .expect("root-neutral polynomial-kernel rank probe");
    eprintln!(
        "root_summary={{query_count:{}, rank:{}, fingerprint:0x{:016x}, degree_one:{}, degree_two:{}, q_individual:{}, q_total:{}, gamma_degree:{}, z_degree:{}, minimum_selectors:{}, complete:{}}}",
        root.query_count,
        root.joint_rank_m31,
        root.minor.fingerprint,
        root.selected_degree_one_q_columns,
        root.selected_degree_two_q_columns,
        root.q_individual_degree_bound,
        root.q_total_degree_bound,
        root.gamma_coordinate_total_degree_bound,
        root.z_total_degree_bound,
        root.minimum_selector_count_for_cap16_over_100_bits,
        root.complete,
    );
    let raw = probe_atomic_state_only_profile22_zero_factor_qm31_tail_root_neutral(&schedule)
        .expect("raw terminal Schur probes");
    eprintln!(
        "raw_summary={{query_count:{}, gd_query_rank:{}, gd_terminal_rank:{}, gd_fingerprint:0x{:016x}, h1_query_rank:{}, h1_terminal_rank:{}, h1_fingerprint:0x{:016x}, complete:{}}}",
        raw.query_count,
        raw.remaining_gd_query_rank_m31,
        raw.remaining_gd_terminal_schur_rank_m31,
        raw.remaining_gd_terminal_schur_minor.fingerprint,
        raw.h1_inactive_padding_query_rank_m31,
        raw.h1_inactive_padding_terminal_schur_rank_m31,
        raw.h1_inactive_padding_terminal_schur_minor.fingerprint,
        raw.complete,
    );
    let product = bind_profile23_complete_good_product_provenance(&root, &raw)
        .expect("complete Good product provenance");

    assert_eq!(root.minor.source_columns.len(), 1_404);
    assert_eq!(root.minor.fingerprint, 0x6b38_3866_2fbf_34db);
    assert_eq!(raw.remaining_gd_terminal_schur_rank_m31, 12);
    assert_eq!(raw.h1_inactive_padding_terminal_schur_rank_m31, 12);
    assert_eq!(raw.remaining_gd_query_rank_m31, 288);
    assert_eq!(raw.h1_inactive_padding_query_rank_m31, 288);
    assert_eq!(raw.remaining_gd_terminal_schur_z_degree, 120);
    assert_eq!(raw.h1_inactive_padding_terminal_schur_z_degree, 120);
    assert_eq!(
        raw.remaining_gd_terminal_schur_minor.fingerprint,
        0x1f34_525d_b611_d292
    );
    assert_eq!(
        raw.h1_inactive_padding_terminal_schur_minor.fingerprint,
        0xe702_15f0_b479_5f52
    );
    assert_eq!(
        raw.remaining_gd_terminal_schur_minor.pivot_rows,
        (0..12).collect::<Vec<_>>()
    );
    assert_eq!(
        raw.h1_inactive_padding_terminal_schur_minor.pivot_rows,
        (0..12).collect::<Vec<_>>()
    );
    assert!(raw
        .remaining_gd_terminal_schur_minor
        .pivot_values_m31
        .iter()
        .all(|&value| value != 0));
    assert!(raw
        .h1_inactive_padding_terminal_schur_minor
        .pivot_values_m31
        .iter()
        .all(|&value| value != 0));
    assert_eq!(product.q_total_degree_bound, 31_320);
    assert_eq!(product.complete_good_z_degree_bound, 41_280);
    assert_eq!(product.gamma_coordinate_total_degree_bound, 80_688);
    assert_eq!(product.continuous_total_degree_bound, 121_968);
    assert_eq!(product.product_fingerprint, 0xfc07_06f3_a304_ae26);
    assert!(product.complete);

    println!(
        "remaining_gd_terminal_schur_minor={:#?}",
        raw.remaining_gd_terminal_schur_minor
    );
    println!(
        "h1_inactive_padding_terminal_schur_minor={:#?}",
        raw.h1_inactive_padding_terminal_schur_minor
    );
    println!("profile23_complete_good_product={product:#?}");
}
