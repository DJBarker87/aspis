//! Executable provenance for the prospective spend complete Good
//! liveness polynomial.

use std::{env, fs};

use aspis_core::state_only_prefix::{
    run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlySpendPrefix,
};
use aspis_prover::state_only_hiding_rank::{
    bind_spend_complete_good_product_provenance,
    probe_atomic_state_only_spend_zero_factor_qm31_tail_root_neutral,
    probe_spend_root_neutral_polynomial_kernel_rank,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0xf6, 0x9e, 0xf3, 0xbc, 0x54, 0x28, 0x47, 0x5f, 0x13, 0x88, 0x9b, 0xe7, 0x7a, 0x5d, 0x0a, 0x9b,
    0xe2, 0x4b, 0x9d, 0x78, 0xd1, 0x8d, 0x93, 0x17, 0x7b, 0x37, 0x21, 0xfc, 0x51, 0xf7, 0x64, 0x71,
];

fn main() {
    let proof_path = env::args().nth(1).unwrap_or_else(|| {
        "crates/aspis-prover/fixtures/atomic_state_only_spend_v4_unmined.bin".to_owned()
    });
    let proof = fs::read(proof_path).expect("read spend fixture");
    let (prefix, _) = StateOnlySpendPrefix::parse_from_proof(&proof).expect("spend prefix");
    let schedule = run_atomic_state_only_spend_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &STATEMENT_DIGEST,
    )
    .expect("spend schedule");

    let root = probe_spend_root_neutral_polynomial_kernel_rank(&schedule)
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
    let raw = probe_atomic_state_only_spend_zero_factor_qm31_tail_root_neutral(&schedule)
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
    let product = bind_spend_complete_good_product_provenance(&root, &raw)
        .expect("complete Good product provenance");

    assert_eq!(root.minor.source_columns.len(), 1_404);
    assert_eq!(root.minor.fingerprint, 0xc1e2_3e3a_cec5_5fc9);
    assert_eq!(raw.remaining_gd_terminal_schur_rank_m31, 12);
    assert_eq!(raw.h1_inactive_padding_terminal_schur_rank_m31, 12);
    assert_eq!(raw.remaining_gd_query_rank_m31, 288);
    assert_eq!(raw.h1_inactive_padding_query_rank_m31, 288);
    assert_eq!(raw.remaining_gd_terminal_schur_z_degree, 120);
    assert_eq!(raw.h1_inactive_padding_terminal_schur_z_degree, 120);
    assert_eq!(
        raw.remaining_gd_terminal_schur_minor.fingerprint,
        0x7ca2_57ac_a211_584a
    );
    assert_eq!(
        raw.h1_inactive_padding_terminal_schur_minor.fingerprint,
        0x2b09_c8e0_f643_b2bf
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
    assert_eq!(product.product_fingerprint, 0xb1af_7cc0_8b30_847d);
    assert!(product.complete);

    println!(
        "remaining_gd_terminal_schur_minor={:#?}",
        raw.remaining_gd_terminal_schur_minor
    );
    println!(
        "h1_inactive_padding_terminal_schur_minor={:#?}",
        raw.h1_inactive_padding_terminal_schur_minor
    );
    println!("spend_complete_good_product={product:#?}");
}
