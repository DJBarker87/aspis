//! Production-neutral exact-rank diagnostic for eliding dedicated G terminal
//! coordinates while retaining the literal PCS relation tail.

use std::fs;

use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_profile21_affine_g_claim_elision_rank_variant,
    probe_atomic_state_only_profile21_affine_g_z_aggregate_claim_rank_variant,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn parse_mask(value: &str) -> u8 {
    let mask = if value.len() == 3 && value.bytes().all(|byte| matches!(byte, b'0' | b'1')) {
        u8::from_str_radix(value, 2).expect("three-bit retained-terminal mask")
    } else {
        value.parse::<u8>().expect("retained-terminal mask")
    };
    assert!(mask <= 0b111, "retained-terminal mask must be <= 0b111");
    mask
}

fn main() {
    let proof_path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".into()
    });
    let insertion_coordinate = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "0".into())
        .parse::<usize>()
        .expect("insertion coordinate");
    let mode = std::env::args()
        .nth(3)
        .unwrap_or_else(|| "aggregate".into());
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
    let c = state_only_mask_tower_basis(2);
    // The legacy gamma value is reused only as a generic non-base-field tau
    // for this linear-rank diagnostic.  This example does not assert the new
    // Fiat--Shamir order; a production schedule must sample fresh tau after
    // the two G claims and must leave gamma later.
    let diagnostic_tau = schedule.base.prefix.gamma;
    let report = if mode == "aggregate" {
        probe_atomic_state_only_profile21_affine_g_z_aggregate_claim_rank_variant(
            &schedule,
            insertion_coordinate,
            c,
            diagnostic_tau,
        )
    } else {
        probe_atomic_state_only_profile21_affine_g_claim_elision_rank_variant(
            &schedule,
            insertion_coordinate,
            c,
            parse_mask(&mode),
        )
    }
    .expect("G claim-elision rank probe");
    let retained_terminal_mask = report.g_retained_terminal_mask;
    let elided = (0..3)
        .filter(|point| retained_terminal_mask & (1 << point) == 0)
        .collect::<Vec<_>>();
    println!(
        "{{\"query_count\":{},\"insertion_coordinate\":{},\"slice_coordinates_m31\":{:?},\"mode\":\"{}\",\"g_retained_terminal_mask\":{},\"g_elided_terminal_points\":{:?},\"g_uses_z_and_weighted_aggregate\":{},\"diagnostic_tau_source\":\"legacy_gamma_value_only_not_fs_order\",\"z_relation_weight_coordinates_m31\":{:?},\"g_single_terminal_reconstructible\":{:?},\"masked_sumcheck_rank_m31\":{},\"g_raw_rank_m31\":{},\"affine_g_raw_kernel_m31\":{},\"baseline_pcs_rank_m31\":{},\"baseline_semantic_augmented_rank_m31\":{},\"baseline_semantic_new_pivots_m31\":{:?},\"baseline_legal_sumcheck_augmented_rank_m31\":{},\"baseline_legal_sumcheck_new_pivots_m31\":{:?},\"baseline_contains\":{},\"affine_g_pcs_rank_m31\":{},\"affine_g_new_pivots_m31\":{:?},\"affine_g_semantic_augmented_rank_m31\":{},\"affine_g_semantic_new_pivots_m31\":{:?},\"affine_g_legal_sumcheck_augmented_rank_m31\":{},\"affine_g_legal_sumcheck_new_pivots_m31\":{:?},\"affine_g_contains\":{},\"g_minor_fingerprint\":\"0x{:016x}\",\"semantic_minor_fingerprint\":\"0x{:016x}\",\"legal_minor_fingerprint\":\"0x{:016x}\",\"elapsed_millis\":{}}}",
        schedule.base.query_count,
        report.insertion_coordinate,
        report.slice_value_coordinates_m31,
        mode,
        report.g_retained_terminal_mask,
        elided,
        report.g_uses_z_and_weighted_aggregate,
        report.z_relation_weight_coordinates_m31,
        report.g_single_terminal_reconstructible,
        report.masked_sumcheck_rank_m31,
        report.g_raw_rank_m31,
        report.affine_g_raw_kernel_m31,
        report.baseline_pcs_rank_m31,
        report.baseline_semantic_augmented_rank_m31,
        report.baseline_semantic_new_pivots_m31,
        report.baseline_legal_sumcheck_augmented_rank_m31,
        report.baseline_legal_sumcheck_new_pivots_m31,
        report.baseline_contains_conservative_semantic_and_legal_sumcheck,
        report.affine_g_pcs_rank_m31,
        report.affine_g_new_pivots_m31,
        report.semantic_augmented_rank_m31,
        report.semantic_new_pivots_m31,
        report.legal_sumcheck_augmented_rank_m31,
        report.legal_sumcheck_new_pivots_m31,
        report.contains_conservative_semantic_and_legal_sumcheck,
        report.affine_g_minor.fingerprint,
        report.semantic_minor.fingerprint,
        report.legal_sumcheck_minor.fingerprint,
        report.elapsed_millis,
    );
}
