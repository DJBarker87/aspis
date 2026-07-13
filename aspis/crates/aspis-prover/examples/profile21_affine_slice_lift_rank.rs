use std::fs;

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_with_query_count_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::probe_atomic_state_only_profile21_affine_extension_slice_lift_rank_variant;
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".into()
    });
    let proof = fs::read(path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("parse profile-21 prefix");
    let insertion_coordinate = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "0".into())
        .parse::<usize>()
        .expect("insertion coordinate");
    let slice_spec = std::env::args().nth(3).unwrap_or_else(|| "2".into());
    let query_count = std::env::args()
        .nth(4)
        .unwrap_or_else(|| "16".into())
        .parse::<usize>()
        .expect("query count");
    let schedule = if query_count == 16 {
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
    } else {
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_with_query_count_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
            query_count,
        )
    }
    .expect("replay profile-21 schedule");
    let slice_value = match slice_spec.as_str() {
        "u" => state_only_mask_tower_basis(2),
        "i" => state_only_mask_tower_basis(1),
        "iu" => state_only_mask_tower_basis(3),
        value => QM31::from_cm31(CM31::from_m31(M31(value
            .parse::<u32>()
            .expect("M31 slice value")))),
    };
    let report = probe_atomic_state_only_profile21_affine_extension_slice_lift_rank_variant(
        &schedule,
        insertion_coordinate,
        slice_value,
    )
    .expect("affine-slice lift rank probe");
    println!(
        "b={} c={} c_coords={:?} sc={} g_raw={} g_kernel={} baseline={} g={} g_pivots={:?} sem={} sem_pivots={:?} legal={} legal_pivots={:?} g_green={} gh={} h_pivots={:?} gh_sem={} gh_sem_pivots={:?} gh_legal={} gh_legal_pivots={:?} gh_green={} g_fp=0x{:016x} h_fp=0x{:016x} sem_fp=0x{:016x} legal_fp=0x{:016x} ms={}",
        report.insertion_coordinate,
        slice_spec,
        report.slice_value_coordinates_m31,
        report.masked_sumcheck_rank_m31,
        report.g_raw_rank_m31,
        report.affine_g_raw_kernel_m31,
        report.baseline_pcs_rank_m31,
        report.affine_g_pcs_rank_m31,
        report.affine_g_new_pivots_m31,
        report.semantic_augmented_rank_m31,
        report.semantic_new_pivots_m31,
        report.legal_sumcheck_augmented_rank_m31,
        report.legal_sumcheck_new_pivots_m31,
        report.contains_conservative_semantic_and_legal_sumcheck,
        report.affine_g_and_h_pcs_rank_m31,
        report.affine_g_and_h_new_pivots_m31,
        report.affine_g_and_h_semantic_augmented_rank_m31,
        report.affine_g_and_h_semantic_new_pivots_m31,
        report.affine_g_and_h_legal_sumcheck_augmented_rank_m31,
        report.affine_g_and_h_legal_sumcheck_new_pivots_m31,
        report.affine_g_and_h_contains_conservative_semantic_and_legal_sumcheck,
        report.affine_g_minor.fingerprint,
        report.affine_h_minor.fingerprint,
        report.semantic_minor.fingerprint,
        report.legal_sumcheck_minor.fingerprint,
        report.elapsed_millis,
    );
}
