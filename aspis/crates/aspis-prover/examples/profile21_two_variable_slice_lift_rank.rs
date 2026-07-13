//! Exact q16 checkpoint for the two-MSB restriction-kernel hiding lift.
//!
//! The promotable default is the base-field slice `(c,d)=(2,3)`.  `u` and
//! `1+u` are accepted only for diagnostics and are labelled non-promotable in
//! the emitted artifact.

use std::fs;
use std::time::Instant;

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::probe_atomic_state_only_profile21_two_variable_slice_lift_rank;
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn parse_slice(label: &str) -> QM31 {
    let u = state_only_mask_tower_basis(2);
    match label {
        "u" => u,
        "1+u" => QM31::ONE.add(u),
        value => QM31::from_cm31(CM31::from_m31(M31(value
            .parse::<u32>()
            .expect("M31 slice value")))),
    }
}

fn main() {
    let started = Instant::now();
    let proof_path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin".into()
    });
    let output_path = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "results/stage2/profile21_two_variable_slice_lift_rank.json".into());
    let c_label = std::env::args().nth(3).unwrap_or_else(|| "2".into());
    let d_label = std::env::args().nth(4).unwrap_or_else(|| "3".into());
    let c = parse_slice(&c_label);
    let d = parse_slice(&d_label);
    let promotable_base_field_slice =
        c.c0.b == M31::ZERO && c.c1 == CM31::ZERO && d.c0.b == M31::ZERO && d.c1 == CM31::ZERO;

    let proof = fs::read(&proof_path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("parse profile-21 prefix");
    let schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("replay profile-21 schedule");
    let report = probe_atomic_state_only_profile21_two_variable_slice_lift_rank(&schedule, c, d)
        .expect("two-variable restriction-kernel rank probe");

    let json = format!(
        concat!(
            "{{\n",
            "  \"schema\": \"aspis.profile21.two_variable_slice_lift_rank.v1\",\n",
            "  \"production_mutation\": false,\n",
            "  \"physical_new_coordinates\": [\"s_msb\", \"t_msb\"],\n",
            "  \"slice_c_label\": \"{}\",\n",
            "  \"slice_d_label\": \"{}\",\n",
            "  \"slice_c_coordinates_m31\": {:?},\n",
            "  \"slice_d_coordinates_m31\": {:?},\n",
            "  \"promotable_base_field_slice\": {},\n",
            "  \"extension_slice_is_diagnostic_only\": true,\n",
            "  \"query_count\": {},\n",
            "  \"message_log\": {},\n",
            "  \"codeword_domain_log\": {},\n",
            "  \"codeword_len\": {},\n",
            "  \"rate_denominator\": {},\n",
            "  \"final_coefficients_qm31\": {},\n",
            "  \"sumcheck_logical_rounds\": 10,\n",
            "  \"initial_restriction_guard\": {},\n",
            "  \"terminal_zero_guard\": {},\n",
            "  \"sparse_dense_differential_guard\": {},\n",
            "  \"sparse_dense_differential_rows\": {:?},\n",
            "  \"masked_sumcheck_rank_m31\": {},\n",
            "  \"g_raw_rank_m31\": {},\n",
            "  \"restriction_raw_kernel_m31\": {:?},\n",
            "  \"baseline_pcs_rank_m31\": {},\n",
            "  \"restriction_incremental_pcs_rank_m31\": {:?},\n",
            "  \"restriction_incremental_new_pivots_m31\": {:?},\n",
            "  \"restriction_pcs_rank_m31\": {},\n",
            "  \"semantic_augmented_rank_m31\": {},\n",
            "  \"semantic_new_pivots_m31\": {:?},\n",
            "  \"legal_sumcheck_augmented_rank_m31\": {},\n",
            "  \"legal_sumcheck_new_pivots_m31\": {:?},\n",
            "  \"contains_conservative_semantic_and_legal_sumcheck\": {},\n",
            "  \"restriction_minor_fingerprint\": \"0x{:016x}\",\n",
            "  \"semantic_minor_fingerprint\": \"0x{:016x}\",\n",
            "  \"legal_sumcheck_minor_fingerprint\": \"0x{:016x}\",\n",
            "  \"elapsed_millis\": {}\n",
            "}}\n"
        ),
        c_label,
        d_label,
        report.slice_c_coordinates_m31,
        report.slice_d_coordinates_m31,
        promotable_base_field_slice,
        report.query_count,
        report.message_log,
        report.codeword_domain_log,
        report.codeword_len,
        report.rate_denominator,
        report.final_coefficients_qm31,
        report.initial_restriction_guard,
        report.terminal_zero_guard,
        report.sparse_dense_differential_guard,
        report.sparse_dense_differential_rows,
        report.masked_sumcheck_rank_m31,
        report.g_raw_rank_m31,
        report.restriction_raw_kernel_m31,
        report.baseline_pcs_rank_m31,
        report.restriction_incremental_pcs_rank_m31,
        report.restriction_incremental_new_pivots_m31,
        report.restriction_pcs_rank_m31,
        report.semantic_augmented_rank_m31,
        report.semantic_new_pivots_m31,
        report.legal_sumcheck_augmented_rank_m31,
        report.legal_sumcheck_new_pivots_m31,
        report.contains_conservative_semantic_and_legal_sumcheck,
        report.restriction_minor.fingerprint,
        report.semantic_minor.fingerprint,
        report.legal_sumcheck_minor.fingerprint,
        report.elapsed_millis,
    );
    if let Some(parent) = std::path::Path::new(&output_path).parent() {
        fs::create_dir_all(parent).expect("create artifact directory");
    }
    fs::write(&output_path, json).expect("write rank artifact");
    println!(
        "two-variable slice c={} d={} base_field={} q={} rate=1/{} baseline={} masks={:?} pcs={} semantic={} legal={} green={} elapsed_ms={} wall_ms={} artifact={}",
        c_label,
        d_label,
        promotable_base_field_slice,
        report.query_count,
        report.rate_denominator,
        report.baseline_pcs_rank_m31,
        report.restriction_incremental_pcs_rank_m31,
        report.restriction_pcs_rank_m31,
        report.semantic_augmented_rank_m31,
        report.legal_sumcheck_augmented_rank_m31,
        report.contains_conservative_semantic_and_legal_sumcheck,
        report.elapsed_millis,
        started.elapsed().as_millis(),
        output_path,
    );
}
