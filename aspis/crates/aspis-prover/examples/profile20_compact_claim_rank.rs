//! Exact log10/q16 rank checkpoint for the joint compact-claim construction.

use std::fs;

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::state_only_mask_tower_basis;
use aspis_core::state_only_prefix::{
    run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyCandidatePrefix,
};
use aspis_prover::state_only_hiding_rank::{
    probe_atomic_state_only_compact_claim_bound_root0_multiplier_lean_rank,
    probe_atomic_state_only_compact_claim_bound_root0_multiplier_rank,
    probe_atomic_state_only_compact_claim_bound_root0_switch_rank,
    probe_atomic_state_only_compact_claim_rank,
    probe_atomic_state_only_compact_claim_rank_with_constant_pad, CompactBoundRoot0SwitchShape,
    CompactRoot0Multiplier,
};
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn parse_scalar(label: &str) -> QM31 {
    match label {
        "i" => state_only_mask_tower_basis(1),
        "u" => state_only_mask_tower_basis(2),
        "iu" => state_only_mask_tower_basis(3),
        "1+u" => QM31::ONE.add(state_only_mask_tower_basis(2)),
        "i+u" => state_only_mask_tower_basis(1).add(state_only_mask_tower_basis(2)),
        "1+i+iu" => QM31::ONE
            .add(state_only_mask_tower_basis(1))
            .add(state_only_mask_tower_basis(3)),
        value => QM31::from_cm31(CM31::from_m31(M31(value
            .parse::<u32>()
            .expect("M31 scalar")))),
    }
}

fn main() {
    let proof_path = std::env::args().nth(1).unwrap_or_else(|| {
        "results/stage2/proofs/atomic_state_only_profile20_v3_unmined.bin".into()
    });
    let tau_label = std::env::args().nth(2).unwrap_or_else(|| "1+u".into());
    let delta_label = std::env::args().nth(3).unwrap_or_else(|| "i+u".into());
    let mode = std::env::args().nth(4).unwrap_or_else(|| "base".into());
    let epsilon_label = std::env::args().nth(5).unwrap_or_else(|| "1+i+iu".into());
    let zeta_label = std::env::args().nth(6).unwrap_or_else(|| "u".into());
    let proof = fs::read(proof_path).expect("read profile-20 fixture");
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(&proof).expect("parse prefix");
    let schedule = run_atomic_state_only_transcript_schedule_host_unmined_for_diagnostics_v3(
        HOST_HASH,
        &prefix,
        &STATEMENT_DIGEST,
    )
    .expect("replay profile-20 schedule");
    let tau = parse_scalar(&tau_label);
    let delta = parse_scalar(&delta_label);
    let epsilon = parse_scalar(&epsilon_label);
    let zeta = parse_scalar(&zeta_label);
    let report = match mode.as_str() {
        "pad" => {
            probe_atomic_state_only_compact_claim_rank_with_constant_pad(&schedule, tau, delta)
        }
        "switch-d18" => probe_atomic_state_only_compact_claim_bound_root0_switch_rank(
            &schedule,
            tau,
            delta,
            epsilon,
            CompactBoundRoot0SwitchShape::D18M2,
        ),
        "switch-d19" => probe_atomic_state_only_compact_claim_bound_root0_switch_rank(
            &schedule,
            tau,
            delta,
            epsilon,
            CompactBoundRoot0SwitchShape::D19M3,
        ),
        "switch-high18" => probe_atomic_state_only_compact_claim_bound_root0_switch_rank(
            &schedule,
            tau,
            delta,
            epsilon,
            CompactBoundRoot0SwitchShape::D19Coefficient18,
        ),
        "switch-d19-affine" => probe_atomic_state_only_compact_claim_bound_root0_multiplier_rank(
            &schedule,
            tau,
            delta,
            epsilon,
            CompactBoundRoot0SwitchShape::D19M3,
            CompactRoot0Multiplier::fixed_affine(zeta),
        ),
        "switch-d19-affine-lean" => {
            probe_atomic_state_only_compact_claim_bound_root0_multiplier_lean_rank(
                &schedule,
                tau,
                delta,
                epsilon,
                CompactBoundRoot0SwitchShape::D19M3,
                CompactRoot0Multiplier::fixed_affine(zeta),
            )
        }
        "switch-d255-affine-lean" => {
            probe_atomic_state_only_compact_claim_bound_root0_multiplier_lean_rank(
                &schedule,
                tau,
                delta,
                epsilon,
                CompactBoundRoot0SwitchShape::D255Natural,
                CompactRoot0Multiplier::fixed_affine(zeta),
            )
        }
        "switch-d256-identity-lean" => {
            probe_atomic_state_only_compact_claim_bound_root0_multiplier_lean_rank(
                &schedule,
                tau,
                delta,
                epsilon,
                CompactBoundRoot0SwitchShape::D256Natural,
                CompactRoot0Multiplier::identity(),
            )
        }
        _ => probe_atomic_state_only_compact_claim_rank(&schedule, tau, delta),
    }
    .expect("compact-claim rank probe");
    println!(
        "{{\"geometry\":\"profile20-log10-q16\",\"mode\":\"{}\",\"tau_label\":\"{}\",\"delta_label\":\"{}\",\"epsilon_label\":\"{}\",\"tau_coordinates_m31\":{:?},\"delta_coordinates_m31\":{:?},\"query_count\":{},\"rate_denominator\":{},\"old_claims_qm31\":{},\"compact_claims_qm31\":{},\"saved_claims_qm31\":{},\"saved_claim_bytes\":{},\"full_domain_pad_probe\":{},\"pad_source_basis_m31\":{},\"pad_joint_raw_kernel_m31\":{},\"shared_unused_raw_rank_m31\":{},\"shared_unused_raw_rows_m31\":{},\"shared_unused_raw_kernel_m31\":{},\"masked_sumcheck_rank_m31\":{},\"baseline_pcs_rank_m31\":{},\"helper_augmented_rank_m31\":{},\"helper_new_pivots_m31\":{:?},\"bound_root0_switch_probe\":{},\"bound_root0_switch_coefficient_functional_mode\":{},\"bound_root0_switch_coefficient_index\":{},\"bound_root0_switch_message_qm31\":{},\"bound_root0_switch_randomness_qm31\":{},\"bound_root0_switch_dimension_qm31\":{},\"bound_root0_switch_variables_qm31\":{},\"bound_root0_switch_epsilon_coordinates_m31\":{:?},\"bound_root0_switch_code_basis_rank_qm31\":{},\"bound_root0_switch_code_basis_fingerprint\":\"0x{:016x}\",\"bound_root0_switch_folded_opening_rank_qm31\":{},\"bound_root0_switch_raw_opening_rank_qm31\":{},\"bound_root0_switch_raw_contains_folded_openings\":{},\"bound_root0_switch_u_plus_folded_rank_qm31\":{},\"bound_root0_switch_u_plus_folded_target_rank_qm31\":{},\"bound_root0_switch_u_plus_raw_rank_qm31\":{},\"bound_root0_switch_u_plus_raw_target_rank_qm31\":{},\"bound_root0_switch_conditioned_kernel_qm31\":{},\"bound_root0_switch_gamma_exponent\":{},\"bound_root0_switch_exact_full_tail\":{},\"bound_root0_switch_sparse_dense_tail_parity\":{},\"bound_root0_switch_pcs_augmented_rank_m31\":{},\"bound_root0_switch_new_pivots_m31\":{:?},\"bound_root0_switch_pivots_later_m31\":{},\"bound_root0_switch_pivots_ood_m31\":{},\"bound_root0_switch_pivots_relation_m31\":{},\"bound_root0_switch_pivots_final_m31\":{},\"semantic_augmented_rank_m31\":{},\"semantic_new_pivots_m31\":{:?},\"legal_sumcheck_augmented_rank_m31\":{},\"legal_sumcheck_new_pivots_m31\":{:?},\"contains_helper_semantic_and_legal_sumcheck\":{},\"bound_root0_switch_contains_semantic_and_legal_sumcheck\":{},\"helper_minor_fingerprint\":\"0x{:016x}\",\"bound_root0_switch_minor_fingerprint\":\"0x{:016x}\",\"semantic_minor_fingerprint\":\"0x{:016x}\",\"legal_sumcheck_minor_fingerprint\":\"0x{:016x}\",\"elapsed_millis\":{}}}",
        mode,
        tau_label,
        delta_label,
        epsilon_label,
        report.tau_coordinates_m31,
        report.delta_coordinates_m31,
        report.query_count,
        report.rate_denominator,
        report.old_claims_qm31,
        report.compact_claims_qm31,
        report.saved_claims_qm31,
        report.saved_claim_bytes,
        report.full_domain_pad_probe,
        report.pad_source_basis_m31,
        report.pad_joint_raw_kernel_m31,
        report.shared_unused_raw_rank_m31,
        report.shared_unused_raw_rows_m31,
        report.shared_unused_raw_kernel_m31,
        report.masked_sumcheck_rank_m31,
        report.baseline_pcs_rank_m31,
        report.helper_augmented_rank_m31,
        report.helper_new_pivots_m31,
        report.bound_root0_switch_probe,
        report.bound_root0_switch_coefficient_functional_mode,
        report.bound_root0_switch_coefficient_index,
        report.bound_root0_switch_message_qm31,
        report.bound_root0_switch_randomness_qm31,
        report.bound_root0_switch_dimension_qm31,
        report.bound_root0_switch_variables_qm31,
        report.bound_root0_switch_epsilon_coordinates_m31,
        report.bound_root0_switch_code_basis_rank_qm31,
        report.bound_root0_switch_code_basis_fingerprint,
        report.bound_root0_switch_folded_opening_rank_qm31,
        report.bound_root0_switch_raw_opening_rank_qm31,
        report.bound_root0_switch_raw_contains_folded_openings,
        report.bound_root0_switch_u_plus_folded_rank_qm31,
        report.bound_root0_switch_u_plus_folded_target_rank_qm31,
        report.bound_root0_switch_u_plus_raw_rank_qm31,
        report.bound_root0_switch_u_plus_raw_target_rank_qm31,
        report.bound_root0_switch_conditioned_kernel_qm31,
        report.bound_root0_switch_gamma_exponent,
        report.bound_root0_switch_exact_full_tail,
        report.bound_root0_switch_sparse_dense_tail_parity,
        report.bound_root0_switch_pcs_augmented_rank_m31,
        report.bound_root0_switch_new_pivots_m31,
        report.bound_root0_switch_pivots_later_m31,
        report.bound_root0_switch_pivots_ood_m31,
        report.bound_root0_switch_pivots_relation_m31,
        report.bound_root0_switch_pivots_final_m31,
        report.semantic_augmented_rank_m31,
        report.semantic_new_pivots_m31,
        report.legal_sumcheck_augmented_rank_m31,
        report.legal_sumcheck_new_pivots_m31,
        report.contains_helper_semantic_and_legal_sumcheck,
        report.bound_root0_switch_contains_semantic_and_legal_sumcheck,
        report.helper_minor.fingerprint,
        report.bound_root0_switch_minor.fingerprint,
        report.semantic_minor.fingerprint,
        report.legal_sumcheck_minor.fingerprint,
        report.elapsed_millis,
    );
    println!(
        "multiplier={{\"zeta_label\":\"{}\",\"lean_x_only\":{},\"degree\":{},\"fingerprint\":\"0x{:016x}\",\"product_dimension_qm31\":{},\"product_max_root_slot\":{},\"product_basis_fingerprint\":\"0x{:016x}\",\"pointwise_identity\":{},\"fold_identity\":{}}}",
        zeta_label,
        report.bound_root0_switch_lean_x_only_mode,
        report.bound_root0_switch_multiplier_degree,
        report.bound_root0_switch_multiplier_fingerprint,
        report.bound_root0_switch_product_dimension_qm31,
        report.bound_root0_switch_product_max_root_slot,
        report.bound_root0_switch_product_basis_fingerprint,
        report.bound_root0_switch_pointwise_product_identity,
        report.bound_root0_switch_fold_product_identity,
    );
}
