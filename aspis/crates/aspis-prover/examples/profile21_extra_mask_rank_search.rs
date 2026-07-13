//! Production-neutral exact-rank search for ordinary C1 repair masks.

use std::env;
use std::fs;

use aspis_core::state_only_prefix::{
    run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3,
    StateOnlyProfile21Prefix,
};
use aspis_prover::state_only_hiding_rank::probe_atomic_state_only_profile21_extra_mask_rank;
use aspis_prover::HOST_HASH;

const STATEMENT_DIGEST: [u8; 32] = [
    0x52, 0xe9, 0x6f, 0x99, 0x75, 0x6f, 0xe8, 0xfd, 0x2d, 0x8b, 0x7a, 0x70, 0x00, 0x19, 0xb1, 0x43,
    0xd7, 0xeb, 0x54, 0x9a, 0xf1, 0xbf, 0x1a, 0xe9, 0x87, 0xe9, 0x9a, 0x75, 0xca, 0xdc, 0xd4, 0xc9,
];

fn main() {
    let candidate = env::args()
        .nth(1)
        .unwrap_or_else(|| "add-shared-23-r0".to_owned());
    let proof_path = env::args()
        .nth(2)
        .unwrap_or_else(|| "/tmp/atomic-current.bin".to_owned());
    let proof = fs::read(&proof_path).expect("read profile-21 fixture");
    let (prefix, _) =
        StateOnlyProfile21Prefix::parse_from_proof(&proof).expect("profile-21 prefix");
    let schedule =
        run_atomic_state_only_profile21_transcript_schedule_host_unmined_for_diagnostics_v3(
            HOST_HASH,
            &prefix,
            &STATEMENT_DIGEST,
        )
        .expect("profile-21 schedule");
    let report = probe_atomic_state_only_profile21_extra_mask_rank(&schedule, &candidate)
        .expect("extra-mask exact rank probe");
    println!(
        "candidate={} fast={} raw={:?} g_raw={} extra_g_raw={:?} sc={} pre_helper={} pre_scalar_m={} pcs={} ambient={} semantic={} semantic_pivots={:?} legal={} legal_pivots={:?} compatibility={} scalar_m={} scalar_obs_rank={} scalar_kernel={} scalar_pivots={:?} scalar_contains={} degree={} factor_fp={:#018x} raw_fp={:#018x} sc_fp={:#018x} pcs_fp={:#018x} semantic_fp={:#018x} scalar_obs_fp={:#018x} scalar_pcs_fp={:#018x} extra_c1={} extra_g={} leaf_delta={} opening_delta={} scalar_wire_delta={} elapsed_ms={}",
        report.candidate,
        report.representative_screen_only,
        report.c1_raw_ranks_m31,
        report.g_raw_rank_m31,
        report.extra_g_raw_ranks_m31,
        report.masked_sumcheck_rank_m31,
        report.pre_helper_pcs_rank_m31,
        report.pre_scalar_m_pcs_rank_m31,
        report.pcs_rank_m31,
        report.ambient_rank_m31,
        report.conservative_semantic_augmented_rank_m31,
        report.conservative_semantic_new_pivots_m31,
        report.legal_sumcheck_augmented_rank_m31,
        report.legal_sumcheck_new_pivots_m31,
        report.compatibility_rank_m31,
        report.post_alpha_scalar_m_probe,
        report.scalar_m_observation_rank_m31,
        report.scalar_m_conditioned_kernel_m31,
        report.scalar_m_new_pivots_m31,
        report.scalar_m_contains_conservative_semantic_superset,
        report.maximum_masked_oracle_degree,
        report.factor_schedule_fingerprint,
        report.raw_minor_fingerprint,
        report.sumcheck_minor_fingerprint,
        report.pcs_minor_fingerprint,
        report.semantic_minor_fingerprint,
        report.scalar_m_observation_minor_fingerprint,
        report.scalar_m_pcs_minor_fingerprint,
        report.extra_mask_only_columns,
        report.extra_g_columns,
        report.layer0_leaf_delta_bytes,
        report.estimated_serialized_opening_delta_bytes,
        report.scalar_m_query_and_tau_delta_bytes,
        report.elapsed_millis,
    );
}
