use aspis_core::{
    circle::SecureCirclePoint,
    field::{CM31, M31, QM31},
    state_only_prefix::{
        StateOnlyPrefixScheduleResult, StateOnlyTranscriptScheduleResult,
        STATE_ONLY_MAX_QUERY_COUNT,
    },
    statement_sumcheck::PaymentConstraintChallenges,
};
use aspis_prover::state_only_hiding_rank::probe_pool_v1_pair_root_message_hiding_rank;

fn pseudorandom_m31(seed: u64) -> M31 {
    let mut value = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^= value >> 31;
    M31((value % 2_147_483_647) as u32)
}

fn qm31(seed: u32) -> QM31 {
    let seed = u64::from(seed) * 4;
    QM31 {
        c0: CM31::new(pseudorandom_m31(seed), pseudorandom_m31(seed + 1)),
        c1: CM31::new(pseudorandom_m31(seed + 2), pseudorandom_m31(seed + 3)),
    }
}

/// A fixed good-schedule witness using the sixteen query words from the
/// frozen V7 full-C2 devnet proof. The extension-field scalars consumed by
/// this gate have all four M31 coordinates populated; putting them in the base
/// subfield would make the raw three-point view degenerate by construction.
/// This pins one nonzero full-rank witness for the exact source layout; it does
/// not by itself prove an all-schedule determinant-liveness probability bound.
fn fixed_full_field_witness_schedule() -> StateOnlyTranscriptScheduleResult {
    let mut queries = [0u32; STATE_ONLY_MAX_QUERY_COUNT];
    queries[..16].copy_from_slice(&[
        152_742, 172_436, 140_755, 112_262, 203_944, 205_890, 96_695, 220_077, 230_153, 141_221,
        182_970, 177_051, 184_191, 160_328, 229_391, 253_215,
    ]);
    let neutral_circle_point = SecureCirclePoint {
        x: QM31::ONE,
        y: QM31::ZERO,
    };
    StateOnlyTranscriptScheduleResult {
        prefix: StateOnlyPrefixScheduleResult {
            lambda: qm31(2),
            chi: qm31(3),
            batching: PaymentConstraintChallenges {
                theta: qm31(5),
                zerocheck_point: core::array::from_fn(|index| qm31(7 + index as u32)),
                mu: qm31(19),
            },
            initial_mask_claim: qm31(23),
            eta: qm31(29),
            z: core::array::from_fn(|index| qm31(31 + index as u32)),
            masked_terminal_claim: qm31(43),
            gamma: qm31(47),
            point_scale: qm31(53),
            state_after_gamma: [0u8; 32],
        },
        circle_ood_points: [neutral_circle_point; 2],
        line_ood_points: [[QM31::ZERO; 2]; 3],
        mu: [[QM31::ZERO; 2]; 4],
        alpha: [qm31(59), qm31(61), qm31(67), qm31(71)],
        state_before_grinding: [0u8; 32],
        queries,
        query_count: 16,
        state_after_queries: [0u8; 32],
    }
}

#[test]
fn pool_pair_exact_layout_spans_complete_root_message_view() {
    let report =
        probe_pool_v1_pair_root_message_hiding_rank(&fixed_full_field_witness_schedule()).unwrap();
    println!(
        "Pool pair hiding rank: pcs={} q={} raw={} sc={}/{} pcs={}/{} ambient_deficit={} physical={:?} legal={:?} helper={:?} elapsed_ms={}",
        report.pcs_schedule,
        report.query_count,
        report.raw_opening_minor.source_columns.len(),
        report.masked_sumcheck_rank,
        report.masked_sumcheck_m31,
        report.joint_pcs_rank,
        report.joint_pcs_declared_rank,
        report.baseline_ambient_deficit_m31,
        report.witness_coupled_physical_contained,
        report.witness_coupled_legal_contained,
        report.witness_coupled_helper_contained,
        report.elapsed_millis,
    );
    assert_eq!(report.pcs_schedule, "v6_log20_root_message_exact_sequence");
    assert_eq!(report.query_count, 16);
    assert!(report.witness_difference_probe);
    assert!(report.baseline_valid_witness_containment);
    assert_eq!(report.witness_coupled_physical_contained, Some(true));
    assert_eq!(report.witness_coupled_legal_contained, Some(true));
    assert_eq!(report.witness_coupled_helper_contained, Some(true));
    assert!(report.witness_coupled_terminal_identity_guard);
    assert!(report.witness_mask_raw_kernel_terminal_zero_guard);
    assert!(report.witness_h_zero_sumcheck_terminal_guard);
    assert!(report.witness_mask_sumcheck_equals_terminal_kernel);
    assert!(report.witness_semantic_sparse_dense_guard);
}
