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

fn lift(value: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(value)))
}

/// A fixed nondegenerate diagnostic schedule using the sixteen query words
/// from the frozen V7 full-C2 devnet proof. The production prover must run the
/// same gate on its actual transcript schedule; this test pins one exact,
/// reproducible full-view certificate for the source layout.
fn frozen_schedule() -> StateOnlyTranscriptScheduleResult {
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
            lambda: lift(2),
            chi: lift(3),
            batching: PaymentConstraintChallenges {
                theta: lift(5),
                zerocheck_point: core::array::from_fn(|index| lift(7 + index as u32)),
                mu: lift(19),
            },
            initial_mask_claim: lift(23),
            eta: lift(29),
            z: core::array::from_fn(|index| lift(31 + index as u32)),
            masked_terminal_claim: lift(43),
            gamma: lift(47),
            point_scale: lift(53),
            state_after_gamma: [0u8; 32],
        },
        circle_ood_points: [neutral_circle_point; 2],
        line_ood_points: [[QM31::ZERO; 2]; 3],
        mu: [[QM31::ZERO; 2]; 4],
        alpha: [lift(59), lift(61), lift(67), lift(71)],
        state_before_grinding: [0u8; 32],
        queries,
        query_count: 16,
        state_after_queries: [0u8; 32],
    }
}

#[test]
fn pool_pair_exact_layout_spans_complete_root_message_view() {
    let report = probe_pool_v1_pair_root_message_hiding_rank(&frozen_schedule()).unwrap();
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
