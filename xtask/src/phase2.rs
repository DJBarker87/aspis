use super::*;
use phase1_probe::{
    build_phase2_arithmetic_instruction, build_phase2_extension_instruction,
    build_phase2_proof_bytes, build_phase2_skeleton_instruction,
    build_phase2_whir_merkle_payload_bytes, build_phase2_whir_merkle_payload_instruction,
    build_phase2_whir_query_instruction, build_phase2_whir_query_proof_bytes,
    build_phase2_whir_transcript_instruction, build_phase2_whir_transcript_proof_bytes,
    build_phase2_whir_transcript_proof_bytes_with_precompute_mode,
    build_phase2_whir_transcript_segment_instruction, derive_phase2_whir_transcript_checkpoints,
    run_phase2_arithmetic_bench, run_phase2_extension_bench, run_phase2_skeleton_verify,
    run_phase2_whir_merkle_payload_parse, run_phase2_whir_query_verify,
    run_phase2_whir_transcript_segment_verify, run_phase2_whir_transcript_verify,
    ArithmeticKernelId, ArithmeticWorkloadId, ExtensionKernelId, ExtensionWorkloadId,
    LazyReductionMode, LiftPolicy, MerkleProofMode, Phase2ArithmeticConfig, Phase2Counters,
    Phase2ExtensionConfig, Phase2ProofPlan, Phase2VerifierConfig, Phase2WhirQueryPlan,
    Phase2WhirRoundPlan, Phase2WhirStatementShape, Phase2WhirTranscriptPlan,
    Phase2WhirTranscriptRoundPlan, ReductionMode, WhirFoldMode, WhirMerklePayloadFormat,
    WhirQueryPrecomputeMode, WhirQueryReuseMode, WhirTranscriptDiagnosticStage,
    WhirTranscriptTraceMode, PHASE2_WHIR_MAX_OPENING_TERMS, PHASE2_WHIR_MAX_ROUNDS,
};
use serde::{Deserialize, Serialize};
use serde_json::json;
use svm_cost_model::{ProfileScoreInput, TransportCostFeatures};

const VERIFY_HEAP_FRAME_BYTES: u32 = 32 * 1024;

#[derive(Clone, Debug, Serialize)]
struct Phase2RunConfig {
    limits: SvmLimits,
    arithmetic_sbf_iterations: Vec<NamedIterations>,
    extension_sbf_iterations: Vec<NamedIterations>,
    upload_chunk_size: usize,
    upload_repetitions: u32,
    verify_repetitions: u32,
    skeleton_repeat_inside_instruction: u32,
    whir_query_repeat_inside_instruction: u32,
    whir_transcript_repeat_inside_instruction: u32,
    whir_transcript_verify_repetitions: u32,
    whir_transcript_trace_repetitions: u32,
    proof_plan: ProofPlanSummary,
    whir_query_scenarios: Vec<WhirQueryScenarioSeed>,
}

#[derive(Clone, Debug, Serialize)]
struct ProofPlanSummary {
    query_count: u16,
    fold_arity: u16,
    merkle_depth: u16,
    merkle_paths: u16,
    target_proof_bytes: u32,
    query_schedule_seed: u64,
    statement_seed: u64,
}

#[derive(Clone, Debug, Serialize)]
struct WhirQueryScenarioSeed {
    name: String,
    security_target_bits: f64,
    soundness_assumption: String,
    log_inv_rate: u32,
    grinding_bits: u32,
}

#[derive(Clone, Debug, Serialize)]
struct NamedIterations {
    name: String,
    iterations: u32,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(default)]
struct CounterSummary {
    proof_bytes: u64,
    parser_bytes: u64,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_paths: u64,
    merkle_levels: u64,
    m31_add_ops: u64,
    m31_mul_ops: u64,
    m31_square_ops: u64,
    m31_inv_ops: u64,
    cm31_mul_ops: u64,
    cm31_square_ops: u64,
    cm31_inv_ops: u64,
    cm31_mul_const_ops: u64,
    cm31_conjugate_ops: u64,
    qm31_mul_ops: u64,
    qm31_square_ops: u64,
    qm31_inv_ops: u64,
    qm31_mul_const_ops: u64,
    qm31_conjugate_ops: u64,
    lift_to_cm31_ops: u64,
    lift_to_qm31_ops: u64,
}

impl From<Phase2Counters> for CounterSummary {
    fn from(value: Phase2Counters) -> Self {
        Self {
            proof_bytes: value.proof_bytes,
            parser_bytes: value.parser_bytes,
            sha_calls: value.sha_calls,
            sha_bytes: value.sha_bytes,
            merkle_paths: value.merkle_paths,
            merkle_levels: value.merkle_levels,
            m31_add_ops: value.m31_add_ops,
            m31_mul_ops: value.m31_mul_ops,
            m31_square_ops: value.m31_square_ops,
            m31_inv_ops: value.m31_inv_ops,
            cm31_mul_ops: value.cm31_mul_ops,
            cm31_square_ops: value.cm31_square_ops,
            cm31_inv_ops: value.cm31_inv_ops,
            cm31_mul_const_ops: value.cm31_mul_const_ops,
            cm31_conjugate_ops: value.cm31_conjugate_ops,
            qm31_mul_ops: value.qm31_mul_ops,
            qm31_square_ops: value.qm31_square_ops,
            qm31_inv_ops: value.qm31_inv_ops,
            qm31_mul_const_ops: value.qm31_mul_const_ops,
            qm31_conjugate_ops: value.qm31_conjugate_ops,
            lift_to_cm31_ops: value.lift_to_cm31_ops,
            lift_to_qm31_ops: value.lift_to_qm31_ops,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
struct ArithmeticMeasurement {
    family: String,
    kernel_id: String,
    reduction_mode: String,
    lazy_reduction_mode: String,
    workload: String,
    domain: String,
    repetition: u32,
    iterations: u32,
    logical_units: u64,
    actual_cu: Option<u64>,
    cu_per_unit: Option<f64>,
    elapsed_ns: Option<u128>,
    ns_per_unit: Option<f64>,
    code_size_bytes: Option<u64>,
    zero_heap: bool,
    stack_observation: String,
    counters: CounterSummary,
}

#[derive(Clone, Debug, Serialize)]
struct ExtensionMeasurement {
    extension_kernel_id: String,
    workload: String,
    domain: String,
    repetition: u32,
    iterations: u32,
    logical_units: u64,
    actual_cu: Option<u64>,
    cu_per_unit: Option<f64>,
    elapsed_ns: Option<u128>,
    ns_per_unit: Option<f64>,
    zero_heap: bool,
    counters: CounterSummary,
}

#[derive(Clone, Debug, Serialize)]
struct EndToEndMeasurement {
    variant: String,
    arithmetic_kernel_id: String,
    extension_kernel_id: String,
    lift_policy: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    stage: String,
    repetition: u32,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    counters: CounterSummary,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
    predicted_cu: Option<f64>,
    predicted_component_cu: Option<f64>,
    predicted_core_cu: Option<f64>,
    predicted_transport_cu: Option<f64>,
    abs_error_cu: Option<f64>,
    rel_error: Option<f64>,
}

#[derive(Clone, Debug, Serialize)]
struct WhirQueryMeasurement {
    scenario_name: String,
    variant: String,
    security_target_bits: f64,
    soundness_assumption: String,
    legacy_bound_cu: f64,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    arithmetic_kernel_id: String,
    extension_kernel_id: String,
    lift_policy: String,
    whir_fold_mode: String,
    stage: String,
    repetition: u32,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    counters: CounterSummary,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
    predicted_cu: Option<f64>,
    predicted_component_cu: Option<f64>,
    predicted_core_cu: Option<f64>,
    predicted_transport_cu: Option<f64>,
    abs_error_cu: Option<f64>,
    rel_error: Option<f64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirTranscriptMeasurement {
    scenario_name: String,
    path_variant: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    counters: CounterSummary,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirMultiproofMeasurement {
    scenario_name: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    counters: CounterSummary,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirMultiproofPayloadMeasurement {
    scenario_name: String,
    merkle_proof_mode: String,
    payload_format: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    commitment_ood_samples: u64,
    payload_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    counters: CounterSummary,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirFoldPayloadMeasurement {
    scenario_name: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    counters: CounterSummary,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirFullReuseMeasurement {
    scenario_name: String,
    path_variant: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    query_reuse_mode: String,
    #[serde(default = "default_query_precompute_mode_name")]
    query_precompute_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    counters: CounterSummary,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Clone, Debug, Serialize)]
struct WhirMulTaxonomyMeasurement {
    scenario_name: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    total_sbf_mean_cu: Option<f64>,
    total_sbf_stddev_cu: Option<f64>,
    proof_bytes: u64,
    total_classified_multiplies: u64,
    general: u64,
    zero_one_negone: u64,
    square: u64,
    sparse_const: u64,
    twiddle: u64,
    bary_weight: u64,
    challenge_power: u64,
    cm31_structured: u64,
    qm31_structured: u64,
    general_extension: u64,
    structured_share: f64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirRound0Measurement {
    scenario_name: String,
    round0_variant: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    round_index: u64,
    round_query_count: u64,
    round_merkle_depth: u64,
    round_ood_samples: u64,
    round_selector_count: u64,
    round_pow_bits: u64,
    round_sumcheck_rounds: u64,
    round_folding_pow_bits: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    counters: CounterSummary,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirRound0SummaryRecord {
    scenario_name: String,
    round0_variant: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    round_query_count: u64,
    round_merkle_depth: u64,
    round_ood_samples: u64,
    round_selector_count: u64,
    round_pow_bits: u64,
    round_sumcheck_rounds: u64,
    round_folding_pow_bits: u64,
    proof_bytes: u64,
    round0_total_mean_cu: Option<f64>,
    round0_total_stddev_cu: Option<f64>,
    phase_parse_mean_cu: Option<f64>,
    phase_ood_mean_cu: Option<f64>,
    phase_per_round_queries_mean_cu: Option<f64>,
    phase_folding_mean_cu: Option<f64>,
    full_total_mean_cu: Option<f64>,
    full_per_round_queries_mean_cu: Option<f64>,
    round0_share_of_full_total: Option<f64>,
    round0_share_of_full_per_round_queries: Option<f64>,
    projected_full_total_mean_cu: Option<f64>,
    projected_full_delta_cu: Option<f64>,
    projected_margin_cu: Option<f64>,
    total_classified_multiplies: u64,
    general: u64,
    square: u64,
    bary_weight: u64,
    challenge_power: u64,
    cm31_structured: u64,
    qm31_structured: u64,
    general_extension: u64,
    structured_share: f64,
}

#[derive(Clone, Debug, Serialize)]
struct WhirFullReuseSummaryRecord {
    scenario_name: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    query_reuse_mode: String,
    query_precompute_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    proof_bytes: u64,
    verify_sbf_mean_cu: Option<f64>,
    verify_sbf_stddev_cu: Option<f64>,
    total_sbf_mean_cu: Option<f64>,
    total_sbf_stddev_cu: Option<f64>,
    upload_mean_cu: Option<f64>,
    phase_transcript_setup_mean_cu: Option<f64>,
    phase_ood_mean_cu: Option<f64>,
    phase_per_round_queries_mean_cu: Option<f64>,
    phase_folding_mean_cu: Option<f64>,
    phase_final_round_mean_cu: Option<f64>,
    query_only_mean_cu: Option<f64>,
    query_only_stddev_cu: Option<f64>,
    round0_projected_total_mean_cu: Option<f64>,
    round0_projection_delta_cu: Option<f64>,
    remaining_margin_cu: Option<f64>,
    verify_ok: usize,
    verify_total: usize,
    trace_ok: usize,
    trace_total: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WhirRoundLocalSummaryRecord {
    scenario_name: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    query_reuse_mode: String,
    query_precompute_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    proof_bytes: u64,
    proof_bytes_delta_vs_none: Option<i64>,
    verify_sbf_mean_cu: Option<f64>,
    verify_sbf_stddev_cu: Option<f64>,
    total_sbf_mean_cu: Option<f64>,
    total_sbf_stddev_cu: Option<f64>,
    upload_mean_cu: Option<f64>,
    phase_transcript_setup_mean_cu: Option<f64>,
    phase_ood_mean_cu: Option<f64>,
    phase_per_round_queries_mean_cu: Option<f64>,
    phase_folding_mean_cu: Option<f64>,
    phase_final_round_mean_cu: Option<f64>,
    delta_vs_none_verify_cu: Option<f64>,
    delta_vs_none_total_cu: Option<f64>,
    delta_vs_none_phase_per_round_queries_cu: Option<f64>,
    remaining_margin_cu: Option<f64>,
    prior_round0_share_of_full_total: Option<f64>,
    prior_round0_projected_total_mean_cu: Option<f64>,
    verify_ok: usize,
    verify_total: usize,
    trace_ok: usize,
    trace_total: usize,
}

#[derive(Clone, Debug, Serialize)]
struct CapacityV0FreezeSummary {
    generated_at_utc: String,
    command: String,
    profile_name: String,
    shipping_branch: String,
    research_branch: String,
    scenario_name: String,
    security_target_bits: f64,
    soundness_assumption: String,
    arithmetic_kernel_id: String,
    extension_kernel_id: String,
    lift_policy: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    merkle_payload_format: String,
    statement_binding: String,
    transcript_path: String,
    proof_bytes: u64,
    verify_mean_cu: f64,
    verify_stddev_cu: f64,
    upload_mean_cu: f64,
    total_mean_cu: f64,
    total_stddev_cu: f64,
    remaining_margin_cu: f64,
    query_only_baseline_cu: f64,
    transcript_separate_paths_cu: f64,
    transcript_minimal_subtree_local_cu: f64,
    transcript_minimal_subtree_raw_cu: f64,
    local_interpolant_delta_cu: f64,
    minimal_subtree_delta_vs_separate_cu: f64,
    stage_breakdown: Vec<CapacityV0StageRecord>,
    payload_flat_nodes_bytes: u64,
    payload_flat_nodes_parse_cu: f64,
    payload_flat_nodes_total_cu: f64,
    payload_canonical_bytes: u64,
    payload_canonical_parse_cu: f64,
    payload_canonical_total_cu: f64,
    payload_canonical_delta_cu: f64,
    verification_repetitions_ok: usize,
    verification_repetitions_total: usize,
    raw_artifacts: Vec<String>,
    next_research_steps: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct CapacityV0StageRecord {
    stage: String,
    mean_cu: f64,
    stddev_cu: f64,
}

#[derive(Serialize)]
struct ArithmeticCsvRow {
    family: String,
    kernel_id: String,
    reduction_mode: String,
    lazy_reduction_mode: String,
    workload: String,
    domain: String,
    repetition: u32,
    iterations: u32,
    logical_units: u64,
    actual_cu: Option<u64>,
    cu_per_unit: Option<f64>,
    elapsed_ns: Option<u128>,
    ns_per_unit: Option<f64>,
    proof_bytes: u64,
    sha_calls: u64,
    merkle_levels: u64,
    m31_add_ops: u64,
    m31_mul_ops: u64,
    m31_square_ops: u64,
    m31_inv_ops: u64,
}

#[derive(Serialize)]
struct ExtensionCsvRow {
    extension_kernel_id: String,
    workload: String,
    domain: String,
    repetition: u32,
    iterations: u32,
    logical_units: u64,
    actual_cu: Option<u64>,
    cu_per_unit: Option<f64>,
    elapsed_ns: Option<u128>,
    ns_per_unit: Option<f64>,
    cm31_mul_ops: u64,
    cm31_square_ops: u64,
    cm31_inv_ops: u64,
    qm31_mul_ops: u64,
    qm31_square_ops: u64,
    qm31_inv_ops: u64,
}

#[derive(Serialize)]
struct EndToEndCsvRow {
    variant: String,
    arithmetic_kernel_id: String,
    extension_kernel_id: String,
    lift_policy: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    stage: String,
    repetition: u32,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
    m31_mul_ops: u64,
    cm31_mul_ops: u64,
    qm31_mul_ops: u64,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
    predicted_cu: Option<f64>,
    predicted_component_cu: Option<f64>,
    predicted_core_cu: Option<f64>,
    predicted_transport_cu: Option<f64>,
    abs_error_cu: Option<f64>,
    rel_error: Option<f64>,
}

#[derive(Serialize)]
struct WhirQueryCsvRow {
    scenario_name: String,
    variant: String,
    security_target_bits: f64,
    soundness_assumption: String,
    legacy_bound_cu: f64,
    total_explicit_query_count: u64,
    round_query_counts: String,
    arithmetic_kernel_id: String,
    extension_kernel_id: String,
    lift_policy: String,
    whir_fold_mode: String,
    stage: String,
    repetition: u32,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
    m31_mul_ops: u64,
    cm31_mul_ops: u64,
    qm31_mul_ops: u64,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
    predicted_cu: Option<f64>,
    predicted_component_cu: Option<f64>,
    predicted_core_cu: Option<f64>,
    predicted_transport_cu: Option<f64>,
    abs_error_cu: Option<f64>,
    rel_error: Option<f64>,
}

#[derive(Serialize)]
struct WhirTranscriptCsvRow {
    scenario_name: String,
    path_variant: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: String,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
    m31_mul_ops: u64,
    cm31_mul_ops: u64,
    qm31_mul_ops: u64,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Serialize)]
struct WhirMultiproofCsvRow {
    scenario_name: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: String,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
    m31_mul_ops: u64,
    cm31_mul_ops: u64,
    qm31_mul_ops: u64,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Serialize)]
struct WhirMultiproofPayloadCsvRow {
    scenario_name: String,
    merkle_proof_mode: String,
    payload_format: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: String,
    commitment_ood_samples: u64,
    payload_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    parser_bytes: u64,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
}

#[derive(Serialize)]
struct WhirFoldPayloadCsvRow {
    scenario_name: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: String,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
    m31_mul_ops: u64,
    cm31_mul_ops: u64,
    qm31_mul_ops: u64,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Serialize)]
struct WhirFullReuseCsvRow {
    scenario_name: String,
    path_variant: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    query_reuse_mode: String,
    query_precompute_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    round_query_counts: String,
    commitment_ood_samples: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
    m31_mul_ops: u64,
    cm31_mul_ops: u64,
    qm31_mul_ops: u64,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Serialize)]
struct WhirMulTaxonomyCsvRow {
    scenario_name: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    total_explicit_query_count: u64,
    total_sbf_mean_cu: Option<f64>,
    total_sbf_stddev_cu: Option<f64>,
    proof_bytes: u64,
    total_classified_multiplies: u64,
    general: u64,
    zero_one_negone: u64,
    square: u64,
    sparse_const: u64,
    twiddle: u64,
    bary_weight: u64,
    challenge_power: u64,
    cm31_structured: u64,
    qm31_structured: u64,
    general_extension: u64,
    structured_share: f64,
}

#[derive(Serialize)]
struct WhirRound0CsvRow {
    scenario_name: String,
    round0_variant: String,
    whir_fold_mode: String,
    merkle_proof_mode: String,
    security_target_bits: f64,
    soundness_assumption: String,
    round_index: u64,
    round_query_count: u64,
    round_merkle_depth: u64,
    round_ood_samples: u64,
    round_selector_count: u64,
    round_pow_bits: u64,
    round_sumcheck_rounds: u64,
    round_folding_pow_bits: u64,
    proof_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    heap_pages_32k: u64,
    stage: String,
    repetition: u32,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    status: String,
    error: Option<String>,
    sha_calls: u64,
    sha_bytes: u64,
    merkle_levels: u64,
    m31_mul_ops: u64,
    cm31_mul_ops: u64,
    qm31_mul_ops: u64,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

#[derive(Clone, Debug, Serialize)]
struct Phase2Summary {
    generated_at_utc: String,
    command: String,
    raw_artifacts: Vec<String>,
    versions: VersionManifest,
    workspace_git_hash: Option<String>,
    vendor_git_hash: Option<String>,
    arithmetic_winner_raw_mul: String,
    arithmetic_winner_verifier_kernel: String,
    extension_kernel_winner: String,
    lift_policy_winner: String,
    whir_fold_winner: String,
    combined_best_variant: String,
    combined_estimated_savings_cu: f64,
    combined_estimated_headroom_cu: f64,
    combined_estimated_post_change_cu: f64,
    whir_query_high_fidelity_winner: String,
    whir_query_translation_summary: Vec<String>,
    whir_transcript_comparison_summary: Vec<String>,
    whir_transcript_remaining_margin_summary: Vec<String>,
    biggest_remaining_risk: String,
}

#[derive(Clone)]
struct ArithmeticCandidate {
    name: &'static str,
    config: Phase2ArithmeticConfig,
}

#[derive(Clone)]
struct SkeletonVariant {
    name: String,
    config: Phase2VerifierConfig,
}

#[derive(Clone)]
struct WhirQueryVariant {
    name: &'static str,
    config: Phase2VerifierConfig,
}

#[derive(Clone)]
struct DerivedWhirQueryScenario {
    seed: WhirQueryScenarioSeed,
    plan: Phase2WhirQueryPlan,
    profile: ProfileScoreInput,
    legacy_bound_cu: f64,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
}

#[derive(Clone)]
struct DerivedWhirTranscriptScenario {
    seed: WhirQueryScenarioSeed,
    query_plan: Phase2WhirQueryPlan,
    transcript_plan: Phase2WhirTranscriptPlan,
    total_explicit_query_count: u64,
    round_query_counts: Vec<u64>,
    commitment_ood_samples: u64,
}

const WHIR_TRANSCRIPT_PREFIX_BYTES: usize = 64;
const WHIR_TRANSCRIPT_STATEMENT_SHAPE_BYTES: usize = 80;
const WHIR_TRANSCRIPT_ROUND_PLAN_BYTES: usize = 16;
const WHIR_TRANSCRIPT_QUERY_RECORD_BYTES: usize = 120;
const WHIR_TRANSCRIPT_SUMCHECK_RECORD_BYTES: usize = 16;
const WHIR_TRANSCRIPT_FINAL_QUERY_BYTES: usize = 8;
const WHIR_TRANSCRIPT_DEFERRED_BYTES: usize = 16;
const WHIR_TRANSCRIPT_MAX_OOD_SAMPLES: u16 = 4;
const WHIR_TRANSCRIPT_MAX_SUMCHECK_ROUNDS: u16 = 8;
const WHIR_TRANSCRIPT_MAX_FINAL_COEFFS: usize = 64;

#[derive(Clone, Copy, Debug)]
struct WhirTranscriptLayout {
    final_pow_nonce_offset: usize,
    final_query_offset: usize,
    final_sumcheck_offset: usize,
}

fn start_phase2_harness(
    root: &Path,
    results_root: &Path,
    program_so: &Path,
    limits: &SvmLimits,
) -> Result<(ValidatorGuard, BenchHarness)> {
    let validator = start_validator(root, results_root, program_so)?;
    let harness = BenchHarness {
        client: LocalRpcClient::new(validator.rpc_url.clone()),
        payer: Keypair::new(),
        program_id: id(),
        limits: limits.clone(),
    };
    fund_payer(&harness)?;
    Ok((validator, harness))
}

pub(super) fn run_phase2_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_run_config();

    let results_root = root.join("results/phase2");
    if results_root.exists() {
        fs::remove_dir_all(&results_root)?;
    }
    let arithmetic_dir = results_root.join("arithmetic");
    let lift_dir = results_root.join("lift-policy");
    let fold_dir = results_root.join("whir-fold");
    let whir_query_dir = results_root.join("whir-query");
    let whir_transcript_dir = results_root.join("whir-transcript");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&arithmetic_dir)?;
    fs::create_dir_all(&lift_dir)?;
    fs::create_dir_all(&fold_dir)?;
    fs::create_dir_all(&whir_query_dir)?;
    fs::create_dir_all(&whir_transcript_dir)?;
    fs::create_dir_all(&manifests_dir)?;
    let examples_phase2 = root.join("examples/phase2");
    fs::create_dir_all(&examples_phase2)?;
    write_json(&results_root.join("run_config.json"), &run_config)?;
    write_json(&examples_phase2.join("phase2-run-config.json"), &run_config)?;

    let versions = capture_version_manifest()?;
    write_json(&results_root.join("version_manifest.json"), &versions)?;

    let program_so = build_sbf_program(&root)?;
    let (
        arithmetic,
        raw_mul_winner,
        verifier_kernel_winner,
        extension,
        extension_kernel_winner,
        skeleton,
        lift_policy_winner,
        whir_fold_winner,
        combined_best,
    ) = {
        let (_validator, harness) =
            start_phase2_harness(&root, &results_root, &program_so, &run_config.limits)?;

        eprintln!("phase2: arithmetic");
        let arithmetic = run_arithmetic_experiment(&harness, &run_config, &arithmetic_dir)?;
        write_generic_jsonl(&arithmetic_dir.join("raw.jsonl"), &arithmetic)?;
        write_arithmetic_csv(&arithmetic_dir.join("raw.csv"), &arithmetic)?;

        let raw_mul_winner = pick_best_arithmetic(&arithmetic, ArithmeticWorkloadId::Mul);
        let verifier_kernel_winner =
            pick_best_arithmetic(&arithmetic, ArithmeticWorkloadId::SkeletonFoldStep);

        let base_arithmetic = arithmetic_candidates()
            .into_iter()
            .find(|candidate| candidate.name == verifier_kernel_winner)
            .map(|candidate| candidate.config)
            .context("failed to resolve arithmetic winner")?;

        eprintln!("phase2: extension");
        let extension =
            run_extension_experiment(&harness, &run_config, base_arithmetic, &lift_dir)?;
        write_generic_jsonl(&lift_dir.join("extension_raw.jsonl"), &extension)?;
        write_extension_csv(&lift_dir.join("extension_raw.csv"), &extension)?;
        let extension_kernel_winner =
            pick_best_extension_kernel(&extension, ExtensionWorkloadId::SkeletonAccumulator);

        eprintln!("phase2: skeleton-matrix");
        let skeleton = run_skeleton_matrix(
            &harness,
            &run_config,
            base_arithmetic,
            &phase1_summary,
            &manifests_dir,
        )?;
        write_generic_jsonl(&fold_dir.join("raw.jsonl"), &skeleton)?;
        write_end_to_end_csv(&fold_dir.join("raw.csv"), &skeleton)?;

        let lift_policy_winner = pick_best_lift_policy(&skeleton);
        let whir_fold_winner = pick_best_fold_mode(&skeleton);
        let combined_best = pick_best_variant(&skeleton)?;

        Ok::<_, anyhow::Error>((
            arithmetic,
            raw_mul_winner,
            verifier_kernel_winner,
            extension,
            extension_kernel_winner,
            skeleton,
            lift_policy_winner,
            whir_fold_winner,
            combined_best,
        ))
    }?;

    eprintln!("phase2: whir-query");
    let whir_query = run_high_fidelity_whir_query_matrix(
        &root,
        &program_so,
        &run_config,
        &phase1_summary,
        &whir_query_dir,
    )?;
    write_generic_jsonl(&whir_query_dir.join("raw.jsonl"), &whir_query)?;
    write_whir_query_csv(&whir_query_dir.join("raw.csv"), &whir_query)?;
    let whir_query_winner = pick_best_whir_query_variant(&whir_query);
    let whir_query_translation = whir_query_translation_summary(&whir_query);

    eprintln!("phase2: whir-transcript");
    let whir_transcript = run_whir_transcript_matrix(
        &root,
        &program_so,
        &run_config,
        &whir_transcript_dir,
        &manifests_dir,
    )?;
    write_generic_jsonl(&whir_transcript_dir.join("raw.jsonl"), &whir_transcript)?;
    write_whir_transcript_csv(&whir_transcript_dir.join("raw.csv"), &whir_transcript)?;
    let whir_transcript_comparison = whir_transcript_comparison_summary(&whir_transcript);
    let whir_transcript_margin = whir_transcript_margin_summary(&whir_transcript);

    let savings = estimate_savings(
        &skeleton,
        &arithmetic,
        &extension,
        &verifier_kernel_winner,
        &extension_kernel_winner,
        &lift_policy_winner,
        &whir_fold_winner,
    )?;

    let workspace_git_hash = optional_git_hash(&root);
    let vendor_git_hash = optional_git_hash(&root.join("third_party/solana-pqzk-fullchain"));

    let summary = Phase2Summary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask phase2-experiments".to_string(),
        raw_artifacts: vec![
            "results/phase2/run_config.json".to_string(),
            "results/phase2/version_manifest.json".to_string(),
            "examples/phase2/phase2-run-config.json".to_string(),
            "results/phase2/arithmetic/raw.jsonl".to_string(),
            "results/phase2/arithmetic/raw.csv".to_string(),
            "results/phase2/lift-policy/extension_raw.jsonl".to_string(),
            "results/phase2/lift-policy/extension_raw.csv".to_string(),
            "results/phase2/whir-fold/raw.jsonl".to_string(),
            "results/phase2/whir-fold/raw.csv".to_string(),
            "results/phase2/whir-query/scenarios.json".to_string(),
            "results/phase2/whir-query/raw.jsonl".to_string(),
            "results/phase2/whir-query/raw.csv".to_string(),
            "results/phase2/whir-transcript/scenarios.json".to_string(),
            "results/phase2/whir-transcript/raw.jsonl".to_string(),
            "results/phase2/whir-transcript/raw.csv".to_string(),
            "results/phase2/whir-transcript/proofs/".to_string(),
            "results/phase2/whir-transcript/validation.json".to_string(),
            "results/phase2/manifests/".to_string(),
            "results/phase2/summary.json".to_string(),
            "docs/phase2-experiments.md".to_string(),
        ],
        versions,
        workspace_git_hash,
        vendor_git_hash,
        arithmetic_winner_raw_mul: raw_mul_winner.clone(),
        arithmetic_winner_verifier_kernel: verifier_kernel_winner.clone(),
        extension_kernel_winner: extension_kernel_winner.clone(),
        lift_policy_winner: lift_policy_winner.clone(),
        whir_fold_winner: whir_fold_winner.clone(),
        combined_best_variant: combined_best.clone(),
        combined_estimated_savings_cu: savings.estimated_savings_cu,
        combined_estimated_headroom_cu: savings.estimated_headroom_cu,
        combined_estimated_post_change_cu: savings.estimated_post_change_cu,
        whir_query_high_fidelity_winner: whir_query_winner,
        whir_query_translation_summary: whir_query_translation.clone(),
        whir_transcript_comparison_summary: whir_transcript_comparison.clone(),
        whir_transcript_remaining_margin_summary: whir_transcript_margin.clone(),
        biggest_remaining_risk: "The transcript-inclusive verifier path is now measured end to end on SBF, but the proof generator is still repo-local because `/tmp/plonky3-official` at commit `0f87f2b543a01880274965c410bf804c124f5046` does not contain the referenced `whir/src/verifier/mod.rs` entrypoint or a usable end-to-end WHIR prover/verifier binary.".to_string(),
    };
    write_json(&results_root.join("summary.json"), &summary)?;

    fs::write(
        &docs_path,
        render_phase2_report(
            &run_config,
            &phase1_summary,
            &arithmetic,
            &extension,
            &skeleton,
            &whir_query,
            &whir_transcript,
            &summary,
            &savings,
        ),
    )?;

    Ok(())
}

pub(super) fn run_phase2_transcript_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-transcript: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_run_config();
    let results_root = root.join("results/phase2");
    let whir_transcript_dir = results_root.join("whir-transcript");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&results_root)?;
    if whir_transcript_dir.exists() {
        fs::remove_dir_all(&whir_transcript_dir)?;
    }
    fs::create_dir_all(&whir_transcript_dir)?;
    fs::create_dir_all(&manifests_dir)?;
    write_json(&results_root.join("run_config.json"), &run_config)?;

    let program_so = build_sbf_program(&root)?;
    let whir_transcript = run_whir_transcript_matrix(
        &root,
        &program_so,
        &run_config,
        &whir_transcript_dir,
        &manifests_dir,
    )?;
    write_generic_jsonl(&whir_transcript_dir.join("raw.jsonl"), &whir_transcript)?;
    write_whir_transcript_csv(&whir_transcript_dir.join("raw.csv"), &whir_transcript)?;
    write_phase2_transcript_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &whir_transcript,
        "cargo xtask phase2-transcript",
    )?;
    Ok(())
}

pub(super) fn run_phase2_multiproof_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-multiproof: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_run_config();
    let results_root = root.join("results/phase2");
    let whir_multiproof_dir = results_root.join("whir-multiproof");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&results_root)?;
    if whir_multiproof_dir.exists() {
        fs::remove_dir_all(&whir_multiproof_dir)?;
    }
    fs::create_dir_all(&whir_multiproof_dir)?;
    fs::create_dir_all(&manifests_dir)?;
    write_json(&results_root.join("run_config.json"), &run_config)?;

    let program_so = build_sbf_program(&root)?;
    let whir_multiproof = run_whir_multiproof_matrix(
        &root,
        &program_so,
        &run_config,
        &whir_multiproof_dir,
        &manifests_dir,
    )?;
    write_generic_jsonl(&whir_multiproof_dir.join("raw.jsonl"), &whir_multiproof)?;
    write_whir_multiproof_csv(&whir_multiproof_dir.join("raw.csv"), &whir_multiproof)?;
    write_phase2_multiproof_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &whir_multiproof,
        "cargo xtask phase2-multiproof",
    )?;
    Ok(())
}

pub(super) fn run_phase2_multiproof_payload_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-multiproof-payload: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_run_config();
    let results_root = root.join("results/phase2");
    let payload_dir = results_root.join("whir-multiproof-payload");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&results_root)?;
    if payload_dir.exists() {
        fs::remove_dir_all(&payload_dir)?;
    }
    fs::create_dir_all(&payload_dir)?;
    fs::create_dir_all(&manifests_dir)?;
    write_json(&results_root.join("run_config.json"), &run_config)?;

    let program_so = build_sbf_program(&root)?;
    let records = run_whir_multiproof_payload_matrix(
        &root,
        &program_so,
        &run_config,
        &payload_dir,
        &manifests_dir,
    )?;
    write_generic_jsonl(&payload_dir.join("raw.jsonl"), &records)?;
    write_whir_multiproof_payload_csv(&payload_dir.join("raw.csv"), &records)?;
    write_phase2_multiproof_payload_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &records,
        "cargo xtask phase2-multiproof-payload",
    )?;
    Ok(())
}

pub(super) fn run_phase2_fold_payload_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-fold-payload: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_run_config();
    let results_root = root.join("results/phase2");
    let fold_dir = results_root.join("whir-fold-payload");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&results_root)?;
    if fold_dir.exists() {
        fs::remove_dir_all(&fold_dir)?;
    }
    fs::create_dir_all(&fold_dir)?;
    fs::create_dir_all(&manifests_dir)?;
    write_json(&results_root.join("run_config.json"), &run_config)?;

    let program_so = build_sbf_program(&root)?;
    let records =
        run_whir_fold_payload_matrix(&root, &program_so, &run_config, &fold_dir, &manifests_dir)?;
    write_generic_jsonl(&fold_dir.join("raw.jsonl"), &records)?;
    write_whir_fold_payload_csv(&fold_dir.join("raw.csv"), &records)?;
    write_phase2_fold_payload_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &records,
        "cargo xtask phase2-fold-payload",
    )?;
    Ok(())
}

pub(super) fn run_phase2_mul_taxonomy_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-mul-taxonomy: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_run_config();
    let results_root = root.join("results/phase2");
    let payload_dir = results_root.join("whir-multiproof-payload");
    if !payload_dir.join("raw.jsonl").exists() {
        run_phase2_multiproof_payload_experiments()?;
    }
    let fold_dir = results_root.join("whir-fold-payload");
    if !fold_dir.join("raw.jsonl").exists() {
        run_phase2_fold_payload_experiments()?;
    }
    let fold_records =
        serde_json::Deserializer::from_reader(File::open(fold_dir.join("raw.jsonl"))?)
            .into_iter::<WhirFoldPayloadMeasurement>()
            .collect::<std::result::Result<Vec<_>, _>>()?;
    let taxonomy = derive_whir_mul_taxonomy(&run_config, &fold_records)?;
    let taxonomy_dir = results_root.join("whir-mul-taxonomy");
    if taxonomy_dir.exists() {
        fs::remove_dir_all(&taxonomy_dir)?;
    }
    fs::create_dir_all(&taxonomy_dir)?;
    write_generic_jsonl(&taxonomy_dir.join("raw.jsonl"), &taxonomy)?;
    write_whir_mul_taxonomy_csv(&taxonomy_dir.join("raw.csv"), &taxonomy)?;
    write_phase2_mul_taxonomy_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &taxonomy,
        "cargo xtask phase2-mul-taxonomy",
    )?;
    Ok(())
}

pub(super) fn run_phase2_round0_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-round0: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_run_config();
    let results_root = root.join("results/phase2");
    let round0_dir = results_root.join("whir-round0");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&results_root)?;
    fs::create_dir_all(&manifests_dir)?;
    let fold_dir = results_root.join("whir-fold-payload");
    if !fold_dir.join("raw.jsonl").exists() {
        run_phase2_fold_payload_experiments()?;
    }
    let multiproof_dir = results_root.join("whir-multiproof");
    if !multiproof_dir.join("raw.jsonl").exists() {
        run_phase2_multiproof_experiments()?;
    }
    if round0_dir.exists() {
        fs::remove_dir_all(&round0_dir)?;
    }
    fs::create_dir_all(&round0_dir)?;
    let program_so = build_sbf_program(&root)?;
    let records =
        run_whir_round0_matrix(&root, &program_so, &run_config, &round0_dir, &manifests_dir)?;
    write_generic_jsonl(&round0_dir.join("raw.jsonl"), &records)?;
    write_whir_round0_csv(&round0_dir.join("raw.csv"), &records)?;
    let fold_records =
        load_jsonl_records::<WhirFoldPayloadMeasurement>(&fold_dir.join("raw.jsonl"))?;
    let multiproof_records =
        load_jsonl_records::<WhirMultiproofMeasurement>(&multiproof_dir.join("raw.jsonl"))?;
    let summary_records =
        derive_whir_round0_summary(&run_config, &records, &fold_records, &multiproof_records)?;
    write_json(&round0_dir.join("summary.json"), &summary_records)?;
    write_phase2_round0_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &records,
        &summary_records,
        "cargo xtask phase2-round0",
    )?;
    Ok(())
}

pub(super) fn run_phase2_full_reuse_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-full-reuse: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_full_reuse_run_config();
    let results_root = root.join("results/phase2");
    let full_reuse_dir = results_root.join("whir-full-reuse");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&results_root)?;
    fs::create_dir_all(&manifests_dir)?;
    if full_reuse_dir.exists() {
        fs::remove_dir_all(&full_reuse_dir)?;
    }
    fs::create_dir_all(&full_reuse_dir)?;
    write_json(&results_root.join("run_config.json"), &run_config)?;

    let program_so = build_sbf_program(&root)?;
    let records = run_whir_full_reuse_matrix(
        &root,
        &program_so,
        &run_config,
        &full_reuse_dir,
        &manifests_dir,
    )?;
    write_generic_jsonl(&full_reuse_dir.join("raw.jsonl"), &records)?;
    write_whir_full_reuse_csv(&full_reuse_dir.join("raw.csv"), &records)?;
    let round0_summary_path = results_root.join("whir-round0/summary.json");
    let round0_summary_records = if round0_summary_path.exists() {
        serde_json::from_reader(File::open(&round0_summary_path)?).unwrap_or_default()
    } else {
        Vec::new()
    };
    let summary_records = derive_whir_full_reuse_summary(&records, &round0_summary_records);
    write_json(&full_reuse_dir.join("summary.json"), &summary_records)?;
    write_phase2_full_reuse_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &records,
        &summary_records,
        "cargo xtask phase2-full-reuse",
    )?;
    Ok(())
}

pub(super) fn run_phase2_roundlocal_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let phase1_summary_path = root.join("phase1_results/summary.json");
    if !phase1_summary_path.exists() {
        eprintln!("phase2-roundlocal: phase1 summary missing, running phase1");
        run_phase1()?;
    }
    let phase1_summary = load_summary(&phase1_summary_path)?;
    let run_config = phase2_full_reuse_run_config();
    let results_root = root.join("results/phase2");
    let roundlocal_dir = results_root.join("whir-roundlocal");
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&results_root)?;
    fs::create_dir_all(&manifests_dir)?;
    if roundlocal_dir.exists() {
        fs::remove_dir_all(&roundlocal_dir)?;
    }
    fs::create_dir_all(&roundlocal_dir)?;
    write_json(&results_root.join("run_config.json"), &run_config)?;

    let program_so = build_sbf_program(&root)?;
    let records = run_whir_roundlocal_matrix(
        &root,
        &program_so,
        &run_config,
        &roundlocal_dir,
        &manifests_dir,
    )?;
    write_generic_jsonl(&roundlocal_dir.join("raw.jsonl"), &records)?;
    write_whir_full_reuse_csv(&roundlocal_dir.join("raw.csv"), &records)?;
    let round0_summary_path = results_root.join("whir-round0/summary.json");
    let round0_summary_records = if round0_summary_path.exists() {
        serde_json::from_reader(File::open(&round0_summary_path)?).unwrap_or_default()
    } else {
        Vec::new()
    };
    let summary_records = derive_whir_roundlocal_summary(&records, &round0_summary_records);
    write_json(&roundlocal_dir.join("summary.json"), &summary_records)?;
    write_phase2_roundlocal_summary_and_docs(
        &root,
        &docs_path,
        &phase1_summary,
        &run_config,
        &summary_records,
        "cargo xtask phase2-roundlocal",
    )?;
    Ok(())
}

pub(super) fn run_phase2_next3_experiments() -> Result<()> {
    run_phase2_multiproof_payload_experiments()?;
    run_phase2_fold_payload_experiments()?;
    run_phase2_mul_taxonomy_experiments()?;
    Ok(())
}

pub(super) fn run_phase2_freeze_capacity_v0() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-experiments.md");
    let capacity_doc_path = root.join("docs/whir-m31-capacity-v0.md");
    let state_of_play_path = root.join("docs/state-of-play.md");
    let results_root = root.join("results/phase2");
    let freeze_dir = results_root.join("whir-m31-capacity-v0");
    fs::create_dir_all(&results_root)?;
    fs::create_dir_all(results_root.join("manifests"))?;
    if !results_root.join("whir-transcript/raw.jsonl").exists() {
        run_phase2_transcript_experiments()?;
    }
    if !results_root.join("whir-multiproof/raw.jsonl").exists() {
        run_phase2_multiproof_experiments()?;
    }
    if !results_root.join("whir-fold-payload/raw.jsonl").exists() {
        run_phase2_fold_payload_experiments()?;
    }
    if !results_root
        .join("whir-multiproof-payload/raw.jsonl")
        .exists()
    {
        run_phase2_multiproof_payload_experiments()?;
    }
    if freeze_dir.exists() {
        fs::remove_dir_all(&freeze_dir)?;
    }
    fs::create_dir_all(&freeze_dir)?;

    let transcript_records = load_jsonl_records::<WhirTranscriptMeasurement>(
        &results_root.join("whir-transcript/raw.jsonl"),
    )?;
    let multiproof_records = load_jsonl_records::<WhirMultiproofMeasurement>(
        &results_root.join("whir-multiproof/raw.jsonl"),
    )?;
    let fold_records = load_jsonl_records::<WhirFoldPayloadMeasurement>(
        &results_root.join("whir-fold-payload/raw.jsonl"),
    )?;
    let payload_records = load_jsonl_records::<WhirMultiproofPayloadMeasurement>(
        &results_root.join("whir-multiproof-payload/raw.jsonl"),
    )?;

    let summary = build_capacity_v0_freeze_summary(
        &root,
        &transcript_records,
        &multiproof_records,
        &fold_records,
        &payload_records,
    )?;
    write_json(&freeze_dir.join("summary.json"), &summary)?;
    write_json(
        &results_root.join("manifests/whir-m31-capacity-v0.json"),
        &summary,
    )?;

    let summary_path = results_root.join("summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!("cargo xtask phase2-freeze-capacity-v0");
    summary_value["shipping_recommendation"] = json!(format!(
        "{} freezes {} with {} / {} / {} / {} / {} as the shipping profile.",
        summary.profile_name,
        summary.scenario_name,
        summary.arithmetic_kernel_id,
        summary.extension_kernel_id,
        summary.lift_policy,
        summary.whir_fold_mode,
        summary.merkle_proof_mode
    ));
    summary_value["whir_m31_capacity_v0_summary"] = serde_json::to_value(&summary)?;
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in &summary.raw_artifacts {
        if !artifact_strings.iter().any(|entry| entry == artifact) {
            artifact_strings.push(artifact.clone());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    write_json(&summary_path, &summary_value)?;

    let phase2_report = if docs_path.exists() {
        replace_markdown_section(
            &fs::read_to_string(&docs_path)?,
            "## Shipping Freeze",
            &render_capacity_v0_phase2_section(&summary),
        )
    } else {
        render_capacity_v0_phase2_section(&summary)
    };
    fs::write(&docs_path, phase2_report)?;
    fs::write(&capacity_doc_path, render_capacity_v0_doc(&summary))?;
    fs::write(&state_of_play_path, render_state_of_play(&summary))?;
    Ok(())
}

#[derive(Clone)]
struct SavingsEstimate {
    estimated_savings_cu: f64,
    estimated_headroom_cu: f64,
    estimated_post_change_cu: f64,
    biggest_remaining_risk: String,
}

fn phase2_run_config() -> Phase2RunConfig {
    Phase2RunConfig {
        limits: SvmLimits::default(),
        arithmetic_sbf_iterations: vec![
            NamedIterations {
                name: "mul".to_string(),
                iterations: 2_048,
            },
            NamedIterations {
                name: "square".to_string(),
                iterations: 2_048,
            },
            NamedIterations {
                name: "mul_add".to_string(),
                iterations: 2_048,
            },
            NamedIterations {
                name: "inner_product4".to_string(),
                iterations: 512,
            },
            NamedIterations {
                name: "horner4".to_string(),
                iterations: 512,
            },
            NamedIterations {
                name: "denominator_chain4".to_string(),
                iterations: 512,
            },
            NamedIterations {
                name: "skeleton_fold_step".to_string(),
                iterations: 512,
            },
        ],
        extension_sbf_iterations: vec![
            NamedIterations {
                name: "cm31_mul".to_string(),
                iterations: 512,
            },
            NamedIterations {
                name: "cm31_square".to_string(),
                iterations: 512,
            },
            NamedIterations {
                name: "cm31_mul_const".to_string(),
                iterations: 512,
            },
            NamedIterations {
                name: "cm31_inv".to_string(),
                iterations: 48,
            },
            NamedIterations {
                name: "qm31_mul".to_string(),
                iterations: 256,
            },
            NamedIterations {
                name: "qm31_square".to_string(),
                iterations: 256,
            },
            NamedIterations {
                name: "qm31_mul_const".to_string(),
                iterations: 256,
            },
            NamedIterations {
                name: "qm31_inv".to_string(),
                iterations: 24,
            },
            NamedIterations {
                name: "skeleton_accumulator".to_string(),
                iterations: 96,
            },
        ],
        upload_chunk_size: 640,
        upload_repetitions: 1,
        verify_repetitions: 3,
        skeleton_repeat_inside_instruction: 12,
        whir_query_repeat_inside_instruction: 1,
        whir_transcript_repeat_inside_instruction: 1,
        whir_transcript_verify_repetitions: 10,
        whir_transcript_trace_repetitions: 10,
        proof_plan: ProofPlanSummary {
            query_count: 4,
            fold_arity: 4,
            merkle_depth: 16,
            merkle_paths: 8,
            target_proof_bytes: 5_120,
            query_schedule_seed: 0xfeed_beef_dead_c0de,
            statement_seed: 0x1234_5678_9abc_def0,
        },
        whir_query_scenarios: vec![
            WhirQueryScenarioSeed {
                name: "whir_t100_capacity_full".to_string(),
                security_target_bits: 100.0,
                soundness_assumption: "whir_capacity_full".to_string(),
                log_inv_rate: 4,
                grinding_bits: 32,
            },
            WhirQueryScenarioSeed {
                name: "whir_t128_capacity_full".to_string(),
                security_target_bits: 128.0,
                soundness_assumption: "whir_capacity_full".to_string(),
                log_inv_rate: 4,
                grinding_bits: 32,
            },
            WhirQueryScenarioSeed {
                name: "whir_t128_johnson_full".to_string(),
                security_target_bits: 128.0,
                soundness_assumption: "whir_johnson_full".to_string(),
                log_inv_rate: 4,
                grinding_bits: 32,
            },
        ],
    }
}

fn arithmetic_candidates() -> Vec<ArithmeticCandidate> {
    vec![
        ArithmeticCandidate {
            name: "reference_canonical",
            config: Phase2ArithmeticConfig::new(
                ArithmeticKernelId::ReferenceCanonical,
                ReductionMode::Canonical,
                LazyReductionMode::None,
            ),
        },
        ArithmeticCandidate {
            name: "direct_m31",
            config: Phase2ArithmeticConfig::new(
                ArithmeticKernelId::DirectM31,
                ReductionMode::DirectM31,
                LazyReductionMode::None,
            ),
        },
        ArithmeticCandidate {
            name: "direct_m31_lazy",
            config: Phase2ArithmeticConfig::new(
                ArithmeticKernelId::DirectM31Lazy,
                ReductionMode::DirectM31,
                LazyReductionMode::Batch4,
            ),
        },
        ArithmeticCandidate {
            name: "montgomery_form",
            config: Phase2ArithmeticConfig::new(
                ArithmeticKernelId::Montgomery,
                ReductionMode::Montgomery,
                LazyReductionMode::None,
            ),
        },
        ArithmeticCandidate {
            name: "barrett_reduction",
            config: Phase2ArithmeticConfig::new(
                ArithmeticKernelId::Barrett,
                ReductionMode::Barrett,
                LazyReductionMode::None,
            ),
        },
    ]
}

fn run_arithmetic_experiment(
    harness: &BenchHarness,
    config: &Phase2RunConfig,
    _results_dir: &Path,
) -> Result<Vec<ArithmeticMeasurement>> {
    let workloads = [
        ArithmeticWorkloadId::Mul,
        ArithmeticWorkloadId::Square,
        ArithmeticWorkloadId::MulAdd,
        ArithmeticWorkloadId::InnerProduct4,
        ArithmeticWorkloadId::Horner4,
        ArithmeticWorkloadId::DenominatorChain4,
        ArithmeticWorkloadId::SkeletonFoldStep,
    ];
    let mut records = Vec::new();
    for candidate in arithmetic_candidates() {
        for workload in workloads {
            let iterations =
                named_iterations(&config.arithmetic_sbf_iterations, workload_name(workload));
            for repetition in 0..3 {
                let host_start = Instant::now();
                let host_outcome =
                    run_phase2_arithmetic_bench(candidate.config, workload, iterations);
                let elapsed_ns = host_start.elapsed().as_nanos();
                let units = arithmetic_logical_units(workload, iterations);
                records.push(ArithmeticMeasurement {
                    family: "experiment_a".to_string(),
                    kernel_id: candidate.name.to_string(),
                    reduction_mode: reduction_mode_name(candidate.config.reduction_mode)
                        .to_string(),
                    lazy_reduction_mode: lazy_mode_name(candidate.config.lazy_reduction_mode)
                        .to_string(),
                    workload: workload_name(workload).to_string(),
                    domain: "host".to_string(),
                    repetition,
                    iterations,
                    logical_units: units,
                    actual_cu: None,
                    cu_per_unit: None,
                    elapsed_ns: Some(elapsed_ns),
                    ns_per_unit: Some(elapsed_ns as f64 / units as f64),
                    code_size_bytes: None,
                    zero_heap: true,
                    stack_observation: "not_observed".to_string(),
                    counters: host_outcome.counters.into(),
                });

                let tx = simulate_plan(
                    harness,
                    TxPlan {
                        instructions: vec![build_phase2_arithmetic_instruction(
                            harness.program_id,
                            candidate.config,
                            workload,
                            iterations,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                records.push(ArithmeticMeasurement {
                    family: "experiment_a".to_string(),
                    kernel_id: candidate.name.to_string(),
                    reduction_mode: reduction_mode_name(candidate.config.reduction_mode)
                        .to_string(),
                    lazy_reduction_mode: lazy_mode_name(candidate.config.lazy_reduction_mode)
                        .to_string(),
                    workload: workload_name(workload).to_string(),
                    domain: "sbf".to_string(),
                    repetition,
                    iterations,
                    logical_units: units,
                    actual_cu: tx.units_consumed,
                    cu_per_unit: tx.units_consumed.map(|value| value as f64 / units as f64),
                    elapsed_ns: None,
                    ns_per_unit: None,
                    code_size_bytes: None,
                    zero_heap: true,
                    stack_observation: "not_observed".to_string(),
                    counters: host_outcome.counters.into(),
                });
            }
        }
    }
    Ok(records)
}

fn run_extension_experiment(
    harness: &BenchHarness,
    config: &Phase2RunConfig,
    base: Phase2ArithmeticConfig,
    _results_dir: &Path,
) -> Result<Vec<ExtensionMeasurement>> {
    let workloads = [
        ExtensionWorkloadId::Cm31Mul,
        ExtensionWorkloadId::Cm31Square,
        ExtensionWorkloadId::Cm31MulConst,
        ExtensionWorkloadId::Cm31Inv,
        ExtensionWorkloadId::Qm31Mul,
        ExtensionWorkloadId::Qm31Square,
        ExtensionWorkloadId::Qm31MulConst,
        ExtensionWorkloadId::Qm31Inv,
        ExtensionWorkloadId::SkeletonAccumulator,
    ];
    let mut records = Vec::new();
    for extension_kernel_id in [ExtensionKernelId::Schoolbook, ExtensionKernelId::Karatsuba] {
        let ext_config = Phase2ExtensionConfig {
            base,
            extension_kernel_id,
        };
        for workload in workloads {
            let iterations = named_iterations(
                &config.extension_sbf_iterations,
                extension_workload_name(workload),
            );
            for repetition in 0..3 {
                let host_start = Instant::now();
                let host_outcome = run_phase2_extension_bench(ext_config, workload, iterations);
                let elapsed_ns = host_start.elapsed().as_nanos();
                let units = extension_logical_units(workload, iterations);
                records.push(ExtensionMeasurement {
                    extension_kernel_id: extension_kernel_name(extension_kernel_id).to_string(),
                    workload: extension_workload_name(workload).to_string(),
                    domain: "host".to_string(),
                    repetition,
                    iterations,
                    logical_units: units,
                    actual_cu: None,
                    cu_per_unit: None,
                    elapsed_ns: Some(elapsed_ns),
                    ns_per_unit: Some(elapsed_ns as f64 / units as f64),
                    zero_heap: true,
                    counters: host_outcome.counters.into(),
                });

                let tx = simulate_plan(
                    harness,
                    TxPlan {
                        instructions: vec![build_phase2_extension_instruction(
                            harness.program_id,
                            ext_config,
                            workload,
                            iterations,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                records.push(ExtensionMeasurement {
                    extension_kernel_id: extension_kernel_name(extension_kernel_id).to_string(),
                    workload: extension_workload_name(workload).to_string(),
                    domain: "sbf".to_string(),
                    repetition,
                    iterations,
                    logical_units: units,
                    actual_cu: tx.units_consumed,
                    cu_per_unit: tx.units_consumed.map(|value| value as f64 / units as f64),
                    elapsed_ns: None,
                    ns_per_unit: None,
                    zero_heap: true,
                    counters: host_outcome.counters.into(),
                });
            }
        }
    }
    Ok(records)
}

fn run_skeleton_matrix(
    harness: &BenchHarness,
    config: &Phase2RunConfig,
    arithmetic: Phase2ArithmeticConfig,
    phase1_summary: &Phase1Summary,
    results_dir: &Path,
) -> Result<Vec<EndToEndMeasurement>> {
    let mut records = Vec::new();
    for variant in skeleton_variants(arithmetic) {
        let proof_bytes =
            build_phase2_proof_bytes(proof_plan(config), variant.config.whir_fold_mode);
        let manifest_path = results_dir.join(format!("{}.json", variant.name));
        write_json(
            &manifest_path,
            &json!({
                "name": variant.name,
                "config": {
                    "arithmetic_kernel_id": arithmetic_kernel_name(variant.config.arithmetic_kernel_id),
                    "reduction_mode": reduction_mode_name(variant.config.reduction_mode),
                    "lazy_reduction_mode": lazy_mode_name(variant.config.lazy_reduction_mode),
                    "extension_kernel_id": extension_kernel_name(variant.config.extension_kernel_id),
                    "lift_policy": lift_policy_name(variant.config.lift_policy),
                    "whir_fold_mode": fold_mode_name(variant.config.whir_fold_mode),
                    "merkle_proof_mode": merkle_mode_name(variant.config.merkle_proof_mode),
                },
                "proof_plan": config.proof_plan,
            }),
        )?;

        let host_start = Instant::now();
        let host_outcome = run_phase2_skeleton_verify(
            variant.config,
            &proof_bytes,
            config.skeleton_repeat_inside_instruction,
        )
        .map_err(|err| anyhow!(err))?;
        let host_elapsed_ns = host_start.elapsed().as_nanos();

        let (upload_account, _upload_records, upload_cu) = upload_bytes(
            harness,
            &proof_bytes,
            config.upload_chunk_size,
            true,
            &format!("phase2/{}", variant.name),
            config.upload_repetitions,
        )?;
        let upload_chunks = proof_bytes.len().div_ceil(config.upload_chunk_size) as u64;
        let projection = project_features(
            &variant.name,
            &host_outcome.counters,
            proof_bytes.len() as u64,
            upload_chunks,
            config.upload_chunk_size,
            VERIFY_HEAP_FRAME_BYTES as u64,
        );
        let score = score_profile_with_components(
            &phase1_summary.model.chosen,
            phase1_summary
                .verification_core_model
                .as_ref()
                .map(|value| &value.chosen),
            phase1_summary
                .transport_model
                .as_ref()
                .map(|value| &value.chosen),
            &config.limits,
            &projection.input,
        )?;

        records.push(EndToEndMeasurement {
            variant: variant.name.clone(),
            arithmetic_kernel_id: arithmetic_kernel_name(variant.config.arithmetic_kernel_id)
                .to_string(),
            extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                .to_string(),
            lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
            whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
            merkle_proof_mode: merkle_mode_name(variant.config.merkle_proof_mode).to_string(),
            stage: "host_verify".to_string(),
            repetition: 0,
            proof_bytes: proof_bytes.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks,
            heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
            heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
            actual_cu: None,
            elapsed_ns: Some(host_elapsed_ns),
            counters: host_outcome.counters.into(),
            field_mul_projection: projection.field_mul_projection,
            extension_mul_projection: projection.extension_mul_projection,
            field_inv_projection: projection.field_inv_projection,
            predicted_cu: None,
            predicted_component_cu: None,
            predicted_core_cu: None,
            predicted_transport_cu: None,
            abs_error_cu: None,
            rel_error: None,
        });

        records.push(EndToEndMeasurement {
            variant: variant.name.clone(),
            arithmetic_kernel_id: arithmetic_kernel_name(variant.config.arithmetic_kernel_id)
                .to_string(),
            extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                .to_string(),
            lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
            whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
            merkle_proof_mode: merkle_mode_name(variant.config.merkle_proof_mode).to_string(),
            stage: "upload_total".to_string(),
            repetition: 0,
            proof_bytes: proof_bytes.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks,
            heap_frame_bytes_requested: 0,
            heap_pages_32k: 0,
            actual_cu: Some(upload_cu),
            elapsed_ns: None,
            counters: CounterSummary::from(Phase2Counters {
                proof_bytes: proof_bytes.len() as u64,
                sha_calls: upload_chunks,
                sha_bytes: proof_bytes.len() as u64 + upload_chunks * 32,
                ..Phase2Counters::default()
            }),
            field_mul_projection: projection.field_mul_projection,
            extension_mul_projection: projection.extension_mul_projection,
            field_inv_projection: projection.field_inv_projection,
            predicted_cu: None,
            predicted_component_cu: None,
            predicted_core_cu: None,
            predicted_transport_cu: None,
            abs_error_cu: None,
            rel_error: None,
        });

        for repetition in 0..config.verify_repetitions {
            let tx = simulate_plan(
                harness,
                TxPlan {
                    instructions: vec![build_phase2_skeleton_instruction(
                        harness.program_id,
                        upload_account.pubkey(),
                        variant.config,
                        config.skeleton_repeat_inside_instruction,
                    )],
                    compute_unit_limit: None,
                    heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                },
            )?;
            let total_cu = tx.units_consumed.map(|value| value + upload_cu);
            records.push(EndToEndMeasurement {
                variant: variant.name.clone(),
                arithmetic_kernel_id: arithmetic_kernel_name(variant.config.arithmetic_kernel_id)
                    .to_string(),
                extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                    .to_string(),
                lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
                whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
                merkle_proof_mode: merkle_mode_name(variant.config.merkle_proof_mode).to_string(),
                stage: "verify_sbf".to_string(),
                repetition,
                proof_bytes: proof_bytes.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                actual_cu: tx.units_consumed,
                elapsed_ns: None,
                counters: host_outcome.counters.into(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
                predicted_cu: Some(score.predicted_cu),
                predicted_component_cu: score.component_predicted_cu,
                predicted_core_cu: score.verification_core_cu,
                predicted_transport_cu: score.transport_overhead_cu,
                abs_error_cu: tx
                    .units_consumed
                    .map(|value| (value as f64 + upload_cu as f64 - score.predicted_cu).abs()),
                rel_error: tx.units_consumed.map(|value| {
                    let total = value as f64 + upload_cu as f64;
                    (total - score.predicted_cu).abs() / total.max(1.0)
                }),
            });
            records.push(EndToEndMeasurement {
                variant: variant.name.clone(),
                arithmetic_kernel_id: arithmetic_kernel_name(variant.config.arithmetic_kernel_id)
                    .to_string(),
                extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                    .to_string(),
                lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
                whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
                merkle_proof_mode: merkle_mode_name(variant.config.merkle_proof_mode).to_string(),
                stage: "total_sbf".to_string(),
                repetition,
                proof_bytes: proof_bytes.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                actual_cu: total_cu,
                elapsed_ns: None,
                counters: host_outcome.counters.into(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
                predicted_cu: Some(score.predicted_cu),
                predicted_component_cu: score.component_predicted_cu,
                predicted_core_cu: score.verification_core_cu,
                predicted_transport_cu: score.transport_overhead_cu,
                abs_error_cu: total_cu.map(|value| (value as f64 - score.predicted_cu).abs()),
                rel_error: total_cu
                    .map(|value| (value as f64 - score.predicted_cu).abs() / value as f64),
            });
        }
    }
    Ok(records)
}

fn run_high_fidelity_whir_query_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    phase1_summary: &Phase1Summary,
    results_dir: &Path,
) -> Result<Vec<WhirQueryMeasurement>> {
    let scenarios = derive_whir_query_scenarios(config, phase1_summary)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "log_inv_rate": scenario.seed.log_inv_rate,
                    "grinding_bits": scenario.seed.grinding_bits,
                    "legacy_bound_cu": scenario.legacy_bound_cu,
                    "total_explicit_query_count": scenario.total_explicit_query_count,
                    "round_query_counts": scenario.round_query_counts,
                    "proof_bytes": scenario.profile.features.proof_bytes,
                    "statement_shape": phase2_whir_statement_shape_json(scenario.plan.statement_shape),
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let mut records = Vec::new();
    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        for variant in whir_query_variants() {
            eprintln!(
                "phase2: whir-query scenario={} variant={}",
                scenario.seed.name, variant.name
            );
            let variant_name = format!("{}_{}", scenario.seed.name, variant.name);
            let proof_bytes =
                build_phase2_whir_query_proof_bytes(scenario.plan, variant.config.whir_fold_mode);
            let manifest_path = results_dir.join(format!("{variant_name}.json"));
            write_json(
                &manifest_path,
                &json!({
                    "name": variant_name,
                    "scenario": {
                        "security_target_bits": scenario.seed.security_target_bits,
                        "soundness_assumption": scenario.seed.soundness_assumption,
                        "legacy_bound_cu": scenario.legacy_bound_cu,
                        "total_explicit_query_count": scenario.total_explicit_query_count,
                        "round_query_counts": scenario.round_query_counts,
                    },
                    "config": {
                        "arithmetic_kernel_id": arithmetic_kernel_name(variant.config.arithmetic_kernel_id),
                        "reduction_mode": reduction_mode_name(variant.config.reduction_mode),
                        "lazy_reduction_mode": lazy_mode_name(variant.config.lazy_reduction_mode),
                        "extension_kernel_id": extension_kernel_name(variant.config.extension_kernel_id),
                        "lift_policy": lift_policy_name(variant.config.lift_policy),
                        "whir_fold_mode": fold_mode_name(variant.config.whir_fold_mode),
                        "merkle_proof_mode": merkle_mode_name(variant.config.merkle_proof_mode),
                    },
                    "plan": {
                        "round_count": scenario.plan.round_count,
                        "target_proof_bytes": scenario.plan.target_proof_bytes,
                        "query_schedule_seed": scenario.plan.query_schedule_seed,
                        "statement_seed": scenario.plan.statement_seed,
                        "statement_shape": phase2_whir_statement_shape_json(scenario.plan.statement_shape),
                        "rounds": scenario
                            .plan
                            .rounds
                            .iter()
                            .map(|round| json!({
                                "query_count": round.query_count,
                                "merkle_depth": round.merkle_depth,
                                "ood_samples": round.ood_samples,
                                "opening_count": round.opening_count,
                                "selector_count": round.selector_count,
                            }))
                            .collect::<Vec<_>>(),
                    },
                }),
            )?;

            let host_start = Instant::now();
            let host_outcome = run_phase2_whir_query_verify(
                variant.config,
                &proof_bytes,
                config.whir_query_repeat_inside_instruction,
            )
            .map_err(|err| anyhow!(err))?;
            let host_elapsed_ns = host_start.elapsed().as_nanos();

            let (upload_account, _upload_records, upload_cu) = upload_bytes(
                &harness,
                &proof_bytes,
                config.upload_chunk_size,
                true,
                &format!("phase2/{variant_name}"),
                config.upload_repetitions,
            )?;
            let upload_chunks = proof_bytes.len().div_ceil(config.upload_chunk_size) as u64;
            let projection = project_features(
                &variant_name,
                &host_outcome.counters,
                proof_bytes.len() as u64,
                upload_chunks,
                config.upload_chunk_size,
                VERIFY_HEAP_FRAME_BYTES as u64,
            );
            let score = score_profile_with_components(
                &phase1_summary.model.chosen,
                phase1_summary
                    .verification_core_model
                    .as_ref()
                    .map(|value| &value.chosen),
                phase1_summary
                    .transport_model
                    .as_ref()
                    .map(|value| &value.chosen),
                &config.limits,
                &projection.input,
            )?;

            records.push(WhirQueryMeasurement {
                scenario_name: scenario.seed.name.clone(),
                variant: variant.name.to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                legacy_bound_cu: scenario.legacy_bound_cu,
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                arithmetic_kernel_id: arithmetic_kernel_name(variant.config.arithmetic_kernel_id)
                    .to_string(),
                extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                    .to_string(),
                lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
                whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
                stage: "host_verify".to_string(),
                repetition: 0,
                proof_bytes: proof_bytes.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                actual_cu: None,
                elapsed_ns: Some(host_elapsed_ns),
                counters: host_outcome.counters.into(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
                predicted_cu: None,
                predicted_component_cu: None,
                predicted_core_cu: None,
                predicted_transport_cu: None,
                abs_error_cu: None,
                rel_error: None,
            });

            records.push(WhirQueryMeasurement {
                scenario_name: scenario.seed.name.clone(),
                variant: variant.name.to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                legacy_bound_cu: scenario.legacy_bound_cu,
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                arithmetic_kernel_id: arithmetic_kernel_name(variant.config.arithmetic_kernel_id)
                    .to_string(),
                extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                    .to_string(),
                lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
                whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
                stage: "upload_total".to_string(),
                repetition: 0,
                proof_bytes: proof_bytes.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: 0,
                heap_pages_32k: 0,
                actual_cu: Some(upload_cu),
                elapsed_ns: None,
                counters: CounterSummary::from(Phase2Counters {
                    proof_bytes: proof_bytes.len() as u64,
                    sha_calls: upload_chunks,
                    sha_bytes: proof_bytes.len() as u64 + upload_chunks * 32,
                    ..Phase2Counters::default()
                }),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
                predicted_cu: None,
                predicted_component_cu: None,
                predicted_core_cu: None,
                predicted_transport_cu: None,
                abs_error_cu: None,
                rel_error: None,
            });

            for repetition in 0..config.verify_repetitions {
                let tx = simulate_plan(
                    &harness,
                    TxPlan {
                        instructions: vec![build_phase2_whir_query_instruction(
                            harness.program_id,
                            upload_account.pubkey(),
                            variant.config,
                            config.whir_query_repeat_inside_instruction,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                let total_cu = tx.units_consumed.map(|value| value + upload_cu);
                records.push(WhirQueryMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    variant: variant.name.to_string(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    legacy_bound_cu: scenario.legacy_bound_cu,
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    arithmetic_kernel_id: arithmetic_kernel_name(
                        variant.config.arithmetic_kernel_id,
                    )
                    .to_string(),
                    extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                        .to_string(),
                    lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
                    whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
                    stage: "verify_sbf".to_string(),
                    repetition,
                    proof_bytes: proof_bytes.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    actual_cu: tx.units_consumed,
                    elapsed_ns: None,
                    counters: host_outcome.counters.into(),
                    field_mul_projection: projection.field_mul_projection,
                    extension_mul_projection: projection.extension_mul_projection,
                    field_inv_projection: projection.field_inv_projection,
                    predicted_cu: Some(score.predicted_cu),
                    predicted_component_cu: score.component_predicted_cu,
                    predicted_core_cu: score.verification_core_cu,
                    predicted_transport_cu: score.transport_overhead_cu,
                    abs_error_cu: tx
                        .units_consumed
                        .map(|value| (value as f64 + upload_cu as f64 - score.predicted_cu).abs()),
                    rel_error: tx.units_consumed.map(|value| {
                        let total = value as f64 + upload_cu as f64;
                        (total - score.predicted_cu).abs() / total.max(1.0)
                    }),
                });
                records.push(WhirQueryMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    variant: variant.name.to_string(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    legacy_bound_cu: scenario.legacy_bound_cu,
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    arithmetic_kernel_id: arithmetic_kernel_name(
                        variant.config.arithmetic_kernel_id,
                    )
                    .to_string(),
                    extension_kernel_id: extension_kernel_name(variant.config.extension_kernel_id)
                        .to_string(),
                    lift_policy: lift_policy_name(variant.config.lift_policy).to_string(),
                    whir_fold_mode: fold_mode_name(variant.config.whir_fold_mode).to_string(),
                    stage: "total_sbf".to_string(),
                    repetition,
                    proof_bytes: proof_bytes.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    actual_cu: total_cu,
                    elapsed_ns: None,
                    counters: host_outcome.counters.into(),
                    field_mul_projection: projection.field_mul_projection,
                    extension_mul_projection: projection.extension_mul_projection,
                    field_inv_projection: projection.field_inv_projection,
                    predicted_cu: Some(score.predicted_cu),
                    predicted_component_cu: score.component_predicted_cu,
                    predicted_core_cu: score.verification_core_cu,
                    predicted_transport_cu: score.transport_overhead_cu,
                    abs_error_cu: total_cu.map(|value| (value as f64 - score.predicted_cu).abs()),
                    rel_error: total_cu
                        .map(|value| (value as f64 - score.predicted_cu).abs() / value as f64),
                });
            }
        }
    }
    Ok(records)
}

fn run_whir_transcript_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    results_dir: &Path,
    manifests_dir: &Path,
) -> Result<Vec<WhirTranscriptMeasurement>> {
    let scenarios = derive_whir_transcript_scenarios(config)?;
    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&proofs_dir)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "round_query_counts": scenario.round_query_counts,
                    "commitment_ood_samples": scenario.commitment_ood_samples,
                    "query_plan": {
                        "round_count": scenario.query_plan.round_count,
                        "target_proof_bytes": scenario.query_plan.target_proof_bytes,
                    },
                    "transcript_plan": {
                        "round_count": scenario.transcript_plan.round_count,
                        "target_proof_bytes": scenario.transcript_plan.target_proof_bytes,
                        "initial_sumcheck_rounds": scenario.transcript_plan.initial_sumcheck_rounds,
                        "final_query_count": scenario.transcript_plan.final_query_count,
                        "final_sumcheck_rounds": scenario.transcript_plan.final_sumcheck_rounds,
                    }
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let query_only_config = whir_query_baseline_config();
    let transcript_config = whir_transcript_config();
    let mut validation = Vec::new();
    let mut records = Vec::new();

    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        eprintln!("phase2: whir-transcript scenario={}", scenario.seed.name);

        let query_only_proof = build_phase2_whir_query_proof_bytes(
            scenario.query_plan,
            query_only_config.whir_fold_mode,
        );
        let transcript_proof = build_phase2_whir_transcript_proof_bytes(
            scenario.transcript_plan,
            transcript_config.whir_fold_mode,
            transcript_config.merkle_proof_mode,
        );
        let transcript_layout = whir_transcript_layout(
            scenario.transcript_plan,
            transcript_config.merkle_proof_mode,
        )?;

        let valid_path = proofs_dir.join(format!("{}_valid.bin", scenario.seed.name));
        fs::write(&valid_path, &transcript_proof)?;
        let mut invalid_challenge = transcript_proof.clone();
        if transcript_layout.final_pow_nonce_offset < invalid_challenge.len() {
            invalid_challenge[transcript_layout.final_pow_nonce_offset] ^= 0x01;
        }
        let invalid_challenge_path =
            proofs_dir.join(format!("{}_invalid_challenge.bin", scenario.seed.name));
        fs::write(&invalid_challenge_path, &invalid_challenge)?;
        let mut invalid_missing_query = transcript_proof.clone();
        if transcript_layout.final_query_offset + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES
            <= invalid_missing_query.len()
        {
            invalid_missing_query.drain(
                transcript_layout.final_query_offset
                    ..transcript_layout.final_query_offset + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES,
            );
        } else {
            invalid_missing_query.truncate(
                invalid_missing_query
                    .len()
                    .saturating_sub(WHIR_TRANSCRIPT_FINAL_QUERY_BYTES),
            );
        }
        let invalid_missing_query_path =
            proofs_dir.join(format!("{}_invalid_missing_query.bin", scenario.seed.name));
        fs::write(&invalid_missing_query_path, &invalid_missing_query)?;
        let mut invalid_folding = transcript_proof.clone();
        if transcript_layout.final_sumcheck_offset < invalid_folding.len() {
            invalid_folding[transcript_layout.final_sumcheck_offset] ^= 0x08;
        }
        let invalid_folding_path =
            proofs_dir.join(format!("{}_invalid_folding.bin", scenario.seed.name));
        fs::write(&invalid_folding_path, &invalid_folding)?;
        let mut invalid_truncated = transcript_proof.clone();
        invalid_truncated.truncate(transcript_proof.len().saturating_sub(8));
        let invalid_truncated_path =
            proofs_dir.join(format!("{}_invalid_truncated.bin", scenario.seed.name));
        fs::write(&invalid_truncated_path, &invalid_truncated)?;

        let host_valid = run_phase2_whir_transcript_verify(
            transcript_config,
            &transcript_proof,
            config.whir_transcript_repeat_inside_instruction,
            WhirTranscriptTraceMode::Disabled,
        );
        let host_invalid_challenge = run_phase2_whir_transcript_verify(
            transcript_config,
            &invalid_challenge,
            config.whir_transcript_repeat_inside_instruction,
            WhirTranscriptTraceMode::Disabled,
        );
        let host_invalid_missing_query = run_phase2_whir_transcript_verify(
            transcript_config,
            &invalid_missing_query,
            config.whir_transcript_repeat_inside_instruction,
            WhirTranscriptTraceMode::Disabled,
        );
        let host_invalid_folding = run_phase2_whir_transcript_verify(
            transcript_config,
            &invalid_folding,
            config.whir_transcript_repeat_inside_instruction,
            WhirTranscriptTraceMode::Disabled,
        );
        let host_invalid_truncated = run_phase2_whir_transcript_verify(
            transcript_config,
            &invalid_truncated,
            config.whir_transcript_repeat_inside_instruction,
            WhirTranscriptTraceMode::Disabled,
        );
        validation.push(json!({
            "scenario_name": scenario.seed.name,
            "valid_proof": host_valid.is_ok(),
            "invalid_challenge_rejected": host_invalid_challenge.is_err(),
            "invalid_missing_query_rejected": host_invalid_missing_query.is_err(),
            "invalid_folding_rejected": host_invalid_folding.is_err(),
            "invalid_truncated_rejected": host_invalid_truncated.is_err(),
            "proofs": {
                "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
            }
        }));
        if !host_valid.is_ok()
            || !host_invalid_challenge.is_err()
            || !host_invalid_missing_query.is_err()
            || !host_invalid_folding.is_err()
            || !host_invalid_truncated.is_err()
        {
            bail!(
                "WHIR transcript validation failed for {}: valid={:?}, invalid_challenge={:?}, invalid_missing_query={:?}, invalid_folding={:?}, invalid_truncated={:?}",
                scenario.seed.name,
                host_valid.as_ref().map(|_| "ok").map_err(|err| *err),
                host_invalid_challenge
                    .as_ref()
                    .map(|_| "ok")
                    .map_err(|err| *err),
                host_invalid_missing_query
                    .as_ref()
                    .map(|_| "ok")
                    .map_err(|err| *err),
                host_invalid_folding
                    .as_ref()
                    .map(|_| "ok")
                    .map_err(|err| *err),
                host_invalid_truncated
                    .as_ref()
                    .map(|_| "ok")
                    .map_err(|err| *err),
            );
        }

        write_json(
            &manifests_dir.join(format!("{}_whir_transcript.json", scenario.seed.name)),
            &json!({
                "scenario_name": scenario.seed.name,
                "security_target_bits": scenario.seed.security_target_bits,
                "soundness_assumption": scenario.seed.soundness_assumption,
                "query_only_config": verifier_config_json(query_only_config),
                "transcript_config": verifier_config_json(transcript_config),
                "statement_shape": phase2_whir_statement_shape_json(scenario.transcript_plan.statement_shape),
                "query_plan": whir_query_plan_json(scenario.query_plan),
                "transcript_plan": whir_transcript_plan_json(scenario.transcript_plan),
                "proofs": {
                    "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                    "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                    "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                    "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                    "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
                }
            }),
        )?;

        let query_host_start = Instant::now();
        let query_host_outcome =
            run_phase2_whir_query_verify(query_only_config, &query_only_proof, 1)
                .map_err(|err| anyhow!(err))?;
        let query_host_elapsed_ns = query_host_start.elapsed().as_nanos();
        let (query_upload_account, _query_upload_records, query_upload_cu) = upload_bytes(
            &harness,
            &query_only_proof,
            config.upload_chunk_size,
            true,
            &format!("phase2/{}-query-only", scenario.seed.name),
            config.upload_repetitions,
        )?;
        let query_upload_chunks = query_only_proof.len().div_ceil(config.upload_chunk_size) as u64;
        let query_projection = project_features(
            &format!("{}_query_only", scenario.seed.name),
            &query_host_outcome.counters,
            query_only_proof.len() as u64,
            query_upload_chunks,
            config.upload_chunk_size,
            VERIFY_HEAP_FRAME_BYTES as u64,
        );

        records.push(WhirTranscriptMeasurement {
            scenario_name: scenario.seed.name.clone(),
            path_variant: "query_only".to_string(),
            security_target_bits: scenario.seed.security_target_bits,
            soundness_assumption: scenario.seed.soundness_assumption.clone(),
            total_explicit_query_count: scenario.total_explicit_query_count,
            round_query_counts: scenario.round_query_counts.clone(),
            commitment_ood_samples: scenario.commitment_ood_samples,
            proof_bytes: query_only_proof.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks: query_upload_chunks,
            heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
            heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
            stage: "host_verify".to_string(),
            repetition: 0,
            actual_cu: None,
            elapsed_ns: Some(query_host_elapsed_ns),
            counters: query_host_outcome.counters.into(),
            field_mul_projection: query_projection.field_mul_projection,
            extension_mul_projection: query_projection.extension_mul_projection,
            field_inv_projection: query_projection.field_inv_projection,
        });
        records.push(WhirTranscriptMeasurement {
            scenario_name: scenario.seed.name.clone(),
            path_variant: "query_only".to_string(),
            security_target_bits: scenario.seed.security_target_bits,
            soundness_assumption: scenario.seed.soundness_assumption.clone(),
            total_explicit_query_count: scenario.total_explicit_query_count,
            round_query_counts: scenario.round_query_counts.clone(),
            commitment_ood_samples: scenario.commitment_ood_samples,
            proof_bytes: query_only_proof.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks: query_upload_chunks,
            heap_frame_bytes_requested: 0,
            heap_pages_32k: 0,
            stage: "upload_total".to_string(),
            repetition: 0,
            actual_cu: Some(query_upload_cu),
            elapsed_ns: None,
            counters: CounterSummary::default(),
            field_mul_projection: query_projection.field_mul_projection,
            extension_mul_projection: query_projection.extension_mul_projection,
            field_inv_projection: query_projection.field_inv_projection,
        });
        for repetition in 0..config.whir_transcript_verify_repetitions {
            let tx = simulate_plan(
                &harness,
                TxPlan {
                    instructions: vec![build_phase2_whir_query_instruction(
                        harness.program_id,
                        query_upload_account.pubkey(),
                        query_only_config,
                        1,
                    )],
                    compute_unit_limit: None,
                    heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                },
            )?;
            let total_cu = tx.units_consumed.map(|value| value + query_upload_cu);
            records.push(WhirTranscriptMeasurement {
                scenario_name: scenario.seed.name.clone(),
                path_variant: "query_only".to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: query_only_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks: query_upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "verify_sbf".to_string(),
                repetition,
                actual_cu: tx.units_consumed,
                elapsed_ns: None,
                counters: query_host_outcome.counters.into(),
                field_mul_projection: query_projection.field_mul_projection,
                extension_mul_projection: query_projection.extension_mul_projection,
                field_inv_projection: query_projection.field_inv_projection,
            });
            records.push(WhirTranscriptMeasurement {
                scenario_name: scenario.seed.name.clone(),
                path_variant: "query_only".to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: query_only_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks: query_upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "total_sbf".to_string(),
                repetition,
                actual_cu: total_cu,
                elapsed_ns: None,
                counters: query_host_outcome.counters.into(),
                field_mul_projection: query_projection.field_mul_projection,
                extension_mul_projection: query_projection.extension_mul_projection,
                field_inv_projection: query_projection.field_inv_projection,
            });
        }

        let transcript_host_start = Instant::now();
        let transcript_host_outcome = run_phase2_whir_transcript_verify(
            transcript_config,
            &transcript_proof,
            config.whir_transcript_repeat_inside_instruction,
            WhirTranscriptTraceMode::Disabled,
        )
        .map_err(|err| anyhow!(err))?;
        let transcript_host_elapsed_ns = transcript_host_start.elapsed().as_nanos();
        let (transcript_upload_account, _transcript_upload_records, transcript_upload_cu) =
            upload_bytes(
                &harness,
                &transcript_proof,
                config.upload_chunk_size,
                true,
                &format!("phase2/{}-transcript", scenario.seed.name),
                config.upload_repetitions,
            )?;
        let transcript_upload_chunks =
            transcript_proof.len().div_ceil(config.upload_chunk_size) as u64;
        let transcript_projection = project_features(
            &format!("{}_transcript", scenario.seed.name),
            &transcript_host_outcome.counters,
            transcript_proof.len() as u64,
            transcript_upload_chunks,
            config.upload_chunk_size,
            VERIFY_HEAP_FRAME_BYTES as u64,
        );

        records.push(WhirTranscriptMeasurement {
            scenario_name: scenario.seed.name.clone(),
            path_variant: "transcript_full".to_string(),
            security_target_bits: scenario.seed.security_target_bits,
            soundness_assumption: scenario.seed.soundness_assumption.clone(),
            total_explicit_query_count: scenario.total_explicit_query_count,
            round_query_counts: scenario.round_query_counts.clone(),
            commitment_ood_samples: scenario.commitment_ood_samples,
            proof_bytes: transcript_proof.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks: transcript_upload_chunks,
            heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
            heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
            stage: "host_verify".to_string(),
            repetition: 0,
            actual_cu: None,
            elapsed_ns: Some(transcript_host_elapsed_ns),
            counters: transcript_host_outcome.counters.into(),
            field_mul_projection: transcript_projection.field_mul_projection,
            extension_mul_projection: transcript_projection.extension_mul_projection,
            field_inv_projection: transcript_projection.field_inv_projection,
        });
        records.push(WhirTranscriptMeasurement {
            scenario_name: scenario.seed.name.clone(),
            path_variant: "transcript_full".to_string(),
            security_target_bits: scenario.seed.security_target_bits,
            soundness_assumption: scenario.seed.soundness_assumption.clone(),
            total_explicit_query_count: scenario.total_explicit_query_count,
            round_query_counts: scenario.round_query_counts.clone(),
            commitment_ood_samples: scenario.commitment_ood_samples,
            proof_bytes: transcript_proof.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks: transcript_upload_chunks,
            heap_frame_bytes_requested: 0,
            heap_pages_32k: 0,
            stage: "upload_total".to_string(),
            repetition: 0,
            actual_cu: Some(transcript_upload_cu),
            elapsed_ns: None,
            counters: CounterSummary::default(),
            field_mul_projection: transcript_projection.field_mul_projection,
            extension_mul_projection: transcript_projection.extension_mul_projection,
            field_inv_projection: transcript_projection.field_inv_projection,
        });
        for repetition in 0..config.whir_transcript_verify_repetitions {
            let tx = simulate_plan(
                &harness,
                TxPlan {
                    instructions: vec![build_phase2_whir_transcript_instruction(
                        harness.program_id,
                        transcript_upload_account.pubkey(),
                        transcript_config,
                        1,
                        WhirTranscriptTraceMode::Disabled,
                    )],
                    compute_unit_limit: None,
                    heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                },
            )?;
            let total_cu = tx.units_consumed.map(|value| value + transcript_upload_cu);
            records.push(WhirTranscriptMeasurement {
                scenario_name: scenario.seed.name.clone(),
                path_variant: "transcript_full".to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks: transcript_upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "verify_sbf".to_string(),
                repetition,
                actual_cu: tx.units_consumed,
                elapsed_ns: None,
                counters: transcript_host_outcome.counters.into(),
                field_mul_projection: transcript_projection.field_mul_projection,
                extension_mul_projection: transcript_projection.extension_mul_projection,
                field_inv_projection: transcript_projection.field_inv_projection,
            });
            records.push(WhirTranscriptMeasurement {
                scenario_name: scenario.seed.name.clone(),
                path_variant: "transcript_full".to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks: transcript_upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "total_sbf".to_string(),
                repetition,
                actual_cu: total_cu,
                elapsed_ns: None,
                counters: transcript_host_outcome.counters.into(),
                field_mul_projection: transcript_projection.field_mul_projection,
                extension_mul_projection: transcript_projection.extension_mul_projection,
                field_inv_projection: transcript_projection.field_inv_projection,
            });
        }

        for repetition in 0..config.whir_transcript_trace_repetitions {
            let tx = simulate_plan(
                &harness,
                TxPlan {
                    instructions: vec![build_phase2_whir_transcript_instruction(
                        harness.program_id,
                        transcript_upload_account.pubkey(),
                        transcript_config,
                        1,
                        WhirTranscriptTraceMode::Enabled,
                    )],
                    compute_unit_limit: None,
                    heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                },
            )?;
            let phase_costs = parse_whir_transcript_phase_trace(&tx.logs)?;
            for (phase, actual_cu) in phase_costs {
                records.push(WhirTranscriptMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    path_variant: "transcript_full".to_string(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks: transcript_upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: phase,
                    repetition,
                    actual_cu: Some(actual_cu),
                    elapsed_ns: None,
                    counters: CounterSummary::default(),
                    field_mul_projection: transcript_projection.field_mul_projection,
                    extension_mul_projection: transcript_projection.extension_mul_projection,
                    field_inv_projection: transcript_projection.field_inv_projection,
                });
            }
        }
    }

    write_json(&results_dir.join("validation.json"), &validation)?;
    Ok(records)
}

fn run_whir_multiproof_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    results_dir: &Path,
    manifests_dir: &Path,
) -> Result<Vec<WhirMultiproofMeasurement>> {
    let scenarios = derive_whir_transcript_scenarios(config)?;
    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&proofs_dir)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "round_query_counts": scenario.round_query_counts,
                    "commitment_ood_samples": scenario.commitment_ood_samples,
                    "base_target_proof_bytes": scenario.transcript_plan.target_proof_bytes,
                    "variants": [
                        {
                            "merkle_proof_mode": merkle_mode_name(MerkleProofMode::SeparatePaths),
                            "target_proof_bytes": whir_transcript_plan_for_merkle_mode(
                                scenario.transcript_plan,
                                WhirFoldMode::LocalInterpolant,
                                MerkleProofMode::SeparatePaths,
                            )
                            .target_proof_bytes,
                            "synthetic_merkle_nodes": synthetic_whir_transcript_merkle_nodes(
                                scenario.transcript_plan,
                                MerkleProofMode::SeparatePaths,
                            ),
                            "synthetic_merkle_witness_bytes": synthetic_whir_transcript_merkle_witness_bytes(
                                scenario.transcript_plan,
                                MerkleProofMode::SeparatePaths,
                            ),
                        },
                        {
                            "merkle_proof_mode": merkle_mode_name(MerkleProofMode::MinimalSubtree),
                            "target_proof_bytes": whir_transcript_plan_for_merkle_mode(
                                scenario.transcript_plan,
                                WhirFoldMode::LocalInterpolant,
                                MerkleProofMode::MinimalSubtree,
                            )
                            .target_proof_bytes,
                            "synthetic_merkle_nodes": synthetic_whir_transcript_merkle_nodes(
                                scenario.transcript_plan,
                                MerkleProofMode::MinimalSubtree,
                            ),
                            "synthetic_merkle_witness_bytes": synthetic_whir_transcript_merkle_witness_bytes(
                                scenario.transcript_plan,
                                MerkleProofMode::MinimalSubtree,
                            ),
                        }
                    ],
                    "transcript_plan": {
                        "round_count": scenario.transcript_plan.round_count,
                        "initial_sumcheck_rounds": scenario.transcript_plan.initial_sumcheck_rounds,
                        "final_query_count": scenario.transcript_plan.final_query_count,
                        "final_sumcheck_rounds": scenario.transcript_plan.final_sumcheck_rounds,
                    }
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let mut validation = Vec::new();
    let mut diagnostics = Vec::new();
    let mut records = Vec::new();

    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        eprintln!("phase2: whir-multiproof scenario={}", scenario.seed.name);

        for merkle_mode in [
            MerkleProofMode::SeparatePaths,
            MerkleProofMode::MinimalSubtree,
        ] {
            let variant_name = merkle_mode_name(merkle_mode).to_string();
            let transcript_config = whir_transcript_config_for_merkle_mode(merkle_mode);
            let transcript_plan = whir_transcript_plan_for_merkle_mode(
                scenario.transcript_plan,
                transcript_config.whir_fold_mode,
                merkle_mode,
            );
            let transcript_proof = build_phase2_whir_transcript_proof_bytes(
                transcript_plan,
                transcript_config.whir_fold_mode,
                merkle_mode,
            );
            let transcript_layout = whir_transcript_layout(transcript_plan, merkle_mode)?;

            let valid_path =
                proofs_dir.join(format!("{}_{}_valid.bin", scenario.seed.name, variant_name));
            fs::write(&valid_path, &transcript_proof)?;
            let mut invalid_challenge = transcript_proof.clone();
            if transcript_layout.final_pow_nonce_offset < invalid_challenge.len() {
                invalid_challenge[transcript_layout.final_pow_nonce_offset] ^= 0x01;
            }
            let invalid_challenge_path = proofs_dir.join(format!(
                "{}_{}_invalid_challenge.bin",
                scenario.seed.name, variant_name
            ));
            fs::write(&invalid_challenge_path, &invalid_challenge)?;
            let mut invalid_missing_query = transcript_proof.clone();
            if transcript_layout.final_query_offset + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES
                <= invalid_missing_query.len()
            {
                invalid_missing_query.drain(
                    transcript_layout.final_query_offset
                        ..transcript_layout.final_query_offset + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES,
                );
            } else {
                invalid_missing_query.truncate(
                    invalid_missing_query
                        .len()
                        .saturating_sub(WHIR_TRANSCRIPT_FINAL_QUERY_BYTES),
                );
            }
            let invalid_missing_query_path = proofs_dir.join(format!(
                "{}_{}_invalid_missing_query.bin",
                scenario.seed.name, variant_name
            ));
            fs::write(&invalid_missing_query_path, &invalid_missing_query)?;
            let mut invalid_folding = transcript_proof.clone();
            if transcript_layout.final_sumcheck_offset < invalid_folding.len() {
                invalid_folding[transcript_layout.final_sumcheck_offset] ^= 0x08;
            }
            let invalid_folding_path = proofs_dir.join(format!(
                "{}_{}_invalid_folding.bin",
                scenario.seed.name, variant_name
            ));
            fs::write(&invalid_folding_path, &invalid_folding)?;
            let mut invalid_truncated = transcript_proof.clone();
            invalid_truncated.truncate(transcript_proof.len().saturating_sub(8));
            let invalid_truncated_path = proofs_dir.join(format!(
                "{}_{}_invalid_truncated.bin",
                scenario.seed.name, variant_name
            ));
            fs::write(&invalid_truncated_path, &invalid_truncated)?;

            let host_valid = run_phase2_whir_transcript_verify(
                transcript_config,
                &transcript_proof,
                config.whir_transcript_repeat_inside_instruction,
                WhirTranscriptTraceMode::Disabled,
            );
            let host_invalid_challenge = run_phase2_whir_transcript_verify(
                transcript_config,
                &invalid_challenge,
                config.whir_transcript_repeat_inside_instruction,
                WhirTranscriptTraceMode::Disabled,
            );
            let host_invalid_missing_query = run_phase2_whir_transcript_verify(
                transcript_config,
                &invalid_missing_query,
                config.whir_transcript_repeat_inside_instruction,
                WhirTranscriptTraceMode::Disabled,
            );
            let host_invalid_folding = run_phase2_whir_transcript_verify(
                transcript_config,
                &invalid_folding,
                config.whir_transcript_repeat_inside_instruction,
                WhirTranscriptTraceMode::Disabled,
            );
            let host_invalid_truncated = run_phase2_whir_transcript_verify(
                transcript_config,
                &invalid_truncated,
                config.whir_transcript_repeat_inside_instruction,
                WhirTranscriptTraceMode::Disabled,
            );
            validation.push(json!({
                "scenario_name": scenario.seed.name,
                "merkle_proof_mode": variant_name,
                "valid_proof": host_valid.is_ok(),
                "invalid_challenge_rejected": host_invalid_challenge.is_err(),
                "invalid_missing_query_rejected": host_invalid_missing_query.is_err(),
                "invalid_folding_rejected": host_invalid_folding.is_err(),
                "invalid_truncated_rejected": host_invalid_truncated.is_err(),
                "proofs": {
                    "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                    "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                    "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                    "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                    "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
                }
            }));
            if !host_valid.is_ok()
                || !host_invalid_challenge.is_err()
                || !host_invalid_missing_query.is_err()
                || !host_invalid_folding.is_err()
                || !host_invalid_truncated.is_err()
            {
                bail!(
                    "WHIR multiproof validation failed for {} {}: valid={:?}, invalid_challenge={:?}, invalid_missing_query={:?}, invalid_folding={:?}, invalid_truncated={:?}",
                    scenario.seed.name,
                    merkle_mode_name(merkle_mode),
                    host_valid.as_ref().map(|_| "ok").map_err(|err| *err),
                    host_invalid_challenge
                        .as_ref()
                        .map(|_| "ok")
                        .map_err(|err| *err),
                    host_invalid_missing_query
                        .as_ref()
                        .map(|_| "ok")
                        .map_err(|err| *err),
                    host_invalid_folding
                        .as_ref()
                        .map(|_| "ok")
                        .map_err(|err| *err),
                    host_invalid_truncated
                        .as_ref()
                        .map(|_| "ok")
                        .map_err(|err| *err),
                );
            }

            write_json(
                &manifests_dir.join(format!(
                    "{}_whir_multiproof_{}.json",
                    scenario.seed.name,
                    merkle_mode_name(merkle_mode)
                )),
                &json!({
                    "scenario_name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "config": verifier_config_json(transcript_config),
                    "base_target_proof_bytes": scenario.transcript_plan.target_proof_bytes,
                    "adjusted_target_proof_bytes": transcript_plan.target_proof_bytes,
                    "synthetic_merkle_nodes": {
                        "separate_paths": synthetic_whir_transcript_merkle_nodes(
                            scenario.transcript_plan,
                            MerkleProofMode::SeparatePaths,
                        ),
                        "selected_mode": synthetic_whir_transcript_merkle_nodes(
                            scenario.transcript_plan,
                            merkle_mode,
                        ),
                    },
                    "synthetic_merkle_witness_bytes": {
                        "separate_paths": synthetic_whir_transcript_merkle_witness_bytes(
                            scenario.transcript_plan,
                            MerkleProofMode::SeparatePaths,
                        ),
                        "selected_mode": synthetic_whir_transcript_merkle_witness_bytes(
                            scenario.transcript_plan,
                            merkle_mode,
                        ),
                    },
                    "statement_shape": phase2_whir_statement_shape_json(transcript_plan.statement_shape),
                    "transcript_plan": whir_transcript_plan_json(transcript_plan),
                    "proofs": {
                        "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                        "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                        "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                        "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                        "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
                    }
                }),
            )?;

            let host_start = Instant::now();
            let host_outcome = run_phase2_whir_transcript_verify(
                transcript_config,
                &transcript_proof,
                config.whir_transcript_repeat_inside_instruction,
                WhirTranscriptTraceMode::Disabled,
            )
            .map_err(|err| anyhow!(err))?;
            let host_elapsed_ns = host_start.elapsed().as_nanos();
            let (upload_account, _upload_records, upload_cu) = upload_bytes(
                &harness,
                &transcript_proof,
                config.upload_chunk_size,
                true,
                &format!("phase2/{}-multiproof-{}", scenario.seed.name, variant_name),
                config.upload_repetitions,
            )?;
            let upload_chunks = transcript_proof.len().div_ceil(config.upload_chunk_size) as u64;
            let projection = project_features(
                &format!("{}_multiproof_{}", scenario.seed.name, variant_name),
                &host_outcome.counters,
                transcript_proof.len() as u64,
                upload_chunks,
                config.upload_chunk_size,
                VERIFY_HEAP_FRAME_BYTES as u64,
            );

            records.push(WhirMultiproofMeasurement {
                scenario_name: scenario.seed.name.clone(),
                merkle_proof_mode: variant_name.clone(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "host_verify".to_string(),
                repetition: 0,
                actual_cu: None,
                elapsed_ns: Some(host_elapsed_ns),
                status: "ok".to_string(),
                error: None,
                counters: host_outcome.counters.into(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
            });
            records.push(WhirMultiproofMeasurement {
                scenario_name: scenario.seed.name.clone(),
                merkle_proof_mode: variant_name.clone(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: 0,
                heap_pages_32k: 0,
                stage: "upload_total".to_string(),
                repetition: 0,
                actual_cu: Some(upload_cu),
                elapsed_ns: None,
                status: "ok".to_string(),
                error: None,
                counters: CounterSummary::default(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
            });

            for repetition in 0..config.whir_transcript_verify_repetitions {
                let tx = simulate_plan(
                    &harness,
                    TxPlan {
                        instructions: vec![build_phase2_whir_transcript_instruction(
                            harness.program_id,
                            upload_account.pubkey(),
                            transcript_config,
                            1,
                            WhirTranscriptTraceMode::Disabled,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                let (status, error) = simulated_tx_status(&tx);
                let total_cu = tx.units_consumed.map(|value| value + upload_cu);
                records.push(WhirMultiproofMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    merkle_proof_mode: variant_name.clone(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "verify_sbf".to_string(),
                    repetition,
                    actual_cu: tx.units_consumed,
                    elapsed_ns: None,
                    status: status.clone(),
                    error: error.clone(),
                    counters: host_outcome.counters.into(),
                    field_mul_projection: projection.field_mul_projection,
                    extension_mul_projection: projection.extension_mul_projection,
                    field_inv_projection: projection.field_inv_projection,
                });
                records.push(WhirMultiproofMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    merkle_proof_mode: variant_name.clone(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "total_sbf".to_string(),
                    repetition,
                    actual_cu: total_cu,
                    elapsed_ns: None,
                    status,
                    error,
                    counters: host_outcome.counters.into(),
                    field_mul_projection: projection.field_mul_projection,
                    extension_mul_projection: projection.extension_mul_projection,
                    field_inv_projection: projection.field_inv_projection,
                });
            }

            for repetition in 0..config.whir_transcript_trace_repetitions {
                let tx = simulate_plan(
                    &harness,
                    TxPlan {
                        instructions: vec![build_phase2_whir_transcript_instruction(
                            harness.program_id,
                            upload_account.pubkey(),
                            transcript_config,
                            1,
                            WhirTranscriptTraceMode::Enabled,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                let (status, error) = simulated_tx_status(&tx);
                match parse_whir_transcript_phase_trace(&tx.logs) {
                    Ok(phase_costs) => {
                        for (phase, actual_cu) in phase_costs {
                            records.push(WhirMultiproofMeasurement {
                                scenario_name: scenario.seed.name.clone(),
                                merkle_proof_mode: variant_name.clone(),
                                security_target_bits: scenario.seed.security_target_bits,
                                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                                total_explicit_query_count: scenario.total_explicit_query_count,
                                round_query_counts: scenario.round_query_counts.clone(),
                                commitment_ood_samples: scenario.commitment_ood_samples,
                                proof_bytes: transcript_proof.len() as u64,
                                upload_chunk_size: config.upload_chunk_size,
                                upload_chunks,
                                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                heap_pages_32k: config
                                    .limits
                                    .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                stage: phase,
                                repetition,
                                actual_cu: Some(actual_cu),
                                elapsed_ns: None,
                                status: status.clone(),
                                error: error.clone(),
                                counters: CounterSummary::default(),
                                field_mul_projection: projection.field_mul_projection,
                                extension_mul_projection: projection.extension_mul_projection,
                                field_inv_projection: projection.field_inv_projection,
                            });
                        }
                    }
                    Err(parse_error) => {
                        let error = match error {
                            Some(existing) => {
                                Some(format!("{existing}; trace_parse={parse_error:#}"))
                            }
                            None => Some(format!("{parse_error:#}")),
                        };
                        records.push(WhirMultiproofMeasurement {
                            scenario_name: scenario.seed.name.clone(),
                            merkle_proof_mode: variant_name.clone(),
                            security_target_bits: scenario.seed.security_target_bits,
                            soundness_assumption: scenario.seed.soundness_assumption.clone(),
                            total_explicit_query_count: scenario.total_explicit_query_count,
                            round_query_counts: scenario.round_query_counts.clone(),
                            commitment_ood_samples: scenario.commitment_ood_samples,
                            proof_bytes: transcript_proof.len() as u64,
                            upload_chunk_size: config.upload_chunk_size,
                            upload_chunks,
                            heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                            heap_pages_32k: config
                                .limits
                                .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                            stage: "trace_incomplete".to_string(),
                            repetition,
                            actual_cu: tx.units_consumed,
                            elapsed_ns: None,
                            status,
                            error,
                            counters: CounterSummary::default(),
                            field_mul_projection: projection.field_mul_projection,
                            extension_mul_projection: projection.extension_mul_projection,
                            field_inv_projection: projection.field_inv_projection,
                        });
                    }
                }
            }

            let tx = simulate_plan(
                &harness,
                TxPlan {
                    instructions: vec![build_phase2_whir_transcript_instruction(
                        harness.program_id,
                        upload_account.pubkey(),
                        transcript_config,
                        1,
                        WhirTranscriptTraceMode::Disabled,
                    )],
                    compute_unit_limit: None,
                    heap_frame_bytes: None,
                },
            )?;
            let (status, error) = simulated_tx_status(&tx);
            let total_cu = tx.units_consumed.map(|value| value + upload_cu);
            diagnostics.push(json!({
                "scenario_name": scenario.seed.name.clone(),
                "merkle_proof_mode": variant_name.clone(),
                "stage": "verify_sbf_no_heap",
                "actual_cu": tx.units_consumed,
                "status": status.clone(),
                "error": error.clone(),
            }));
            records.push(WhirMultiproofMeasurement {
                scenario_name: scenario.seed.name.clone(),
                merkle_proof_mode: variant_name.clone(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: 0,
                heap_pages_32k: 0,
                stage: "verify_sbf_no_heap".to_string(),
                repetition: 0,
                actual_cu: tx.units_consumed,
                elapsed_ns: None,
                status: status.clone(),
                error: error.clone(),
                counters: host_outcome.counters.into(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
            });
            records.push(WhirMultiproofMeasurement {
                scenario_name: scenario.seed.name.clone(),
                merkle_proof_mode: variant_name.clone(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: 0,
                heap_pages_32k: 0,
                stage: "total_sbf_no_heap".to_string(),
                repetition: 0,
                actual_cu: total_cu,
                elapsed_ns: None,
                status,
                error,
                counters: host_outcome.counters.into(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
            });

            if scenario.seed.name == "whir_t128_johnson_full"
                && merkle_mode == MerkleProofMode::MinimalSubtree
            {
                let checkpoints = derive_phase2_whir_transcript_checkpoints(
                    transcript_plan,
                    transcript_config.whir_fold_mode,
                    merkle_mode,
                );
                for round_index in
                    0..usize::from(checkpoints.round_count.min(PHASE2_WHIR_MAX_ROUNDS as u16))
                {
                    let checkpoint = checkpoints.round_starts[round_index];
                    let host_segment = run_phase2_whir_transcript_segment_verify(
                        transcript_config,
                        &transcript_proof,
                        WhirTranscriptDiagnosticStage::Round,
                        round_index as u16,
                        checkpoint,
                        1,
                        WhirTranscriptTraceMode::Disabled,
                    )
                    .map_err(|err| anyhow!(err))?;
                    let segment_projection = project_features(
                        &format!(
                            "{}_{}_diagnostic_round_{}",
                            scenario.seed.name, variant_name, round_index
                        ),
                        &host_segment.counters,
                        transcript_proof.len() as u64,
                        upload_chunks,
                        config.upload_chunk_size,
                        VERIFY_HEAP_FRAME_BYTES as u64,
                    );
                    let tx = simulate_plan(
                        &harness,
                        TxPlan {
                            instructions: vec![build_phase2_whir_transcript_segment_instruction(
                                harness.program_id,
                                upload_account.pubkey(),
                                transcript_config,
                                WhirTranscriptDiagnosticStage::Round,
                                round_index as u16,
                                checkpoint,
                                1,
                                WhirTranscriptTraceMode::Disabled,
                            )],
                            compute_unit_limit: None,
                            heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                        },
                    )?;
                    let (status, error) = simulated_tx_status(&tx);
                    let stage = format!("diagnostic_round_{round_index}");
                    diagnostics.push(json!({
                        "scenario_name": scenario.seed.name.clone(),
                        "merkle_proof_mode": variant_name.clone(),
                        "stage": stage.clone(),
                        "round_index": round_index,
                        "checkpoint_claim": checkpoint.claim,
                        "checkpoint_transcript_state": checkpoint.transcript_state,
                        "actual_cu": tx.units_consumed,
                        "status": status.clone(),
                        "error": error.clone(),
                    }));
                    records.push(WhirMultiproofMeasurement {
                        scenario_name: scenario.seed.name.clone(),
                        merkle_proof_mode: variant_name.clone(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        total_explicit_query_count: scenario.total_explicit_query_count,
                        round_query_counts: scenario.round_query_counts.clone(),
                        commitment_ood_samples: scenario.commitment_ood_samples,
                        proof_bytes: transcript_proof.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage,
                        repetition: 0,
                        actual_cu: tx.units_consumed,
                        elapsed_ns: None,
                        status,
                        error,
                        counters: host_segment.counters.into(),
                        field_mul_projection: segment_projection.field_mul_projection,
                        extension_mul_projection: segment_projection.extension_mul_projection,
                        field_inv_projection: segment_projection.field_inv_projection,
                    });
                }

                let checkpoint = checkpoints.final_round;
                let host_segment = run_phase2_whir_transcript_segment_verify(
                    transcript_config,
                    &transcript_proof,
                    WhirTranscriptDiagnosticStage::FinalRound,
                    0,
                    checkpoint,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                )
                .map_err(|err| anyhow!(err))?;
                let segment_projection = project_features(
                    &format!(
                        "{}_{}_diagnostic_final_round",
                        scenario.seed.name, variant_name
                    ),
                    &host_segment.counters,
                    transcript_proof.len() as u64,
                    upload_chunks,
                    config.upload_chunk_size,
                    VERIFY_HEAP_FRAME_BYTES as u64,
                );
                let tx = simulate_plan(
                    &harness,
                    TxPlan {
                        instructions: vec![build_phase2_whir_transcript_segment_instruction(
                            harness.program_id,
                            upload_account.pubkey(),
                            transcript_config,
                            WhirTranscriptDiagnosticStage::FinalRound,
                            0,
                            checkpoint,
                            1,
                            WhirTranscriptTraceMode::Disabled,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                let (status, error) = simulated_tx_status(&tx);
                diagnostics.push(json!({
                    "scenario_name": scenario.seed.name.clone(),
                    "merkle_proof_mode": variant_name.clone(),
                    "stage": "diagnostic_final_round",
                    "checkpoint_claim": checkpoint.claim,
                    "checkpoint_transcript_state": checkpoint.transcript_state,
                    "actual_cu": tx.units_consumed,
                    "status": status.clone(),
                    "error": error.clone(),
                }));
                records.push(WhirMultiproofMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    merkle_proof_mode: variant_name.clone(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "diagnostic_final_round".to_string(),
                    repetition: 0,
                    actual_cu: tx.units_consumed,
                    elapsed_ns: None,
                    status,
                    error,
                    counters: host_segment.counters.into(),
                    field_mul_projection: segment_projection.field_mul_projection,
                    extension_mul_projection: segment_projection.extension_mul_projection,
                    field_inv_projection: segment_projection.field_inv_projection,
                });
            }
        }
    }

    write_json(&results_dir.join("validation.json"), &validation)?;
    write_json(&results_dir.join("diagnostics.json"), &diagnostics)?;
    Ok(records)
}

fn run_whir_round0_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    results_dir: &Path,
    manifests_dir: &Path,
) -> Result<Vec<WhirRound0Measurement>> {
    let scenarios = derive_whir_transcript_scenarios(config)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                let round0 = scenario.transcript_plan.rounds[0];
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "round_query_counts": scenario.round_query_counts,
                    "commitment_ood_samples": scenario.commitment_ood_samples,
                    "round0": {
                        "query_count": round0.query_count,
                        "merkle_depth": round0.merkle_depth,
                        "ood_samples": round0.ood_samples,
                        "selector_count": round0.selector_count,
                        "pow_bits": round0.pow_bits,
                        "sumcheck_rounds": round0.sumcheck_rounds,
                        "folding_pow_bits": round0.folding_pow_bits,
                    },
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let mut records = Vec::new();
    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        eprintln!("phase2: whir-round0 scenario={}", scenario.seed.name);

        for merkle_mode in [
            MerkleProofMode::SeparatePaths,
            MerkleProofMode::MinimalSubtree,
        ] {
            for fold_mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
                let verifier_config = whir_transcript_config_for_modes(fold_mode, merkle_mode);
                let transcript_plan = whir_transcript_plan_for_merkle_mode(
                    scenario.transcript_plan,
                    fold_mode,
                    merkle_mode,
                );
                let transcript_proof = build_phase2_whir_transcript_proof_bytes(
                    transcript_plan,
                    fold_mode,
                    merkle_mode,
                );
                let upload_label = format!(
                    "phase2/{}-round0-{}-{}",
                    scenario.seed.name,
                    fold_mode_name(fold_mode),
                    merkle_mode_name(merkle_mode),
                );
                let (upload_account, _upload_records, _upload_cu) = upload_bytes(
                    &harness,
                    &transcript_proof,
                    config.upload_chunk_size,
                    true,
                    &upload_label,
                    config.upload_repetitions,
                )?;
                let upload_chunks =
                    transcript_proof.len().div_ceil(config.upload_chunk_size) as u64;
                let checkpoints = derive_phase2_whir_transcript_checkpoints(
                    transcript_plan,
                    fold_mode,
                    merkle_mode,
                );
                if checkpoints.round_count == 0 {
                    bail!("round-0 checkpoints missing for {}", scenario.seed.name);
                }
                let checkpoint = checkpoints.round_starts[0];
                let round0 = transcript_plan.rounds[0];

                for (diagnostic_stage, round0_variant) in [
                    (WhirTranscriptDiagnosticStage::Round, "baseline_round0"),
                    (
                        WhirTranscriptDiagnosticStage::RoundReuse,
                        "round_reuse_batch_inverse",
                    ),
                ] {
                    write_json(
                        &manifests_dir.join(format!(
                            "{}_whir_round0_{}_{}_{}.json",
                            scenario.seed.name,
                            merkle_mode_name(merkle_mode),
                            fold_mode_name(fold_mode),
                            round0_variant
                        )),
                        &json!({
                            "scenario_name": scenario.seed.name,
                            "security_target_bits": scenario.seed.security_target_bits,
                            "soundness_assumption": scenario.seed.soundness_assumption,
                            "round0_variant": round0_variant,
                            "config": verifier_config_json(verifier_config),
                            "round_index": 0,
                            "round0": {
                                "query_count": round0.query_count,
                                "merkle_depth": round0.merkle_depth,
                                "ood_samples": round0.ood_samples,
                                "selector_count": round0.selector_count,
                                "pow_bits": round0.pow_bits,
                                "sumcheck_rounds": round0.sumcheck_rounds,
                                "folding_pow_bits": round0.folding_pow_bits,
                            },
                            "checkpoint": {
                                "claim": checkpoint.claim,
                                "transcript_state": checkpoint.transcript_state,
                            },
                            "statement_shape": phase2_whir_statement_shape_json(transcript_plan.statement_shape),
                            "transcript_plan": whir_transcript_plan_json(transcript_plan),
                        }),
                    )?;

                    let host_start = Instant::now();
                    let host_outcome = run_phase2_whir_transcript_segment_verify(
                        verifier_config,
                        &transcript_proof,
                        diagnostic_stage,
                        0,
                        checkpoint,
                        1,
                        WhirTranscriptTraceMode::Disabled,
                    )
                    .map_err(|err| anyhow!(err))?;
                    let host_elapsed_ns = host_start.elapsed().as_nanos();
                    let projection = project_features(
                        &format!(
                            "{}_{}_{}_{}",
                            scenario.seed.name,
                            fold_mode_name(fold_mode),
                            merkle_mode_name(merkle_mode),
                            round0_variant,
                        ),
                        &host_outcome.counters,
                        transcript_proof.len() as u64,
                        upload_chunks,
                        config.upload_chunk_size,
                        VERIFY_HEAP_FRAME_BYTES as u64,
                    );

                    records.push(WhirRound0Measurement {
                        scenario_name: scenario.seed.name.clone(),
                        round0_variant: round0_variant.to_string(),
                        whir_fold_mode: fold_mode_name(fold_mode).to_string(),
                        merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        round_index: 0,
                        round_query_count: u64::from(round0.query_count),
                        round_merkle_depth: u64::from(round0.merkle_depth),
                        round_ood_samples: u64::from(round0.ood_samples),
                        round_selector_count: u64::from(round0.selector_count),
                        round_pow_bits: u64::from(round0.pow_bits),
                        round_sumcheck_rounds: u64::from(round0.sumcheck_rounds),
                        round_folding_pow_bits: u64::from(round0.folding_pow_bits),
                        proof_bytes: transcript_proof.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage: "host_verify".to_string(),
                        repetition: 0,
                        actual_cu: None,
                        elapsed_ns: Some(host_elapsed_ns),
                        status: "ok".to_string(),
                        error: None,
                        counters: host_outcome.counters.into(),
                        field_mul_projection: projection.field_mul_projection,
                        extension_mul_projection: projection.extension_mul_projection,
                        field_inv_projection: projection.field_inv_projection,
                    });

                    for repetition in 0..config.whir_transcript_verify_repetitions {
                        let tx = simulate_plan(
                            &harness,
                            TxPlan {
                                instructions: vec![
                                    build_phase2_whir_transcript_segment_instruction(
                                        harness.program_id,
                                        upload_account.pubkey(),
                                        verifier_config,
                                        diagnostic_stage,
                                        0,
                                        checkpoint,
                                        1,
                                        WhirTranscriptTraceMode::Disabled,
                                    ),
                                ],
                                compute_unit_limit: None,
                                heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                            },
                        )?;
                        let (status, error) = simulated_tx_status(&tx);
                        records.push(WhirRound0Measurement {
                            scenario_name: scenario.seed.name.clone(),
                            round0_variant: round0_variant.to_string(),
                            whir_fold_mode: fold_mode_name(fold_mode).to_string(),
                            merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                            security_target_bits: scenario.seed.security_target_bits,
                            soundness_assumption: scenario.seed.soundness_assumption.clone(),
                            round_index: 0,
                            round_query_count: u64::from(round0.query_count),
                            round_merkle_depth: u64::from(round0.merkle_depth),
                            round_ood_samples: u64::from(round0.ood_samples),
                            round_selector_count: u64::from(round0.selector_count),
                            round_pow_bits: u64::from(round0.pow_bits),
                            round_sumcheck_rounds: u64::from(round0.sumcheck_rounds),
                            round_folding_pow_bits: u64::from(round0.folding_pow_bits),
                            proof_bytes: transcript_proof.len() as u64,
                            upload_chunk_size: config.upload_chunk_size,
                            upload_chunks,
                            heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                            heap_pages_32k: config
                                .limits
                                .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                            stage: "verify_sbf".to_string(),
                            repetition,
                            actual_cu: tx.units_consumed,
                            elapsed_ns: None,
                            status,
                            error,
                            counters: host_outcome.counters.into(),
                            field_mul_projection: projection.field_mul_projection,
                            extension_mul_projection: projection.extension_mul_projection,
                            field_inv_projection: projection.field_inv_projection,
                        });
                    }

                    for repetition in 0..config.whir_transcript_trace_repetitions {
                        let tx = simulate_plan(
                            &harness,
                            TxPlan {
                                instructions: vec![
                                    build_phase2_whir_transcript_segment_instruction(
                                        harness.program_id,
                                        upload_account.pubkey(),
                                        verifier_config,
                                        diagnostic_stage,
                                        0,
                                        checkpoint,
                                        1,
                                        WhirTranscriptTraceMode::Enabled,
                                    ),
                                ],
                                compute_unit_limit: None,
                                heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                            },
                        )?;
                        let (status, error) = simulated_tx_status(&tx);
                        match parse_whir_transcript_phase_trace(&tx.logs) {
                            Ok(phase_costs) => {
                                for (stage, actual_cu) in phase_costs {
                                    records.push(WhirRound0Measurement {
                                        scenario_name: scenario.seed.name.clone(),
                                        round0_variant: round0_variant.to_string(),
                                        whir_fold_mode: fold_mode_name(fold_mode).to_string(),
                                        merkle_proof_mode: merkle_mode_name(merkle_mode)
                                            .to_string(),
                                        security_target_bits: scenario.seed.security_target_bits,
                                        soundness_assumption: scenario
                                            .seed
                                            .soundness_assumption
                                            .clone(),
                                        round_index: 0,
                                        round_query_count: u64::from(round0.query_count),
                                        round_merkle_depth: u64::from(round0.merkle_depth),
                                        round_ood_samples: u64::from(round0.ood_samples),
                                        round_selector_count: u64::from(round0.selector_count),
                                        round_pow_bits: u64::from(round0.pow_bits),
                                        round_sumcheck_rounds: u64::from(round0.sumcheck_rounds),
                                        round_folding_pow_bits: u64::from(round0.folding_pow_bits),
                                        proof_bytes: transcript_proof.len() as u64,
                                        upload_chunk_size: config.upload_chunk_size,
                                        upload_chunks,
                                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                        heap_pages_32k: config
                                            .limits
                                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                        stage,
                                        repetition,
                                        actual_cu: Some(actual_cu),
                                        elapsed_ns: None,
                                        status: status.clone(),
                                        error: error.clone(),
                                        counters: CounterSummary::default(),
                                        field_mul_projection: projection.field_mul_projection,
                                        extension_mul_projection: projection
                                            .extension_mul_projection,
                                        field_inv_projection: projection.field_inv_projection,
                                    });
                                }
                            }
                            Err(parse_error) => {
                                let error = match error {
                                    Some(existing) => {
                                        Some(format!("{existing}; trace_parse={parse_error:#}"))
                                    }
                                    None => Some(format!("{parse_error:#}")),
                                };
                                records.push(WhirRound0Measurement {
                                    scenario_name: scenario.seed.name.clone(),
                                    round0_variant: round0_variant.to_string(),
                                    whir_fold_mode: fold_mode_name(fold_mode).to_string(),
                                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                                    security_target_bits: scenario.seed.security_target_bits,
                                    soundness_assumption: scenario
                                        .seed
                                        .soundness_assumption
                                        .clone(),
                                    round_index: 0,
                                    round_query_count: u64::from(round0.query_count),
                                    round_merkle_depth: u64::from(round0.merkle_depth),
                                    round_ood_samples: u64::from(round0.ood_samples),
                                    round_selector_count: u64::from(round0.selector_count),
                                    round_pow_bits: u64::from(round0.pow_bits),
                                    round_sumcheck_rounds: u64::from(round0.sumcheck_rounds),
                                    round_folding_pow_bits: u64::from(round0.folding_pow_bits),
                                    proof_bytes: transcript_proof.len() as u64,
                                    upload_chunk_size: config.upload_chunk_size,
                                    upload_chunks,
                                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                    heap_pages_32k: config
                                        .limits
                                        .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                    stage: "trace_incomplete".to_string(),
                                    repetition,
                                    actual_cu: tx.units_consumed,
                                    elapsed_ns: None,
                                    status,
                                    error,
                                    counters: CounterSummary::default(),
                                    field_mul_projection: projection.field_mul_projection,
                                    extension_mul_projection: projection.extension_mul_projection,
                                    field_inv_projection: projection.field_inv_projection,
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(records)
}

fn run_whir_multiproof_payload_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    results_dir: &Path,
    manifests_dir: &Path,
) -> Result<Vec<WhirMultiproofPayloadMeasurement>> {
    let scenarios = derive_whir_transcript_scenarios(config)?;
    let payloads_dir = results_dir.join("payloads");
    fs::create_dir_all(&payloads_dir)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "round_query_counts": scenario.round_query_counts,
                    "commitment_ood_samples": scenario.commitment_ood_samples,
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let mut validation = Vec::new();
    let mut records = Vec::new();

    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        eprintln!(
            "phase2: whir-multiproof-payload scenario={}",
            scenario.seed.name
        );

        for merkle_mode in [
            MerkleProofMode::SeparatePaths,
            MerkleProofMode::MinimalSubtree,
        ] {
            let parser_config = whir_transcript_config_for_merkle_mode(merkle_mode);
            let transcript_plan = whir_transcript_plan_for_merkle_mode(
                scenario.transcript_plan,
                parser_config.whir_fold_mode,
                merkle_mode,
            );
            let mode_name = merkle_mode_name(merkle_mode).to_string();

            for payload_format in [
                WhirMerklePayloadFormat::FlatNodes,
                WhirMerklePayloadFormat::CanonicalPayload,
            ] {
                let payload_name = merkle_payload_format_name(payload_format).to_string();
                let payload = build_phase2_whir_merkle_payload_bytes(
                    transcript_plan,
                    merkle_mode,
                    payload_format,
                );
                let payload_path = payloads_dir.join(format!(
                    "{}_{}_{}.bin",
                    scenario.seed.name, mode_name, payload_name
                ));
                fs::write(&payload_path, &payload)?;

                let host_valid = run_phase2_whir_merkle_payload_parse(
                    parser_config,
                    transcript_plan,
                    &payload,
                    payload_format,
                    1,
                );
                let mut invalid = payload.clone();
                match payload_format {
                    WhirMerklePayloadFormat::FlatNodes => {
                        invalid.truncate(invalid.len().saturating_sub(1));
                    }
                    WhirMerklePayloadFormat::CanonicalPayload => {
                        if !invalid.is_empty() {
                            invalid[0] ^= 0x01;
                        }
                    }
                }
                let invalid_path = payloads_dir.join(format!(
                    "{}_{}_{}_invalid.bin",
                    scenario.seed.name, mode_name, payload_name
                ));
                fs::write(&invalid_path, &invalid)?;
                let host_invalid = run_phase2_whir_merkle_payload_parse(
                    parser_config,
                    transcript_plan,
                    &invalid,
                    payload_format,
                    1,
                );
                validation.push(json!({
                    "scenario_name": scenario.seed.name,
                    "merkle_proof_mode": mode_name,
                    "payload_format": payload_name,
                    "valid_payload": host_valid.is_ok(),
                    "invalid_payload_rejected": host_invalid.is_err(),
                    "payloads": {
                        "valid": payload_path.strip_prefix(root).unwrap_or(&payload_path).display().to_string(),
                        "invalid": invalid_path.strip_prefix(root).unwrap_or(&invalid_path).display().to_string(),
                    }
                }));
                if !host_valid.is_ok() || !host_invalid.is_err() {
                    bail!(
                        "WHIR multiproof payload validation failed for {} {} {}",
                        scenario.seed.name,
                        mode_name,
                        payload_name,
                    );
                }

                write_json(
                    &manifests_dir.join(format!(
                        "{}_whir_multiproof_payload_{}_{}.json",
                        scenario.seed.name, mode_name, payload_name
                    )),
                    &json!({
                        "scenario_name": scenario.seed.name,
                        "security_target_bits": scenario.seed.security_target_bits,
                        "soundness_assumption": scenario.seed.soundness_assumption,
                        "config": verifier_config_json(parser_config),
                        "payload_format": payload_name,
                        "payload_bytes": payload.len(),
                        "transcript_plan": whir_transcript_plan_json(transcript_plan),
                        "payloads": {
                            "valid": payload_path.strip_prefix(root).unwrap_or(&payload_path).display().to_string(),
                            "invalid": invalid_path.strip_prefix(root).unwrap_or(&invalid_path).display().to_string(),
                        }
                    }),
                )?;

                let host_start = Instant::now();
                let host_outcome = run_phase2_whir_merkle_payload_parse(
                    parser_config,
                    transcript_plan,
                    &payload,
                    payload_format,
                    1,
                )
                .map_err(|err| anyhow!(err))?;
                let host_elapsed_ns = host_start.elapsed().as_nanos();
                let (upload_account, _upload_records, upload_cu) = upload_bytes(
                    &harness,
                    &payload,
                    config.upload_chunk_size,
                    true,
                    &format!(
                        "phase2/{}-multiproof-payload-{}-{}",
                        scenario.seed.name, mode_name, payload_name
                    ),
                    config.upload_repetitions,
                )?;
                let upload_chunks = payload.len().div_ceil(config.upload_chunk_size) as u64;

                records.push(WhirMultiproofPayloadMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    merkle_proof_mode: mode_name.clone(),
                    payload_format: payload_name.clone(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    payload_bytes: payload.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "host_parse".to_string(),
                    repetition: 0,
                    actual_cu: None,
                    elapsed_ns: Some(host_elapsed_ns),
                    status: "ok".to_string(),
                    error: None,
                    counters: host_outcome.counters.into(),
                });
                records.push(WhirMultiproofPayloadMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    merkle_proof_mode: mode_name.clone(),
                    payload_format: payload_name.clone(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    payload_bytes: payload.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: 0,
                    heap_pages_32k: 0,
                    stage: "upload_total".to_string(),
                    repetition: 0,
                    actual_cu: Some(upload_cu),
                    elapsed_ns: None,
                    status: "ok".to_string(),
                    error: None,
                    counters: CounterSummary::default(),
                });

                for repetition in 0..config.whir_transcript_verify_repetitions {
                    let tx = simulate_plan(
                        &harness,
                        TxPlan {
                            instructions: vec![build_phase2_whir_merkle_payload_instruction(
                                harness.program_id,
                                upload_account.pubkey(),
                                parser_config,
                                transcript_plan,
                                payload_format,
                                1,
                            )],
                            compute_unit_limit: None,
                            heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                        },
                    )?;
                    let (status, error) = simulated_tx_status(&tx);
                    let total_cu = tx.units_consumed.map(|value| value + upload_cu);
                    records.push(WhirMultiproofPayloadMeasurement {
                        scenario_name: scenario.seed.name.clone(),
                        merkle_proof_mode: mode_name.clone(),
                        payload_format: payload_name.clone(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        total_explicit_query_count: scenario.total_explicit_query_count,
                        round_query_counts: scenario.round_query_counts.clone(),
                        commitment_ood_samples: scenario.commitment_ood_samples,
                        payload_bytes: payload.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage: "parse_sbf".to_string(),
                        repetition,
                        actual_cu: tx.units_consumed,
                        elapsed_ns: None,
                        status: status.clone(),
                        error: error.clone(),
                        counters: host_outcome.counters.into(),
                    });
                    records.push(WhirMultiproofPayloadMeasurement {
                        scenario_name: scenario.seed.name.clone(),
                        merkle_proof_mode: mode_name.clone(),
                        payload_format: payload_name.clone(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        total_explicit_query_count: scenario.total_explicit_query_count,
                        round_query_counts: scenario.round_query_counts.clone(),
                        commitment_ood_samples: scenario.commitment_ood_samples,
                        payload_bytes: payload.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage: "total_sbf".to_string(),
                        repetition,
                        actual_cu: total_cu,
                        elapsed_ns: None,
                        status,
                        error,
                        counters: host_outcome.counters.into(),
                    });
                }
            }
        }
    }

    write_json(&results_dir.join("validation.json"), &validation)?;
    Ok(records)
}

fn run_whir_fold_payload_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    results_dir: &Path,
    manifests_dir: &Path,
) -> Result<Vec<WhirFoldPayloadMeasurement>> {
    let scenarios = derive_whir_transcript_scenarios(config)?;
    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&proofs_dir)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "round_query_counts": scenario.round_query_counts,
                    "commitment_ood_samples": scenario.commitment_ood_samples,
                    "merkle_proof_mode": merkle_mode_name(MerkleProofMode::MinimalSubtree),
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let mut validation = Vec::new();
    let mut records = Vec::new();
    let merkle_mode = MerkleProofMode::MinimalSubtree;

    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        eprintln!("phase2: whir-fold-payload scenario={}", scenario.seed.name);

        for fold_mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
            let mut transcript_config = whir_transcript_config_for_merkle_mode(merkle_mode);
            transcript_config.whir_fold_mode = fold_mode;
            let transcript_plan = whir_transcript_plan_for_merkle_mode(
                scenario.transcript_plan,
                fold_mode,
                merkle_mode,
            );
            let transcript_proof =
                build_phase2_whir_transcript_proof_bytes(transcript_plan, fold_mode, merkle_mode);
            let transcript_layout = whir_transcript_layout(transcript_plan, merkle_mode)?;
            let fold_name = fold_mode_name(fold_mode).to_string();

            let valid_path =
                proofs_dir.join(format!("{}_{}_valid.bin", scenario.seed.name, fold_name));
            fs::write(&valid_path, &transcript_proof)?;
            let mut invalid = transcript_proof.clone();
            if transcript_layout.final_sumcheck_offset < invalid.len() {
                invalid[transcript_layout.final_sumcheck_offset] ^= 0x08;
            }
            let invalid_path =
                proofs_dir.join(format!("{}_{}_invalid.bin", scenario.seed.name, fold_name));
            fs::write(&invalid_path, &invalid)?;
            let host_valid = run_phase2_whir_transcript_verify(
                transcript_config,
                &transcript_proof,
                1,
                WhirTranscriptTraceMode::Disabled,
            );
            let host_invalid = run_phase2_whir_transcript_verify(
                transcript_config,
                &invalid,
                1,
                WhirTranscriptTraceMode::Disabled,
            );
            validation.push(json!({
                "scenario_name": scenario.seed.name,
                "whir_fold_mode": fold_name,
                "valid_proof": host_valid.is_ok(),
                "invalid_proof_rejected": host_invalid.is_err(),
                "proofs": {
                    "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                    "invalid": invalid_path.strip_prefix(root).unwrap_or(&invalid_path).display().to_string(),
                }
            }));
            if !host_valid.is_ok() || !host_invalid.is_err() {
                bail!(
                    "WHIR fold payload validation failed for {} {}",
                    scenario.seed.name,
                    fold_name,
                );
            }

            write_json(
                &manifests_dir.join(format!(
                    "{}_whir_fold_payload_{}.json",
                    scenario.seed.name, fold_name
                )),
                &json!({
                    "scenario_name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "config": verifier_config_json(transcript_config),
                    "transcript_plan": whir_transcript_plan_json(transcript_plan),
                    "proofs": {
                        "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                        "invalid": invalid_path.strip_prefix(root).unwrap_or(&invalid_path).display().to_string(),
                    }
                }),
            )?;

            let host_start = Instant::now();
            let host_outcome = run_phase2_whir_transcript_verify(
                transcript_config,
                &transcript_proof,
                1,
                WhirTranscriptTraceMode::Disabled,
            )
            .map_err(|err| anyhow!(err))?;
            let host_elapsed_ns = host_start.elapsed().as_nanos();
            let (upload_account, _upload_records, upload_cu) = upload_bytes(
                &harness,
                &transcript_proof,
                config.upload_chunk_size,
                true,
                &format!("phase2/{}-fold-{}", scenario.seed.name, fold_name),
                config.upload_repetitions,
            )?;
            let upload_chunks = transcript_proof.len().div_ceil(config.upload_chunk_size) as u64;
            let projection = project_features(
                &format!("{}_fold_{}", scenario.seed.name, fold_name),
                &host_outcome.counters,
                transcript_proof.len() as u64,
                upload_chunks,
                config.upload_chunk_size,
                VERIFY_HEAP_FRAME_BYTES as u64,
            );

            records.push(WhirFoldPayloadMeasurement {
                scenario_name: scenario.seed.name.clone(),
                whir_fold_mode: fold_name.clone(),
                merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "host_verify".to_string(),
                repetition: 0,
                actual_cu: None,
                elapsed_ns: Some(host_elapsed_ns),
                status: "ok".to_string(),
                error: None,
                counters: host_outcome.counters.into(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
            });
            records.push(WhirFoldPayloadMeasurement {
                scenario_name: scenario.seed.name.clone(),
                whir_fold_mode: fold_name.clone(),
                merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: transcript_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks,
                heap_frame_bytes_requested: 0,
                heap_pages_32k: 0,
                stage: "upload_total".to_string(),
                repetition: 0,
                actual_cu: Some(upload_cu),
                elapsed_ns: None,
                status: "ok".to_string(),
                error: None,
                counters: CounterSummary::default(),
                field_mul_projection: projection.field_mul_projection,
                extension_mul_projection: projection.extension_mul_projection,
                field_inv_projection: projection.field_inv_projection,
            });

            for repetition in 0..config.whir_transcript_verify_repetitions {
                let tx = simulate_plan(
                    &harness,
                    TxPlan {
                        instructions: vec![build_phase2_whir_transcript_instruction(
                            harness.program_id,
                            upload_account.pubkey(),
                            transcript_config,
                            1,
                            WhirTranscriptTraceMode::Disabled,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                let (status, error) = simulated_tx_status(&tx);
                let total_cu = tx.units_consumed.map(|value| value + upload_cu);
                records.push(WhirFoldPayloadMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    whir_fold_mode: fold_name.clone(),
                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "verify_sbf".to_string(),
                    repetition,
                    actual_cu: tx.units_consumed,
                    elapsed_ns: None,
                    status: status.clone(),
                    error: error.clone(),
                    counters: host_outcome.counters.into(),
                    field_mul_projection: projection.field_mul_projection,
                    extension_mul_projection: projection.extension_mul_projection,
                    field_inv_projection: projection.field_inv_projection,
                });
                records.push(WhirFoldPayloadMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    whir_fold_mode: fold_name.clone(),
                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "total_sbf".to_string(),
                    repetition,
                    actual_cu: total_cu,
                    elapsed_ns: None,
                    status,
                    error,
                    counters: host_outcome.counters.into(),
                    field_mul_projection: projection.field_mul_projection,
                    extension_mul_projection: projection.extension_mul_projection,
                    field_inv_projection: projection.field_inv_projection,
                });
            }

            for repetition in 0..config.whir_transcript_trace_repetitions {
                let tx = simulate_plan(
                    &harness,
                    TxPlan {
                        instructions: vec![build_phase2_whir_transcript_instruction(
                            harness.program_id,
                            upload_account.pubkey(),
                            transcript_config,
                            1,
                            WhirTranscriptTraceMode::Enabled,
                        )],
                        compute_unit_limit: None,
                        heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                    },
                )?;
                let (status, error) = simulated_tx_status(&tx);
                match parse_whir_transcript_phase_trace(&tx.logs) {
                    Ok(phase_costs) => {
                        for (phase, actual_cu) in phase_costs {
                            records.push(WhirFoldPayloadMeasurement {
                                scenario_name: scenario.seed.name.clone(),
                                whir_fold_mode: fold_name.clone(),
                                merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                                security_target_bits: scenario.seed.security_target_bits,
                                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                                total_explicit_query_count: scenario.total_explicit_query_count,
                                round_query_counts: scenario.round_query_counts.clone(),
                                commitment_ood_samples: scenario.commitment_ood_samples,
                                proof_bytes: transcript_proof.len() as u64,
                                upload_chunk_size: config.upload_chunk_size,
                                upload_chunks,
                                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                heap_pages_32k: config
                                    .limits
                                    .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                stage: phase,
                                repetition,
                                actual_cu: Some(actual_cu),
                                elapsed_ns: None,
                                status: status.clone(),
                                error: error.clone(),
                                counters: CounterSummary::default(),
                                field_mul_projection: projection.field_mul_projection,
                                extension_mul_projection: projection.extension_mul_projection,
                                field_inv_projection: projection.field_inv_projection,
                            });
                        }
                    }
                    Err(parse_error) => {
                        records.push(WhirFoldPayloadMeasurement {
                            scenario_name: scenario.seed.name.clone(),
                            whir_fold_mode: fold_name.clone(),
                            merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                            security_target_bits: scenario.seed.security_target_bits,
                            soundness_assumption: scenario.seed.soundness_assumption.clone(),
                            total_explicit_query_count: scenario.total_explicit_query_count,
                            round_query_counts: scenario.round_query_counts.clone(),
                            commitment_ood_samples: scenario.commitment_ood_samples,
                            proof_bytes: transcript_proof.len() as u64,
                            upload_chunk_size: config.upload_chunk_size,
                            upload_chunks,
                            heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                            heap_pages_32k: config
                                .limits
                                .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                            stage: "trace_incomplete".to_string(),
                            repetition,
                            actual_cu: tx.units_consumed,
                            elapsed_ns: None,
                            status,
                            error: Some(match error {
                                Some(existing) => {
                                    format!("{existing}; trace_parse={parse_error:#}")
                                }
                                None => format!("{parse_error:#}"),
                            }),
                            counters: CounterSummary::default(),
                            field_mul_projection: projection.field_mul_projection,
                            extension_mul_projection: projection.extension_mul_projection,
                            field_inv_projection: projection.field_inv_projection,
                        });
                    }
                }
            }
        }
    }

    write_json(&results_dir.join("validation.json"), &validation)?;
    Ok(records)
}

fn run_whir_full_reuse_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    results_dir: &Path,
    manifests_dir: &Path,
) -> Result<Vec<WhirFullReuseMeasurement>> {
    let scenarios = derive_whir_transcript_scenarios(config)?
        .into_iter()
        .filter(|scenario| {
            matches!(
                scenario.seed.name.as_str(),
                "whir_t128_capacity_full" | "whir_t100_johnson_full"
            )
        })
        .collect::<Vec<_>>();
    if scenarios.is_empty() {
        bail!("no targeted WHIR transcript reuse scenarios were derived");
    }

    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&proofs_dir)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "round_query_counts": scenario.round_query_counts,
                    "commitment_ood_samples": scenario.commitment_ood_samples,
                    "merkle_proof_mode": merkle_mode_name(MerkleProofMode::MinimalSubtree),
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let query_only_config = whir_query_baseline_config();
    let merkle_mode = MerkleProofMode::MinimalSubtree;
    let mut validation = Vec::new();
    let mut trace_diagnostics = Vec::new();
    let mut records = Vec::new();

    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        eprintln!("phase2: whir-full-reuse scenario={}", scenario.seed.name);

        let query_only_proof = build_phase2_whir_query_proof_bytes(
            scenario.query_plan,
            query_only_config.whir_fold_mode,
        );
        let query_host_start = Instant::now();
        let query_host_outcome =
            run_phase2_whir_query_verify(query_only_config, &query_only_proof, 1)
                .map_err(|err| anyhow!(err))?;
        let query_host_elapsed_ns = query_host_start.elapsed().as_nanos();
        let (query_upload_account, _query_upload_records, query_upload_cu) = upload_bytes(
            &harness,
            &query_only_proof,
            config.upload_chunk_size,
            true,
            &format!("phase2/{}-query-only-full-reuse", scenario.seed.name),
            config.upload_repetitions,
        )?;
        let query_upload_chunks = query_only_proof.len().div_ceil(config.upload_chunk_size) as u64;
        let query_projection = project_features(
            &format!("{}_query_only_full_reuse", scenario.seed.name),
            &query_host_outcome.counters,
            query_only_proof.len() as u64,
            query_upload_chunks,
            config.upload_chunk_size,
            VERIFY_HEAP_FRAME_BYTES as u64,
        );

        records.push(WhirFullReuseMeasurement {
            scenario_name: scenario.seed.name.clone(),
            path_variant: "query_only".to_string(),
            whir_fold_mode: fold_mode_name(query_only_config.whir_fold_mode).to_string(),
            merkle_proof_mode: "not_applicable".to_string(),
            query_reuse_mode: "not_applicable".to_string(),
            query_precompute_mode: "not_applicable".to_string(),
            security_target_bits: scenario.seed.security_target_bits,
            soundness_assumption: scenario.seed.soundness_assumption.clone(),
            total_explicit_query_count: scenario.total_explicit_query_count,
            round_query_counts: scenario.round_query_counts.clone(),
            commitment_ood_samples: scenario.commitment_ood_samples,
            proof_bytes: query_only_proof.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks: query_upload_chunks,
            heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
            heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
            stage: "host_verify".to_string(),
            repetition: 0,
            actual_cu: None,
            elapsed_ns: Some(query_host_elapsed_ns),
            status: "ok".to_string(),
            error: None,
            counters: query_host_outcome.counters.into(),
            field_mul_projection: query_projection.field_mul_projection,
            extension_mul_projection: query_projection.extension_mul_projection,
            field_inv_projection: query_projection.field_inv_projection,
        });
        records.push(WhirFullReuseMeasurement {
            scenario_name: scenario.seed.name.clone(),
            path_variant: "query_only".to_string(),
            whir_fold_mode: fold_mode_name(query_only_config.whir_fold_mode).to_string(),
            merkle_proof_mode: "not_applicable".to_string(),
            query_reuse_mode: "not_applicable".to_string(),
            query_precompute_mode: "not_applicable".to_string(),
            security_target_bits: scenario.seed.security_target_bits,
            soundness_assumption: scenario.seed.soundness_assumption.clone(),
            total_explicit_query_count: scenario.total_explicit_query_count,
            round_query_counts: scenario.round_query_counts.clone(),
            commitment_ood_samples: scenario.commitment_ood_samples,
            proof_bytes: query_only_proof.len() as u64,
            upload_chunk_size: config.upload_chunk_size,
            upload_chunks: query_upload_chunks,
            heap_frame_bytes_requested: 0,
            heap_pages_32k: 0,
            stage: "upload_total".to_string(),
            repetition: 0,
            actual_cu: Some(query_upload_cu),
            elapsed_ns: None,
            status: "ok".to_string(),
            error: None,
            counters: CounterSummary::default(),
            field_mul_projection: query_projection.field_mul_projection,
            extension_mul_projection: query_projection.extension_mul_projection,
            field_inv_projection: query_projection.field_inv_projection,
        });
        for repetition in 0..config.whir_transcript_verify_repetitions {
            let tx = simulate_plan(
                &harness,
                TxPlan {
                    instructions: vec![build_phase2_whir_query_instruction(
                        harness.program_id,
                        query_upload_account.pubkey(),
                        query_only_config,
                        1,
                    )],
                    compute_unit_limit: None,
                    heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                },
            )?;
            let (status, error) = simulated_tx_status(&tx);
            let total_cu = tx.units_consumed.map(|value| value + query_upload_cu);
            records.push(WhirFullReuseMeasurement {
                scenario_name: scenario.seed.name.clone(),
                path_variant: "query_only".to_string(),
                whir_fold_mode: fold_mode_name(query_only_config.whir_fold_mode).to_string(),
                merkle_proof_mode: "not_applicable".to_string(),
                query_reuse_mode: "not_applicable".to_string(),
                query_precompute_mode: "not_applicable".to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: query_only_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks: query_upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "verify_sbf".to_string(),
                repetition,
                actual_cu: tx.units_consumed,
                elapsed_ns: None,
                status: status.clone(),
                error: error.clone(),
                counters: query_host_outcome.counters.into(),
                field_mul_projection: query_projection.field_mul_projection,
                extension_mul_projection: query_projection.extension_mul_projection,
                field_inv_projection: query_projection.field_inv_projection,
            });
            records.push(WhirFullReuseMeasurement {
                scenario_name: scenario.seed.name.clone(),
                path_variant: "query_only".to_string(),
                whir_fold_mode: fold_mode_name(query_only_config.whir_fold_mode).to_string(),
                merkle_proof_mode: "not_applicable".to_string(),
                query_reuse_mode: "not_applicable".to_string(),
                query_precompute_mode: "not_applicable".to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                round_query_counts: scenario.round_query_counts.clone(),
                commitment_ood_samples: scenario.commitment_ood_samples,
                proof_bytes: query_only_proof.len() as u64,
                upload_chunk_size: config.upload_chunk_size,
                upload_chunks: query_upload_chunks,
                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                stage: "total_sbf".to_string(),
                repetition,
                actual_cu: total_cu,
                elapsed_ns: None,
                status,
                error,
                counters: query_host_outcome.counters.into(),
                field_mul_projection: query_projection.field_mul_projection,
                extension_mul_projection: query_projection.extension_mul_projection,
                field_inv_projection: query_projection.field_inv_projection,
            });
        }

        for fold_mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
            let fold_name = fold_mode_name(fold_mode).to_string();
            let transcript_plan = whir_transcript_plan_for_merkle_mode(
                scenario.transcript_plan,
                fold_mode,
                merkle_mode,
            );
            let transcript_proof =
                build_phase2_whir_transcript_proof_bytes(transcript_plan, fold_mode, merkle_mode);
            let transcript_layout = whir_transcript_layout(transcript_plan, merkle_mode)?;

            let valid_path =
                proofs_dir.join(format!("{}_{}_valid.bin", scenario.seed.name, fold_name));
            fs::write(&valid_path, &transcript_proof)?;
            let mut invalid_challenge = transcript_proof.clone();
            if transcript_layout.final_pow_nonce_offset < invalid_challenge.len() {
                invalid_challenge[transcript_layout.final_pow_nonce_offset] ^= 0x01;
            }
            let invalid_challenge_path = proofs_dir.join(format!(
                "{}_{}_invalid_challenge.bin",
                scenario.seed.name, fold_name
            ));
            fs::write(&invalid_challenge_path, &invalid_challenge)?;
            let mut invalid_missing_query = transcript_proof.clone();
            if transcript_layout.final_query_offset + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES
                <= invalid_missing_query.len()
            {
                invalid_missing_query.drain(
                    transcript_layout.final_query_offset
                        ..transcript_layout.final_query_offset + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES,
                );
            } else {
                invalid_missing_query.truncate(
                    invalid_missing_query
                        .len()
                        .saturating_sub(WHIR_TRANSCRIPT_FINAL_QUERY_BYTES),
                );
            }
            let invalid_missing_query_path = proofs_dir.join(format!(
                "{}_{}_invalid_missing_query.bin",
                scenario.seed.name, fold_name
            ));
            fs::write(&invalid_missing_query_path, &invalid_missing_query)?;
            let mut invalid_folding = transcript_proof.clone();
            if transcript_layout.final_sumcheck_offset < invalid_folding.len() {
                invalid_folding[transcript_layout.final_sumcheck_offset] ^= 0x08;
            }
            let invalid_folding_path = proofs_dir.join(format!(
                "{}_{}_invalid_folding.bin",
                scenario.seed.name, fold_name
            ));
            fs::write(&invalid_folding_path, &invalid_folding)?;
            let mut invalid_truncated = transcript_proof.clone();
            invalid_truncated.truncate(transcript_proof.len().saturating_sub(8));
            let invalid_truncated_path = proofs_dir.join(format!(
                "{}_{}_invalid_truncated.bin",
                scenario.seed.name, fold_name
            ));
            fs::write(&invalid_truncated_path, &invalid_truncated)?;

            let (transcript_upload_account, _transcript_upload_records, transcript_upload_cu) =
                upload_bytes(
                    &harness,
                    &transcript_proof,
                    config.upload_chunk_size,
                    true,
                    &format!("phase2/{}-full-reuse-{}", scenario.seed.name, fold_name),
                    config.upload_repetitions,
                )?;
            let transcript_upload_chunks =
                transcript_proof.len().div_ceil(config.upload_chunk_size) as u64;

            for query_reuse_mode in [
                WhirQueryReuseMode::PerQueryInversion,
                WhirQueryReuseMode::RoundBatchInversion,
            ] {
                let mut transcript_config =
                    whir_transcript_config_for_modes(fold_mode, merkle_mode);
                transcript_config.query_reuse_mode = query_reuse_mode;
                let reuse_name = whir_query_reuse_mode_name(query_reuse_mode).to_string();

                let host_valid = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &transcript_proof,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_challenge = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_challenge,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_missing_query = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_missing_query,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_folding = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_folding,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_truncated = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_truncated,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                validation.push(json!({
                    "scenario_name": scenario.seed.name,
                    "whir_fold_mode": fold_name,
                    "merkle_proof_mode": merkle_mode_name(merkle_mode),
                    "query_reuse_mode": reuse_name,
                    "valid_proof": host_valid.is_ok(),
                    "invalid_challenge_rejected": host_invalid_challenge.is_err(),
                    "invalid_missing_query_rejected": host_invalid_missing_query.is_err(),
                    "invalid_folding_rejected": host_invalid_folding.is_err(),
                    "invalid_truncated_rejected": host_invalid_truncated.is_err(),
                    "proofs": {
                        "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                        "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                        "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                        "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                        "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
                    }
                }));
                if !host_valid.is_ok()
                    || !host_invalid_challenge.is_err()
                    || !host_invalid_missing_query.is_err()
                    || !host_invalid_folding.is_err()
                    || !host_invalid_truncated.is_err()
                {
                    bail!(
                        "WHIR full reuse validation failed for {} {} {}",
                        scenario.seed.name,
                        fold_name,
                        reuse_name,
                    );
                }

                write_json(
                    &manifests_dir.join(format!(
                        "{}_whir_full_reuse_{}_{}.json",
                        scenario.seed.name, fold_name, reuse_name
                    )),
                    &json!({
                        "scenario_name": scenario.seed.name,
                        "security_target_bits": scenario.seed.security_target_bits,
                        "soundness_assumption": scenario.seed.soundness_assumption,
                        "config": verifier_config_json(transcript_config),
                        "query_only_config": verifier_config_json(query_only_config),
                        "statement_shape": phase2_whir_statement_shape_json(transcript_plan.statement_shape),
                        "query_plan": whir_query_plan_json(scenario.query_plan),
                        "transcript_plan": whir_transcript_plan_json(transcript_plan),
                        "proofs": {
                            "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                            "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                            "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                            "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                            "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
                        }
                    }),
                )?;

                let transcript_host_start = Instant::now();
                let transcript_host_outcome = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &transcript_proof,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                )
                .map_err(|err| anyhow!(err))?;
                let transcript_host_elapsed_ns = transcript_host_start.elapsed().as_nanos();
                let transcript_projection = project_features(
                    &format!(
                        "{}_{}_{}_full_reuse",
                        scenario.seed.name, fold_name, reuse_name
                    ),
                    &transcript_host_outcome.counters,
                    transcript_proof.len() as u64,
                    transcript_upload_chunks,
                    config.upload_chunk_size,
                    VERIFY_HEAP_FRAME_BYTES as u64,
                );

                records.push(WhirFullReuseMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    path_variant: "transcript_full".to_string(),
                    whir_fold_mode: fold_name.clone(),
                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                    query_reuse_mode: reuse_name.clone(),
                    query_precompute_mode: whir_query_precompute_mode_name(
                        transcript_config.query_precompute_mode,
                    )
                    .to_string(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks: transcript_upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "host_verify".to_string(),
                    repetition: 0,
                    actual_cu: None,
                    elapsed_ns: Some(transcript_host_elapsed_ns),
                    status: "ok".to_string(),
                    error: None,
                    counters: transcript_host_outcome.counters.into(),
                    field_mul_projection: transcript_projection.field_mul_projection,
                    extension_mul_projection: transcript_projection.extension_mul_projection,
                    field_inv_projection: transcript_projection.field_inv_projection,
                });
                records.push(WhirFullReuseMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    path_variant: "transcript_full".to_string(),
                    whir_fold_mode: fold_name.clone(),
                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                    query_reuse_mode: reuse_name.clone(),
                    query_precompute_mode: whir_query_precompute_mode_name(
                        transcript_config.query_precompute_mode,
                    )
                    .to_string(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks: transcript_upload_chunks,
                    heap_frame_bytes_requested: 0,
                    heap_pages_32k: 0,
                    stage: "upload_total".to_string(),
                    repetition: 0,
                    actual_cu: Some(transcript_upload_cu),
                    elapsed_ns: None,
                    status: "ok".to_string(),
                    error: None,
                    counters: CounterSummary::default(),
                    field_mul_projection: transcript_projection.field_mul_projection,
                    extension_mul_projection: transcript_projection.extension_mul_projection,
                    field_inv_projection: transcript_projection.field_inv_projection,
                });

                for repetition in 0..config.whir_transcript_verify_repetitions {
                    let tx = simulate_plan(
                        &harness,
                        TxPlan {
                            instructions: vec![build_phase2_whir_transcript_instruction(
                                harness.program_id,
                                transcript_upload_account.pubkey(),
                                transcript_config,
                                1,
                                WhirTranscriptTraceMode::Disabled,
                            )],
                            compute_unit_limit: None,
                            heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                        },
                    )?;
                    let (status, error) = simulated_tx_status(&tx);
                    let total_cu = tx.units_consumed.map(|value| value + transcript_upload_cu);
                    records.push(WhirFullReuseMeasurement {
                        scenario_name: scenario.seed.name.clone(),
                        path_variant: "transcript_full".to_string(),
                        whir_fold_mode: fold_name.clone(),
                        merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                        query_reuse_mode: reuse_name.clone(),
                        query_precompute_mode: whir_query_precompute_mode_name(
                            transcript_config.query_precompute_mode,
                        )
                        .to_string(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        total_explicit_query_count: scenario.total_explicit_query_count,
                        round_query_counts: scenario.round_query_counts.clone(),
                        commitment_ood_samples: scenario.commitment_ood_samples,
                        proof_bytes: transcript_proof.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks: transcript_upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage: "verify_sbf".to_string(),
                        repetition,
                        actual_cu: tx.units_consumed,
                        elapsed_ns: None,
                        status: status.clone(),
                        error: error.clone(),
                        counters: transcript_host_outcome.counters.into(),
                        field_mul_projection: transcript_projection.field_mul_projection,
                        extension_mul_projection: transcript_projection.extension_mul_projection,
                        field_inv_projection: transcript_projection.field_inv_projection,
                    });
                    records.push(WhirFullReuseMeasurement {
                        scenario_name: scenario.seed.name.clone(),
                        path_variant: "transcript_full".to_string(),
                        whir_fold_mode: fold_name.clone(),
                        merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                        query_reuse_mode: reuse_name.clone(),
                        query_precompute_mode: whir_query_precompute_mode_name(
                            transcript_config.query_precompute_mode,
                        )
                        .to_string(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        total_explicit_query_count: scenario.total_explicit_query_count,
                        round_query_counts: scenario.round_query_counts.clone(),
                        commitment_ood_samples: scenario.commitment_ood_samples,
                        proof_bytes: transcript_proof.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks: transcript_upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage: "total_sbf".to_string(),
                        repetition,
                        actual_cu: total_cu,
                        elapsed_ns: None,
                        status,
                        error,
                        counters: transcript_host_outcome.counters.into(),
                        field_mul_projection: transcript_projection.field_mul_projection,
                        extension_mul_projection: transcript_projection.extension_mul_projection,
                        field_inv_projection: transcript_projection.field_inv_projection,
                    });
                }

                for repetition in 0..config.whir_transcript_trace_repetitions {
                    let tx = simulate_plan(
                        &harness,
                        TxPlan {
                            instructions: vec![build_phase2_whir_transcript_instruction(
                                harness.program_id,
                                transcript_upload_account.pubkey(),
                                transcript_config,
                                1,
                                WhirTranscriptTraceMode::Enabled,
                            )],
                            compute_unit_limit: None,
                            heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                        },
                    )?;
                    let (status, error) = simulated_tx_status(&tx);
                    match parse_whir_transcript_phase_trace(&tx.logs) {
                        Ok(phase_costs) => {
                            for (phase, actual_cu) in phase_costs {
                                records.push(WhirFullReuseMeasurement {
                                    scenario_name: scenario.seed.name.clone(),
                                    path_variant: "transcript_full".to_string(),
                                    whir_fold_mode: fold_name.clone(),
                                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                                    query_reuse_mode: reuse_name.clone(),
                                    query_precompute_mode: whir_query_precompute_mode_name(
                                        transcript_config.query_precompute_mode,
                                    )
                                    .to_string(),
                                    security_target_bits: scenario.seed.security_target_bits,
                                    soundness_assumption: scenario
                                        .seed
                                        .soundness_assumption
                                        .clone(),
                                    total_explicit_query_count: scenario.total_explicit_query_count,
                                    round_query_counts: scenario.round_query_counts.clone(),
                                    commitment_ood_samples: scenario.commitment_ood_samples,
                                    proof_bytes: transcript_proof.len() as u64,
                                    upload_chunk_size: config.upload_chunk_size,
                                    upload_chunks: transcript_upload_chunks,
                                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                    heap_pages_32k: config
                                        .limits
                                        .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                    stage: phase,
                                    repetition,
                                    actual_cu: Some(actual_cu),
                                    elapsed_ns: None,
                                    status: status.clone(),
                                    error: error.clone(),
                                    counters: CounterSummary::default(),
                                    field_mul_projection: transcript_projection
                                        .field_mul_projection,
                                    extension_mul_projection: transcript_projection
                                        .extension_mul_projection,
                                    field_inv_projection: transcript_projection
                                        .field_inv_projection,
                                });
                            }
                        }
                        Err(parse_error) => {
                            records.push(WhirFullReuseMeasurement {
                                scenario_name: scenario.seed.name.clone(),
                                path_variant: "transcript_full".to_string(),
                                whir_fold_mode: fold_name.clone(),
                                merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                                query_reuse_mode: reuse_name.clone(),
                                query_precompute_mode: whir_query_precompute_mode_name(
                                    transcript_config.query_precompute_mode,
                                )
                                .to_string(),
                                security_target_bits: scenario.seed.security_target_bits,
                                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                                total_explicit_query_count: scenario.total_explicit_query_count,
                                round_query_counts: scenario.round_query_counts.clone(),
                                commitment_ood_samples: scenario.commitment_ood_samples,
                                proof_bytes: transcript_proof.len() as u64,
                                upload_chunk_size: config.upload_chunk_size,
                                upload_chunks: transcript_upload_chunks,
                                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                heap_pages_32k: config
                                    .limits
                                    .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                stage: "trace_incomplete".to_string(),
                                repetition,
                                actual_cu: tx.units_consumed,
                                elapsed_ns: None,
                                status: status.clone(),
                                error: Some(match error.as_ref() {
                                    Some(existing) => {
                                        format!("{existing}; trace_parse={parse_error:#}")
                                    }
                                    None => format!("{parse_error:#}"),
                                }),
                                counters: CounterSummary::default(),
                                field_mul_projection: transcript_projection.field_mul_projection,
                                extension_mul_projection: transcript_projection
                                    .extension_mul_projection,
                                field_inv_projection: transcript_projection.field_inv_projection,
                            });
                            trace_diagnostics.push(json!({
                                "scenario_name": scenario.seed.name.clone(),
                                "whir_fold_mode": fold_name.clone(),
                                "merkle_proof_mode": merkle_mode_name(merkle_mode),
                                "query_reuse_mode": reuse_name.clone(),
                                "repetition": repetition,
                                "status": status.clone(),
                                "error": error.clone(),
                                "trace_parse_error": parse_error.to_string(),
                                "units_consumed": tx.units_consumed,
                            }));
                        }
                    }
                }
            }
        }
    }

    write_json(&results_dir.join("validation.json"), &validation)?;
    write_json(
        &results_dir.join("trace_diagnostics.json"),
        &trace_diagnostics,
    )?;
    Ok(records)
}

fn run_whir_roundlocal_matrix(
    root: &Path,
    program_so: &Path,
    config: &Phase2RunConfig,
    results_dir: &Path,
    manifests_dir: &Path,
) -> Result<Vec<WhirFullReuseMeasurement>> {
    let scenarios = derive_whir_transcript_scenarios(config)?
        .into_iter()
        .filter(|scenario| {
            matches!(
                scenario.seed.name.as_str(),
                "whir_t128_capacity_full" | "whir_t100_johnson_full"
            )
        })
        .collect::<Vec<_>>();
    if scenarios.is_empty() {
        bail!("no targeted WHIR round-local scenarios were derived");
    }

    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&proofs_dir)?;
    write_json(
        &results_dir.join("scenarios.json"),
        &scenarios
            .iter()
            .map(|scenario| {
                json!({
                    "name": scenario.seed.name,
                    "security_target_bits": scenario.seed.security_target_bits,
                    "soundness_assumption": scenario.seed.soundness_assumption,
                    "round_query_counts": scenario.round_query_counts,
                    "commitment_ood_samples": scenario.commitment_ood_samples,
                    "merkle_proof_mode": merkle_mode_name(MerkleProofMode::MinimalSubtree),
                    "query_reuse_mode": whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion),
                    "query_precompute_modes": [
                        whir_query_precompute_mode_name(WhirQueryPrecomputeMode::None),
                        whir_query_precompute_mode_name(
                            WhirQueryPrecomputeMode::ProofCarriedRoundLocal,
                        ),
                    ],
                })
            })
            .collect::<Vec<_>>(),
    )?;

    let merkle_mode = MerkleProofMode::MinimalSubtree;
    let query_reuse_mode = WhirQueryReuseMode::RoundBatchInversion;
    let mut validation = Vec::new();
    let mut trace_diagnostics = Vec::new();
    let mut records = Vec::new();

    for scenario in scenarios {
        let (_validator, harness) =
            start_phase2_harness(root, results_dir, program_so, &config.limits)?;
        eprintln!("phase2: whir-roundlocal scenario={}", scenario.seed.name);

        for fold_mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
            let fold_name = fold_mode_name(fold_mode).to_string();
            let transcript_plan = whir_transcript_plan_for_merkle_mode(
                scenario.transcript_plan,
                fold_mode,
                merkle_mode,
            );

            for precompute_mode in [
                WhirQueryPrecomputeMode::None,
                WhirQueryPrecomputeMode::ProofCarriedRoundLocal,
            ] {
                let precompute_name = whir_query_precompute_mode_name(precompute_mode).to_string();
                let mut transcript_config =
                    whir_transcript_config_for_modes(fold_mode, merkle_mode);
                transcript_config.query_reuse_mode = query_reuse_mode;
                transcript_config.query_precompute_mode = precompute_mode;
                let transcript_proof =
                    build_phase2_whir_transcript_proof_bytes_with_precompute_mode(
                        transcript_plan,
                        fold_mode,
                        merkle_mode,
                        precompute_mode,
                    );
                let transcript_layout = whir_transcript_layout(transcript_plan, merkle_mode)?;

                let valid_path = proofs_dir.join(format!(
                    "{}_{}_{}_valid.bin",
                    scenario.seed.name, fold_name, precompute_name
                ));
                fs::write(&valid_path, &transcript_proof)?;
                let mut invalid_challenge = transcript_proof.clone();
                if transcript_layout.final_pow_nonce_offset < invalid_challenge.len() {
                    invalid_challenge[transcript_layout.final_pow_nonce_offset] ^= 0x01;
                }
                let invalid_challenge_path = proofs_dir.join(format!(
                    "{}_{}_{}_invalid_challenge.bin",
                    scenario.seed.name, fold_name, precompute_name
                ));
                fs::write(&invalid_challenge_path, &invalid_challenge)?;
                let mut invalid_missing_query = transcript_proof.clone();
                if transcript_layout.final_query_offset + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES
                    <= invalid_missing_query.len()
                {
                    invalid_missing_query.drain(
                        transcript_layout.final_query_offset
                            ..transcript_layout.final_query_offset
                                + WHIR_TRANSCRIPT_FINAL_QUERY_BYTES,
                    );
                } else {
                    invalid_missing_query.truncate(
                        invalid_missing_query
                            .len()
                            .saturating_sub(WHIR_TRANSCRIPT_FINAL_QUERY_BYTES),
                    );
                }
                let invalid_missing_query_path = proofs_dir.join(format!(
                    "{}_{}_{}_invalid_missing_query.bin",
                    scenario.seed.name, fold_name, precompute_name
                ));
                fs::write(&invalid_missing_query_path, &invalid_missing_query)?;
                let mut invalid_folding = transcript_proof.clone();
                if transcript_layout.final_sumcheck_offset < invalid_folding.len() {
                    invalid_folding[transcript_layout.final_sumcheck_offset] ^= 0x08;
                }
                let invalid_folding_path = proofs_dir.join(format!(
                    "{}_{}_{}_invalid_folding.bin",
                    scenario.seed.name, fold_name, precompute_name
                ));
                fs::write(&invalid_folding_path, &invalid_folding)?;
                let mut invalid_truncated = transcript_proof.clone();
                invalid_truncated.truncate(transcript_proof.len().saturating_sub(8));
                let invalid_truncated_path = proofs_dir.join(format!(
                    "{}_{}_{}_invalid_truncated.bin",
                    scenario.seed.name, fold_name, precompute_name
                ));
                fs::write(&invalid_truncated_path, &invalid_truncated)?;

                let (transcript_upload_account, _transcript_upload_records, transcript_upload_cu) =
                    upload_bytes(
                        &harness,
                        &transcript_proof,
                        config.upload_chunk_size,
                        true,
                        &format!(
                            "phase2/{}-roundlocal-{}-{}",
                            scenario.seed.name, fold_name, precompute_name
                        ),
                        config.upload_repetitions,
                    )?;
                let transcript_upload_chunks =
                    transcript_proof.len().div_ceil(config.upload_chunk_size) as u64;

                let host_valid = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &transcript_proof,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_challenge = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_challenge,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_missing_query = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_missing_query,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_folding = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_folding,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                let host_invalid_truncated = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &invalid_truncated,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                validation.push(json!({
                    "scenario_name": scenario.seed.name,
                    "whir_fold_mode": fold_name,
                    "merkle_proof_mode": merkle_mode_name(merkle_mode),
                    "query_reuse_mode": whir_query_reuse_mode_name(query_reuse_mode),
                    "query_precompute_mode": precompute_name,
                    "valid_proof": host_valid.is_ok(),
                    "invalid_challenge_rejected": host_invalid_challenge.is_err(),
                    "invalid_missing_query_rejected": host_invalid_missing_query.is_err(),
                    "invalid_folding_rejected": host_invalid_folding.is_err(),
                    "invalid_truncated_rejected": host_invalid_truncated.is_err(),
                    "proofs": {
                        "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                        "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                        "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                        "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                        "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
                    }
                }));
                if !host_valid.is_ok()
                    || !host_invalid_challenge.is_err()
                    || !host_invalid_missing_query.is_err()
                    || !host_invalid_folding.is_err()
                    || !host_invalid_truncated.is_err()
                {
                    bail!(
                        "WHIR round-local validation failed for {} {} {}",
                        scenario.seed.name,
                        fold_name,
                        precompute_name,
                    );
                }

                write_json(
                    &manifests_dir.join(format!(
                        "{}_whir_roundlocal_{}_{}.json",
                        scenario.seed.name, fold_name, precompute_name
                    )),
                    &json!({
                        "scenario_name": scenario.seed.name,
                        "security_target_bits": scenario.seed.security_target_bits,
                        "soundness_assumption": scenario.seed.soundness_assumption,
                        "config": verifier_config_json(transcript_config),
                        "statement_shape": phase2_whir_statement_shape_json(transcript_plan.statement_shape),
                        "query_plan": whir_query_plan_json(scenario.query_plan),
                        "transcript_plan": whir_transcript_plan_json(transcript_plan),
                        "proofs": {
                            "valid": valid_path.strip_prefix(root).unwrap_or(&valid_path).display().to_string(),
                            "invalid_challenge": invalid_challenge_path.strip_prefix(root).unwrap_or(&invalid_challenge_path).display().to_string(),
                            "invalid_missing_query": invalid_missing_query_path.strip_prefix(root).unwrap_or(&invalid_missing_query_path).display().to_string(),
                            "invalid_folding": invalid_folding_path.strip_prefix(root).unwrap_or(&invalid_folding_path).display().to_string(),
                            "invalid_truncated": invalid_truncated_path.strip_prefix(root).unwrap_or(&invalid_truncated_path).display().to_string(),
                        }
                    }),
                )?;

                let transcript_host_start = Instant::now();
                let transcript_host_outcome = run_phase2_whir_transcript_verify(
                    transcript_config,
                    &transcript_proof,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                )
                .map_err(|err| anyhow!(err))?;
                let transcript_host_elapsed_ns = transcript_host_start.elapsed().as_nanos();
                let transcript_projection = project_features(
                    &format!(
                        "{}_{}_{}_roundlocal",
                        scenario.seed.name, fold_name, precompute_name
                    ),
                    &transcript_host_outcome.counters,
                    transcript_proof.len() as u64,
                    transcript_upload_chunks,
                    config.upload_chunk_size,
                    VERIFY_HEAP_FRAME_BYTES as u64,
                );

                records.push(WhirFullReuseMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    path_variant: "transcript_full".to_string(),
                    whir_fold_mode: fold_name.clone(),
                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                    query_reuse_mode: whir_query_reuse_mode_name(query_reuse_mode).to_string(),
                    query_precompute_mode: precompute_name.clone(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks: transcript_upload_chunks,
                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                    heap_pages_32k: config.limits.heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                    stage: "host_verify".to_string(),
                    repetition: 0,
                    actual_cu: None,
                    elapsed_ns: Some(transcript_host_elapsed_ns),
                    status: "ok".to_string(),
                    error: None,
                    counters: transcript_host_outcome.counters.into(),
                    field_mul_projection: transcript_projection.field_mul_projection,
                    extension_mul_projection: transcript_projection.extension_mul_projection,
                    field_inv_projection: transcript_projection.field_inv_projection,
                });
                records.push(WhirFullReuseMeasurement {
                    scenario_name: scenario.seed.name.clone(),
                    path_variant: "transcript_full".to_string(),
                    whir_fold_mode: fold_name.clone(),
                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                    query_reuse_mode: whir_query_reuse_mode_name(query_reuse_mode).to_string(),
                    query_precompute_mode: precompute_name.clone(),
                    security_target_bits: scenario.seed.security_target_bits,
                    soundness_assumption: scenario.seed.soundness_assumption.clone(),
                    total_explicit_query_count: scenario.total_explicit_query_count,
                    round_query_counts: scenario.round_query_counts.clone(),
                    commitment_ood_samples: scenario.commitment_ood_samples,
                    proof_bytes: transcript_proof.len() as u64,
                    upload_chunk_size: config.upload_chunk_size,
                    upload_chunks: transcript_upload_chunks,
                    heap_frame_bytes_requested: 0,
                    heap_pages_32k: 0,
                    stage: "upload_total".to_string(),
                    repetition: 0,
                    actual_cu: Some(transcript_upload_cu),
                    elapsed_ns: None,
                    status: "ok".to_string(),
                    error: None,
                    counters: CounterSummary::default(),
                    field_mul_projection: transcript_projection.field_mul_projection,
                    extension_mul_projection: transcript_projection.extension_mul_projection,
                    field_inv_projection: transcript_projection.field_inv_projection,
                });

                for repetition in 0..config.whir_transcript_verify_repetitions {
                    let tx = simulate_plan(
                        &harness,
                        TxPlan {
                            instructions: vec![build_phase2_whir_transcript_instruction(
                                harness.program_id,
                                transcript_upload_account.pubkey(),
                                transcript_config,
                                1,
                                WhirTranscriptTraceMode::Disabled,
                            )],
                            compute_unit_limit: None,
                            heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                        },
                    )?;
                    let (status, error) = simulated_tx_status(&tx);
                    let total_cu = tx.units_consumed.map(|value| value + transcript_upload_cu);
                    records.push(WhirFullReuseMeasurement {
                        scenario_name: scenario.seed.name.clone(),
                        path_variant: "transcript_full".to_string(),
                        whir_fold_mode: fold_name.clone(),
                        merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                        query_reuse_mode: whir_query_reuse_mode_name(query_reuse_mode).to_string(),
                        query_precompute_mode: precompute_name.clone(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        total_explicit_query_count: scenario.total_explicit_query_count,
                        round_query_counts: scenario.round_query_counts.clone(),
                        commitment_ood_samples: scenario.commitment_ood_samples,
                        proof_bytes: transcript_proof.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks: transcript_upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage: "verify_sbf".to_string(),
                        repetition,
                        actual_cu: tx.units_consumed,
                        elapsed_ns: None,
                        status: status.clone(),
                        error: error.clone(),
                        counters: transcript_host_outcome.counters.into(),
                        field_mul_projection: transcript_projection.field_mul_projection,
                        extension_mul_projection: transcript_projection.extension_mul_projection,
                        field_inv_projection: transcript_projection.field_inv_projection,
                    });
                    records.push(WhirFullReuseMeasurement {
                        scenario_name: scenario.seed.name.clone(),
                        path_variant: "transcript_full".to_string(),
                        whir_fold_mode: fold_name.clone(),
                        merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                        query_reuse_mode: whir_query_reuse_mode_name(query_reuse_mode).to_string(),
                        query_precompute_mode: precompute_name.clone(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        total_explicit_query_count: scenario.total_explicit_query_count,
                        round_query_counts: scenario.round_query_counts.clone(),
                        commitment_ood_samples: scenario.commitment_ood_samples,
                        proof_bytes: transcript_proof.len() as u64,
                        upload_chunk_size: config.upload_chunk_size,
                        upload_chunks: transcript_upload_chunks,
                        heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                        heap_pages_32k: config
                            .limits
                            .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                        stage: "total_sbf".to_string(),
                        repetition,
                        actual_cu: total_cu,
                        elapsed_ns: None,
                        status,
                        error,
                        counters: transcript_host_outcome.counters.into(),
                        field_mul_projection: transcript_projection.field_mul_projection,
                        extension_mul_projection: transcript_projection.extension_mul_projection,
                        field_inv_projection: transcript_projection.field_inv_projection,
                    });
                }

                for repetition in 0..config.whir_transcript_trace_repetitions {
                    let tx = simulate_plan(
                        &harness,
                        TxPlan {
                            instructions: vec![build_phase2_whir_transcript_instruction(
                                harness.program_id,
                                transcript_upload_account.pubkey(),
                                transcript_config,
                                1,
                                WhirTranscriptTraceMode::Enabled,
                            )],
                            compute_unit_limit: None,
                            heap_frame_bytes: Some(VERIFY_HEAP_FRAME_BYTES),
                        },
                    )?;
                    let (status, error) = simulated_tx_status(&tx);
                    match parse_whir_transcript_phase_trace(&tx.logs) {
                        Ok(phase_costs) => {
                            for (phase, actual_cu) in phase_costs {
                                records.push(WhirFullReuseMeasurement {
                                    scenario_name: scenario.seed.name.clone(),
                                    path_variant: "transcript_full".to_string(),
                                    whir_fold_mode: fold_name.clone(),
                                    merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                                    query_reuse_mode: whir_query_reuse_mode_name(query_reuse_mode)
                                        .to_string(),
                                    query_precompute_mode: precompute_name.clone(),
                                    security_target_bits: scenario.seed.security_target_bits,
                                    soundness_assumption: scenario
                                        .seed
                                        .soundness_assumption
                                        .clone(),
                                    total_explicit_query_count: scenario.total_explicit_query_count,
                                    round_query_counts: scenario.round_query_counts.clone(),
                                    commitment_ood_samples: scenario.commitment_ood_samples,
                                    proof_bytes: transcript_proof.len() as u64,
                                    upload_chunk_size: config.upload_chunk_size,
                                    upload_chunks: transcript_upload_chunks,
                                    heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                    heap_pages_32k: config
                                        .limits
                                        .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                    stage: phase,
                                    repetition,
                                    actual_cu: Some(actual_cu),
                                    elapsed_ns: None,
                                    status: status.clone(),
                                    error: error.clone(),
                                    counters: CounterSummary::default(),
                                    field_mul_projection: transcript_projection
                                        .field_mul_projection,
                                    extension_mul_projection: transcript_projection
                                        .extension_mul_projection,
                                    field_inv_projection: transcript_projection
                                        .field_inv_projection,
                                });
                            }
                        }
                        Err(parse_error) => {
                            records.push(WhirFullReuseMeasurement {
                                scenario_name: scenario.seed.name.clone(),
                                path_variant: "transcript_full".to_string(),
                                whir_fold_mode: fold_name.clone(),
                                merkle_proof_mode: merkle_mode_name(merkle_mode).to_string(),
                                query_reuse_mode: whir_query_reuse_mode_name(query_reuse_mode)
                                    .to_string(),
                                query_precompute_mode: precompute_name.clone(),
                                security_target_bits: scenario.seed.security_target_bits,
                                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                                total_explicit_query_count: scenario.total_explicit_query_count,
                                round_query_counts: scenario.round_query_counts.clone(),
                                commitment_ood_samples: scenario.commitment_ood_samples,
                                proof_bytes: transcript_proof.len() as u64,
                                upload_chunk_size: config.upload_chunk_size,
                                upload_chunks: transcript_upload_chunks,
                                heap_frame_bytes_requested: VERIFY_HEAP_FRAME_BYTES as u64,
                                heap_pages_32k: config
                                    .limits
                                    .heap_pages_32k(VERIFY_HEAP_FRAME_BYTES as u64),
                                stage: "trace_incomplete".to_string(),
                                repetition,
                                actual_cu: tx.units_consumed,
                                elapsed_ns: None,
                                status: status.clone(),
                                error: Some(match error.as_ref() {
                                    Some(existing) => {
                                        format!("{existing}; trace_parse={parse_error:#}")
                                    }
                                    None => format!("{parse_error:#}"),
                                }),
                                counters: CounterSummary::default(),
                                field_mul_projection: transcript_projection.field_mul_projection,
                                extension_mul_projection: transcript_projection
                                    .extension_mul_projection,
                                field_inv_projection: transcript_projection.field_inv_projection,
                            });
                            trace_diagnostics.push(json!({
                                "scenario_name": scenario.seed.name.clone(),
                                "whir_fold_mode": fold_name.clone(),
                                "merkle_proof_mode": merkle_mode_name(merkle_mode),
                                "query_reuse_mode": whir_query_reuse_mode_name(query_reuse_mode),
                                "query_precompute_mode": precompute_name.clone(),
                                "repetition": repetition,
                                "status": status.clone(),
                                "error": error.clone(),
                                "trace_parse_error": parse_error.to_string(),
                                "units_consumed": tx.units_consumed,
                            }));
                        }
                    }
                }
            }
        }
    }

    write_json(&results_dir.join("validation.json"), &validation)?;
    write_json(
        &results_dir.join("trace_diagnostics.json"),
        &trace_diagnostics,
    )?;
    Ok(records)
}

fn proof_plan(run_config: &Phase2RunConfig) -> Phase2ProofPlan {
    Phase2ProofPlan {
        query_count: run_config.proof_plan.query_count,
        fold_arity: run_config.proof_plan.fold_arity,
        merkle_depth: run_config.proof_plan.merkle_depth,
        merkle_paths: run_config.proof_plan.merkle_paths,
        target_proof_bytes: run_config.proof_plan.target_proof_bytes,
        query_schedule_seed: run_config.proof_plan.query_schedule_seed,
        statement_seed: run_config.proof_plan.statement_seed,
    }
}

#[derive(Clone)]
struct ProjectedFeatures {
    input: ProfileScoreInput,
    field_mul_projection: u64,
    extension_mul_projection: u64,
    field_inv_projection: u64,
}

fn project_features(
    name: &str,
    counters: &Phase2Counters,
    proof_bytes: u64,
    upload_chunks: u64,
    upload_chunk_size: usize,
    heap_frame_bytes_requested: u64,
) -> ProjectedFeatures {
    let upload_bytes = proof_bytes;
    let upload_sha_bytes = upload_bytes + upload_chunks * 32;
    let field_mul_projection = counters.m31_mul_ops + counters.m31_square_ops;
    let extension_mul_projection = counters.cm31_mul_ops
        + counters.cm31_square_ops
        + counters.cm31_mul_const_ops
        + counters.qm31_mul_ops
        + counters.qm31_square_ops
        + counters.qm31_mul_const_ops;
    let field_inv_projection = counters.m31_inv_ops + counters.cm31_inv_ops + counters.qm31_inv_ops;
    let features = CostFeatures {
        sha_calls: counters.sha_calls + upload_chunks,
        sha_bytes: counters.sha_bytes + upload_sha_bytes,
        merkle_paths: counters.merkle_paths,
        merkle_levels: counters.merkle_levels,
        proof_bytes,
        upload_bytes,
        upload_chunks,
        heap_frame_bytes_requested,
        heap_pages_32k: SvmLimits::default().heap_pages_32k(heap_frame_bytes_requested),
        ro_account_count: 1,
        rw_account_count: 1,
        account_data_bytes_read: proof_bytes,
        account_data_bytes_written: proof_bytes,
        field_add_sub_ops: counters.m31_add_ops,
        field_mul_ops: field_mul_projection,
        field_inv_ops: field_inv_projection,
        extension_mul_ops: extension_mul_projection,
        ..CostFeatures::default()
    };
    let transport = TransportCostFeatures {
        sha_calls: upload_chunks,
        sha_bytes: upload_sha_bytes,
        upload_bytes,
        upload_chunks,
    };
    let mut notes = Vec::new();
    notes.push(format!(
        "Phase 2 feature projection uses upload_chunk_size={} and explicit {}-byte heap frame.",
        upload_chunk_size, heap_frame_bytes_requested
    ));
    notes.push(
        "field_mul_ops and extension_mul_ops are projected from Phase 2 instrumentation rather than a production verifier trace."
            .to_string(),
    );
    ProjectedFeatures {
        input: ProfileScoreInput {
            name: name.to_string(),
            features,
            protocol_family: Some("whir_phase2_skeleton".to_string()),
            transport,
            parameter_choices: Vec::new(),
            references: Vec::new(),
            query_soundness_model: None,
            notes,
        },
        field_mul_projection,
        extension_mul_projection,
        field_inv_projection,
    }
}

fn named_iterations(records: &[NamedIterations], name: &str) -> u32 {
    records
        .iter()
        .find(|item| item.name == name)
        .map(|item| item.iterations)
        .unwrap_or(1)
}

fn arithmetic_logical_units(workload: ArithmeticWorkloadId, iterations: u32) -> u64 {
    let multiplier = match workload {
        ArithmeticWorkloadId::Mul => 1,
        ArithmeticWorkloadId::Square => 1,
        ArithmeticWorkloadId::MulAdd => 1,
        ArithmeticWorkloadId::InnerProduct4 => 4,
        ArithmeticWorkloadId::Horner4 => 4,
        ArithmeticWorkloadId::DenominatorChain4 => 4,
        ArithmeticWorkloadId::SkeletonFoldStep => 4,
    };
    iterations as u64 * multiplier
}

fn extension_logical_units(workload: ExtensionWorkloadId, iterations: u32) -> u64 {
    let multiplier = match workload {
        ExtensionWorkloadId::Cm31Mul => 1,
        ExtensionWorkloadId::Cm31Square => 1,
        ExtensionWorkloadId::Cm31MulConst => 1,
        ExtensionWorkloadId::Cm31Inv => 1,
        ExtensionWorkloadId::Qm31Mul => 1,
        ExtensionWorkloadId::Qm31Square => 1,
        ExtensionWorkloadId::Qm31MulConst => 1,
        ExtensionWorkloadId::Qm31Inv => 1,
        ExtensionWorkloadId::SkeletonAccumulator => 1,
    };
    iterations as u64 * multiplier
}

fn pick_best_arithmetic(
    records: &[ArithmeticMeasurement],
    workload: ArithmeticWorkloadId,
) -> String {
    let workload = workload_name(workload);
    let mut best = None::<(&str, f64)>;
    for candidate in arithmetic_candidates() {
        let values = records
            .iter()
            .filter(|record| {
                record.domain == "sbf"
                    && record.workload == workload
                    && record.kernel_id == candidate.name
            })
            .filter_map(|record| record.cu_per_unit)
            .collect::<Vec<_>>();
        if values.is_empty() {
            continue;
        }
        let mean = values.iter().sum::<f64>() / values.len() as f64;
        if best.map(|(_, current)| mean < current).unwrap_or(true) {
            best = Some((candidate.name, mean));
        }
    }
    best.map(|(name, _)| name.to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

fn pick_best_extension_kernel(
    records: &[ExtensionMeasurement],
    workload: ExtensionWorkloadId,
) -> String {
    let workload = extension_workload_name(workload);
    let mut best = None::<(&str, f64)>;
    for extension_kernel_id in [ExtensionKernelId::Schoolbook, ExtensionKernelId::Karatsuba] {
        let name = extension_kernel_name(extension_kernel_id);
        let values = records
            .iter()
            .filter(|record| {
                record.domain == "sbf"
                    && record.workload == workload
                    && record.extension_kernel_id == name
            })
            .filter_map(|record| record.cu_per_unit)
            .collect::<Vec<_>>();
        if values.is_empty() {
            continue;
        }
        let mean = values.iter().sum::<f64>() / values.len() as f64;
        if best.map(|(_, current)| mean < current).unwrap_or(true) {
            best = Some((name, mean));
        }
    }
    best.map(|(name, _)| name.to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

fn skeleton_variants(arithmetic: Phase2ArithmeticConfig) -> Vec<SkeletonVariant> {
    let mut variants = Vec::new();
    for extension_kernel_id in [ExtensionKernelId::Schoolbook, ExtensionKernelId::Karatsuba] {
        for lift_policy in [LiftPolicy::EagerQm31, LiftPolicy::LateLiftQm31] {
            for whir_fold_mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
                let name = format!(
                    "{}_{}_{}",
                    extension_kernel_name(extension_kernel_id),
                    lift_policy_name(lift_policy),
                    fold_mode_name(whir_fold_mode)
                );
                variants.push(SkeletonVariant {
                    name,
                    config: Phase2VerifierConfig {
                        arithmetic_kernel_id: arithmetic.kernel_id,
                        reduction_mode: arithmetic.reduction_mode,
                        lazy_reduction_mode: arithmetic.lazy_reduction_mode,
                        extension_kernel_id,
                        lift_policy,
                        whir_fold_mode,
                        merkle_proof_mode: MerkleProofMode::SeparatePaths,
                        query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
                        query_precompute_mode: WhirQueryPrecomputeMode::None,
                    },
                });
            }
        }
    }
    variants
}

fn whir_query_variants() -> Vec<WhirQueryVariant> {
    vec![
        WhirQueryVariant {
            name: "direct_schoolbook_eager",
            config: Phase2VerifierConfig {
                arithmetic_kernel_id: ArithmeticKernelId::DirectM31,
                reduction_mode: ReductionMode::DirectM31,
                lazy_reduction_mode: LazyReductionMode::None,
                extension_kernel_id: ExtensionKernelId::Schoolbook,
                lift_policy: LiftPolicy::EagerQm31,
                whir_fold_mode: WhirFoldMode::RawFibers,
                merkle_proof_mode: MerkleProofMode::SeparatePaths,
                query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
                query_precompute_mode: WhirQueryPrecomputeMode::None,
            },
        },
        WhirQueryVariant {
            name: "reference_schoolbook_eager",
            config: Phase2VerifierConfig {
                arithmetic_kernel_id: ArithmeticKernelId::ReferenceCanonical,
                reduction_mode: ReductionMode::Canonical,
                lazy_reduction_mode: LazyReductionMode::None,
                extension_kernel_id: ExtensionKernelId::Schoolbook,
                lift_policy: LiftPolicy::EagerQm31,
                whir_fold_mode: WhirFoldMode::RawFibers,
                merkle_proof_mode: MerkleProofMode::SeparatePaths,
                query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
                query_precompute_mode: WhirQueryPrecomputeMode::None,
            },
        },
        WhirQueryVariant {
            name: "reference_karatsuba_eager",
            config: Phase2VerifierConfig {
                arithmetic_kernel_id: ArithmeticKernelId::ReferenceCanonical,
                reduction_mode: ReductionMode::Canonical,
                lazy_reduction_mode: LazyReductionMode::None,
                extension_kernel_id: ExtensionKernelId::Karatsuba,
                lift_policy: LiftPolicy::EagerQm31,
                whir_fold_mode: WhirFoldMode::RawFibers,
                merkle_proof_mode: MerkleProofMode::SeparatePaths,
                query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
                query_precompute_mode: WhirQueryPrecomputeMode::None,
            },
        },
        WhirQueryVariant {
            name: "reference_karatsuba_late",
            config: Phase2VerifierConfig {
                arithmetic_kernel_id: ArithmeticKernelId::ReferenceCanonical,
                reduction_mode: ReductionMode::Canonical,
                lazy_reduction_mode: LazyReductionMode::None,
                extension_kernel_id: ExtensionKernelId::Karatsuba,
                lift_policy: LiftPolicy::LateLiftQm31,
                whir_fold_mode: WhirFoldMode::RawFibers,
                merkle_proof_mode: MerkleProofMode::SeparatePaths,
                query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
                query_precompute_mode: WhirQueryPrecomputeMode::None,
            },
        },
    ]
}

fn derive_whir_query_scenarios(
    config: &Phase2RunConfig,
    phase1_summary: &Phase1Summary,
) -> Result<Vec<DerivedWhirQueryScenario>> {
    let statement_shape = phase2_whir_statement_shape()?;
    let mut scenarios = Vec::new();
    for seed in &config.whir_query_scenarios {
        let qualified_assumption = match seed.soundness_assumption.as_str() {
            "whir_capacity_full" => SecurityQualifiedAssumption::Optimistic,
            "whir_johnson_full" => SecurityQualifiedAssumption::Conservative,
            other => bail!("unsupported WHIR query assumption `{other}`"),
        };
        let whir_assumption = match qualified_assumption {
            SecurityQualifiedAssumption::Optimistic => WhirSecurityAssumption::Capacity,
            SecurityQualifiedAssumption::Conservative => WhirSecurityAssumption::Johnson,
        };
        let statement = default_spend_statement();
        let mut arithmetization = default_spend_arithmetization();
        let boundary_layout = spend_boundary_layout(&statement);
        arithmetization.boundary_constraint_groups = boundary_layout.total_groups;
        let application_merkle_levels =
            statement.spends * statement.note_openings_per_spend * statement.note_tree_depth;
        let total_rows = application_merkle_levels * arithmetization.merkle_rows_per_level
            + statement.spends
                * statement.nullifier_hashes_per_spend
                * arithmetization.nullifier_hash_rows
            + statement.outputs
                * statement.note_commitments_per_output
                * arithmetization.note_commitment_rows
            + statement.amount_range_checks_64 * arithmetization.range_check_rows
            + statement.ownership_checks * arithmetization.ownership_rows
            + statement.balance_constraints * arithmetization.balance_rows
            + statement.lookup_arguments * arithmetization.lookup_rows
            + arithmetization.misc_rows;
        let evaluation_domain_log2 = ceil_log2(total_rows.max(1));
        let derivation = derive_full_whir_security(
            seed.security_target_bits,
            seed.log_inv_rate,
            seed.grinding_bits,
            whir_assumption,
            evaluation_domain_log2,
            155,
            4,
            4,
            1,
        );
        let (profile, _assessment, _starting_query_count, _notes) =
            build_security_qualified_profile(
                SpendProtocol::Whir,
                &seed.name,
                seed.log_inv_rate,
                seed.grinding_bits,
                seed.security_target_bits,
                qualified_assumption,
            )?;
        let legacy_bound = score_profile_with_components(
            &phase1_summary.model.chosen,
            phase1_summary
                .verification_core_model
                .as_ref()
                .map(|value| &value.chosen),
            phase1_summary
                .transport_model
                .as_ref()
                .map(|value| &value.chosen),
            &config.limits,
            &profile,
        )?;
        let mut rounds = [Phase2WhirRoundPlan::default(); PHASE2_WHIR_MAX_ROUNDS];
        let mut round_query_counts = Vec::new();
        for (index, round) in derivation.rounds.iter().enumerate() {
            if index >= PHASE2_WHIR_MAX_ROUNDS {
                bail!("derived WHIR round count exceeds probe capacity");
            }
            let verifier = spend_verifier_assumptions(
                SpendProtocol::Whir,
                round.num_queries,
                round.current_log_inv_rate,
                seed.grinding_bits,
            );
            rounds[index] = Phase2WhirRoundPlan {
                query_count: round
                    .num_queries
                    .try_into()
                    .context("round query count exceeds u16")?,
                merkle_depth: verifier
                    .proof_merkle_depth
                    .try_into()
                    .context("round merkle depth exceeds u16")?,
                ood_samples: round
                    .ood_samples
                    .try_into()
                    .context("round ood samples exceeds u16")?,
                opening_count: ((round.ood_samples.max(1) + 1)
                    .min(PHASE2_WHIR_MAX_OPENING_TERMS as u64))
                .try_into()
                .unwrap(),
                selector_count: 1,
            };
            round_query_counts.push(round.num_queries);
        }
        let final_index = derivation.rounds.len();
        if final_index >= PHASE2_WHIR_MAX_ROUNDS {
            bail!("final WHIR round exceeds probe capacity");
        }
        let final_verifier = spend_verifier_assumptions(
            SpendProtocol::Whir,
            derivation.final_queries,
            derivation.final_log_inv_rate,
            seed.grinding_bits,
        );
        rounds[final_index] = Phase2WhirRoundPlan {
            query_count: derivation
                .final_queries
                .try_into()
                .context("final query count exceeds u16")?,
            merkle_depth: final_verifier
                .proof_merkle_depth
                .try_into()
                .context("final merkle depth exceeds u16")?,
            ood_samples: derivation
                .commitment_ood_samples
                .try_into()
                .context("final ood samples exceeds u16")?,
            opening_count: ((derivation.commitment_ood_samples.max(1) + 1)
                .min(PHASE2_WHIR_MAX_OPENING_TERMS as u64))
            .try_into()
            .unwrap(),
            selector_count: 2,
        };
        round_query_counts.push(derivation.final_queries);
        scenarios.push(DerivedWhirQueryScenario {
            seed: seed.clone(),
            plan: Phase2WhirQueryPlan {
                round_count: (derivation.rounds.len() + 1)
                    .try_into()
                    .context("derived WHIR round count exceeds u16")?,
                rounds,
                statement_shape,
                target_proof_bytes: profile
                    .features
                    .proof_bytes
                    .try_into()
                    .context("WHIR proof bytes exceed u32")?,
                query_schedule_seed: 0x0f11_dbee_7bad_c0de ^ seed.log_inv_rate as u64,
                statement_seed: 0x52ee_d123_9abc_7711 ^ seed.grinding_bits as u64,
            },
            profile,
            legacy_bound_cu: legacy_bound.predicted_cu,
            total_explicit_query_count: derivation.total_explicit_query_count,
            round_query_counts,
        });
    }
    Ok(scenarios)
}

fn derive_whir_transcript_scenarios(
    config: &Phase2RunConfig,
) -> Result<Vec<DerivedWhirTranscriptScenario>> {
    let statement_shape = phase2_whir_statement_shape()?;
    let mut scenarios = Vec::new();
    for seed in &config.whir_query_scenarios {
        let qualified_assumption = match seed.soundness_assumption.as_str() {
            "whir_capacity_full" => SecurityQualifiedAssumption::Optimistic,
            "whir_johnson_full" => SecurityQualifiedAssumption::Conservative,
            other => bail!("unsupported WHIR transcript assumption `{other}`"),
        };
        let whir_assumption = match qualified_assumption {
            SecurityQualifiedAssumption::Optimistic => WhirSecurityAssumption::Capacity,
            SecurityQualifiedAssumption::Conservative => WhirSecurityAssumption::Johnson,
        };
        let derivation = derive_full_whir_security(
            seed.security_target_bits,
            seed.log_inv_rate,
            seed.grinding_bits,
            whir_assumption,
            u32::from(statement_shape.evaluation_domain_log2),
            155,
            4,
            4,
            1,
        );
        let (profile, _assessment, _starting_query_count, _notes) =
            build_security_qualified_profile(
                SpendProtocol::Whir,
                &seed.name,
                seed.log_inv_rate,
                seed.grinding_bits,
                seed.security_target_bits,
                qualified_assumption,
            )?;

        let mut query_rounds = [Phase2WhirRoundPlan::default(); PHASE2_WHIR_MAX_ROUNDS];
        let mut transcript_rounds =
            [Phase2WhirTranscriptRoundPlan::default(); PHASE2_WHIR_MAX_ROUNDS];
        let mut round_query_counts = Vec::new();
        for (index, round) in derivation.rounds.iter().enumerate() {
            if index >= PHASE2_WHIR_MAX_ROUNDS {
                bail!("derived WHIR transcript round count exceeds probe capacity");
            }
            let verifier = spend_verifier_assumptions(
                SpendProtocol::Whir,
                round.num_queries,
                round.current_log_inv_rate,
                seed.grinding_bits,
            );
            query_rounds[index] = Phase2WhirRoundPlan {
                query_count: round
                    .num_queries
                    .try_into()
                    .context("transcript round query count exceeds u16")?,
                merkle_depth: verifier
                    .proof_merkle_depth
                    .try_into()
                    .context("transcript round merkle depth exceeds u16")?,
                ood_samples: round
                    .ood_samples
                    .try_into()
                    .context("transcript round ood samples exceeds u16")?,
                opening_count: ((round.ood_samples.max(1) + 1)
                    .min(PHASE2_WHIR_MAX_OPENING_TERMS as u64))
                .try_into()
                .unwrap(),
                selector_count: 1,
            };
            transcript_rounds[index] = Phase2WhirTranscriptRoundPlan {
                query_count: query_rounds[index].query_count,
                merkle_depth: query_rounds[index].merkle_depth,
                ood_samples: query_rounds[index].ood_samples,
                opening_count: query_rounds[index].opening_count,
                selector_count: query_rounds[index].selector_count,
                pow_bits: round
                    .query_pow_bits_required
                    .try_into()
                    .context("transcript round pow bits exceeds u16")?,
                sumcheck_rounds: derivation
                    .later_round_folding_factor
                    .try_into()
                    .context("transcript sumcheck rounds exceeds u16")?,
                folding_pow_bits: round
                    .folding_pow_bits_required
                    .try_into()
                    .context("transcript folding pow bits exceeds u16")?,
            };
            round_query_counts.push(round.num_queries);
        }

        let final_index = derivation.rounds.len();
        if final_index >= PHASE2_WHIR_MAX_ROUNDS {
            bail!("transcript final round exceeds probe capacity");
        }
        let final_verifier = spend_verifier_assumptions(
            SpendProtocol::Whir,
            derivation.final_queries,
            derivation.final_log_inv_rate,
            seed.grinding_bits,
        );
        query_rounds[final_index] = Phase2WhirRoundPlan {
            query_count: derivation
                .final_queries
                .try_into()
                .context("transcript final query count exceeds u16")?,
            merkle_depth: final_verifier
                .proof_merkle_depth
                .try_into()
                .context("transcript final merkle depth exceeds u16")?,
            ood_samples: derivation
                .commitment_ood_samples
                .try_into()
                .context("transcript final ood samples exceeds u16")?,
            opening_count: ((derivation.commitment_ood_samples.max(1) + 1)
                .min(PHASE2_WHIR_MAX_OPENING_TERMS as u64))
            .try_into()
            .unwrap(),
            selector_count: 2,
        };
        round_query_counts.push(derivation.final_queries);

        let (_, final_sumcheck_rounds) = whir_round_structure(
            u32::from(statement_shape.evaluation_domain_log2),
            derivation.first_round_folding_factor,
            derivation.later_round_folding_factor,
        );

        scenarios.push(DerivedWhirTranscriptScenario {
            seed: seed.clone(),
            query_plan: Phase2WhirQueryPlan {
                round_count: (derivation.rounds.len() + 1)
                    .try_into()
                    .context("transcript query round count exceeds u16")?,
                rounds: query_rounds,
                statement_shape,
                target_proof_bytes: profile
                    .features
                    .proof_bytes
                    .try_into()
                    .context("transcript query proof bytes exceed u32")?,
                query_schedule_seed: 0x0f11_dbee_7bad_c0de ^ seed.log_inv_rate as u64,
                statement_seed: 0x52ee_d123_9abc_7711 ^ seed.grinding_bits as u64,
            },
            transcript_plan: Phase2WhirTranscriptPlan {
                round_count: derivation
                    .rounds
                    .len()
                    .try_into()
                    .context("transcript round count exceeds u16")?,
                rounds: transcript_rounds,
                statement_shape,
                target_proof_bytes: profile
                    .features
                    .proof_bytes
                    .try_into()
                    .context("transcript proof bytes exceed u32")?,
                query_schedule_seed: 0x0f11_dbee_7bad_c0de ^ seed.log_inv_rate as u64,
                statement_seed: 0x52ee_d123_9abc_7711 ^ seed.grinding_bits as u64,
                commitment_ood_samples: derivation
                    .commitment_ood_samples
                    .try_into()
                    .context("transcript commitment ood exceeds u16")?,
                initial_sumcheck_rounds: derivation
                    .first_round_folding_factor
                    .try_into()
                    .context("transcript initial sumcheck rounds exceeds u16")?,
                initial_folding_pow_bits: derivation
                    .starting_folding_pow_bits_required
                    .try_into()
                    .context("transcript initial folding pow exceeds u16")?,
                final_query_count: derivation
                    .final_queries
                    .try_into()
                    .context("transcript final queries exceed u16")?,
                final_merkle_depth: final_verifier
                    .proof_merkle_depth
                    .try_into()
                    .context("transcript final merkle depth exceeds u16")?,
                final_pow_bits: derivation
                    .final_query_pow_bits_required
                    .try_into()
                    .context("transcript final pow bits exceeds u16")?,
                final_sumcheck_rounds: final_sumcheck_rounds
                    .try_into()
                    .context("transcript final sumcheck rounds exceeds u16")?,
                final_folding_pow_bits: derivation
                    .final_folding_pow_bits_required
                    .try_into()
                    .context("transcript final folding pow bits exceeds u16")?,
            },
            total_explicit_query_count: derivation.total_explicit_query_count,
            round_query_counts,
            commitment_ood_samples: derivation.commitment_ood_samples,
        });
    }
    Ok(scenarios)
}

fn whir_query_baseline_config() -> Phase2VerifierConfig {
    Phase2VerifierConfig {
        arithmetic_kernel_id: ArithmeticKernelId::ReferenceCanonical,
        reduction_mode: ReductionMode::Canonical,
        lazy_reduction_mode: LazyReductionMode::None,
        extension_kernel_id: ExtensionKernelId::Karatsuba,
        lift_policy: LiftPolicy::LateLiftQm31,
        whir_fold_mode: WhirFoldMode::LocalInterpolant,
        merkle_proof_mode: MerkleProofMode::SeparatePaths,
        query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
        query_precompute_mode: WhirQueryPrecomputeMode::None,
    }
}

fn whir_transcript_config() -> Phase2VerifierConfig {
    whir_query_baseline_config()
}

fn whir_transcript_config_for_merkle_mode(mode: MerkleProofMode) -> Phase2VerifierConfig {
    let mut config = whir_transcript_config();
    config.merkle_proof_mode = mode;
    config
}

fn whir_transcript_config_for_modes(
    fold_mode: WhirFoldMode,
    merkle_mode: MerkleProofMode,
) -> Phase2VerifierConfig {
    let mut config = whir_transcript_config();
    config.whir_fold_mode = fold_mode;
    config.merkle_proof_mode = merkle_mode;
    config
}

fn whir_query_reuse_mode_name(mode: WhirQueryReuseMode) -> &'static str {
    match mode {
        WhirQueryReuseMode::PerQueryInversion => "per_query_inversion",
        WhirQueryReuseMode::RoundBatchInversion => "round_batch_inversion",
    }
}

fn default_query_precompute_mode_name() -> String {
    "none".to_string()
}

fn whir_query_precompute_mode_name(mode: WhirQueryPrecomputeMode) -> &'static str {
    match mode {
        WhirQueryPrecomputeMode::None => "none",
        WhirQueryPrecomputeMode::ProofCarriedRoundLocal => "proof_carried_round_local",
    }
}

fn phase2_targeted_t100_johnson_seed() -> WhirQueryScenarioSeed {
    WhirQueryScenarioSeed {
        name: "whir_t100_johnson_full".to_string(),
        security_target_bits: 100.0,
        soundness_assumption: "whir_johnson_full".to_string(),
        log_inv_rate: 4,
        grinding_bits: 32,
    }
}

fn phase2_full_reuse_run_config() -> Phase2RunConfig {
    let mut config = phase2_run_config();
    if !config
        .whir_query_scenarios
        .iter()
        .any(|scenario| scenario.name == "whir_t100_johnson_full")
    {
        config
            .whir_query_scenarios
            .push(phase2_targeted_t100_johnson_seed());
    }
    config
}

fn synthetic_merkle_node_count(depth: u16, paths: u16, mode: MerkleProofMode) -> u64 {
    let effective_paths = u64::from(paths.max(1));
    let effective_depth = u64::from(depth.max(1));
    match mode {
        MerkleProofMode::SeparatePaths => effective_depth * effective_paths,
        MerkleProofMode::MinimalSubtree => effective_depth + effective_paths.saturating_sub(1),
    }
}

fn synthetic_whir_transcript_merkle_nodes(
    plan: Phase2WhirTranscriptPlan,
    mode: MerkleProofMode,
) -> u64 {
    let round_count = usize::from(plan.round_count.clamp(0, PHASE2_WHIR_MAX_ROUNDS as u16));
    let mut total = 0_u64;
    for round in plan.rounds.iter().take(round_count) {
        total += synthetic_merkle_node_count(round.merkle_depth, round.query_count, mode);
    }
    total + synthetic_merkle_node_count(plan.final_merkle_depth, plan.final_query_count, mode)
}

fn synthetic_whir_transcript_merkle_witness_bytes(
    plan: Phase2WhirTranscriptPlan,
    mode: MerkleProofMode,
) -> u64 {
    synthetic_whir_transcript_merkle_nodes(plan, mode) * 32
}

fn whir_transcript_plan_for_merkle_mode(
    plan: Phase2WhirTranscriptPlan,
    fold_mode: WhirFoldMode,
    mode: MerkleProofMode,
) -> Phase2WhirTranscriptPlan {
    let separate_nodes =
        synthetic_whir_transcript_merkle_nodes(plan, MerkleProofMode::SeparatePaths);
    let mode_nodes = synthetic_whir_transcript_merkle_nodes(plan, mode);
    let node_savings = separate_nodes.saturating_sub(mode_nodes);
    let byte_savings = node_savings.saturating_mul(32);
    let mut adjusted = plan;
    adjusted.target_proof_bytes = adjusted
        .target_proof_bytes
        .saturating_sub(byte_savings.min(u64::from(u32::MAX)) as u32);
    let minimum_proof = build_phase2_whir_transcript_proof_bytes(adjusted, fold_mode, mode);
    adjusted.target_proof_bytes = minimum_proof.len() as u32;
    adjusted
}

fn simulated_tx_status(tx: &SimulatedTx) -> (String, Option<String>) {
    match &tx.error {
        Some(error) => ("simulation_error".to_string(), Some(error.clone())),
        None => ("ok".to_string(), None),
    }
}

fn whir_transcript_layout(
    plan: Phase2WhirTranscriptPlan,
    merkle_mode: MerkleProofMode,
) -> Result<WhirTranscriptLayout> {
    let round_count = usize::from(plan.round_count.clamp(0, PHASE2_WHIR_MAX_ROUNDS as u16));
    let mut cursor = WHIR_TRANSCRIPT_PREFIX_BYTES
        .checked_add(WHIR_TRANSCRIPT_STATEMENT_SHAPE_BYTES)
        .and_then(|value| value.checked_add(16))
        .ok_or_else(|| anyhow!("WHIR transcript header overflow"))?;
    cursor = cursor
        .checked_add(round_count * WHIR_TRANSCRIPT_ROUND_PLAN_BYTES)
        .ok_or_else(|| anyhow!("WHIR transcript round plan overflow"))?;
    cursor = cursor
        .checked_add(32)
        .ok_or_else(|| anyhow!("WHIR transcript commitment root overflow"))?;
    cursor = cursor
        .checked_add(
            usize::from(
                plan.commitment_ood_samples
                    .min(WHIR_TRANSCRIPT_MAX_OOD_SAMPLES),
            ) * 8,
        )
        .ok_or_else(|| anyhow!("WHIR transcript commitment OOD overflow"))?;
    cursor = cursor
        .checked_add(
            usize::from(
                plan.initial_sumcheck_rounds
                    .min(WHIR_TRANSCRIPT_MAX_SUMCHECK_ROUNDS),
            ) * WHIR_TRANSCRIPT_SUMCHECK_RECORD_BYTES,
        )
        .ok_or_else(|| anyhow!("WHIR transcript initial sumcheck overflow"))?;

    for round in plan.rounds.iter().take(round_count) {
        cursor = cursor
            .checked_add(32)
            .ok_or_else(|| anyhow!("WHIR transcript round root overflow"))?;
        cursor = cursor
            .checked_add(usize::from(round.ood_samples.min(WHIR_TRANSCRIPT_MAX_OOD_SAMPLES)) * 8)
            .ok_or_else(|| anyhow!("WHIR transcript round OOD overflow"))?;
        cursor = cursor
            .checked_add(8)
            .ok_or_else(|| anyhow!("WHIR transcript round PoW overflow"))?;
        cursor = cursor
            .checked_add(usize::from(round.query_count.max(1)) * WHIR_TRANSCRIPT_QUERY_RECORD_BYTES)
            .ok_or_else(|| anyhow!("WHIR transcript query record overflow"))?;
        cursor = cursor
            .checked_add(
                synthetic_merkle_node_count(round.merkle_depth, round.query_count, merkle_mode)
                    as usize
                    * 32,
            )
            .ok_or_else(|| anyhow!("WHIR transcript round merkle witness overflow"))?;
        cursor = cursor
            .checked_add(
                usize::from(
                    round
                        .sumcheck_rounds
                        .min(WHIR_TRANSCRIPT_MAX_SUMCHECK_ROUNDS),
                ) * WHIR_TRANSCRIPT_SUMCHECK_RECORD_BYTES,
            )
            .ok_or_else(|| anyhow!("WHIR transcript round sumcheck overflow"))?;
    }

    let final_coeff_count = (1usize
        << usize::from(
            plan.final_sumcheck_rounds
                .min(WHIR_TRANSCRIPT_MAX_SUMCHECK_ROUNDS),
        ))
    .min(WHIR_TRANSCRIPT_MAX_FINAL_COEFFS);
    cursor = cursor
        .checked_add(final_coeff_count * 4)
        .ok_or_else(|| anyhow!("WHIR transcript final coeff overflow"))?;
    let final_pow_nonce_offset = cursor;
    cursor = cursor
        .checked_add(8)
        .ok_or_else(|| anyhow!("WHIR transcript final PoW overflow"))?;
    let final_query_offset = cursor;
    cursor = cursor
        .checked_add(usize::from(plan.final_query_count.max(1)) * WHIR_TRANSCRIPT_FINAL_QUERY_BYTES)
        .ok_or_else(|| anyhow!("WHIR transcript final query overflow"))?;
    cursor = cursor
        .checked_add(
            synthetic_merkle_node_count(
                plan.final_merkle_depth,
                plan.final_query_count,
                merkle_mode,
            ) as usize
                * 32,
        )
        .ok_or_else(|| anyhow!("WHIR transcript final merkle witness overflow"))?;
    let final_sumcheck_offset = cursor;
    let _deferred_offset = cursor
        .checked_add(
            usize::from(
                plan.final_sumcheck_rounds
                    .min(WHIR_TRANSCRIPT_MAX_SUMCHECK_ROUNDS),
            ) * WHIR_TRANSCRIPT_SUMCHECK_RECORD_BYTES,
        )
        .and_then(|value| value.checked_add(WHIR_TRANSCRIPT_DEFERRED_BYTES))
        .ok_or_else(|| anyhow!("WHIR transcript deferred section overflow"))?;

    Ok(WhirTranscriptLayout {
        final_pow_nonce_offset,
        final_query_offset,
        final_sumcheck_offset,
    })
}

fn verifier_config_json(config: Phase2VerifierConfig) -> serde_json::Value {
    json!({
        "arithmetic_kernel_id": arithmetic_kernel_name(config.arithmetic_kernel_id),
        "reduction_mode": reduction_mode_name(config.reduction_mode),
        "lazy_reduction_mode": lazy_mode_name(config.lazy_reduction_mode),
        "extension_kernel_id": extension_kernel_name(config.extension_kernel_id),
        "lift_policy": lift_policy_name(config.lift_policy),
        "whir_fold_mode": fold_mode_name(config.whir_fold_mode),
        "merkle_proof_mode": merkle_mode_name(config.merkle_proof_mode),
        "query_reuse_mode": whir_query_reuse_mode_name(config.query_reuse_mode),
        "query_precompute_mode": whir_query_precompute_mode_name(config.query_precompute_mode),
    })
}

fn whir_query_plan_json(plan: Phase2WhirQueryPlan) -> serde_json::Value {
    json!({
        "round_count": plan.round_count,
        "target_proof_bytes": plan.target_proof_bytes,
        "query_schedule_seed": plan.query_schedule_seed,
        "statement_seed": plan.statement_seed,
        "rounds": plan
            .rounds
            .iter()
            .take(usize::from(plan.round_count.min(PHASE2_WHIR_MAX_ROUNDS as u16)))
            .map(|round| {
                json!({
                    "query_count": round.query_count,
                    "merkle_depth": round.merkle_depth,
                    "ood_samples": round.ood_samples,
                    "opening_count": round.opening_count,
                    "selector_count": round.selector_count,
                })
            })
            .collect::<Vec<_>>(),
    })
}

fn whir_transcript_plan_json(plan: Phase2WhirTranscriptPlan) -> serde_json::Value {
    json!({
        "round_count": plan.round_count,
        "target_proof_bytes": plan.target_proof_bytes,
        "query_schedule_seed": plan.query_schedule_seed,
        "statement_seed": plan.statement_seed,
        "commitment_ood_samples": plan.commitment_ood_samples,
        "initial_sumcheck_rounds": plan.initial_sumcheck_rounds,
        "initial_folding_pow_bits": plan.initial_folding_pow_bits,
        "final_query_count": plan.final_query_count,
        "final_merkle_depth": plan.final_merkle_depth,
        "final_pow_bits": plan.final_pow_bits,
        "final_sumcheck_rounds": plan.final_sumcheck_rounds,
        "final_folding_pow_bits": plan.final_folding_pow_bits,
        "rounds": plan
            .rounds
            .iter()
            .take(usize::from(plan.round_count.min(PHASE2_WHIR_MAX_ROUNDS as u16)))
            .map(|round| {
                json!({
                    "query_count": round.query_count,
                    "merkle_depth": round.merkle_depth,
                    "ood_samples": round.ood_samples,
                    "opening_count": round.opening_count,
                    "selector_count": round.selector_count,
                    "pow_bits": round.pow_bits,
                    "sumcheck_rounds": round.sumcheck_rounds,
                    "folding_pow_bits": round.folding_pow_bits,
                })
            })
            .collect::<Vec<_>>(),
    })
}

fn phase2_whir_statement_shape() -> Result<Phase2WhirStatementShape> {
    let statement = default_spend_statement();
    let mut arithmetization = default_spend_arithmetization();
    let boundary_layout = spend_boundary_layout(&statement);
    arithmetization.boundary_constraint_groups = boundary_layout.total_groups;
    let application_merkle_paths = statement.spends * statement.note_openings_per_spend;
    let application_hash_gadgets = statement.spends * statement.nullifier_hashes_per_spend
        + statement.outputs * statement.note_commitments_per_output;
    let row_breakdown = [
        application_merkle_paths
            * statement.note_tree_depth
            * arithmetization.merkle_rows_per_level,
        statement.spends
            * statement.nullifier_hashes_per_spend
            * arithmetization.nullifier_hash_rows,
        statement.outputs
            * statement.note_commitments_per_output
            * arithmetization.note_commitment_rows,
        statement.amount_range_checks_64 * arithmetization.range_check_rows,
        statement.ownership_checks * arithmetization.ownership_rows,
        statement.balance_constraints * arithmetization.balance_rows,
        statement.lookup_arguments * arithmetization.lookup_rows,
        arithmetization.misc_rows,
    ];
    let total_rows = row_breakdown.iter().copied().sum::<u64>();
    Ok(Phase2WhirStatementShape {
        spends: statement.spends.try_into().context("spends exceeds u16")?,
        outputs: statement
            .outputs
            .try_into()
            .context("outputs exceeds u16")?,
        note_tree_depth: statement
            .note_tree_depth
            .try_into()
            .context("note_tree_depth exceeds u16")?,
        note_openings_per_spend: statement
            .note_openings_per_spend
            .try_into()
            .context("note_openings_per_spend exceeds u16")?,
        nullifier_hashes_per_spend: statement
            .nullifier_hashes_per_spend
            .try_into()
            .context("nullifier_hashes_per_spend exceeds u16")?,
        note_commitments_per_output: statement
            .note_commitments_per_output
            .try_into()
            .context("note_commitments_per_output exceeds u16")?,
        amount_range_checks_64: statement
            .amount_range_checks_64
            .try_into()
            .context("amount_range_checks_64 exceeds u16")?,
        ownership_checks: statement
            .ownership_checks
            .try_into()
            .context("ownership_checks exceeds u16")?,
        balance_constraints: statement
            .balance_constraints
            .try_into()
            .context("balance_constraints exceeds u16")?,
        lookup_arguments: statement
            .lookup_arguments
            .try_into()
            .context("lookup_arguments exceeds u16")?,
        boundary_constraint_groups: boundary_layout
            .total_groups
            .try_into()
            .context("boundary groups exceeds u16")?,
        application_merkle_paths: application_merkle_paths
            .try_into()
            .context("application_merkle_paths exceeds u16")?,
        application_hash_gadgets: application_hash_gadgets
            .try_into()
            .context("application_hash_gadgets exceeds u16")?,
        evaluation_domain_log2: ceil_log2(total_rows.max(1))
            .try_into()
            .context("evaluation_domain_log2 exceeds u16")?,
        merkle_rows_per_level: arithmetization
            .merkle_rows_per_level
            .try_into()
            .context("merkle_rows_per_level exceeds u16")?,
        nullifier_hash_rows: arithmetization
            .nullifier_hash_rows
            .try_into()
            .context("nullifier_hash_rows exceeds u16")?,
        note_commitment_rows: arithmetization
            .note_commitment_rows
            .try_into()
            .context("note_commitment_rows exceeds u16")?,
        range_check_rows: arithmetization
            .range_check_rows
            .try_into()
            .context("range_check_rows exceeds u16")?,
        ownership_rows: arithmetization
            .ownership_rows
            .try_into()
            .context("ownership_rows exceeds u16")?,
        balance_rows: arithmetization
            .balance_rows
            .try_into()
            .context("balance_rows exceeds u16")?,
        lookup_rows: arithmetization
            .lookup_rows
            .try_into()
            .context("lookup_rows exceeds u16")?,
        misc_rows: arithmetization
            .misc_rows
            .try_into()
            .context("misc_rows exceeds u16")?,
        total_rows: total_rows.try_into().context("total_rows exceeds u32")?,
        row_breakdown: [
            row_breakdown[0]
                .try_into()
                .context("row_breakdown[0] exceeds u32")?,
            row_breakdown[1]
                .try_into()
                .context("row_breakdown[1] exceeds u32")?,
            row_breakdown[2]
                .try_into()
                .context("row_breakdown[2] exceeds u32")?,
            row_breakdown[3]
                .try_into()
                .context("row_breakdown[3] exceeds u32")?,
            row_breakdown[4]
                .try_into()
                .context("row_breakdown[4] exceeds u32")?,
            row_breakdown[5]
                .try_into()
                .context("row_breakdown[5] exceeds u32")?,
            row_breakdown[6]
                .try_into()
                .context("row_breakdown[6] exceeds u32")?,
            row_breakdown[7]
                .try_into()
                .context("row_breakdown[7] exceeds u32")?,
        ],
    })
}

fn phase2_whir_statement_shape_json(shape: Phase2WhirStatementShape) -> serde_json::Value {
    json!({
        "spends": shape.spends,
        "outputs": shape.outputs,
        "note_tree_depth": shape.note_tree_depth,
        "note_openings_per_spend": shape.note_openings_per_spend,
        "nullifier_hashes_per_spend": shape.nullifier_hashes_per_spend,
        "note_commitments_per_output": shape.note_commitments_per_output,
        "amount_range_checks_64": shape.amount_range_checks_64,
        "ownership_checks": shape.ownership_checks,
        "balance_constraints": shape.balance_constraints,
        "lookup_arguments": shape.lookup_arguments,
        "boundary_constraint_groups": shape.boundary_constraint_groups,
        "application_merkle_paths": shape.application_merkle_paths,
        "application_hash_gadgets": shape.application_hash_gadgets,
        "evaluation_domain_log2": shape.evaluation_domain_log2,
        "merkle_rows_per_level": shape.merkle_rows_per_level,
        "nullifier_hash_rows": shape.nullifier_hash_rows,
        "note_commitment_rows": shape.note_commitment_rows,
        "range_check_rows": shape.range_check_rows,
        "ownership_rows": shape.ownership_rows,
        "balance_rows": shape.balance_rows,
        "lookup_rows": shape.lookup_rows,
        "misc_rows": shape.misc_rows,
        "total_rows": shape.total_rows,
        "row_breakdown": shape.row_breakdown,
    })
}

fn pick_best_lift_policy(records: &[EndToEndMeasurement]) -> String {
    let eager = mean_stage(records, "total_sbf", "lift_policy", "eager_qm31");
    let late = mean_stage(records, "total_sbf", "lift_policy", "late_lift_qm31");
    if late <= eager {
        "late_lift_qm31".to_string()
    } else {
        "eager_qm31".to_string()
    }
}

fn pick_best_fold_mode(records: &[EndToEndMeasurement]) -> String {
    let raw = mean_stage(records, "total_sbf", "whir_fold_mode", "raw_fibers");
    let local = mean_stage(records, "total_sbf", "whir_fold_mode", "local_interpolant");
    if local <= raw {
        "local_interpolant".to_string()
    } else {
        "raw_fibers".to_string()
    }
}

fn mean_stage(records: &[EndToEndMeasurement], stage: &str, key: &str, value: &str) -> f64 {
    let values = records
        .iter()
        .filter(|record| record.stage == stage)
        .filter(|record| match key {
            "lift_policy" => record.lift_policy == value,
            "whir_fold_mode" => record.whir_fold_mode == value,
            _ => false,
        })
        .filter_map(|record| record.actual_cu.map(|v| v as f64))
        .collect::<Vec<_>>();
    if values.is_empty() {
        f64::INFINITY
    } else {
        values.iter().sum::<f64>() / values.len() as f64
    }
}

fn pick_best_variant(records: &[EndToEndMeasurement]) -> Result<String> {
    let best = records
        .iter()
        .filter(|record| record.stage == "total_sbf")
        .filter_map(|record| record.actual_cu.map(|actual| (&record.variant, actual)))
        .min_by_key(|(_, actual)| *actual)
        .context("missing total_sbf measurements")?;
    Ok(best.0.clone())
}

fn mean_whir_query_total(
    records: &[WhirQueryMeasurement],
    scenario_name: &str,
    variant_name: &str,
) -> Option<f64> {
    let values = records
        .iter()
        .filter(|record| {
            record.stage == "total_sbf"
                && record.scenario_name == scenario_name
                && record.variant == variant_name
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect::<Vec<_>>();
    if values.is_empty() {
        None
    } else {
        Some(values.iter().sum::<f64>() / values.len() as f64)
    }
}

fn whir_query_translation_summary(records: &[WhirQueryMeasurement]) -> Vec<String> {
    let mut scenarios = records
        .iter()
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();
    let mut lines = Vec::new();
    for scenario in scenarios {
        let baseline = mean_whir_query_total(records, &scenario, "direct_schoolbook_eager");
        let base_only = mean_whir_query_total(records, &scenario, "reference_schoolbook_eager");
        let ext_only = mean_whir_query_total(records, &scenario, "reference_karatsuba_eager");
        let winner = mean_whir_query_total(records, &scenario, "reference_karatsuba_late");
        if let (Some(baseline), Some(base_only), Some(ext_only), Some(winner)) =
            (baseline, base_only, ext_only, winner)
        {
            lines.push(format!(
                "{scenario}: direct/schoolbook/eager {:.0} CU -> reference/schoolbook/eager {:.0} CU -> reference/karatsuba/eager {:.0} CU -> reference/karatsuba/late {:.0} CU",
                baseline, base_only, ext_only, winner
            ));
        }
    }
    lines
}

fn pick_best_whir_query_variant(records: &[WhirQueryMeasurement]) -> String {
    let best = records
        .iter()
        .filter(|record| record.stage == "total_sbf")
        .filter_map(|record| record.actual_cu.map(|actual| (&record.variant, actual)))
        .min_by_key(|(_, actual)| *actual);
    best.map(|(variant, _)| variant.clone())
        .unwrap_or_else(|| "unknown".to_string())
}

fn estimate_savings(
    skeleton: &[EndToEndMeasurement],
    arithmetic: &[ArithmeticMeasurement],
    extension: &[ExtensionMeasurement],
    arithmetic_winner: &str,
    extension_winner: &str,
    lift_policy_winner: &str,
    whir_fold_winner: &str,
) -> Result<SavingsEstimate> {
    let baseline_variant = skeleton
        .iter()
        .find(|record| {
            record.stage == "host_verify"
                && record.extension_kernel_id == "schoolbook"
                && record.lift_policy == "eager_qm31"
                && record.whir_fold_mode == "raw_fibers"
        })
        .context("missing baseline host variant")?;
    let best_variant = skeleton
        .iter()
        .find(|record| {
            record.stage == "host_verify"
                && record.extension_kernel_id == extension_winner
                && record.lift_policy == lift_policy_winner
                && record.whir_fold_mode == whir_fold_winner
        })
        .context("missing best host variant")?;

    let base_mul_ref = mean_arithmetic_cu_per_unit(
        arithmetic,
        arithmetic_winner,
        ArithmeticWorkloadId::SkeletonFoldStep,
    )
    .unwrap_or(1.0);
    let base_mul_baseline = mean_arithmetic_cu_per_unit(
        arithmetic,
        "reference_canonical",
        ArithmeticWorkloadId::SkeletonFoldStep,
    )
    .unwrap_or(base_mul_ref);
    let field_mul_multiplier = (base_mul_ref / base_mul_baseline).min(1.0);

    let extension_kernel_multiplier = mean_extension_cu_per_unit(
        extension,
        extension_winner,
        ExtensionWorkloadId::SkeletonAccumulator,
    )
    .unwrap_or(1.0)
        / mean_extension_cu_per_unit(
            extension,
            "schoolbook",
            ExtensionWorkloadId::SkeletonAccumulator,
        )
        .unwrap_or(1.0);

    let field_op_multiplier = best_variant.field_mul_projection as f64
        / baseline_variant.field_mul_projection.max(1) as f64;
    let extension_op_multiplier = best_variant.extension_mul_projection as f64
        / baseline_variant.extension_mul_projection.max(1) as f64;
    let inv_op_multiplier = best_variant.field_inv_projection as f64
        / baseline_variant.field_inv_projection.max(1) as f64;

    let current_total = 1_450_000.0;
    let current_field_mul = 490_000.0;
    let current_heap = 335_000.0;
    let current_extension = 285_000.0;
    let current_merkle = 140_000.0;
    let current_field_inv = 80_000.0;
    let current_transport = 120_000.0;

    let adjusted_field_mul = current_field_mul * field_mul_multiplier * field_op_multiplier;
    let adjusted_extension =
        current_extension * extension_kernel_multiplier * extension_op_multiplier;
    let adjusted_field_inv = current_field_inv * inv_op_multiplier;
    let adjusted_heap = current_heap * 0.25;
    let adjusted_merkle = current_merkle;
    let adjusted_transport = current_transport;

    let post_change = current_total
        - current_field_mul
        - current_extension
        - current_field_inv
        - current_heap
        - current_merkle
        - current_transport
        + adjusted_field_mul
        + adjusted_extension
        + adjusted_field_inv
        + adjusted_heap
        + adjusted_merkle
        + adjusted_transport;
    let estimated_savings = current_total - post_change;
    let estimated_headroom = SvmLimits::default().max_compute_units_per_tx as f64 - post_change;

    Ok(SavingsEstimate {
        estimated_savings_cu: estimated_savings,
        estimated_headroom_cu: estimated_headroom,
        estimated_post_change_cu: post_change,
        biggest_remaining_risk: "The high-fidelity WHIR path is now bound to the concrete Spend statement shape, but it still is not a native WHIR prover/verifier transcript, so proof-layout and transcript costs can still move when the real query evaluator lands.".to_string(),
    })
}

fn mean_arithmetic_cu_per_unit(
    records: &[ArithmeticMeasurement],
    winner: &str,
    workload: ArithmeticWorkloadId,
) -> Option<f64> {
    let workload = workload_name(workload);
    let values = records
        .iter()
        .filter(|record| {
            record.domain == "sbf" && record.kernel_id == winner && record.workload == workload
        })
        .filter_map(|record| record.cu_per_unit)
        .collect::<Vec<_>>();
    if values.is_empty() {
        None
    } else {
        Some(values.iter().sum::<f64>() / values.len() as f64)
    }
}

fn mean_extension_cu_per_unit(
    records: &[ExtensionMeasurement],
    extension_kernel_id: &str,
    workload: ExtensionWorkloadId,
) -> Option<f64> {
    let workload = extension_workload_name(workload);
    let values = records
        .iter()
        .filter(|record| {
            record.domain == "sbf"
                && record.extension_kernel_id == extension_kernel_id
                && record.workload == workload
        })
        .filter_map(|record| record.cu_per_unit)
        .collect::<Vec<_>>();
    if values.is_empty() {
        None
    } else {
        Some(values.iter().sum::<f64>() / values.len() as f64)
    }
}

fn arithmetic_kernel_name(kernel_id: ArithmeticKernelId) -> &'static str {
    match kernel_id {
        ArithmeticKernelId::ReferenceCanonical => "reference_canonical",
        ArithmeticKernelId::DirectM31 => "direct_m31",
        ArithmeticKernelId::DirectM31Lazy => "direct_m31_lazy",
        ArithmeticKernelId::Montgomery => "montgomery_form",
        ArithmeticKernelId::Barrett => "barrett_reduction",
    }
}

fn reduction_mode_name(mode: ReductionMode) -> &'static str {
    match mode {
        ReductionMode::Canonical => "canonical",
        ReductionMode::DirectM31 => "direct_m31",
        ReductionMode::Montgomery => "montgomery",
        ReductionMode::Barrett => "barrett",
    }
}

fn lazy_mode_name(mode: LazyReductionMode) -> &'static str {
    match mode {
        LazyReductionMode::None => "none",
        LazyReductionMode::Batch4 => "batch4",
    }
}

fn extension_kernel_name(kernel_id: ExtensionKernelId) -> &'static str {
    match kernel_id {
        ExtensionKernelId::Schoolbook => "schoolbook",
        ExtensionKernelId::Karatsuba => "karatsuba",
    }
}

fn lift_policy_name(policy: LiftPolicy) -> &'static str {
    match policy {
        LiftPolicy::EagerQm31 => "eager_qm31",
        LiftPolicy::LateLiftQm31 => "late_lift_qm31",
    }
}

fn fold_mode_name(mode: WhirFoldMode) -> &'static str {
    match mode {
        WhirFoldMode::RawFibers => "raw_fibers",
        WhirFoldMode::LocalInterpolant => "local_interpolant",
    }
}

fn merkle_mode_name(mode: MerkleProofMode) -> &'static str {
    match mode {
        MerkleProofMode::SeparatePaths => "separate_paths",
        MerkleProofMode::MinimalSubtree => "minimal_subtree",
    }
}

fn merkle_payload_format_name(format: WhirMerklePayloadFormat) -> &'static str {
    match format {
        WhirMerklePayloadFormat::FlatNodes => "flat_nodes",
        WhirMerklePayloadFormat::CanonicalPayload => "canonical_payload",
    }
}

fn workload_name(workload: ArithmeticWorkloadId) -> &'static str {
    match workload {
        ArithmeticWorkloadId::Mul => "mul",
        ArithmeticWorkloadId::Square => "square",
        ArithmeticWorkloadId::MulAdd => "mul_add",
        ArithmeticWorkloadId::InnerProduct4 => "inner_product4",
        ArithmeticWorkloadId::Horner4 => "horner4",
        ArithmeticWorkloadId::DenominatorChain4 => "denominator_chain4",
        ArithmeticWorkloadId::SkeletonFoldStep => "skeleton_fold_step",
    }
}

fn extension_workload_name(workload: ExtensionWorkloadId) -> &'static str {
    match workload {
        ExtensionWorkloadId::Cm31Mul => "cm31_mul",
        ExtensionWorkloadId::Cm31Square => "cm31_square",
        ExtensionWorkloadId::Cm31MulConst => "cm31_mul_const",
        ExtensionWorkloadId::Cm31Inv => "cm31_inv",
        ExtensionWorkloadId::Qm31Mul => "qm31_mul",
        ExtensionWorkloadId::Qm31Square => "qm31_square",
        ExtensionWorkloadId::Qm31MulConst => "qm31_mul_const",
        ExtensionWorkloadId::Qm31Inv => "qm31_inv",
        ExtensionWorkloadId::SkeletonAccumulator => "skeleton_accumulator",
    }
}

fn optional_git_hash(path: &Path) -> Option<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(path)
        .arg("rev-parse")
        .arg("HEAD")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn write_generic_jsonl<T: Serialize>(path: &Path, records: &[T]) -> Result<()> {
    let mut file = File::create(path)?;
    for record in records {
        serde_json::to_writer(&mut file, record)?;
        file.write_all(b"\n")?;
    }
    Ok(())
}

fn write_arithmetic_csv(path: &Path, records: &[ArithmeticMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(ArithmeticCsvRow {
            family: record.family.clone(),
            kernel_id: record.kernel_id.clone(),
            reduction_mode: record.reduction_mode.clone(),
            lazy_reduction_mode: record.lazy_reduction_mode.clone(),
            workload: record.workload.clone(),
            domain: record.domain.clone(),
            repetition: record.repetition,
            iterations: record.iterations,
            logical_units: record.logical_units,
            actual_cu: record.actual_cu,
            cu_per_unit: record.cu_per_unit,
            elapsed_ns: record.elapsed_ns,
            ns_per_unit: record.ns_per_unit,
            proof_bytes: record.counters.proof_bytes,
            sha_calls: record.counters.sha_calls,
            merkle_levels: record.counters.merkle_levels,
            m31_add_ops: record.counters.m31_add_ops,
            m31_mul_ops: record.counters.m31_mul_ops,
            m31_square_ops: record.counters.m31_square_ops,
            m31_inv_ops: record.counters.m31_inv_ops,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_extension_csv(path: &Path, records: &[ExtensionMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(ExtensionCsvRow {
            extension_kernel_id: record.extension_kernel_id.clone(),
            workload: record.workload.clone(),
            domain: record.domain.clone(),
            repetition: record.repetition,
            iterations: record.iterations,
            logical_units: record.logical_units,
            actual_cu: record.actual_cu,
            cu_per_unit: record.cu_per_unit,
            elapsed_ns: record.elapsed_ns,
            ns_per_unit: record.ns_per_unit,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            cm31_square_ops: record.counters.cm31_square_ops,
            cm31_inv_ops: record.counters.cm31_inv_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            qm31_square_ops: record.counters.qm31_square_ops,
            qm31_inv_ops: record.counters.qm31_inv_ops,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_end_to_end_csv(path: &Path, records: &[EndToEndMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(EndToEndCsvRow {
            variant: record.variant.clone(),
            arithmetic_kernel_id: record.arithmetic_kernel_id.clone(),
            extension_kernel_id: record.extension_kernel_id.clone(),
            lift_policy: record.lift_policy.clone(),
            whir_fold_mode: record.whir_fold_mode.clone(),
            merkle_proof_mode: record.merkle_proof_mode.clone(),
            stage: record.stage.clone(),
            repetition: record.repetition,
            proof_bytes: record.proof_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
            m31_mul_ops: record.counters.m31_mul_ops,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            field_mul_projection: record.field_mul_projection,
            extension_mul_projection: record.extension_mul_projection,
            field_inv_projection: record.field_inv_projection,
            predicted_cu: record.predicted_cu,
            predicted_component_cu: record.predicted_component_cu,
            predicted_core_cu: record.predicted_core_cu,
            predicted_transport_cu: record.predicted_transport_cu,
            abs_error_cu: record.abs_error_cu,
            rel_error: record.rel_error,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_query_csv(path: &Path, records: &[WhirQueryMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirQueryCsvRow {
            scenario_name: record.scenario_name.clone(),
            variant: record.variant.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            legacy_bound_cu: record.legacy_bound_cu,
            total_explicit_query_count: record.total_explicit_query_count,
            round_query_counts: record
                .round_query_counts
                .iter()
                .map(|value| value.to_string())
                .collect::<Vec<_>>()
                .join("|"),
            arithmetic_kernel_id: record.arithmetic_kernel_id.clone(),
            extension_kernel_id: record.extension_kernel_id.clone(),
            lift_policy: record.lift_policy.clone(),
            whir_fold_mode: record.whir_fold_mode.clone(),
            stage: record.stage.clone(),
            repetition: record.repetition,
            proof_bytes: record.proof_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
            m31_mul_ops: record.counters.m31_mul_ops,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            field_mul_projection: record.field_mul_projection,
            extension_mul_projection: record.extension_mul_projection,
            field_inv_projection: record.field_inv_projection,
            predicted_cu: record.predicted_cu,
            predicted_component_cu: record.predicted_component_cu,
            predicted_core_cu: record.predicted_core_cu,
            predicted_transport_cu: record.predicted_transport_cu,
            abs_error_cu: record.abs_error_cu,
            rel_error: record.rel_error,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_transcript_csv(path: &Path, records: &[WhirTranscriptMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirTranscriptCsvRow {
            scenario_name: record.scenario_name.clone(),
            path_variant: record.path_variant.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            total_explicit_query_count: record.total_explicit_query_count,
            round_query_counts: record
                .round_query_counts
                .iter()
                .map(|value| value.to_string())
                .collect::<Vec<_>>()
                .join("|"),
            commitment_ood_samples: record.commitment_ood_samples,
            proof_bytes: record.proof_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            stage: record.stage.clone(),
            repetition: record.repetition,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
            m31_mul_ops: record.counters.m31_mul_ops,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            field_mul_projection: record.field_mul_projection,
            extension_mul_projection: record.extension_mul_projection,
            field_inv_projection: record.field_inv_projection,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_multiproof_csv(path: &Path, records: &[WhirMultiproofMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirMultiproofCsvRow {
            scenario_name: record.scenario_name.clone(),
            merkle_proof_mode: record.merkle_proof_mode.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            total_explicit_query_count: record.total_explicit_query_count,
            round_query_counts: record
                .round_query_counts
                .iter()
                .map(|value| value.to_string())
                .collect::<Vec<_>>()
                .join("|"),
            commitment_ood_samples: record.commitment_ood_samples,
            proof_bytes: record.proof_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            stage: record.stage.clone(),
            repetition: record.repetition,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            status: record.status.clone(),
            error: record.error.clone(),
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
            m31_mul_ops: record.counters.m31_mul_ops,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            field_mul_projection: record.field_mul_projection,
            extension_mul_projection: record.extension_mul_projection,
            field_inv_projection: record.field_inv_projection,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_multiproof_payload_csv(
    path: &Path,
    records: &[WhirMultiproofPayloadMeasurement],
) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirMultiproofPayloadCsvRow {
            scenario_name: record.scenario_name.clone(),
            merkle_proof_mode: record.merkle_proof_mode.clone(),
            payload_format: record.payload_format.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            total_explicit_query_count: record.total_explicit_query_count,
            round_query_counts: record
                .round_query_counts
                .iter()
                .map(|value| value.to_string())
                .collect::<Vec<_>>()
                .join("|"),
            commitment_ood_samples: record.commitment_ood_samples,
            payload_bytes: record.payload_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            stage: record.stage.clone(),
            repetition: record.repetition,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            status: record.status.clone(),
            error: record.error.clone(),
            parser_bytes: record.counters.parser_bytes,
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_fold_payload_csv(path: &Path, records: &[WhirFoldPayloadMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirFoldPayloadCsvRow {
            scenario_name: record.scenario_name.clone(),
            whir_fold_mode: record.whir_fold_mode.clone(),
            merkle_proof_mode: record.merkle_proof_mode.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            total_explicit_query_count: record.total_explicit_query_count,
            round_query_counts: record
                .round_query_counts
                .iter()
                .map(|value| value.to_string())
                .collect::<Vec<_>>()
                .join("|"),
            commitment_ood_samples: record.commitment_ood_samples,
            proof_bytes: record.proof_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            stage: record.stage.clone(),
            repetition: record.repetition,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            status: record.status.clone(),
            error: record.error.clone(),
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
            m31_mul_ops: record.counters.m31_mul_ops,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            field_mul_projection: record.field_mul_projection,
            extension_mul_projection: record.extension_mul_projection,
            field_inv_projection: record.field_inv_projection,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_full_reuse_csv(path: &Path, records: &[WhirFullReuseMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirFullReuseCsvRow {
            scenario_name: record.scenario_name.clone(),
            path_variant: record.path_variant.clone(),
            whir_fold_mode: record.whir_fold_mode.clone(),
            merkle_proof_mode: record.merkle_proof_mode.clone(),
            query_reuse_mode: record.query_reuse_mode.clone(),
            query_precompute_mode: record.query_precompute_mode.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            total_explicit_query_count: record.total_explicit_query_count,
            round_query_counts: record
                .round_query_counts
                .iter()
                .map(|value| value.to_string())
                .collect::<Vec<_>>()
                .join("|"),
            commitment_ood_samples: record.commitment_ood_samples,
            proof_bytes: record.proof_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            stage: record.stage.clone(),
            repetition: record.repetition,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            status: record.status.clone(),
            error: record.error.clone(),
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
            m31_mul_ops: record.counters.m31_mul_ops,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            field_mul_projection: record.field_mul_projection,
            extension_mul_projection: record.extension_mul_projection,
            field_inv_projection: record.field_inv_projection,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_mul_taxonomy_csv(path: &Path, records: &[WhirMulTaxonomyMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirMulTaxonomyCsvRow {
            scenario_name: record.scenario_name.clone(),
            whir_fold_mode: record.whir_fold_mode.clone(),
            merkle_proof_mode: record.merkle_proof_mode.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            total_explicit_query_count: record.total_explicit_query_count,
            total_sbf_mean_cu: record.total_sbf_mean_cu,
            total_sbf_stddev_cu: record.total_sbf_stddev_cu,
            proof_bytes: record.proof_bytes,
            total_classified_multiplies: record.total_classified_multiplies,
            general: record.general,
            zero_one_negone: record.zero_one_negone,
            square: record.square,
            sparse_const: record.sparse_const,
            twiddle: record.twiddle,
            bary_weight: record.bary_weight,
            challenge_power: record.challenge_power,
            cm31_structured: record.cm31_structured,
            qm31_structured: record.qm31_structured,
            general_extension: record.general_extension,
            structured_share: record.structured_share,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn write_whir_round0_csv(path: &Path, records: &[WhirRound0Measurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(WhirRound0CsvRow {
            scenario_name: record.scenario_name.clone(),
            round0_variant: record.round0_variant.clone(),
            whir_fold_mode: record.whir_fold_mode.clone(),
            merkle_proof_mode: record.merkle_proof_mode.clone(),
            security_target_bits: record.security_target_bits,
            soundness_assumption: record.soundness_assumption.clone(),
            round_index: record.round_index,
            round_query_count: record.round_query_count,
            round_merkle_depth: record.round_merkle_depth,
            round_ood_samples: record.round_ood_samples,
            round_selector_count: record.round_selector_count,
            round_pow_bits: record.round_pow_bits,
            round_sumcheck_rounds: record.round_sumcheck_rounds,
            round_folding_pow_bits: record.round_folding_pow_bits,
            proof_bytes: record.proof_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            heap_pages_32k: record.heap_pages_32k,
            stage: record.stage.clone(),
            repetition: record.repetition,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            status: record.status.clone(),
            error: record.error.clone(),
            sha_calls: record.counters.sha_calls,
            sha_bytes: record.counters.sha_bytes,
            merkle_levels: record.counters.merkle_levels,
            m31_mul_ops: record.counters.m31_mul_ops,
            cm31_mul_ops: record.counters.cm31_mul_ops,
            qm31_mul_ops: record.counters.qm31_mul_ops,
            field_mul_projection: record.field_mul_projection,
            extension_mul_projection: record.extension_mul_projection,
            field_inv_projection: record.field_inv_projection,
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn load_jsonl_records<T>(path: &Path) -> Result<Vec<T>>
where
    T: for<'de> Deserialize<'de>,
{
    let contents = fs::read_to_string(path)
        .with_context(|| format!("failed to read JSONL records from {}", path.display()))?;
    contents
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| serde_json::from_str(line).map_err(anyhow::Error::from))
        .collect()
}

fn extract_units_remaining(line: &str) -> Option<u64> {
    let marker = "units remaining";
    let end = line.find(marker)?;
    let prefix = &line[..end];
    let digits = prefix
        .chars()
        .rev()
        .skip_while(|ch| !ch.is_ascii_digit())
        .take_while(|ch| ch.is_ascii_digit())
        .collect::<String>()
        .chars()
        .rev()
        .collect::<String>();
    digits.parse().ok()
}

fn parse_whir_transcript_phase_trace(logs: &[String]) -> Result<BTreeMap<String, u64>> {
    let mut phases = BTreeMap::new();
    let mut previous_remaining = None;
    for (index, line) in logs.iter().enumerate() {
        if line.contains("phase2-whir-transcript start") {
            previous_remaining = Some(
                logs[index + 1..]
                    .iter()
                    .find_map(|entry| extract_units_remaining(entry))
                    .context("missing initial transcript CU trace")?,
            );
            continue;
        }
        if let Some(label) = line.split("phase2-whir-transcript stage ").nth(1) {
            let remaining = logs[index + 1..]
                .iter()
                .find_map(|entry| extract_units_remaining(entry))
                .with_context(|| format!("missing stage CU trace for `{label}`"))?;
            let start = previous_remaining
                .context("missing initial transcript CU trace before stage marker")?;
            if start < remaining {
                bail!(
                    "invalid CU trace for `{label}`: start {start} < end {remaining}; logs={}",
                    logs.join(" | ")
                );
            }
            *phases.entry(format!("phase_{}", label.trim())).or_insert(0) += start - remaining;
            previous_remaining = Some(remaining);
        }
    }
    if phases.is_empty() {
        bail!("no WHIR transcript phase CU traces found in logs");
    }
    if previous_remaining.is_none() {
        bail!("missing initial WHIR transcript CU trace marker");
    }
    Ok(phases)
}

fn whir_transcript_stage_values<'a>(
    records: &'a [WhirTranscriptMeasurement],
    scenario_name: &str,
    path_variant: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == path_variant
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn sample_mean(values: &[f64]) -> Option<f64> {
    if values.is_empty() {
        None
    } else {
        Some(values.iter().sum::<f64>() / values.len() as f64)
    }
}

fn sample_stddev(values: &[f64]) -> Option<f64> {
    if values.len() < 2 {
        return Some(0.0);
    }
    let mean = sample_mean(values)?;
    let variance = values
        .iter()
        .map(|value| {
            let delta = value - mean;
            delta * delta
        })
        .sum::<f64>()
        / (values.len() - 1) as f64;
    Some(variance.sqrt())
}

fn scenario_names_from_transcript(records: &[WhirTranscriptMeasurement]) -> Vec<String> {
    let mut scenarios = records
        .iter()
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();
    scenarios
}

fn whir_transcript_comparison_summary(records: &[WhirTranscriptMeasurement]) -> Vec<String> {
    let mut lines = Vec::new();
    for scenario in scenario_names_from_transcript(records) {
        let query_values =
            whir_transcript_stage_values(records, &scenario, "query_only", "total_sbf");
        let transcript_values =
            whir_transcript_stage_values(records, &scenario, "transcript_full", "total_sbf");
        if let (
            Some(query_mean),
            Some(query_stddev),
            Some(transcript_mean),
            Some(transcript_stddev),
        ) = (
            sample_mean(&query_values),
            sample_stddev(&query_values),
            sample_mean(&transcript_values),
            sample_stddev(&transcript_values),
        ) {
            let delta = transcript_mean - query_mean;
            lines.push(format!(
                "{scenario}: query-only {:.0} +- {:.0} CU -> transcript-inclusive {:.0} +- {:.0} CU (delta {:+.0} CU)",
                query_mean, query_stddev, transcript_mean, transcript_stddev, delta
            ));
        }
    }
    lines
}

fn whir_transcript_margin_summary(records: &[WhirTranscriptMeasurement]) -> Vec<String> {
    const CAP: f64 = 1_400_000.0;
    let mut lines = Vec::new();
    for scenario in scenario_names_from_transcript(records) {
        let transcript_values =
            whir_transcript_stage_values(records, &scenario, "transcript_full", "total_sbf");
        if let (Some(transcript_mean), Some(transcript_stddev)) = (
            sample_mean(&transcript_values),
            sample_stddev(&transcript_values),
        ) {
            lines.push(format!(
                "{scenario}: transcript-inclusive {:.0} +- {:.0} CU leaves {:.0} CU mean margin against the 1.4M cap",
                transcript_mean,
                transcript_stddev,
                CAP - transcript_mean
            ));
        }
    }
    lines
}

fn render_whir_transcript_section(records: &[WhirTranscriptMeasurement]) -> String {
    let comparison = whir_transcript_comparison_summary(records);
    let margin = whir_transcript_margin_summary(records);
    let mut lines = Vec::new();
    lines.push("## WHIR Transcript Path".to_string());
    lines.push("- Executed: transcript absorption/challenge derivation, commitment OOD checks, per-round query PoW checks, folding verification across all rounds, final-round query verification, and transcript consistency checks on SBF.".to_string());
    lines.push("- Executed: repo-local valid/invalid proof validation. Valid proofs were accepted; deliberately wrong challenge, missing-query, incorrect-folding, and truncated proofs were rejected.".to_string());
    lines.push("- Scaffolded: external proof interop with the official Plonky3 WHIR prover/verifier was not executed because `/tmp/plonky3-official` at commit `0f87f2b543a01880274965c410bf804c124f5046` does not contain the referenced `whir/src/verifier/mod.rs` entrypoint or a runnable end-to-end WHIR prover/verifier surface.".to_string());
    lines.push("- Honest caveat: the current PoW step checks transcript-bound witness consistency inside the verifier path, not full prover-side grinding cost.".to_string());
    if !comparison.is_empty() {
        lines.push(String::new());
        lines.push("### Query-Only vs Transcript-Inclusive".to_string());
        for line in comparison {
            lines.push(format!("- {line}."));
        }
    }
    let stage_order = [
        ("phase_parse", "parse"),
        ("phase_transcript_setup", "transcript setup"),
        ("phase_ood", "OOD"),
        ("phase_per_round_queries", "per-round queries"),
        ("phase_folding", "folding"),
        ("phase_final_round", "final round"),
    ];
    for scenario in scenario_names_from_transcript(records) {
        lines.push(String::new());
        lines.push(format!("### {scenario}"));
        for (stage, label) in stage_order {
            let values = whir_transcript_stage_values(records, &scenario, "transcript_full", stage);
            if let (Some(mean), Some(stddev)) = (sample_mean(&values), sample_stddev(&values)) {
                lines.push(format!("- {label}: {:.0} +- {:.0} CU.", mean, stddev));
            }
        }
        if let Some(line) = margin.iter().find(|line| line.starts_with(&scenario)) {
            lines.push(format!("- {line}."));
        }
    }
    lines.join("\n")
}

fn replace_markdown_section(document: &str, heading: &str, replacement: &str) -> String {
    if let Some(start) = document.find(heading) {
        let next = document[start + heading.len()..]
            .find("\n## ")
            .map(|offset| start + heading.len() + offset + 1)
            .unwrap_or(document.len());
        let separator = if next < document.len() && !replacement.ends_with('\n') {
            "\n"
        } else {
            ""
        };
        format!(
            "{}{}{}{}",
            &document[..start],
            replacement,
            separator,
            &document[next..]
        )
    } else if document.trim().is_empty() {
        replacement.to_string()
    } else {
        format!("{document}\n\n{replacement}")
    }
}

fn write_phase2_transcript_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    phase1_summary: &Phase1Summary,
    run_config: &Phase2RunConfig,
    records: &[WhirTranscriptMeasurement],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    let comparison = whir_transcript_comparison_summary(records);
    let margin = whir_transcript_margin_summary(records);
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_transcript_comparison_summary"] = json!(comparison);
    summary_value["whir_transcript_remaining_margin_summary"] = json!(margin);
    summary_value["biggest_remaining_risk"] = json!("The transcript-inclusive verifier path is measured on SBF, but external proof interop is still blocked by the missing end-to-end verifier/prover entrypoint in `/tmp/plonky3-official`.");
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-transcript/scenarios.json",
        "results/phase2/whir-transcript/raw.jsonl",
        "results/phase2/whir-transcript/raw.csv",
        "results/phase2/whir-transcript/proofs/",
        "results/phase2/whir-transcript/validation.json",
        "results/phase2/manifests/",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|entry| entry == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    write_json(&summary_path, &summary_value)?;

    let transcript_section = render_whir_transcript_section(records);
    let docs = if docs_path.exists() {
        replace_markdown_section(
            &fs::read_to_string(docs_path)?,
            "## WHIR Transcript Path",
            &transcript_section,
        )
    } else {
        format!(
            "# Phase 2 Experiments\n\n## Goal\nRun the Phase 2 verifier experiments against the Phase 1 spend model and report measured SBF CU.\n\n## Baseline\n- Phase 1 chosen model: `{}` with RMSE {:.1} CU.\n- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}.\n\n{}",
            phase1_summary.model.chosen.method,
            phase1_summary.model.chosen.metrics.rmse,
            run_config.proof_plan.query_count,
            run_config.proof_plan.fold_arity,
            run_config.proof_plan.target_proof_bytes,
            transcript_section
        )
    };
    fs::write(docs_path, docs)?;
    Ok(())
}

fn scenario_names_from_multiproof(records: &[WhirMultiproofMeasurement]) -> Vec<String> {
    let mut scenarios = records
        .iter()
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();
    scenarios
}

fn whir_multiproof_stage_values(
    records: &[WhirMultiproofMeasurement],
    scenario_name: &str,
    merkle_mode: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.merkle_proof_mode == merkle_mode
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn whir_multiproof_status_counts(
    records: &[WhirMultiproofMeasurement],
    scenario_name: &str,
    merkle_mode: &str,
    stage: &str,
) -> (usize, usize) {
    let filtered = records.iter().filter(|record| {
        record.scenario_name == scenario_name
            && record.merkle_proof_mode == merkle_mode
            && record.stage == stage
    });
    let total = filtered.clone().count();
    let ok = filtered.filter(|record| record.status == "ok").count();
    (ok, total)
}

fn whir_multiproof_proof_bytes(
    records: &[WhirMultiproofMeasurement],
    scenario_name: &str,
    merkle_mode: &str,
) -> Option<u64> {
    records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.merkle_proof_mode == merkle_mode
                && record.stage == "host_verify"
        })
        .map(|record| record.proof_bytes)
}

fn whir_multiproof_has_trace_gap(
    records: &[WhirMultiproofMeasurement],
    scenario_name: &str,
    merkle_mode: &str,
) -> bool {
    records.iter().any(|record| {
        record.scenario_name == scenario_name
            && record.merkle_proof_mode == merkle_mode
            && record.stage == "trace_incomplete"
    })
}

fn whir_multiproof_stage_error(
    records: &[WhirMultiproofMeasurement],
    scenario_name: &str,
    merkle_mode: &str,
    stage: &str,
) -> Option<String> {
    records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.merkle_proof_mode == merkle_mode
                && record.stage == stage
        })
        .and_then(|record| record.error.clone())
}

fn whir_multiproof_comparison_summary(records: &[WhirMultiproofMeasurement]) -> Vec<String> {
    let mut lines = Vec::new();
    for scenario in scenario_names_from_multiproof(records) {
        let separate_total = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            "total_sbf",
        );
        let minimal_total = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
            "total_sbf",
        );
        let separate_per_round = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            "phase_per_round_queries",
        );
        let minimal_per_round = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
            "phase_per_round_queries",
        );
        let separate_upload = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            "upload_total",
        );
        let minimal_upload = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
            "upload_total",
        );
        let separate_proof = whir_multiproof_proof_bytes(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
        );
        let minimal_proof = whir_multiproof_proof_bytes(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
        );
        let (separate_ok, separate_total_reps) = whir_multiproof_status_counts(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            "verify_sbf",
        );
        let (minimal_ok, minimal_total_reps) = whir_multiproof_status_counts(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
            "verify_sbf",
        );
        if let (Some(separate_mean), Some(minimal_mean)) =
            (sample_mean(&separate_total), sample_mean(&minimal_total))
        {
            let total_delta = minimal_mean - separate_mean;
            let per_round_delta = match (
                sample_mean(&separate_per_round),
                sample_mean(&minimal_per_round),
            ) {
                (Some(separate), Some(minimal)) => {
                    format!(
                        "per-round {:.0} -> {:.0} CU (delta {:+.0})",
                        separate,
                        minimal,
                        minimal - separate
                    )
                }
                _ => "per-round trace incomplete".to_string(),
            };
            let upload_delta = match (sample_mean(&separate_upload), sample_mean(&minimal_upload)) {
                (Some(separate), Some(minimal)) => {
                    format!(
                        "upload {:.0} -> {:.0} CU (delta {:+.0})",
                        separate,
                        minimal,
                        minimal - separate
                    )
                }
                _ => "upload unavailable".to_string(),
            };
            let proof_delta = match (separate_proof, minimal_proof) {
                (Some(separate), Some(minimal)) => {
                    format!(
                        "proof {separate} -> {minimal} bytes (delta {:+})",
                        minimal as i64 - separate as i64
                    )
                }
                _ => "proof bytes unavailable".to_string(),
            };
            lines.push(format!(
                "{scenario}: total {:.0} -> {:.0} CU (delta {:+.0}); {per_round_delta}; {proof_delta}; {upload_delta}; verify ok {separate_ok}/{separate_total_reps} -> {minimal_ok}/{minimal_total_reps}",
                separate_mean,
                minimal_mean,
                total_delta,
            ));
        }
    }
    lines
}

fn whir_multiproof_margin_summary(records: &[WhirMultiproofMeasurement]) -> Vec<String> {
    const CAP: f64 = 1_400_000.0;
    let mut lines = Vec::new();
    for scenario in scenario_names_from_multiproof(records) {
        let separate_total = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            "total_sbf",
        );
        let minimal_total = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
            "total_sbf",
        );
        if let (Some(separate_mean), Some(minimal_mean)) =
            (sample_mean(&separate_total), sample_mean(&minimal_total))
        {
            lines.push(format!(
                "{scenario}: separate_paths leaves {:.0} CU mean margin, minimal_subtree leaves {:.0} CU mean margin against the 1.4M cap",
                CAP - separate_mean,
                CAP - minimal_mean
            ));
        }
    }
    lines
}

fn render_whir_multiproof_section(records: &[WhirMultiproofMeasurement]) -> String {
    let comparison = whir_multiproof_comparison_summary(records);
    let margin = whir_multiproof_margin_summary(records);
    let stage_order = [
        ("phase_parse", "parse"),
        ("phase_transcript_setup", "transcript setup"),
        ("phase_ood", "OOD"),
        ("phase_per_round_queries", "per-round queries"),
        ("phase_folding", "folding"),
        ("phase_final_round", "final round"),
    ];
    let mut lines = Vec::new();
    lines.push("## WHIR Merkle Multiproof".to_string());
    lines.push("- Executed: the full WHIR transcript verifier path was rerun with the same winning kernels and statement binding, comparing `separate_paths` against `minimal_subtree` Merkle verification on SBF.".to_string());
    lines.push("- Executed: repo-local valid/invalid proof validation for both Merkle modes. Valid proofs were accepted; deliberately wrong challenge, missing-query, incorrect-folding, and truncated proofs were rejected.".to_string());
    lines.push("- Executed: a no-heap control run for each variant and Johnson-only segment diagnostics that replay each round plus the final round from captured transcript checkpoints.".to_string());
    lines.push("- Honest caveat: the repo-local synthetic proof now serializes mode-specific Merkle witness bytes, but total proof sizing is still profile-shaped from synthetic node counts rather than an external prover-emitted multiproof payload.".to_string());
    if !comparison.is_empty() {
        lines.push(String::new());
        lines.push("### Separate Paths vs Minimal Subtree".to_string());
        for line in comparison {
            lines.push(format!("- {line}."));
        }
    }
    for scenario in scenario_names_from_multiproof(records) {
        lines.push(String::new());
        lines.push(format!("### {scenario}"));
        for merkle_mode in [
            MerkleProofMode::SeparatePaths,
            MerkleProofMode::MinimalSubtree,
        ] {
            let mode_name = merkle_mode_name(merkle_mode);
            let total_values =
                whir_multiproof_stage_values(records, &scenario, mode_name, "total_sbf");
            let per_round_values = whir_multiproof_stage_values(
                records,
                &scenario,
                mode_name,
                "phase_per_round_queries",
            );
            let upload_values =
                whir_multiproof_stage_values(records, &scenario, mode_name, "upload_total");
            let proof_bytes = whir_multiproof_proof_bytes(records, &scenario, mode_name);
            let (verify_ok, verify_total) =
                whir_multiproof_status_counts(records, &scenario, mode_name, "verify_sbf");

            if let (Some(total_mean), Some(total_stddev)) =
                (sample_mean(&total_values), sample_stddev(&total_values))
            {
                let per_round = match (
                    sample_mean(&per_round_values),
                    sample_stddev(&per_round_values),
                ) {
                    (Some(mean), Some(stddev)) => {
                        format!(", per-round queries {:.0} +- {:.0} CU", mean, stddev)
                    }
                    _ => String::new(),
                };
                let upload = sample_mean(&upload_values)
                    .map(|mean| format!(", upload {:.0} CU", mean))
                    .unwrap_or_default();
                let proof = proof_bytes
                    .map(|value| format!(", proof {value} bytes"))
                    .unwrap_or_default();
                lines.push(format!(
                    "- {mode_name}: total {:.0} +- {:.0} CU{per_round}{upload}{proof}, verify ok {verify_ok}/{verify_total}.",
                    total_mean, total_stddev
                ));
            }

            let mut phase_parts = Vec::new();
            for (stage, label) in stage_order {
                let values = whir_multiproof_stage_values(records, &scenario, mode_name, stage);
                if let (Some(mean), Some(stddev)) = (sample_mean(&values), sample_stddev(&values)) {
                    phase_parts.push(format!("{label} {:.0} +- {:.0} CU", mean, stddev));
                }
            }
            if !phase_parts.is_empty() {
                lines.push(format!(
                    "- {mode_name} phase breakdown: {}.",
                    phase_parts.join(", ")
                ));
            }

            let no_heap_verify =
                whir_multiproof_stage_values(records, &scenario, mode_name, "verify_sbf_no_heap");
            let no_heap_total =
                whir_multiproof_stage_values(records, &scenario, mode_name, "total_sbf_no_heap");
            let (no_heap_ok, no_heap_reps) =
                whir_multiproof_status_counts(records, &scenario, mode_name, "verify_sbf_no_heap");
            if no_heap_reps > 0 {
                let verify = sample_mean(&no_heap_verify)
                    .map(|mean| format!("verify {:.0} CU", mean))
                    .unwrap_or_else(|| "verify unavailable".to_string());
                let total = sample_mean(&no_heap_total)
                    .map(|mean| format!(", total {:.0} CU", mean))
                    .unwrap_or_default();
                lines.push(format!(
                    "- {mode_name} no-heap control: {verify}{total}, status {no_heap_ok}/{no_heap_reps}."
                ));
                if let Some(error) =
                    whir_multiproof_stage_error(records, &scenario, mode_name, "verify_sbf_no_heap")
                {
                    lines.push(format!("- {mode_name} no-heap error: `{error}`."));
                }
            }

            let mut diagnostic_records = records
                .iter()
                .filter(|record| {
                    record.scenario_name == scenario
                        && record.merkle_proof_mode == mode_name
                        && record.stage.starts_with("diagnostic_")
                })
                .collect::<Vec<_>>();
            diagnostic_records.sort_by_key(|record| {
                if let Some(index) = record.stage.strip_prefix("diagnostic_round_") {
                    index.parse::<u32>().unwrap_or(u32::MAX)
                } else {
                    u32::MAX
                }
            });
            for record in diagnostic_records {
                let actual = record
                    .actual_cu
                    .map(|value| format!("{value} CU"))
                    .unwrap_or_else(|| "CU unavailable".to_string());
                lines.push(format!(
                    "- {mode_name} {}: {actual}, status {}.",
                    record.stage, record.status
                ));
                if let Some(error) = &record.error {
                    lines.push(format!("- {mode_name} {} error: `{error}`.", record.stage));
                }
            }
        }

        let separate_total = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            "total_sbf",
        );
        let minimal_total = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
            "total_sbf",
        );
        let separate_upload = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            "upload_total",
        );
        let minimal_upload = whir_multiproof_stage_values(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
            "upload_total",
        );
        let separate_proof = whir_multiproof_proof_bytes(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
        );
        let minimal_proof = whir_multiproof_proof_bytes(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
        );
        if let (Some(separate_mean), Some(minimal_mean)) =
            (sample_mean(&separate_total), sample_mean(&minimal_total))
        {
            let proof_delta = match (separate_proof, minimal_proof) {
                (Some(separate), Some(minimal)) => {
                    format!(", proof delta {:+} bytes", minimal as i64 - separate as i64)
                }
                _ => String::new(),
            };
            let upload_delta = match (sample_mean(&separate_upload), sample_mean(&minimal_upload)) {
                (Some(separate), Some(minimal)) => {
                    format!(", upload delta {:+.0} CU", minimal - separate)
                }
                _ => String::new(),
            };
            lines.push(format!(
                "- delta: total {:+.0} CU{proof_delta}{upload_delta}.",
                minimal_mean - separate_mean
            ));
        }
        if whir_multiproof_has_trace_gap(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::SeparatePaths),
        ) || whir_multiproof_has_trace_gap(
            records,
            &scenario,
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
        ) {
            lines.push("- Some traced runs terminated before all phase markers were emitted; missing per-phase rows should be read as incomplete traces rather than zero cost.".to_string());
        }
        if let Some(line) = margin.iter().find(|line| line.starts_with(&scenario)) {
            lines.push(format!("- {line}."));
        }
    }
    lines.join("\n")
}

fn write_phase2_multiproof_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    phase1_summary: &Phase1Summary,
    run_config: &Phase2RunConfig,
    records: &[WhirMultiproofMeasurement],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    let comparison = whir_multiproof_comparison_summary(records);
    let margin = whir_multiproof_margin_summary(records);
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_multiproof_comparison_summary"] = json!(comparison);
    summary_value["whir_multiproof_remaining_margin_summary"] = json!(margin);
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-multiproof/scenarios.json",
        "results/phase2/whir-multiproof/raw.jsonl",
        "results/phase2/whir-multiproof/raw.csv",
        "results/phase2/whir-multiproof/diagnostics.json",
        "results/phase2/whir-multiproof/proofs/",
        "results/phase2/whir-multiproof/validation.json",
        "results/phase2/manifests/",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|entry| entry == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    summary_value["biggest_remaining_risk"] = json!("Merkle multiproof savings are now measured on the transcript path with explicit synthetic witness bytes, but external prover-emitted multiproof payloads and proof-carried fold representations are still missing.");
    write_json(&summary_path, &summary_value)?;

    let multiproof_section = render_whir_multiproof_section(records);
    let docs = if docs_path.exists() {
        let docs = fs::read_to_string(docs_path)?;
        let docs = replace_markdown_section(
            &docs,
            "## Optional Experiment Results",
            "## Optional Experiment Results\n- Merkle multiproof / `minimal_subtree` was executed via `cargo xtask phase2-multiproof`; the measured results are summarized in the dedicated section below.\n- A no-heap control and Johnson segment diagnostics were executed in the same run.\n- External prover-emitted multiproof payloads remain scaffolded; the current proof bytes are still repo-local synthetic layouts.",
        );
        replace_markdown_section(&docs, "## WHIR Merkle Multiproof", &multiproof_section)
    } else {
        format!(
            "# Phase 2 Experiments\n\n## Goal\nRun the Phase 2 verifier experiments against the Phase 1 spend model and report measured SBF CU.\n\n## Baseline\n- Phase 1 chosen model: `{}` with RMSE {:.1} CU.\n- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}.\n\n{}",
            phase1_summary.model.chosen.method,
            phase1_summary.model.chosen.metrics.rmse,
            run_config.proof_plan.query_count,
            run_config.proof_plan.fold_arity,
            run_config.proof_plan.target_proof_bytes,
            multiproof_section
        )
    };
    fs::write(docs_path, docs)?;
    Ok(())
}

fn scenario_names_from_multiproof_payload(
    records: &[WhirMultiproofPayloadMeasurement],
) -> Vec<String> {
    let mut scenarios = records
        .iter()
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();
    scenarios
}

fn whir_multiproof_payload_stage_values(
    records: &[WhirMultiproofPayloadMeasurement],
    scenario_name: &str,
    merkle_mode: &str,
    payload_format: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.merkle_proof_mode == merkle_mode
                && record.payload_format == payload_format
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn whir_multiproof_payload_bytes(
    records: &[WhirMultiproofPayloadMeasurement],
    scenario_name: &str,
    merkle_mode: &str,
    payload_format: &str,
) -> Option<u64> {
    records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.merkle_proof_mode == merkle_mode
                && record.payload_format == payload_format
                && record.stage == "host_parse"
        })
        .map(|record| record.payload_bytes)
}

fn whir_multiproof_payload_comparison_summary(
    records: &[WhirMultiproofPayloadMeasurement],
) -> Vec<String> {
    let mut lines = Vec::new();
    for scenario in scenario_names_from_multiproof_payload(records) {
        for merkle_mode in [
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
        ] {
            let flat_parse = whir_multiproof_payload_stage_values(
                records,
                &scenario,
                merkle_mode,
                merkle_payload_format_name(WhirMerklePayloadFormat::FlatNodes),
                "parse_sbf",
            );
            let canonical_parse = whir_multiproof_payload_stage_values(
                records,
                &scenario,
                merkle_mode,
                merkle_payload_format_name(WhirMerklePayloadFormat::CanonicalPayload),
                "parse_sbf",
            );
            let flat_total = whir_multiproof_payload_stage_values(
                records,
                &scenario,
                merkle_mode,
                merkle_payload_format_name(WhirMerklePayloadFormat::FlatNodes),
                "total_sbf",
            );
            let canonical_total = whir_multiproof_payload_stage_values(
                records,
                &scenario,
                merkle_mode,
                merkle_payload_format_name(WhirMerklePayloadFormat::CanonicalPayload),
                "total_sbf",
            );
            if let (Some(flat_parse_mean), Some(canonical_parse_mean)) =
                (sample_mean(&flat_parse), sample_mean(&canonical_parse))
            {
                let flat_bytes = whir_multiproof_payload_bytes(
                    records,
                    &scenario,
                    merkle_mode,
                    merkle_payload_format_name(WhirMerklePayloadFormat::FlatNodes),
                )
                .unwrap_or_default();
                let canonical_bytes = whir_multiproof_payload_bytes(
                    records,
                    &scenario,
                    merkle_mode,
                    merkle_payload_format_name(WhirMerklePayloadFormat::CanonicalPayload),
                )
                .unwrap_or_default();
                let total_delta = match (sample_mean(&flat_total), sample_mean(&canonical_total)) {
                    (Some(flat), Some(canonical)) => {
                        format!(
                            ", total {:.0} -> {:.0} CU (delta {:+.0})",
                            flat,
                            canonical,
                            canonical - flat
                        )
                    }
                    _ => String::new(),
                };
                lines.push(format!(
                    "{scenario} {merkle_mode}: flat {flat_bytes} bytes -> canonical {canonical_bytes} bytes (delta {:+}), parse {:.0} -> {:.0} CU (delta {:+.0}){total_delta}",
                    canonical_bytes as i64 - flat_bytes as i64,
                    flat_parse_mean,
                    canonical_parse_mean,
                    canonical_parse_mean - flat_parse_mean,
                ));
            }
        }
    }
    lines
}

fn render_whir_multiproof_payload_section(records: &[WhirMultiproofPayloadMeasurement]) -> String {
    let comparison = whir_multiproof_payload_comparison_summary(records);
    let mut lines = Vec::new();
    lines.push("## WHIR Multiproof Payload".to_string());
    lines.push("- Executed: a prover-emitted-style Merkle payload parser benchmark on SBF, comparing the existing flat-node witness bytes against a repo-local canonical payload that carries per-section metadata and canonical query/node ordering.".to_string());
    lines.push("- Executed: both `separate_paths` and `minimal_subtree` payloads across the three transcript scenarios, with host validation plus valid/invalid parser checks.".to_string());
    lines.push("- Honest caveat: this is still a repo-local canonical payload rather than an official Plonky3 prover-emitted multiproof format; the value here is parser and upload cost, not interoperability.".to_string());
    if !comparison.is_empty() {
        lines.push(String::new());
        lines.push("### Flat Nodes vs Canonical Payload".to_string());
        for line in comparison {
            lines.push(format!("- {line}."));
        }
    }
    lines.join("\n")
}

fn write_phase2_multiproof_payload_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    phase1_summary: &Phase1Summary,
    run_config: &Phase2RunConfig,
    records: &[WhirMultiproofPayloadMeasurement],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    let comparison = whir_multiproof_payload_comparison_summary(records);
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_multiproof_payload_summary"] = json!(comparison);
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-multiproof-payload/scenarios.json",
        "results/phase2/whir-multiproof-payload/raw.jsonl",
        "results/phase2/whir-multiproof-payload/raw.csv",
        "results/phase2/whir-multiproof-payload/payloads/",
        "results/phase2/whir-multiproof-payload/validation.json",
        "results/phase2/manifests/",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|entry| entry == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    write_json(&summary_path, &summary_value)?;

    let payload_section = render_whir_multiproof_payload_section(records);
    let docs = if docs_path.exists() {
        replace_markdown_section(
            &fs::read_to_string(docs_path)?,
            "## WHIR Multiproof Payload",
            &payload_section,
        )
    } else {
        format!(
            "# Phase 2 Experiments\n\n## Goal\nRun the Phase 2 verifier experiments against the Phase 1 spend model and report measured SBF CU.\n\n## Baseline\n- Phase 1 chosen model: `{}` with RMSE {:.1} CU.\n- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}.\n\n{}",
            phase1_summary.model.chosen.method,
            phase1_summary.model.chosen.metrics.rmse,
            run_config.proof_plan.query_count,
            run_config.proof_plan.fold_arity,
            run_config.proof_plan.target_proof_bytes,
            payload_section
        )
    };
    fs::write(docs_path, docs)?;
    Ok(())
}

fn scenario_names_from_fold_payload(records: &[WhirFoldPayloadMeasurement]) -> Vec<String> {
    let mut scenarios = records
        .iter()
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();
    scenarios
}

fn whir_fold_payload_stage_values(
    records: &[WhirFoldPayloadMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.whir_fold_mode == fold_mode
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn whir_fold_payload_proof_bytes(
    records: &[WhirFoldPayloadMeasurement],
    scenario_name: &str,
    fold_mode: &str,
) -> Option<u64> {
    records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.whir_fold_mode == fold_mode
                && record.stage == "host_verify"
        })
        .map(|record| record.proof_bytes)
}

fn whir_round0_stage_values(
    records: &[WhirRound0Measurement],
    scenario_name: &str,
    round0_variant: &str,
    fold_mode: &str,
    merkle_mode: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.round0_variant == round0_variant
                && record.whir_fold_mode == fold_mode
                && record.merkle_proof_mode == merkle_mode
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn whir_round0_host_record<'a>(
    records: &'a [WhirRound0Measurement],
    scenario_name: &str,
    round0_variant: &str,
    fold_mode: &str,
    merkle_mode: &str,
) -> Option<&'a WhirRound0Measurement> {
    records.iter().find(|record| {
        record.scenario_name == scenario_name
            && record.round0_variant == round0_variant
            && record.whir_fold_mode == fold_mode
            && record.merkle_proof_mode == merkle_mode
            && record.stage == "host_verify"
    })
}

fn derive_whir_round0_taxonomy(
    record: &WhirRound0Measurement,
) -> (u64, u64, u64, u64, u64, u64, u64, u64, f64) {
    let query_fold_muls = match record.whir_fold_mode.as_str() {
        "raw_fibers" => 7 * record.round_query_count,
        "local_interpolant" => 11 * record.round_query_count,
        _ => 0,
    };
    let sumcheck_challenge_muls = 2 * record.round_sumcheck_rounds;
    let gamma_muls = record.round_query_count;
    let bary_weight = record
        .round_query_count
        .saturating_mul(record.round_selector_count.max(1));
    let challenge_power = query_fold_muls + sumcheck_challenge_muls + gamma_muls;
    let square = record.counters.m31_square_ops
        + record.counters.cm31_square_ops
        + record.counters.qm31_square_ops;
    let cm31_structured = record.counters.cm31_mul_const_ops
        + record.counters.cm31_conjugate_ops
        + record.counters.lift_to_cm31_ops;
    let qm31_structured = record.counters.qm31_mul_const_ops
        + record.counters.qm31_conjugate_ops
        + record.counters.lift_to_qm31_ops;
    let general_extension = record
        .counters
        .cm31_mul_ops
        .saturating_add(record.counters.qm31_mul_ops)
        .saturating_sub(gamma_muls);
    let general = record
        .counters
        .m31_mul_ops
        .saturating_sub(bary_weight.saturating_add(query_fold_muls + sumcheck_challenge_muls));
    let total_classified = general
        + square
        + bary_weight
        + challenge_power
        + cm31_structured
        + qm31_structured
        + general_extension;
    let structured_share = if total_classified == 0 {
        0.0
    } else {
        (square + bary_weight + challenge_power + cm31_structured + qm31_structured) as f64
            / total_classified as f64
    };
    (
        total_classified,
        general,
        square,
        bary_weight,
        challenge_power,
        cm31_structured,
        qm31_structured,
        general_extension,
        structured_share,
    )
}

fn whir_fold_payload_comparison_summary(records: &[WhirFoldPayloadMeasurement]) -> Vec<String> {
    let mut lines = Vec::new();
    for scenario in scenario_names_from_fold_payload(records) {
        let raw_total = whir_fold_payload_stage_values(
            records,
            &scenario,
            fold_mode_name(WhirFoldMode::RawFibers),
            "total_sbf",
        );
        let local_total = whir_fold_payload_stage_values(
            records,
            &scenario,
            fold_mode_name(WhirFoldMode::LocalInterpolant),
            "total_sbf",
        );
        let raw_per_round = whir_fold_payload_stage_values(
            records,
            &scenario,
            fold_mode_name(WhirFoldMode::RawFibers),
            "phase_per_round_queries",
        );
        let local_per_round = whir_fold_payload_stage_values(
            records,
            &scenario,
            fold_mode_name(WhirFoldMode::LocalInterpolant),
            "phase_per_round_queries",
        );
        if let (Some(raw_mean), Some(local_mean)) =
            (sample_mean(&raw_total), sample_mean(&local_total))
        {
            let raw_bytes = whir_fold_payload_proof_bytes(
                records,
                &scenario,
                fold_mode_name(WhirFoldMode::RawFibers),
            )
            .unwrap_or_default();
            let local_bytes = whir_fold_payload_proof_bytes(
                records,
                &scenario,
                fold_mode_name(WhirFoldMode::LocalInterpolant),
            )
            .unwrap_or_default();
            let per_round_delta = match (sample_mean(&raw_per_round), sample_mean(&local_per_round))
            {
                (Some(raw), Some(local)) => {
                    format!(
                        ", per-round {:.0} -> {:.0} CU (delta {:+.0})",
                        raw,
                        local,
                        local - raw
                    )
                }
                _ => String::new(),
            };
            lines.push(format!(
                "{scenario}: raw {:.0} -> local {:.0} CU (delta {:+.0}), proof {raw_bytes} -> {local_bytes} bytes (delta {:+}){per_round_delta}",
                raw_mean,
                local_mean,
                local_mean - raw_mean,
                local_bytes as i64 - raw_bytes as i64,
            ));
        }
    }
    lines
}

fn render_whir_fold_payload_section(records: &[WhirFoldPayloadMeasurement]) -> String {
    let comparison = whir_fold_payload_comparison_summary(records);
    let mut lines = Vec::new();
    let stage_order = [
        ("phase_parse", "parse"),
        ("phase_transcript_setup", "transcript setup"),
        ("phase_ood", "OOD"),
        ("phase_per_round_queries", "per-round queries"),
        ("phase_folding", "folding"),
        ("phase_final_round", "final round"),
    ];
    lines.push("## WHIR Fold Payload".to_string());
    lines.push("- Executed: a proof-carried fold representation comparison on the full transcript path, holding the winning arithmetic kernels and `minimal_subtree` Merkle mode fixed while comparing `raw_fibers` against `local_interpolant`.".to_string());
    lines.push("- Honest caveat: this measures the current repo-local local-interpolant payload, not Fenzi's exact fold representation trick; it answers whether our present proof-carried fold encoding helps once the whole transcript path is included.".to_string());
    if !comparison.is_empty() {
        lines.push(String::new());
        lines.push("### Raw Fibers vs Local Interpolant".to_string());
        for line in comparison {
            lines.push(format!("- {line}."));
        }
    }
    for scenario in scenario_names_from_fold_payload(records) {
        lines.push(String::new());
        lines.push(format!("### {scenario}"));
        for fold_mode in [
            fold_mode_name(WhirFoldMode::RawFibers),
            fold_mode_name(WhirFoldMode::LocalInterpolant),
        ] {
            let total = whir_fold_payload_stage_values(records, &scenario, fold_mode, "total_sbf");
            if let (Some(mean), Some(stddev)) = (sample_mean(&total), sample_stddev(&total)) {
                let proof = whir_fold_payload_proof_bytes(records, &scenario, fold_mode)
                    .map(|value| format!(", proof {value} bytes"))
                    .unwrap_or_default();
                lines.push(format!(
                    "- {fold_mode}: total {:.0} +- {:.0} CU{proof}.",
                    mean, stddev
                ));
            }
            let mut phase_parts = Vec::new();
            for (stage, label) in stage_order {
                let values = whir_fold_payload_stage_values(records, &scenario, fold_mode, stage);
                if let (Some(mean), Some(stddev)) = (sample_mean(&values), sample_stddev(&values)) {
                    phase_parts.push(format!("{label} {:.0} +- {:.0} CU", mean, stddev));
                }
            }
            if !phase_parts.is_empty() {
                lines.push(format!(
                    "- {fold_mode} phase breakdown: {}.",
                    phase_parts.join(", ")
                ));
            }
        }
    }
    lines.join("\n")
}

fn write_phase2_fold_payload_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    phase1_summary: &Phase1Summary,
    run_config: &Phase2RunConfig,
    records: &[WhirFoldPayloadMeasurement],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    let comparison = whir_fold_payload_comparison_summary(records);
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_fold_payload_summary"] = json!(comparison);
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-fold-payload/scenarios.json",
        "results/phase2/whir-fold-payload/raw.jsonl",
        "results/phase2/whir-fold-payload/raw.csv",
        "results/phase2/whir-fold-payload/proofs/",
        "results/phase2/whir-fold-payload/validation.json",
        "results/phase2/manifests/",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|entry| entry == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    write_json(&summary_path, &summary_value)?;

    let fold_section = render_whir_fold_payload_section(records);
    let docs = if docs_path.exists() {
        replace_markdown_section(
            &fs::read_to_string(docs_path)?,
            "## WHIR Fold Payload",
            &fold_section,
        )
    } else {
        format!(
            "# Phase 2 Experiments\n\n## Goal\nRun the Phase 2 verifier experiments against the Phase 1 spend model and report measured SBF CU.\n\n## Baseline\n- Phase 1 chosen model: `{}` with RMSE {:.1} CU.\n- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}.\n\n{}",
            phase1_summary.model.chosen.method,
            phase1_summary.model.chosen.metrics.rmse,
            run_config.proof_plan.query_count,
            run_config.proof_plan.fold_arity,
            run_config.proof_plan.target_proof_bytes,
            fold_section
        )
    };
    fs::write(docs_path, docs)?;
    Ok(())
}

fn derive_whir_mul_taxonomy(
    run_config: &Phase2RunConfig,
    records: &[WhirFoldPayloadMeasurement],
) -> Result<Vec<WhirMulTaxonomyMeasurement>> {
    let scenarios = derive_whir_transcript_scenarios(run_config)?;
    let mut out = Vec::new();
    for scenario in scenarios {
        for fold_mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
            let fold_name = fold_mode_name(fold_mode);
            let host = records
                .iter()
                .find(|record| {
                    record.scenario_name == scenario.seed.name
                        && record.whir_fold_mode == fold_name
                        && record.stage == "host_verify"
                })
                .context("missing host fold payload record for taxonomy")?;
            let plan = whir_transcript_plan_for_merkle_mode(
                scenario.transcript_plan,
                fold_mode,
                MerkleProofMode::MinimalSubtree,
            );
            let total_sumcheck_rounds = u64::from(plan.initial_sumcheck_rounds)
                + u64::from(plan.final_sumcheck_rounds)
                + plan
                    .rounds
                    .iter()
                    .take(usize::from(
                        plan.round_count.min(PHASE2_WHIR_MAX_ROUNDS as u16),
                    ))
                    .map(|round| u64::from(round.sumcheck_rounds))
                    .sum::<u64>();
            let bary_weight = plan
                .rounds
                .iter()
                .take(usize::from(
                    plan.round_count.min(PHASE2_WHIR_MAX_ROUNDS as u16),
                ))
                .map(|round| u64::from(round.query_count) * u64::from(round.selector_count.max(1)))
                .sum::<u64>();
            let query_fold_muls = match fold_mode {
                WhirFoldMode::RawFibers => 7 * scenario.total_explicit_query_count,
                WhirFoldMode::LocalInterpolant => 11 * scenario.total_explicit_query_count,
            };
            let sumcheck_challenge_muls = 2 * total_sumcheck_rounds;
            let gamma_muls = scenario.total_explicit_query_count;
            let challenge_power = query_fold_muls + sumcheck_challenge_muls + gamma_muls;
            let square = host.counters.m31_square_ops
                + host.counters.cm31_square_ops
                + host.counters.qm31_square_ops;
            let cm31_structured = host.counters.cm31_mul_const_ops
                + host.counters.cm31_conjugate_ops
                + host.counters.lift_to_cm31_ops;
            let qm31_structured = host.counters.qm31_mul_const_ops
                + host.counters.qm31_conjugate_ops
                + host.counters.lift_to_qm31_ops;
            let general_extension = host
                .counters
                .cm31_mul_ops
                .saturating_add(host.counters.qm31_mul_ops)
                .saturating_sub(gamma_muls);
            let general = host.counters.m31_mul_ops.saturating_sub(
                bary_weight.saturating_add(query_fold_muls + sumcheck_challenge_muls),
            );
            let total_classified = general
                + square
                + bary_weight
                + challenge_power
                + cm31_structured
                + qm31_structured
                + general_extension;
            let structured_share = if total_classified == 0 {
                0.0
            } else {
                (square + bary_weight + challenge_power + cm31_structured + qm31_structured) as f64
                    / total_classified as f64
            };
            out.push(WhirMulTaxonomyMeasurement {
                scenario_name: scenario.seed.name.clone(),
                whir_fold_mode: fold_name.to_string(),
                merkle_proof_mode: merkle_mode_name(MerkleProofMode::MinimalSubtree).to_string(),
                security_target_bits: scenario.seed.security_target_bits,
                soundness_assumption: scenario.seed.soundness_assumption.clone(),
                total_explicit_query_count: scenario.total_explicit_query_count,
                total_sbf_mean_cu: sample_mean(&whir_fold_payload_stage_values(
                    records,
                    &scenario.seed.name,
                    fold_name,
                    "total_sbf",
                )),
                total_sbf_stddev_cu: sample_stddev(&whir_fold_payload_stage_values(
                    records,
                    &scenario.seed.name,
                    fold_name,
                    "total_sbf",
                )),
                proof_bytes: host.proof_bytes,
                total_classified_multiplies: total_classified,
                general,
                zero_one_negone: 0,
                square,
                sparse_const: 0,
                twiddle: 0,
                bary_weight,
                challenge_power,
                cm31_structured,
                qm31_structured,
                general_extension,
                structured_share,
            });
        }
    }
    Ok(out)
}

fn render_whir_mul_taxonomy_section(records: &[WhirMulTaxonomyMeasurement]) -> String {
    let mut lines = Vec::new();
    lines.push("## WHIR Multiplication Taxonomy".to_string());
    lines.push("- Executed: a taxonomy pass over the real fold-payload transcript verifier counters, classifying multiply sites as `general`, `square`, `bary_weight`, `challenge_power`, `cm31_structured`, `qm31_structured`, and `general_extension`.".to_string());
    lines.push("- Honest caveat: `zero/one/-one`, `sparse_const`, and `twiddle` remain zero in this report because the current instrumentation does not yet tag operand values dynamically; those classes need a deeper runtime wrapper pass if we want exact counts.".to_string());
    for record in records {
        lines.push(String::new());
        lines.push(format!(
            "### {} {}",
            record.scenario_name, record.whir_fold_mode
        ));
        lines.push(format!(
            "- total {:.0} +- {:.0} CU, proof {} bytes, structured share {:.1}%.",
            record.total_sbf_mean_cu.unwrap_or(0.0),
            record.total_sbf_stddev_cu.unwrap_or(0.0),
            record.proof_bytes,
            record.structured_share * 100.0
        ));
        lines.push(format!(
            "- classified multiplies: general {}, square {}, bary_weight {}, challenge_power {}, cm31_structured {}, qm31_structured {}, general_extension {}.",
            record.general,
            record.square,
            record.bary_weight,
            record.challenge_power,
            record.cm31_structured,
            record.qm31_structured,
            record.general_extension,
        ));
    }
    lines.join("\n")
}

fn full_whir_metrics_for_round0_variant(
    fold_records: &[WhirFoldPayloadMeasurement],
    multiproof_records: &[WhirMultiproofMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    merkle_mode: &str,
) -> (Option<f64>, Option<f64>) {
    if merkle_mode == merkle_mode_name(MerkleProofMode::MinimalSubtree) {
        (
            sample_mean(&whir_fold_payload_stage_values(
                fold_records,
                scenario_name,
                fold_mode,
                "total_sbf",
            )),
            sample_mean(&whir_fold_payload_stage_values(
                fold_records,
                scenario_name,
                fold_mode,
                "phase_per_round_queries",
            )),
        )
    } else if merkle_mode == merkle_mode_name(MerkleProofMode::SeparatePaths)
        && fold_mode == fold_mode_name(WhirFoldMode::LocalInterpolant)
    {
        (
            sample_mean(&whir_multiproof_stage_values(
                multiproof_records,
                scenario_name,
                merkle_mode,
                "total_sbf",
            )),
            sample_mean(&whir_multiproof_stage_values(
                multiproof_records,
                scenario_name,
                merkle_mode,
                "phase_per_round_queries",
            )),
        )
    } else {
        (None, None)
    }
}

fn derive_whir_round0_summary(
    run_config: &Phase2RunConfig,
    records: &[WhirRound0Measurement],
    fold_records: &[WhirFoldPayloadMeasurement],
    multiproof_records: &[WhirMultiproofMeasurement],
) -> Result<Vec<WhirRound0SummaryRecord>> {
    let scenarios = derive_whir_transcript_scenarios(run_config)?;
    let mut out = Vec::new();
    for scenario in scenarios {
        for merkle_mode in [
            merkle_mode_name(MerkleProofMode::SeparatePaths),
            merkle_mode_name(MerkleProofMode::MinimalSubtree),
        ] {
            for fold_mode in [
                fold_mode_name(WhirFoldMode::RawFibers),
                fold_mode_name(WhirFoldMode::LocalInterpolant),
            ] {
                let baseline_round0_mean = sample_mean(&whir_round0_stage_values(
                    records,
                    &scenario.seed.name,
                    "baseline_round0",
                    fold_mode,
                    merkle_mode,
                    "verify_sbf",
                ));
                for round0_variant in ["baseline_round0", "round_reuse_batch_inverse"] {
                    let host = whir_round0_host_record(
                        records,
                        &scenario.seed.name,
                        round0_variant,
                        fold_mode,
                        merkle_mode,
                    )
                    .with_context(|| {
                        format!(
                            "missing round0 host record for {} {} {} {}",
                            scenario.seed.name, round0_variant, fold_mode, merkle_mode
                        )
                    })?;
                    let round0_total_mean = sample_mean(&whir_round0_stage_values(
                        records,
                        &scenario.seed.name,
                        round0_variant,
                        fold_mode,
                        merkle_mode,
                        "verify_sbf",
                    ));
                    let round0_total_stddev = sample_stddev(&whir_round0_stage_values(
                        records,
                        &scenario.seed.name,
                        round0_variant,
                        fold_mode,
                        merkle_mode,
                        "verify_sbf",
                    ));
                    let phase_parse_mean = sample_mean(&whir_round0_stage_values(
                        records,
                        &scenario.seed.name,
                        round0_variant,
                        fold_mode,
                        merkle_mode,
                        "phase_parse",
                    ));
                    let phase_ood_mean = sample_mean(&whir_round0_stage_values(
                        records,
                        &scenario.seed.name,
                        round0_variant,
                        fold_mode,
                        merkle_mode,
                        "phase_ood",
                    ));
                    let phase_per_round_queries_mean = sample_mean(&whir_round0_stage_values(
                        records,
                        &scenario.seed.name,
                        round0_variant,
                        fold_mode,
                        merkle_mode,
                        "phase_per_round_queries",
                    ));
                    let phase_folding_mean = sample_mean(&whir_round0_stage_values(
                        records,
                        &scenario.seed.name,
                        round0_variant,
                        fold_mode,
                        merkle_mode,
                        "phase_folding",
                    ));
                    let (full_total_mean, full_per_round_queries_mean) =
                        full_whir_metrics_for_round0_variant(
                            fold_records,
                            multiproof_records,
                            &scenario.seed.name,
                            fold_mode,
                            merkle_mode,
                        );
                    let round0_share_of_full_total = match (round0_total_mean, full_total_mean) {
                        (Some(round0), Some(full)) if full > 0.0 => Some(round0 / full),
                        _ => None,
                    };
                    let round0_share_of_full_per_round_queries =
                        match (round0_total_mean, full_per_round_queries_mean) {
                            (Some(round0), Some(per_round)) if per_round > 0.0 => {
                                Some(round0 / per_round)
                            }
                            _ => None,
                        };
                    let projected_full_total_mean_cu =
                        match (full_total_mean, baseline_round0_mean, round0_total_mean) {
                            (Some(full), Some(baseline_round0), Some(current_round0)) => {
                                Some(full - baseline_round0 + current_round0)
                            }
                            _ => None,
                        };
                    let projected_full_delta_cu =
                        match (projected_full_total_mean_cu, full_total_mean) {
                            (Some(projected), Some(full)) => Some(projected - full),
                            _ => None,
                        };
                    let projected_margin_cu =
                        projected_full_total_mean_cu.map(|value| 1_400_000.0 - value);
                    let (
                        total_classified_multiplies,
                        general,
                        square,
                        bary_weight,
                        challenge_power,
                        cm31_structured,
                        qm31_structured,
                        general_extension,
                        structured_share,
                    ) = derive_whir_round0_taxonomy(host);
                    out.push(WhirRound0SummaryRecord {
                        scenario_name: scenario.seed.name.clone(),
                        round0_variant: round0_variant.to_string(),
                        whir_fold_mode: fold_mode.to_string(),
                        merkle_proof_mode: merkle_mode.to_string(),
                        security_target_bits: scenario.seed.security_target_bits,
                        soundness_assumption: scenario.seed.soundness_assumption.clone(),
                        round_query_count: host.round_query_count,
                        round_merkle_depth: host.round_merkle_depth,
                        round_ood_samples: host.round_ood_samples,
                        round_selector_count: host.round_selector_count,
                        round_pow_bits: host.round_pow_bits,
                        round_sumcheck_rounds: host.round_sumcheck_rounds,
                        round_folding_pow_bits: host.round_folding_pow_bits,
                        proof_bytes: host.proof_bytes,
                        round0_total_mean_cu: round0_total_mean,
                        round0_total_stddev_cu: round0_total_stddev,
                        phase_parse_mean_cu: phase_parse_mean,
                        phase_ood_mean_cu: phase_ood_mean,
                        phase_per_round_queries_mean_cu: phase_per_round_queries_mean,
                        phase_folding_mean_cu: phase_folding_mean,
                        full_total_mean_cu: full_total_mean,
                        full_per_round_queries_mean_cu: full_per_round_queries_mean,
                        round0_share_of_full_total,
                        round0_share_of_full_per_round_queries,
                        projected_full_total_mean_cu,
                        projected_full_delta_cu,
                        projected_margin_cu,
                        total_classified_multiplies,
                        general,
                        square,
                        bary_weight,
                        challenge_power,
                        cm31_structured,
                        qm31_structured,
                        general_extension,
                        structured_share,
                    });
                }
            }
        }
    }
    Ok(out)
}

fn render_whir_round0_section(records: &[WhirRound0SummaryRecord]) -> String {
    let mut lines = Vec::new();
    lines.push("## WHIR Round-0 Investigation".to_string());
    lines.push("- Executed: a dedicated round-0 replay on SBF for all three security regimes, both Merkle modes, both fold modes, and two round-0 variants: `baseline_round0` and `round_reuse_batch_inverse`.".to_string());
    lines.push("- Executed: phase-level tracing inside round 0 (`parse`, `OOD`, `per_round_queries`, `folding`) plus a round-0 multiply taxonomy from the host counters.".to_string());
    lines.push("- Prototype: `round_reuse_batch_inverse` keeps the existing proof-carried selector weights / local-interpolant representation, but replaces per-query denominator inversion with a round-local batched inversion over the combined CM31 denominators.".to_string());

    for scenario in [
        "whir_t100_capacity_full",
        "whir_t128_capacity_full",
        "whir_t128_johnson_full",
    ] {
        lines.push(String::new());
        lines.push(format!("### {scenario}"));
        for fold_mode in [
            fold_mode_name(WhirFoldMode::RawFibers),
            fold_mode_name(WhirFoldMode::LocalInterpolant),
        ] {
            let baseline = records.iter().find(|record| {
                record.scenario_name == scenario
                    && record.round0_variant == "baseline_round0"
                    && record.whir_fold_mode == fold_mode
                    && record.merkle_proof_mode == merkle_mode_name(MerkleProofMode::MinimalSubtree)
            });
            let reuse = records.iter().find(|record| {
                record.scenario_name == scenario
                    && record.round0_variant == "round_reuse_batch_inverse"
                    && record.whir_fold_mode == fold_mode
                    && record.merkle_proof_mode == merkle_mode_name(MerkleProofMode::MinimalSubtree)
            });
            if let Some(baseline) = baseline {
                let mut line = format!(
                    "- minimal_subtree / {}: round0 {:.0} +- {:.0} CU",
                    fold_mode,
                    baseline.round0_total_mean_cu.unwrap_or(0.0),
                    baseline.round0_total_stddev_cu.unwrap_or(0.0),
                );
                if let Some(share) = baseline.round0_share_of_full_total {
                    line.push_str(&format!(", {:.1}% of full verifier", share * 100.0));
                }
                if let Some(share) = baseline.round0_share_of_full_per_round_queries {
                    line.push_str(&format!(
                        ", {:.1}% of the full per-round bucket",
                        share * 100.0
                    ));
                }
                line.push_str(&format!(
                    ", structured share {:.1}%",
                    baseline.structured_share * 100.0
                ));
                if baseline.phase_per_round_queries_mean_cu.is_none() {
                    line.push_str(", saturated at the 1.4M cap before the per-round trace closed");
                }
                if let Some(reuse) = reuse {
                    let delta = reuse.round0_total_mean_cu.unwrap_or(0.0)
                        - baseline.round0_total_mean_cu.unwrap_or(0.0);
                    line.push_str(&format!(
                        "; reuse {:.0} CU (delta {:+.0})",
                        reuse.round0_total_mean_cu.unwrap_or(0.0),
                        delta
                    ));
                    if let Some(projected) = reuse.projected_full_total_mean_cu {
                        line.push_str(&format!(", projected full {:.0} CU", projected));
                    }
                    if let Some(margin) = reuse.projected_margin_cu {
                        line.push_str(&format!(", projected margin {:.0} CU", margin));
                    }
                }
                line.push('.');
                lines.push(line);
            }
        }

        let separate = records.iter().find(|record| {
            record.scenario_name == scenario
                && record.round0_variant == "baseline_round0"
                && record.whir_fold_mode == fold_mode_name(WhirFoldMode::LocalInterpolant)
                && record.merkle_proof_mode == merkle_mode_name(MerkleProofMode::SeparatePaths)
        });
        let minimal = records.iter().find(|record| {
            record.scenario_name == scenario
                && record.round0_variant == "baseline_round0"
                && record.whir_fold_mode == fold_mode_name(WhirFoldMode::LocalInterpolant)
                && record.merkle_proof_mode == merkle_mode_name(MerkleProofMode::MinimalSubtree)
        });
        if let (Some(separate), Some(minimal)) = (separate, minimal) {
            lines.push(format!(
                "- local_interpolant Merkle delta: separate_paths round0 {:.0} CU -> minimal_subtree {:.0} CU (delta {:+.0}).",
                separate.round0_total_mean_cu.unwrap_or(0.0),
                minimal.round0_total_mean_cu.unwrap_or(0.0),
                minimal.round0_total_mean_cu.unwrap_or(0.0)
                    - separate.round0_total_mean_cu.unwrap_or(0.0),
            ));
        }
    }

    lines.join("\n")
}

fn write_phase2_round0_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    _phase1_summary: &Phase1Summary,
    _run_config: &Phase2RunConfig,
    _records: &[WhirRound0Measurement],
    summary_records: &[WhirRound0SummaryRecord],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_round0_summary"] = json!(summary_records);
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-round0/raw.jsonl",
        "results/phase2/whir-round0/raw.csv",
        "results/phase2/whir-round0/summary.json",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|existing| existing == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    write_json(&summary_path, &summary_value)?;

    let round0_section = render_whir_round0_section(summary_records);
    let docs = if docs_path.exists() {
        let docs = fs::read_to_string(docs_path)?;
        if docs.contains("## WHIR Round-0 Investigation") {
            replace_markdown_section(&docs, "## WHIR Round-0 Investigation", &round0_section)
        } else if docs.contains("## Shipping Freeze") {
            docs.replace(
                "## Shipping Freeze",
                &format!("{round0_section}\n\n## Shipping Freeze"),
            )
        } else {
            format!("{docs}\n\n{round0_section}")
        }
    } else {
        round0_section
    };
    fs::write(docs_path, docs)?;
    Ok(())
}

fn scenario_names_from_full_reuse(records: &[WhirFullReuseMeasurement]) -> Vec<String> {
    let mut scenarios = records
        .iter()
        .filter(|record| record.path_variant == "transcript_full")
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();
    scenarios
}

fn whir_full_reuse_query_only_stage_values(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "query_only"
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn whir_full_reuse_transcript_stage_values(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_reuse_mode: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode == query_reuse_mode
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn whir_full_reuse_transcript_status_counts(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_reuse_mode: &str,
    stage: &str,
) -> (usize, usize) {
    let filtered = records.iter().filter(|record| {
        record.scenario_name == scenario_name
            && record.path_variant == "transcript_full"
            && record.whir_fold_mode == fold_mode
            && record.query_reuse_mode == query_reuse_mode
            && record.stage == stage
    });
    let total = filtered.clone().count();
    let ok = filtered.filter(|record| record.status == "ok").count();
    (ok, total)
}

fn whir_full_reuse_trace_counts(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_reuse_mode: &str,
) -> (usize, usize) {
    let ok = records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode == query_reuse_mode
                && record.stage == "phase_transcript_setup"
                && record.status == "ok"
        })
        .count();
    let phase_rows = records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode == query_reuse_mode
                && record.stage == "phase_transcript_setup"
        })
        .count();
    let incomplete = records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode == query_reuse_mode
                && record.stage == "trace_incomplete"
        })
        .count();
    (ok, phase_rows + incomplete)
}

fn whir_full_reuse_proof_bytes(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_reuse_mode: &str,
) -> Option<u64> {
    records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode == query_reuse_mode
                && record.stage == "host_verify"
        })
        .map(|record| record.proof_bytes)
}

fn whir_full_reuse_round0_projection(
    round0_summary_records: &[WhirRound0SummaryRecord],
    scenario_name: &str,
    fold_mode: &str,
) -> Option<f64> {
    round0_summary_records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.round0_variant == "round_reuse_batch_inverse"
                && record.whir_fold_mode == fold_mode
                && record.merkle_proof_mode == merkle_mode_name(MerkleProofMode::MinimalSubtree)
        })
        .and_then(|record| record.projected_full_total_mean_cu)
}

fn derive_whir_full_reuse_summary(
    records: &[WhirFullReuseMeasurement],
    round0_summary_records: &[WhirRound0SummaryRecord],
) -> Vec<WhirFullReuseSummaryRecord> {
    let mut out = Vec::new();
    for scenario in scenario_names_from_full_reuse(records) {
        let query_only_mean = sample_mean(&whir_full_reuse_query_only_stage_values(
            records,
            &scenario,
            "total_sbf",
        ));
        let query_only_stddev = sample_stddev(&whir_full_reuse_query_only_stage_values(
            records,
            &scenario,
            "total_sbf",
        ));
        for fold_mode in [
            fold_mode_name(WhirFoldMode::RawFibers),
            fold_mode_name(WhirFoldMode::LocalInterpolant),
        ] {
            for query_reuse_mode in [
                whir_query_reuse_mode_name(WhirQueryReuseMode::PerQueryInversion),
                whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion),
            ] {
                let total_values = whir_full_reuse_transcript_stage_values(
                    records,
                    &scenario,
                    fold_mode,
                    query_reuse_mode,
                    "total_sbf",
                );
                if total_values.is_empty() {
                    continue;
                }
                let verify_values = whir_full_reuse_transcript_stage_values(
                    records,
                    &scenario,
                    fold_mode,
                    query_reuse_mode,
                    "verify_sbf",
                );
                let upload_values = whir_full_reuse_transcript_stage_values(
                    records,
                    &scenario,
                    fold_mode,
                    query_reuse_mode,
                    "upload_total",
                );
                let phase_transcript_setup_mean =
                    sample_mean(&whir_full_reuse_transcript_stage_values(
                        records,
                        &scenario,
                        fold_mode,
                        query_reuse_mode,
                        "phase_transcript_setup",
                    ));
                let phase_ood_mean = sample_mean(&whir_full_reuse_transcript_stage_values(
                    records,
                    &scenario,
                    fold_mode,
                    query_reuse_mode,
                    "phase_ood",
                ));
                let phase_per_round_queries_mean =
                    sample_mean(&whir_full_reuse_transcript_stage_values(
                        records,
                        &scenario,
                        fold_mode,
                        query_reuse_mode,
                        "phase_per_round_queries",
                    ));
                let phase_folding_mean = sample_mean(&whir_full_reuse_transcript_stage_values(
                    records,
                    &scenario,
                    fold_mode,
                    query_reuse_mode,
                    "phase_folding",
                ));
                let phase_final_round_mean = sample_mean(&whir_full_reuse_transcript_stage_values(
                    records,
                    &scenario,
                    fold_mode,
                    query_reuse_mode,
                    "phase_final_round",
                ));
                let total_mean = sample_mean(&total_values);
                let projected_total = if query_reuse_mode
                    == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
                {
                    whir_full_reuse_round0_projection(round0_summary_records, &scenario, fold_mode)
                } else {
                    None
                };
                let round0_projection_delta = match (total_mean, projected_total) {
                    (Some(measured), Some(projected)) => Some(measured - projected),
                    _ => None,
                };
                let (verify_ok, verify_total) = whir_full_reuse_transcript_status_counts(
                    records,
                    &scenario,
                    fold_mode,
                    query_reuse_mode,
                    "verify_sbf",
                );
                let (trace_ok, trace_total) =
                    whir_full_reuse_trace_counts(records, &scenario, fold_mode, query_reuse_mode);
                let host = records.iter().find(|record| {
                    record.scenario_name == scenario
                        && record.path_variant == "transcript_full"
                        && record.whir_fold_mode == fold_mode
                        && record.query_reuse_mode == query_reuse_mode
                        && record.stage == "host_verify"
                });
                if let Some(host) = host {
                    out.push(WhirFullReuseSummaryRecord {
                        scenario_name: scenario.clone(),
                        whir_fold_mode: fold_mode.to_string(),
                        merkle_proof_mode: merkle_mode_name(MerkleProofMode::MinimalSubtree)
                            .to_string(),
                        query_reuse_mode: query_reuse_mode.to_string(),
                        query_precompute_mode: host.query_precompute_mode.clone(),
                        security_target_bits: host.security_target_bits,
                        soundness_assumption: host.soundness_assumption.clone(),
                        proof_bytes: whir_full_reuse_proof_bytes(
                            records,
                            &scenario,
                            fold_mode,
                            query_reuse_mode,
                        )
                        .unwrap_or(host.proof_bytes),
                        verify_sbf_mean_cu: sample_mean(&verify_values),
                        verify_sbf_stddev_cu: sample_stddev(&verify_values),
                        total_sbf_mean_cu: total_mean,
                        total_sbf_stddev_cu: sample_stddev(&total_values),
                        upload_mean_cu: sample_mean(&upload_values),
                        phase_transcript_setup_mean_cu: phase_transcript_setup_mean,
                        phase_ood_mean_cu: phase_ood_mean,
                        phase_per_round_queries_mean_cu: phase_per_round_queries_mean,
                        phase_folding_mean_cu: phase_folding_mean,
                        phase_final_round_mean_cu: phase_final_round_mean,
                        query_only_mean_cu: query_only_mean,
                        query_only_stddev_cu: query_only_stddev,
                        round0_projected_total_mean_cu: projected_total,
                        round0_projection_delta_cu: round0_projection_delta,
                        remaining_margin_cu: total_mean.map(|value| 1_400_000.0 - value),
                        verify_ok,
                        verify_total,
                        trace_ok,
                        trace_total,
                    });
                }
            }
        }
    }
    out
}

fn render_whir_full_reuse_section(records: &[WhirFullReuseSummaryRecord]) -> String {
    let mut lines = Vec::new();
    lines.push("## WHIR Full-Path Round Reuse".to_string());
    lines.push("- Executed: `minimal_subtree` full-transcript verifier runs for `whir_t128_capacity_full` and `whir_t100_johnson_full`, with both fold payloads (`raw_fibers`, `local_interpolant`) and both denominator strategies (`per_query_inversion`, `round_batch_inversion`).".to_string());
    lines.push("- Executed: fresh query-only baselines for both scenarios, 10 SBF repetitions for `verify_sbf` and `total_sbf`, plus 10 traced repetitions for transcript phase breakdown.".to_string());
    lines.push("- Executed: valid/invalid proof checks for each fold/reuse combination before timing. The proof bytes stayed constant across the reuse variants; only the verifier path changed.".to_string());

    let mut scenarios = records
        .iter()
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();

    for scenario in scenarios {
        lines.push(String::new());
        lines.push(format!("### {scenario}"));
        if let Some(query_only) = records
            .iter()
            .find(|record| record.scenario_name == scenario)
        {
            if let (Some(mean), Some(stddev)) = (
                query_only.query_only_mean_cu,
                query_only.query_only_stddev_cu,
            ) {
                lines.push(format!(
                    "- query_only baseline: {:.0} +- {:.0} CU.",
                    mean, stddev
                ));
            }
        }
        for fold_mode in [
            fold_mode_name(WhirFoldMode::RawFibers),
            fold_mode_name(WhirFoldMode::LocalInterpolant),
        ] {
            let baseline = records.iter().find(|record| {
                record.scenario_name == scenario
                    && record.whir_fold_mode == fold_mode
                    && record.query_reuse_mode
                        == whir_query_reuse_mode_name(WhirQueryReuseMode::PerQueryInversion)
            });
            let reuse = records.iter().find(|record| {
                record.scenario_name == scenario
                    && record.whir_fold_mode == fold_mode
                    && record.query_reuse_mode
                        == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
            });
            if let (Some(baseline), Some(reuse)) = (baseline, reuse) {
                let baseline_total = baseline.total_sbf_mean_cu.unwrap_or(0.0);
                let reuse_total = reuse.total_sbf_mean_cu.unwrap_or(0.0);
                let delta = reuse_total - baseline_total;
                let mut line = format!(
                    "- minimal_subtree / {}: baseline {:.0} +- {:.0} CU -> batched {:.0} +- {:.0} CU (delta {:+.0})",
                    fold_mode,
                    baseline_total,
                    baseline.total_sbf_stddev_cu.unwrap_or(0.0),
                    reuse_total,
                    reuse.total_sbf_stddev_cu.unwrap_or(0.0),
                    delta,
                );
                if let Some(projected) = reuse.round0_projected_total_mean_cu {
                    line.push_str(&format!(", round-0 projection {:.0} CU", projected));
                }
                if let Some(projection_delta) = reuse.round0_projection_delta_cu {
                    line.push_str(&format!(", projection delta {:+.0}", projection_delta));
                }
                if let Some(margin) = reuse.remaining_margin_cu {
                    line.push_str(&format!(", margin {:.0} CU", margin));
                }
                line.push('.');
                lines.push(line);
            }
        }

        if let Some(best) = records
            .iter()
            .filter(|record| record.scenario_name == scenario)
            .filter(|record| record.total_sbf_mean_cu.is_some())
            .min_by(|lhs, rhs| {
                lhs.total_sbf_mean_cu
                    .partial_cmp(&rhs.total_sbf_mean_cu)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
        {
            lines.push(format!(
                "- best measured stack: {} / {} at {:.0} CU total, {:.0} CU verify, margin {:.0} CU, verify {}/{} ok, trace {}/{} complete.",
                best.whir_fold_mode,
                best.query_reuse_mode,
                best.total_sbf_mean_cu.unwrap_or(0.0),
                best.verify_sbf_mean_cu.unwrap_or(0.0),
                best.remaining_margin_cu.unwrap_or(0.0),
                best.verify_ok,
                best.verify_total,
                best.trace_ok,
                best.trace_total,
            ));
            let mut breakdown = Vec::new();
            if let Some(value) = best.phase_transcript_setup_mean_cu {
                breakdown.push(format!("transcript setup {:.0}", value));
            }
            if let Some(value) = best.phase_ood_mean_cu {
                breakdown.push(format!("OOD {:.0}", value));
            }
            if let Some(value) = best.phase_per_round_queries_mean_cu {
                breakdown.push(format!("per-round queries {:.0}", value));
            }
            if let Some(value) = best.phase_folding_mean_cu {
                breakdown.push(format!("folding {:.0}", value));
            }
            if let Some(value) = best.phase_final_round_mean_cu {
                breakdown.push(format!("final round {:.0}", value));
            }
            if !breakdown.is_empty() {
                lines.push(format!(
                    "- best-path phase means: {}.",
                    breakdown.join(", ")
                ));
            }
        }
    }

    lines.join("\n")
}

fn write_phase2_full_reuse_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    phase1_summary: &Phase1Summary,
    run_config: &Phase2RunConfig,
    _records: &[WhirFullReuseMeasurement],
    summary_records: &[WhirFullReuseSummaryRecord],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_full_reuse_summary"] = json!(summary_records);
    summary_value["biggest_remaining_risk"] = json!(
        "Round-batched inversion brings both targeted profiles under the 1.4M CU cap, but per-round queries still dominate the budget (~770k CU for t128 capacity and ~1.10M CU for t100 Johnson on the best measured paths). Johnson's remaining headroom is only about 199k CU, so proof-carried round-local structure is still the next structural lever."
    );
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-full-reuse/scenarios.json",
        "results/phase2/whir-full-reuse/raw.jsonl",
        "results/phase2/whir-full-reuse/raw.csv",
        "results/phase2/whir-full-reuse/summary.json",
        "results/phase2/whir-full-reuse/validation.json",
        "results/phase2/whir-full-reuse/trace_diagnostics.json",
        "results/phase2/whir-full-reuse/proofs/",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|existing| existing == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    write_json(&summary_path, &summary_value)?;

    let reuse_section = render_whir_full_reuse_section(summary_records);
    let docs = if docs_path.exists() {
        let docs = fs::read_to_string(docs_path)?;
        if docs.contains("## WHIR Full-Path Round Reuse") {
            replace_markdown_section(&docs, "## WHIR Full-Path Round Reuse", &reuse_section)
        } else if docs.contains("## Shipping Freeze") {
            docs.replace(
                "## Shipping Freeze",
                &format!("{reuse_section}\n\n## Shipping Freeze"),
            )
        } else {
            format!("{docs}\n\n{reuse_section}")
        }
    } else {
        format!(
            "# Phase 2 Experiments\n\n## Goal\nRun the Phase 2 verifier experiments against the Phase 1 spend model and report measured SBF CU.\n\n## Baseline\n- Phase 1 chosen model: `{}` with RMSE {:.1} CU.\n- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}.\n\n{}",
            phase1_summary.model.chosen.method,
            phase1_summary.model.chosen.metrics.rmse,
            run_config.proof_plan.query_count,
            run_config.proof_plan.fold_arity,
            run_config.proof_plan.target_proof_bytes,
            reuse_section
        )
    };
    fs::write(docs_path, docs)?;
    Ok(())
}

fn whir_roundlocal_transcript_stage_values(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_precompute_mode: &str,
    stage: &str,
) -> Vec<f64> {
    records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode
                    == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
                && record.query_precompute_mode == query_precompute_mode
                && record.stage == stage
        })
        .filter_map(|record| record.actual_cu.map(|value| value as f64))
        .collect()
}

fn whir_roundlocal_status_counts(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_precompute_mode: &str,
    stage: &str,
) -> (usize, usize) {
    let filtered = records.iter().filter(|record| {
        record.scenario_name == scenario_name
            && record.path_variant == "transcript_full"
            && record.whir_fold_mode == fold_mode
            && record.query_reuse_mode
                == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
            && record.query_precompute_mode == query_precompute_mode
            && record.stage == stage
    });
    let total = filtered.clone().count();
    let ok = filtered.filter(|record| record.status == "ok").count();
    (ok, total)
}

fn whir_roundlocal_trace_counts(
    records: &[WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_precompute_mode: &str,
) -> (usize, usize) {
    let ok = records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode
                    == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
                && record.query_precompute_mode == query_precompute_mode
                && record.stage == "phase_transcript_setup"
                && record.status == "ok"
        })
        .count();
    let phase_rows = records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode
                    == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
                && record.query_precompute_mode == query_precompute_mode
                && record.stage == "phase_transcript_setup"
        })
        .count();
    let incomplete = records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.path_variant == "transcript_full"
                && record.whir_fold_mode == fold_mode
                && record.query_reuse_mode
                    == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
                && record.query_precompute_mode == query_precompute_mode
                && record.stage == "trace_incomplete"
        })
        .count();
    (ok, phase_rows + incomplete)
}

fn whir_roundlocal_host_record<'a>(
    records: &'a [WhirFullReuseMeasurement],
    scenario_name: &str,
    fold_mode: &str,
    query_precompute_mode: &str,
) -> Option<&'a WhirFullReuseMeasurement> {
    records.iter().find(|record| {
        record.scenario_name == scenario_name
            && record.path_variant == "transcript_full"
            && record.whir_fold_mode == fold_mode
            && record.query_reuse_mode
                == whir_query_reuse_mode_name(WhirQueryReuseMode::RoundBatchInversion)
            && record.query_precompute_mode == query_precompute_mode
            && record.stage == "host_verify"
    })
}

fn derive_whir_roundlocal_summary(
    records: &[WhirFullReuseMeasurement],
    round0_summary_records: &[WhirRound0SummaryRecord],
) -> Vec<WhirRoundLocalSummaryRecord> {
    let mut out = Vec::new();
    for scenario in scenario_names_from_full_reuse(records) {
        for fold_mode in [
            fold_mode_name(WhirFoldMode::RawFibers),
            fold_mode_name(WhirFoldMode::LocalInterpolant),
        ] {
            let baseline = whir_roundlocal_host_record(
                records,
                &scenario,
                fold_mode,
                whir_query_precompute_mode_name(WhirQueryPrecomputeMode::None),
            );
            let baseline_total_mean = sample_mean(&whir_roundlocal_transcript_stage_values(
                records,
                &scenario,
                fold_mode,
                whir_query_precompute_mode_name(WhirQueryPrecomputeMode::None),
                "total_sbf",
            ));
            let baseline_verify_mean = sample_mean(&whir_roundlocal_transcript_stage_values(
                records,
                &scenario,
                fold_mode,
                whir_query_precompute_mode_name(WhirQueryPrecomputeMode::None),
                "verify_sbf",
            ));
            let baseline_per_round_mean = sample_mean(&whir_roundlocal_transcript_stage_values(
                records,
                &scenario,
                fold_mode,
                whir_query_precompute_mode_name(WhirQueryPrecomputeMode::None),
                "phase_per_round_queries",
            ));
            let prior_round0 = round0_summary_records.iter().find(|record| {
                record.scenario_name == scenario
                    && record.round0_variant == "round_reuse_batch_inverse"
                    && record.whir_fold_mode == fold_mode
                    && record.merkle_proof_mode == merkle_mode_name(MerkleProofMode::MinimalSubtree)
            });

            for query_precompute_mode in [
                whir_query_precompute_mode_name(WhirQueryPrecomputeMode::None),
                whir_query_precompute_mode_name(WhirQueryPrecomputeMode::ProofCarriedRoundLocal),
            ] {
                let host = whir_roundlocal_host_record(
                    records,
                    &scenario,
                    fold_mode,
                    query_precompute_mode,
                );
                if let Some(host) = host {
                    let verify_values = whir_roundlocal_transcript_stage_values(
                        records,
                        &scenario,
                        fold_mode,
                        query_precompute_mode,
                        "verify_sbf",
                    );
                    let total_values = whir_roundlocal_transcript_stage_values(
                        records,
                        &scenario,
                        fold_mode,
                        query_precompute_mode,
                        "total_sbf",
                    );
                    let upload_values = whir_roundlocal_transcript_stage_values(
                        records,
                        &scenario,
                        fold_mode,
                        query_precompute_mode,
                        "upload_total",
                    );
                    let phase_transcript_setup_mean =
                        sample_mean(&whir_roundlocal_transcript_stage_values(
                            records,
                            &scenario,
                            fold_mode,
                            query_precompute_mode,
                            "phase_transcript_setup",
                        ));
                    let phase_ood_mean = sample_mean(&whir_roundlocal_transcript_stage_values(
                        records,
                        &scenario,
                        fold_mode,
                        query_precompute_mode,
                        "phase_ood",
                    ));
                    let phase_per_round_queries_mean =
                        sample_mean(&whir_roundlocal_transcript_stage_values(
                            records,
                            &scenario,
                            fold_mode,
                            query_precompute_mode,
                            "phase_per_round_queries",
                        ));
                    let phase_folding_mean = sample_mean(&whir_roundlocal_transcript_stage_values(
                        records,
                        &scenario,
                        fold_mode,
                        query_precompute_mode,
                        "phase_folding",
                    ));
                    let phase_final_round_mean =
                        sample_mean(&whir_roundlocal_transcript_stage_values(
                            records,
                            &scenario,
                            fold_mode,
                            query_precompute_mode,
                            "phase_final_round",
                        ));
                    let total_mean = sample_mean(&total_values);
                    let verify_mean = sample_mean(&verify_values);
                    let proof_bytes_delta_vs_none = baseline
                        .map(|baseline| host.proof_bytes as i64 - baseline.proof_bytes as i64);
                    let (verify_ok, verify_total) = whir_roundlocal_status_counts(
                        records,
                        &scenario,
                        fold_mode,
                        query_precompute_mode,
                        "verify_sbf",
                    );
                    let (trace_ok, trace_total) = whir_roundlocal_trace_counts(
                        records,
                        &scenario,
                        fold_mode,
                        query_precompute_mode,
                    );
                    out.push(WhirRoundLocalSummaryRecord {
                        scenario_name: scenario.clone(),
                        whir_fold_mode: fold_mode.to_string(),
                        merkle_proof_mode: merkle_mode_name(MerkleProofMode::MinimalSubtree)
                            .to_string(),
                        query_reuse_mode: whir_query_reuse_mode_name(
                            WhirQueryReuseMode::RoundBatchInversion,
                        )
                        .to_string(),
                        query_precompute_mode: query_precompute_mode.to_string(),
                        security_target_bits: host.security_target_bits,
                        soundness_assumption: host.soundness_assumption.clone(),
                        proof_bytes: host.proof_bytes,
                        proof_bytes_delta_vs_none,
                        verify_sbf_mean_cu: verify_mean,
                        verify_sbf_stddev_cu: sample_stddev(&verify_values),
                        total_sbf_mean_cu: total_mean,
                        total_sbf_stddev_cu: sample_stddev(&total_values),
                        upload_mean_cu: sample_mean(&upload_values),
                        phase_transcript_setup_mean_cu: phase_transcript_setup_mean,
                        phase_ood_mean_cu: phase_ood_mean,
                        phase_per_round_queries_mean_cu: phase_per_round_queries_mean,
                        phase_folding_mean_cu: phase_folding_mean,
                        phase_final_round_mean_cu: phase_final_round_mean,
                        delta_vs_none_verify_cu: match (verify_mean, baseline_verify_mean) {
                            (Some(current), Some(baseline)) => Some(current - baseline),
                            _ => None,
                        },
                        delta_vs_none_total_cu: match (total_mean, baseline_total_mean) {
                            (Some(current), Some(baseline)) => Some(current - baseline),
                            _ => None,
                        },
                        delta_vs_none_phase_per_round_queries_cu: match (
                            phase_per_round_queries_mean,
                            baseline_per_round_mean,
                        ) {
                            (Some(current), Some(baseline)) => Some(current - baseline),
                            _ => None,
                        },
                        remaining_margin_cu: total_mean.map(|value| 1_400_000.0 - value),
                        prior_round0_share_of_full_total: prior_round0
                            .and_then(|record| record.round0_share_of_full_total),
                        prior_round0_projected_total_mean_cu: prior_round0
                            .and_then(|record| record.projected_full_total_mean_cu),
                        verify_ok,
                        verify_total,
                        trace_ok,
                        trace_total,
                    });
                }
            }
        }
    }
    out
}

fn render_whir_roundlocal_section(records: &[WhirRoundLocalSummaryRecord]) -> String {
    let mut lines = Vec::new();
    lines.push("## WHIR Proof-Carried Round-Local Structure".to_string());
    lines.push("- Executed: `minimal_subtree` full-transcript verifier runs for `whir_t128_capacity_full` and `whir_t100_johnson_full`, with both fold payloads (`raw_fibers`, `local_interpolant`), `round_batch_inversion`, and an A/B between `none` and `proof_carried_round_local` query supplements.".to_string());
    lines.push("- Executed: 10 SBF repetitions for `verify_sbf` and `total_sbf`, plus 10 traced repetitions for phase breakdown, with valid/invalid proof checks before timing.".to_string());
    lines.push("- Prototype: each transcript query carries a checked supplement for numerator evaluation, selector affine terms, selector weight sum, and both CM31 denominator products, so the verifier can skip the repeated round-local rebuild when the transcript bytes are correct.".to_string());

    let mut scenarios = records
        .iter()
        .map(|record| record.scenario_name.clone())
        .collect::<Vec<_>>();
    scenarios.sort();
    scenarios.dedup();

    for scenario in scenarios {
        lines.push(String::new());
        lines.push(format!("### {scenario}"));
        for fold_mode in [
            fold_mode_name(WhirFoldMode::RawFibers),
            fold_mode_name(WhirFoldMode::LocalInterpolant),
        ] {
            let baseline = records.iter().find(|record| {
                record.scenario_name == scenario
                    && record.whir_fold_mode == fold_mode
                    && record.query_precompute_mode
                        == whir_query_precompute_mode_name(WhirQueryPrecomputeMode::None)
            });
            let precomputed = records.iter().find(|record| {
                record.scenario_name == scenario
                    && record.whir_fold_mode == fold_mode
                    && record.query_precompute_mode
                        == whir_query_precompute_mode_name(
                            WhirQueryPrecomputeMode::ProofCarriedRoundLocal,
                        )
            });
            if let (Some(baseline), Some(precomputed)) = (baseline, precomputed) {
                let mut line = format!(
                    "- minimal_subtree / {}: baseline {:.0} +- {:.0} CU -> proof-carried {:.0} +- {:.0} CU (delta {:+.0})",
                    fold_mode,
                    baseline.total_sbf_mean_cu.unwrap_or(0.0),
                    baseline.total_sbf_stddev_cu.unwrap_or(0.0),
                    precomputed.total_sbf_mean_cu.unwrap_or(0.0),
                    precomputed.total_sbf_stddev_cu.unwrap_or(0.0),
                    precomputed.delta_vs_none_total_cu.unwrap_or(0.0),
                );
                if let Some(delta) = precomputed.delta_vs_none_phase_per_round_queries_cu {
                    line.push_str(&format!(", per-round bucket {:+.0}", delta));
                }
                if let Some(delta) = precomputed.delta_vs_none_verify_cu {
                    line.push_str(&format!(", verify {:+.0}", delta));
                }
                if let Some(delta) = precomputed.proof_bytes_delta_vs_none {
                    line.push_str(&format!(", proof bytes {:+}", delta));
                }
                if let Some(margin) = precomputed.remaining_margin_cu {
                    line.push_str(&format!(", margin {:.0} CU", margin));
                }
                if let Some(share) = precomputed.prior_round0_share_of_full_total {
                    line.push_str(&format!(", prior round-0 share {:.1}%", share * 100.0));
                }
                line.push('.');
                lines.push(line);
            }
        }

        if let Some(best) = records
            .iter()
            .filter(|record| record.scenario_name == scenario)
            .filter(|record| record.total_sbf_mean_cu.is_some())
            .min_by(|lhs, rhs| {
                lhs.total_sbf_mean_cu
                    .partial_cmp(&rhs.total_sbf_mean_cu)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
        {
            lines.push(format!(
                "- best measured stack: {} / {} at {:.0} CU total, {:.0} CU verify, margin {:.0} CU, proof {} bytes, verify {}/{} ok, trace {}/{} complete.",
                best.whir_fold_mode,
                best.query_precompute_mode,
                best.total_sbf_mean_cu.unwrap_or(0.0),
                best.verify_sbf_mean_cu.unwrap_or(0.0),
                best.remaining_margin_cu.unwrap_or(0.0),
                best.proof_bytes,
                best.verify_ok,
                best.verify_total,
                best.trace_ok,
                best.trace_total,
            ));
            let mut breakdown = Vec::new();
            if let Some(value) = best.phase_transcript_setup_mean_cu {
                breakdown.push(format!("transcript setup {:.0}", value));
            }
            if let Some(value) = best.phase_ood_mean_cu {
                breakdown.push(format!("OOD {:.0}", value));
            }
            if let Some(value) = best.phase_per_round_queries_mean_cu {
                breakdown.push(format!("per-round queries {:.0}", value));
            }
            if let Some(value) = best.phase_folding_mean_cu {
                breakdown.push(format!("folding {:.0}", value));
            }
            if let Some(value) = best.phase_final_round_mean_cu {
                breakdown.push(format!("final round {:.0}", value));
            }
            if !breakdown.is_empty() {
                lines.push(format!(
                    "- best-path phase means: {}.",
                    breakdown.join(", ")
                ));
            }
        }
    }

    lines.join("\n")
}

fn write_phase2_roundlocal_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    phase1_summary: &Phase1Summary,
    run_config: &Phase2RunConfig,
    summary_records: &[WhirRoundLocalSummaryRecord],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_roundlocal_summary"] = json!(summary_records);
    if let Some(best) = summary_records
        .iter()
        .filter(|record| record.total_sbf_mean_cu.is_some())
        .min_by(|lhs, rhs| {
            lhs.total_sbf_mean_cu
                .partial_cmp(&rhs.total_sbf_mean_cu)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
    {
        summary_value["biggest_remaining_risk"] = json!(format!(
            "Proof-carried round-local structure moved the best path to {} / {} at {:.0} CU total, but per-round queries still dominate at about {:.0} CU on the best trace. Johnson feasibility now hinges on whether the remaining round-0 algebra can be pushed further without a large proof-byte penalty.",
            best.whir_fold_mode,
            best.query_precompute_mode,
            best.total_sbf_mean_cu.unwrap_or(0.0),
            best.phase_per_round_queries_mean_cu.unwrap_or(0.0)
        ));
    }
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-roundlocal/scenarios.json",
        "results/phase2/whir-roundlocal/raw.jsonl",
        "results/phase2/whir-roundlocal/raw.csv",
        "results/phase2/whir-roundlocal/summary.json",
        "results/phase2/whir-roundlocal/validation.json",
        "results/phase2/whir-roundlocal/trace_diagnostics.json",
        "results/phase2/whir-roundlocal/proofs/",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|existing| existing == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    write_json(&summary_path, &summary_value)?;

    let roundlocal_section = render_whir_roundlocal_section(summary_records);
    let docs = if docs_path.exists() {
        let docs = fs::read_to_string(docs_path)?;
        if docs.contains("## WHIR Proof-Carried Round-Local Structure") {
            replace_markdown_section(
                &docs,
                "## WHIR Proof-Carried Round-Local Structure",
                &roundlocal_section,
            )
        } else if docs.contains("## Shipping Freeze") {
            docs.replace(
                "## Shipping Freeze",
                &format!("{roundlocal_section}\n\n## Shipping Freeze"),
            )
        } else {
            format!("{docs}\n\n{roundlocal_section}")
        }
    } else {
        format!(
            "# Phase 2 Experiments\n\n## Goal\nRun the Phase 2 verifier experiments against the Phase 1 spend model and report measured SBF CU.\n\n## Baseline\n- Phase 1 chosen model: `{}` with RMSE {:.1} CU.\n- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}.\n\n{}",
            phase1_summary.model.chosen.method,
            phase1_summary.model.chosen.metrics.rmse,
            run_config.proof_plan.query_count,
            run_config.proof_plan.fold_arity,
            run_config.proof_plan.target_proof_bytes,
            roundlocal_section
        )
    };
    fs::write(docs_path, docs)?;
    Ok(())
}

fn write_phase2_mul_taxonomy_summary_and_docs(
    root: &Path,
    docs_path: &Path,
    phase1_summary: &Phase1Summary,
    run_config: &Phase2RunConfig,
    records: &[WhirMulTaxonomyMeasurement],
    command: &str,
) -> Result<()> {
    let summary_path = root.join("results/phase2/summary.json");
    let mut summary_value = if summary_path.exists() {
        serde_json::from_reader(File::open(&summary_path)?).unwrap_or_else(|_| json!({}))
    } else {
        json!({})
    };
    if !summary_value.is_object() {
        summary_value = json!({});
    }
    summary_value["generated_at_utc"] = json!(Utc::now().to_rfc3339());
    summary_value["command"] = json!(command);
    summary_value["whir_mul_taxonomy_summary"] = json!(records);
    let raw_artifacts = summary_value
        .get("raw_artifacts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut artifact_strings = raw_artifacts
        .into_iter()
        .filter_map(|value| value.as_str().map(str::to_owned))
        .collect::<Vec<_>>();
    for artifact in [
        "results/phase2/whir-mul-taxonomy/raw.jsonl",
        "results/phase2/whir-mul-taxonomy/raw.csv",
        "results/phase2/summary.json",
        "docs/phase2-experiments.md",
    ] {
        if !artifact_strings.iter().any(|entry| entry == artifact) {
            artifact_strings.push(artifact.to_string());
        }
    }
    summary_value["raw_artifacts"] = json!(artifact_strings);
    summary_value["biggest_remaining_risk"] = json!("Merkle multiproof, payload parsing, and fold-payload comparisons are now measured on the Phase 2 path, but no arithmetic specialization or prover-side representation change has been implemented yet; Johnson still depends on a larger structural win.");
    write_json(&summary_path, &summary_value)?;

    let taxonomy_section = render_whir_mul_taxonomy_section(records);
    let docs = if docs_path.exists() {
        let docs = fs::read_to_string(docs_path)?;
        let docs = replace_markdown_section(
            &docs,
            "## Optional Experiment Results",
            "## Optional Experiment Results\n- Merkle multiproof / `minimal_subtree` was executed via `cargo xtask phase2-multiproof`.\n- Prover-emitted-style multiproof payload parsing was executed via `cargo xtask phase2-multiproof-payload`.\n- Proof-carried fold payload comparison was executed via `cargo xtask phase2-fold-payload`.\n- Multiplication taxonomy was executed via `cargo xtask phase2-mul-taxonomy`.\n- External prover interoperability and dynamic operand-pattern tagging remain scaffolded.",
        );
        let docs =
            replace_markdown_section(&docs, "## WHIR Multiplication Taxonomy", &taxonomy_section);
        docs
    } else {
        format!(
            "# Phase 2 Experiments\n\n## Goal\nRun the Phase 2 verifier experiments against the Phase 1 spend model and report measured SBF CU.\n\n## Baseline\n- Phase 1 chosen model: `{}` with RMSE {:.1} CU.\n- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}.\n\n{}",
            phase1_summary.model.chosen.method,
            phase1_summary.model.chosen.metrics.rmse,
            run_config.proof_plan.query_count,
            run_config.proof_plan.fold_arity,
            run_config.proof_plan.target_proof_bytes,
            taxonomy_section
        )
    };
    let docs = replace_markdown_section(
        &docs,
        "## WHIR Multiproof Payload",
        &render_whir_multiproof_payload_section(
            &serde_json::Deserializer::from_reader(File::open(
                root.join("results/phase2/whir-multiproof-payload/raw.jsonl"),
            )?)
            .into_iter::<WhirMultiproofPayloadMeasurement>()
            .collect::<std::result::Result<Vec<_>, _>>()?,
        ),
    );
    let docs = replace_markdown_section(
        &docs,
        "## WHIR Fold Payload",
        &render_whir_fold_payload_section(
            &serde_json::Deserializer::from_reader(File::open(
                root.join("results/phase2/whir-fold-payload/raw.jsonl"),
            )?)
            .into_iter::<WhirFoldPayloadMeasurement>()
            .collect::<std::result::Result<Vec<_>, _>>()?,
        ),
    );
    fs::write(docs_path, docs)?;
    Ok(())
}

fn build_capacity_v0_freeze_summary(
    _root: &Path,
    transcript_records: &[WhirTranscriptMeasurement],
    multiproof_records: &[WhirMultiproofMeasurement],
    fold_records: &[WhirFoldPayloadMeasurement],
    payload_records: &[WhirMultiproofPayloadMeasurement],
) -> Result<CapacityV0FreezeSummary> {
    const CAP: f64 = 1_400_000.0;
    let scenario_name = "whir_t128_capacity_full";
    let raw_mode = fold_mode_name(WhirFoldMode::RawFibers);
    let local_mode = fold_mode_name(WhirFoldMode::LocalInterpolant);
    let minimal_mode = merkle_mode_name(MerkleProofMode::MinimalSubtree);
    let separate_mode = merkle_mode_name(MerkleProofMode::SeparatePaths);
    let flat_payload = merkle_payload_format_name(WhirMerklePayloadFormat::FlatNodes);
    let canonical_payload = merkle_payload_format_name(WhirMerklePayloadFormat::CanonicalPayload);

    let raw_host = fold_records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.whir_fold_mode == raw_mode
                && record.stage == "host_verify"
        })
        .context("missing raw_fibers host record for whir_t128_capacity_full")?;
    let raw_total =
        whir_fold_payload_stage_values(fold_records, scenario_name, raw_mode, "total_sbf");
    let raw_verify =
        whir_fold_payload_stage_values(fold_records, scenario_name, raw_mode, "verify_sbf");
    let raw_upload =
        whir_fold_payload_stage_values(fold_records, scenario_name, raw_mode, "upload_total");
    let raw_total_mean = sample_mean(&raw_total).context("missing raw total mean")?;
    let raw_total_stddev = sample_stddev(&raw_total).context("missing raw total stddev")?;
    let raw_verify_mean = sample_mean(&raw_verify).context("missing raw verify mean")?;
    let raw_verify_stddev = sample_stddev(&raw_verify).context("missing raw verify stddev")?;
    let raw_upload_mean = sample_mean(&raw_upload).context("missing raw upload mean")?;
    let verification_repetitions_total = fold_records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.whir_fold_mode == raw_mode
                && record.stage == "verify_sbf"
        })
        .count();
    let verification_repetitions_ok = fold_records
        .iter()
        .filter(|record| {
            record.scenario_name == scenario_name
                && record.whir_fold_mode == raw_mode
                && record.stage == "verify_sbf"
                && record.status == "ok"
        })
        .count();

    let query_only_baseline_cu = sample_mean(&whir_transcript_stage_values(
        transcript_records,
        scenario_name,
        "query_only",
        "total_sbf",
    ))
    .context("missing query-only baseline")?;
    let transcript_separate_paths_cu = sample_mean(&whir_transcript_stage_values(
        transcript_records,
        scenario_name,
        "transcript_full",
        "total_sbf",
    ))
    .context("missing transcript full baseline")?;
    let transcript_minimal_subtree_local_cu = sample_mean(&whir_multiproof_stage_values(
        multiproof_records,
        scenario_name,
        minimal_mode,
        "total_sbf",
    ))
    .context("missing minimal subtree local total")?;
    let transcript_minimal_subtree_raw_cu = raw_total_mean;
    let local_interpolant_delta_cu = sample_mean(&whir_fold_payload_stage_values(
        fold_records,
        scenario_name,
        local_mode,
        "total_sbf",
    ))
    .context("missing local total")?
        - raw_total_mean;
    let minimal_subtree_delta_vs_separate_cu = sample_mean(&whir_multiproof_stage_values(
        multiproof_records,
        scenario_name,
        separate_mode,
        "total_sbf",
    ))
    .context("missing separate-path total")?
        - raw_total_mean;

    let mut stage_breakdown = Vec::new();
    for (stage, label) in [
        ("phase_parse", "parse"),
        ("phase_transcript_setup", "transcript setup"),
        ("phase_ood", "OOD"),
        ("phase_per_round_queries", "per-round queries"),
        ("phase_folding", "folding"),
        ("phase_final_round", "final round"),
    ] {
        let values = whir_fold_payload_stage_values(fold_records, scenario_name, raw_mode, stage);
        stage_breakdown.push(CapacityV0StageRecord {
            stage: label.to_string(),
            mean_cu: sample_mean(&values).unwrap_or(0.0),
            stddev_cu: sample_stddev(&values).unwrap_or(0.0),
        });
    }

    let flat_payload_bytes = payload_records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.merkle_proof_mode == minimal_mode
                && record.payload_format == flat_payload
                && record.stage == "host_parse"
        })
        .map(|record| record.payload_bytes)
        .context("missing flat payload bytes")?;
    let payload_flat_nodes_parse_cu = sample_mean(&whir_multiproof_payload_stage_values(
        payload_records,
        scenario_name,
        minimal_mode,
        flat_payload,
        "parse_sbf",
    ))
    .context("missing flat payload parse")?;
    let payload_flat_nodes_total_cu = sample_mean(&whir_multiproof_payload_stage_values(
        payload_records,
        scenario_name,
        minimal_mode,
        flat_payload,
        "total_sbf",
    ))
    .context("missing flat payload total")?;
    let payload_canonical_bytes = payload_records
        .iter()
        .find(|record| {
            record.scenario_name == scenario_name
                && record.merkle_proof_mode == minimal_mode
                && record.payload_format == canonical_payload
                && record.stage == "host_parse"
        })
        .map(|record| record.payload_bytes)
        .context("missing canonical payload bytes")?;
    let payload_canonical_parse_cu = sample_mean(&whir_multiproof_payload_stage_values(
        payload_records,
        scenario_name,
        minimal_mode,
        canonical_payload,
        "parse_sbf",
    ))
    .context("missing canonical payload parse")?;
    let payload_canonical_total_cu = sample_mean(&whir_multiproof_payload_stage_values(
        payload_records,
        scenario_name,
        minimal_mode,
        canonical_payload,
        "total_sbf",
    ))
    .context("missing canonical payload total")?;

    Ok(CapacityV0FreezeSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask phase2-freeze-capacity-v0".to_string(),
        profile_name: "whir-m31-capacity-v0".to_string(),
        shipping_branch: "ship/whir-m31-capacity-v0".to_string(),
        research_branch: "research/johnson-round0".to_string(),
        scenario_name: scenario_name.to_string(),
        security_target_bits: 128.0,
        soundness_assumption: "whir_capacity_full".to_string(),
        arithmetic_kernel_id: "reference_canonical".to_string(),
        extension_kernel_id: "karatsuba".to_string(),
        lift_policy: "late_lift_qm31".to_string(),
        whir_fold_mode: raw_mode.to_string(),
        merkle_proof_mode: minimal_mode.to_string(),
        merkle_payload_format: flat_payload.to_string(),
        statement_binding: "spend-shaped Phase 2 statement".to_string(),
        transcript_path: "full transcript path with Fiat-Shamir, OOD, folding, final round".to_string(),
        proof_bytes: raw_host.proof_bytes,
        verify_mean_cu: raw_verify_mean,
        verify_stddev_cu: raw_verify_stddev,
        upload_mean_cu: raw_upload_mean,
        total_mean_cu: raw_total_mean,
        total_stddev_cu: raw_total_stddev,
        remaining_margin_cu: CAP - raw_total_mean,
        query_only_baseline_cu,
        transcript_separate_paths_cu,
        transcript_minimal_subtree_local_cu,
        transcript_minimal_subtree_raw_cu,
        local_interpolant_delta_cu,
        minimal_subtree_delta_vs_separate_cu,
        stage_breakdown,
        payload_flat_nodes_bytes: flat_payload_bytes,
        payload_flat_nodes_parse_cu,
        payload_flat_nodes_total_cu,
        payload_canonical_bytes,
        payload_canonical_parse_cu,
        payload_canonical_total_cu,
        payload_canonical_delta_cu: payload_canonical_total_cu - payload_flat_nodes_total_cu,
        verification_repetitions_ok,
        verification_repetitions_total,
        raw_artifacts: vec![
            "results/phase2/whir-transcript/raw.jsonl".to_string(),
            "results/phase2/whir-multiproof/raw.jsonl".to_string(),
            "results/phase2/whir-fold-payload/raw.jsonl".to_string(),
            "results/phase2/whir-multiproof-payload/raw.jsonl".to_string(),
            "results/phase2/whir-m31-capacity-v0/summary.json".to_string(),
            "results/phase2/manifests/whir-m31-capacity-v0.json".to_string(),
            "docs/whir-m31-capacity-v0.md".to_string(),
            "docs/state-of-play.md".to_string(),
            "docs/phase2-experiments.md".to_string(),
        ],
        next_research_steps: vec![
            "freeze the shipping branch on the measured capacity profile and keep Johnson off the critical path".to_string(),
            "implement proof-carried round-0 structure for Johnson before any more broad end-to-end reruns".to_string(),
            "run a taxonomy-driven round-0 specialization pass while preserving late_lift_qm31".to_string(),
            "defer external prover-emitted payload interop until after the round-0 representation settles".to_string(),
        ],
    })
}

fn render_capacity_v0_phase2_section(summary: &CapacityV0FreezeSummary) -> String {
    let mut lines = Vec::new();
    lines.push("## Shipping Freeze".to_string());
    lines.push(format!(
        "- Shipping recommendation: freeze `{}` on `{}` now and treat Johnson as a separate round-0 research track.",
        summary.profile_name, summary.scenario_name
    ));
    lines.push(format!(
        "- Exact measured shipping profile: `{}` + `{}` + `{}` + `{}` + `{}` + `{}`.",
        summary.arithmetic_kernel_id,
        summary.extension_kernel_id,
        summary.lift_policy,
        summary.whir_fold_mode,
        summary.merkle_proof_mode,
        summary.merkle_payload_format
    ));
    lines.push(format!(
        "- Measured total: {:.0} +- {:.0} CU, verify {:.0} +- {:.0} CU, upload {:.0} CU, proof {} bytes, remaining margin {:.0} CU, verify ok {}/{}.",
        summary.total_mean_cu,
        summary.total_stddev_cu,
        summary.verify_mean_cu,
        summary.verify_stddev_cu,
        summary.upload_mean_cu,
        summary.proof_bytes,
        summary.remaining_margin_cu,
        summary.verification_repetitions_ok,
        summary.verification_repetitions_total
    ));
    lines.push(format!(
        "- Why this freeze: query-only {:.0} CU -> transcript separate-paths {:.0} CU -> minimal-subtree local {:.0} CU -> minimal-subtree raw {:.0} CU. `local_interpolant` is {:+.0} CU versus raw on the real full path.",
        summary.query_only_baseline_cu,
        summary.transcript_separate_paths_cu,
        summary.transcript_minimal_subtree_local_cu,
        summary.transcript_minimal_subtree_raw_cu,
        summary.local_interpolant_delta_cu
    ));
    lines.push(format!(
        "- Payload decision: keep `{}` for now. For `{}` at `{}`, flat nodes are {} bytes / {:.0} CU total; canonical payload is {} bytes / {:.0} CU total (delta {:+.0} CU).",
        summary.merkle_payload_format,
        summary.scenario_name,
        summary.merkle_proof_mode,
        summary.payload_flat_nodes_bytes,
        summary.payload_flat_nodes_total_cu,
        summary.payload_canonical_bytes,
        summary.payload_canonical_total_cu,
        summary.payload_canonical_delta_cu
    ));
    lines.join("\n")
}

fn render_capacity_v0_doc(summary: &CapacityV0FreezeSummary) -> String {
    let mut lines = Vec::new();
    lines.push("# WHIR M31 Capacity v0".to_string());
    lines.push(String::new());
    lines.push("## Decision".to_string());
    lines.push(format!(
        "Freeze `{}` as the shipping profile now. This is the measured capacity profile that is already under Solana's current 1.4M CU cap on the full transcript path.",
        summary.profile_name
    ));
    lines.push(String::new());
    lines.push("## Frozen Profile".to_string());
    lines.push(format!(
        "- Scenario: `{}` (`{}` bits, `{}`).",
        summary.scenario_name, summary.security_target_bits, summary.soundness_assumption
    ));
    lines.push(format!(
        "- Arithmetic kernel: `{}`.",
        summary.arithmetic_kernel_id
    ));
    lines.push(format!(
        "- Extension kernel: `{}`.",
        summary.extension_kernel_id
    ));
    lines.push(format!("- Lift policy: `{}`.", summary.lift_policy));
    lines.push(format!("- Fold mode: `{}`.", summary.whir_fold_mode));
    lines.push(format!("- Merkle mode: `{}`.", summary.merkle_proof_mode));
    lines.push(format!(
        "- Merkle payload baseline: `{}`.",
        summary.merkle_payload_format
    ));
    lines.push(format!(
        "- Statement binding: {}.",
        summary.statement_binding
    ));
    lines.push(format!("- Transcript path: {}.", summary.transcript_path));
    lines.push(String::new());
    lines.push("## Measurements".to_string());
    lines.push(format!(
        "- Total: {:.0} +- {:.0} CU.",
        summary.total_mean_cu, summary.total_stddev_cu
    ));
    lines.push(format!(
        "- Verify: {:.0} +- {:.0} CU.",
        summary.verify_mean_cu, summary.verify_stddev_cu
    ));
    lines.push(format!("- Upload: {:.0} CU.", summary.upload_mean_cu));
    lines.push(format!("- Proof bytes: {}.", summary.proof_bytes));
    lines.push(format!(
        "- Margin against the 1.4M cap: {:.0} CU.",
        summary.remaining_margin_cu
    ));
    lines.push(String::new());
    lines.push("## Stage Breakdown".to_string());
    for stage in &summary.stage_breakdown {
        lines.push(format!(
            "- {}: {:.0} +- {:.0} CU.",
            stage.stage, stage.mean_cu, stage.stddev_cu
        ));
    }
    lines.push(String::new());
    lines.push("## Comparisons".to_string());
    lines.push(format!(
        "- Query-only baseline: {:.0} CU.",
        summary.query_only_baseline_cu
    ));
    lines.push(format!(
        "- Transcript-inclusive, separate paths: {:.0} CU.",
        summary.transcript_separate_paths_cu
    ));
    lines.push(format!(
        "- Transcript-inclusive, minimal_subtree + local_interpolant: {:.0} CU.",
        summary.transcript_minimal_subtree_local_cu
    ));
    lines.push(format!(
        "- Transcript-inclusive, minimal_subtree + raw_fibers: {:.0} CU.",
        summary.transcript_minimal_subtree_raw_cu
    ));
    lines.push(format!(
        "- `local_interpolant` delta on the measured full path: {:+.0} CU.",
        summary.local_interpolant_delta_cu
    ));
    lines.push(String::new());
    lines.push("## Payload Decision".to_string());
    lines.push(format!(
        "- Flat nodes: {} bytes, parse {:.0} CU, total {:.0} CU.",
        summary.payload_flat_nodes_bytes,
        summary.payload_flat_nodes_parse_cu,
        summary.payload_flat_nodes_total_cu
    ));
    lines.push(format!(
        "- Canonical payload: {} bytes, parse {:.0} CU, total {:.0} CU.",
        summary.payload_canonical_bytes,
        summary.payload_canonical_parse_cu,
        summary.payload_canonical_total_cu
    ));
    lines.push(format!(
        "- Shipping decision: keep `{}` until a real prover-emitted payload beats it on measured total CU.",
        summary.merkle_payload_format
    ));
    lines.push(String::new());
    lines.push("## Branch Split".to_string());
    lines.push(format!("- Shipping branch: `{}`.", summary.shipping_branch));
    lines.push(format!("- Research branch: `{}`.", summary.research_branch));
    lines.push(String::new());
    lines.push("## Research Order".to_string());
    for (index, step) in summary.next_research_steps.iter().enumerate() {
        lines.push(format!("{}. {}", index + 1, step));
    }
    lines.push(String::new());
    lines.push("## Reproduction".to_string());
    lines.push("- `cargo xtask phase2-transcript`".to_string());
    lines.push("- `cargo xtask phase2-multiproof`".to_string());
    lines.push("- `cargo xtask phase2-fold-payload`".to_string());
    lines.push("- `cargo xtask phase2-multiproof-payload`".to_string());
    lines.push("- `cargo xtask phase2-freeze-capacity-v0`".to_string());
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} from `{}`._",
        summary.generated_at_utc, summary.command
    ));
    lines.join("\n")
}

fn render_state_of_play(summary: &CapacityV0FreezeSummary) -> String {
    let mut lines = Vec::new();
    lines.push("# State Of Play".to_string());
    lines.push(String::new());
    lines.push("## Snapshot".to_string());
    lines.push("- Date: April 19, 2026".to_string());
    lines.push("- Workspace state: Phase 1 and Phase 2 experiment harnesses are working, the capacity shipping profile is now frozen from measured data, and Johnson is explicitly a research track.".to_string());
    lines.push(String::new());
    lines.push("## Shipping Track".to_string());
    lines.push(format!(
        "- Shipping profile: `{}` on `{}`.",
        summary.profile_name, summary.scenario_name
    ));
    lines.push(format!(
        "- Exact measured config: `{}` + `{}` + `{}` + `{}` + `{}` + `{}`.",
        summary.arithmetic_kernel_id,
        summary.extension_kernel_id,
        summary.lift_policy,
        summary.whir_fold_mode,
        summary.merkle_proof_mode,
        summary.merkle_payload_format
    ));
    lines.push(format!(
        "- Measured total: {:.0} CU with {:.0} CU margin against the 1.4M cap.",
        summary.total_mean_cu, summary.remaining_margin_cu
    ));
    lines.push("- This is the shortest path to a real vertical slice. The under-construction native WHIR track is not yet the frozen shipping artifact.".to_string());
    lines.push(String::new());
    lines.push("## Research Track".to_string());
    lines.push(format!("- Research branch: `{}`.", summary.research_branch));
    lines.push("- Johnson is treated as a round-0 optimization problem, not as the current shipping target.".to_string());
    lines.push("- Heap work and generic payload churn are deprioritized; the next wins must come from round-0 algebraic cost reduction.".to_string());
    lines.push(String::new());
    lines.push("## What We Now Know".to_string());
    lines.push(format!(
        "- `minimal_subtree` is a real end-to-end win against separate paths: {:+.0} CU on the frozen capacity scenario.",
        summary.minimal_subtree_delta_vs_separate_cu
    ));
    lines.push(format!(
        "- The current repo-local `local_interpolant` path is not a shipping win on the full path: {:+.0} CU versus raw.",
        summary.local_interpolant_delta_cu
    ));
    lines.push(format!(
        "- Canonical multiproof payloads are not ready for shipping: {:+.0} CU on the frozen scenario versus flat nodes.",
        summary.payload_canonical_delta_cu
    ));
    lines.push("- The next serious Johnson work should target proof-carried round-local structure and profile-specific round-0 specialization.".to_string());
    lines.push(String::new());
    lines.push("## Recommended Next Steps".to_string());
    lines.push(format!(
        "1. Build the real native vertical slice around `{}`.",
        summary.profile_name
    ));
    lines.push("2. Implement proof-carried round-0 structure for Johnson.".to_string());
    lines.push("3. Run a multiplication-taxonomy-driven round-0 specialization pass.".to_string());
    lines.push(
        "4. Revisit prover-emitted payload interop only after the round-0 representation settles."
            .to_string(),
    );
    lines.push(String::new());
    lines.push("## Primary Artifacts".to_string());
    for artifact in &summary.raw_artifacts {
        lines.push(format!("- `{artifact}`"));
    }
    lines.join("\n")
}

fn render_phase2_report(
    run_config: &Phase2RunConfig,
    phase1_summary: &Phase1Summary,
    arithmetic: &[ArithmeticMeasurement],
    extension: &[ExtensionMeasurement],
    skeleton: &[EndToEndMeasurement],
    whir_query: &[WhirQueryMeasurement],
    whir_transcript: &[WhirTranscriptMeasurement],
    summary: &Phase2Summary,
    savings: &SavingsEstimate,
) -> String {
    let mut lines = Vec::new();
    lines.push("# Phase 2 Experiments".to_string());
    lines.push(String::new());
    lines.push("## Goal".to_string());
    lines.push("Run the highest expected-value CU-reduction experiments for a WHIR-shaped transparent verifier on Solana using real SBF measurements, fixed-layout proof parsing, and the existing Phase 1 scorer.".to_string());
    lines.push(String::new());
    lines.push("## Discovery Summary".to_string());
    lines.push("- Workspace root still centers on the Phase 1 scaffold: `xtask`, `programs/phase1-probe`, `crates/svm-cost-model`, `examples/phase1`, and `phase1_results`.".to_string());
    lines.push("- No dedicated Phase 2 crate tree existed at the workspace root. This run reuses the existing SBF probe and extends it with shared Phase 2 arithmetic and skeleton-verifier logic.".to_string());
    lines.push("- Vendored `third_party/solana-pqzk-fullchain` remains the main local source of on-chain verifier, custom heap, and Winterfell/FRI stack-discipline reference code.".to_string());
    lines.push("- Baseline commands already present before this work: `cargo xtask phase1`, `cargo xtask phase1-next`, and `cargo run -p svm-cost-model --bin phase1-score -- phase1_results/summary.json <profile>`.".to_string());
    lines.push(String::new());
    lines.push("## Baseline".to_string());
    lines.push(format!(
        "- Phase 1 chosen model: `{}` with RMSE {:.1} CU.",
        phase1_summary.model.chosen.method, phase1_summary.model.chosen.metrics.rmse
    ));
    lines.push("- Current WHIR spend floor from the existing Phase 1 report is still above the 1.4M CU transaction cap.".to_string());
    lines.push(format!(
        "- Phase 2 run config: query_count={}, fold_arity={}, proof_bytes={}, merkle_depth={}, merkle_paths={}, upload_chunk_size={}, verify_repeat={}.",
        run_config.proof_plan.query_count,
        run_config.proof_plan.fold_arity,
        run_config.proof_plan.target_proof_bytes,
        run_config.proof_plan.merkle_depth,
        run_config.proof_plan.merkle_paths,
        run_config.upload_chunk_size,
        run_config.skeleton_repeat_inside_instruction
    ));
    lines.push(String::new());
    lines.push("## Experiment Design".to_string());
    lines.push("- Experiment A: five M31 reduction kernels measured on host and SBF across raw mul, square, mul-add, short inner product, Horner, denominator chain, and a verifier-shaped fold step.".to_string());
    lines.push("- Experiment B: CM31/QM31 schoolbook vs Karatsuba kernels measured in isolation and inside the skeleton verifier, plus eager-QM31 vs late-lift-QM31 policy comparison.".to_string());
    lines.push("- Experiment C: raw-fiber vs local-interpolant fold representation comparison on the same statement digest, query schedule, proof size target, and Merkle schedule.".to_string());
    lines.push("- Experiment D: a higher-fidelity WHIR query evaluator that reuses the winning kernels on derived WHIR schedules from the Phase 1 spend model, with explicit round-by-round query counts and separate opening/selector denominator chains.".to_string());
    lines.push("- Transport is included in end-to-end totals by measuring upload CU separately and adding it to verify CU.".to_string());
    lines.push(String::new());
    lines.push("## Measured vs Inferred vs Unknown".to_string());
    lines.push("- Measured directly: host timings, SBF CU, proof bytes, upload chunk count, fixed heap-frame request, and Phase 2 instrumentation counters from the shared host/SBF code path.".to_string());
    lines.push("- Inferred for Phase 1 scorer projection: `field_mul_ops`, `extension_mul_ops`, and `field_inv_ops` are projected from Phase 2 counters into the coarser Phase 1 feature schema.".to_string());
    lines.push("- Unknown: code-size deltas per arithmetic kernel, native WHIR transcript/proof-layout interaction effects beyond the current statement-bound proxy, and multi-validator drift beyond the local Agave toolchain.".to_string());
    lines.push(String::new());
    lines.push("## Experiment A Results".to_string());
    lines.push(format!(
        "- Raw mul winner on SBF: `{}`.",
        summary.arithmetic_winner_raw_mul
    ));
    lines.push(format!(
        "- Verifier-shaped fold-step winner on SBF: `{}`. This is the recommended new base-field kernel baseline.",
        summary.arithmetic_winner_verifier_kernel
    ));
    lines.push(format!(
        "- Measured arithmetic records: {}.",
        arithmetic.len()
    ));
    lines.push(String::new());
    lines.push("## Experiment B Results".to_string());
    lines.push(format!(
        "- Extension kernel winner on the skeleton-shaped accumulator workload: `{}`.",
        summary.extension_kernel_winner
    ));
    lines.push(format!(
        "- Lift-policy winner in the end-to-end skeleton matrix: `{}`.",
        summary.lift_policy_winner
    ));
    lines.push(format!(
        "- Measured extension records: {}.",
        extension.len()
    ));
    lines.push(String::new());
    lines.push("## Experiment C Results".to_string());
    lines.push(format!(
        "- Fold-mode winner in the end-to-end skeleton matrix: `{}`.",
        summary.whir_fold_winner
    ));
    lines.push("- The fold-mode comparison is explicitly a narrow experimental packaging study: transcript/challenge derivation stays fixed across modes, while the proof payload switches between raw local values and prepackaged local coefficients.".to_string());
    lines.push(format!(
        "- Measured end-to-end records: {}.",
        skeleton.len()
    ));
    lines.push(String::new());
    lines.push("## Higher-Fidelity WHIR Query Evaluator".to_string());
    lines.push(format!(
        "- Best measured higher-fidelity variant: `{}`.",
        summary.whir_query_high_fidelity_winner
    ));
    lines.push("- This evaluator is still experimental rather than a production verifier, but it now uses the Phase 1 WHIR round schedule, the same query-count regimes behind the old 2.5M / 3.2M / 5.7M bounds, concrete Spend statement row breakdowns to derive semantically meaningful query records, eight-point local evaluation, and explicit opening/selector denominator chains.".to_string());
    for line in &summary.whir_query_translation_summary {
        lines.push(format!("- {line}."));
    }
    lines.push(format!(
        "- Measured higher-fidelity records: {}.",
        whir_query.len()
    ));
    lines.push(String::new());
    lines.push("## WHIR Transcript Path".to_string());
    lines.push("- Executed on SBF: transcript absorption/challenge derivation through `sol_sha256`, commitment OOD checks, per-round query PoW checks, folding verification across all WHIR rounds, final-round query verification, and transcript consistency checks.".to_string());
    lines.push("- Executed locally for correctness validation: valid transcript proofs were accepted; deliberately wrong challenge, missing-query, incorrect-folding, and truncated proofs were rejected.".to_string());
    lines.push("- Scaffolded only: external proof interop with the official Plonky3 WHIR prover/verifier. The checkout at `/tmp/plonky3-official` commit `0f87f2b543a01880274965c410bf804c124f5046` does not contain the referenced `whir/src/verifier/mod.rs` entrypoint or a runnable end-to-end verifier surface.".to_string());
    lines.push("- Honest caveat: the current PoW step measures verifier-side transcript-bound witness checks, not prover-side grinding work.".to_string());
    for line in &summary.whir_transcript_comparison_summary {
        lines.push(format!("- {line}."));
    }
    let stage_order = [
        ("phase_parse", "parse"),
        ("phase_transcript_setup", "transcript setup"),
        ("phase_ood", "OOD"),
        ("phase_per_round_queries", "per-round queries"),
        ("phase_folding", "folding"),
        ("phase_final_round", "final round"),
    ];
    for scenario in scenario_names_from_transcript(whir_transcript) {
        lines.push(format!("- `{scenario}` phase breakdown:"));
        for (stage, label) in stage_order {
            let values =
                whir_transcript_stage_values(whir_transcript, &scenario, "transcript_full", stage);
            if let (Some(mean), Some(stddev)) = (sample_mean(&values), sample_stddev(&values)) {
                lines.push(format!("  - {label}: {:.0} +- {:.0} CU.", mean, stddev));
            }
        }
    }
    for line in &summary.whir_transcript_remaining_margin_summary {
        lines.push(format!("- {line}."));
    }
    lines.push(format!(
        "- Measured transcript-path records: {}.",
        whir_transcript.len()
    ));
    lines.push(String::new());
    lines.push("## Optional Experiment Results".to_string());
    lines.push("- Minimal-subtree / multiproof Merkle mode and heap-streaming audit were not executed in this run. The config surface already reserves `MerkleProofMode` for that follow-up.".to_string());
    lines.push(String::new());
    lines.push("## Predicted vs Measured Comparison".to_string());
    lines.push("- Each end-to-end skeleton variant is scored with the Phase 1 chosen model plus the Phase 1 core/transport component models when present.".to_string());
    lines.push("- The current Phase 1 coefficients materially over-predict this narrow M31/QM31 skeleton path because the scorer was fit on coarser verifier proxies, not these explicit field kernels. Treat the absolute error here as a calibration diagnostic, not as a replacement for the measured CU.".to_string());
    if let Some(best_total) = skeleton
        .iter()
        .filter(|record| {
            record.stage == "total_sbf" && record.variant == summary.combined_best_variant
        })
        .min_by_key(|record| record.actual_cu.unwrap_or(u64::MAX))
    {
        lines.push(format!(
            "- Best variant `{}`: measured total {:.0} CU, predicted {:.1} CU, abs error {:.1} CU, rel error {:.2}%.",
            best_total.variant,
            best_total.actual_cu.unwrap_or_default() as f64,
            best_total.predicted_cu.unwrap_or_default(),
            best_total.abs_error_cu.unwrap_or_default(),
            best_total.rel_error.unwrap_or_default() * 100.0
        ));
    }
    if let Some(best_query_total) = whir_query
        .iter()
        .filter(|record| {
            record.stage == "total_sbf" && record.variant == summary.whir_query_high_fidelity_winner
        })
        .min_by_key(|record| record.actual_cu.unwrap_or(u64::MAX))
    {
        lines.push(format!(
            "- Higher-fidelity `{}` on `{}`: measured total {:.0} CU, legacy bound {:.1} CU, measured-feature prediction {:.1} CU.",
            best_query_total.variant,
            best_query_total.scenario_name,
            best_query_total.actual_cu.unwrap_or_default() as f64,
            best_query_total.legacy_bound_cu,
            best_query_total.predicted_cu.unwrap_or_default()
        ));
    }
    lines.push(String::new());
    lines.push("## Combined Best-Case Configuration".to_string());
    lines.push(format!(
        "- `{}` + `{}` + `{}` + `{}`.",
        summary.arithmetic_winner_verifier_kernel,
        summary.extension_kernel_winner,
        summary.lift_policy_winner,
        summary.whir_fold_winner
    ));
    lines.push(format!(
        "- Best measured skeleton variant: `{}`.",
        summary.combined_best_variant
    ));
    lines.push(String::new());
    lines.push("## Estimated Total CU Savings".to_string());
    lines.push(format!(
        "- Estimated savings versus the current 1.45M-CU working point: {:.1} CU.",
        savings.estimated_savings_cu
    ));
    lines.push(format!(
        "- Estimated post-change total: {:.1} CU.",
        savings.estimated_post_change_cu
    ));
    lines.push(format!(
        "- Estimated remaining headroom against the 1.4M cap: {:.1} CU.",
        savings.estimated_headroom_cu
    ));
    lines.push(String::new());
    lines.push("## Open Risks".to_string());
    lines.push(format!("- {}", summary.biggest_remaining_risk));
    lines.push("- The fold-mode experiment keeps challenge derivation fixed across layouts to isolate verifier work; that is useful for measurement but not yet a production-complete proof-layout commitment story.".to_string());
    lines.push("- The transcript-path measurements cover verifier work only. Real prover-side PoW grinding cost and proof-shape drift still need external prover interop before this can be called production-complete.".to_string());
    lines.push(String::new());
    lines.push("## Recommended Next Steps Toward SpendV0".to_string());
    lines.push("- Land external prover/verifier interop once the upstream WHIR end-to-end verifier surface exists, then re-run the same transcript matrix against official proof bytes.".to_string());
    lines.push("- Replace the verifier-side PoW witness shortcut with real transcript-bound grinding so query and folding PoW costs reflect the production protocol instead of only verifier checks.".to_string());
    lines.push("- Execute the reserved minimal-subtree Merkle experiment to see whether proof-byte and hash-call savings survive fixed-layout parsing on the transcript-inclusive path.".to_string());
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} UTC from `cargo xtask phase2-experiments`._",
        Utc::now().to_rfc3339()
    ));
    lines.join("\n")
}
