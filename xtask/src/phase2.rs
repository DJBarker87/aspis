use super::*;
use phase1_probe::{
    build_phase2_arithmetic_instruction, build_phase2_extension_instruction,
    build_phase2_proof_bytes, build_phase2_skeleton_instruction,
    build_phase2_whir_query_instruction, build_phase2_whir_query_proof_bytes,
    run_phase2_arithmetic_bench, run_phase2_extension_bench, run_phase2_skeleton_verify,
    run_phase2_whir_query_verify, ArithmeticKernelId, ArithmeticWorkloadId, ExtensionKernelId,
    ExtensionWorkloadId, LazyReductionMode, LiftPolicy, MerkleProofMode, Phase2ArithmeticConfig,
    Phase2Counters, Phase2ExtensionConfig, Phase2ProofPlan, Phase2VerifierConfig,
    Phase2WhirQueryPlan, Phase2WhirRoundPlan, Phase2WhirStatementShape, ReductionMode,
    WhirFoldMode, PHASE2_WHIR_MAX_OPENING_TERMS, PHASE2_WHIR_MAX_ROUNDS,
};
use serde::Serialize;
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

#[derive(Clone, Debug, Serialize)]
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
    qm31_mul_ops: u64,
    qm31_square_ops: u64,
    qm31_inv_ops: u64,
    qm31_mul_const_ops: u64,
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
            qm31_mul_ops: value.qm31_mul_ops,
            qm31_square_ops: value.qm31_square_ops,
            qm31_inv_ops: value.qm31_inv_ops,
            qm31_mul_const_ops: value.qm31_mul_const_ops,
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
    let manifests_dir = results_root.join("manifests");
    fs::create_dir_all(&arithmetic_dir)?;
    fs::create_dir_all(&lift_dir)?;
    fs::create_dir_all(&fold_dir)?;
    fs::create_dir_all(&whir_query_dir)?;
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
        biggest_remaining_risk: savings.biggest_remaining_risk.clone(),
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
            &summary,
            &savings,
        ),
    )?;

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

fn render_phase2_report(
    run_config: &Phase2RunConfig,
    phase1_summary: &Phase1Summary,
    arithmetic: &[ArithmeticMeasurement],
    extension: &[ExtensionMeasurement],
    skeleton: &[EndToEndMeasurement],
    whir_query: &[WhirQueryMeasurement],
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
    lines.push(String::new());
    lines.push("## Recommended Next Steps Toward SpendV0".to_string());
    lines.push("- Port the same winning kernels and late-lift policy into a native WHIR prover/verifier transcript path so the current statement-bound proxy can be replaced by real proof bytes and challenge flow.".to_string());
    lines.push("- Execute the reserved minimal-subtree Merkle experiment to see whether proof-byte and hash-call savings survive fixed-layout parsing on SBF.".to_string());
    lines.push("- Replace the fixed local-neighborhood proxy with the exact packaged local-interpolant payload emitted by the eventual WHIR prover so the fold-mode result can be re-measured without transcript-isolation shortcuts.".to_string());
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} UTC from `cargo xtask phase2-experiments`._",
        Utc::now().to_rfc3339()
    ));
    lines.join("\n")
}
