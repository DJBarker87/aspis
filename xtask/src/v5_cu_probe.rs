//! Local-validator measurements for v5 layer-zero and Component-B work.
//!
//! Mode 9 carries only authenticated width-16 C1 and C2 records. The host-only
//! tag-66 diagnostic fixture appends the retired width-26 comparison records
//! as a sidecar that the accepted mode-9 grammar never parses. The program
//! marks account borrowing, parsing, power preparation, and output allocation
//! separately from the hash-and-combine kernel. Component-B modes separately
//! mark claim aggregation, exact prototype covector derivation, and the shared
//! relation-fold work. Marker deltas include fixed marker/logging overhead.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use serde::Serialize;
use sha2::{Digest as _, Sha256};
use solana_sdk::pubkey::Pubkey;

use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CIRCLE_LINE_TAGS,
};
use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
use aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES;
use aspis_core::state_only_sumcheck::{
    decode_state_only_polynomial, state_only_boundary_sum, STATE_ONLY_SUMCHECK_ROUND_BYTES,
};
use aspis_core::transcript::label;
use aspis_prover::circle_candidate::{
    combined_layer_leaves, fold_candidate_codeword_round_for_domain_log, COMBINED_LAYER_LEAF_BYTES,
};
use aspis_prover::state_only_private_openings::{
    build_state_only_private_merkle_tree, serialize_state_only_private_opening,
    StateOnlyPrivateMerkleTree,
};
use aspis_prover::v5_mask::real_host_proof::{
    build_v5_production_host_artifact_cap17, build_v5_real_host_artifact, V5HostGoodGateEvaluation,
    V5HostPcsSalts, V5HostPowBits, V5ProductionAttemptInputs, V5PublicFsSalts, V5RealHostArtifact,
    V5RealHostInputs, V5_PUBLIC_FS_SALT_BYTES,
};
use aspis_prover::v5_mask::spend_messages::{
    build_v5_cu_stress_pcs_artifact, verify_v5_pcs_openings, V5BuiltPcsOpenings, V5PcsSalts,
    V5SpendMessages, V5_C1_LANES, V5_C2_LANES, V5_LATER_LAYERS, V5_LAYER_ZERO_LEAVES,
    V5_PRIVATE_DEPTHS, V5_TOTAL_LANES,
};
use aspis_prover::v5_mask::{
    sample_atomic_m31_lane_masks, Qm31WordSource, V5_CODEWORD_LEN, V5_DOMAIN_LOG, V5_TRACE_ROWS,
};
use aspis_prover::v5_sumcheck_mask::V5SumcheckMask;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3;
use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
use aspis_statement::{
    derive_nullifier, derive_owner_key, note_commitment, output_commitment,
    AtomicPaymentStatementV4, Digest, MerklePath, SpendPublic, SpendWitness,
};
use aspis_verifier::atomic_payment::{
    atomic_nullifier_address, AtomicPoolStateV2, ATOMIC_NULLIFIER_MARKER_LEN, ATOMIC_POOL_STATE_LEN,
};
use aspis_verifier::v5_atomic_terminal::{
    encode_v5_atomic_terminal_context, V5AtomicTerminalChallenges,
};
use aspis_verifier::v5_cu_probe::wire_skeleton::{
    build_deterministic_synthetic_v5_wire, V5_WIRE_OPENINGS_OFFSET, V5_WIRE_TERMINALS_OFFSET,
};
use aspis_verifier::v5_cu_probe::{
    build_v5_complete_relation_stress_tail_for_diagnostics, probe_sink, v5_complete_queries,
    v5_complete_transcript_before_final, V5_CU_PROBE_ACCOUNT_BYTES, V5_CU_PROBE_ACCOUNT_MAGIC,
    V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET, V5_CU_PROBE_BATCH_NONCE_BYTES,
    V5_CU_PROBE_BATCH_NONCE_OFFSET, V5_CU_PROBE_B_BLOCK_SELECTORS,
    V5_CU_PROBE_B_COMPACT_DYNAMIC_HEAP_BYTES, V5_CU_PROBE_B_COMPACT_STATE_BYTES,
    V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW, V5_CU_PROBE_B_INITIAL_STATE_ROW,
    V5_CU_PROBE_B_MASK_COORDINATES, V5_CU_PROBE_B_PAD_COORDINATES, V5_CU_PROBE_C2_COLUMNS,
    V5_CU_PROBE_C2_OFFSET, V5_CU_PROBE_C2_RECORD_BYTES, V5_CU_PROBE_C2_VALUE_BYTES,
    V5_CU_PROBE_CANDIDATE_C1_COLUMNS, V5_CU_PROBE_CANDIDATE_C1_OFFSET,
    V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES, V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES,
    V5_CU_PROBE_COMPOSITE_MODE, V5_CU_PROBE_DIAGNOSTIC_ACCOUNT_BYTES,
    V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET, V5_CU_PROBE_FINAL_NONCE_OFFSET,
    V5_CU_PROBE_GAMMA_OFFSET, V5_CU_PROBE_GENERIC16_FUSED_MODE,
    V5_CU_PROBE_GENERIC16_NONFUSED_MODE, V5_CU_PROBE_GENERIC26_FUSED_MODE,
    V5_CU_PROBE_GENERIC26_NONFUSED_MODE, V5_CU_PROBE_PREFIX_OFFSET,
    V5_CU_PROBE_PRIVATE_ROOTS_OFFSET, V5_CU_PROBE_PRODUCTION26_MODE,
    V5_CU_PROBE_PRODUCTION_C1_COLUMNS, V5_CU_PROBE_PRODUCTION_C1_OFFSET,
    V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES, V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES,
    V5_CU_PROBE_PROVISIONAL_QUERIES, V5_CU_PROBE_QUERY_COUNT, V5_CU_PROBE_QUERY_SELECTOR_OFFSET,
    V5_CU_PROBE_RELATION3_MODE, V5_CU_PROBE_RELATION4_COMPACT_MODE,
    V5_CU_PROBE_RELATION4_DENSE_MODE, V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE,
    V5_CU_PROBE_RELATION_ALPHAS_OFFSET, V5_CU_PROBE_RELATION_CLAIMS_OFFSET,
    V5_CU_PROBE_RELATION_CLAIMS_PER_LANE, V5_CU_PROBE_RELATION_DENSE_VALUES,
    V5_CU_PROBE_RELATION_FINAL_OFFSET, V5_CU_PROBE_RELATION_FINAL_VALUES,
    V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_BYTES, V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET,
    V5_CU_PROBE_RELATION_FOLDS, V5_CU_PROBE_RELATION_LANES, V5_CU_PROBE_RELATION_LOG_ROWS,
    V5_CU_PROBE_RELATION_POINTS, V5_CU_PROBE_RELATION_POINTS_OFFSET,
    V5_CU_PROBE_RELATION_SCALES_OFFSET, V5_CU_PROBE_RELATION_STRESS_OFFSET, V5_CU_PROBE_TAG,
    V5_CU_PROBE_WIRE_BYTES, V5_CU_REAL_PREFIX_C1_ROOT_OFFSET, V5_CU_REAL_PREFIX_C2_ROOT_OFFSET,
    V5_CU_REAL_PREFIX_CLAIMS_OFFSET, V5_CU_REAL_PREFIX_HEADER_BYTES,
    V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET, V5_CU_REAL_PREFIX_MAGIC,
    V5_CU_REAL_PREFIX_RESERVED_OFFSET, V5_CU_REAL_PREFIX_SUMCHECK_OFFSET,
    V5_CU_REAL_PREFIX_TERMINAL_OFFSET, V5_CU_REAL_PREFIX_VERSION,
};
use aspis_verifier::v5_full_transaction::{
    V5_FULL_CU_TRANSACTION_TAG, V5_FULL_CU_TRANSACTION_WIRE_BYTES,
};
use aspis_verifier::v5_relation_stress::{
    V5_RELATION_STRESS_BYTES, V5_RELATION_STRESS_CIRCLE_OFFSET, V5_RELATION_STRESS_FINAL_OFFSET,
    V5_RELATION_STRESS_LINE_OFFSET, V5_RELATION_STRESS_MIX_OFFSET, V5_RELATION_STRESS_OOD_OFFSET,
    V5_RELATION_STRESS_SUMCHECK_OFFSET,
};
use aspis_verifier::PROOF_ACCOUNT_HEADER_LEN;

use crate::spend_measure::{
    parse_cu_markers, simulate_atomic_program_account_instructions,
    simulate_atomic_program_account_instructions_with_absent_marker,
    simulate_readonly_program_account_instructions, StatelessSimulationResult,
};

const REPEATS: usize = 3;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum V5NullifierMarkerFixtureMode {
    MissingCreateCpi,
    PreloadedProgramOwnedControl,
}

const V5_DEVNET_PATH_MARKER_MODE: V5NullifierMarkerFixtureMode =
    V5NullifierMarkerFixtureMode::MissingCreateCpi;
const V5_PRELOADED_MARKER_CONTROL_MODE: V5NullifierMarkerFixtureMode =
    V5NullifierMarkerFixtureMode::PreloadedProgramOwnedControl;

impl V5NullifierMarkerFixtureMode {
    const fn label(self) -> &'static str {
        match self {
            Self::MissingCreateCpi => "missing-system-owned-create-cpi",
            Self::PreloadedProgramOwnedControl => "preloaded-program-owned-control",
        }
    }

    const fn preloads_marker(self) -> bool {
        matches!(self, Self::PreloadedProgramOwnedControl)
    }

    const fn requires_system_program_cpi(self) -> bool {
        matches!(self, Self::MissingCreateCpi)
    }

    const fn simulation_helper(self) -> &'static str {
        match self {
            Self::MissingCreateCpi => {
                "spend_measure::simulate_atomic_program_account_instructions_with_absent_marker"
            }
            Self::PreloadedProgramOwnedControl => {
                "spend_measure::simulate_atomic_program_account_instructions"
            }
        }
    }
}

const PROVISIONAL_FORECAST_ENVELOPE_CU: i64 = 112_000;
const FIBER_SLOTS: usize = 4;
const M31_BYTES: usize = 4;
const QM31_BYTES: usize = 16;
const MODE_COUNT: usize = 10;
const PARSE_START_MARKER: &str = "v5-probe-parse-start";
const PREFIX_START_MARKER: &str = "v5-probe-prefix-start";
const PREFIX_COMPLETE_MARKER: &str = "v5-probe-prefix-complete";
const QUERY_BINDING_START_MARKER: &str = "v5-probe-query-binding-start";
const QUERY_BINDING_COMPLETE_MARKER: &str = "v5-probe-query-binding-complete";
const PRIVATE_START_MARKER: &str = "v5-probe-private-start";
const PRIVATE_COMPLETE_MARKER: &str = "v5-probe-private-complete";
const KERNEL_START_MARKER: &str = "v5-probe-kernel-start";
const KERNEL_COMPLETE_MARKER: &str = "v5-probe-kernel-complete";
const FRI_PREPARE_START_MARKER: &str = "v5-probe-fri-prepare-start";
const FRI_PREPARE_COMPLETE_MARKER: &str = "v5-probe-fri-prepare-complete";
const FRI_START_MARKER: &str = "v5-probe-fri-start";
const FRI_COMPLETE_MARKER: &str = "v5-probe-fri-complete";
const RELATION_STRESS_START_MARKER: &str = "v5-probe-relation-stress-start";
const RELATION_STRESS_COMPLETE_MARKER: &str = "v5-probe-relation-stress-complete";
const CLAIMS_COMPLETE_MARKER: &str = "v5-probe-claims-complete";
const COVECTOR_COMPLETE_MARKER: &str = "v5-probe-covector-complete";
const COMPOSITE_HEAP_PREFIX: &str = "aspis-heap:v5-composite-high-water=";

#[derive(Clone, Copy)]
struct Mode {
    id: u8,
    name: &'static str,
    description: &'static str,
}

const MODES: [Mode; MODE_COUNT] = [
    Mode {
        id: V5_CU_PROBE_PRODUCTION26_MODE,
        name: "production26",
        description:
            "current production 26-C1/3-C2 helper, already using the fused three-product C2 sum",
    },
    Mode {
        id: V5_CU_PROBE_GENERIC26_NONFUSED_MODE,
        name: "generic26_nonfused",
        description: "generic 26-C1 dot and two-plus-one C2 products",
    },
    Mode {
        id: V5_CU_PROBE_GENERIC16_NONFUSED_MODE,
        name: "generic16_nonfused",
        description: "generic 16-C1 dot and two-plus-one C2 products",
    },
    Mode {
        id: V5_CU_PROBE_GENERIC16_FUSED_MODE,
        name: "generic16_fused",
        description: "generic 16-C1 dot and exact fused three-product C2 accumulator",
    },
    Mode {
        id: V5_CU_PROBE_GENERIC26_FUSED_MODE,
        name: "generic26_fused",
        description: "generic 26-C1 dot and exact fused three-product C2 accumulator",
    },
    Mode {
        id: V5_CU_PROBE_RELATION3_MODE,
        name: "relation_3_claims",
        description: "nineteen lanes with three gamma-aggregated claims and the existing relation folds",
    },
    Mode {
        id: V5_CU_PROBE_RELATION4_DENSE_MODE,
        name: "relation_4_claims_shared_dense",
        description: "nineteen lanes with a kappa^3-scaled fourth gamma-aggregated claim and prototype row covector in the existing relation folds",
    },
    Mode {
        id: V5_CU_PROBE_RELATION4_STANDALONE_DOT_MODE,
        name: "relation_4_claims_standalone_dot_rejected",
        description: "rejected control: kappa^3-scaled fourth claim and prototype covector followed by a standalone 1023-term row dot",
    },
    Mode {
        id: V5_CU_PROBE_RELATION4_COMPACT_MODE,
        name: "relation_4_claims_compact_degree27",
        description: "nineteen fourth claims plus ten aligned degree-27 blocks and one initial-state singleton carried through the existing four relation folds without a dense vector",
    },
    Mode {
        id: V5_CU_PROBE_COMPOSITE_MODE,
        name: "composite_width16_compact_b",
        description: "one invocation running the width-16 q18 layer-zero kernel followed by the exact compact degree-27 Component-B claim, setup, four folds, and final dot",
    },
];

#[derive(Debug, Serialize)]
pub struct ModeMeasurement {
    pub mode: u8,
    pub name: String,
    pub description: String,
    pub transaction_total_cu: u64,
    pub marked_parse_and_power_prep_cu: u64,
    pub marked_wire_prefix_verify_cu: Option<u64>,
    pub marked_query_binding_cu: Option<u64>,
    pub marked_private_opening_verify_cu: Option<u64>,
    pub marked_fri_claim_prepare_cu: Option<u64>,
    pub marked_hash_and_combine_kernel_cu: u64,
    pub marked_claim_aggregation_cu: Option<u64>,
    pub marked_covector_derivation_cu: Option<u64>,
    pub marked_relation_fold_or_standalone_dot_cu: Option<u64>,
    pub transaction_total_minus_marked_deltas_cu: i64,
    pub transaction_total_repeats: Vec<u64>,
    pub marked_parse_and_power_prep_repeats: Vec<u64>,
    pub marked_wire_prefix_verify_repeats: Vec<u64>,
    pub marked_query_binding_repeats: Vec<u64>,
    pub marked_private_opening_verify_repeats: Vec<u64>,
    pub marked_fri_claim_prepare_repeats: Vec<u64>,
    pub marked_hash_and_combine_kernel_repeats: Vec<u64>,
    pub marked_claim_aggregation_repeats: Vec<u64>,
    pub marked_covector_derivation_repeats: Vec<u64>,
    pub marked_relation_fold_or_standalone_dot_repeats: Vec<u64>,
    pub sbf_heap_high_water_bytes: Option<usize>,
    pub sbf_heap_high_water_repeats: Vec<usize>,
}

#[derive(Debug, Serialize)]
pub struct V5Layer0CuProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub scope: String,
    pub full_v5_measured: bool,
    pub authority_note: String,
    pub measurement_method: String,
    pub runtime_input_account: String,
    pub runtime_input_account_bytes: usize,
    pub runtime_input_sha256: String,
    pub query_count: usize,
    pub production_c1_columns: usize,
    pub candidate_c1_columns: usize,
    pub shared_c2_columns: usize,
    pub production_c1_record_bytes: usize,
    pub candidate_c1_record_bytes: usize,
    pub shared_c2_record_bytes: usize,
    pub modes: Vec<ModeMeasurement>,
    pub marked_generic_nonfused_width_saving_cu: i64,
    pub marked_generic_fused_width_saving_cu: i64,
    pub marked_generic26_fusion_saving_cu: i64,
    pub marked_generic16_fusion_saving_cu: i64,
    pub clean_forecast_fused_width_saving_cu: i64,
    pub clean_forecast_width16_fusion_saving_cu: i64,
    pub marked_generic_nonfused_width_saving_mode_selection_asymmetry_cu: i64,
    pub marked_generic26_fusion_saving_mode_selection_asymmetry_cu: i64,
    pub production26_uses_current_fused_three_product_helper: bool,
    pub production26_to_generic16_fused_is_old_v4_to_v5_comparison: bool,
    pub comparison_caveat: String,
    pub marked_generic26_nonfused_to_generic16_fused_saving_cu: i64,
    pub marked_production26_to_generic26_fused_delta_cu: i64,
    pub marked_production26_to_generic16_fused_delta_cu: i64,
    pub marked_production26_to_generic16_fused_parse_and_power_saving_cu: i64,
    pub marked_production26_to_generic16_fused_parse_plus_kernel_saving_cu: i64,
    pub transaction_production26_to_generic16_fused_delta_cu: i64,
    pub component_b_lane_count: usize,
    pub component_b_existing_claims_per_lane: usize,
    pub component_b_candidate_claims_per_lane: usize,
    pub component_b_dense_rows: usize,
    pub component_b_nonzero_state_weights: usize,
    pub component_b_zero_pad_weights: usize,
    pub component_b_shared_existing_pcs_pass: bool,
    pub component_b_functional_batch_scales: String,
    pub component_b_functional_batch_sz_degree: u8,
    pub component_b_soundness_ledger_update_required: bool,
    pub component_b_default_heap_observation: String,
    pub marked_component_b_fourth_claim_delta_cu: i64,
    pub marked_component_b_covector_derivation_delta_cu: i64,
    pub marked_component_b_shared_fold_delta_cu: i64,
    pub marked_component_b_total_delta_cu: i64,
    pub transaction_component_b_total_delta_cu: i64,
    pub rejected_standalone_dot_marked_delta_cu: i64,
    pub rejected_standalone_total_delta_cu: i64,
    pub compact_component_b_block_selectors: [u8; 10],
    pub compact_component_b_initial_state_row: usize,
    pub compact_component_b_dependent_pivot_row: usize,
    pub compact_component_b_degree: usize,
    pub compact_component_b_zero_tail_weights: usize,
    pub compact_component_b_state_bytes: usize,
    pub compact_component_b_dynamic_heap_bytes: usize,
    pub compact_component_b_dense_payload_avoided_bytes: usize,
    pub marked_compact_component_b_fourth_claim_delta_cu: i64,
    pub marked_compact_component_b_derivation_delta_cu: i64,
    pub marked_compact_component_b_fold_delta_cu: i64,
    pub marked_compact_component_b_total_delta_cu: i64,
    pub transaction_compact_component_b_total_delta_cu: i64,
    pub provisional_forecast_envelope_cu: i64,
    pub compact_component_b_fits_provisional_forecast_envelope: bool,
    pub provisional_forecast_envelope_after_compact_component_b_cu: i64,
    pub component_b_binding_caveat: String,
    pub composite_uses_atomic_v3_inactive_relation: bool,
    pub composite_transaction_total_cu: u64,
    pub composite_marked_parse_and_allocation_cu: u64,
    pub composite_marked_wire_prefix_verify_cu: u64,
    pub composite_marked_query_binding_cu: u64,
    pub composite_marked_private_opening_verify_cu: u64,
    pub composite_marked_fri_claim_prepare_cu: u64,
    pub composite_marked_full_fri_cu: u64,
    pub composite_marked_claim_aggregation_cu: u64,
    pub composite_marked_compact_setup_cu: u64,
    pub composite_marked_relation_folds_and_dot_cu: u64,
    pub composite_marked_total_cu: u64,
    pub isolated_marked_total_cu: u64,
    pub composite_marked_overhead_vs_isolated_cu: i64,
    pub isolated_transaction_total_cu: u64,
    pub composite_transaction_saving_vs_two_isolated_cu: i64,
    pub default_sbf_heap_bytes: usize,
    pub composite_heap_high_water_bytes: usize,
    pub composite_default_heap_headroom_bytes: usize,
    pub composite_default_heap_viable_three_of_three: bool,
    pub historical_tag65_projection_made: bool,
    pub production_control_sbf_bytes: usize,
    pub production_control_sbf_sha256: String,
    pub production_control_rebuild_byte_identical: bool,
    pub probe_sbf_bytes: usize,
    pub probe_sbf_sha256: String,
    pub unmeasured_obligations: Vec<String>,
    pub conclusion: String,
}

pub struct V5Layer0CuProbeOutcome {
    pub path: PathBuf,
    pub production_kernel_cu: u64,
    pub candidate_kernel_cu: u64,
    pub production_to_candidate_delta_cu: i64,
    pub generic_fused_width_saving_cu: i64,
    pub generic16_fusion_saving_cu: i64,
}

#[derive(Debug, Serialize)]
struct V5FullCuPhaseMarker {
    label: String,
    remaining: u64,
    delta_from_previous: Option<i64>,
}

struct V5FullCuArtifactMetadata {
    query_selector: u8,
    honest_least_good_selector: u8,
    batch_nonce: u64,
    selected_branch_good: bool,
    test_only_nonleast_branch_override: bool,
    query_indices: [u32; V5_CU_PROBE_QUERY_COUNT],
    good_gate_evaluations: [V5HostGoodGateEvaluation; 3],
    opening_index_counts: [usize; 5],
    opening_frontier_nodes: [usize; 5],
    opening_section_bytes: [usize; 5],
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct V5ValidatorProvenance {
    executable_path: String,
    executable_sha256: String,
    version: String,
    version_manifest_path: String,
    version_manifest_sha256: String,
    version_manifest_commit: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct V5ExecutableProvenance {
    executable_path: String,
    executable_sha256: String,
    version: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct V5RustSourceFileProvenance {
    path: String,
    bytes: usize,
    sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct V5RustSourceProvenance {
    git_head: String,
    aggregate_sha256: String,
    files: Vec<V5RustSourceFileProvenance>,
}

#[derive(Debug, Serialize)]
struct V5FullCuTransactionSummary {
    generated_at_utc: String,
    command: String,
    scope: String,
    security_scope: String,
    transaction_repeats: usize,
    transaction_total_cu: u64,
    transaction_cu_limit: u64,
    transaction_headroom_cu: u64,
    transaction_total_repeats: Vec<u64>,
    nullifier_marker_fixture_mode: &'static str,
    nullifier_marker_simulation_helper: &'static str,
    nullifier_marker_preloaded: bool,
    system_program_cpi_required: bool,
    system_program_cpi_observed_all_repeats: bool,
    system_program_cpi_log_evidence: Vec<Vec<String>>,
    phase_markers: Vec<V5FullCuPhaseMarker>,
    query_selector: u8,
    honest_least_good_selector: u8,
    batch_nonce: u64,
    selected_branch_good: bool,
    test_only_nonleast_branch_override: bool,
    all_candidate_good: [bool; 3],
    proof_body_bytes: usize,
    sealed_proof_account_bytes: usize,
    sealed_proof_account_sha256: String,
    proof_body_sha256: String,
    query_indices: [u32; V5_CU_PROBE_QUERY_COUNT],
    opening_index_counts: [usize; 5],
    opening_frontier_nodes: [usize; 5],
    opening_section_bytes: [usize; 5],
    probe_sbf_bytes: usize,
    probe_sbf_sha256: String,
    sbf_build_command: String,
    sbf_build_tool: V5ExecutableProvenance,
    rust_sources: V5RustSourceProvenance,
    validator: V5ValidatorProvenance,
    state_transition_wrapper: String,
    component_a: String,
    component_b: String,
    component_c: String,
    accepted_three_of_three: bool,
    deterministic_cu_three_of_three: bool,
    conclusion: String,
}

fn workspace_root() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .map(Path::to_path_buf)
        .ok_or_else(|| anyhow!("no workspace root"))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn resolve_executable_on_path(name: &str) -> Result<PathBuf> {
    let path = env::var_os("PATH").context("PATH is not set")?;
    for directory in env::split_paths(&path) {
        let candidate = directory.join(name);
        if candidate.is_file() {
            return fs::canonicalize(&candidate)
                .with_context(|| format!("canonicalize {}", candidate.display()));
        }
    }
    bail!("{name} not found on PATH")
}

fn executable_provenance(name: &str, version_args: &[&str]) -> Result<V5ExecutableProvenance> {
    let executable = resolve_executable_on_path(name)?;
    let executable_bytes = fs::read(&executable)
        .with_context(|| format!("read executable {}", executable.display()))?;
    let version_output = Command::new(&executable)
        .args(version_args)
        .output()
        .with_context(|| format!("run {} {}", executable.display(), version_args.join(" ")))?;
    ensure!(
        version_output.status.success(),
        "{} {} failed with {}",
        executable.display(),
        version_args.join(" "),
        version_output.status
    );
    let mut version_bytes = version_output.stdout;
    version_bytes.extend_from_slice(&version_output.stderr);
    let version = String::from_utf8(version_bytes)
        .context("tool version output was not UTF-8")?
        .trim()
        .to_string();
    ensure!(!version.is_empty(), "{name} version output was empty");
    Ok(V5ExecutableProvenance {
        executable_path: executable.display().to_string(),
        executable_sha256: hex(&Sha256::digest(&executable_bytes)),
        version,
    })
}

fn collect_rust_source_paths(directory: &Path, paths: &mut Vec<PathBuf>) -> Result<()> {
    let mut entries = fs::read_dir(directory)
        .with_context(|| format!("read source directory {}", directory.display()))?
        .collect::<std::io::Result<Vec<_>>>()?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        let file_type = entry
            .file_type()
            .with_context(|| format!("read file type for {}", path.display()))?;
        if file_type.is_dir() {
            collect_rust_source_paths(&path, paths)?;
        } else if file_type.is_file()
            && matches!(
                path.extension().and_then(|extension| extension.to_str()),
                Some("rs" | "toml" | "lock")
            )
        {
            paths.push(path);
        }
    }
    Ok(())
}

fn rust_source_provenance(root: &Path) -> Result<V5RustSourceProvenance> {
    let mut paths = vec![root.join("Cargo.toml"), root.join("Cargo.lock")];
    for directory in [
        "crates/aspis-core",
        "crates/aspis-statement",
        "crates/aspis-prover",
        "programs/aspis-verifier",
        "xtask",
    ] {
        collect_rust_source_paths(&root.join(directory), &mut paths)?;
    }
    paths.sort();
    paths.dedup();

    let mut aggregate = Sha256::new();
    let mut files = Vec::with_capacity(paths.len());
    for path in paths {
        let relative = path
            .strip_prefix(root)
            .with_context(|| format!("source path escaped workspace: {}", path.display()))?;
        let relative = relative
            .to_str()
            .ok_or_else(|| anyhow!("non-UTF-8 source path: {}", relative.display()))?;
        let bytes = fs::read(&path)
            .with_context(|| format!("read Rust source input {}", path.display()))?;
        let digest = hex(&Sha256::digest(&bytes));
        aggregate.update((relative.len() as u64).to_le_bytes());
        aggregate.update(relative.as_bytes());
        aggregate.update((bytes.len() as u64).to_le_bytes());
        aggregate.update(&bytes);
        files.push(V5RustSourceFileProvenance {
            path: relative.to_string(),
            bytes: bytes.len(),
            sha256: digest,
        });
    }

    let head_output = Command::new("git")
        .arg("rev-parse")
        .arg("HEAD")
        .current_dir(root)
        .output()
        .context("run git rev-parse HEAD for CU provenance")?;
    ensure!(
        head_output.status.success(),
        "git rev-parse HEAD failed with {}",
        head_output.status
    );
    let git_head = String::from_utf8(head_output.stdout)
        .context("git HEAD was not UTF-8")?
        .trim()
        .to_string();
    ensure!(!git_head.is_empty(), "git HEAD was empty");

    Ok(V5RustSourceProvenance {
        git_head,
        aggregate_sha256: hex(&aggregate.finalize()),
        files,
    })
}

fn validator_provenance() -> Result<V5ValidatorProvenance> {
    let executable = resolve_executable_on_path("solana-test-validator")?;
    let executable_bytes = fs::read(&executable)
        .with_context(|| format!("read validator executable {}", executable.display()))?;
    let version_output = Command::new(&executable)
        .arg("--version")
        .output()
        .with_context(|| format!("run {} --version", executable.display()))?;
    ensure!(
        version_output.status.success(),
        "{} --version failed with {}",
        executable.display(),
        version_output.status
    );
    let version = String::from_utf8(version_output.stdout)
        .context("validator --version output was not UTF-8")?
        .trim()
        .to_string();
    ensure!(!version.is_empty(), "validator --version output was empty");

    let release_root = executable.parent().and_then(Path::parent).ok_or_else(|| {
        anyhow!(
            "validator path has no release root: {}",
            executable.display()
        )
    })?;
    let version_manifest = release_root.join("version.yml");
    let version_manifest_bytes = fs::read(&version_manifest)
        .with_context(|| format!("read validator manifest {}", version_manifest.display()))?;
    let version_manifest_text = std::str::from_utf8(&version_manifest_bytes)
        .context("validator version.yml was not UTF-8")?;
    let version_manifest_commit = version_manifest_text
        .lines()
        .find_map(|line| line.strip_prefix("commit:"))
        .map(str::trim)
        .filter(|commit| !commit.is_empty())
        .ok_or_else(|| anyhow!("validator version.yml omitted commit"))?
        .to_string();

    Ok(V5ValidatorProvenance {
        executable_path: executable.display().to_string(),
        executable_sha256: hex(&Sha256::digest(&executable_bytes)),
        version,
        version_manifest_path: version_manifest.display().to_string(),
        version_manifest_sha256: hex(&Sha256::digest(&version_manifest_bytes)),
        version_manifest_commit,
    })
}

fn build_sbf(root: &Path, features: &str, pinned_name: &str) -> Result<PathBuf> {
    if let Some(prebuilt) = env::var_os("V5_CU_PREBUILT_SBF") {
        let prebuilt = PathBuf::from(prebuilt);
        ensure!(
            prebuilt.is_absolute(),
            "V5_CU_PREBUILT_SBF must be an absolute path"
        );
        let metadata = fs::symlink_metadata(&prebuilt)
            .with_context(|| format!("inspect prebuilt SBF {}", prebuilt.display()))?;
        ensure!(
            metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
            "V5_CU_PREBUILT_SBF must be a regular non-symlink file"
        );
        let bytes = fs::read(&prebuilt)
            .with_context(|| format!("read prebuilt SBF {}", prebuilt.display()))?;
        let actual_sha256 = hex(&Sha256::digest(&bytes));
        let expected_sha256 = env::var("V5_CU_PREBUILT_SBF_SHA256")
            .context("V5_CU_PREBUILT_SBF_SHA256 is required with V5_CU_PREBUILT_SBF")?;
        ensure!(
            expected_sha256 == actual_sha256,
            "prebuilt SBF SHA-256 mismatch"
        );
        return Ok(prebuilt);
    }
    ensure!(
        env::var_os("V5_CU_PREBUILT_SBF_SHA256").is_none(),
        "V5_CU_PREBUILT_SBF_SHA256 requires V5_CU_PREBUILT_SBF"
    );
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .arg("--manifest-path")
        .arg(root.join("programs/aspis-verifier/Cargo.toml"))
        .arg("--no-default-features")
        .arg("--features")
        .arg(features)
        .status()
        .context("cargo-build-sbf not found on PATH — install the Solana toolchain")?;
    if !status.success() {
        bail!("cargo-build-sbf failed for feature set {features}");
    }
    let built = root.join("target/deploy/aspis_verifier.so");
    ensure!(built.exists(), "missing {}", built.display());
    let pinned = root.join(format!("target/deploy/{pinned_name}.so"));
    fs::copy(&built, &pinned)
        .with_context(|| format!("pin SBF probe artifact {}", pinned.display()))?;
    Ok(pinned)
}

fn next_m31(state: &mut u64) -> M31 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    M31((*state % u64::from(P)) as u32)
}

fn next_qm31(state: &mut u64) -> QM31 {
    QM31 {
        c0: CM31::new(next_m31(state), next_m31(state)),
        c1: CM31::new(next_m31(state), next_m31(state)),
    }
}

/// Host-side input construction. Candidate C1 records are the first sixteen
/// columns of the corresponding production record and reuse its salt; every
/// mode reads the same C2 record for a given query.
fn deterministic_salts(seed: u64, count: usize) -> Vec<[u8; 32]> {
    let mut state = seed;
    (0..count)
        .map(|_| {
            core::array::from_fn(|_| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                (state >> 27) as u8
            })
        })
        .collect()
}

/// Deterministic values only for the local CU/test fixture. Production must
/// supply fresh, independent public FS salts; this fixture does not model that
/// operational premise.
fn deterministic_public_fs_salts_for_cu_test_fixture() -> V5PublicFsSalts {
    V5PublicFsSalts {
        c1: [0xa1; V5_PUBLIC_FS_SALT_BYTES],
        c2: [0xa2; V5_PUBLIC_FS_SALT_BYTES],
        later: [
            [0xb1; V5_PUBLIC_FS_SALT_BYTES],
            [0xb2; V5_PUBLIC_FS_SALT_BYTES],
            [0xb3; V5_PUBLIC_FS_SALT_BYTES],
        ],
    }
}

struct V5FixtureRng(u64);

impl Qm31WordSource for V5FixtureRng {
    fn next_word(&mut self) -> u32 {
        let mut value = self.0;
        value ^= value << 13;
        value ^= value >> 7;
        value ^= value << 17;
        self.0 = value;
        (value >> 21) as u32 % P
    }
}

fn fixture_q(seed: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
        c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
    }
}

fn fixture_digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

const RUNTIME_WITNESS_M31_RETRY_LIMIT: usize = 16;

/// Draw one runtime witness digest directly from the operating system. Each
/// limb uses the same canonical bounded M31 rejection rule as the proof-mask
/// samplers, and entropy/rejection failure has no deterministic fallback.
fn fresh_runtime_witness_digest() -> Result<Digest> {
    let mut digest = [M31::ZERO; 8];
    for limb in &mut digest {
        let mut accepted = None;
        for _ in 0..RUNTIME_WITNESS_M31_RETRY_LIMIT {
            let mut bytes = [0u8; core::mem::size_of::<u32>()];
            getrandom::fill(&mut bytes)
                .map_err(|_| anyhow!("runtime witness entropy unavailable"))?;
            let candidate = u32::from_le_bytes(bytes) & 0x7fff_ffff;
            if candidate < aspis_core::field::P {
                accepted = Some(M31(candidate));
                break;
            }
        }
        *limb = accepted.ok_or_else(|| anyhow!("runtime witness sampling aborted"))?;
    }
    Ok(digest)
}

fn fresh_v5_statement_and_witness_for_runtime(
    pool: [u8; 32],
    sequence: u64,
    deployment_domain: [u8; 32],
) -> Result<(AtomicPaymentStatementV4, SpendWitness)> {
    let nullifier_key = fresh_runtime_witness_digest()?;
    let input_salt = fresh_runtime_witness_digest()?;
    let output_salt = fresh_runtime_witness_digest()?;
    let output_owner_key = fresh_runtime_witness_digest()?;
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let merkle_path = MerklePath {
        siblings: (0..20)
            .map(|_| fresh_runtime_witness_digest())
            .collect::<Result<Vec<_>>>()?,
        index: 0x5_a5a5,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let statement = AtomicPaymentStatementV4 {
        pool,
        sequence,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
        deployment_domain,
    };
    Ok((statement, witness))
}

fn real_v5_statement_and_witness_for_runtime(
    pool: [u8; 32],
    sequence: u64,
    deployment_domain: [u8; 32],
) -> (AtomicPaymentStatementV4, SpendWitness) {
    let nullifier_key = fixture_digest(101);
    let input_salt = fixture_digest(301);
    let output_salt = fixture_digest(501);
    let output_owner_key = fixture_digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let merkle_path = MerklePath {
        siblings: (0..20)
            .map(|level| fixture_digest(1_000 + 31 * level))
            .collect(),
        index: 0x5_a5a5,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let statement = AtomicPaymentStatementV4 {
        pool,
        sequence,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
        deployment_domain,
    };
    (statement, witness)
}

fn real_v5_statement_and_witness() -> (AtomicPaymentStatementV4, SpendWitness) {
    real_v5_statement_and_witness_for_runtime([0x5a; 32], 73, [0x5d; 32])
}

fn real_v5_hcopy_padding() -> [QM31; V5_TRACE_ROWS] {
    let mut active = [false; V5_TRACE_ROWS];
    for &row in atomic_state_only_copy_active_rows_v3() {
        active[usize::from(row)] = true;
    }
    let pivot = (0..V5_TRACE_ROWS).find(|row| !active[*row]).unwrap();
    let mut padding = [QM31::ZERO; V5_TRACE_ROWS];
    let mut sum = QM31::ZERO;
    for row in 0..V5_TRACE_ROWS {
        if !active[row] && row != pivot {
            padding[row] = fixture_q(10_000 + row as u32);
            sum = sum.add(padding[row]);
        }
    }
    padding[pivot] = sum.neg();
    padding
}

fn build_real_v5_fixture_with_runtime_binding_and_pivot_pad(
    pool: [u8; 32],
    sequence: u64,
    deployment_domain: [u8; 32],
    component_b_pivot_pad: QM31,
) -> Result<(AtomicPaymentStatementV4, V5RealHostArtifact)> {
    let (statement, witness) =
        real_v5_statement_and_witness_for_runtime(pool, sequence, deployment_domain);
    let mut a_sources: [V5FixtureRng; V5_C1_LANES] =
        core::array::from_fn(|lane| V5FixtureRng(0xa531_0000_0000_0001 ^ lane as u64));
    let component_a = sample_atomic_m31_lane_masks(&mut a_sources)
        .map_err(|error| anyhow!("sample real v5 Component A: {error:?}"))?;
    let hcopy_padding = real_v5_hcopy_padding();
    let sumcheck_mask = V5SumcheckMask::sample(&mut V5FixtureRng(0xb500_0000_0000_0001))
        .map_err(|error| anyhow!("sample real v5 Component B: {error:?}"))?;
    let component_b_pads = core::array::from_fn(|index| fixture_q(20_000 + index as u32));
    let component_c = aspis_prover::v5_mask::component_c::V5ComponentCLane::sample(
        &mut V5FixtureRng(0xc500_0000_0000_0001),
    )
    .map_err(|error| anyhow!("sample direct real v5 Component C: {error:?}"))?;
    let c1_salts = deterministic_salts(0xc1, 1 << 17);
    let c2_salts = deterministic_salts(0xc2, 1 << 17);
    let later_salts = [
        deterministic_salts(0xd1, 1 << 15),
        deterministic_salts(0xd2, 1 << 13),
        deterministic_salts(0xd3, 1 << 11),
    ];
    let artifact = build_v5_real_host_artifact(V5RealHostInputs {
        statement: &statement,
        witness: &witness,
        component_a: &component_a,
        hcopy_padding: &hcopy_padding,
        sumcheck_mask: &sumcheck_mask,
        component_b_pads: &component_b_pads,
        component_b_pivot_pad,
        component_c: &component_c,
        salts: V5HostPcsSalts {
            c1: &c1_salts,
            c2: &c2_salts,
            later: [&later_salts[0], &later_salts[1], &later_salts[2]],
        },
        public_fs_salts: deterministic_public_fs_salts_for_cu_test_fixture(),
        hash: aspis_prover::HOST_HASH,
        pow_bits: V5HostPowBits::DEPLOYED,
    })
    .map_err(|error| anyhow!("build real-witness v5 host artifact: {error:?}"))?;
    Ok((statement, artifact))
}

fn build_real_v5_fixture_with_pivot_pad(
    component_b_pivot_pad: QM31,
) -> Result<(AtomicPaymentStatementV4, V5RealHostArtifact)> {
    build_real_v5_fixture_with_runtime_binding_and_pivot_pad(
        [0x5a; 32],
        73,
        [0x5d; 32],
        component_b_pivot_pad,
    )
}

pub(crate) fn build_real_v5_fixture() -> Result<(AtomicPaymentStatementV4, V5RealHostArtifact)> {
    // Deterministic CU/KAT fixture only. Production must supply a fresh,
    // independent pre-C2-commitment pad through the explicit host input.
    build_real_v5_fixture_with_pivot_pad(fixture_q(29_999))
}

fn honest_least_good_selector(artifact: &V5RealHostArtifact) -> Result<u8> {
    artifact
        .good_gate_evaluations
        .iter()
        .position(|evaluation| evaluation.is_good())
        .map(|index| index as u8)
        .ok_or_else(|| anyhow!("production host artifact has no Good branch"))
}

/// Test-only reconstruction of one already-Good selector branch.
///
/// The production host remains authoritative for the least-Good selector and
/// is never passed an override. Selectors one and two deliberately model a
/// malicious nonleast prover for selected-branch CU coverage. They are not
/// produced by the honest host. The complete query-dependent PCS suffix is
/// rebuilt from the retained committed codewords, fold challenges, salts, and
/// Merkle trees; changing only the serialized selector is never accepted.
fn test_only_rebuild_selected_good_branch(
    artifact: &mut V5RealHostArtifact,
    selector: u8,
) -> Result<u8> {
    ensure!(selector < 3, "test-only v5 selector is out of range");
    let honest_least_good_selector = honest_least_good_selector(artifact)?;
    let selected = artifact.good_gate_evaluations[usize::from(selector)];
    ensure!(
        selected.is_good(),
        "test-only v5 selector {selector} is not GoodA && GoodB"
    );
    let queries = selected.queries;

    ensure!(
        artifact.layer_zero.c1.encoded.len() == V5_C1_LANES
            && artifact.layer_zero.c2.encoded.len() == V5_C2_LANES
            && artifact
                .layer_zero
                .c1
                .encoded
                .iter()
                .all(|word| word.len() == V5_CODEWORD_LEN)
            && artifact
                .layer_zero
                .c2
                .encoded
                .iter()
                .all(|word| word.len() == V5_CODEWORD_LEN),
        "test-only v5 layer-zero codeword shape drift"
    );
    let powers = qm31_power_table::<V5_TOTAL_LANES>(artifact.challenges.gamma);
    let mut combined_codeword = vec![QM31::ZERO; V5_CODEWORD_LEN];
    for (lane, word) in artifact.layer_zero.c1.encoded.iter().enumerate() {
        for (output, value) in combined_codeword.iter_mut().zip(word.iter().copied()) {
            *output = output.add(powers[lane].mul_m31(value));
        }
    }
    for (helper, word) in artifact.layer_zero.c2.encoded.iter().enumerate() {
        let power = powers[V5_C1_LANES + helper];
        for (output, value) in combined_codeword.iter_mut().zip(word.iter().copied()) {
            *output = output.add(power.mul(value));
        }
    }

    let later_salts = [
        deterministic_salts(0xd1, 1 << 15),
        deterministic_salts(0xd2, 1 << 13),
        deterministic_salts(0xd3, 1 << 11),
    ];
    let mut later_values: [Vec<u8>; V5_LATER_LAYERS] = core::array::from_fn(|_| Vec::new());
    let mut later_trees: [Option<StateOnlyPrivateMerkleTree>; V5_LATER_LAYERS] =
        core::array::from_fn(|_| None);
    for round in 0..V5_LATER_LAYERS {
        combined_codeword = fold_candidate_codeword_round_for_domain_log(
            &combined_codeword,
            artifact.alphas[round],
            round,
            V5_DOMAIN_LOG,
        )
        .map_err(|error| anyhow!("test-only v5 fold {round}: {error:?}"))?;
        let leaves = combined_layer_leaves(&combined_codeword);
        let mut values = Vec::with_capacity(leaves.len() * COMBINED_LAYER_LEAF_BYTES);
        for leaf in leaves {
            values.extend_from_slice(&leaf);
        }
        let tree = build_state_only_private_merkle_tree(
            aspis_prover::HOST_HASH,
            V5_PRIVATE_DEPTHS[2 + round],
            CIRCLE_LINE_TAGS[round],
            COMBINED_LAYER_LEAF_BYTES,
            &values,
            &later_salts[round],
        )
        .map_err(|error| anyhow!("test-only v5 later tree {round}: {error:?}"))?;
        ensure!(
            tree.root() == artifact.roots.later[round],
            "test-only v5 later root {round} changed while rebuilding a selector branch"
        );
        later_values[round] = values;
        later_trees[round] = Some(tree);
    }

    let c1_salts = deterministic_salts(0xc1, 1 << 17);
    let c2_salts = deterministic_salts(0xc2, 1 << 17);
    let opening_indices =
        derive_circle_line_query_indices_for_count(&queries, V5_LAYER_ZERO_LEAVES)
            .map_err(|error| anyhow!("test-only v5 opening indices: {error:?}"))?;
    let section_indices: [&[u32]; 5] = [
        &opening_indices.layer0,
        &opening_indices.layer0,
        &opening_indices.later[0],
        &opening_indices.later[1],
        &opening_indices.later[2],
    ];
    let section_values: [&[u8]; 5] = [
        &artifact.layer_zero.c1.packed_values,
        &artifact.layer_zero.c2.packed_values,
        &later_values[0],
        &later_values[1],
        &later_values[2],
    ];
    let section_salts: [&[[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES]]; 5] = [
        &c1_salts,
        &c2_salts,
        &later_salts[0],
        &later_salts[1],
        &later_salts[2],
    ];
    let section_trees: [&StateOnlyPrivateMerkleTree; 5] = [
        &artifact.layer_zero.c1.tree,
        &artifact.layer_zero.c2.tree,
        later_trees[0].as_ref().unwrap(),
        later_trees[1].as_ref().unwrap(),
        later_trees[2].as_ref().unwrap(),
    ];
    let mut opening_bytes = Vec::new();
    let mut section_bytes = [0usize; 5];
    let mut frontier_nodes = [0usize; 5];
    for section in 0..5 {
        let opening = serialize_state_only_private_opening(
            section_trees[section],
            section_values[section],
            section_salts[section],
            section_indices[section],
        )
        .map_err(|error| anyhow!("test-only v5 opening section {section}: {error:?}"))?;
        section_bytes[section] = opening.bytes.len();
        frontier_nodes[section] = opening.frontier_nodes;
        opening_bytes.extend_from_slice(&opening.bytes);
    }
    let openings = V5BuiltPcsOpenings {
        bytes: opening_bytes,
        indices: opening_indices.clone(),
        section_bytes,
        frontier_nodes,
    };
    let verified = verify_v5_pcs_openings(
        aspis_prover::HOST_HASH,
        &artifact.roots,
        &queries,
        &openings.bytes,
    )
    .map_err(|error| anyhow!("self-verify test-only v5 selector {selector}: {error}"))?;
    ensure!(
        verified.end == openings.bytes.len(),
        "test-only v5 selector opening suffix has trailing bytes"
    );

    artifact.query_selector = selector;
    artifact.queries = queries;
    artifact.opening_indices = opening_indices;
    artifact.openings = openings;
    Ok(honest_least_good_selector)
}

fn write_qm31(output: &mut [u8], offset: usize, value: QM31) {
    value.write_le_bytes(&mut output[offset..offset + QM31_BYTES]);
}

const _: () = assert!(V5_CU_PROBE_BATCH_NONCE_OFFSET == 11_080);
const _: () = assert!(V5_CU_PROBE_BATCH_NONCE_BYTES == 8);
const _: () = assert!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET == 11_088);
const _: () = assert!(V5_CU_PROBE_PREFIX_OFFSET == 11_112);

fn serialize_real_v5_runtime_account_data_with_metadata(
    statement: &AtomicPaymentStatementV4,
    artifact: &V5RealHostArtifact,
) -> Result<(Vec<u8>, V5FullCuArtifactMetadata)> {
    let honest_least_good_selector = honest_least_good_selector(artifact)?;
    let prefix = artifact.encode_real_prefix();
    let context = artifact
        .encode_atomic_terminal_context(statement)
        .map_err(|error| anyhow!("encode real v5 atomic terminal context: {error:?}"))?;

    let mut data = vec![0u8; V5_CU_PROBE_ACCOUNT_BYTES];
    data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
    write_qm31(
        &mut data,
        V5_CU_PROBE_GAMMA_OFFSET,
        artifact.challenges.gamma,
    );
    for (index, scale) in [
        QM31::ONE,
        artifact.challenges.kappa,
        artifact.challenges.kappa.square(),
    ]
    .into_iter()
    .enumerate()
    {
        write_qm31(
            &mut data,
            V5_CU_PROBE_RELATION_SCALES_OFFSET + index * QM31_BYTES,
            scale,
        );
    }
    for point in 0..3 {
        for coordinate in 0..10 {
            write_qm31(
                &mut data,
                V5_CU_PROBE_RELATION_POINTS_OFFSET + (point * 10 + coordinate) * QM31_BYTES,
                artifact.relation_claims.points[point][coordinate],
            );
        }
    }
    data[V5_CU_PROBE_RELATION_CLAIMS_OFFSET..V5_CU_PROBE_RELATION_ALPHAS_OFFSET]
        .copy_from_slice(&artifact.relation_claims.encode_point_major());
    for (round, alpha) in artifact.alphas.iter().copied().enumerate() {
        write_qm31(
            &mut data,
            V5_CU_PROBE_RELATION_ALPHAS_OFFSET + round * QM31_BYTES,
            alpha,
        );
        let nonce_start = V5_CU_PROBE_RELATION_FINAL_OFFSET + round * 8;
        data[nonce_start..nonce_start + 8]
            .copy_from_slice(&artifact.fold_nonces[round].to_le_bytes());
    }
    data[V5_CU_PROBE_BATCH_NONCE_OFFSET..V5_CU_PROBE_BATCH_NONCE_OFFSET + 8]
        .copy_from_slice(&artifact.batch_nonce.to_le_bytes());
    debug_assert!(
        data[V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET..V5_CU_PROBE_PREFIX_OFFSET]
            .iter()
            .all(|byte| *byte == 0)
    );
    data[V5_CU_PROBE_PREFIX_OFFSET..V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET]
        .copy_from_slice(&prefix);
    data[V5_CU_PROBE_ATOMIC_TERMINAL_CONTEXT_OFFSET..V5_CU_PROBE_PRIVATE_ROOTS_OFFSET]
        .copy_from_slice(&context);
    let roots = [
        artifact.roots.c1,
        artifact.roots.c2,
        artifact.roots.later[0],
        artifact.roots.later[1],
        artifact.roots.later[2],
    ];
    for (index, root) in roots.iter().enumerate() {
        let start = V5_CU_PROBE_PRIVATE_ROOTS_OFFSET + index * 32;
        data[start..start + 32].copy_from_slice(root);
    }
    for (index, coefficient) in artifact
        .relation
        .final_coefficients
        .iter()
        .copied()
        .enumerate()
    {
        write_qm31(
            &mut data,
            V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET + index * QM31_BYTES,
            coefficient,
        );
    }
    data[V5_CU_PROBE_RELATION_STRESS_OFFSET..V5_CU_PROBE_FINAL_NONCE_OFFSET]
        .copy_from_slice(&artifact.encode_relation_tail());
    data[V5_CU_PROBE_FINAL_NONCE_OFFSET..V5_CU_PROBE_QUERY_SELECTOR_OFFSET]
        .copy_from_slice(&artifact.final_nonce.to_le_bytes());
    data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET] = artifact.query_selector;

    let verified = verify_v5_pcs_openings(
        aspis_prover::HOST_HASH,
        &artifact.roots,
        &artifact.queries,
        &artifact.openings.bytes,
    )
    .map_err(|error| anyhow!("self-verify real v5 q18 openings: {error}"))?;
    install_authenticated_layer0_records(&mut data, verified.c1.records, verified.c2.records);
    data.extend_from_slice(&artifact.openings.bytes);
    ensure!(artifact.queries.len() == V5_CU_PROBE_QUERY_COUNT);
    let replayed_queries = v5_complete_queries(aspis_prover::HOST_HASH, &data)
        .map_err(|error| anyhow!("host replay real v5 q18 queries: {error:?}"))?;
    ensure!(
        replayed_queries == artifact.queries,
        "real v5 prover/verifier q18 query drift"
    );
    probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &data)
        .map_err(|error| anyhow!("host verify complete real v5 CU artifact: {error:?}"))?;
    let metadata = V5FullCuArtifactMetadata {
        query_selector: artifact.query_selector,
        honest_least_good_selector,
        batch_nonce: artifact.batch_nonce,
        selected_branch_good: artifact.good_gate_evaluations[usize::from(artifact.query_selector)]
            .is_good(),
        test_only_nonleast_branch_override: artifact.query_selector != honest_least_good_selector,
        query_indices: artifact.queries,
        good_gate_evaluations: artifact.good_gate_evaluations,
        opening_index_counts: [
            artifact.opening_indices.layer0.len(),
            artifact.opening_indices.layer0.len(),
            artifact.opening_indices.later[0].len(),
            artifact.opening_indices.later[1].len(),
            artifact.opening_indices.later[2].len(),
        ],
        opening_frontier_nodes: artifact.openings.frontier_nodes,
        opening_section_bytes: artifact.openings.section_bytes,
    };
    Ok((data, metadata))
}

/// Serialize one already-built honest v5 host artifact into the exact tag-67
/// proof body. This seam performs no sampling and has no selector override:
/// callers must supply the statement used to construct the artifact, and the
/// artifact must retain the host's least-Good selector.
pub(crate) fn serialize_honest_v5_runtime_proof_body(
    statement: &AtomicPaymentStatementV4,
    artifact: &V5RealHostArtifact,
) -> Result<(Vec<u8>, u8)> {
    let honest_selector = honest_least_good_selector(artifact)?;
    ensure!(
        artifact.query_selector == honest_selector,
        "v5 host artifact does not retain its honest least-Good selector"
    );
    let (proof_body, metadata) =
        serialize_real_v5_runtime_account_data_with_metadata(statement, artifact)?;
    ensure!(
        metadata.query_selector == honest_selector
            && metadata.honest_least_good_selector == honest_selector
            && metadata.selected_branch_good
            && !metadata.test_only_nonleast_branch_override,
        "honest v5 serialization metadata drift"
    );
    Ok((proof_body, honest_selector))
}

/// Build a runtime-bound proof for the parameterized demo witness through the
/// cap-17 production attempt manager, then serialize its honest least-Good
/// artifact. The manager owns every private mask/salt and staged public-FS
/// salt draw; this seam has no deterministic production fallback.
pub(crate) fn build_v5_runtime_bound_production_demo_proof_body(
    pool: [u8; 32],
    sequence: u64,
    deployment_domain: [u8; 32],
) -> Result<(AtomicPaymentStatementV4, Vec<u8>, u8, u8)> {
    let (statement, witness) =
        fresh_v5_statement_and_witness_for_runtime(pool, sequence, deployment_domain)?;
    let output = build_v5_production_host_artifact_cap17(V5ProductionAttemptInputs {
        statement: &statement,
        witness: &witness,
    })
    .map_err(|error| anyhow!("build cap-17 production v5 demo artifact: {error:?}"))?;
    let successful_attempt_index = output.successful_attempt_index;
    let (proof_body, honest_selector) =
        serialize_honest_v5_runtime_proof_body(&statement, &output.artifact)?;
    Ok((
        statement,
        proof_body,
        honest_selector,
        successful_attempt_index,
    ))
}

fn serialize_real_v5_runtime_account_data_for_test_selector(
    statement: &AtomicPaymentStatementV4,
    artifact: &mut V5RealHostArtifact,
    test_selector: Option<u8>,
) -> Result<(Vec<u8>, V5FullCuArtifactMetadata)> {
    let honest_selector = honest_least_good_selector(artifact)?;
    if let Some(selector) = test_selector {
        if selector != artifact.query_selector {
            let preserved = test_only_rebuild_selected_good_branch(artifact, selector)?;
            ensure!(
                preserved == honest_selector,
                "test-only selector reconstruction changed honest least-Good metadata"
            );
        } else {
            ensure!(
                artifact.good_gate_evaluations[usize::from(selector)].is_good(),
                "selected v5 test fixture branch is not GoodA && GoodB"
            );
        }
    } else {
        ensure!(
            artifact.query_selector == honest_selector,
            "honest v5 test fixture lost its least-Good selector"
        );
    }
    let (data, metadata) =
        serialize_real_v5_runtime_account_data_with_metadata(statement, artifact)?;
    ensure!(
        metadata.honest_least_good_selector == honest_selector,
        "v5 test serialization changed honest least-Good metadata"
    );
    Ok((data, metadata))
}

fn build_real_v5_runtime_account_data_with_pivot_pad_and_test_selector(
    component_b_pivot_pad: QM31,
    test_selector: Option<u8>,
) -> Result<(AtomicPaymentStatementV4, Vec<u8>, V5FullCuArtifactMetadata)> {
    let (statement, mut artifact) = build_real_v5_fixture_with_pivot_pad(component_b_pivot_pad)?;
    let (data, metadata) = serialize_real_v5_runtime_account_data_for_test_selector(
        &statement,
        &mut artifact,
        test_selector,
    )?;
    Ok((statement, data, metadata))
}

fn build_real_v5_runtime_account_data_with_pivot_pad(
    component_b_pivot_pad: QM31,
) -> Result<(AtomicPaymentStatementV4, Vec<u8>, V5FullCuArtifactMetadata)> {
    build_real_v5_runtime_account_data_with_pivot_pad_and_test_selector(component_b_pivot_pad, None)
}

fn build_real_v5_runtime_account_data(
) -> Result<(AtomicPaymentStatementV4, Vec<u8>, V5FullCuArtifactMetadata)> {
    build_real_v5_runtime_account_data_with_pivot_pad(fixture_q(29_999))
}

fn finalized_proof_account_data(proof: &[u8]) -> Result<Vec<u8>> {
    let proof_len = u32::try_from(proof.len()).context("v5 CU proof exceeds u32 wire length")?;
    let mut account = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
    account[..4].copy_from_slice(b"ASPU");
    account[4..8].copy_from_slice(&proof_len.to_le_bytes());
    // Bytes 8..40 are the upload authority. Canonical all-zero bytes mean the
    // proof account is sealed, exactly as required by the production wrapper.
    account[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(proof);
    Ok(account)
}

/// Build the exact fixed 169-byte tag-67 atomic public-input wire. The proof
/// body remains account-backed and is deliberately not duplicated here.
pub(crate) fn build_v5_tag67_transaction_wire(
    statement: &AtomicPaymentStatementV4,
) -> [u8; V5_FULL_CU_TRANSACTION_WIRE_BYTES] {
    use aspis_statement::encode_digest_canonical;

    let mut wire = [0u8; V5_FULL_CU_TRANSACTION_WIRE_BYTES];
    wire[0] = V5_FULL_CU_TRANSACTION_TAG;
    let mut offset = 1usize;
    {
        let mut append = |bytes: &[u8]| {
            let end = offset + bytes.len();
            wire[offset..end].copy_from_slice(bytes);
            offset = end;
        };
        append(&encode_digest_canonical(&statement.spend.anchor));
        append(&encode_digest_canonical(&statement.spend.nullifier));
        append(&encode_digest_canonical(&statement.spend.output_commitment));
        append(&encode_digest_canonical(&statement.output_anchor));
        append(&statement.spend.asset_id.0.to_le_bytes());
        append(&statement.spend.fee.to_le_bytes());
        append(&statement.deployment_domain);
    }
    debug_assert_eq!(offset, V5_FULL_CU_TRANSACTION_WIRE_BYTES);
    wire
}

fn full_v5_transaction_wire(statement: &AtomicPaymentStatementV4) -> Vec<u8> {
    build_v5_tag67_transaction_wire(statement).to_vec()
}

fn completed_system_program_cpi_log_evidence(logs: &[String]) -> Option<Vec<String>> {
    let system_program = Pubkey::default().to_string();
    let invoke_prefix = format!("Program {system_program} invoke");
    let success_line = format!("Program {system_program} success");
    let invoke = logs
        .iter()
        .position(|line| line.starts_with(&invoke_prefix))?;
    logs.iter()
        .skip(invoke + 1)
        .position(|line| line == &success_line)?;
    Some(
        logs.iter()
            .filter(|line| line.starts_with(&format!("Program {system_program} ")))
            .cloned()
            .collect(),
    )
}

fn run_real_full_transaction_with_serialized_fixture(
    results_dir: &Path,
    probe_so: &Path,
    selector: u8,
    statement: &AtomicPaymentStatementV4,
    proof_body: &[u8],
    artifact_metadata: &V5FullCuArtifactMetadata,
    summary_filename: &str,
    sbf_build_tool: &V5ExecutableProvenance,
    rust_sources: &V5RustSourceProvenance,
    measurement_test_name: &'static str,
    marker_mode: V5NullifierMarkerFixtureMode,
) -> Result<V5Layer0CuProbeOutcome> {
    let validator_before = validator_provenance()?;
    ensure!(artifact_metadata.query_selector == selector);
    ensure!(artifact_metadata.selected_branch_good);
    let sealed_proof = finalized_proof_account_data(proof_body)?;
    let probe_bytes = fs::read(probe_so)?;

    let public_anchor = aspis_statement::encode_digest_canonical(&statement.spend.anchor);
    let public_nullifier = aspis_statement::encode_digest_canonical(&statement.spend.nullifier);
    let pool_address = Pubkey::new_from_array(statement.pool);
    let (marker_address, _) = atomic_nullifier_address(&aspis_verifier::id(), &public_nullifier);
    let selector_seed = [selector];
    let (proof_address, _) = Pubkey::find_program_address(
        &[b"v5-full-cu-real-proof-v1", &selector_seed],
        &aspis_verifier::id(),
    );
    ensure!(
        proof_address != pool_address
            && proof_address != marker_address
            && pool_address != marker_address,
        "v5 full-CU fixture account collision"
    );

    let mut pool_data = [0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV2 {
        sequence: statement.sequence,
        anchor: public_anchor,
        deployment_domain: statement.deployment_domain,
    }
    .encode(&mut pool_data)
    .map_err(|error| anyhow!("encode v5 full-CU pool fixture: {error:?}"))?;
    let marker_data = [0u8; ATOMIC_NULLIFIER_MARKER_LEN];
    let wire = full_v5_transaction_wire(statement);
    let instructions = vec![wire; REPEATS];
    let simulations = match marker_mode {
        V5NullifierMarkerFixtureMode::MissingCreateCpi => {
            simulate_atomic_program_account_instructions_with_absent_marker(
                probe_so,
                proof_address,
                &sealed_proof,
                pool_address,
                &pool_data,
                marker_address,
                &instructions,
            )?
        }
        V5NullifierMarkerFixtureMode::PreloadedProgramOwnedControl => {
            simulate_atomic_program_account_instructions(
                probe_so,
                proof_address,
                &sealed_proof,
                pool_address,
                &pool_data,
                marker_address,
                &marker_data,
                &instructions,
            )?
        }
    };
    let validator_after = validator_provenance()?;
    ensure!(
        validator_after == validator_before,
        "solana-test-validator provenance changed during measurement: before={validator_before:?}, after={validator_after:?}"
    );
    ensure!(
        simulations.len() == REPEATS,
        "v5 full-CU repeat count drift"
    );
    let totals = simulations
        .iter()
        .map(|simulation| simulation.units)
        .collect::<Vec<_>>();
    ensure!(
        totals.iter().all(|units| *units == totals[0]),
        "v5 full transaction CU was nondeterministic across repeats: {totals:?}"
    );
    let system_program_cpi_log_evidence = simulations
        .iter()
        .filter_map(|simulation| completed_system_program_cpi_log_evidence(&simulation.logs))
        .collect::<Vec<_>>();
    let system_program_cpi_observed_all_repeats = system_program_cpi_log_evidence.len() == REPEATS;
    ensure!(
        system_program_cpi_observed_all_repeats == marker_mode.requires_system_program_cpi(),
        "v5 marker mode {} system-CPI evidence drift: observed {}/{} repetitions",
        marker_mode.label(),
        system_program_cpi_log_evidence.len(),
        REPEATS,
    );

    let total = totals[0];
    let phase_markers = parse_cu_markers(&simulations[0].logs, "aspis-cu:")
        .into_iter()
        .map(|marker| V5FullCuPhaseMarker {
            label: marker.label,
            remaining: marker.remaining,
            delta_from_previous: marker.delta_from_previous,
        })
        .collect::<Vec<_>>();
    ensure!(
        phase_markers.is_empty(),
        "frozen tag-67 verifier unexpectedly retained CU phase instrumentation: {:?}",
        phase_markers
            .iter()
            .map(|marker| marker.label.as_str())
            .collect::<Vec<_>>()
    );
    const TRANSACTION_CU_LIMIT: u64 = 1_400_000;
    ensure!(
        total <= TRANSACTION_CU_LIMIT,
        "successful v5 full-CU simulation exceeded configured limit: {total}"
    );
    let summary = V5FullCuTransactionSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: format!("NO_DNA=1 V5_CU_RESULTS_DIR=<tmp> cargo test -p aspis-xtask {measurement_test_name} --release -- --ignored --nocapture # marker-mode={}", marker_mode.label()),
        scope: format!("One isolated local-SBF tag-67 transaction for selected Good branch {selector}: sealed real-witness v5 proof account, exact branch-{selector} transcript-derived q18 queries, five branch-regenerated authenticated openings, semantic terminal, four-claim compact-B relation, complete FRI checks, and the unchanged atomic verify-and-apply state wrapper. Nullifier marker fixture mode: {}.", marker_mode.label()),
        security_scope: format!("CU fixture only. The production host artifact remains leastGood={}; selector {selector} is {}. Selectors one and two are explicitly test-only malicious/nonleast branch overrides used solely to measure selected-Good verifier control flow; their q18 indices, fixed C1/C2 records, all five private opening sections, and every later FRI value are rebuilt from the retained committed codewords and original deterministic salts. The five caller-supplied public FS salt fields implement the wire and transcript-order hook needed by one Chiesa--Fenzi premise; deterministic fixture salts do not instantiate its fresh uniform sampling requirement. The radix-4/oracle transport, BCS reduction, and HVZK obligations remain open. Component-B production sampling and Rust--Lean correspondence remain open. Direct Component C is the live finite route; its executable encoder/downstream correspondence remains an explicit premise. This measurement is not a v5 security proof, production grammar, or deployment authorization.", artifact_metadata.honest_least_good_selector, if artifact_metadata.test_only_nonleast_branch_override { "nonleast but selected-Good-valid" } else { "the honest least-Good branch" }),
        transaction_repeats: REPEATS,
        transaction_total_cu: total,
        transaction_cu_limit: TRANSACTION_CU_LIMIT,
        transaction_headroom_cu: TRANSACTION_CU_LIMIT - total,
        transaction_total_repeats: totals,
        nullifier_marker_fixture_mode: marker_mode.label(),
        nullifier_marker_simulation_helper: marker_mode.simulation_helper(),
        nullifier_marker_preloaded: marker_mode.preloads_marker(),
        system_program_cpi_required: marker_mode.requires_system_program_cpi(),
        system_program_cpi_observed_all_repeats,
        system_program_cpi_log_evidence,
        phase_markers,
        query_selector: artifact_metadata.query_selector,
        honest_least_good_selector: artifact_metadata.honest_least_good_selector,
        batch_nonce: artifact_metadata.batch_nonce,
        selected_branch_good: artifact_metadata.selected_branch_good,
        test_only_nonleast_branch_override: artifact_metadata
            .test_only_nonleast_branch_override,
        all_candidate_good: artifact_metadata
            .good_gate_evaluations
            .map(V5HostGoodGateEvaluation::is_good),
        proof_body_bytes: proof_body.len(),
        sealed_proof_account_bytes: sealed_proof.len(),
        sealed_proof_account_sha256: hex(&Sha256::digest(&sealed_proof)),
        proof_body_sha256: hex(&Sha256::digest(proof_body)),
        query_indices: artifact_metadata.query_indices,
        opening_index_counts: artifact_metadata.opening_index_counts,
        opening_frontier_nodes: artifact_metadata.opening_frontier_nodes,
        opening_section_bytes: artifact_metadata.opening_section_bytes,
        probe_sbf_bytes: probe_bytes.len(),
        probe_sbf_sha256: hex(&Sha256::digest(&probe_bytes)),
        sbf_build_command: if let Some(path) = env::var_os("V5_CU_PREBUILT_SBF") {
            format!(
                "prebuilt exact SBF {} sha256 {}",
                PathBuf::from(path).display(),
                env::var("V5_CU_PREBUILT_SBF_SHA256")
                    .expect("prebuilt SBF hash was validated before measurement")
            )
        } else {
            "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v5-cu-probe".to_string()
        },
        sbf_build_tool: sbf_build_tool.clone(),
        rust_sources: rust_sources.clone(),
        validator: validator_before,
        state_transition_wrapper: format!("aspis_verifier::atomic_payment::verify_and_apply_atomic_payment_state (proof retained, marker mode {})", marker_mode.label()),
        component_a: "real sampled aligned circle masks".to_string(),
        component_b: "real structured ten-round degree-27 sumcheck mask with compact authenticated terminal functional and a deterministic CU-fixture pivot pad committed in C2; fresh independent production sampling remains an explicit obligation".to_string(),
        component_c: "direct full-kernel lane; the live finite Component-C route, with executable encoder/downstream correspondence retained as an explicit premise".to_string(),
        accepted_three_of_three: true,
        deterministic_cu_three_of_three: true,
        conclusion: format!(
            "The feature-gated v5 tag-67 selected-Good branch {selector} transaction accepted three of three local-SBF simulations at {total} CU in marker mode {}. System Program CPI completion was observed in {}/{} repetitions. The production host still chooses leastGood={}; this {} fixture answers branch-specific implementation fit only. Production sampling/correspondence for Component B, executable correspondence for direct Component C, and the full security argument remain open.",
            marker_mode.label(),
            usize::from(system_program_cpi_observed_all_repeats) * REPEATS,
            REPEATS,
            artifact_metadata.honest_least_good_selector,
            if artifact_metadata.test_only_nonleast_branch_override { "test-only nonleast" } else { "honest least-Good" }
        ),
    };
    fs::create_dir_all(results_dir)?;
    let path = results_dir.join(summary_filename);
    fs::write(
        &path,
        format!("{}\n", serde_json::to_string_pretty(&summary)?),
    )?;
    Ok(V5Layer0CuProbeOutcome {
        path,
        production_kernel_cu: 0,
        candidate_kernel_cu: total,
        production_to_candidate_delta_cu: total as i64,
        generic_fused_width_saving_cu: 0,
        generic16_fusion_saving_cu: 0,
    })
}

fn run_real_full_transaction_for_marker_mode(
    results_dir: &Path,
    root: &Path,
    marker_mode: V5NullifierMarkerFixtureMode,
) -> Result<V5Layer0CuProbeOutcome> {
    let sbf_build_tool_before = executable_provenance("cargo-build-sbf", &["--version"])?;
    let rust_sources_before = rust_source_provenance(root)?;
    let probe_so = build_sbf(root, "v5-cu-probe", "aspis_verifier_v5_full_transaction_cu")?;
    ensure!(
        executable_provenance("cargo-build-sbf", &["--version"])? == sbf_build_tool_before,
        "cargo-build-sbf provenance changed during SBF build"
    );
    ensure!(
        rust_source_provenance(root)? == rust_sources_before,
        "Rust/Cargo source snapshot changed during SBF build"
    );
    let (statement, proof_body, artifact_metadata) = build_real_v5_runtime_account_data()?;
    let honest_selector = artifact_metadata.query_selector;
    ensure!(honest_selector == artifact_metadata.honest_least_good_selector);
    ensure!(!artifact_metadata.test_only_nonleast_branch_override);
    let summary_filename = match marker_mode {
        V5NullifierMarkerFixtureMode::MissingCreateCpi => {
            "v5_full_transaction_missing_marker_cu_probe.json"
        }
        V5NullifierMarkerFixtureMode::PreloadedProgramOwnedControl => {
            "v5_full_transaction_preloaded_marker_control_cu_probe.json"
        }
    };
    let measurement_test_name = match marker_mode {
        V5NullifierMarkerFixtureMode::MissingCreateCpi => {
            "v5_full_transaction_current_good_gate_cu_measurement"
        }
        V5NullifierMarkerFixtureMode::PreloadedProgramOwnedControl => {
            "v5_full_transaction_preloaded_marker_control_cu_measurement"
        }
    };
    let outcome = run_real_full_transaction_with_serialized_fixture(
        results_dir,
        &probe_so,
        honest_selector,
        &statement,
        &proof_body,
        &artifact_metadata,
        summary_filename,
        &sbf_build_tool_before,
        &rust_sources_before,
        measurement_test_name,
        marker_mode,
    )?;
    ensure!(
        rust_source_provenance(root)? == rust_sources_before,
        "Rust/Cargo source snapshot changed during CU measurement"
    );
    Ok(outcome)
}

fn run_real_full_transaction(results_dir: &Path, root: &Path) -> Result<V5Layer0CuProbeOutcome> {
    run_real_full_transaction_for_marker_mode(results_dir, root, V5_DEVNET_PATH_MARKER_MODE)
}

fn run_real_full_transaction_preloaded_marker_control(
    results_dir: &Path,
    root: &Path,
) -> Result<V5Layer0CuProbeOutcome> {
    run_real_full_transaction_for_marker_mode(results_dir, root, V5_PRELOADED_MARKER_CONTROL_MODE)
}

fn run_real_full_transactions_all_selectors_for_marker_mode(
    results_dir: &Path,
    root: &Path,
    marker_mode: V5NullifierMarkerFixtureMode,
) -> Result<Vec<V5Layer0CuProbeOutcome>> {
    let sbf_build_tool_before = executable_provenance("cargo-build-sbf", &["--version"])?;
    let rust_sources_before = rust_source_provenance(root)?;
    let probe_so = build_sbf(root, "v5-cu-probe", "aspis_verifier_v5_full_transaction_cu")?;
    ensure!(
        executable_provenance("cargo-build-sbf", &["--version"])? == sbf_build_tool_before,
        "cargo-build-sbf provenance changed during SBF build"
    );
    ensure!(
        rust_source_provenance(root)? == rust_sources_before,
        "Rust/Cargo source snapshot changed during SBF build"
    );
    let measurement_test_name = match marker_mode {
        V5NullifierMarkerFixtureMode::MissingCreateCpi => {
            "v5_full_transaction_all_selected_good_branches_cu_measurement"
        }
        V5NullifierMarkerFixtureMode::PreloadedProgramOwnedControl => {
            "v5_full_transaction_all_selected_good_branches_preloaded_marker_control_cu_measurement"
        }
    };
    // Mine the shared batch/fold/final work exactly once. Selector-specific
    // fixtures only rebuild query-dependent records and opening sections from
    // this one honest least-Good artifact.
    let (statement, mut artifact) = build_real_v5_fixture_with_pivot_pad(fixture_q(29_999))?;
    let honest_least_good_selector = artifact.query_selector;
    ensure!(
        artifact
            .good_gate_evaluations
            .iter()
            .position(|evaluation| evaluation.is_good())
            == Some(usize::from(honest_least_good_selector)),
        "shared v5 artifact did not retain its honest least-Good selector"
    );
    let mut outcomes = Vec::with_capacity(3);
    for selector in 0..3u8 {
        let (proof_body, artifact_metadata) =
            serialize_real_v5_runtime_account_data_for_test_selector(
                &statement,
                &mut artifact,
                Some(selector),
            )?;
        ensure!(
            artifact_metadata.honest_least_good_selector == honest_least_good_selector,
            "selector {selector} changed honest least-Good metadata"
        );
        let summary_filename = match marker_mode {
            V5NullifierMarkerFixtureMode::MissingCreateCpi => {
                format!("v5_full_transaction_selector_{selector}_missing_marker_cu_probe.json")
            }
            V5NullifierMarkerFixtureMode::PreloadedProgramOwnedControl => format!(
                "v5_full_transaction_selector_{selector}_preloaded_marker_control_cu_probe.json"
            ),
        };
        outcomes.push(run_real_full_transaction_with_serialized_fixture(
            results_dir,
            &probe_so,
            selector,
            &statement,
            &proof_body,
            &artifact_metadata,
            &summary_filename,
            &sbf_build_tool_before,
            &rust_sources_before,
            measurement_test_name,
            marker_mode,
        )?);
        ensure!(
            rust_source_provenance(root)? == rust_sources_before,
            "Rust/Cargo source snapshot changed during selector {selector} CU measurement"
        );
    }
    Ok(outcomes)
}

fn run_real_full_transactions_all_selectors(
    results_dir: &Path,
    root: &Path,
) -> Result<Vec<V5Layer0CuProbeOutcome>> {
    run_real_full_transactions_all_selectors_for_marker_mode(
        results_dir,
        root,
        V5_DEVNET_PATH_MARKER_MODE,
    )
}

fn run_real_full_transactions_all_selectors_preloaded_marker_control(
    results_dir: &Path,
    root: &Path,
) -> Result<Vec<V5Layer0CuProbeOutcome>> {
    run_real_full_transactions_all_selectors_for_marker_mode(
        results_dir,
        root,
        V5_PRELOADED_MARKER_CONTROL_MODE,
    )
}

/// Regenerate and measure exactly one selected-Good diagnostic branch. The
/// completed proof body is persisted before simulation so a later replay does
/// not need the expensive retained-codeword artifact. This deliberately does
/// not call either all-selector helper.
fn run_real_full_transaction_single_selector(
    results_dir: &Path,
    root: &Path,
    selector: u8,
) -> Result<V5Layer0CuProbeOutcome> {
    ensure!(
        selector < 3,
        "single selected-Good selector is out of range"
    );
    let sbf_build_tool_before = executable_provenance("cargo-build-sbf", &["--version"])?;
    let rust_sources_before = rust_source_provenance(root)?;
    let probe_so = build_sbf(root, "v5-cu-probe", "aspis_verifier_v5_full_transaction_cu")?;
    ensure!(
        rust_source_provenance(root)? == rust_sources_before,
        "Rust/Cargo source snapshot changed while resolving the frozen SBF"
    );

    let (statement, mut artifact) = build_real_v5_fixture_with_pivot_pad(fixture_q(29_999))?;
    let (proof_body, artifact_metadata) = serialize_real_v5_runtime_account_data_for_test_selector(
        &statement,
        &mut artifact,
        Some(selector),
    )?;
    ensure!(artifact_metadata.query_selector == selector);

    fs::create_dir_all(results_dir)?;
    let proof_path = results_dir.join(format!("v5_selector_{selector}_proof_body.bin"));
    let mut proof_file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&proof_path)
        .with_context(|| format!("create selector proof cache {}", proof_path.display()))?;
    use std::io::Write as _;
    proof_file.write_all(&proof_body)?;
    proof_file.sync_all()?;
    ensure!(
        fs::read(&proof_path)? == proof_body,
        "selector proof cache drift"
    );

    let outcome = run_real_full_transaction_with_serialized_fixture(
        results_dir,
        &probe_so,
        selector,
        &statement,
        &proof_body,
        &artifact_metadata,
        &format!("v5_selector_{selector}_frozen_sbf_missing_marker_cu.json"),
        &sbf_build_tool_before,
        &rust_sources_before,
        "v5_full_transaction_single_selected_good_branch_cu_measurement",
        V5NullifierMarkerFixtureMode::MissingCreateCpi,
    )?;
    ensure!(
        rust_source_provenance(root)? == rust_sources_before,
        "Rust/Cargo source snapshot changed during single-selector CU measurement"
    );
    Ok(outcome)
}

/// Replay one retained selector-specific proof against the frozen SBF without
/// rebuilding the proof or program. The hashes below authenticate the exact
/// proof bodies generated by the independent selector runs.
fn replay_cached_selected_good_branch(
    frozen_dir: &Path,
    selector: u8,
) -> Result<V5Layer0CuProbeOutcome> {
    let (expected_proof_sha256, expected_sealed_sha256) = match selector {
        1 => (
            "c671966c30e2f00363359e668381f3e4bf0f9e99d03da54887c93d5066fc2f5d",
            "f4ab44139c54d914246edf37caf39d6bb80e45c80b7c12c126f9956f9efab69a",
        ),
        2 => (
            "9e1298513f691aeac88be67027b90a6f54ec0b9a6f06eeb1c01cdac21a7d1996",
            "418b9202e76e70878c83158bc832238f4c28ee7558cc4bb4fb17da49252adb48",
        ),
        _ => bail!("cached selected-Good replay supports only selectors 1 and 2"),
    };
    let replay_dir = frozen_dir.join("selector-replay");
    let proof_path = replay_dir.join(format!("v5_selector_{selector}_proof_body.bin"));
    let proof_body = fs::read(&proof_path)
        .with_context(|| format!("read cached selector proof {}", proof_path.display()))?;
    ensure!(
        hex(&Sha256::digest(&proof_body)) == expected_proof_sha256,
        "cached selector {selector} proof-body hash mismatch"
    );
    ensure!(
        proof_body.get(V5_CU_PROBE_QUERY_SELECTOR_OFFSET) == Some(&selector),
        "cached selector {selector} proof-body selector byte mismatch"
    );
    let sealed_proof = finalized_proof_account_data(&proof_body)?;
    ensure!(
        hex(&Sha256::digest(&sealed_proof)) == expected_sealed_sha256,
        "cached selector {selector} sealed-account hash mismatch"
    );

    let probe_so = frozen_dir.join("aspis_verifier_v5_tag67.so");
    let expected_sbf_sha256 = env::var("V5_CU_PREBUILT_SBF_SHA256")
        .context("V5_CU_PREBUILT_SBF_SHA256 must pin the frozen SBF")?;
    let probe_bytes =
        fs::read(&probe_so).with_context(|| format!("read frozen SBF {}", probe_so.display()))?;
    ensure!(
        hex(&Sha256::digest(&probe_bytes)) == expected_sbf_sha256,
        "frozen SBF hash mismatch"
    );

    let (statement, _) = real_v5_statement_and_witness();
    let queries = v5_complete_queries(aspis_prover::HOST_HASH, &proof_body)
        .map_err(|error| anyhow!("derive cached selector {selector} queries: {error:?}"))?;
    let pool_address = Pubkey::new_from_array(statement.pool);
    let public_nullifier = aspis_statement::encode_digest_canonical(&statement.spend.nullifier);
    let (marker_address, _) = atomic_nullifier_address(&aspis_verifier::id(), &public_nullifier);
    let selector_seed = [selector];
    let (proof_address, _) = Pubkey::find_program_address(
        &[b"v5-full-cu-real-proof-v1", &selector_seed],
        &aspis_verifier::id(),
    );
    let mut pool_data = [0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV2 {
        sequence: statement.sequence,
        anchor: aspis_statement::encode_digest_canonical(&statement.spend.anchor),
        deployment_domain: statement.deployment_domain,
    }
    .encode(&mut pool_data)
    .map_err(|error| anyhow!("encode cached-replay pool fixture: {error:?}"))?;
    let instructions = vec![full_v5_transaction_wire(&statement); REPEATS];
    let simulations = simulate_atomic_program_account_instructions_with_absent_marker(
        &probe_so,
        proof_address,
        &sealed_proof,
        pool_address,
        &pool_data,
        marker_address,
        &instructions,
    )?;
    let totals = simulations
        .iter()
        .map(|simulation| simulation.units)
        .collect::<Vec<_>>();
    ensure!(totals.len() == REPEATS, "cached replay repeat-count drift");
    ensure!(
        totals.iter().all(|total| *total == totals[0]),
        "cached selector {selector} CU was nondeterministic: {totals:?}"
    );
    let system_program_cpi_log_evidence = simulations
        .iter()
        .filter_map(|simulation| completed_system_program_cpi_log_evidence(&simulation.logs))
        .collect::<Vec<_>>();
    ensure!(
        system_program_cpi_log_evidence.len() == REPEATS,
        "cached selector {selector} did not complete System Program CPI in every repeat"
    );
    const TRANSACTION_CU_LIMIT: u64 = 1_400_000;
    let total = totals[0];
    ensure!(total <= TRANSACTION_CU_LIMIT);
    let summary_path = replay_dir.join(format!(
        "v5_selector_{selector}_cached_replay_missing_marker_cu.json"
    ));
    fs::write(
        &summary_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&serde_json::json!({
                "artifact": "v5_selector_cached_replay_missing_marker_cu",
                "query_selector": selector,
                "marker_mode": "missing-system-owned-create-cpi",
                "sbf_path": probe_so,
                "sbf_bytes": probe_bytes.len(),
                "sbf_sha256": expected_sbf_sha256,
                "proof_body_path": proof_path,
                "proof_body_bytes": proof_body.len(),
                "proof_body_sha256": expected_proof_sha256,
                "sealed_proof_account_bytes": sealed_proof.len(),
                "sealed_proof_account_sha256": expected_sealed_sha256,
                "query_indices": queries,
                "totals_cu": totals,
                "transaction_cu_limit": TRANSACTION_CU_LIMIT,
                "transaction_headroom_cu": TRANSACTION_CU_LIMIT - total,
                "identical_repeats": REPEATS,
                "system_program_cpi_completed_repeats": system_program_cpi_log_evidence.len(),
                "system_program_cpi_log_evidence": system_program_cpi_log_evidence,
                "proof_generation_performed": false,
                "sbf_build_performed": false,
            }))?
        ),
    )?;
    Ok(V5Layer0CuProbeOutcome {
        path: summary_path,
        production_kernel_cu: 0,
        candidate_kernel_cu: total,
        production_to_candidate_delta_cu: total as i64,
        generic_fused_width_saving_cu: 0,
        generic16_fusion_saving_cu: 0,
    })
}

fn zero_v5_pcs_messages() -> V5SpendMessages {
    // A zero word is a genuine degree-zero member of every encoded lane. It
    // keeps verifier control flow live and shares final4=0 with the isolated
    // production-order relation stress tail.
    let c1: [Vec<M31>; V5_C1_LANES] = core::array::from_fn(|_| vec![M31::ZERO; V5_TRACE_ROWS]);
    let c2: [Vec<QM31>; V5_C2_LANES] = core::array::from_fn(|_| vec![QM31::ZERO; V5_TRACE_ROWS]);
    V5SpendMessages { c1, c2 }
}

fn install_authenticated_layer0_records(data: &mut [u8], c1_records: &[u8], c2_records: &[u8]) {
    assert_eq!(
        c1_records.len(),
        V5_CU_PROBE_QUERY_COUNT * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES
    );
    assert_eq!(
        c2_records.len(),
        V5_CU_PROBE_QUERY_COUNT * V5_CU_PROBE_C2_RECORD_BYTES
    );
    for query in 0..V5_CU_PROBE_QUERY_COUNT {
        let c1_source = &c1_records[query * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES
            ..(query + 1) * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES];
        let candidate_start =
            V5_CU_PROBE_CANDIDATE_C1_OFFSET + query * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES;
        data[candidate_start..candidate_start + V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES]
            .copy_from_slice(c1_source);

        let c2_source = &c2_records
            [query * V5_CU_PROBE_C2_RECORD_BYTES..(query + 1) * V5_CU_PROBE_C2_RECORD_BYTES];
        let c2_start = V5_CU_PROBE_C2_OFFSET + query * V5_CU_PROBE_C2_RECORD_BYTES;
        data[c2_start..c2_start + V5_CU_PROBE_C2_RECORD_BYTES].copy_from_slice(c2_source);
    }
}

fn runtime_account_data() -> Result<Vec<u8>> {
    let mut state = 0x5a17_9c31_26f0_0012;
    let mut data = vec![0u8; V5_CU_PROBE_DIAGNOSTIC_ACCOUNT_BYTES];
    data[..V5_CU_PROBE_ACCOUNT_MAGIC.len()].copy_from_slice(&V5_CU_PROBE_ACCOUNT_MAGIC);
    next_qm31(&mut state)
        .write_le_bytes(&mut data[V5_CU_PROBE_GAMMA_OFFSET..V5_CU_PROBE_GAMMA_OFFSET + QM31_BYTES]);
    for query in 0..V5_CU_PROBE_QUERY_COUNT {
        let production_start =
            V5_CU_PROBE_PRODUCTION_C1_OFFSET + query * V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES;
        for slot in 0..FIBER_SLOTS {
            for column in 0..V5_CU_PROBE_PRODUCTION_C1_COLUMNS {
                let value = next_m31(&mut state);
                let offset = production_start
                    + (slot * V5_CU_PROBE_PRODUCTION_C1_COLUMNS + column) * M31_BYTES;
                data[offset..offset + M31_BYTES].copy_from_slice(&value.to_le_bytes());
            }
        }
        for salt in 0..STATE_ONLY_PRIVATE_LEAF_SALT_BYTES {
            data[production_start + V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES + salt] =
                next_m31(&mut state).0 as u8;
        }

        let candidate_start =
            V5_CU_PROBE_CANDIDATE_C1_OFFSET + query * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES;
        for slot in 0..FIBER_SLOTS {
            for column in 0..V5_CU_PROBE_CANDIDATE_C1_COLUMNS {
                let source = production_start
                    + (slot * V5_CU_PROBE_PRODUCTION_C1_COLUMNS + column) * M31_BYTES;
                let target = candidate_start
                    + (slot * V5_CU_PROBE_CANDIDATE_C1_COLUMNS + column) * M31_BYTES;
                let word: [u8; M31_BYTES] = data[source..source + M31_BYTES].try_into().unwrap();
                data[target..target + M31_BYTES].copy_from_slice(&word);
            }
        }
        let salt: [u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES] = data[production_start
            + V5_CU_PROBE_PRODUCTION_C1_VALUE_BYTES
            ..production_start + V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES]
            .try_into()
            .unwrap();
        data[candidate_start + V5_CU_PROBE_CANDIDATE_C1_VALUE_BYTES
            ..candidate_start + V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES]
            .copy_from_slice(&salt);

        let c2_start = V5_CU_PROBE_C2_OFFSET + query * V5_CU_PROBE_C2_RECORD_BYTES;
        for helper in 0..V5_CU_PROBE_C2_COLUMNS {
            for slot in 0..FIBER_SLOTS {
                let offset = c2_start + (helper * FIBER_SLOTS + slot) * QM31_BYTES;
                next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
            }
        }
        for salt in 0..STATE_ONLY_PRIVATE_LEAF_SALT_BYTES {
            data[c2_start + V5_CU_PROBE_C2_VALUE_BYTES + salt] = next_m31(&mut state).0 as u8;
        }
    }
    for index in 0..V5_CU_PROBE_RELATION_POINTS {
        let offset = V5_CU_PROBE_RELATION_SCALES_OFFSET + index * QM31_BYTES;
        next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
    }
    for index in 0..V5_CU_PROBE_RELATION_POINTS * V5_CU_PROBE_RELATION_LOG_ROWS as usize {
        let offset = V5_CU_PROBE_RELATION_POINTS_OFFSET + index * QM31_BYTES;
        next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
    }
    for index in 0..V5_CU_PROBE_RELATION_CLAIMS_PER_LANE * V5_CU_PROBE_RELATION_LANES {
        let offset = V5_CU_PROBE_RELATION_CLAIMS_OFFSET + index * QM31_BYTES;
        next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
    }
    for index in 0..V5_CU_PROBE_RELATION_FOLDS {
        let offset = V5_CU_PROBE_RELATION_ALPHAS_OFFSET + index * QM31_BYTES;
        next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
    }
    for index in 0..V5_CU_PROBE_RELATION_FINAL_VALUES {
        let offset = V5_CU_PROBE_RELATION_FINAL_OFFSET + index * QM31_BYTES;
        next_qm31(&mut state).write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
    }
    let prefix = build_deterministic_synthetic_v5_wire(aspis_prover::host_hashv);
    data[V5_CU_PROBE_PREFIX_OFFSET..V5_CU_PROBE_PRIVATE_ROOTS_OFFSET].copy_from_slice(&prefix);
    data[V5_CU_PROBE_RELATION_CLAIMS_OFFSET..V5_CU_PROBE_RELATION_ALPHAS_OFFSET]
        .copy_from_slice(&prefix[V5_WIRE_OPENINGS_OFFSET..V5_WIRE_TERMINALS_OFFSET]);

    let gamma =
        QM31::from_le_bytes(&data[V5_CU_PROBE_GAMMA_OFFSET..V5_CU_PROBE_GAMMA_OFFSET + QM31_BYTES])
            .unwrap();
    let alphas: [QM31; 4] = core::array::from_fn(|index| {
        let offset = V5_CU_PROBE_RELATION_ALPHAS_OFFSET + index * QM31_BYTES;
        QM31::from_le_bytes(&data[offset..offset + QM31_BYTES]).unwrap()
    });
    let c1_salts = deterministic_salts(0x51, 1 << 17);
    let c2_salts = deterministic_salts(0x52, 1 << 17);
    let later_salts: [Vec<[u8; 32]>; V5_LATER_LAYERS] = [
        deterministic_salts(0x61, 1 << 15),
        deterministic_salts(0x62, 1 << 13),
        deterministic_salts(0x63, 1 << 11),
    ];
    let provisional_artifact = build_v5_cu_stress_pcs_artifact(
        zero_v5_pcs_messages(),
        gamma,
        alphas,
        &V5_CU_PROBE_PROVISIONAL_QUERIES,
        V5PcsSalts {
            c1: &c1_salts,
            c2: &c2_salts,
            later: [&later_salts[0], &later_salts[1], &later_salts[2]],
        },
        aspis_prover::HOST_HASH,
    )
    .map_err(|error| anyhow!("build exact v5 CU-stress PCS suffix: {error}"))?;

    let roots = [
        provisional_artifact.roots.c1,
        provisional_artifact.roots.c2,
        provisional_artifact.roots.later[0],
        provisional_artifact.roots.later[1],
        provisional_artifact.roots.later[2],
    ];
    for (index, root) in roots.iter().enumerate() {
        let offset = V5_CU_PROBE_PRIVATE_ROOTS_OFFSET + 32 * index;
        data[offset..offset + 32].copy_from_slice(root);
    }
    for (index, coefficient) in provisional_artifact
        .folds
        .final_coefficients
        .iter()
        .enumerate()
    {
        let offset = V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET + QM31_BYTES * index;
        coefficient.write_le_bytes(&mut data[offset..offset + QM31_BYTES]);
    }
    let relation_stress = build_v5_complete_relation_stress_tail_for_diagnostics(&data)
        .map_err(|error| anyhow!("build exact combined v5 relation stress tail: {error:?}"))?;
    ensure!(relation_stress.len() == V5_RELATION_STRESS_BYTES);
    data[V5_CU_PROBE_RELATION_STRESS_OFFSET..V5_CU_PROBE_FINAL_NONCE_OFFSET]
        .copy_from_slice(&relation_stress);
    data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET] = 0;

    // Mine against the exact pre-final transcript state later replayed by the
    // SBF verifier. The canonical verifier predicate checks the returned
    // nonce again before any query is derived.
    let mut transcript = v5_complete_transcript_before_final(aspis_prover::HOST_HASH, &data)
        .map_err(|error| anyhow!("build v5 CU-stress transcript: {error:?}"))?;
    transcript.absorb(
        label::M31_CIRCLE_FINAL_TENSOR_POLY,
        &data[V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET..V5_CU_PROBE_RELATION_STRESS_OFFSET],
    );
    let final_nonce = aspis_prover::pow::find_grinding_nonce(
        &transcript,
        aspis_core::state_only_prefix::STATE_ONLY_SPEND_GRINDING_BITS,
    );
    data[V5_CU_PROBE_FINAL_NONCE_OFFSET..V5_CU_PROBE_QUERY_SELECTOR_OFFSET]
        .copy_from_slice(&final_nonce.to_le_bytes());
    let queries = v5_complete_queries(aspis_prover::HOST_HASH, &data)
        .map_err(|error| anyhow!("derive mined v5 CU-stress q18: {error:?}"))?;

    // Queries do not affect any committed codeword or root. Rebuild the five
    // serialized Merkle sections for the transcript-derived positions and
    // require the query-independent artefact to remain byte-identical.
    let artifact = build_v5_cu_stress_pcs_artifact(
        zero_v5_pcs_messages(),
        gamma,
        alphas,
        &queries,
        V5PcsSalts {
            c1: &c1_salts,
            c2: &c2_salts,
            later: [&later_salts[0], &later_salts[1], &later_salts[2]],
        },
        aspis_prover::HOST_HASH,
    )
    .map_err(|error| anyhow!("rebuild transcript-derived v5 PCS suffix: {error}"))?;
    ensure!(
        artifact.roots == provisional_artifact.roots,
        "v5 roots changed with q18"
    );
    ensure!(
        artifact.folds.final_coefficients == provisional_artifact.folds.final_coefficients,
        "v5 final polynomial changed with q18"
    );
    let verified = verify_v5_pcs_openings(
        aspis_prover::HOST_HASH,
        &artifact.roots,
        &queries,
        &artifact.openings.bytes,
    )
    .map_err(|error| anyhow!("self-verify transcript-derived v5 PCS suffix: {error}"))?;
    install_authenticated_layer0_records(&mut data, verified.c1.records, verified.c2.records);
    data.extend_from_slice(&artifact.openings.bytes);
    Ok(data)
}

fn probe_wire(mode: u8, account_data: &[u8]) -> Result<Vec<u8>> {
    let expected = probe_sink(mode, account_data)
        .map_err(|error| anyhow!("host v5 CU probe mode {mode} failed: {error:?}"))?;
    let mut wire = Vec::with_capacity(V5_CU_PROBE_WIRE_BYTES);
    wire.push(V5_CU_PROBE_TAG);
    wire.push(mode);
    wire.extend_from_slice(&expected);
    ensure!(wire.len() == V5_CU_PROBE_WIRE_BYTES, "probe wire drift");
    Ok(wire)
}

fn one_value(values: &[u64], label: &str) -> Result<u64> {
    let (&first, rest) = values
        .split_first()
        .ok_or_else(|| anyhow!("no {label} CU measurements"))?;
    ensure!(
        rest.iter().all(|&value| value == first),
        "non-deterministic {label} CU measurements: {values:?}"
    );
    Ok(first)
}

fn marker_delta(value: Option<i64>, label: &str) -> Result<u64> {
    let delta = value.ok_or_else(|| anyhow!("marker {label} omitted delta"))?;
    ensure!(delta >= 0, "marker {label} increased remaining CU: {delta}");
    Ok(delta as u64)
}

fn marked_intervals(
    simulation: &StatelessSimulationResult,
    relation_mode: bool,
    composite_mode: bool,
) -> Result<(
    u64,
    u64,
    Option<u64>,
    Option<u64>,
    Option<u64>,
    Option<u64>,
    Option<u64>,
    Option<u64>,
    Option<u64>,
)> {
    let markers = parse_cu_markers(&simulation.logs, "aspis-cu:");
    let labels = markers
        .iter()
        .map(|marker| marker.label.as_str())
        .collect::<Vec<_>>();
    if composite_mode {
        ensure!(
            labels
                == [
                    PARSE_START_MARKER,
                    PREFIX_START_MARKER,
                    PREFIX_COMPLETE_MARKER,
                    QUERY_BINDING_START_MARKER,
                    QUERY_BINDING_COMPLETE_MARKER,
                    PRIVATE_START_MARKER,
                    PRIVATE_COMPLETE_MARKER,
                    FRI_PREPARE_START_MARKER,
                    FRI_PREPARE_COMPLETE_MARKER,
                    FRI_START_MARKER,
                    FRI_COMPLETE_MARKER,
                    CLAIMS_COMPLETE_MARKER,
                    COVECTOR_COMPLETE_MARKER,
                    RELATION_STRESS_START_MARKER,
                    RELATION_STRESS_COMPLETE_MARKER,
                ],
            "unexpected v5 composite CU marker sequence: {labels:?}"
        );
        let base_parse = marker_delta(markers[1].delta_from_previous, PREFIX_START_MARKER)?;
        let prefix = marker_delta(markers[2].delta_from_previous, PREFIX_COMPLETE_MARKER)?;
        let query = marker_delta(
            markers[4].delta_from_previous,
            QUERY_BINDING_COMPLETE_MARKER,
        )?;
        let private = marker_delta(markers[6].delta_from_previous, PRIVATE_COMPLETE_MARKER)?;
        let fri_prepare =
            marker_delta(markers[8].delta_from_previous, FRI_PREPARE_COMPLETE_MARKER)?;
        let fri = marker_delta(markers[10].delta_from_previous, FRI_COMPLETE_MARKER)?;
        let claims = marker_delta(markers[11].delta_from_previous, CLAIMS_COMPLETE_MARKER)?;
        let compact = marker_delta(markers[12].delta_from_previous, COVECTOR_COMPLETE_MARKER)?;
        let relation = marker_delta(
            markers[14].delta_from_previous,
            RELATION_STRESS_COMPLETE_MARKER,
        )?;
        Ok((
            base_parse,
            fri,
            Some(prefix),
            Some(query),
            Some(private),
            Some(fri_prepare),
            Some(claims),
            Some(compact),
            Some(relation),
        ))
    } else if relation_mode {
        ensure!(
            labels
                == [
                    PARSE_START_MARKER,
                    CLAIMS_COMPLETE_MARKER,
                    COVECTOR_COMPLETE_MARKER,
                    KERNEL_COMPLETE_MARKER,
                ],
            "unexpected v5 relation CU marker sequence: {labels:?}"
        );
        let claims = marker_delta(markers[1].delta_from_previous, CLAIMS_COMPLETE_MARKER)?;
        let covector = marker_delta(markers[2].delta_from_previous, COVECTOR_COMPLETE_MARKER)?;
        let relation = marker_delta(markers[3].delta_from_previous, KERNEL_COMPLETE_MARKER)?;
        Ok((
            claims,
            relation,
            None,
            None,
            None,
            None,
            Some(claims),
            Some(covector),
            Some(relation),
        ))
    } else {
        ensure!(
            labels
                == [
                    PARSE_START_MARKER,
                    KERNEL_START_MARKER,
                    KERNEL_COMPLETE_MARKER,
                ],
            "unexpected v5 layer-zero CU marker sequence: {labels:?}"
        );
        let preparation = marker_delta(markers[1].delta_from_previous, KERNEL_START_MARKER)?;
        let kernel = marker_delta(markers[2].delta_from_previous, KERNEL_COMPLETE_MARKER)?;
        Ok((
            preparation,
            kernel,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
        ))
    }
}

fn heap_high_water(logs: &[String]) -> Result<usize> {
    let values = logs
        .iter()
        .filter_map(|line| {
            line.find(COMPOSITE_HEAP_PREFIX).map(|offset| {
                line[offset + COMPOSITE_HEAP_PREFIX.len()..]
                    .trim()
                    .parse::<usize>()
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    ensure!(
        values.len() == 1,
        "expected one composite heap high-water log, got {values:?}"
    );
    Ok(values[0])
}

fn collect_mode(mode: Mode, simulations: &[StatelessSimulationResult]) -> Result<ModeMeasurement> {
    let mut totals = Vec::with_capacity(REPEATS);
    let mut parse_and_prep = Vec::with_capacity(REPEATS);
    let mut prefix_intervals = Vec::with_capacity(REPEATS);
    let mut query_intervals = Vec::with_capacity(REPEATS);
    let mut private_intervals = Vec::with_capacity(REPEATS);
    let mut fri_prepare_intervals = Vec::with_capacity(REPEATS);
    let mut kernels = Vec::with_capacity(REPEATS);
    let mut claim_intervals = Vec::with_capacity(REPEATS);
    let mut covector_intervals = Vec::with_capacity(REPEATS);
    let mut relation_intervals = Vec::with_capacity(REPEATS);
    let composite_mode = mode.id == V5_CU_PROBE_COMPOSITE_MODE;
    let relation_mode =
        (V5_CU_PROBE_RELATION3_MODE..=V5_CU_PROBE_RELATION4_COMPACT_MODE).contains(&mode.id);
    let mut heap_high_waters = Vec::with_capacity(REPEATS);
    for simulation in simulations {
        ensure!(
            simulation.logs.iter().any(|line| line.contains("success")),
            "{} transaction omitted success log",
            mode.name
        );
        totals.push(simulation.units);
        let (preparation, kernel, prefix, query, private, fri_prepare, claims, covector, relation) =
            marked_intervals(simulation, relation_mode, composite_mode)?;
        parse_and_prep.push(preparation);
        kernels.push(kernel);
        if let Some(value) = prefix {
            prefix_intervals.push(value);
        }
        if let Some(value) = query {
            query_intervals.push(value);
        }
        if let Some(value) = private {
            private_intervals.push(value);
        }
        if let Some(value) = fri_prepare {
            fri_prepare_intervals.push(value);
        }
        if let Some(value) = claims {
            claim_intervals.push(value);
        }
        if let Some(value) = covector {
            covector_intervals.push(value);
        }
        if let Some(value) = relation {
            relation_intervals.push(value);
        }
        if composite_mode {
            heap_high_waters.push(heap_high_water(&simulation.logs)?);
        }
    }
    let transaction_total_cu = one_value(&totals, &format!("{} total", mode.name))?;
    let marked_parse_and_power_prep_cu =
        one_value(&parse_and_prep, &format!("{} parse/prep", mode.name))?;
    let marked_hash_and_combine_kernel_cu = one_value(&kernels, &format!("{} kernel", mode.name))?;
    let marked_wire_prefix_verify_cu = composite_mode
        .then(|| one_value(&prefix_intervals, &format!("{} wire prefix", mode.name)))
        .transpose()?;
    let marked_query_binding_cu = composite_mode
        .then(|| one_value(&query_intervals, &format!("{} query binding", mode.name)))
        .transpose()?;
    let marked_private_opening_verify_cu = composite_mode
        .then(|| {
            one_value(
                &private_intervals,
                &format!("{} private openings", mode.name),
            )
        })
        .transpose()?;
    let marked_fri_claim_prepare_cu = composite_mode
        .then(|| {
            one_value(
                &fri_prepare_intervals,
                &format!("{} FRI claim preparation", mode.name),
            )
        })
        .transpose()?;
    let has_relation_intervals = relation_mode || composite_mode;
    let marked_claim_aggregation_cu = has_relation_intervals
        .then(|| one_value(&claim_intervals, &format!("{} claims", mode.name)))
        .transpose()?;
    let marked_covector_derivation_cu = has_relation_intervals
        .then(|| one_value(&covector_intervals, &format!("{} covector", mode.name)))
        .transpose()?;
    let marked_relation_fold_or_standalone_dot_cu = has_relation_intervals
        .then(|| one_value(&relation_intervals, &format!("{} relation", mode.name)))
        .transpose()?;
    let sbf_heap_high_water_bytes = composite_mode
        .then(|| {
            one_value(
                &heap_high_waters
                    .iter()
                    .map(|&value| value as u64)
                    .collect::<Vec<_>>(),
                &format!("{} heap", mode.name),
            )
            .map(|value| value as usize)
        })
        .transpose()?;
    let marked_total = marked_parse_and_power_prep_cu as i64
        + marked_wire_prefix_verify_cu.unwrap_or_default() as i64
        + marked_query_binding_cu.unwrap_or_default() as i64
        + marked_private_opening_verify_cu.unwrap_or_default() as i64
        + marked_fri_claim_prepare_cu.unwrap_or_default() as i64
        + marked_hash_and_combine_kernel_cu as i64
        + marked_covector_derivation_cu.unwrap_or_default() as i64
        + if composite_mode {
            marked_claim_aggregation_cu.unwrap_or_default() as i64
                + marked_relation_fold_or_standalone_dot_cu.unwrap_or_default() as i64
        } else {
            0
        };
    Ok(ModeMeasurement {
        mode: mode.id,
        name: mode.name.to_string(),
        description: mode.description.to_string(),
        transaction_total_cu,
        marked_parse_and_power_prep_cu,
        marked_wire_prefix_verify_cu,
        marked_query_binding_cu,
        marked_private_opening_verify_cu,
        marked_fri_claim_prepare_cu,
        marked_hash_and_combine_kernel_cu,
        marked_claim_aggregation_cu,
        marked_covector_derivation_cu,
        marked_relation_fold_or_standalone_dot_cu,
        transaction_total_minus_marked_deltas_cu: transaction_total_cu as i64 - marked_total,
        transaction_total_repeats: totals,
        marked_parse_and_power_prep_repeats: parse_and_prep,
        marked_wire_prefix_verify_repeats: prefix_intervals,
        marked_query_binding_repeats: query_intervals,
        marked_private_opening_verify_repeats: private_intervals,
        marked_fri_claim_prepare_repeats: fri_prepare_intervals,
        marked_hash_and_combine_kernel_repeats: kernels,
        marked_claim_aggregation_repeats: claim_intervals,
        marked_covector_derivation_repeats: covector_intervals,
        marked_relation_fold_or_standalone_dot_repeats: relation_intervals,
        sbf_heap_high_water_bytes,
        sbf_heap_high_water_repeats: heap_high_waters,
    })
}

#[allow(dead_code)]
fn run_legacy_probe(results_dir: &Path) -> Result<V5Layer0CuProbeOutcome> {
    let root = workspace_root()?;
    let account_data = runtime_account_data()?;
    ensure!(
        account_data.len() > V5_CU_PROBE_ACCOUNT_BYTES,
        "runtime account layout drift"
    );
    let (account_address, _) =
        Pubkey::find_program_address(&[b"v5-cu-probe-runtime-v3"], &aspis_verifier::id());

    // These controls establish only that adding/building the isolated probe
    // did not perturb this exact worktree's production SBF.
    let control_before = build_sbf(
        &root,
        "spend-production",
        "aspis_verifier_v5_cu_control_before",
    )?;
    let control_before_bytes = fs::read(&control_before)?;
    let probe_so = build_sbf(&root, "v5-cu-probe", "aspis_verifier_v5_cu_probe")?;
    let probe_bytes = fs::read(&probe_so)?;

    let mut instructions = Vec::with_capacity(REPEATS * MODE_COUNT);
    for _ in 0..REPEATS {
        for mode in MODES {
            instructions.push(probe_wire(mode.id, &account_data)?);
        }
    }
    let simulations = simulate_readonly_program_account_instructions(
        &probe_so,
        account_address,
        aspis_verifier::id(),
        &account_data,
        &instructions,
    )?;
    ensure!(
        simulations.len() == REPEATS * MODE_COUNT,
        "probe simulation count drift"
    );

    let mut measurements = Vec::with_capacity(MODE_COUNT);
    for (mode_index, mode) in MODES.into_iter().enumerate() {
        let mode_simulations = (0..REPEATS)
            .map(|repeat| &simulations[repeat * MODE_COUNT + mode_index])
            .collect::<Vec<_>>();
        // Collecting references keeps the original interleaving. Clone only
        // the narrow public result fields needed by the common collector.
        let owned = mode_simulations
            .into_iter()
            .map(|simulation| StatelessSimulationResult {
                units: simulation.units,
                logs: simulation.logs.clone(),
            })
            .collect::<Vec<_>>();
        measurements.push(collect_mode(mode, &owned)?);
    }

    let control_after = build_sbf(
        &root,
        "spend-production",
        "aspis_verifier_v5_cu_control_after",
    )?;
    let control_after_bytes = fs::read(&control_after)?;
    let control_identical = control_before_bytes == control_after_bytes;
    ensure!(
        control_identical,
        "production control SBF changed after the opt-in probe build"
    );

    let production = &measurements[0];
    let generic26 = &measurements[1];
    let generic16_nonfused = &measurements[2];
    let generic16_fused = &measurements[3];
    let generic26_fused = &measurements[4];
    let relation3 = &measurements[5];
    let relation4_dense = &measurements[6];
    let relation4_standalone = &measurements[7];
    let relation4_compact = &measurements[8];
    let composite = &measurements[9];
    let generic_nonfused_width_saving = generic26.marked_hash_and_combine_kernel_cu as i64
        - generic16_nonfused.marked_hash_and_combine_kernel_cu as i64;
    let generic_fused_width_saving = generic26_fused.marked_hash_and_combine_kernel_cu as i64
        - generic16_fused.marked_hash_and_combine_kernel_cu as i64;
    let generic26_fusion_saving = generic26.marked_hash_and_combine_kernel_cu as i64
        - generic26_fused.marked_hash_and_combine_kernel_cu as i64;
    let generic16_fusion_saving = generic16_nonfused.marked_hash_and_combine_kernel_cu as i64
        - generic16_fused.marked_hash_and_combine_kernel_cu as i64;
    // Modes 4→3 and 2→3 traverse the same three-comparison C1-record
    // selection depth. Modes 1→2 and 1→4 do not: mode 1 exits one comparison
    // earlier. Retain every raw delta, but expose the matched-depth signals
    // separately from the observed selection asymmetry.
    let nonfused_width_mode_selection_asymmetry =
        generic_fused_width_saving - generic_nonfused_width_saving;
    let generic26_fusion_mode_selection_asymmetry =
        generic16_fusion_saving - generic26_fusion_saving;
    let generic_total_saving = generic26.marked_hash_and_combine_kernel_cu as i64
        - generic16_fused.marked_hash_and_combine_kernel_cu as i64;
    let production_to_candidate_delta = production.marked_hash_and_combine_kernel_cu as i64
        - generic16_fused.marked_hash_and_combine_kernel_cu as i64;
    let production_to_candidate_parse_saving = production.marked_parse_and_power_prep_cu as i64
        - generic16_fused.marked_parse_and_power_prep_cu as i64;
    let production_to_candidate_marked_total =
        production_to_candidate_delta + production_to_candidate_parse_saving;
    let production_to_candidate_transaction_delta =
        production.transaction_total_cu as i64 - generic16_fused.transaction_total_cu as i64;
    let production_to_generic26_fused_delta = production.marked_hash_and_combine_kernel_cu as i64
        - generic26_fused.marked_hash_and_combine_kernel_cu as i64;
    let relation_claims = |measurement: &ModeMeasurement| {
        measurement
            .marked_claim_aggregation_cu
            .expect("relation mode records its claim interval") as i64
    };
    let relation_covector = |measurement: &ModeMeasurement| {
        measurement
            .marked_covector_derivation_cu
            .expect("relation mode records its covector interval") as i64
    };
    let relation_fold = |measurement: &ModeMeasurement| {
        measurement
            .marked_relation_fold_or_standalone_dot_cu
            .expect("relation mode records its terminal interval") as i64
    };
    let component_b_fourth_claim_delta =
        relation_claims(relation4_dense) - relation_claims(relation3);
    let component_b_covector_delta =
        relation_covector(relation4_dense) - relation_covector(relation3);
    let component_b_shared_fold_delta = relation_fold(relation4_dense) - relation_fold(relation3);
    let component_b_total_delta =
        component_b_fourth_claim_delta + component_b_covector_delta + component_b_shared_fold_delta;
    let component_b_transaction_delta =
        relation4_dense.transaction_total_cu as i64 - relation3.transaction_total_cu as i64;
    let rejected_standalone_dot_delta =
        relation_fold(relation4_standalone) - relation_fold(relation3);
    let rejected_standalone_total_delta = relation_claims(relation4_standalone)
        - relation_claims(relation3)
        + relation_covector(relation4_standalone)
        - relation_covector(relation3)
        + rejected_standalone_dot_delta;
    let compact_component_b_fourth_claim_delta =
        relation_claims(relation4_compact) - relation_claims(relation3);
    let compact_component_b_derivation_delta =
        relation_covector(relation4_compact) - relation_covector(relation3);
    let compact_component_b_fold_delta =
        relation_fold(relation4_compact) - relation_fold(relation3);
    let compact_component_b_total_delta = compact_component_b_fourth_claim_delta
        + compact_component_b_derivation_delta
        + compact_component_b_fold_delta;
    let compact_component_b_transaction_delta =
        relation4_compact.transaction_total_cu as i64 - relation3.transaction_total_cu as i64;
    let compact_component_b_forecast_remaining =
        PROVISIONAL_FORECAST_ENVELOPE_CU - compact_component_b_total_delta;
    let composite_claims = composite.marked_claim_aggregation_cu.unwrap();
    let composite_setup = composite.marked_covector_derivation_cu.unwrap();
    let composite_relation = composite.marked_relation_fold_or_standalone_dot_cu.unwrap();
    let composite_wire_prefix = composite.marked_wire_prefix_verify_cu.unwrap();
    let composite_private_openings = composite.marked_private_opening_verify_cu.unwrap();
    let composite_marked_total = composite.marked_parse_and_power_prep_cu
        + composite_wire_prefix
        + composite_private_openings
        + composite.marked_hash_and_combine_kernel_cu
        + composite_claims
        + composite_setup
        + composite_relation;
    let isolated_marked_total = generic16_fused.marked_parse_and_power_prep_cu
        + generic16_fused.marked_hash_and_combine_kernel_cu
        + relation_claims(relation4_compact) as u64
        + relation_covector(relation4_compact) as u64
        + relation_fold(relation4_compact) as u64;
    let isolated_transaction_total =
        generic16_fused.transaction_total_cu + relation4_compact.transaction_total_cu;
    let composite_heap_high_water = composite.sbf_heap_high_water_bytes.unwrap();
    const DEFAULT_SBF_HEAP_BYTES: usize = 32 * 1024;
    ensure!(
        generic_nonfused_width_saving > 0 && generic_fused_width_saving > 0,
        "generic width change did not save CU in both helper strategies"
    );
    ensure!(
        generic26_fusion_saving > 0 && generic16_fusion_saving > 0,
        "generic helper fusion did not save CU at both widths"
    );
    ensure!(
        generic_total_saving > 0,
        "generic candidate did not save CU"
    );
    ensure!(
        component_b_fourth_claim_delta > 0
            && component_b_covector_delta > 0
            && component_b_shared_fold_delta > 0,
        "component-B dense-opening intervals did not each add CU"
    );
    ensure!(
        compact_component_b_fourth_claim_delta > 0
            && compact_component_b_derivation_delta > 0
            && compact_component_b_fold_delta > 0,
        "compact component-B intervals did not each add CU"
    );
    ensure!(
        composite_heap_high_water < DEFAULT_SBF_HEAP_BYTES,
        "composite exhausted the default SBF heap"
    );

    let summary = V5Layer0CuProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- v5-cu-probe".to_string(),
        scope: "ten modes in one SBF, adding one composite invocation that parses and algebraically verifies the exact fail-closed 19-lane/76-claim v5 prefix, authenticates the canonical five-section private-opening suffix at widths [256,192,64,64,64] and depths [17,17,15,13,11], byte-binds its q18 C1/C2 records to the layer-zero inputs, executes the width-16 layer-zero hash/recombination kernel, and runs the compact degree-27 Component-B claim/setup/four-fold/final-dot path; the later FRI algebra and final production v5 dispatcher remain absent".to_string(),
        full_v5_measured: false,
        authority_note: "This ten-mode build uses the deployed atomic-v3 copy-inactive mask for every relation mode. Adding a mode or changing that mask changes compiled control flow and code layout, so only comparisons recorded together in this artifact are authoritative.".to_string(),
        measurement_method: "The composite mode runs in one SBF invocation with one borrowed runtime account and one 18-output allocation. Its seven measured workloads are base-account parse plus power preparation; exact 6,423-byte v5 prefix verification; five canonical salted-Merkle opening verifications over the real encoder/fold artefact; width-16 q18 layer-zero; compact relation/four-claim preparation; exact compact-state setup; and four dual folds plus final dot. The authenticated C1/C2 opening records are byte-equal to the records consumed by layer zero. The common sink follows the last marker. Every mode is submitted three times and every reported phase, total, and heap value must be identical.".to_string(),
        runtime_input_account: account_address.to_string(),
        runtime_input_account_bytes: account_data.len(),
        runtime_input_sha256: hex(&Sha256::digest(&account_data)),
        query_count: V5_CU_PROBE_QUERY_COUNT,
        production_c1_columns: V5_CU_PROBE_PRODUCTION_C1_COLUMNS,
        candidate_c1_columns: V5_CU_PROBE_CANDIDATE_C1_COLUMNS,
        shared_c2_columns: V5_CU_PROBE_C2_COLUMNS,
        production_c1_record_bytes: V5_CU_PROBE_PRODUCTION_C1_RECORD_BYTES,
        candidate_c1_record_bytes: V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES,
        shared_c2_record_bytes: V5_CU_PROBE_C2_RECORD_BYTES,
        marked_generic_nonfused_width_saving_cu: generic_nonfused_width_saving,
        marked_generic_fused_width_saving_cu: generic_fused_width_saving,
        marked_generic26_fusion_saving_cu: generic26_fusion_saving,
        marked_generic16_fusion_saving_cu: generic16_fusion_saving,
        clean_forecast_fused_width_saving_cu: generic_fused_width_saving,
        clean_forecast_width16_fusion_saving_cu: generic16_fusion_saving,
        marked_generic_nonfused_width_saving_mode_selection_asymmetry_cu:
            nonfused_width_mode_selection_asymmetry,
        marked_generic26_fusion_saving_mode_selection_asymmetry_cu:
            generic26_fusion_mode_selection_asymmetry,
        production26_uses_current_fused_three_product_helper: true,
        production26_to_generic16_fused_is_old_v4_to_v5_comparison: false,
        comparison_caveat: format!(
            "The clean forecast signals use matched three-comparison mode-selection paths: generic26_fused to generic16_fused for width, and generic16_nonfused to generic16_fused for fusion. The raw generic non-fused width and width-26 fusion deltas each contain an observed {nonfused_width_mode_selection_asymmetry}-CU mode-selection asymmetry. Production26 already uses the current fused three-product helper, so its delta to generic16_fused is not an old-v4-to-v5 comparison."
        ),
        marked_generic26_nonfused_to_generic16_fused_saving_cu: generic_total_saving,
        marked_production26_to_generic26_fused_delta_cu: production_to_generic26_fused_delta,
        marked_production26_to_generic16_fused_delta_cu: production_to_candidate_delta,
        marked_production26_to_generic16_fused_parse_and_power_saving_cu:
            production_to_candidate_parse_saving,
        marked_production26_to_generic16_fused_parse_plus_kernel_saving_cu:
            production_to_candidate_marked_total,
        transaction_production26_to_generic16_fused_delta_cu:
            production_to_candidate_transaction_delta,
        component_b_lane_count: V5_CU_PROBE_RELATION_LANES,
        component_b_existing_claims_per_lane: V5_CU_PROBE_RELATION_POINTS,
        component_b_candidate_claims_per_lane: V5_CU_PROBE_RELATION_CLAIMS_PER_LANE,
        component_b_dense_rows: V5_CU_PROBE_RELATION_DENSE_VALUES,
        component_b_nonzero_state_weights: V5_CU_PROBE_B_MASK_COORDINATES,
        component_b_zero_pad_weights: V5_CU_PROBE_B_PAD_COORDINATES,
        component_b_shared_existing_pcs_pass: true,
        component_b_functional_batch_scales: "[1, kappa, kappa^2, kappa^3]".to_string(),
        component_b_functional_batch_sz_degree: 3,
        component_b_soundness_ledger_update_required: true,
        component_b_default_heap_observation: "The retained literal fixed-array control exceeded the 4 KiB SBF stack and was moved to an algebraically identical heap vector. With the ordinary 2.3 KiB layer-zero sink allocated after its Dense folds, the default SBF heap then exhausted; relation modes therefore use a fixed 16-byte post-marker sink. The compact candidate itself requests no dynamic heap and its 540-byte fixed state builds below the SBF stack limit, but an integrated verifier still needs a lifetime audit with the production parser and sink.".to_string(),
        marked_component_b_fourth_claim_delta_cu: component_b_fourth_claim_delta,
        marked_component_b_covector_derivation_delta_cu: component_b_covector_delta,
        marked_component_b_shared_fold_delta_cu: component_b_shared_fold_delta,
        marked_component_b_total_delta_cu: component_b_total_delta,
        transaction_component_b_total_delta_cu: component_b_transaction_delta,
        rejected_standalone_dot_marked_delta_cu: rejected_standalone_dot_delta,
        rejected_standalone_total_delta_cu: rejected_standalone_total_delta,
        compact_component_b_block_selectors: V5_CU_PROBE_B_BLOCK_SELECTORS,
        compact_component_b_initial_state_row: V5_CU_PROBE_B_INITIAL_STATE_ROW,
        compact_component_b_dependent_pivot_row: V5_CU_PROBE_B_DEPENDENT_PIVOT_ROW,
        compact_component_b_degree: 27,
        compact_component_b_zero_tail_weights: 10 * 4,
        compact_component_b_state_bytes: V5_CU_PROBE_B_COMPACT_STATE_BYTES,
        compact_component_b_dynamic_heap_bytes: V5_CU_PROBE_B_COMPACT_DYNAMIC_HEAP_BYTES,
        compact_component_b_dense_payload_avoided_bytes:
            V5_CU_PROBE_RELATION_DENSE_VALUES * core::mem::size_of::<QM31>(),
        marked_compact_component_b_fourth_claim_delta_cu:
            compact_component_b_fourth_claim_delta,
        marked_compact_component_b_derivation_delta_cu:
            compact_component_b_derivation_delta,
        marked_compact_component_b_fold_delta_cu: compact_component_b_fold_delta,
        marked_compact_component_b_total_delta_cu: compact_component_b_total_delta,
        transaction_compact_component_b_total_delta_cu:
            compact_component_b_transaction_delta,
        provisional_forecast_envelope_cu: PROVISIONAL_FORECAST_ENVELOPE_CU,
        compact_component_b_fits_provisional_forecast_envelope:
            compact_component_b_forecast_remaining >= 0,
        provisional_forecast_envelope_after_compact_component_b_cu:
            compact_component_b_forecast_remaining,
        component_b_binding_caveat: "The composite path absorbs all 76 point-major claims and the terminal tuple before deriving kappa, then batches four functionals as [1, kappa, kappa^2, kappa^3]. Eta and all ten round challenges are likewise derived, never proof-carried. The separate five-section suffix now authenticates the q18 C1/C2 records and later-tree leaves, but the prefix's lane-digest table and OOD claims are still synthetic and are not yet checked by the later FRI algebra. Production verification therefore remains fail-closed at that seam, and the degree-three soundness ledger update remains mandatory.".to_string(),
        composite_uses_atomic_v3_inactive_relation: true,
        composite_transaction_total_cu: composite.transaction_total_cu,
        composite_marked_parse_and_allocation_cu: composite.marked_parse_and_power_prep_cu,
        composite_marked_wire_prefix_verify_cu: composite_wire_prefix,
        composite_marked_query_binding_cu: composite.marked_query_binding_cu.unwrap(),
        composite_marked_private_opening_verify_cu: composite_private_openings,
        composite_marked_fri_claim_prepare_cu: composite.marked_fri_claim_prepare_cu.unwrap(),
        composite_marked_full_fri_cu: composite.marked_hash_and_combine_kernel_cu,
        composite_marked_claim_aggregation_cu: composite_claims,
        composite_marked_compact_setup_cu: composite_setup,
        composite_marked_relation_folds_and_dot_cu: composite_relation,
        composite_marked_total_cu: composite_marked_total,
        isolated_marked_total_cu: isolated_marked_total,
        composite_marked_overhead_vs_isolated_cu:
            composite_marked_total as i64 - isolated_marked_total as i64,
        isolated_transaction_total_cu: isolated_transaction_total,
        composite_transaction_saving_vs_two_isolated_cu:
            isolated_transaction_total as i64 - composite.transaction_total_cu as i64,
        default_sbf_heap_bytes: DEFAULT_SBF_HEAP_BYTES,
        composite_heap_high_water_bytes: composite_heap_high_water,
        composite_default_heap_headroom_bytes:
            DEFAULT_SBF_HEAP_BYTES - composite_heap_high_water,
        composite_default_heap_viable_three_of_three: true,
        historical_tag65_projection_made: false,
        production_control_sbf_bytes: control_before_bytes.len(),
        production_control_sbf_sha256: hex(&Sha256::digest(&control_before_bytes)),
        production_control_rebuild_byte_identical: control_identical,
        probe_sbf_bytes: probe_bytes.len(),
        probe_sbf_sha256: hex(&Sha256::digest(&probe_bytes)),
        unmeasured_obligations: vec![
            "later FRI algebra, OOD equations, final-polynomial checks, and production transcript integration after the now-measured five-section Merkle authentication".to_string(),
            "integration of the measured derived eta/r_i/kappa transcript order with the production circle-PCS transcript".to_string(),
            "kernel-checked correspondence between the Rust 1024-row mapping and the Lean terminal functional".to_string(),
            "soundness-ledger update for degree-three [1, kappa, kappa^2, kappa^3] functional batching".to_string(),
            "integrated stack and heap audit with the production proof parser; this probe measures only its own shared output/relation lifetimes".to_string(),
            "component-C complete-view masking, transcript binding, and verifier logic".to_string(),
            "an exact tag65 baseline and candidate delta measured in one integrated same-worktree SBF".to_string(),
        ],
        conclusion: format!(
            "The v5 CU-stress composite invocation consumes {} CU total. Its seven measured workloads consume {}, {}, {}, {}, {}, {}, and {} CU, for {} marked CU. The third number is exact authentication of the five-section private-opening suffix, whose C1/C2 records feed layer zero byte-for-byte. The default 32768-byte SBF heap succeeds three of three times at a measured {}-byte high-water mark. Later FRI algebra and the production v5 dispatcher remain unmeasured, so this is not yet a full-v5 fit claim.",
            composite.transaction_total_cu,
            composite.marked_parse_and_power_prep_cu,
            composite_wire_prefix,
            composite_private_openings,
            composite.marked_hash_and_combine_kernel_cu,
            composite_claims,
            composite_setup,
            composite_relation,
            composite_marked_total,
            composite_heap_high_water,
        ),
        modes: measurements,
    };

    let production_kernel_cu = summary.modes[0].marked_hash_and_combine_kernel_cu;
    let candidate_kernel_cu = summary.modes[3].marked_hash_and_combine_kernel_cu;
    fs::create_dir_all(results_dir)?;
    let path = results_dir.join("v5_composite_width16_component_b_cu_probe.json");
    fs::write(
        &path,
        format!("{}\n", serde_json::to_string_pretty(&summary)?),
    )?;
    Ok(V5Layer0CuProbeOutcome {
        path,
        production_kernel_cu,
        candidate_kernel_cu,
        production_to_candidate_delta_cu: production_to_candidate_delta,
        generic_fused_width_saving_cu: generic_fused_width_saving,
        generic16_fusion_saving_cu: generic16_fusion_saving,
    })
}

pub fn run(results_dir: &Path) -> Result<V5Layer0CuProbeOutcome> {
    let root = workspace_root()?;
    run_real_full_transaction(results_dir, &root)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Run the honest tag-67 devnet-shaped transaction with no preloaded
    /// nullifier marker. Every repetition must therefore complete the marker
    /// creation CPI. JSON is written only to a caller-owned directory.
    #[test]
    #[ignore = "expensive current tag-67 SBF/CU measurement; set V5_CU_RESULTS_DIR"]
    fn v5_full_transaction_current_good_gate_cu_measurement() {
        let results_dir = std::env::var_os("V5_CU_RESULTS_DIR")
            .map(PathBuf::from)
            .expect("V5_CU_RESULTS_DIR must name an explicit temporary directory");
        let root = workspace_root().expect("resolve workspace root");
        let outcome = run_real_full_transaction(&results_dir, &root)
            .expect("measure missing-marker tag-67 GoodA/GoodB transaction");
        println!(
            "v5-missing-marker-full-cu total={} path={}",
            outcome.candidate_kernel_cu,
            outcome.path.display()
        );
    }

    /// Preserve the former preloaded program-owned zero-marker measurement as
    /// an explicit control rather than conflating it with the deployment path.
    #[test]
    #[ignore = "expensive preloaded-marker tag-67 SBF/CU control; set V5_CU_RESULTS_DIR"]
    fn v5_full_transaction_preloaded_marker_control_cu_measurement() {
        let results_dir = std::env::var_os("V5_CU_RESULTS_DIR")
            .map(PathBuf::from)
            .expect("V5_CU_RESULTS_DIR must name an explicit temporary directory");
        let root = workspace_root().expect("resolve workspace root");
        let outcome = run_real_full_transaction_preloaded_marker_control(&results_dir, &root)
            .expect("measure preloaded-marker tag-67 control transaction");
        println!(
            "v5-preloaded-marker-control-cu total={} path={}",
            outcome.candidate_kernel_cu,
            outcome.path.display()
        );
    }

    /// Build and execute all three selected-Good branches against one pinned
    /// SBF with the nullifier marker absent. Any branch other than the
    /// artifact's runtime leastGood branch is an explicitly test-only nonleast
    /// prover fixture. Each selector repeats the creation path three times.
    #[test]
    #[ignore = "expensive all-selector tag-67 SBF/CU measurement; set V5_CU_RESULTS_DIR"]
    fn v5_full_transaction_all_selected_good_branches_cu_measurement() {
        let results_dir = std::env::var_os("V5_CU_RESULTS_DIR")
            .map(PathBuf::from)
            .expect("V5_CU_RESULTS_DIR must name an explicit temporary directory");
        let root = workspace_root().expect("resolve workspace root");
        let outcomes = run_real_full_transactions_all_selectors(&results_dir, &root)
            .expect("measure all three selected-Good tag-67 branches");
        assert_eq!(outcomes.len(), 3);
        for (selector, outcome) in outcomes.iter().enumerate() {
            println!(
                "v5-selected-good-full-cu selector={selector} total={} path={}",
                outcome.candidate_kernel_cu,
                outcome.path.display()
            );
        }
    }

    /// All-selector counterpart of the former preloaded-marker control. This
    /// remains available for an apples-to-apples CU delta against the missing
    /// marker path, but is not the deployment-shaped measurement.
    #[test]
    #[ignore = "expensive all-selector preloaded-marker SBF/CU control; set V5_CU_RESULTS_DIR"]
    fn v5_full_transaction_all_selected_good_branches_preloaded_marker_control_cu_measurement() {
        let results_dir = std::env::var_os("V5_CU_RESULTS_DIR")
            .map(PathBuf::from)
            .expect("V5_CU_RESULTS_DIR must name an explicit temporary directory");
        let root = workspace_root().expect("resolve workspace root");
        let outcomes =
            run_real_full_transactions_all_selectors_preloaded_marker_control(&results_dir, &root)
                .expect("measure all three selected-Good preloaded-marker controls");
        assert_eq!(outcomes.len(), 3);
        for (selector, outcome) in outcomes.iter().enumerate() {
            println!(
                "v5-selected-good-preloaded-control selector={selector} total={} path={}",
                outcome.candidate_kernel_cu,
                outcome.path.display()
            );
        }
    }

    /// Regenerate and cache one selector independently, then replay it three
    /// times through the missing-marker/System Program CPI path against the
    /// explicitly pinned prebuilt SBF.
    #[test]
    #[ignore = "expensive single-selector tag-67 SBF/CU measurement; set V5_CU_RESULTS_DIR and V5_CU_SINGLE_SELECTOR"]
    fn v5_full_transaction_single_selected_good_branch_cu_measurement() {
        let results_dir = std::env::var_os("V5_CU_RESULTS_DIR")
            .map(PathBuf::from)
            .expect("V5_CU_RESULTS_DIR must name an explicit cache directory");
        let selector = std::env::var("V5_CU_SINGLE_SELECTOR")
            .expect("V5_CU_SINGLE_SELECTOR must be 0, 1, or 2")
            .parse::<u8>()
            .expect("V5_CU_SINGLE_SELECTOR must parse as u8");
        let root = workspace_root().expect("resolve workspace root");
        let outcome = run_real_full_transaction_single_selector(&results_dir, &root, selector)
            .expect("measure one independently regenerated selected-Good branch");
        println!(
            "v5-single-selected-good-full-cu selector={selector} total={} path={}",
            outcome.candidate_kernel_cu,
            outcome.path.display()
        );
    }

    /// Fast replay for one retained selector-specific proof. This performs no
    /// proof generation, selector reconstruction, or SBF build.
    #[test]
    #[ignore = "cached selector replay; set V5_CU_FROZEN_DIR, V5_CU_SINGLE_SELECTOR, and V5_CU_PREBUILT_SBF_SHA256"]
    fn v5_cached_selected_good_branch_missing_marker_cu_measurement() {
        let frozen_dir = std::env::var_os("V5_CU_FROZEN_DIR")
            .map(PathBuf::from)
            .expect("V5_CU_FROZEN_DIR must name the frozen artifact directory");
        let selector = std::env::var("V5_CU_SINGLE_SELECTOR")
            .expect("V5_CU_SINGLE_SELECTOR must be 1 or 2")
            .parse::<u8>()
            .expect("V5_CU_SINGLE_SELECTOR must parse as u8");
        let outcome = replay_cached_selected_good_branch(&frozen_dir, selector)
            .expect("replay retained selected-Good proof against frozen SBF");
        println!(
            "v5-cached-selected-good-full-cu selector={selector} total={} path={}",
            outcome.candidate_kernel_cu,
            outcome.path.display()
        );
    }

    #[test]
    fn v5_devnet_marker_mode_and_system_cpi_evidence_are_explicit() {
        assert_eq!(REPEATS, 3);
        assert_eq!(
            V5_DEVNET_PATH_MARKER_MODE,
            V5NullifierMarkerFixtureMode::MissingCreateCpi
        );
        assert!(!V5_DEVNET_PATH_MARKER_MODE.preloads_marker());
        assert!(V5_DEVNET_PATH_MARKER_MODE.requires_system_program_cpi());
        assert_eq!(
            V5_DEVNET_PATH_MARKER_MODE.simulation_helper(),
            "spend_measure::simulate_atomic_program_account_instructions_with_absent_marker"
        );
        assert_eq!(
            V5_PRELOADED_MARKER_CONTROL_MODE,
            V5NullifierMarkerFixtureMode::PreloadedProgramOwnedControl
        );
        assert!(V5_PRELOADED_MARKER_CONTROL_MODE.preloads_marker());
        assert!(!V5_PRELOADED_MARKER_CONTROL_MODE.requires_system_program_cpi());
        assert_eq!(
            V5_PRELOADED_MARKER_CONTROL_MODE.simulation_helper(),
            "spend_measure::simulate_atomic_program_account_instructions"
        );

        let system_program = Pubkey::default();
        let completed_cpi = vec![
            format!("Program {} invoke [2]", aspis_verifier::id()),
            format!("Program {system_program} invoke [3]"),
            format!("Program {system_program} success"),
            format!("Program {} success", aspis_verifier::id()),
        ];
        assert_eq!(
            completed_system_program_cpi_log_evidence(&completed_cpi),
            Some(vec![
                format!("Program {system_program} invoke [3]"),
                format!("Program {system_program} success"),
            ])
        );
        assert!(completed_system_program_cpi_log_evidence(&completed_cpi[..2]).is_none());
        assert!(completed_system_program_cpi_log_evidence(&[
            format!("Program {} invoke [1]", aspis_verifier::id()),
            format!("Program {} success", aspis_verifier::id()),
        ])
        .is_none());
    }

    fn frozen_hex32(value: &str) -> [u8; 32] {
        assert_eq!(value.len(), 64, "frozen hex32 length");
        let mut output = [0u8; 32];
        for (index, byte) in output.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
                .expect("frozen hex32 digit");
        }
        output
    }

    fn private_topology_parent_hashes(queries: [u32; 18]) -> ([usize; 5], [usize; 5]) {
        let mut sorted = queries;
        sorted.sort_unstable();
        let specifications = [(17u32, 0u32), (17, 0), (15, 2), (13, 4), (11, 6)];
        let mut parent_hashes = [0usize; 5];
        let mut frontier_nodes = [0usize; 5];
        for (section, (depth, shift)) in specifications.into_iter().enumerate() {
            let mut level = sorted
                .into_iter()
                .map(|query| query >> shift)
                .collect::<Vec<_>>();
            level.dedup();
            for _ in 0..depth / 2 {
                let previous = level.len();
                for value in &mut level {
                    *value >>= 2;
                }
                level.dedup();
                parent_hashes[section] += level.len();
                frontier_nodes[section] += 4 * level.len() - previous;
            }
            // Every odd-depth private tree executes exactly one binary-cap
            // parent hash. A singleton top level also consumes one frontier
            // sibling; two top nodes consume none.
            parent_hashes[section] += 1;
            if level.len() == 1 {
                frontier_nodes[section] += 1;
            }
        }
        (parent_hashes, frontier_nodes)
    }

    #[test]
    fn v5_universal_accepted_topology_cu_policy_is_conservative() {
        const FROZEN_QUERIES: [u32; 18] = [
            50_532, 22_083, 130_755, 96_325, 64_748, 111_639, 62_701, 121_059, 10_797, 8_586,
            122_389, 28_732, 60_839, 45_002, 58_911, 23_292, 45_221, 104_967,
        ];
        const MAX_PARENT_HASHES: [usize; 5] = [119, 119, 101, 83, 65];
        const MAX_FRONTIER_NODES: [usize; 5] = [338, 338, 284, 230, 176];
        const FROZEN_MISSING_MARKER_CU: u64 = 1_331_212;
        const MAX_EXTRA_PARENT_HASHES: u64 = 30;
        // Runtime 2.3.13 charges 149 CU for the 129-byte SHA-256 syscall.
        // 512 retains 363 CU for topology iteration and four fixed 32-byte
        // child copies. It also exceeds the largest observed all-in delta,
        // 300 CU per parent, across the three selector fixtures.
        const CONSERVATIVE_CU_PER_EXTRA_PARENT: u64 = 512;
        // Accepted matrices are nonsingular. Elimination updates are fixed;
        // only pivot search and row swapping vary. Relative to the mandatory
        // one pivot check per column, the maxima are 66 extra M31 checks and
        // six extra QM31 checks (24 limb comparisons), plus at most 208 u32
        // word swaps. These paths contain no cryptographic syscall. 4096 CU
        // is over four ordinary SBF instructions per bounded word operation.
        const GOOD_GATE_VARIABLE_CU: u64 = 4_096;
        const TRANSACTION_LIMIT_CU: u64 = 1_400_000;

        let (frozen_hashes, frozen_frontier) = private_topology_parent_hashes(FROZEN_QUERIES);
        assert_eq!(frozen_hashes, [113, 113, 95, 77, 59]);
        assert_eq!(frozen_frontier, [320, 320, 266, 212, 158]);
        assert_eq!(frozen_hashes.into_iter().sum::<usize>(), 457);
        assert_eq!(MAX_PARENT_HASHES.into_iter().sum::<usize>(), 487);
        assert_eq!(MAX_FRONTIER_NODES.into_iter().sum::<usize>(), 1_366);
        assert_eq!(487 - 457, MAX_EXTRA_PARENT_HASHES as usize);

        let universal_cu = FROZEN_MISSING_MARKER_CU
            + MAX_EXTRA_PARENT_HASHES * CONSERVATIVE_CU_PER_EXTRA_PARENT
            + GOOD_GATE_VARIABLE_CU;
        assert_eq!(universal_cu, 1_350_668);
        assert_eq!(TRANSACTION_LIMIT_CU - universal_cu, 49_332);
    }

    /// Replay the checked-in runtime proof against the checked-in tag-67 SBF.
    /// `V5_CU_FROZEN_MARKER_MODE=present` is the program-owned zero-marker
    /// control; `missing` exercises the real System Program create-account CPI.
    /// Neither mode performs proof generation, work mining, or an SBF build.
    #[test]
    #[ignore = "frozen-artifact local-validator control; set V5_CU_FROZEN_DIR"]
    fn v5_frozen_artifact_marker_mode_cu_measurement() {
        let frozen_dir = std::env::var_os("V5_CU_FROZEN_DIR")
            .map(PathBuf::from)
            .expect("V5_CU_FROZEN_DIR must name the frozen artifact directory");
        let probe_so = frozen_dir.join("aspis_verifier_v5_tag67.so");
        let expected_sbf = std::env::var("V5_CU_PREBUILT_SBF_SHA256")
            .expect("V5_CU_PREBUILT_SBF_SHA256 must pin the frozen SBF");
        assert_eq!(
            hex(&Sha256::digest(
                fs::read(&probe_so).expect("read frozen SBF")
            )),
            expected_sbf
        );

        let proof_body = fs::read(frozen_dir.join("v5_runtime_proof.bin"))
            .expect("read frozen runtime proof body");
        let frozen_queries = v5_complete_queries(aspis_prover::HOST_HASH, &proof_body)
            .expect("derive frozen runtime proof queries");
        let sealed_proof = finalized_proof_account_data(&proof_body).expect("seal frozen proof");
        let statement_json: serde_json::Value = serde_json::from_slice(
            &fs::read(frozen_dir.join("v5_runtime_statement.json"))
                .expect("read frozen runtime statement"),
        )
        .expect("decode frozen runtime statement JSON");
        let text32 = |field: &str| {
            frozen_hex32(
                statement_json[field]
                    .as_str()
                    .unwrap_or_else(|| panic!("missing frozen statement field {field}")),
            )
        };
        let statement = AtomicPaymentStatementV4 {
            pool: text32("pool_hex"),
            sequence: statement_json["sequence"]
                .as_u64()
                .expect("frozen sequence"),
            spend: SpendPublic {
                anchor: aspis_statement::decode_digest_canonical(&text32("current_anchor_hex"))
                    .expect("canonical frozen anchor"),
                nullifier: aspis_statement::decode_digest_canonical(&text32("nullifier_hex"))
                    .expect("canonical frozen nullifier"),
                output_commitment: aspis_statement::decode_digest_canonical(&text32(
                    "output_commitment_hex",
                ))
                .expect("canonical frozen output commitment"),
                asset_id: M31(statement_json["asset_id"]
                    .as_u64()
                    .expect("frozen asset id") as u32),
                fee: statement_json["fee"].as_u64().expect("frozen fee") as u32,
            },
            output_anchor: aspis_statement::decode_digest_canonical(&text32("output_anchor_hex"))
                .expect("canonical frozen output anchor"),
            deployment_domain: text32("deployment_domain_hex"),
        };
        let pool_address = Pubkey::new_from_array(statement.pool);
        let public_nullifier = aspis_statement::encode_digest_canonical(&statement.spend.nullifier);
        let (marker_address, _) =
            atomic_nullifier_address(&aspis_verifier::id(), &public_nullifier);
        let (proof_address, _) =
            Pubkey::find_program_address(&[b"v5-frozen-replay-proof-v1"], &aspis_verifier::id());
        let mut pool_data = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV2 {
            sequence: statement.sequence,
            anchor: aspis_statement::encode_digest_canonical(&statement.spend.anchor),
            deployment_domain: statement.deployment_domain,
        }
        .encode(&mut pool_data)
        .expect("encode frozen pool");
        let marker_data = [0u8; ATOMIC_NULLIFIER_MARKER_LEN];
        let instructions = vec![full_v5_transaction_wire(&statement); REPEATS];
        let marker_mode = std::env::var("V5_CU_FROZEN_MARKER_MODE")
            .expect("V5_CU_FROZEN_MARKER_MODE must be `present` or `missing`");
        let simulations = match marker_mode.as_str() {
            "present" => simulate_atomic_program_account_instructions(
                &probe_so,
                proof_address,
                &sealed_proof,
                pool_address,
                &pool_data,
                marker_address,
                &marker_data,
                &instructions,
            ),
            "missing" => simulate_atomic_program_account_instructions_with_absent_marker(
                &probe_so,
                proof_address,
                &sealed_proof,
                pool_address,
                &pool_data,
                marker_address,
                &instructions,
            ),
            mode => panic!("unsupported V5_CU_FROZEN_MARKER_MODE {mode:?}"),
        }
        .expect("simulate frozen marker mode");
        let totals = simulations
            .iter()
            .map(|result| result.units)
            .collect::<Vec<_>>();
        assert_eq!(totals.len(), REPEATS);
        assert!(totals.iter().all(|total| *total == totals[0]));
        let completed_cpi = simulations
            .iter()
            .filter(|result| completed_system_program_cpi_log_evidence(&result.logs).is_some())
            .count();
        assert_eq!(
            completed_cpi,
            if marker_mode == "missing" { REPEATS } else { 0 }
        );
        let summary_path = frozen_dir.join(format!("v5_frozen_marker_{marker_mode}_cu.json"));
        fs::write(
            &summary_path,
            format!(
                "{}\n",
                serde_json::to_string_pretty(&serde_json::json!({
                    "artifact": "v5_frozen_marker_mode_cu",
                    "marker_mode": marker_mode,
                    "sbf_path": probe_so,
                    "sbf_sha256": expected_sbf,
                    "totals_cu": totals,
                    "identical_repeats": REPEATS,
                    "system_program_cpi_completed_repeats": completed_cpi,
                    "proof_body_bytes": proof_body.len(),
                    "sealed_proof_account_bytes": sealed_proof.len(),
                    "query_indices": frozen_queries,
                }))
                .expect("encode frozen marker-mode summary")
            ),
        )
        .expect("write frozen marker-mode summary");
        println!(
            "v5-frozen-marker-mode mode={marker_mode} total={} repeats={totals:?} system_cpi_repeats={completed_cpi} proof_body_bytes={} sealed_proof_account_bytes={} queries={frozen_queries:?} path={}",
            totals[0],
            proof_body.len(),
            sealed_proof.len(),
            summary_path.display()
        );
    }

    #[test]
    fn v5_runtime_statement_and_exact_tag67_wire_preserve_the_cu_fixture() {
        let (legacy_statement, legacy_witness) = real_v5_statement_and_witness();
        let (runtime_statement, runtime_witness) =
            real_v5_statement_and_witness_for_runtime([0x5a; 32], 73, [0x5d; 32]);
        assert_eq!(runtime_statement, legacy_statement);
        assert_eq!(runtime_witness, legacy_witness);

        let exact_wire = build_v5_tag67_transaction_wire(&runtime_statement);
        assert_eq!(exact_wire.len(), V5_FULL_CU_TRANSACTION_WIRE_BYTES);
        assert_eq!(exact_wire.len(), 169);
        assert_eq!(
            exact_wire.to_vec(),
            full_v5_transaction_wire(&legacy_statement)
        );

        let decoded =
            aspis_verifier::v5_full_transaction::parse_v5_full_cu_public_inputs(&exact_wire)
                .expect("parse exact tag-67 public-input wire");
        assert_eq!(
            decoded.current_anchor,
            aspis_statement::encode_digest_canonical(&runtime_statement.spend.anchor)
        );
        assert_eq!(
            decoded.nullifier,
            aspis_statement::encode_digest_canonical(&runtime_statement.spend.nullifier)
        );
        assert_eq!(
            decoded.output_commitment,
            aspis_statement::encode_digest_canonical(&runtime_statement.spend.output_commitment,)
        );
        assert_eq!(
            decoded.output_anchor,
            aspis_statement::encode_digest_canonical(&runtime_statement.output_anchor)
        );
        assert_eq!(decoded.asset_id, runtime_statement.spend.asset_id.0);
        assert_eq!(decoded.fee, runtime_statement.spend.fee);
        assert_eq!(
            decoded.deployment_domain,
            runtime_statement.deployment_domain
        );
    }

    #[test]
    #[ignore = "expensive real-witness serializer/runtime-binding regression"]
    fn v5_honest_serializer_preserves_fixture_and_binds_runtime_statement() {
        let (legacy_statement, mut legacy_artifact) =
            build_real_v5_fixture_with_pivot_pad(fixture_q(29_999))
                .expect("build legacy deterministic CU fixture");
        let (legacy_proof, legacy_metadata) =
            serialize_real_v5_runtime_account_data_for_test_selector(
                &legacy_statement,
                &mut legacy_artifact,
                None,
            )
            .expect("serialize legacy deterministic CU fixture");
        let (honest_proof, honest_selector) =
            serialize_honest_v5_runtime_proof_body(&legacy_statement, &legacy_artifact)
                .expect("serialize through honest artifact seam");

        assert_eq!(honest_proof, legacy_proof);
        assert_eq!(honest_selector, legacy_artifact.query_selector);
        assert_eq!(honest_selector, legacy_metadata.honest_least_good_selector);
        assert_eq!(
            legacy_artifact
                .good_gate_evaluations
                .iter()
                .position(|evaluation| evaluation.is_good()),
            Some(usize::from(honest_selector))
        );
        assert!(legacy_metadata.selected_branch_good);
        assert!(!legacy_metadata.test_only_nonleast_branch_override);
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &honest_proof).is_ok());

        let runtime_pool = [0x6a; 32];
        let runtime_sequence = 74;
        let runtime_deployment_domain = [0x6d; 32];
        let (runtime_statement, runtime_artifact) =
            build_real_v5_fixture_with_runtime_binding_and_pivot_pad(
                runtime_pool,
                runtime_sequence,
                runtime_deployment_domain,
                fixture_q(29_999),
            )
            .expect("build runtime-bound deterministic regression fixture");
        let (runtime_proof, runtime_selector) =
            serialize_honest_v5_runtime_proof_body(&runtime_statement, &runtime_artifact)
                .expect("serialize runtime-bound honest artifact");

        assert_eq!(runtime_statement.pool, runtime_pool);
        assert_eq!(runtime_statement.sequence, runtime_sequence);
        assert_eq!(
            runtime_statement.deployment_domain,
            runtime_deployment_domain
        );
        assert_ne!(runtime_statement, legacy_statement);
        assert_ne!(
            runtime_artifact.statement_digest,
            legacy_artifact.statement_digest
        );
        assert_ne!(
            runtime_artifact.transcript_state_after_queries,
            legacy_artifact.transcript_state_after_queries
        );
        assert_ne!(runtime_proof, honest_proof);
        assert!(!runtime_proof.is_empty());
        let sealed_runtime_proof =
            finalized_proof_account_data(&runtime_proof).expect("seal runtime-bound proof body");
        let declared_runtime_length = u32::from_le_bytes(
            sealed_runtime_proof[4..8]
                .try_into()
                .expect("proof-account length word"),
        );
        assert_eq!(declared_runtime_length as usize, runtime_proof.len());
        assert_eq!(
            sealed_runtime_proof.len(),
            PROOF_ACCOUNT_HEADER_LEN + runtime_proof.len()
        );
        assert_eq!(runtime_selector, runtime_artifact.query_selector);
        assert_eq!(
            runtime_artifact
                .good_gate_evaluations
                .iter()
                .position(|evaluation| evaluation.is_good()),
            Some(usize::from(runtime_selector))
        );
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &runtime_proof).is_ok());

        assert!(
            serialize_honest_v5_runtime_proof_body(&runtime_statement, &legacy_artifact,).is_err()
        );
        assert!(
            serialize_honest_v5_runtime_proof_body(&legacy_statement, &runtime_artifact,).is_err()
        );
    }

    #[test]
    #[ignore = "expensive all-selector real-witness fixture regeneration"]
    fn v5_selected_good_test_fixtures_rebuild_every_query_dependent_object() {
        let (statement, mut artifact) = build_real_v5_fixture_with_pivot_pad(fixture_q(29_999))
            .expect("build one honest least-Good artifact");
        let honest_selector = artifact.query_selector;
        let (honest_data, honest_metadata) =
            serialize_real_v5_runtime_account_data_for_test_selector(
                &statement,
                &mut artifact,
                None,
            )
            .expect("serialize honest least-Good fixture");
        assert_eq!(honest_metadata.query_selector, honest_selector);
        assert_eq!(honest_metadata.honest_least_good_selector, honest_selector);
        assert!(!honest_metadata.test_only_nonleast_branch_override);
        assert!(honest_metadata.selected_branch_good);
        assert!(honest_metadata
            .good_gate_evaluations
            .into_iter()
            .all(V5HostGoodGateEvaluation::is_good));

        let mut fixtures = Vec::with_capacity(3);
        for selector in 0..3u8 {
            let (data, metadata) = serialize_real_v5_runtime_account_data_for_test_selector(
                &statement,
                &mut artifact,
                Some(selector),
            )
            .unwrap_or_else(|error| {
                panic!("serialize selected-Good fixture {selector}: {error:#}")
            });
            assert_eq!(metadata.query_selector, selector);
            assert_eq!(metadata.honest_least_good_selector, honest_selector);
            assert_eq!(
                metadata.test_only_nonleast_branch_override,
                selector != honest_selector
            );
            assert_eq!(metadata.batch_nonce, honest_metadata.batch_nonce);
            assert!(metadata.selected_branch_good);
            assert!(metadata.good_gate_evaluations[usize::from(selector)].is_good());
            assert_eq!(data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET], selector);
            assert_eq!(
                v5_complete_queries(aspis_prover::HOST_HASH, &data)
                    .expect("replay selected-Good fixture queries"),
                metadata.query_indices
            );
            assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &data).is_ok());

            // All pre-opening bytes outside the fixed selected C1/C2 records
            // and selector byte are query-independent and remain identical to
            // the honest least-Good artifact.
            let c1_end = V5_CU_PROBE_CANDIDATE_C1_OFFSET
                + V5_CU_PROBE_QUERY_COUNT * V5_CU_PROBE_CANDIDATE_C1_RECORD_BYTES;
            let c2_end =
                V5_CU_PROBE_C2_OFFSET + V5_CU_PROBE_QUERY_COUNT * V5_CU_PROBE_C2_RECORD_BYTES;
            for byte in 0..V5_CU_PROBE_ACCOUNT_BYTES {
                let selected_record = (V5_CU_PROBE_CANDIDATE_C1_OFFSET..c1_end).contains(&byte)
                    || (V5_CU_PROBE_C2_OFFSET..c2_end).contains(&byte);
                if !selected_record && byte != V5_CU_PROBE_QUERY_SELECTOR_OFFSET {
                    assert_eq!(
                        data[byte], honest_data[byte],
                        "selector {selector} changed query-independent byte {byte}"
                    );
                }
            }
            fixtures.push(data);
        }

        let proof_hashes = fixtures
            .iter()
            .map(|proof| Sha256::digest(proof).to_vec())
            .collect::<Vec<_>>();
        assert!(proof_hashes[0] != proof_hashes[1]);
        assert!(proof_hashes[0] != proof_hashes[2]);
        assert!(proof_hashes[1] != proof_hashes[2]);

        // A selector byte without its regenerated q18 records/opening suffix
        // is not a branch fixture and must remain rejected.
        for selector in 0..3usize {
            let mut selector_only = fixtures[selector].clone();
            selector_only[V5_CU_PROBE_QUERY_SELECTOR_OFFSET] = ((selector + 1) % 3) as u8;
            assert!(
                probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &selector_only).is_err(),
                "selector-only mutation {selector} unexpectedly verified"
            );
        }

        // A valid branch prefix cannot borrow a different branch's complete
        // opening suffix, even though both selected branches are Good.
        let mut crossed_suffix = fixtures[1][..V5_CU_PROBE_ACCOUNT_BYTES].to_vec();
        crossed_suffix.extend_from_slice(&fixtures[2][V5_CU_PROBE_ACCOUNT_BYTES..]);
        assert!(
            probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &crossed_suffix).is_err(),
            "selector-one prefix accepted selector-two opening suffix"
        );
    }

    use aspis_verifier::v5_cu_probe::wire_skeleton::V5_WIRE_PREFIX_BYTES;
    use aspis_verifier::v5_cu_probe::{
        V5_CU_REAL_PREFIX_C2_ROOT_OFFSET, V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET,
        V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET, V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES,
        V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT, V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET,
    };

    #[test]
    fn v5_batch_nonce_wire_slot_and_outer_magic_are_exact() {
        assert_eq!(V5_CU_PROBE_ACCOUNT_MAGIC, *b"AV5CUP08");
        assert_eq!(V5_CU_PROBE_BATCH_NONCE_OFFSET, 11_080);
        assert_eq!(V5_CU_PROBE_BATCH_NONCE_BYTES, 8);
        assert_eq!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET, 11_088);
        assert_eq!(V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_BYTES, 24);
        assert_eq!(V5_CU_PROBE_PREFIX_OFFSET, 11_112);
        assert_eq!(V5_CU_PROBE_ACCOUNT_BYTES, 19_136);
    }

    #[test]
    #[ignore = "expensive real-witness binding check; run before full CU measurement"]
    fn v5_component_b_pivot_commitment_and_inactive_claim_mutations_are_rejected() {
        let (_, first, _) = build_real_v5_runtime_account_data().expect("build pivot fixture");

        let prefix_c2 = V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_C2_ROOT_OFFSET;
        let private_c2 = V5_CU_PROBE_PRIVATE_ROOTS_OFFSET + 32;
        let claim = V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET;

        // Mutate the C2 commitment in both redundant root locations, leaving
        // its claims/openings intact. Verification must notice the
        // transcript/PCS inconsistency rather than only the duplicate-root
        // check. The separate split-layer test proves that changing p changes
        // this root.
        let mut pivot_mutation = first.clone();
        pivot_mutation[prefix_c2] ^= 1;
        pivot_mutation[private_c2] ^= 1;
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &pivot_mutation).is_err());

        let mut claim_mutation = first;
        claim_mutation[claim] ^= 1;
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &claim_mutation).is_err());
    }

    #[test]
    #[ignore = "expensive real-witness exact-layout check; run before full CU measurement"]
    fn v5_mode9_rejects_retired_and_malformed_runtime_layouts() {
        let (_, data, metadata) =
            build_real_v5_runtime_account_data().expect("build real v5 fixture");
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &data).is_ok());
        assert_eq!(
            &data[V5_CU_PROBE_BATCH_NONCE_OFFSET
                ..V5_CU_PROBE_BATCH_NONCE_OFFSET + V5_CU_PROBE_BATCH_NONCE_BYTES],
            &metadata.batch_nonce.to_le_bytes()
        );
        assert!(
            data[V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET..V5_CU_PROBE_PREFIX_OFFSET]
                .iter()
                .all(|byte| *byte == 0)
        );

        let work_nonce_offsets = [
            ("fold 0", V5_CU_PROBE_RELATION_FINAL_OFFSET),
            ("fold 1", V5_CU_PROBE_RELATION_FINAL_OFFSET + 8),
            ("fold 2", V5_CU_PROBE_RELATION_FINAL_OFFSET + 16),
            ("fold 3", V5_CU_PROBE_RELATION_FINAL_OFFSET + 24),
            ("batch", V5_CU_PROBE_BATCH_NONCE_OFFSET),
            ("final", V5_CU_PROBE_FINAL_NONCE_OFFSET),
        ];
        for (stage, offset) in work_nonce_offsets {
            let mut nonce_mutation = data.clone();
            nonce_mutation[offset] ^= 1;
            assert!(
                probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &nonce_mutation).is_err(),
                "mutating the {stage} work nonce did not change verification"
            );
        }

        let fold_zero: [u8; 8] = data
            [V5_CU_PROBE_RELATION_FINAL_OFFSET..V5_CU_PROBE_RELATION_FINAL_OFFSET + 8]
            .try_into()
            .unwrap();
        let fold_one: [u8; 8] = data
            [V5_CU_PROBE_RELATION_FINAL_OFFSET + 8..V5_CU_PROBE_RELATION_FINAL_OFFSET + 16]
            .try_into()
            .unwrap();
        assert_ne!(fold_zero, fold_one, "fixture fold nonces must be distinct");
        let mut fold_permutation = data.clone();
        fold_permutation[V5_CU_PROBE_RELATION_FINAL_OFFSET..V5_CU_PROBE_RELATION_FINAL_OFFSET + 8]
            .copy_from_slice(&fold_one);
        fold_permutation
            [V5_CU_PROBE_RELATION_FINAL_OFFSET + 8..V5_CU_PROBE_RELATION_FINAL_OFFSET + 16]
            .copy_from_slice(&fold_zero);
        assert!(
            probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &fold_permutation).is_err(),
            "swapping distinct fold-zero/fold-one nonces unexpectedly verified"
        );

        let batch_nonce: [u8; 8] = data[V5_CU_PROBE_BATCH_NONCE_OFFSET
            ..V5_CU_PROBE_BATCH_NONCE_OFFSET + V5_CU_PROBE_BATCH_NONCE_BYTES]
            .try_into()
            .unwrap();
        let final_nonce: [u8; 8] = data
            [V5_CU_PROBE_FINAL_NONCE_OFFSET..V5_CU_PROBE_QUERY_SELECTOR_OFFSET]
            .try_into()
            .unwrap();
        assert_ne!(
            batch_nonce, final_nonce,
            "fixture batch and final nonces must be distinct"
        );

        let mut final_substituted_for_batch = data.clone();
        final_substituted_for_batch[V5_CU_PROBE_BATCH_NONCE_OFFSET
            ..V5_CU_PROBE_BATCH_NONCE_OFFSET + V5_CU_PROBE_BATCH_NONCE_BYTES]
            .copy_from_slice(&final_nonce);
        assert!(
            probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &final_substituted_for_batch).is_err(),
            "the final nonce substituted for batch work unexpectedly verified"
        );

        let mut batch_substituted_for_final = data.clone();
        batch_substituted_for_final
            [V5_CU_PROBE_FINAL_NONCE_OFFSET..V5_CU_PROBE_QUERY_SELECTOR_OFFSET]
            .copy_from_slice(&batch_nonce);
        assert!(
            probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &batch_substituted_for_final).is_err(),
            "the batch nonce substituted for final work unexpectedly verified"
        );

        let mut swapped_batch_and_final = data.clone();
        swapped_batch_and_final[V5_CU_PROBE_BATCH_NONCE_OFFSET
            ..V5_CU_PROBE_BATCH_NONCE_OFFSET + V5_CU_PROBE_BATCH_NONCE_BYTES]
            .copy_from_slice(&final_nonce);
        swapped_batch_and_final[V5_CU_PROBE_FINAL_NONCE_OFFSET..V5_CU_PROBE_QUERY_SELECTOR_OFFSET]
            .copy_from_slice(&batch_nonce);
        assert!(
            probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &swapped_batch_and_final).is_err(),
            "swapping distinct batch/final work nonces unexpectedly verified"
        );

        let mut relation_final_hidden_extension = data.clone();
        relation_final_hidden_extension[V5_CU_PROBE_RELATION_FINAL_ZERO_TAIL_OFFSET] = 1;
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &relation_final_hidden_extension).is_err());

        let retired_span_bytes = V5_CU_PROBE_DIAGNOSTIC_ACCOUNT_BYTES - V5_CU_PROBE_ACCOUNT_BYTES;
        assert_eq!(retired_span_bytes, 8_064);
        let mut old_layout = Vec::with_capacity(data.len() + retired_span_bytes);
        old_layout.extend_from_slice(&data[..V5_CU_PROBE_CANDIDATE_C1_OFFSET]);
        old_layout.resize(old_layout.len() + retired_span_bytes, 0);
        old_layout.extend_from_slice(&data[V5_CU_PROBE_CANDIDATE_C1_OFFSET..]);
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &old_layout).is_err());

        let mut former_legacy_mutation = old_layout;
        former_legacy_mutation[V5_CU_PROBE_CANDIDATE_C1_OFFSET + retired_span_bytes / 2] ^= 1;
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &former_legacy_mutation).is_err());

        let mut truncated = data.clone();
        truncated.pop();
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &truncated).is_err());

        let mut appended = data.clone();
        appended.push(0);
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &appended).is_err());

        let mut swapped_lanes = data.clone();
        let b_lane = V5_CU_PROBE_CANDIDATE_C1_COLUMNS + 1;
        let c_lane = V5_CU_PROBE_CANDIDATE_C1_COLUMNS + 2;
        for point in 0..V5_CU_PROBE_RELATION_CLAIMS_PER_LANE {
            for table in [
                V5_CU_PROBE_RELATION_CLAIMS_OFFSET,
                V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_CLAIMS_OFFSET,
            ] {
                let b_start = table + (point * V5_CU_PROBE_RELATION_LANES + b_lane) * QM31_BYTES;
                let c_start = table + (point * V5_CU_PROBE_RELATION_LANES + c_lane) * QM31_BYTES;
                let b: [u8; QM31_BYTES] = swapped_lanes[b_start..b_start + QM31_BYTES]
                    .try_into()
                    .unwrap();
                let c: [u8; QM31_BYTES] = swapped_lanes[c_start..c_start + QM31_BYTES]
                    .try_into()
                    .unwrap();
                swapped_lanes[b_start..b_start + QM31_BYTES].copy_from_slice(&c);
                swapped_lanes[c_start..c_start + QM31_BYTES].copy_from_slice(&b);
            }
        }
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &swapped_lanes).is_err());

        let mut fixed_duplicate_mismatch = data;
        fixed_duplicate_mismatch[V5_CU_PROBE_CANDIDATE_C1_OFFSET] ^= 1;
        assert!(probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &fixed_duplicate_mismatch).is_err());
    }

    #[test]
    #[ignore = "expensive real-witness fixture; run explicitly before the full CU measurement"]
    fn v5_public_fs_salts_round_trip_and_each_mutation_is_rejected() {
        let (_, data, _) = build_real_v5_runtime_account_data().expect("build real v5 fixture");
        let expected = deterministic_public_fs_salts_for_cu_test_fixture();

        assert_eq!(V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES, 32);
        assert_eq!(V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT, 5);
        for section in 0..V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT {
            let start = V5_CU_PROBE_PREFIX_OFFSET
                + V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET
                + section * V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES;
            assert_eq!(
                &data[start..start + V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_BYTES],
                expected.section(section),
                "public FS salt section {section} did not round-trip"
            );

            let mut mutated = data.clone();
            mutated[start + section] ^= 1;
            assert!(
                probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &mutated).is_err(),
                "mutating public FS salt section {section} did not change verification"
            );
        }

        let zero_tail_start = V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_ZERO_RESERVE_OFFSET;
        let zero_tail_end = V5_CU_PROBE_PREFIX_OFFSET + V5_WIRE_PREFIX_BYTES;
        assert!(data[zero_tail_start..zero_tail_end]
            .iter()
            .all(|byte| *byte == 0));
        let mut hidden_extension = data;
        hidden_extension[zero_tail_start + 199] = 1;
        assert!(
            probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &hidden_extension).is_err(),
            "non-canonical hidden prefix extension was accepted"
        );
    }

    #[test]
    #[ignore = "expensive exact GoodA/GoodB host--verifier correspondence fixture"]
    fn v5_good_gate_verifier_replays_all_three_current_fixture_selectors() {
        let (_, data, metadata) =
            build_real_v5_runtime_account_data().expect("build real v5 fixture");
        let evaluations =
            aspis_verifier::v5_cu_probe::v5_good_gate_evaluations(aspis_prover::HOST_HASH, &data)
                .expect("replay all three verifier GoodA/GoodB candidates");
        for selector in 0..3 {
            let host = metadata.good_gate_evaluations[selector];
            let verifier = evaluations[selector];
            assert_eq!(verifier.queries, host.queries);
            assert_eq!(verifier.good_a_matrix, host.good_a_matrix);
            assert_eq!(verifier.good_a_determinant, host.good_a_determinant);
            assert_eq!(verifier.good_b_matrix, host.good_b_matrix);
            assert_eq!(verifier.good_b_determinant, host.good_b_determinant);
        }
        assert_eq!(data[V5_CU_PROBE_QUERY_SELECTOR_OFFSET], 0);
        for hostile_selector in [1u8, 2, 3, u8::MAX] {
            let mut hostile = data.clone();
            hostile[V5_CU_PROBE_QUERY_SELECTOR_OFFSET] = hostile_selector;
            assert!(
                probe_sink(V5_CU_PROBE_COMPOSITE_MODE, &hostile).is_err(),
                "selector byte {hostile_selector} verified without regenerated authenticated q18 records and opening suffix"
            );
        }
        assert_eq!(
            evaluations.map(|evaluation| evaluation.good_a_determinant.0),
            [1_767_599_905, 1_031_059_058, 741_285_019]
        );
        assert_eq!(
            evaluations.map(|evaluation| evaluation.queries),
            [
                [
                    19_380, 21_014, 109_352, 44_674, 21_260, 83_507, 40_798, 61_881, 8_433, 33_910,
                    14_602, 124_621, 2_601, 126_631, 71_128, 101_903, 42_568, 9_991,
                ],
                [
                    60_629, 85_776, 36_449, 50_431, 67_618, 87_432, 55_668, 91_796, 6_843, 96_772,
                    476, 115_313, 119_442, 65_639, 82_196, 53_157, 105_745, 110_139,
                ],
                [
                    75_558, 79_839, 63_274, 107_847, 122_569, 118_926, 50_796, 52_161, 43_596,
                    129_622, 92_207, 129_493, 37_001, 52_953, 43_467, 73_149, 41_929, 13_368,
                ],
            ],
            "verifier transcript/query derivation diverged from the host GoodA fixture"
        );
        let expected_a_matrix_sha256 = [
            "6175fde5462b081465ca73438f81a7b855913814a79923a4bfbbaf6f6c7817a7",
            "c6f390a1ed6099721a7830035bdbc9e030383c75bef4050a71112dd09f5c1501",
            "6ed1fbcad33569162339d656aabc25896608017443b283ca9bfc99fe9e10792d",
        ];
        let expected_b_matrix_sha256 = [
            "a30b17d314807990eb21ca5dd43ed5ce1c7ecf321e48c6608b31c920522d4176",
            "05b101e45722773cb160d33b629fc54957b88edc09b9f173187ae59a33e1ba7b",
            "f2656b4fc398bf739cd3e8b13294378bfffad4623f5648a3c108ccaceb021631",
        ];
        let expected_b_determinants = [
            [1_580_537_480, 1_607_608_012, 2_104_226_277, 1_639_904_929],
            [1_678_945_095, 293_547_005, 1_673_929_587, 2_007_946_658],
            [1_915_211_067, 649_993_141, 369_026_797, 636_829_088],
        ];
        for (selector, evaluation) in evaluations.into_iter().enumerate() {
            assert!(
                evaluation.is_good(),
                "selector {selector} is not GoodA && GoodB"
            );
            let mut a_matrix_bytes = [0u8; 12 * 12 * 4];
            for (index, value) in evaluation.good_a_matrix.iter().flatten().enumerate() {
                a_matrix_bytes[4 * index..4 * index + 4].copy_from_slice(&value.0.to_le_bytes());
            }
            assert_eq!(
                hex(&Sha256::digest(a_matrix_bytes)),
                expected_a_matrix_sha256[selector],
                "verifier GoodA matrix bytes diverged from the host fixture at selector {selector}"
            );
            let mut b_matrix_bytes = [0u8; 4 * 4 * 4 * 4];
            for (index, value) in evaluation.good_b_matrix.iter().flatten().enumerate() {
                let limbs = [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0];
                for (limb, word) in limbs.into_iter().enumerate() {
                    let offset = 16 * index + 4 * limb;
                    b_matrix_bytes[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
                }
            }
            assert_eq!(
                hex(&Sha256::digest(b_matrix_bytes)),
                expected_b_matrix_sha256[selector],
                "verifier GoodB matrix bytes diverged from the independent host fixture at selector {selector}"
            );
            assert_eq!(
                [
                    evaluation.good_b_determinant.c0.a.0,
                    evaluation.good_b_determinant.c0.b.0,
                    evaluation.good_b_determinant.c1.a.0,
                    evaluation.good_b_determinant.c1.b.0,
                ],
                expected_b_determinants[selector],
                "verifier GoodB determinant diverged from the independent host fixture at selector {selector}"
            );
            println!(
                "v5-verifier-good selector={selector} queries={:?} a_matrix={:?} a_det={} b_matrix={:?} b_det={:?}",
                evaluation.queries,
                evaluation
                    .good_a_matrix
                    .map(|row| row.map(|value| value.0)),
                evaluation.good_a_determinant.0,
                evaluation.good_b_matrix.map(|row| row.map(|value| [
                    value.c0.a.0,
                    value.c0.b.0,
                    value.c1.a.0,
                    value.c1.b.0,
                ])),
                [
                    evaluation.good_b_determinant.c0.a.0,
                    evaluation.good_b_determinant.c0.b.0,
                    evaluation.good_b_determinant.c1.a.0,
                    evaluation.good_b_determinant.c1.b.0,
                ],
            );
        }
    }
}
