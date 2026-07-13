//! `stage0-onchain`: build the SBF program, spawn a local validator, run the
//! Stage 0 measurement matrix and corruption suite on-chain, and write
//! `results/stage0/onchain_summary.json`.
//!
//! Requires `cargo-build-sbf` and `solana-test-validator` on PATH (blocked in
//! some sandboxes; the gate note records where this has and hasn't run).

use std::{
    fs,
    net::TcpListener,
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use borsh::to_vec;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use solana_sdk::{
    compute_budget::ComputeBudgetInstruction,
    instruction::{AccountMeta, Instruction},
    native_token::LAMPORTS_PER_SOL,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    transaction::Transaction,
};
// solana-sdk 2.x deprecates the re-export in favor of solana-system-interface;
// keep the single-crate dependency surface for the Stage 0 harness.
#[allow(deprecated)]
use solana_sdk::system_instruction;

use aspis_core::params::{
    PROFILE_CAPACITY, PROFILE_CAPACITY_G32_Q32, PROFILE_CAPACITY_G32_Q36,
    PROFILE_CAPACITY_LR10_Q32_G16, PROFILE_CAPACITY_LR10_Q36_G16, PROFILE_CAPACITY_LR10_Q40_G16,
    PROFILE_CAPACITY_LR14, PROFILE_JOHNSON,
};
use aspis_core::{FoldPayload, MerkleMode, Profile};
use aspis_prover::{
    multilinear_eval, prove, prove_exact_wide_v4_scaffold_for_measurement, prove_with_claim,
    prove_with_claim_v4, prove_with_synthetic_second_phase, seeded_coeffs, ProveOptions, HOST_HASH,
};
use aspis_verifier::{
    AspisInstruction, ExactWideV4DiagnosticMode, JohnsonM31CircleDiagnosticPhase,
    M31CircleBasisDiagnosticMode, StateOnlyWidth28DiagnosticPhase, TwoPointBatchingDiagnosticMode,
    ZkKernelKind, M31_CIRCLE_BASIS_C1_COLUMNS, M31_CIRCLE_BASIS_C1_LEAF_BYTES,
    M31_CIRCLE_BASIS_C2_LEAF_BYTES, M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS,
    M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES, M31_CIRCLE_FOLD_FIXTURE_BYTES, PROOF_ACCOUNT_HEADER_LEN,
};

const UPLOAD_CHUNK_BYTES: usize = 640;
const VERIFY_CU_LIMIT: u32 = 1_400_000;
const HEAP_FRAME_BYTES: u32 = 262_144;
const VERIFY_REPETITIONS: usize = 5;

#[derive(Serialize)]
pub struct OnchainVariant {
    pub profile: &'static str,
    pub soundness_label: &'static str,
    pub fold_payload: &'static str,
    pub merkle_mode: &'static str,
    pub status: &'static str,
    pub verify_error: Option<String>,
    pub proof_bytes: usize,
    pub upload_chunks: usize,
    pub upload_cu_total: u64,
    pub verify_cu: Vec<u64>,
    pub verify_cu_mean: f64,
    pub verify_repetitions_requested: usize,
    pub corruption_rejected_onchain: Vec<(String, bool)>,
}

#[derive(Serialize)]
pub struct OnchainSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub verify_cu_limit: u32,
    pub heap_frame_bytes: u32,
    pub gate_matrix_only: bool,
    pub variants: Vec<OnchainVariant>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct CuMarker {
    pub label: String,
    pub remaining: u64,
    pub delta_from_previous: Option<i64>,
}

#[derive(Serialize)]
pub struct ProfileRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub fold_payload: &'static str,
    pub merkle_mode: &'static str,
    pub proof_bytes: usize,
    pub upload_chunks: usize,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub markers: Vec<CuMarker>,
    pub logs: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct M31FreshKappaSbfSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub upload_chunks: usize,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub isolated_rlc_seam_reference_cu: u64,
    pub reconciliation_rule: String,
    pub markers: Vec<CuMarker>,
    pub accepted_all_runs: bool,
    pub stale_statement_rejected: bool,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub explicit_nonclaims: Vec<String>,
}

#[derive(Serialize)]
pub struct M31JohnsonPhaseRun {
    pub label: String,
    pub phase: String,
    pub start: u16,
    pub end: u16,
    pub simulation_cu: Vec<u64>,
    pub selected_cu: u64,
}

#[derive(Serialize)]
pub struct M31JohnsonSbfSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub profile: String,
    pub query_count: u16,
    pub grinding_bits: u8,
    pub johnson_rho: f64,
    pub johnson_eta: f64,
    pub bits_per_query: f64,
    pub query_round_bits: f64,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_cache: String,
    pub proof_source: String,
    pub grinding_generation_seconds: Option<f64>,
    pub upload_chunks: usize,
    pub unique_layer_indices: [usize; 4],
    pub shared_base_cu: u64,
    pub phase_runs: Vec<M31JohnsonPhaseRun>,
    pub reconciliation_formula: String,
    pub reconciled_integrated_cu: u64,
    pub headroom_vs_1_4m_cu: i64,
    pub full_simulation_cu_at_cap: Option<u64>,
    pub full_simulation_error: Option<String>,
    pub full_host_verifier_accepted: bool,
    pub stale_statement_rejected: bool,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub soundness_caveat: String,
    pub explicit_nonclaims: Vec<String>,
}

#[derive(Serialize)]
pub struct M31Rate16SbfSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub profile: String,
    pub rate: String,
    pub query_count: u16,
    pub grinding_bits: u8,
    pub johnson_eta: f64,
    pub bits_per_query: f64,
    pub query_round_bits: f64,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_cache: String,
    pub proof_source: String,
    pub grinding_generation_seconds: Option<f64>,
    pub upload_chunks: usize,
    pub unique_layer_indices: [usize; 4],
    pub full_simulation_cu: Vec<Option<u64>>,
    pub full_simulation_errors: Vec<Option<String>>,
    pub direct_integrated_cu: Option<u64>,
    pub shared_base_cu: u64,
    pub layer0_inclusive_cu: u64,
    pub later_inclusive_cu: u64,
    pub segment_reconciled_cu: u64,
    pub segment_delta_vs_direct_cu: Option<i64>,
    pub selected_integrated_cu: u64,
    pub headroom_vs_1_4m_cu: i64,
    pub headroom_vs_1_19m_cu: i64,
    pub composition_central_cu: Option<u64>,
    pub composition_central_error: Option<String>,
    pub composition_central_increment_cu: Option<i64>,
    pub composition_central_headroom_vs_1_4m_cu: Option<i64>,
    pub composition_stress_cu: Option<u64>,
    pub composition_stress_error: Option<String>,
    pub composition_stress_increment_cu: Option<i64>,
    pub composition_stress_headroom_vs_1_4m_cu: Option<i64>,
    pub full_host_verifier_accepted: bool,
    pub stale_statement_rejected: bool,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub soundness_caveat: String,
    pub explicit_nonclaims: Vec<String>,
}

#[derive(Serialize)]
pub struct M31Rate16HardenedSbfSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub profile: String,
    pub rate: String,
    pub query_count: u16,
    pub query_grinding_bits: u8,
    pub fold_pow_bits: [u8; 4],
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_cache: String,
    pub proof_source: String,
    pub grinding_generation_seconds: Option<f64>,
    pub fold_nonces: [u64; 4],
    pub query_nonce: u64,
    pub upload_chunks: usize,
    pub simulation_cu: Vec<u64>,
    pub selected_integrated_cu: u64,
    pub incremental_cu_vs_unhardened: i64,
    pub headroom_vs_1_4m_cu: i64,
    pub full_host_verifier_accepted: bool,
    pub fold_nonce_corruptions_rejected: [bool; 4],
    pub query_nonce_corruption_rejected: bool,
    pub stale_statement_rejected: bool,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub explicit_nonclaims: Vec<String>,
}

#[derive(Serialize)]
pub struct LayoutPoint {
    pub log_rows: u8,
    pub columns: u16,
    pub query_count: u16,
    pub leaf_bytes: u16,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub markers: Vec<CuMarker>,
}

#[derive(Serialize)]
pub struct LayoutSweep {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub points: Vec<LayoutPoint>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Stage2LayoutVariant {
    pub columns: u16,
    pub leaf_bytes: u16,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub delta_vs_k64_cu: i64,
    pub diagnostic_markers: Vec<CuMarker>,
    pub wide_leaf_hash_cu: Option<i64>,
    pub synthetic_merkle_cu: Option<i64>,
    pub obsolete_same_gamma_rlc_cu: Option<i64>,
}

#[derive(Serialize)]
pub struct Stage2LayoutSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub log_rows: u8,
    pub query_count: u16,
    pub repetitions: usize,
    pub variants: Vec<Stage2LayoutVariant>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Poseidon2ProbeVariant {
    pub implementation: &'static str,
    pub permutations: u16,
    pub simulation_cu: Vec<Option<u64>>,
    pub simulation_errors: Vec<Option<String>>,
    pub accepted_all: bool,
    pub mean_cu_if_accepted: Option<f64>,
    pub incremental_cu_over_zero_if_accepted: Option<i64>,
}

#[derive(Serialize)]
pub struct Poseidon2ProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub variants: Vec<Poseidon2ProbeVariant>,
    pub measured_incremental_cu_per_permutation_from_8: Option<f64>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct ZkKernelProbeVariant {
    pub kernel: &'static str,
    pub iterations: u16,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub incremental_cu_over_zero: i64,
    pub incremental_cu_per_iteration: f64,
}

#[derive(Serialize)]
pub struct ZkKernelProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub variants: Vec<ZkKernelProbeVariant>,
    pub full_pcs_verifier: FullPcsVerifierComparison,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct WideRlcProbeVariant {
    pub kernel: &'static str,
    pub columns: u16,
    pub query_count: u16,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub baseline_cu_mean: f64,
    pub incremental_cu: i64,
}

#[derive(Serialize)]
pub struct WideRlcProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub variants: Vec<WideRlcProbeVariant>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct MerkleArityProbePoint {
    pub tree: &'static str,
    pub depth: u8,
    pub query_count: u16,
    pub binary_cu: Vec<u64>,
    pub binary_cu_mean: f64,
    pub radix4_cu: Vec<u64>,
    pub radix4_cu_mean: f64,
    pub radix4_savings_cu: i64,
}

#[derive(Serialize)]
pub struct MerkleArityProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub points: Vec<MerkleArityProbePoint>,
    pub modeled_binary_total_cu: i64,
    pub modeled_radix4_total_cu: i64,
    pub modeled_radix4_savings_cu: i64,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Radix8MerkleDepth12Variant {
    pub arity: u8,
    pub parent_hash_calls: usize,
    pub frontier_hashes: usize,
    pub frontier_bytes: usize,
    pub opened_digest_entry_bytes: usize,
    pub synthetic_minimal_subtree_bytes: usize,
    pub parent_preimage_bytes: usize,
    pub sha256_compression_blocks: usize,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub corrupted_frontier_probe_cu: u64,
    pub corrupted_frontier_rejected: bool,
}

#[derive(Serialize)]
pub struct Radix8MerkleDepth12Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub depth: u8,
    pub distinct_queries: u16,
    pub variants: Vec<Radix8MerkleDepth12Variant>,
    pub radix8_minus_radix4_cu: i64,
    pub two_layer0_tree_projection_cu: i64,
    pub two_layer0_tree_frontier_byte_delta: i64,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct MerkleForestProbeVariant {
    pub mode: &'static str,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub corrupted_lane_probe_cu: Vec<u64>,
    pub all_five_corrupted_lanes_rejected: bool,
}

#[derive(Serialize)]
pub struct MerkleForestProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub depth: u8,
    pub distinct_queries: u16,
    pub tree_start_levels: [u8; 5],
    pub unique_leaves: [usize; 5],
    pub parent_hash_calls: usize,
    pub frontier_hashes: usize,
    pub frontier_bytes: usize,
    pub variants: Vec<MerkleForestProbeVariant>,
    pub fused_minus_independent_cu: i64,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Layer0DotWidthProbeVariant {
    pub columns: u8,
    pub c1_leaf_bytes: usize,
    pub c2_leaf_bytes: usize,
    pub query_count: u8,
    pub expected_sink_hex: String,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub savings_vs_49_columns_cu: i64,
    pub noncanonical_c1_probe_cu: u64,
    pub noncanonical_c2_probe_cu: u64,
    pub both_noncanonical_cases_rejected: bool,
}

#[derive(Serialize)]
pub struct Layer0DotWidthProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub query_count: u8,
    pub variants: Vec<Layer0DotWidthProbeVariant>,
    pub savings_49_to_33_cu: i64,
    pub savings_49_to_17_cu: i64,
    pub savings_49_to_16_cu: i64,
    pub marginal_cu_per_removed_column_49_to_33: f64,
    pub marginal_cu_per_removed_column_33_to_17: f64,
    pub marginal_cu_for_removed_tail_17_to_16: i64,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicRoutingPartitionProbeVariant {
    pub mode: &'static str,
    pub low_row_bit_mask_hex: &'static str,
    pub tensor_routing_rank: usize,
    pub shared_outer_products: usize,
    pub factor_entries: usize,
    pub expected_sink_hex: String,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub wrong_sink_probe_cu: u64,
    pub wrong_sink_rejected: bool,
}

#[derive(Serialize)]
pub struct AtomicRoutingPartitionProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub seed: u32,
    pub registry_fingerprint_hex: &'static str,
    pub copy_terms: usize,
    pub active_rows: usize,
    pub variants: Vec<AtomicRoutingPartitionProbeVariant>,
    pub optimized_savings_cu: i64,
    pub outputs_identical: bool,
    pub measurement_scope: &'static str,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile20CostLedger {
    pub transaction_setup_and_public_decode_cu: u64,
    pub proof_load_cu: u64,
    pub parse_cu: u64,
    pub transcript_cu: u64,
    pub atomic_terminal_cu: u64,
    pub relation_cu: u64,
    pub merkle_openings_cu: u64,
    pub query_arithmetic_cu: u64,
    pub verifier_return_cu: u64,
    pub post_last_marker_cu: u64,
    pub overlap_reconciled_total_cu: u64,
    pub formula: String,
    pub source: String,
}

#[derive(Serialize)]
pub struct AtomicProfile20CostSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub profile_id: u8,
    pub rho: &'static str,
    pub query_count: u16,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub expected_atomic_terminal_hex: String,
    pub literal_simulation_cu: Option<u64>,
    pub literal_simulation_error: Option<String>,
    pub literal_markers: Vec<CuMarker>,
    pub literal_ledger: Option<AtomicProfile20CostLedger>,
    pub overlap_substituted_ledger: AtomicProfile20CostLedger,
    pub headroom_under_1_4m_cu: i64,
    pub wrong_terminal_rejected: bool,
    pub sound_acceptance_complete: bool,
    pub blockers: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile20AcceptanceSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub profile_id: u8,
    pub rho: &'static str,
    pub query_count: u16,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub statement_digest_sha256: String,
    pub proof_path: String,
    pub host_read_only_acceptance: bool,
    pub host_public_field_teeth: usize,
    pub host_corruption_teeth: usize,
    pub literal_simulation_cu: Option<u64>,
    pub literal_simulation_error: Option<String>,
    pub literal_markers: Vec<CuMarker>,
    pub literal_ledger: Option<AtomicProfile20CostLedger>,
    pub headroom_under_1_4m_cu: Option<i64>,
    pub pre_rewrite_literal_simulation_cu: u64,
    pub pre_rewrite_atomic_terminal_cu: u64,
    pub pre_rewrite_copy_patterns_cu: u64,
    pub optimized_copy_patterns_cu: u64,
    pub pre_rewrite_prepared_cu: u64,
    pub selected_shared_prepared_cu: u64,
    pub pre_rewrite_copy_routing_cu: u64,
    pub rank74_lazy_copy_routing_cu: u64,
    pub selected_shared_copy_routing_cu: u64,
    pub post_pattern_literal_simulation_cu: u64,
    pub rank74_lazy_literal_simulation_cu: u64,
    pub literal_savings_vs_pre_rewrite_cu: i64,
    pub random_qm31_pattern_identity_points: usize,
    pub wrong_public_field_rejected_sbf: bool,
    pub production_pow_mined: bool,
    pub read_only_acceptance_complete: bool,
    pub live_mutation_enabled: bool,
    pub atomic_hiding_rank_complete: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile20MutationLedger {
    pub transaction_setup_cu: u64,
    pub account_validation_cu: u64,
    pub statement_decode_and_digest_cu: u64,
    pub exact_profile20_verifier_cu: u64,
    pub marker_prepare_or_cpi_cu: u64,
    pub mutable_state_recheck_cu: u64,
    pub final_account_writes_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile20MutationPathSummary {
    pub marker_path: &'static str,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub incremental_over_tag46_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: AtomicProfile20MutationLedger,
    pub clean_simulation_accepted: bool,
    pub corrupt_proof_rejected_without_mutation: bool,
    pub committed_transition_succeeded: bool,
    pub pool_sequence_advanced_once: bool,
    pub pool_anchor_replaced: bool,
    pub nullifier_marker_written: bool,
    pub duplicate_rejected_without_second_mutation: bool,
    pub concurrent_exactly_one_committed: Option<bool>,
}

#[derive(Serialize)]
pub struct AtomicProfile20MutationSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub production_instruction_wire_ordinal: u8,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub diagnostic_sbf_features: Vec<&'static str>,
    pub proof_path: String,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub production_pow_bypass_exposed: bool,
    pub default_tag47_fail_closed_host: bool,
    pub candidate_tag47_rejects_unmined_sbf: bool,
    pub candidate_tag47_rollback_green: bool,
    pub paths: Vec<AtomicProfile20MutationPathSummary>,
    pub production_profile21_mutation_enabled: bool,
    pub atomic_complete_view_hiding_closed: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile21AcceptanceLedger {
    pub transaction_setup_cu: u64,
    pub proof_load_cu: u64,
    pub parse_base_cu: u64,
    pub transcript_base_cu: u64,
    pub terminal_cu: u64,
    pub relation_cu: u64,
    pub existing_openings_cu: u64,
    pub existing_queries_cu: u64,
    pub source_xf_shared_c2_cu: u64,
    pub source_work_cu: u64,
    pub translated_splice_cu: u64,
    pub direct_u_query_cu: u64,
    pub final_query_work_cu: u64,
    pub completion_cu: u64,
    pub wrapper_return_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile21AcceptanceSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub proof_path: String,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub masked_switch_basis_fingerprint: String,
    pub masked_switch_basis_fingerprint_matches_pin: bool,
    pub default_tag50_fail_closed_host: bool,
    pub production_api_rejected_unmined_sbf: bool,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: AtomicProfile21AcceptanceLedger,
    pub nonintegrated_read_only_bridge_cu: u64,
    pub nonintegrated_program_marker_bridge_cu: u64,
    pub nonintegrated_system_create_bridge_cu: u64,
    pub bridge_inputs: Vec<String>,
    pub soundness_reduction_complete: bool,
    pub complete_view_hvzk_simulator_complete: bool,
    pub production_mutation_enabled: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile21MutationLedger {
    pub transaction_setup_cu: u64,
    pub account_validation_cu: u64,
    pub statement_decode_and_digest_cu: u64,
    pub exact_profile21_verifier_cu: u64,
    pub marker_prepare_or_cpi_cu: u64,
    pub mutable_state_recheck_cu: u64,
    pub final_account_writes_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile21MutationPathSummary {
    pub marker_path: &'static str,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub incremental_over_tag50_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: AtomicProfile21MutationLedger,
    pub clean_simulation_accepted: bool,
    pub corrupt_proof_rejected_without_mutation: bool,
    pub committed_transition_succeeded: bool,
    pub pool_sequence_advanced_once: bool,
    pub pool_anchor_replaced: bool,
    pub nullifier_marker_written: bool,
    pub duplicate_rejected_without_second_mutation: bool,
    pub concurrent_exactly_one_committed: Option<bool>,
}

#[derive(Serialize)]
pub struct AtomicProfile21MutationSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub production_instruction_wire_ordinal: u8,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub diagnostic_sbf_features: Vec<&'static str>,
    pub proof_path: String,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub masked_switch_basis_fingerprint: String,
    pub production_pow_bypass_exposed: bool,
    pub default_tag51_fail_closed_host: bool,
    pub candidate_tag51_rejects_unmined_sbf: bool,
    pub candidate_tag51_rollback_green: bool,
    pub paths: Vec<AtomicProfile21MutationPathSummary>,
    pub soundness_reduction_complete: bool,
    pub complete_view_hvzk_simulator_complete: bool,
    pub production_profile21_mutation_enabled: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile22AcceptanceLedger {
    pub transaction_setup_cu: u64,
    pub proof_load_cu: u64,
    pub parsed_cu: u64,
    pub transcript_cu: u64,
    pub terminal_cu: u64,
    pub relation_cu: u64,
    pub openings_cu: u64,
    pub layer0_queries_cu: u64,
    pub later_queries_cu: u64,
    pub completion_cu: u64,
    pub wrapper_return_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile22AcceptanceSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub proof_path: String,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub batch_grinding_bits: u8,
    pub final_grinding_bits: u8,
    pub fold_grinding_bits: [u8; 4],
    pub soundness_bits_factor31: f64,
    pub soundness_bits_factor40: f64,
    pub default_tag56_fail_closed_host: bool,
    pub production_api_rejected_unmined_sbf: bool,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: AtomicProfile22AcceptanceLedger,
    pub production_mutation_enabled: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile22MutationLedger {
    pub transaction_setup_cu: u64,
    pub account_validation_cu: u64,
    pub statement_decode_and_digest_cu: u64,
    pub exact_profile22_verifier_cu: u64,
    pub marker_prepare_or_cpi_cu: u64,
    pub mutable_state_recheck_cu: u64,
    pub final_account_writes_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile22MutationPathSummary {
    pub marker_path: &'static str,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub incremental_over_tag56_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: AtomicProfile22MutationLedger,
    pub clean_simulation_accepted: bool,
    pub corrupt_proof_rejected_without_mutation: bool,
    pub committed_transition_succeeded: bool,
    pub pool_sequence_advanced_once: bool,
    pub pool_anchor_replaced: bool,
    pub nullifier_marker_written: bool,
    pub duplicate_rejected_without_second_mutation: bool,
    pub concurrent_exactly_one_committed: Option<bool>,
}

#[derive(Serialize)]
pub struct AtomicProfile22MutationSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub production_instruction_wire_ordinal: u8,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub diagnostic_sbf_features: Vec<&'static str>,
    pub proof_path: String,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub production_pow_bypass_exposed: bool,
    pub default_tag57_fail_closed_host: bool,
    pub candidate_tag57_rejects_unmined_sbf: bool,
    pub candidate_tag57_rollback_green: bool,
    pub paths: Vec<AtomicProfile22MutationPathSummary>,
    pub complete_system_claim_quotable: bool,
    pub complete_view_hvzk_simulator_complete: bool,
    pub production_profile22_mutation_enabled: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile23AcceptanceLedger {
    pub transaction_setup_cu: u64,
    pub proof_load_cu: u64,
    pub parsed_cu: u64,
    pub transcript_cu: u64,
    pub terminal_cu: u64,
    pub relation_cu: u64,
    pub openings_cu: u64,
    pub layer0_queries_cu: u64,
    pub later_queries_cu: u64,
    pub completion_cu: u64,
    pub wrapper_return_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile23AcceptanceSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub proof_path: String,
    pub proof_source_override: bool,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub statement_path: Option<String>,
    pub statement_source_override: bool,
    pub statement_sha256: Option<String>,
    pub statement_pool_hex: String,
    pub statement_sequence: u64,
    pub canonical_public_input_digest: String,
    pub batch_grinding_bits: u8,
    pub final_grinding_bits: u8,
    pub fold_grinding_bits: [u8; 4],
    pub query_selector_candidates: u8,
    pub rank_exhaustion_cap16_bits: f64,
    pub whole_soundness_bits_after_selector: f64,
    pub soundness_bookable: bool,
    pub proof_account_finalized_before_verification: bool,
    pub default_tag59_fail_closed_host: bool,
    pub production_api_rejected_unmined_sbf: bool,
    pub production_api_accepted_mined_sbf: bool,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: AtomicProfile23AcceptanceLedger,
    pub production_mutation_enabled: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct AtomicProfile23MutationLedger {
    pub transaction_setup_cu: u64,
    pub account_validation_cu: u64,
    pub statement_decode_and_digest_cu: u64,
    pub exact_profile23_verifier_cu: u64,
    pub marker_prepare_or_cpi_cu: u64,
    pub mutable_state_recheck_cu: u64,
    pub final_account_writes_cu: u64,
    pub post_last_marker_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile23MutationPathSummary {
    pub marker_path: &'static str,
    pub literal_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub incremental_over_tag59_cu: i64,
    pub markers: Vec<CuMarker>,
    pub ledger: AtomicProfile23MutationLedger,
    pub clean_simulation_accepted: bool,
    pub corrupt_proof_rejected_without_mutation: bool,
    pub committed_transition_succeeded: bool,
    pub pool_sequence_advanced_once: bool,
    pub pool_anchor_replaced: bool,
    pub nullifier_marker_written: bool,
    pub duplicate_rejected_without_second_mutation: bool,
    pub concurrent_exactly_one_committed: Option<bool>,
}

/// Overlap-subtracted ledger for the production-only Profile-23 binary.
///
/// Tag 60 deliberately has no diagnostic CU markers.  Its exact transaction
/// total is therefore reconciled against the exact read-only tag-59 total
/// measured in the same binary and validator configuration.  The signed
/// increment contains account validation, statement reconstruction, marker
/// preparation/creation, the mutable-state recheck and final writes, net of
/// the tag-59 wrapper it replaces.
#[derive(Serialize)]
pub struct AtomicProfile23ProductionMutationLedger {
    pub production_read_only_tag59_cu: u64,
    pub production_tag60_increment_over_tag59_cu: i64,
    pub production_tag60_total_cu: u64,
    pub reconciled_total_cu: u64,
    pub formula: String,
}

#[derive(Serialize)]
pub struct AtomicProfile23ProductionMutationPathSummary {
    pub marker_path: &'static str,
    pub proof_accounts_finalized_before_production_verification: bool,
    pub literal_tag59_simulation_cu: u64,
    pub literal_tag60_simulation_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub ledger: AtomicProfile23ProductionMutationLedger,
    pub production_unmined_tag59_rejected: bool,
    pub production_unmined_tag59_error: String,
    pub production_unmined_tag60_rejected: bool,
    pub production_unmined_tag60_rollback_green: bool,
    pub production_unmined_tag60_landed_error: String,
    pub production_tag59_accepted_mined_sbf: bool,
    pub production_tag60_clean_simulation_accepted: bool,
    pub corrupt_proof_rejected_with_transaction_rollback: bool,
    pub corrupt_transaction_landed_error: String,
    pub committed_transition_succeeded: bool,
    pub pool_sequence_advanced_once: bool,
    pub pool_anchor_replaced: bool,
    pub nullifier_marker_written: bool,
    pub duplicate_rejected_without_second_mutation: bool,
    pub concurrent_exactly_one_committed: Option<bool>,
}

#[derive(Serialize)]
pub struct AtomicProfile23MutationSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub production_instruction_wire_ordinal: u8,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub finalize_proof_instruction_wire_ordinal: u8,
    pub diagnostic_sbf_features: Vec<&'static str>,
    pub proof_path: String,
    pub proof_source_override: bool,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_unmined: bool,
    pub statement_path: Option<String>,
    pub statement_source_override: bool,
    pub statement_sha256: Option<String>,
    pub statement_pool_hex: String,
    pub statement_sequence: u64,
    pub canonical_public_input_digest: String,
    pub production_pow_bypass_exposed: bool,
    pub default_tag60_fail_closed_host: bool,
    pub candidate_tag60_rejects_unmined_sbf: bool,
    pub candidate_tag60_accepts_mined_sbf: bool,
    pub candidate_tag60_outcome_matches_pow: bool,
    pub candidate_tag60_rollback_green: bool,
    pub paths: Vec<AtomicProfile23MutationPathSummary>,
    pub production_only_sbf_features: Vec<&'static str>,
    pub production_only_sbf_bytes: Option<usize>,
    pub production_only_sbf_sha256: Option<String>,
    pub production_only_mined_override_exercised: bool,
    pub production_only_unmined_tag59_rejected: Option<bool>,
    pub production_only_unmined_tag60_rejected: Option<bool>,
    pub production_only_unmined_tag60_rollback_green: Option<bool>,
    pub production_only_tag59_diagnostic_bit_unavailable: Option<bool>,
    pub production_only_tag61_unavailable: Option<bool>,
    pub production_alias_forbidden_feature_unions_rejected: Option<bool>,
    pub production_alias_forbidden_feature_unions_tested: Vec<String>,
    pub production_paths: Vec<AtomicProfile23ProductionMutationPathSummary>,
    pub soundness_bookable: bool,
    pub complete_view_hvzk_simulator_complete: bool,
    pub production_profile23_mutation_enabled: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct StateOnlyRelationStructuralVariant {
    pub mode: &'static str,
    pub deferred_binary_copy: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub markers: Vec<CuMarker>,
    pub corruption_probe_cu: Option<u64>,
    pub corruption_rejected_host: bool,
    pub corruption_rejected_sbf: bool,
}

#[derive(Serialize)]
pub struct StateOnlyRelationStructuralSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub profile_id: u8,
    pub rho: &'static str,
    pub query_count: u16,
    pub proof_bytes: usize,
    pub variants: Vec<StateOnlyRelationStructuralVariant>,
    pub optimized_savings_cu: i64,
    pub legacy_relation_bucket_cu: u64,
    pub projected_optimized_relation_bucket_cu: i64,
    pub random_off_domain_identity_points: usize,
    pub exact_equivalence_scope: &'static str,
    pub overlap_scope: &'static str,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct HvzkMaskProbeRow {
    pub mask_log_inv_rate: u8,
    pub soundness_model: &'static str,
    pub mask_queries: u8,
    pub bits_per_query: f64,
    pub mask_domain_depths: [u32; 3],
    pub conditional_root_bound: bool,
    pub control_cu: u64,
    pub upstream_merkle_cu: u64,
    pub timing_batched_merkle_cu: u64,
    pub scalar_one_query_cu: u64,
    pub scalar_spot_checks_reconciled_cu: i64,
    pub batched_setup_cu: u64,
    pub batched_one_query_cu: u64,
    pub batched_spot_checks_reconciled_cu: i64,
    pub target_identity_cu: u64,
    pub upstream_transcript_cu: u64,
    pub timing_batched_transcript_cu: u64,
    pub upstream_reconciled_mask_verifier_cu: i64,
    pub timing_batched_reconciled_mask_verifier_cu: i64,
    pub upstream_incremental_proof_bytes: usize,
    pub timing_batched_incremental_proof_bytes: usize,
    pub optional_pow: Vec<HvzkMaskPowRow>,
}

#[derive(Clone, Serialize)]
pub struct HvzkMaskPowRow {
    pub bits: u8,
    pub root_bound_queries: u8,
    pub johnson_queries: u8,
    pub verifier_incremental_cu: i64,
    pub proof_bytes: usize,
    pub honest_expected_trials: String,
    pub johnson_timing_batched_mask_verifier_cu: i64,
    pub johnson_timing_batched_incremental_proof_bytes: usize,
}

#[derive(Serialize)]
pub struct HvzkMaskProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub upstream_commit: String,
    pub instruction_wire_ordinal: u8,
    pub internal_carried_groups: [u8; 7],
    pub internal_mask_codewords: u8,
    pub external_zerocheck_group_width: u8,
    pub source_padding: HvzkSourcePaddingProbe,
    pub direct_cm31_rs_decision: HvzkDirectCm31RsDecision,
    pub minimal_one_switch: HvzkOneSwitchProbe,
    pub rows: Vec<HvzkMaskProbeRow>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct HvzkOneSwitchProbe {
    pub message_len: usize,
    pub randomness_len: usize,
    pub domain_size: usize,
    pub domain_depth: u32,
    pub query_count: usize,
    pub johnson_query_bits: f64,
    pub positioned_work_bits: usize,
    pub combined_query_work_bits: f64,
    pub reaches_104_bits: bool,
    pub roots_fixed_before_work_required: bool,
    pub scalar_merkle_cu: i64,
    pub scalar_spot_cu: i64,
    pub optimized_single_word_spot_cu: i64,
    pub target_identity_cu: i64,
    pub transcript_cu: i64,
    pub scalar_reconciled_cu: i64,
    pub optimized_reconciled_cu: i64,
    pub incremental_proof_bytes: usize,
    pub shared_root_leaf_hash_delta_cu_per_lane: i64,
    pub shared_root_transcript_cu: i64,
    pub shared_root_lower_bound_cu: i64,
    pub shared_root_lower_bound_proof_bytes: usize,
    pub shared_root_conditions: &'static str,
    pub optional_source_reencode_incremental_cu: i64,
    pub source_reencode_required_for_isolated_switch_identity: bool,
    pub soundness_status: &'static str,
}

#[derive(Serialize)]
pub struct HvzkDirectCm31RsDecision {
    pub state_only_columns: usize,
    pub query_count: usize,
    pub circle_m31_leaf_bytes: usize,
    pub direct_cm31_leaf_bytes: usize,
    pub incremental_opened_leaf_bytes: usize,
    pub measured_double_limb_arithmetic_proxy_cu: i64,
    pub derived_leaf_hash_proxy_cu: i64,
    pub combined_verifier_delta_proxy_cu: i64,
    pub arithmetic_proxy_source: &'static str,
    pub hash_proxy_source: &'static str,
    pub theorem_transfer_status: &'static str,
}

#[derive(Serialize)]
pub struct HvzkSourcePaddingProbe {
    pub dimensions: [usize; 4],
    pub current_domains: [usize; 4],
    pub padded_domains: [usize; 4],
    pub padded_actual_rates: [f64; 4],
    pub every_padded_rate_at_most_one_over_32: bool,
    pub query_count: u8,
    pub current_merkle_cu: u64,
    pub padded_merkle_cu: u64,
    pub padded_minus_current_merkle_cu: i64,
    pub padded_minus_current_frontier_bytes: i64,
    pub source_base_spot_reencode_cu: u64,
    pub source_base_spot_reencode_incremental_cu: i64,
    pub fresh_main_merkle_cu: u64,
    pub fresh_main_merkle_incremental_cu: i64,
    pub total_new_source_side_incremental_cu: i64,
    pub q29_g36_johnson_shape_survives_rate_check: bool,
}

#[derive(Serialize)]
pub struct Radix4ProofVariant {
    pub merkle_mode: &'static str,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    /// Production `Verify` CU (the optimized path). Named `verify_cu`, not
    /// `verify_fast_cu`: `VerifyFast` survives only as a wire-compatible
    /// alias and the g32 runner has always measured `Verify` itself.
    pub verify_cu: Vec<u64>,
    pub verify_cu_mean: f64,
    pub host_corruption_cases: usize,
    pub host_corruption_all_rejected: bool,
}

#[derive(Serialize)]
pub struct Radix4G16Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub repetitions: usize,
    pub second_phase_enabled: bool,
    pub variants: Vec<Radix4ProofVariant>,
    pub radix4_savings_cu: i64,
    pub radix4_savings_percent: f64,
    pub radix4_proof_bytes_delta: i64,
    pub radix4_frontier_corruption_rejected_host: bool,
    pub radix4_frontier_corruption_rejected_sbf: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct Radix4G32Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub repetitions: usize,
    pub binary_proof_source: String,
    pub radix4_proof_source: String,
    pub radix4_generation_seconds: Option<f64>,
    pub binary_first_root: String,
    pub radix4_first_root: String,
    pub root_changed: bool,
    pub transcript_kat_unchanged: bool,
    pub variants: Vec<Radix4ProofVariant>,
    pub radix4_savings_cu: i64,
    pub radix4_savings_percent: f64,
    pub radix4_proof_bytes_delta: i64,
    pub radix4_frontier_corruption_rejected_host: bool,
    pub radix4_frontier_corruption_rejected_sbf: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct VarianceSeedSample {
    pub seed: u64,
    pub binary_proof_bytes: usize,
    pub binary_verify_cu: u64,
    pub radix4_proof_bytes: usize,
    pub radix4_verify_cu: u64,
    pub radix4_saving_cu: i64,
}

#[derive(Serialize)]
pub struct VarianceModeStats {
    pub merkle_mode: &'static str,
    pub per_seed_cu: Vec<u64>,
    pub mean_cu: f64,
    pub population_std_dev_cu: f64,
    pub min_cu: u64,
    pub max_cu: u64,
    pub range_cu: u64,
    pub max_minus_mean_cu: f64,
    pub mean_plus_two_sigma_cu: f64,
}

#[derive(Serialize)]
pub struct VarianceG16Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub seeds: u64,
    pub repetitions_per_seed: usize,
    pub criterion: String,
    pub samples: Vec<VarianceSeedSample>,
    pub binary_stats: VarianceModeStats,
    pub radix4_stats: VarianceModeStats,
    pub strict_candidate_projection_cu: i64,
    pub ten_percent_slack_maximum_cu: i64,
    pub single_draw_headroom_cu: i64,
    pub criterion_penalty_range_cu: u64,
    pub criterion_adjusted_projection_cu: i64,
    pub criterion_passes: bool,
    pub secondary_two_sigma_penalty_cu: f64,
    pub secondary_adjusted_projection_cu: i64,
    pub notes: Vec<String>,
}

fn variance_stats(merkle_mode: &'static str, per_seed_cu: Vec<u64>) -> VarianceModeStats {
    let n = per_seed_cu.len() as f64;
    let mean = per_seed_cu.iter().sum::<u64>() as f64 / n;
    let variance = per_seed_cu
        .iter()
        .map(|&cu| {
            let d = cu as f64 - mean;
            d * d
        })
        .sum::<f64>()
        / n;
    let sigma = variance.sqrt();
    let min = *per_seed_cu.iter().min().expect("nonempty seed set");
    let max = *per_seed_cu.iter().max().expect("nonempty seed set");
    VarianceModeStats {
        merkle_mode,
        mean_cu: mean,
        population_std_dev_cu: sigma,
        min_cu: min,
        max_cu: max,
        range_cu: max - min,
        max_minus_mean_cu: max as f64 - mean,
        mean_plus_two_sigma_cu: mean + 2.0 * sigma,
        per_seed_cu,
    }
}

#[derive(Serialize)]
pub struct FullPcsVerifierComparison {
    pub profile: &'static str,
    pub proof_bytes: usize,
    pub software_inverse_cu: Vec<u64>,
    pub software_inverse_cu_mean: f64,
    pub syscall_inverse_cu: Vec<u64>,
    pub syscall_inverse_cu_mean: f64,
    pub syscall_savings_cu: i64,
    pub circle_conjugate_cu: Vec<u64>,
    pub circle_conjugate_cu_mean: f64,
    pub circle_conjugate_savings_vs_software_cu: i64,
    pub diagnostic_profile_cu: Option<u64>,
    pub diagnostic_profile_markers: Vec<CuMarker>,
}

struct Validator {
    child: Child,
    rpc_url: String,
}

impl Drop for Validator {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

struct Rpc {
    url: String,
    http: reqwest::blocking::Client,
}

struct SimulationResult {
    units: Option<u64>,
    err: Option<String>,
    logs: Vec<String>,
}

impl Rpc {
    fn call(&self, method: &str, params: Value) -> Result<Value> {
        let response = self
            .http
            .post(&self.url)
            .json(&json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}))
            .send()
            .with_context(|| format!("rpc {method}"))?;
        let value: Value = response.json()?;
        if let Some(err) = value.get("error") {
            bail!("rpc {method} error: {err}");
        }
        value
            .get("result")
            .cloned()
            .ok_or_else(|| anyhow!("rpc {method}: missing result"))
    }

    fn latest_blockhash(&self) -> Result<solana_sdk::hash::Hash> {
        let result = self.call("getLatestBlockhash", json!([{"commitment": "processed"}]))?;
        let hash = result["value"]["blockhash"]
            .as_str()
            .ok_or_else(|| anyhow!("missing blockhash"))?;
        Ok(hash.parse()?)
    }

    fn airdrop_and_wait(&self, pubkey: &Pubkey, lamports: u64) -> Result<()> {
        self.call(
            "requestAirdrop",
            json!([pubkey.to_string(), lamports, {"commitment": "processed"}]),
        )?;
        let started = Instant::now();
        loop {
            let balance = self.call(
                "getBalance",
                json!([pubkey.to_string(), {"commitment": "processed"}]),
            )?;
            if balance["value"].as_u64().unwrap_or(0) >= lamports {
                return Ok(());
            }
            if started.elapsed() > Duration::from_secs(20) {
                bail!("airdrop timed out");
            }
            thread::sleep(Duration::from_millis(200));
        }
    }

    fn send_and_confirm(&self, tx: &Transaction) -> Result<u64> {
        let encoded = BASE64.encode(bincode::serialize(tx)?);
        let sig = self.call(
            "sendTransaction",
            json!([encoded, {"encoding": "base64", "preflightCommitment": "processed"}]),
        )?;
        let sig = sig.as_str().ok_or_else(|| anyhow!("missing signature"))?;
        let started = Instant::now();
        loop {
            let statuses = self.call(
                "getSignatureStatuses",
                json!([[sig], {"searchTransactionHistory": false}]),
            )?;
            let status = &statuses["value"][0];
            if !status.is_null() {
                if !status["err"].is_null() {
                    bail!("transaction failed: {}", status["err"]);
                }
                if status["confirmationStatus"].as_str().is_some() {
                    break;
                }
            }
            if started.elapsed() > Duration::from_secs(15) {
                bail!("confirmation timed out");
            }
            thread::sleep(Duration::from_millis(100));
        }
        // fetch CU from simulation-free path is awkward; use getTransaction meta
        let tx_info = self.call(
            "getTransaction",
            json!([sig, {"encoding": "json", "commitment": "confirmed", "maxSupportedTransactionVersion": 0}]),
        );
        Ok(tx_info
            .ok()
            .and_then(|t| t["meta"]["computeUnitsConsumed"].as_u64())
            .unwrap_or(0))
    }

    /// Submit without preflight and require the transaction to land with an
    /// execution error. This distinguishes ledger rollback from an RPC-side
    /// simulation rejection.
    fn send_and_confirm_failure(&self, tx: &Transaction) -> Result<String> {
        let encoded = BASE64.encode(bincode::serialize(tx)?);
        let sig = self.call(
            "sendTransaction",
            json!([encoded, {
                "encoding": "base64",
                "skipPreflight": true,
                "preflightCommitment": "processed"
            }]),
        )?;
        let sig = sig.as_str().ok_or_else(|| anyhow!("missing signature"))?;
        let started = Instant::now();
        loop {
            let statuses = self.call(
                "getSignatureStatuses",
                json!([[sig], {"searchTransactionHistory": false}]),
            )?;
            let status = &statuses["value"][0];
            if !status.is_null() {
                if !status["err"].is_null() {
                    return Ok(status["err"].to_string());
                }
                if status["confirmationStatus"].as_str().is_some() {
                    bail!("transaction unexpectedly succeeded: {sig}");
                }
            }
            if started.elapsed() > Duration::from_secs(15) {
                bail!("failed transaction confirmation timed out: {sig}");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    fn simulate_verbose(&self, tx: &Transaction) -> Result<SimulationResult> {
        let encoded = BASE64.encode(bincode::serialize(tx)?);
        let result = self.call(
            "simulateTransaction",
            json!([encoded, {"encoding": "base64", "sigVerify": false, "replaceRecentBlockhash": true, "commitment": "processed"}]),
        )?;
        let units = result["value"]["unitsConsumed"].as_u64();
        let logs = result["value"]["logs"]
            .as_array()
            .map(|logs| {
                logs.iter()
                    .filter_map(|log| log.as_str().map(str::to_string))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let err = if result["value"]["err"].is_null() {
            None
        } else {
            Some(format!(
                "{} logs={}",
                result["value"]["err"], result["value"]["logs"]
            ))
        };
        Ok(SimulationResult { units, err, logs })
    }

    /// Simulate and return (units_consumed, error).
    fn simulate(&self, tx: &Transaction) -> Result<(Option<u64>, Option<String>)> {
        let result = self.simulate_verbose(tx)?;
        Ok((result.units, result.err))
    }
}

fn workspace_root() -> Result<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    Ok(manifest
        .parent()
        .ok_or_else(|| anyhow!("no workspace root"))?
        .to_path_buf())
}

fn profile23_proof_path(root: &Path) -> (PathBuf, bool) {
    match std::env::var_os("ASPIS_PROFILE23_PROOF") {
        Some(path) => {
            let path = PathBuf::from(path);
            let path = if path.is_absolute() {
                path
            } else {
                root.join(path)
            };
            (path, true)
        }
        None => (
            root.join("results/stage2/proofs/atomic_state_only_profile23_v3_unmined.bin"),
            false,
        ),
    }
}

const PROFILE23_STATEMENT_ARTIFACT: &str = "profile23_production_statement";
const PROFILE23_STATEMENT_SELECTION_RULE: &str =
    "least Good23 selector from three post-final branches";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Profile23StatementSidecar {
    artifact: String,
    pool_hex: String,
    sequence: u64,
    current_anchor_hex: String,
    nullifier_hex: String,
    output_commitment_hex: String,
    output_anchor_hex: String,
    asset_id: u32,
    fee: u32,
    selection_rule: String,
    witness_independent_public_metadata: bool,
}

#[derive(Debug)]
struct Profile23StatementSelection {
    statement: aspis_statement::AtomicPaymentStatementV3,
    path: Option<PathBuf>,
    source_override: bool,
    sha256: Option<String>,
    canonical_public_input_digest: String,
}

fn profile23_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_profile23_hex_32(field: &str, value: &str) -> Result<[u8; 32]> {
    let bytes = value.as_bytes();
    ensure!(
        bytes.len() == 64,
        "Profile23 statement sidecar {field} must contain exactly 64 lowercase hex characters"
    );
    ensure!(
        bytes
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte)),
        "Profile23 statement sidecar {field} is not canonical lowercase hex"
    );
    let mut decoded = [0u8; 32];
    for (index, output) in decoded.iter_mut().enumerate() {
        let high = match bytes[index * 2] {
            b'0'..=b'9' => bytes[index * 2] - b'0',
            byte => byte - b'a' + 10,
        };
        let low = match bytes[index * 2 + 1] {
            b'0'..=b'9' => bytes[index * 2 + 1] - b'0',
            byte => byte - b'a' + 10,
        };
        *output = (high << 4) | low;
    }
    Ok(decoded)
}

fn profile23_statement_from_sidecar(
    sidecar: Profile23StatementSidecar,
) -> Result<aspis_statement::AtomicPaymentStatementV3> {
    ensure!(
        sidecar.artifact == PROFILE23_STATEMENT_ARTIFACT,
        "Profile23 statement sidecar artifact must be {PROFILE23_STATEMENT_ARTIFACT}"
    );
    ensure!(
        sidecar.selection_rule == PROFILE23_STATEMENT_SELECTION_RULE,
        "Profile23 statement sidecar selection_rule drift"
    );
    ensure!(
        sidecar.witness_independent_public_metadata,
        "Profile23 statement sidecar must declare witness-independent public metadata"
    );

    let current_anchor_bytes =
        decode_profile23_hex_32("current_anchor_hex", &sidecar.current_anchor_hex)?;
    let nullifier_bytes = decode_profile23_hex_32("nullifier_hex", &sidecar.nullifier_hex)?;
    let output_commitment_bytes =
        decode_profile23_hex_32("output_commitment_hex", &sidecar.output_commitment_hex)?;
    let output_anchor_bytes =
        decode_profile23_hex_32("output_anchor_hex", &sidecar.output_anchor_hex)?;
    let statement = aspis_statement::AtomicPaymentStatementV3 {
        pool: decode_profile23_hex_32("pool_hex", &sidecar.pool_hex)?,
        sequence: sidecar.sequence,
        spend: aspis_statement::SpendPublic {
            anchor: aspis_statement::decode_digest_canonical(&current_anchor_bytes).map_err(
                |_| anyhow!("Profile23 statement sidecar current_anchor_hex is noncanonical"),
            )?,
            nullifier: aspis_statement::decode_digest_canonical(&nullifier_bytes).map_err(
                |_| anyhow!("Profile23 statement sidecar nullifier_hex is noncanonical"),
            )?,
            output_commitment: aspis_statement::decode_digest_canonical(&output_commitment_bytes)
                .map_err(|_| {
                anyhow!("Profile23 statement sidecar output_commitment_hex is noncanonical")
            })?,
            asset_id: aspis_statement::decode_asset_id_canonical(sidecar.asset_id)
                .map_err(|_| anyhow!("Profile23 statement sidecar asset_id is noncanonical"))?,
            fee: sidecar.fee,
        },
        output_anchor: aspis_statement::decode_digest_canonical(&output_anchor_bytes).map_err(
            |_| anyhow!("Profile23 statement sidecar output_anchor_hex is noncanonical"),
        )?,
    };
    aspis_statement::encode_atomic_payment_statement_v3(&statement)
        .map_err(|error| anyhow!("Profile23 statement sidecar is noncanonical: {error:?}"))?;
    Ok(statement)
}

fn decode_profile23_statement_sidecar(
    bytes: &[u8],
) -> Result<aspis_statement::AtomicPaymentStatementV3> {
    let sidecar: Profile23StatementSidecar =
        serde_json::from_slice(bytes).context("decode canonical Profile23 statement sidecar")?;
    profile23_statement_from_sidecar(sidecar)
}

fn profile23_fixture_statement() -> Result<aspis_statement::AtomicPaymentStatementV3> {
    use aspis_core::field::M31;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment, Digest, MerklePath,
        SpendPublic,
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
        index: 0x5_a5a5,
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    Ok(aspis_statement::AtomicPaymentStatementV3 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &path)
                .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &path)
            .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
    })
}

fn profile23_statement_selection_from_path(
    root: &Path,
    proof_source_override: bool,
    statement_path: Option<PathBuf>,
) -> Result<Profile23StatementSelection> {
    use sha2::Digest as _;

    let (statement, path, source_override, sha256) = match statement_path {
        Some(path) => {
            ensure!(
                proof_source_override,
                "ASPIS_PROFILE23_STATEMENT requires ASPIS_PROFILE23_PROOF"
            );
            let path = if path.is_absolute() {
                path
            } else {
                root.join(path)
            };
            let path = fs::canonicalize(&path).with_context(|| {
                format!("resolve Profile23 statement sidecar {}", path.display())
            })?;
            let bytes = fs::read(&path)
                .with_context(|| format!("read Profile23 statement sidecar {}", path.display()))?;
            let statement = decode_profile23_statement_sidecar(&bytes).with_context(|| {
                format!(
                    "decode canonical Profile23 statement sidecar {}",
                    path.display()
                )
            })?;
            let sha256 = profile23_hex(&sha2::Sha256::digest(&bytes));
            (statement, Some(path), true, Some(sha256))
        }
        None => (profile23_fixture_statement()?, None, false, None),
    };
    let canonical_public_input_digest = profile23_hex(
        &aspis_statement::atomic_payment_statement_digest_v3(&statement, HOST_HASH)
            .map_err(|error| anyhow!("canonical Profile23 public-input digest: {error:?}"))?,
    );
    Ok(Profile23StatementSelection {
        statement,
        path,
        source_override,
        sha256,
        canonical_public_input_digest,
    })
}

fn profile23_statement_selection(
    root: &Path,
    proof_source_override: bool,
) -> Result<Profile23StatementSelection> {
    profile23_statement_selection_from_path(
        root,
        proof_source_override,
        std::env::var_os("ASPIS_PROFILE23_STATEMENT").map(PathBuf::from),
    )
}

fn profile23_recorded_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

#[cfg(test)]
mod profile23_statement_sidecar_tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use serde_json::{json, Value};
    use sha2::Digest as _;

    use super::*;

    static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

    struct TempRoot(PathBuf);

    impl TempRoot {
        fn new() -> Self {
            let suffix = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-profile23-statement-{}-{suffix}",
                std::process::id()
            ));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for TempRoot {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn sidecar(statement: &aspis_statement::AtomicPaymentStatementV3) -> Value {
        json!({
            "artifact": PROFILE23_STATEMENT_ARTIFACT,
            "pool_hex": profile23_hex(&statement.pool),
            "sequence": statement.sequence,
            "current_anchor_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.anchor)
            ),
            "nullifier_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.nullifier)
            ),
            "output_commitment_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.output_commitment)
            ),
            "output_anchor_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.output_anchor)
            ),
            "asset_id": statement.spend.asset_id.0,
            "fee": statement.spend.fee,
            "selection_rule": PROFILE23_STATEMENT_SELECTION_RULE,
            "witness_independent_public_metadata": true,
        })
    }

    #[test]
    fn canonical_sidecar_reconstructs_every_public_field() {
        let mut expected = profile23_fixture_statement().unwrap();
        expected.pool = [0x42; 32];
        expected.sequence = 91;
        let bytes = serde_json::to_vec_pretty(&sidecar(&expected)).unwrap();

        let decoded = decode_profile23_statement_sidecar(&bytes).unwrap();
        assert_eq!(decoded, expected);
        let digest =
            aspis_statement::atomic_payment_statement_digest_v3(&decoded, HOST_HASH).unwrap();
        assert_eq!(profile23_hex(&digest).len(), 64);
    }

    #[test]
    fn sidecar_rejects_noncanonical_fields_and_schema_drift() {
        let statement = profile23_fixture_statement().unwrap();

        let mut uppercase = sidecar(&statement);
        uppercase["pool_hex"] = Value::String("AA".repeat(32));
        let error = decode_profile23_statement_sidecar(&serde_json::to_vec(&uppercase).unwrap())
            .unwrap_err();
        assert!(error.to_string().contains("canonical lowercase hex"));

        let mut noncanonical_digest = sidecar(&statement);
        let mut digest = [0u8; 32];
        digest[..4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
        noncanonical_digest["current_anchor_hex"] = Value::String(profile23_hex(&digest));
        let error =
            decode_profile23_statement_sidecar(&serde_json::to_vec(&noncanonical_digest).unwrap())
                .unwrap_err();
        assert!(error
            .to_string()
            .contains("current_anchor_hex is noncanonical"));

        let mut invalid_fee = sidecar(&statement);
        invalid_fee["fee"] = Value::from(aspis_statement::VALUE_LIMIT);
        let error = decode_profile23_statement_sidecar(&serde_json::to_vec(&invalid_fee).unwrap())
            .unwrap_err();
        assert!(error.to_string().contains("FeeOutOfRange"));

        let mut unknown_field = sidecar(&statement);
        unknown_field["unreviewed"] = Value::Bool(true);
        let error =
            decode_profile23_statement_sidecar(&serde_json::to_vec(&unknown_field).unwrap())
                .unwrap_err();
        assert!(format!("{error:#}").contains("unknown field"));
    }

    #[test]
    fn explicit_sidecar_requires_proof_override_and_records_exact_identity() {
        let root = TempRoot::new();
        let mut expected = profile23_fixture_statement().unwrap();
        expected.pool = [0x24; 32];
        expected.sequence = 107;
        let bytes = serde_json::to_vec_pretty(&sidecar(&expected)).unwrap();
        let relative = PathBuf::from("statement.json");
        fs::write(root.0.join(&relative), &bytes).unwrap();

        let error = profile23_statement_selection_from_path(&root.0, false, Some(relative.clone()))
            .unwrap_err();
        assert!(error.to_string().contains("requires ASPIS_PROFILE23_PROOF"));

        let selected =
            profile23_statement_selection_from_path(&root.0, true, Some(relative)).unwrap();
        assert_eq!(selected.statement, expected);
        assert!(selected.source_override);
        assert_eq!(
            selected.path.as_deref(),
            Some(
                fs::canonicalize(root.0.join("statement.json"))
                    .unwrap()
                    .as_path()
            )
        );
        assert_eq!(
            selected.sha256.as_deref(),
            Some(profile23_hex(&sha2::Sha256::digest(&bytes)).as_str())
        );
        let expected_digest =
            aspis_statement::atomic_payment_statement_digest_v3(&selected.statement, HOST_HASH)
                .unwrap();
        assert_eq!(
            selected.canonical_public_input_digest,
            profile23_hex(&expected_digest)
        );

        let default = profile23_statement_selection_from_path(&root.0, false, None).unwrap();
        assert_eq!(default.statement, profile23_fixture_statement().unwrap());
        assert!(!default.source_override);
        assert!(default.path.is_none());
        assert!(default.sha256.is_none());
        assert_eq!(
            default.canonical_public_input_digest,
            "52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9"
        );
    }

    #[test]
    fn built_in_fixture_preserves_committed_unmined_negative_kat() {
        use aspis_statement::state_only_profile23::{
            verify_atomic_state_only_profile23_unmined_for_diagnostics_v3,
            verify_atomic_state_only_profile23_v3,
        };

        let root = workspace_root().unwrap();
        let proof =
            fs::read(root.join("results/stage2/proofs/atomic_state_only_profile23_v3_unmined.bin"))
                .unwrap();
        let statement = profile23_fixture_statement().unwrap();
        verify_atomic_state_only_profile23_unmined_for_diagnostics_v3(
            &proof, &statement, HOST_HASH, None,
        )
        .unwrap();
        assert!(
            verify_atomic_state_only_profile23_v3(&proof, &statement, HOST_HASH, None).is_err()
        );
    }
}

fn build_sbf(root: &Path) -> Result<PathBuf> {
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .arg("--manifest-path")
        .arg(root.join("programs/aspis-verifier/Cargo.toml"))
        // Historical/probe runners require a stable feature-empty binary.
        // The final release gate builds the package default explicitly and
        // compares it with the pinned production-only Profile23 SBF.
        .arg("--no-default-features")
        .status()
        .context("cargo-build-sbf not found on PATH — install the Solana toolchain")?;
    if !status.success() {
        bail!("cargo-build-sbf failed");
    }
    let so = root.join("target/deploy/aspis_verifier.so");
    if !so.exists() {
        bail!("missing {}", so.display());
    }
    Ok(so)
}

fn build_sbf_with_features(root: &Path, features: &[&str], pinned_name: &str) -> Result<PathBuf> {
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .arg("--manifest-path")
        .arg(root.join("programs/aspis-verifier/Cargo.toml"))
        .arg("--no-default-features")
        .arg("--features")
        .arg(features.join(","))
        .status()
        .context("cargo-build-sbf not found on PATH — install the Solana toolchain")?;
    if !status.success() {
        bail!("cargo-build-sbf with features {features:?} failed");
    }
    let built = root.join("target/deploy/aspis_verifier.so");
    if !built.exists() {
        bail!("missing {}", built.display());
    }
    let pinned = root.join("target/deploy").join(pinned_name);
    fs::copy(&built, &pinned)
        .with_context(|| format!("pin diagnostic SBF {}", pinned.display()))?;
    Ok(pinned)
}

/// Build the final Profile23 binary in the same Cargo feature context as a
/// plain package-default deployment, while redundantly naming the reviewed
/// production alias for artifact provenance.  Unlike diagnostic and historic
/// probe builds, this deliberately does not pass `--no-default-features`.
fn build_profile23_production_default_sbf(
    root: &Path,
    requested_features: &[&str],
    pinned_name: &str,
) -> Result<PathBuf> {
    ensure!(
        requested_features == ["profile23-production"],
        "Profile23 production/default SBF must request only the reviewed production alias"
    );
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .arg("--manifest-path")
        .arg(root.join("programs/aspis-verifier/Cargo.toml"))
        .arg("--features")
        .arg(requested_features.join(","))
        .status()
        .context("cargo-build-sbf not found on PATH — install the Solana toolchain")?;
    if !status.success() {
        bail!(
            "cargo-build-sbf for Profile23 production/default alias {requested_features:?} failed"
        );
    }
    let built = root.join("target/deploy/aspis_verifier.so");
    if !built.exists() {
        bail!("missing {}", built.display());
    }
    let pinned = root.join("target/deploy").join(pinned_name);
    fs::copy(&built, &pinned)
        .with_context(|| format!("pin Profile23 production/default SBF {}", pinned.display()))?;
    Ok(pinned)
}

/// Prove that the final Profile23 production alias cannot be feature-unified
/// with a PoW bypass or an older statement candidate.  Each forbidden feature
/// is checked independently so one working guard cannot hide a missing guard,
/// and the combined invocation catches cfg expressions that behave differently
/// when several families are enabled at once.
///
/// The production KAT names the reviewed `profile23-production` alias, so every
/// forbidden union must fail with the dedicated verifier compile-error marker
/// rather than an unrelated build failure.
fn check_profile23_production_feature_isolation(
    root: &Path,
    production_features: &[&str],
) -> Result<(Option<bool>, Vec<String>)> {
    const PRODUCTION_ALIAS: &str = "profile23-production";
    const FORBIDDEN: [&str; 11] = [
        "diagnostic-unmined-mutation",
        "diagnostic-unmined-profile21-mutation",
        "diagnostic-unmined-profile22-acceptance",
        "diagnostic-unmined-profile22-mutation",
        "diagnostic-unmined-profile23-acceptance",
        "diagnostic-unmined-profile23-mutation",
        "profile20-mutation-candidate",
        "profile21-integrated-candidate",
        "profile21-mutation-candidate",
        "profile22-integrated-candidate",
        "profile22-mutation-candidate",
    ];
    const EXPECTED_COMPILE_ERROR_MARKER: &str = "PROFILE23_PRODUCTION_FEATURE_ISOLATION";

    if production_features != [PRODUCTION_ALIAS] {
        return Ok((None, Vec::new()));
    }

    fn require_compile_failure(root: &Path, enabled_features: &str, label: &str) -> Result<()> {
        let output = Command::new("cargo")
            .env("NO_DNA", "1")
            .current_dir(root)
            .args([
                "check",
                "-p",
                "aspis-verifier",
                "--no-default-features",
                "--features",
                enabled_features,
            ])
            .output()
            .with_context(|| format!("run Profile23 feature-isolation tooth {label}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        ensure!(
            !output.status.success(),
            "forbidden Profile23 feature union unexpectedly compiled: {label}"
        );
        ensure!(
            stdout.contains(EXPECTED_COMPILE_ERROR_MARKER)
                || stderr.contains(EXPECTED_COMPILE_ERROR_MARKER),
            "Profile23 feature union {label} failed for an unrelated reason; expected marker {EXPECTED_COMPILE_ERROR_MARKER}; stdout={stdout}; stderr={stderr}"
        );
        Ok(())
    }

    let mut tested = Vec::with_capacity(FORBIDDEN.len() + 1);
    for forbidden in FORBIDDEN {
        let label = format!("{PRODUCTION_ALIAS}+{forbidden}");
        let enabled = format!("{PRODUCTION_ALIAS},{forbidden}");
        require_compile_failure(root, &enabled, &label)?;
        tested.push(label);
    }

    let all_forbidden = FORBIDDEN.join(",");
    let enabled = format!("{PRODUCTION_ALIAS},{all_forbidden}");
    let label = format!("{PRODUCTION_ALIAS}+all-forbidden");
    require_compile_failure(root, &enabled, &label)?;
    tested.push(label);

    Ok((Some(true), tested))
}

fn free_ports(count: usize) -> Result<Vec<u16>> {
    // Hold every listener until all ports have been selected so the OS
    // cannot hand the same ephemeral port back to a later request.
    let listeners = (0..count)
        .map(|_| TcpListener::bind("127.0.0.1:0"))
        .collect::<std::io::Result<Vec<_>>>()?;
    listeners
        .iter()
        .map(|listener| Ok(listener.local_addr()?.port()))
        .collect()
}

fn start_validator(root: &Path, so: &Path) -> Result<Validator> {
    start_validator_with_accounts(root, so, &[])
}

fn start_validator_with_accounts(
    root: &Path,
    so: &Path,
    accounts: &[(Pubkey, PathBuf)],
) -> Result<Validator> {
    let ledger = root.join(".stage0-validator");
    let _ = fs::remove_dir_all(&ledger);
    let ports = free_ports(3)?;
    let (rpc_port, faucet_port, gossip_port) = (ports[0], ports[1], ports[2]);
    let mut command = Command::new("solana-test-validator");
    command
        .env("NO_DNA", "1")
        .arg("--reset")
        .arg("--quiet")
        .arg("--ledger")
        .arg(&ledger)
        .arg("--rpc-port")
        .arg(rpc_port.to_string())
        .arg("--faucet-port")
        .arg(faucet_port.to_string())
        .arg("--gossip-port")
        .arg(gossip_port.to_string())
        .arg("--bpf-program")
        .arg(aspis_verifier::id().to_string())
        .arg(so);
    for (address, path) in accounts {
        command.arg("--account").arg(address.to_string()).arg(path);
    }
    let child = command
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .context("solana-test-validator not found on PATH")?;
    let mut validator = Validator {
        child,
        rpc_url: format!("http://127.0.0.1:{rpc_port}"),
    };
    // wait for RPC
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let started = Instant::now();
    loop {
        if rpc.call("getHealth", json!([])).is_ok() {
            break;
        }
        if let Some(status) = validator.child.try_wait()? {
            bail!("validator exited before RPC became healthy: {status}");
        }
        if started.elapsed() > Duration::from_secs(90) {
            bail!("validator did not become healthy");
        }
        thread::sleep(Duration::from_millis(500));
    }
    Ok(validator)
}

fn proof_instruction(
    payer: &Pubkey,
    proof_account: &Pubkey,
    instruction: &AspisInstruction,
) -> Result<Instruction> {
    let proof_account_signer = matches!(instruction, AspisInstruction::InitProof { .. });
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![
            AccountMeta::new(*proof_account, proof_account_signer),
            AccountMeta::new_readonly(*payer, true),
        ],
        data: to_vec(instruction)?,
    })
}

#[derive(Serialize)]
pub struct StateOnlyMaskedSwitchProfile21Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub profile_label: String,
    pub line_code_length: usize,
    pub line_code_dimension: usize,
    pub query_count: usize,
    pub source_work_bits: u8,
    pub final_work_bits: u8,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub upload_chunks: usize,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    /// Exact scalar M31 sparse-fold reference.
    pub direct_q_reference_simulation_cu: Vec<u64>,
    pub direct_q_reference_simulation_cu_mean: f64,
    /// Exact generic-QM31 sparse-fold reference retained to make the full
    /// representation saving reproducible in the same artifact.
    pub generic_qm31_reference_simulation_cu: Vec<u64>,
    pub generic_qm31_reference_simulation_cu_mean: f64,
    pub measured_four_query_fusion_savings_cu: f64,
    pub measured_direct_q_evaluation_savings_cu: f64,
    pub measured_u_tree_replacement_bucket_cu: u64,
    pub overlap_subtracted_incremental_estimate_cu: f64,
    pub markers: Vec<CuMarker>,
    pub host_fixture_accepted: bool,
    pub production_api_rejected_unmined: bool,
    pub stale_statement_rejected_onchain: bool,
    pub corrupted_root_rejected_onchain: bool,
    pub sound_acceptance_complete: bool,
    pub explicit_nonclaims: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct StateOnlyPrivateMerkleSaltProbeRow {
    pub mode: u8,
    pub label: &'static str,
    pub opened_leaf_lengths: Vec<usize>,
    pub salted: bool,
    pub leaf_hash_calls: usize,
    pub expected_sink_hex: String,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct StateOnlyPrivateMerkleSaltProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub query_count: usize,
    pub distinct_opened_leaves_per_tree: usize,
    pub rows: Vec<StateOnlyPrivateMerkleSaltProbeRow>,
    pub shared_c2_leaf_widening_delta_cu: i64,
    pub all_five_tree_private_salt_delta_cu: i64,
    pub conservative_booked_private_salt_delta_cu: i64,
    pub dedicated_xf_tree_measured_bucket_cu: i64,
    pub shared_root_net_saving_before_salts_cu: i64,
    pub literal_micro_shared_root_net_saving_after_salts_cu: i64,
    pub shared_root_net_saving_after_salts_cu: i64,
    pub salt_wire_delta_bytes: usize,
    pub shared_c2_opened_value_wire_delta_bytes: usize,
    pub production_salted_leaf_hash: &'static str,
    pub explicit_nonclaims: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct StateOnlyHelperDot2ProbeRow {
    pub fused_helpers: bool,
    pub label: &'static str,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct StateOnlyHelperDot2ProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub query_count: usize,
    pub c1_columns: usize,
    pub qm31_helper_lanes: usize,
    pub rows: Vec<StateOnlyHelperDot2ProbeRow>,
    pub measured_savings_cu: i64,
    pub host_outputs_equal: bool,
    pub c1_noncanonical_rejected_both: bool,
    pub c2_noncanonical_rejected_both: bool,
    pub soundness_neutral: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct StateOnlyHelperDot3ProbeRow {
    pub fused_helpers: bool,
    pub label: &'static str,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct StateOnlyHelperDot3ProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub query_count: usize,
    pub fiber_slots: usize,
    pub qm31_helper_lanes: usize,
    pub rows: Vec<StateOnlyHelperDot3ProbeRow>,
    pub measured_savings_cu: i64,
    pub host_outputs_equal: bool,
    pub noncanonical_qm31_rejected_both: bool,
    pub soundness_neutral: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct StateOnlyFoldPolynomialProbeRow {
    pub polynomial_basis: bool,
    pub label: &'static str,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct StateOnlyFoldPolynomialProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub query_count: usize,
    pub folds_per_query: usize,
    pub rows: Vec<StateOnlyFoldPolynomialProbeRow>,
    pub measured_savings_cu: i64,
    pub host_outputs_equal: bool,
    pub random_off_domain_identity_cases: usize,
    pub noncanonical_qm31_rejected_both: bool,
    pub soundness_neutral: bool,
    pub notes: Vec<String>,
}

pub fn run_stage2_state_only_helper_dot2_probe() -> Result<StateOnlyHelperDot2ProbeSummary> {
    let expected_reference = aspis_verifier::state_only_helper_dot2_probe_sink(false, 0)
        .map_err(|error| anyhow!("host helper-dot2 reference failed: {error:?}"))?;
    let expected_fused = aspis_verifier::state_only_helper_dot2_probe_sink(true, 0)
        .map_err(|error| anyhow!("host helper-dot2 candidate failed: {error:?}"))?;
    ensure!(
        expected_fused == expected_reference,
        "helper-dot2 host differential failed"
    );

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut rows = Vec::with_capacity(2);
    for (fused_helpers, label) in [(false, "independent_products"), (true, "lazy_dot2")] {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StateOnlyHelperDot2Probe {
                fused_helpers,
                corrupt: 0,
                expected_sink: expected_reference,
            })?,
        };
        ensure!(
            instruction.data.first() == Some(&53),
            "helper-dot2 tag drifted"
        );
        let simulation_cu =
            simulate_pure_instruction(&rpc, &payer, instruction, VERIFY_REPETITIONS)
                .with_context(|| format!("helper-dot2 {label}"))?;
        ensure!(
            simulation_cu.iter().all(|&value| value == simulation_cu[0]),
            "helper-dot2 {label} was nondeterministic: {simulation_cu:?}"
        );
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        rows.push(StateOnlyHelperDot2ProbeRow {
            fused_helpers,
            label,
            simulation_cu,
            simulation_cu_mean,
        });
    }

    let mut rejected = [true; 2];
    for (corrupt_index, corrupt) in [1u8, 2].into_iter().enumerate() {
        for fused_helpers in [false, true] {
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&AspisInstruction::StateOnlyHelperDot2Probe {
                    fused_helpers,
                    corrupt,
                    expected_sink: [0u8; 32],
                })?,
            };
            rejected[corrupt_index] &=
                simulate_pure_instruction(&rpc, &payer, instruction, 1).is_ok();
        }
    }
    ensure!(rejected[0], "helper-dot2 C1 corruption tooth failed");
    ensure!(rejected[1], "helper-dot2 C2 corruption tooth failed");
    let measured_savings_cu =
        (rows[0].simulation_cu_mean - rows[1].simulation_cu_mean).round() as i64;
    drop(validator);

    Ok(StateOnlyHelperDot2ProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command:
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-state-only-helper-dot2-probe"
                .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 53,
        query_count: 16,
        c1_columns: aspis_core::state_only_query::STATE_ONLY_C1_COLUMNS,
        qm31_helper_lanes: aspis_core::state_only_query::STATE_ONLY_C2_COLUMNS,
        rows,
        measured_savings_cu,
        host_outputs_equal: true,
        c1_noncanonical_rejected_both: rejected[0],
        c2_noncanonical_rejected_both: rejected[1],
        soundness_neutral: true,
        notes: vec![
            "Both arms execute the identical 26-column C1 canonical byte dot and sixteen varied four-slot fibers. Only the two helper products' reduction schedule changes.".to_string(),
            "The candidate retains all 18 helper M31 products but reduces their nine Karatsuba channels once per slot instead of once per product.".to_string(),
            "This is an isolated arithmetic A/B. If the pending soundness repair adds X as a third main QM31 lane, the same construction must be remeasured as an exact prepared dot3 before integration.".to_string(),
        ],
    })
}

pub fn run_stage2_state_only_helper_dot3_probe() -> Result<StateOnlyHelperDot3ProbeSummary> {
    let expected_reference = aspis_verifier::state_only_helper_dot3_probe_sink(false, 0)
        .map_err(|error| anyhow!("host helper-dot3 reference failed: {error:?}"))?;
    let expected_fused = aspis_verifier::state_only_helper_dot3_probe_sink(true, 0)
        .map_err(|error| anyhow!("host helper-dot3 candidate failed: {error:?}"))?;
    ensure!(
        expected_fused == expected_reference,
        "helper-dot3 host differential failed"
    );

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut rows = Vec::with_capacity(2);
    for (fused_helpers, label) in [(false, "independent_products"), (true, "lazy_dot3")] {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StateOnlyHelperDot3Probe {
                fused_helpers,
                corrupt: 0,
                expected_sink: expected_reference,
            })?,
        };
        ensure!(
            instruction.data.first() == Some(&54),
            "helper-dot3 tag drifted"
        );
        let simulation_cu =
            simulate_pure_instruction(&rpc, &payer, instruction, VERIFY_REPETITIONS)
                .with_context(|| format!("helper-dot3 {label}"))?;
        ensure!(
            simulation_cu.iter().all(|&value| value == simulation_cu[0]),
            "helper-dot3 {label} was nondeterministic: {simulation_cu:?}"
        );
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        rows.push(StateOnlyHelperDot3ProbeRow {
            fused_helpers,
            label,
            simulation_cu,
            simulation_cu_mean,
        });
    }

    let mut noncanonical_rejected_both = true;
    for fused_helpers in [false, true] {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StateOnlyHelperDot3Probe {
                fused_helpers,
                corrupt: 1,
                expected_sink: [0u8; 32],
            })?,
        };
        noncanonical_rejected_both &=
            simulate_pure_instruction(&rpc, &payer, instruction, 1).is_ok();
    }
    ensure!(
        noncanonical_rejected_both,
        "helper-dot3 QM31 canonicality tooth failed"
    );
    let measured_savings_cu =
        (rows[0].simulation_cu_mean - rows[1].simulation_cu_mean).round() as i64;
    drop(validator);

    Ok(StateOnlyHelperDot3ProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command:
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-state-only-helper-dot3-probe"
                .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 54,
        query_count: 16,
        fiber_slots: 4,
        qm31_helper_lanes: 3,
        rows,
        measured_savings_cu,
        host_outputs_equal: true,
        noncanonical_qm31_rejected_both: noncanonical_rejected_both,
        soundness_neutral: true,
        notes: vec![
            "Both arms canonically decode the identical sixteen four-slot, three-QM31-lane fibers and use the same prepared gamma^26, gamma^27, and gamma^28 factors.".to_string(),
            "The candidate retains all 27 M31 products per slot but reduces the nine Karatsuba channels once for the three-product dot instead of once per QM31 product.".to_string(),
            "This is an isolated arithmetic A/B for the pending repaired main-RLC shape. It does not implement, price, or assert the X carry repair itself.".to_string(),
        ],
    })
}

pub fn run_stage2_state_only_fold_polynomial_probe() -> Result<StateOnlyFoldPolynomialProbeSummary>
{
    let expected_nested = aspis_verifier::state_only_fold_polynomial_probe_sink(false, 0)
        .map_err(|error| anyhow!("host nested-fold reference failed: {error:?}"))?;
    let expected_polynomial = aspis_verifier::state_only_fold_polynomial_probe_sink(true, 0)
        .map_err(|error| anyhow!("host polynomial-fold candidate failed: {error:?}"))?;
    ensure!(
        expected_polynomial == expected_nested,
        "fold polynomial host differential failed"
    );

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut rows = Vec::with_capacity(2);
    for (polynomial_basis, label) in [(false, "nested_folds"), (true, "lazy_cubic_dot3")] {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StateOnlyFoldPolynomialProbe {
                polynomial_basis,
                corrupt: 0,
                expected_sink: expected_nested,
            })?,
        };
        ensure!(
            instruction.data.first() == Some(&55),
            "fold-polynomial tag drifted"
        );
        let simulation_cu =
            simulate_pure_instruction(&rpc, &payer, instruction, VERIFY_REPETITIONS)
                .with_context(|| format!("fold polynomial {label}"))?;
        ensure!(
            simulation_cu.iter().all(|&value| value == simulation_cu[0]),
            "fold polynomial {label} was nondeterministic: {simulation_cu:?}"
        );
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        rows.push(StateOnlyFoldPolynomialProbeRow {
            polynomial_basis,
            label,
            simulation_cu,
            simulation_cu_mean,
        });
    }

    let mut noncanonical_rejected_both = true;
    for polynomial_basis in [false, true] {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StateOnlyFoldPolynomialProbe {
                polynomial_basis,
                corrupt: 1,
                expected_sink: [0u8; 32],
            })?,
        };
        noncanonical_rejected_both &=
            simulate_pure_instruction(&rpc, &payer, instruction, 1).is_ok();
    }
    ensure!(
        noncanonical_rejected_both,
        "fold-polynomial QM31 canonicality tooth failed"
    );
    let measured_savings_cu =
        (rows[0].simulation_cu_mean - rows[1].simulation_cu_mean).round() as i64;
    drop(validator);

    Ok(StateOnlyFoldPolynomialProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command:
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-state-only-fold-polynomial-probe"
                .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 55,
        query_count: 16,
        folds_per_query: 4,
        rows,
        measured_savings_cu,
        host_outputs_equal: true,
        random_off_domain_identity_cases: 512,
        noncanonical_qm31_rejected_both: noncanonical_rejected_both,
        soundness_neutral: true,
        notes: vec![
            "Both arms execute one circle-to-line fold and three line folds for each of sixteen query fibers, with identical canonical decodes, challenges, and M31 inverse coordinates.".to_string(),
            "The candidate expands the exact nested butterfly to c0 + alpha*c1 + alpha^2*c2 + alpha^3*c3 and lazily accumulates the three nonconstant products. It includes the one-time cost of deriving and preparing four alpha^3 values.".to_string(),
            "A separate core identity guard compares both circle and line forms at 512 fresh deterministic random QM31 value/challenge cases and unrestricted M31 inverse coordinates.".to_string(),
            "This is an isolated arithmetic differential. It changes no transcript, challenge, commitment, query, or acceptance polynomial.".to_string(),
        ],
    })
}

pub fn run_stage2_state_only_private_merkle_salt_probe(
) -> Result<StateOnlyPrivateMerkleSaltProbeSummary> {
    use sha2::{Digest as _, Sha256};

    const OPENED_LEAVES: usize = 16;
    const SALT_BYTES: usize = 32;
    const MAX_LEAF_BYTES: usize = 416;
    const FULL_SHARED_LENGTHS: [usize; 5] = [416, 256, 64, 64, 64];
    const DEDICATED_XF_TREE_BUCKET_CU: i64 = 31_930;

    fn host_sink(mode: u8) -> Result<[u8; 32]> {
        let (leaf_lengths, salted): (&[usize], bool) = match mode {
            0 => (&[128], false),
            1 => (&[256], false),
            2 => (&FULL_SHARED_LENGTHS, false),
            3 => (&FULL_SHARED_LENGTHS, true),
            _ => bail!("invalid private-Merkle salt mode {mode}"),
        };
        let mut storage = [0u8; SALT_BYTES + MAX_LEAF_BYTES];
        for (offset, byte) in storage.iter_mut().enumerate() {
            *byte = (offset as u8).wrapping_mul(73).wrapping_add(19);
        }
        let mut sink = [0u8; 32];
        for (tree, &leaf_len) in leaf_lengths.iter().enumerate() {
            let domain = [0x10, tree as u8];
            for leaf in 0..OPENED_LEAVES {
                storage[0] = (tree as u8).wrapping_mul(29).wrapping_add(leaf as u8);
                storage[SALT_BYTES] = (tree as u8).wrapping_mul(61).wrapping_add(leaf as u8);
                let opened = if salted {
                    &storage[..SALT_BYTES + leaf_len]
                } else {
                    &storage[SALT_BYTES..SALT_BYTES + leaf_len]
                };
                let mut hasher = Sha256::new();
                hasher.update(domain);
                hasher.update(opened);
                let digest: [u8; 32] = hasher.finalize().into();
                for (coordinate, byte) in digest.iter().enumerate() {
                    sink[coordinate] ^= byte.rotate_left(((tree + leaf + coordinate) & 7) as u32);
                }
            }
        }
        Ok(sink)
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let specs = [
        (0u8, "existing_c2_128", vec![128usize], false),
        (1u8, "shared_c2_256", vec![256usize], false),
        (
            2u8,
            "five_shared_trees_unsalted",
            FULL_SHARED_LENGTHS.to_vec(),
            false,
        ),
        (
            3u8,
            "five_shared_trees_salted",
            FULL_SHARED_LENGTHS.to_vec(),
            true,
        ),
    ];
    let mut rows = Vec::with_capacity(specs.len());
    for (mode, label, opened_leaf_lengths, salted) in specs {
        let expected_sink = host_sink(mode)?;
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StateOnlyPrivateMerkleSaltProbe {
                mode,
                expected_sink,
            })?,
        };
        ensure!(
            instruction.data.first() == Some(&49),
            "salt probe tag drifted"
        );
        let simulation_cu =
            simulate_pure_instruction(&rpc, &payer, instruction, VERIFY_REPETITIONS)
                .with_context(|| format!("private-Merkle salt probe mode {mode}"))?;
        ensure!(
            simulation_cu.iter().all(|&value| value == simulation_cu[0]),
            "private-Merkle salt probe mode {mode} was nondeterministic: {simulation_cu:?}"
        );
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        rows.push(StateOnlyPrivateMerkleSaltProbeRow {
            mode,
            label,
            leaf_hash_calls: opened_leaf_lengths.len() * OPENED_LEAVES,
            opened_leaf_lengths,
            salted,
            expected_sink_hex: expected_sink
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect(),
            simulation_cu,
            simulation_cu_mean,
        });
    }

    let shared_c2_leaf_widening_delta_cu =
        (rows[1].simulation_cu_mean - rows[0].simulation_cu_mean).round() as i64;
    let all_five_tree_private_salt_delta_cu =
        (rows[3].simulation_cu_mean - rows[2].simulation_cu_mean).round() as i64;
    let shared_root_net_saving_before_salts_cu =
        DEDICATED_XF_TREE_BUCKET_CU - shared_c2_leaf_widening_delta_cu;
    let literal_micro_shared_root_net_saving_after_salts_cu =
        shared_root_net_saving_before_salts_cu - all_five_tree_private_salt_delta_cu;
    // A negative isolated salt delta is measurement noise/code-layout luck,
    // not margin. Until the integrated parser/hash path is measured, book
    // salts at max(0, literal delta).
    let conservative_booked_private_salt_delta_cu = all_five_tree_private_salt_delta_cu.max(0);
    let shared_root_net_saving_after_salts_cu =
        shared_root_net_saving_before_salts_cu - conservative_booked_private_salt_delta_cu;
    drop(validator);

    Ok(StateOnlyPrivateMerkleSaltProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-state-only-private-merkle-salt-probe".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 49,
        query_count: 16,
        distinct_opened_leaves_per_tree: OPENED_LEAVES,
        rows,
        shared_c2_leaf_widening_delta_cu,
        all_five_tree_private_salt_delta_cu,
        conservative_booked_private_salt_delta_cu,
        dedicated_xf_tree_measured_bucket_cu: DEDICATED_XF_TREE_BUCKET_CU,
        shared_root_net_saving_before_salts_cu,
        literal_micro_shared_root_net_saving_after_salts_cu,
        shared_root_net_saving_after_salts_cu,
        salt_wire_delta_bytes: 5 * OPENED_LEAVES * SALT_BYTES,
        shared_c2_opened_value_wire_delta_bytes: OPENED_LEAVES * (256 - 128),
        production_salted_leaf_hash: "SHA256([0x10, tree_tag] || salt32 || leaf), with salt32 contiguous to leaf and one salt per logical opened leaf",
        explicit_nonclaims: vec![
            "This tag measures only leaf rehashing; radix-four frontier traversal and transcript absorption are intentionally identical or removed by the shared-root substitution.".to_string(),
            "Private-Merkle salts hide unopened leaf preimages but do not replace the full-field WHIR masks required for transcript HVZK.".to_string(),
            "The net saving is an overlap-safe isolated substitution, not an integrated profile-21 verifier total.".to_string(),
        ],
        notes: vec![
            "The 31,930-CU dedicated-X/F bucket is the exact switch45_xf_merkle_done marker delta from the same q16/depth15 tag45 artifact; sharing root0 removes that entire tree and retains only the measured 128-to-256-byte C2 leaf-hash delta.".to_string(),
            "All five production trees use exactly 16 distinct opened logical leaves: C1=416 bytes, widened C2=256, and W1/W2/W3=64 each. U replaces W1 and X/F share C2, so neither introduces another salt or tree.".to_string(),
            "Salted and unsalted arms both use two SHA syscall slices. The on-wire salt is contiguous with the leaf, avoiding a third slice descriptor while hashing exactly domain || salt || leaf.".to_string(),
            "A negative isolated salt delta is not booked as one-transaction headroom. The conservative salt charge is max(0, measured delta) until the integrated parser plus leaf-hash path confirms the complete effect.".to_string(),
        ],
    })
}

pub fn run_stage2_state_only_masked_switch_profile21_probe(
) -> Result<StateOnlyMaskedSwitchProfile21Summary> {
    use aspis_core::state_only_masked_switch::{
        verify_state_only_masked_switch, verify_state_only_masked_switch_diagnostic_unmined,
        MASKED_SWITCH_COEFFICIENTS, MASKED_SWITCH_FINAL_WORK_BITS, MASKED_SWITCH_LINE_DOMAIN_LOG,
        MASKED_SWITCH_QUERY_COUNT, MASKED_SWITCH_SOURCE_WORK_BITS,
    };
    use sha2::{Digest as _, Sha256};

    let root = workspace_root()?;
    let proof_path = root.join("results/stage2/proofs/state_only_masked_switch_p21_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read masked-switch fixture {}", proof_path.display()))?;
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/state-only/profile21/masked-switch/fixture/v1").into();
    verify_state_only_masked_switch_diagnostic_unmined(&proof, &statement_digest, HOST_HASH)
        .map_err(|error| anyhow!("host masked-switch fixture rejected: {error:?}"))?;
    let production_api_rejected_unmined =
        verify_state_only_masked_switch(&proof, &statement_digest, HOST_HASH).is_err();
    ensure!(
        production_api_rejected_unmined,
        "unmined fixture escaped no-bypass production API"
    );

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 3 * LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof, true)?;

    let make_instruction = |account: Pubkey,
                            digest: [u8; 32],
                            diagnostic_unmined: bool,
                            direct_u_query_evaluation: bool|
     -> Result<Instruction> {
        let data = to_vec(&AspisInstruction::StateOnlyMaskedSwitchProfile21Probe {
            statement_digest: digest,
            diagnostic_unmined,
            direct_u_query_evaluation,
        })?;
        ensure!(data.first() == Some(&45), "masked-switch probe tag drifted");
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(account, false)],
            data,
        })
    };
    let simulate = |instruction: Instruction| -> Result<SimulationResult> {
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        rpc.simulate_verbose(&transaction)
    };

    let mut simulation_cu = Vec::new();
    let mut markers = Vec::new();
    for repetition in 0..VERIFY_REPETITIONS {
        let result = simulate(make_instruction(
            proof_account.pubkey(),
            statement_digest,
            true,
            false,
        )?)?;
        ensure!(
            result.err.is_none(),
            "tag45 repetition {repetition} failed: {:?}",
            result.err
        );
        simulation_cu.push(result.units.context("tag45 units consumed")?);
        if repetition == 0 {
            markers = parse_cu_markers(&result.logs, "aspis-cu:");
        }
    }

    let mut direct_q_reference_simulation_cu = Vec::new();
    for repetition in 0..VERIFY_REPETITIONS {
        let result = simulate(make_instruction(
            proof_account.pubkey(),
            statement_digest,
            true,
            true,
        )?)?;
        ensure!(
            result.err.is_none(),
            "tag45 direct-q repetition {repetition} failed: {:?}",
            result.err
        );
        direct_q_reference_simulation_cu
            .push(result.units.context("tag45 direct-q units consumed")?);
    }

    let mut generic_qm31_reference_simulation_cu = Vec::new();
    for repetition in 0..VERIFY_REPETITIONS {
        let result = simulate(make_instruction(
            proof_account.pubkey(),
            statement_digest,
            false,
            true,
        )?)?;
        ensure!(
            result.err.is_none(),
            "tag45 generic-QM31 repetition {repetition} failed: {:?}",
            result.err
        );
        generic_qm31_reference_simulation_cu
            .push(result.units.context("tag45 generic-QM31 units consumed")?);
    }

    let mut stale_statement = statement_digest;
    stale_statement[0] ^= 1;
    let stale_statement_rejected_onchain = simulate(make_instruction(
        proof_account.pubkey(),
        stale_statement,
        true,
        false,
    )?)?
    .err
    .is_some();
    ensure!(
        stale_statement_rejected_onchain,
        "stale statement accepted by tag45"
    );

    let mut corrupted = proof.clone();
    corrupted[1] ^= 1;
    let corrupt_account = Keypair::new();
    upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
    let corrupted_root_rejected_onchain = simulate(make_instruction(
        corrupt_account.pubkey(),
        statement_digest,
        true,
        false,
    )?)?
    .err
    .is_some();
    ensure!(
        corrupted_root_rejected_onchain,
        "corrupted X/F root accepted by tag45"
    );

    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    let simulation_cu_mean = simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
    let direct_q_reference_simulation_cu_mean = direct_q_reference_simulation_cu.iter().sum::<u64>()
        as f64
        / direct_q_reference_simulation_cu.len() as f64;
    let generic_qm31_reference_simulation_cu_mean =
        generic_qm31_reference_simulation_cu.iter().sum::<u64>() as f64
            / generic_qm31_reference_simulation_cu.len() as f64;
    let measured_four_query_fusion_savings_cu =
        direct_q_reference_simulation_cu_mean - simulation_cu_mean;
    let measured_direct_q_evaluation_savings_cu =
        generic_qm31_reference_simulation_cu_mean - simulation_cu_mean;
    let measured_u_tree_replacement_bucket_cu = markers
        .iter()
        .find(|marker| marker.label == "switch45_u_merkle_done")
        .and_then(|marker| marker.delta_from_previous)
        .and_then(|value| u64::try_from(value).ok())
        .context("tag45 U-tree marker bucket")?;
    let overlap_subtracted_incremental_estimate_cu =
        simulation_cu_mean - measured_u_tree_replacement_bucket_cu as f64;
    drop(validator);
    Ok(StateOnlyMaskedSwitchProfile21Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-state-only-masked-switch-profile21-probe".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 45,
        profile_label: "profile21 isolated masked-switch PCS diagnostic over profile20 geometry".to_string(),
        line_code_length: 1usize << MASKED_SWITCH_LINE_DOMAIN_LOG,
        line_code_dimension: MASKED_SWITCH_COEFFICIENTS,
        query_count: MASKED_SWITCH_QUERY_COUNT,
        source_work_bits: MASKED_SWITCH_SOURCE_WORK_BITS,
        final_work_bits: MASKED_SWITCH_FINAL_WORK_BITS,
        proof_bytes: proof.len(),
        proof_sha256,
        upload_chunks,
        simulation_cu,
        simulation_cu_mean,
        direct_q_reference_simulation_cu,
        direct_q_reference_simulation_cu_mean,
        generic_qm31_reference_simulation_cu,
        generic_qm31_reference_simulation_cu_mean,
        measured_four_query_fusion_savings_cu,
        measured_direct_q_evaluation_savings_cu,
        measured_u_tree_replacement_bucket_cu,
        overlap_subtracted_incremental_estimate_cu,
        markers,
        host_fixture_accepted: true,
        production_api_rejected_unmined,
        stale_statement_rejected_onchain,
        corrupted_root_rejected_onchain,
        sound_acceptance_complete: false,
        explicit_nonclaims: vec![
            "Tag45 is not spliced into the production profile20 transcript or FRI continuation.".to_string(),
            "Tag45 does not bind tX/muF to the production round-zero relation or virtual-W0 p0.".to_string(),
            "The 18,443-byte fixture includes a second U tree/frontier which replaces, rather than adds to, the existing root-one tree in an integrated profile21 proof.".to_string(),
            "The diagnostic arms execute both work hashes but bypass only their predicates; the no-bypass core API rejects this fixture. Production freezes all affected work predicates at g38.".to_string(),
        ],
        notes: vec![
            "X/F root and targets precede a dedicated source-round work witness; delta follows that witness. The translated root precedes two OOD samples and the final work/q16 round. Production uses g38 at each affected normalization point.".to_string(),
            "The same q16 positions authenticate X/F and U under independent radix-four depth-15 packed-leaf roots (four line values per leaf) and enforce F(q)+delta*X(q)=U(q)=Enc(U)(q).".to_string(),
            "S-two Theorem-19 source batching is approximately 72.8173 bits before this dedicated grinding term; final post-delta work is not credited backward.".to_string(),
            format!("Exact q16 A/B: four-query fused M31 mean {} CU, scalar M31 sparse reference {} CU, generic-QM31 reference {} CU. The fused path computes the identical natural tensor polynomial.", simulation_cu_mean, direct_q_reference_simulation_cu_mean, generic_qm31_reference_simulation_cu_mean),
            format!("Overlap rule: literal production-equivalent tag45 mean {} CU minus the measured {}-CU U-tree bucket gives a {}-CU incremental estimate. This is measurement minus measurement, but remains non-integrated until the W0/W1 splice exists.", simulation_cu_mean, measured_u_tree_replacement_bucket_cu, overlap_subtracted_incremental_estimate_cu),
        ],
    })
}

fn create_program_account(
    rpc: &Rpc,
    payer: &Keypair,
    account: &Keypair,
    space: usize,
) -> Result<()> {
    let rent = rpc.call("getMinimumBalanceForRentExemption", json!([space]))?;
    let rent = rent.as_u64().ok_or_else(|| anyhow!("bad rent"))?;
    let create = system_instruction::create_account(
        &payer.pubkey(),
        &account.pubkey(),
        rent,
        space as u64,
        &aspis_verifier::id(),
    );
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[create],
        Some(&payer.pubkey()),
        &[payer, account],
        blockhash,
    );
    rpc.send_and_confirm(&tx)?;
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RpcAccountSnapshot {
    lamports: u64,
    owner: Pubkey,
    data: Vec<u8>,
}

fn rpc_account_snapshot(rpc: &Rpc, address: &Pubkey) -> Result<Option<RpcAccountSnapshot>> {
    let result = rpc.call(
        "getAccountInfo",
        json!([address.to_string(), {"encoding": "base64", "commitment": "processed"}]),
    )?;
    let value = &result["value"];
    if value.is_null() {
        return Ok(None);
    }
    let owner = value["owner"]
        .as_str()
        .ok_or_else(|| anyhow!("account snapshot missing owner"))?
        .parse()?;
    let lamports = value["lamports"]
        .as_u64()
        .ok_or_else(|| anyhow!("account snapshot missing lamports"))?;
    let encoded = value["data"][0]
        .as_str()
        .ok_or_else(|| anyhow!("account snapshot missing base64 data"))?;
    let data = BASE64
        .decode(encoded)
        .context("decode account snapshot base64")?;
    Ok(Some(RpcAccountSnapshot {
        lamports,
        owner,
        data,
    }))
}

fn write_validator_account_fixture(
    root: &Path,
    label: &str,
    address: Pubkey,
    owner: Pubkey,
    data: &[u8],
) -> Result<PathBuf> {
    let directory = root.join(".stage2-validator-account-fixtures");
    fs::create_dir_all(&directory)?;
    let path = directory.join(format!("{label}-{address}.json"));
    let account = json!({
        "pubkey": address.to_string(),
        "account": {
            "lamports": 10_000_000u64,
            "data": [BASE64.encode(data), "base64"],
            "owner": owner.to_string(),
            "executable": false,
            "rentEpoch": 0u64,
            "space": data.len(),
        }
    });
    fs::write(&path, serde_json::to_vec_pretty(&account)?)?;
    Ok(path)
}

#[allow(clippy::too_many_arguments)]
fn upload_proof(
    rpc: &Rpc,
    payer: &Keypair,
    proof_account: &Keypair,
    proof: &[u8],
    fresh_account: bool,
) -> Result<(usize, u64)> {
    let space = PROOF_ACCOUNT_HEADER_LEN + proof.len();
    if fresh_account {
        let rent = rpc.call("getMinimumBalanceForRentExemption", json!([space]))?;
        let rent = rent.as_u64().ok_or_else(|| anyhow!("bad rent"))?;
        let create = system_instruction::create_account(
            &payer.pubkey(),
            &proof_account.pubkey(),
            rent,
            space as u64,
            &aspis_verifier::id(),
        );
        let blockhash = rpc.latest_blockhash()?;
        let tx = Transaction::new_signed_with_payer(
            &[create],
            Some(&payer.pubkey()),
            &[payer, proof_account],
            blockhash,
        );
        rpc.send_and_confirm(&tx)?;
    }

    let mut total_cu = 0u64;
    let init = proof_instruction(
        &payer.pubkey(),
        &proof_account.pubkey(),
        &AspisInstruction::InitProof {
            total_len: proof.len() as u32,
        },
    )?;
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            init,
        ],
        Some(&payer.pubkey()),
        &[payer, proof_account],
        blockhash,
    );
    total_cu += rpc.send_and_confirm(&tx)?;

    let mut chunks = 0usize;
    for (i, chunk) in proof.chunks(UPLOAD_CHUNK_BYTES).enumerate() {
        let upload = proof_instruction(
            &payer.pubkey(),
            &proof_account.pubkey(),
            &AspisInstruction::UploadChunk {
                offset: (i * UPLOAD_CHUNK_BYTES) as u32,
                chunk: chunk.to_vec(),
            },
        )?;
        let blockhash = rpc.latest_blockhash()?;
        let tx = Transaction::new_signed_with_payer(
            &[upload],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        total_cu += rpc.send_and_confirm(&tx)?;
        chunks += 1;
    }
    Ok((chunks, total_cu))
}

fn finalize_proof(rpc: &Rpc, payer: &Keypair, proof_account: &Pubkey) -> Result<u64> {
    let finalize = proof_instruction(
        &payer.pubkey(),
        proof_account,
        &AspisInstruction::FinalizeProof,
    )?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            finalize,
        ],
        Some(&payer.pubkey()),
        &[payer],
        rpc.latest_blockhash()?,
    );
    rpc.send_and_confirm(&transaction)
}

fn verify_tx(
    payer: &Keypair,
    proof_account: &Pubkey,
    digest: [u8; 32],
    blockhash: solana_sdk::hash::Hash,
    profile_cu: bool,
) -> Result<Transaction> {
    let instruction = if profile_cu {
        AspisInstruction::VerifyProfile {
            statement_digest: digest,
        }
    } else {
        AspisInstruction::Verify {
            statement_digest: digest,
        }
    };
    let ixs = vec![
        ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
        ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
        proof_instruction(&payer.pubkey(), proof_account, &instruction)?,
    ];
    Ok(Transaction::new_signed_with_payer(
        &ixs,
        Some(&payer.pubkey()),
        &[payer],
        blockhash,
    ))
}

fn validator_version() -> String {
    Command::new("solana-test-validator")
        .env("NO_DNA", "1")
        .arg("--version")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|_| "unknown".to_string())
}

fn parse_cu_markers(logs: &[String], marker_prefix: &str) -> Vec<CuMarker> {
    let mut pending: Option<String> = None;
    let mut previous: Option<u64> = None;
    let mut markers = Vec::new();
    for log in logs {
        if let Some((_, suffix)) = log.split_once(marker_prefix) {
            pending = Some(suffix.trim().to_string());
            continue;
        }
        let Some((_, rest)) = log.split_once("Program consumption:") else {
            continue;
        };
        let Some(label) = pending.take() else {
            continue;
        };
        let Some(remaining) = rest
            .split_whitespace()
            .find_map(|token| token.parse::<u64>().ok())
        else {
            continue;
        };
        let delta_from_previous = previous.map(|prev| prev as i64 - remaining as i64);
        previous = Some(remaining);
        markers.push(CuMarker {
            label,
            remaining,
            delta_from_previous,
        });
    }
    markers
}

pub fn run_stage0_onchain(gate_matrix_only: bool) -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let validator_version = validator_version();

    let mut variants = Vec::new();
    let modes: &[MerkleMode] = if gate_matrix_only {
        &[MerkleMode::MinimalSubtree]
    } else {
        &[MerkleMode::MinimalSubtree, MerkleMode::SinglePaths]
    };
    for profile in [&PROFILE_CAPACITY, &PROFILE_JOHNSON, &PROFILE_CAPACITY_LR14] {
        for payload in [FoldPayload::RawFibers, FoldPayload::ProofCarriedRoundLocal] {
            for &mode in modes {
                if gate_matrix_only
                    && profile.id == PROFILE_CAPACITY_LR14.id
                    && payload == FoldPayload::ProofCarriedRoundLocal
                {
                    continue;
                }
                variants.push(run_onchain_variant(&rpc, &payer, profile, payload, mode)?);
            }
        }
    }

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: if gate_matrix_only {
            "cargo run -p aspis-xtask -- stage0-onchain-gate".to_string()
        } else {
            "cargo run -p aspis-xtask -- stage0-onchain".to_string()
        },
        validator_version,
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only,
        variants,
        notes: vec![
            "verify_cu are simulateTransaction unitsConsumed for the full verify transaction (including compute-budget instructions) against a local test validator.".to_string(),
            "Variants with status=verify_failed exceeded budget or otherwise failed during simulation; their corruption suite is skipped because no accepting baseline exists.".to_string(),
            "Soundness labels remain heuristic pending the Stage 1 note; the capacity-vs-Johnson asymmetry must be restated wherever these CU numbers are quoted.".to_string(),
        ],
    })
}

pub fn run_stage0_onchain_g32() -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for profile in [&PROFILE_CAPACITY_G32_Q36, &PROFILE_CAPACITY_G32_Q32] {
        variants.push(run_onchain_variant(
            &rpc,
            &payer,
            profile,
            FoldPayload::RawFibers,
            MerkleMode::MinimalSubtree,
        )?);
    }

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-onchain-g32".to_string(),
        validator_version: validator_version(),
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only: true,
        variants,
        notes: vec![
            "Diagnostic g32 query/grinding trade; not a frozen profile until Stage 1 soundness accounting confirms the query count.".to_string(),
            "Only raw_fibers/minimal_subtree is measured because proof_carried_round_local lost on both bytes and CU in the gate artifact.".to_string(),
        ],
    })
}

pub fn run_stage0_onchain_layout_target() -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for profile in [
        // the literal ruled Stage 1 schedule first (soundness-note §4)
        &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32,
        &PROFILE_CAPACITY_LR10_Q40_G16,
        &PROFILE_CAPACITY_LR10_Q36_G16,
        &PROFILE_CAPACITY_LR10_Q32_G16,
    ] {
        variants.push(run_onchain_variant(
            &rpc,
            &payer,
            profile,
            FoldPayload::RawFibers,
            MerkleMode::MinimalSubtree,
        )?);
    }

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-onchain-layout-target".to_string(),
        validator_version: validator_version(),
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only: true,
        variants,
        notes: vec![
            "Lower-row diagnostic for the wide-row statement layout decision; not a frozen profile until Stage 1 soundness accounting and the Stage 2 direct evaluator exist.".to_string(),
            "Only raw_fibers/minimal_subtree is measured because proof_carried_round_local lost on both bytes and CU in the gate artifact.".to_string(),
            "The first row is the literal ruled q36/g32 Stage 1 profile and performs the real prover-side 32-bit nonce search; the remaining g16 rows are comparison diagnostics.".to_string(),
            "Although the verifier's grinding threshold check is constant-cost, changing g16 to g32 changes the transcript-bound header and therefore the sampled query collisions and minimal-subtree shape. Use the literal g32 row, not a g16 CU proxy, for the ruled profile.".to_string(),
            "Historical lower-row diagnostic emitted by the current v3 verifier without C2: one OOD value and its interleaved relation polynomial are enforced per round. Use stage1-onchain-hardening for the frozen C2 gate profile.".to_string(),
            "Combine these PCS verifier costs with layout_sweep RLC/wide-leaf deltas; do not add the full synthetic Merkle loop or path hashing is double-counted.".to_string(),
        ],
    })
}

/// Stage 1 hardened-profile measurement. The valid g32 proof is cached as a
/// pinned fixture after its expensive nonce search; every reuse first runs
/// the current host verifier, so a protocol change invalidates and replaces
/// it instead of silently measuring stale bytes.
pub fn run_stage1_onchain_hardening() -> Result<OnchainSummary> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let profile = &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32;
    let payload = FoldPayload::RawFibers;
    let mode = MerkleMode::MinimalSubtree;
    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let digest = crate::host_statement_digest(0);
    let options = ProveOptions {
        fold_payload: payload,
        merkle_mode: mode,
    };
    let proof_dir = root.join("results/stage1/proofs");
    fs::create_dir_all(&proof_dir)?;
    let proof_path = proof_dir.join("capacity_lr10_q36_g32_v3_c2.bin");

    let cached = fs::read(&proof_path)
        .ok()
        .filter(|proof| aspis_core::verify(proof, &digest, HOST_HASH).is_ok());
    let (proof, proof_source) = if let Some(proof) = cached {
        (proof, "reused host-verified cached g32 proof".to_string())
    } else {
        eprintln!("stage1-onchain: searching literal g32 nonce (cached after success)");
        let started = Instant::now();
        let proof =
            prove_with_synthetic_second_phase(profile, &coeffs, &digest, &options, HOST_HASH);
        fs::write(&proof_path, &proof)?;
        (
            proof,
            format!(
                "generated and cached literal g32 proof; prover search {:.3}s",
                started.elapsed().as_secs_f64()
            ),
        )
    };
    let proof_digest = HOST_HASH(&[&proof]);
    let proof_digest_hex = proof_digest
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();

    let variant =
        run_onchain_variant_with_proof(&rpc, &payer, profile, payload, mode, Some(proof))?;

    Ok(OnchainSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage1-onchain-hardening".to_string(),
        validator_version: validator_version(),
        verify_cu_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        gate_matrix_only: true,
        variants: vec![variant],
        notes: vec![
            "Literal ruled Stage 1 q36/g32 profile with C1 -> (lambda, chi) -> C2 -> claims -> gamma and the interleaved OOD/evaluation-relation sumcheck enabled.".to_string(),
            "C2 uses a deterministic challenge-dependent Stage-1 helper to price and test the generic second-phase interface; it is not the Stage-2 LogUp helper and proves no payment relation.".to_string(),
            "All host-generated corruption cases are replayed against the SBF verifier; every entry must be true.".to_string(),
            format!("proof fixture: {}; {proof_source}", proof_path.display()),
            format!("proof SHA-256: {proof_digest_hex}"),
        ],
    })
}

pub fn run_stage0_onchain_profile() -> Result<ProfileRun> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 500 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY;
    let payload = FoldPayload::RawFibers;
    let mode = MerkleMode::MinimalSubtree;
    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let digest = crate::host_statement_digest(0);
    let proof = prove(
        profile,
        &coeffs,
        &digest,
        &ProveOptions {
            fold_payload: payload,
            merkle_mode: mode,
        },
        HOST_HASH,
    );
    let proof_account = Keypair::new();
    let (chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let blockhash = rpc.latest_blockhash()?;
    let tx = verify_tx(&payer, &proof_account.pubkey(), digest, blockhash, true)?;
    let sim = rpc.simulate_verbose(&tx)?;
    Ok(ProfileRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-onchain-profile".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        fold_payload: "raw_fibers",
        merkle_mode: "minimal_subtree",
        proof_bytes: proof.len(),
        upload_chunks: chunks,
        simulation_units: sim.units,
        simulation_error: sim.err,
        markers: parse_cu_markers(&sim.logs, "aspis-cu:"),
        logs: sim.logs,
        notes: vec![
            "Diagnostic only: msg!/sol_log_compute_units markers add CU and should not be quoted as the verifier cost.".to_string(),
            "Use marker deltas for stage attribution: header/transcript/query/layer Merkle+fold/final.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct TranscriptKatRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub expected_digest_hex: String,
    pub matched_on_sbf: bool,
    pub simulation_units: Option<u64>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct TranscriptKatV4S2PcsScaffoldRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub expected_digest_hex: String,
    pub host_digest_hex: String,
    pub host_matched: bool,
    pub matched_on_sbf: bool,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub v3_pin_unchanged: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct FinalPaymentTranscriptKatV4Run {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub expected_digest_hex: String,
    pub host_digest_hex: String,
    pub host_matched: bool,
    pub matched_on_sbf: bool,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub earlier_pins_unchanged: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct LogUpCompressionKatRun {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub expected_phi_hex: String,
    pub host_phi_hex: String,
    pub host_matched: bool,
    pub matched_on_sbf: bool,
    pub simulation_units: Option<u64>,
    pub simulation_error: Option<String>,
    pub weakened_feature_forwarded_to_verifier: bool,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct OodSampleRelationProbeVariant {
    pub samples_per_round: u8,
    pub expected_sink_hex: String,
    pub host_sink_hex: String,
    pub host_sink_matched: bool,
    pub sbf_sink_matched: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct OodSampleRelationProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub log_rows: u8,
    pub rounds: u8,
    pub terminal_coefficients: u8,
    pub existing_multilinear_claim_components: u8,
    pub variants: Vec<OodSampleRelationProbeVariant>,
    pub pcs_s2_second_ood_sample_transcript_relation_cu: i64,
    pub superseded_probe_local_generated_value_delta_cu: i64,
    pub probe_local_value_generation_contamination_removed_cu: i64,
    pub previous_estimate_bracket_cu: [i64; 2],
    pub delta_over_previous_bracket_max_cu: i64,
    pub structural_proof_record_delta_bytes: u64,
    pub extra_transcript_hash_calls_no_retry: u32,
    pub extra_geometric_fold_operations: u32,
    pub extra_terminal_component_evaluations: u32,
    pub production_transcript_kat_unchanged: bool,
    pub production_proof_format_unchanged: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct TwoPointBatchingProbeVariant {
    pub mode: &'static str,
    pub mode_ordinal: u8,
    pub expected_sink_hex: String,
    pub host_sink_hex: String,
    pub host_sink_matched: bool,
    pub sbf_sink_matched: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub simulation_cu_delta_vs_one_point: i64,
    pub relation_lanes: u8,
    pub point_components: u8,
    pub relation_polynomials: u8,
    pub relation_proof_bytes: u32,
    pub relation_proof_bytes_delta_vs_one_point: i64,
    pub instruction_data_bytes: usize,
    pub transcript_hash_calls_no_retry: u32,
    pub transcript_hash_calls_delta_vs_one_point: i32,
}

#[derive(Serialize)]
pub struct TwoPointBatchingProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub compute_unit_limit: u32,
    pub heap_frame: &'static str,
    pub log_rows: u32,
    pub rounds: u32,
    pub statement_points: u8,
    pub statement_values: usize,
    pub pre_gamma_point_bytes: usize,
    pub pre_gamma_value_bytes: usize,
    pub variants: Vec<TwoPointBatchingProbeVariant>,
    pub production_rule_selected: bool,
    pub product_projection_updated: bool,
    pub architecture_ruling_made: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct V4S2PcsScaffoldSeedMeasurement {
    pub seed: u64,
    pub v3_proof_bytes: usize,
    pub v4_proof_bytes: usize,
    pub proof_bytes_delta: i64,
    pub v3_proof_sha256: String,
    pub v4_proof_sha256: String,
    pub v3_layer0_unique_fibers: u16,
    pub v4_layer0_unique_fibers: u16,
    pub v3_verify_cu: u64,
    pub v4_verify_cu: u64,
    pub verify_cu_delta: i64,
}

#[derive(Serialize)]
pub struct V4S2PcsScaffoldCorruptionCase {
    pub seed: u64,
    pub target: String,
    pub layer: Option<u32>,
    pub sample_index: Option<u8>,
    pub helper_claim_index: Option<u8>,
    pub helper_leaf_half_index: Option<u8>,
    pub proof_byte_offset: usize,
    pub host_rejected: bool,
    pub host_error: String,
    pub sbf_rejected: bool,
    pub sbf_error: String,
}

#[derive(Serialize)]
pub struct V4S2PcsScaffoldSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub profile: &'static str,
    pub statement_kind: &'static str,
    pub is_payment_proof: bool,
    pub production_verify_instruction_wire_ordinal: u8,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub transaction_envelope: &'static str,
    pub merkle_mode: &'static str,
    pub seeds: u64,
    pub repetitions_per_proof: usize,
    pub v3_samples_per_round: u8,
    pub v4_samples_per_round: u8,
    pub v3_second_phase_helper_columns: u8,
    pub v4_second_phase_helper_columns: u8,
    pub v3_second_phase_leaf_bytes: u16,
    pub v4_second_phase_leaf_bytes: u16,
    pub v3_second_phase_claims: u8,
    pub v4_second_phase_claims: u8,
    pub transcript_kat_v4_s2_pcs_scaffold_wire_ordinal: u8,
    pub transcript_kat_v4_s2_pcs_scaffold_expected_hex: String,
    pub transcript_kat_v4_s2_pcs_scaffold_host_matched: bool,
    pub transcript_kat_v4_s2_pcs_scaffold_sbf_matched: bool,
    pub transcript_kat_v4_s2_pcs_scaffold_simulation_cu: u64,
    pub transcript_kat_v3_unchanged: bool,
    pub measurements: Vec<V4S2PcsScaffoldSeedMeasurement>,
    pub v3_layer0_unique_fibers_min: u16,
    pub v3_layer0_unique_fibers_max: u16,
    pub v4_layer0_unique_fibers_min: u16,
    pub v4_layer0_unique_fibers_max: u16,
    pub v3_verify_cu_mean: f64,
    pub v4_verify_cu_mean: f64,
    pub paired_verify_cu_delta_mean: f64,
    pub paired_verify_cu_delta_min: i64,
    pub paired_verify_cu_delta_max: i64,
    pub paired_verify_cu_delta_range: u64,
    pub proof_bytes_delta_min: i64,
    pub proof_bytes_delta_max: i64,
    pub second_ood_corruptions: Vec<V4S2PcsScaffoldCorruptionCase>,
    pub helper_claim_corruptions: Vec<V4S2PcsScaffoldCorruptionCase>,
    pub helper_leaf_half_corruptions: Vec<V4S2PcsScaffoldCorruptionCase>,
    pub every_second_ood_rejected_host: bool,
    pub every_second_ood_rejected_sbf: bool,
    pub every_helper_claim_rejected_host: bool,
    pub every_helper_claim_rejected_sbf: bool,
    pub every_helper_leaf_half_rejected_host: bool,
    pub every_helper_leaf_half_rejected_sbf: bool,
    pub normative_payment_v4_framing_complete: bool,
    pub missing_payment_v4_components: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct ReconciledExactWideSeedMeasurement {
    pub seed: u64,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub layer0_unique_fibers: u16,
    pub authenticated_c1_opening_bytes: usize,
    pub authenticated_c2_opening_bytes: usize,
    pub diagnostic_host_accepted: bool,
    pub production_host_rejected_bad_header: bool,
    pub observed_cu_or_cap: u64,
    pub simulation_error: Option<String>,
    pub accepted_at_1_400_000_limit: bool,
    pub compute_budget_exhausted: bool,
    pub exact_cu_if_accepted: Option<u64>,
    pub required_cu_lower_bound_if_exhausted: Option<u64>,
    pub signed_headroom_vs_1_190_000_if_accepted: Option<i64>,
    pub signed_headroom_vs_1_400_000_if_accepted: Option<i64>,
    pub minimum_breach_vs_1_190_000_if_exhausted: Option<u64>,
    pub minimum_breach_vs_1_400_000_if_exhausted: Option<u64>,
    pub outcome_vs_1_190_000: String,
    pub outcome_vs_1_400_000: String,
}

#[derive(Serialize)]
pub struct ReconciledExactWideCorruptionCase {
    pub target: &'static str,
    pub kind: &'static str,
    pub proof_byte_offset: usize,
    pub host_rejected: bool,
    pub host_error: String,
    pub sbf_error: String,
    pub sbf_compute_budget_exhausted: bool,
    pub sbf_rejection_conclusive: bool,
}

#[derive(Serialize)]
pub struct ReconciledExactWideSummary {
    pub generated_at_utc: String,
    pub command: &'static str,
    pub validator_version: String,
    pub profile: &'static str,
    pub statement_kind: &'static str,
    pub is_payment_proof: bool,
    pub diagnostic_verify_instruction_wire_ordinal: u8,
    pub production_verify_with_claim_wire_ordinal: u8,
    pub production_verify_with_claim_accepts_wide_flag: bool,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub strict_project_threshold_cu: u64,
    pub absolute_execution_cap_cu: u64,
    pub transaction_envelope: &'static str,
    pub merkle_mode: &'static str,
    pub seeds: u64,
    pub c1_columns: usize,
    pub c1_leaf_bytes: usize,
    pub c2_columns: usize,
    pub c2_leaf_bytes: usize,
    pub auxiliary_c1_columns: &'static str,
    pub measurements: Vec<ReconciledExactWideSeedMeasurement>,
    pub accepted_seed_count: usize,
    pub compute_budget_exhausted_seed_count: usize,
    pub all_seed_outcomes_classified: bool,
    pub observed_cu_or_cap_min: u64,
    pub observed_cu_or_cap_max: u64,
    pub exact_accepted_cu_mean: Option<f64>,
    pub threshold_1_190_000_observation: String,
    pub threshold_1_400_000_observation: String,
    pub production_tag6_seed1_sbf_rejected: bool,
    pub production_tag6_seed1_sbf_cu: u64,
    pub production_tag6_seed1_sbf_error: String,
    pub corruption_cases: Vec<ReconciledExactWideCorruptionCase>,
    pub canonical_mutations_rejected_host: bool,
    pub noncanonical_limbs_rejected_host_and_sbf_conclusively: bool,
    pub owner_ruling_made: bool,
    pub overlap_replacement: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct ExactWideV4DiagnosticVariant {
    pub mode: &'static str,
    pub expected_host_sink_hex: String,
    pub sbf_matched_host_sink: bool,
    pub accepted_all: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_errors: Vec<Option<String>>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct ExactWideV4CorruptionCase {
    pub target: &'static str,
    pub mode: &'static str,
    pub fixture_byte_offset: usize,
    pub host_corrupted_sink_differs: bool,
    pub host_rejected_malformed: bool,
    pub sbf_rejected_canonical_sink: bool,
    pub sbf_error: String,
}

#[derive(Serialize)]
pub struct ExactWideV4DiagnosticSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub final_payment_kat_reserved_wire_ordinal: u8,
    pub final_payment_kat_implemented: bool,
    pub repetitions: usize,
    pub fixture_seed: u64,
    pub fixture_payload_bytes: usize,
    pub fixture_upload_chunks: usize,
    pub fixture_upload_cu_excluded: u64,
    pub batch_fixture_payload_bytes: usize,
    pub batch_fixture_upload_chunks: usize,
    pub batch_fixture_upload_cu_excluded: u64,
    pub fixture_generation_in_measured_instruction: bool,
    pub c1_columns: usize,
    pub c2_columns: usize,
    pub total_gamma_powers: usize,
    pub c1_leaf_bytes: usize,
    pub c2_leaf_bytes: usize,
    pub c1_layout: &'static str,
    pub c2_layout: &'static str,
    pub host_baseline_equals_fused: bool,
    pub variants: Vec<ExactWideV4DiagnosticVariant>,
    pub fused_dot4_savings_cu: i64,
    pub fused_dot4_savings_percent: f64,
    pub c1_leaf_hash_incremental_over_empty_cu: i64,
    pub c2_leaf_hash_incremental_over_empty_cu: i64,
    pub gamma_powers_incremental_over_control_cu: i64,
    pub gate_q36_batch_unique_fibers: usize,
    pub gate_batch_count_provenance: String,
    pub frozen_q36_fixture_unique_fibers: [usize; 2],
    pub theoretical_q36_unique_fibers_max: usize,
    pub transaction_compute_limit_cu: u32,
    pub strict_transaction_target_cu: u32,
    pub heap_frame_bytes: u32,
    pub transaction_envelope: &'static str,
    pub batch_unprepared_accepted: bool,
    pub batch_unprepared_compute_budget_exhausted: bool,
    pub batch_prepared_accepted: bool,
    pub batch_unprepared_cu_mean_or_cap: f64,
    pub batch_prepared_cu_mean: f64,
    pub batch_prepared_headroom_vs_compute_cap_cu: i64,
    pub batch_prepared_headroom_vs_strict_target_cu: i64,
    pub batch_prepared_bytes_accepted: bool,
    pub batch_prepared_bytes_cu_mean: f64,
    pub batch_prepared_bytes_headroom_vs_compute_cap_cu: i64,
    pub batch_prepared_bytes_headroom_vs_strict_target_cu: i64,
    pub batch_prepared_bytes_savings_vs_structured_cu: i64,
    pub batch_prepared_bytes_savings_vs_structured_percent: f64,
    pub batch_prepared_savings_cu_if_exact: Option<i64>,
    pub batch_prepared_savings_lower_bound_cu: i64,
    pub batch_prepared_bytes_savings_lower_bound_cu: i64,
    pub corruption_cases: Vec<ExactWideV4CorruptionCase>,
    pub all_corruptions_rejected_sbf: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

#[derive(Serialize)]
pub struct M31CircleBasisVariant {
    pub mode: &'static str,
    pub expected_host_sink_hex: String,
    pub accepted_all: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub signed_headroom_vs_1_190_000_cu: i64,
    pub signed_headroom_vs_1_400_000_cu: i64,
}

#[derive(Serialize)]
pub struct M31CircleBasisCorruptionCase {
    pub target: &'static str,
    pub fixture: &'static str,
    pub fixture_byte_offset: usize,
    pub host_rejected: bool,
    pub sbf_rejected: bool,
    pub sbf_error: String,
}

#[derive(Serialize)]
pub struct M31CircleBasisSummary {
    pub generated_at_utc: String,
    pub command: &'static str,
    pub validator_version: String,
    pub status: &'static str,
    pub diagnostic_instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub compute_unit_limit: u32,
    pub heap_frame_bytes: u32,
    pub transaction_envelope: &'static str,
    pub structural_fibers: usize,
    pub c1_field: &'static str,
    pub c1_columns: usize,
    pub c1_leaf_bytes: usize,
    pub c2_field: &'static str,
    pub c2_columns: usize,
    pub c2_leaf_bytes: usize,
    pub gamma_powers: &'static str,
    pub rlc_fixture_bytes: usize,
    pub fold_fixture_bytes: usize,
    pub host_structured_equals_fused: bool,
    pub host_all_rlc_modes_equal: bool,
    pub host_normalized_fold_matches_cubic_reference: bool,
    pub variants: Vec<M31CircleBasisVariant>,
    pub fused_rlc_savings_cu: i64,
    pub fused_rlc_savings_percent: f64,
    pub decoded_fused_rlc_savings_vs_structured_cu: i64,
    pub decoded_fused_rlc_savings_vs_structured_percent: f64,
    pub streaming_rlc_savings_vs_structured_cu: i64,
    pub streaming_rlc_savings_vs_structured_percent: f64,
    pub winning_rlc_mode: &'static str,
    pub winning_rlc_cu_mean: f64,
    pub winning_rlc_savings_vs_structured_cu: i64,
    pub winning_rlc_savings_vs_structured_percent: f64,
    pub c1_leaf_hash_incremental_over_empty_cu: i64,
    pub fold_cached_coordinate_derivation_increment_cu: i64,
    pub fold_batch_inverse_syscall_increment_cu: i64,
    pub fold_coordinate_and_batch_inverse_increment_cu: i64,
    pub fold_batch_inverse_backend: &'static str,
    pub corruption_cases: Vec<M31CircleBasisCorruptionCase>,
    pub all_corruptions_rejected: bool,
    pub current_aspis_serialization: bool,
    pub genuine_circle_pcs_integration_implemented: bool,
    pub protocol_or_architecture_ruling_made: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

/// Host/SBF transcript known-answer check: send `TranscriptKat` with the
/// host-pinned digest; the program recomputes with the syscall backend and
/// errors on mismatch (soundness-note appendix, sampler step).
pub fn run_transcript_kat() -> Result<TranscriptKatRun> {
    // host-side assertion first, so a drifted pin fails before spawning a validator
    let host_digest = aspis_core::transcript::transcript_kat(HOST_HASH);
    anyhow::ensure!(
        host_digest == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED,
        "host transcript KAT does not match the pinned constant; re-pin only as a deliberate protocol change"
    );

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::TranscriptKat {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (units, err) = rpc.simulate(&tx)?;
    let mut hex = String::new();
    for b in aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED {
        hex.push_str(&format!("{b:02x}"));
    }
    Ok(TranscriptKatRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-transcript-kat".to_string(),
        validator_version: validator_version(),
        expected_digest_hex: hex,
        matched_on_sbf: err.is_none(),
        simulation_units: units,
        notes: vec![
            "matched_on_sbf=false means the SBF transcript diverged from the host — stop and diagnose before trusting any on-chain measurement.".to_string(),
        ],
    })
}

/// Host/SBF known-answer check for the explicit two-helper v4/s=2 PCS
/// scaffold. The legacy tag-5 KAT remains independently pinned. This is not
/// the final payment-v4 schedule KAT, which will use a later wire tag.
pub fn run_transcript_kat_v4_s2_pcs_scaffold() -> Result<TranscriptKatV4S2PcsScaffoldRun> {
    const INSTRUCTION_WIRE_ORDINAL: u8 = 19;
    let hex = |bytes: &[u8]| {
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };
    let host_digest = aspis_core::transcript::transcript_kat_v4_s2_pcs_scaffold(HOST_HASH);
    ensure!(
        host_digest == aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        "host v4/s=2 PCS-scaffold transcript KAT drifted"
    );
    let v3_pin_unchanged = aspis_core::transcript::transcript_kat(HOST_HASH)
        == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED;
    ensure!(v3_pin_unchanged, "legacy v3 transcript KAT drifted");

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::TranscriptKatV4S2PcsScaffold {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (simulation_units, simulation_error) = rpc.simulate(&transaction)?;
    Ok(TranscriptKatV4S2PcsScaffoldRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command:
            "cargo run --release -p aspis-xtask -- stage2-v4-s2-pcs-scaffold-kat".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        expected_digest_hex: hex(
            &aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        ),
        host_digest_hex: hex(&host_digest),
        host_matched: true,
        matched_on_sbf: simulation_error.is_none(),
        simulation_units,
        simulation_error,
        v3_pin_unchanged,
        notes: vec![
            "Wire tag 19 is append-only and permanently names the two-helper v4/s=2 PCS scaffold; frozen v3 remains tag 5 and final payment-v4 will use tag 20 or later.".to_string(),
            "The vector absorbs one C2 root and both helper evaluations before gamma, then exercises two complete sequential beta/y/mu triples per round.".to_string(),
            "This KAT is necessary but neither a payment-v4 KAT nor a proof measurement; scaffold proof CU is measured separately through production VerifyWithClaim tag 6.".to_string(),
        ],
    })
}

/// Host/SBF known-answer check for the complete payment-v4 schedule through
/// the distinct-query tail, including the dedicated pre-gamma batch work.
pub fn run_final_payment_transcript_kat_v4() -> Result<FinalPaymentTranscriptKatV4Run> {
    const INSTRUCTION_WIRE_ORDINAL: u8 = 20;
    let hex = |bytes: &[u8]| {
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };
    let host_digest = aspis_core::transcript::transcript_kat_final_payment_v4(HOST_HASH);
    ensure!(
        host_digest == aspis_core::transcript::TRANSCRIPT_KAT_FINAL_PAYMENT_V4_EXPECTED,
        "host final payment-v4 transcript KAT drifted"
    );
    let earlier_pins_unchanged = aspis_core::transcript::transcript_kat(HOST_HASH)
        == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED
        && aspis_core::transcript::transcript_kat_v4_s2_pcs_scaffold(HOST_HASH)
            == aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED;
    ensure!(earlier_pins_unchanged, "an earlier transcript KAT drifted");

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::FinalPaymentTranscriptKatV4 {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_FINAL_PAYMENT_V4_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (simulation_units, simulation_error) = rpc.simulate(&transaction)?;
    Ok(FinalPaymentTranscriptKatV4Run {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-final-payment-v4-kat"
            .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        expected_digest_hex: hex(
            &aspis_core::transcript::TRANSCRIPT_KAT_FINAL_PAYMENT_V4_EXPECTED,
        ),
        host_digest_hex: hex(&host_digest),
        host_matched: true,
        matched_on_sbf: simulation_error.is_none(),
        simulation_units,
        simulation_error,
        earlier_pins_unchanged,
        notes: vec![
            "Tag 20 is append-only and now pins the complete profile-15 payment schedule; tags 5 and 19 remain independently pinned.".to_string(),
            "The vector checks and absorbs a domain-separated batch nonce after every statement row and before gamma, then exercises both OOD samples, all fold work records, final work, and 36 distinct queries.".to_string(),
        ],
    })
}

/// Host/SBF known-answer check for the canonical LogUp tagged-tuple encoding.
/// The program is built through the normal production feature set, which does
/// not forward `insecure-test-logup-compression` to `aspis-statement`.
pub fn run_logup_compression_kat() -> Result<LogUpCompressionKatRun> {
    let mut host_phi = [0u8; 16];
    aspis_statement::logup_compression_kat().write_le_bytes(&mut host_phi);
    let host_matched = host_phi == aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED;
    anyhow::ensure!(
        host_matched,
        "host LogUp compression KAT does not match the pinned phi; re-pin only as a deliberate statement-protocol change"
    );

    let root = workspace_root()?;
    let feature_tree = Command::new("cargo")
        .args([
            "tree",
            "-p",
            "aspis-verifier",
            "-e",
            "features",
            "--prefix",
            "none",
        ])
        .current_dir(&root)
        .output()
        .context("inspect verifier dependency features")?;
    ensure!(
        feature_tree.status.success(),
        "cargo tree failed while checking verifier feature isolation: {}",
        String::from_utf8_lossy(&feature_tree.stderr)
    );
    let weakened_feature_forwarded =
        String::from_utf8_lossy(&feature_tree.stdout).contains("insecure-test-logup-compression");
    ensure!(
        !weakened_feature_forwarded,
        "production verifier dependency graph enables insecure-test-logup-compression"
    );
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::LogUpCompressionKat {
            expected_phi: aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let tx = Transaction::new_signed_with_payer(
        &[instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (simulation_units, simulation_error) = rpc.simulate(&tx)?;

    let to_hex = |bytes: &[u8]| {
        let mut hex = String::new();
        for byte in bytes {
            hex.push_str(&format!("{byte:02x}"));
        }
        hex
    };
    Ok(LogUpCompressionKatRun {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage2-logup-compression-kat".to_string(),
        validator_version: validator_version(),
        expected_phi_hex: to_hex(&aspis_statement::LOGUP_COMPRESSION_KAT_EXPECTED),
        host_phi_hex: to_hex(&host_phi),
        host_matched,
        matched_on_sbf: simulation_error.is_none(),
        simulation_units,
        simulation_error,
        weakened_feature_forwarded_to_verifier: weakened_feature_forwarded,
        notes: vec![
            "The runner mechanically checks `cargo tree -p aspis-verifier -e features` before the SBF build; the deliberately weakened lambda^0 compression feature must be absent.".to_string(),
            "matched_on_sbf=false means host and SBF disagree on the pinned tagged-tuple phi; stop before regenerating transcript-bound statement artifacts.".to_string(),
        ],
    })
}

/// Isolated SBF A/B for the second sequential per-round OOD relation sample.
/// Both rows run the same lr10/four-round claim-carrying kernel; subtracting
/// s=1 from s=2 removes instruction and common sumcheck overhead without
/// importing transcript-induced query/Merkle variance from a full proof.
pub fn run_stage2_s2_ood_probe() -> Result<OodSampleRelationProbeSummary> {
    const REPETITIONS: usize = 5;
    const INSTRUCTION_WIRE_ORDINAL: u8 = 18;
    let pinned = [
        (1u8, aspis_core::verify::OOD_SAMPLE_PROBE_S1_EXPECTED),
        (2u8, aspis_core::verify::OOD_SAMPLE_PROBE_S2_EXPECTED),
    ];
    let to_hex = |bytes: &[u8]| {
        let mut hex = String::new();
        for byte in bytes {
            hex.push_str(&format!("{byte:02x}"));
        }
        hex
    };

    let mut host_rows = Vec::with_capacity(pinned.len());
    for (samples_per_round, expected_sink) in pinned {
        let value = aspis_core::verify::ood_sample_relation_probe(HOST_HASH, samples_per_round)
            .map_err(|error| anyhow!("host OOD sample probe failed: {error:?}"))?;
        let mut host_sink = [0u8; 16];
        value.write_le_bytes(&mut host_sink);
        anyhow::ensure!(
            host_sink == expected_sink,
            "host s={samples_per_round} OOD probe sink drifted: expected {}, got {}; re-pin only for a deliberate probe-kernel change",
            to_hex(&expected_sink),
            to_hex(&host_sink)
        );
        host_rows.push((samples_per_round, expected_sink, host_sink));
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut variants = Vec::with_capacity(host_rows.len());
    for (samples_per_round, expected_sink, host_sink) in host_rows {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::OodSampleRelationProbe {
                samples_per_round,
                expected_sink,
            })?,
        };
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        variants.push(OodSampleRelationProbeVariant {
            samples_per_round,
            expected_sink_hex: to_hex(&expected_sink),
            host_sink_hex: to_hex(&host_sink),
            host_sink_matched: host_sink == expected_sink,
            sbf_sink_matched: true,
            simulation_cu,
            simulation_cu_mean,
        });
    }
    anyhow::ensure!(
        variants.len() == 2
            && variants[0].samples_per_round == 1
            && variants[1].samples_per_round == 2,
        "OOD probe A/B rows are not in canonical s=1, s=2 order"
    );
    let incremental =
        (variants[1].simulation_cu_mean - variants[0].simulation_cu_mean).round() as i64;

    Ok(OodSampleRelationProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-s2-ood-probe".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        repetitions: REPETITIONS,
        log_rows: 10,
        rounds: 4,
        terminal_coefficients: 4,
        existing_multilinear_claim_components: 1,
        variants,
        pcs_s2_second_ood_sample_transcript_relation_cu: incremental,
        superseded_probe_local_generated_value_delta_cu: 49_155,
        probe_local_value_generation_contamination_removed_cu: 49_155 - incremental,
        previous_estimate_bracket_cu: [5_000, 12_000],
        delta_over_previous_bracket_max_cu: incremental - 12_000,
        structural_proof_record_delta_bytes: 64,
        extra_transcript_hash_calls_no_retry: 20,
        extra_geometric_fold_operations: 10,
        extra_terminal_component_evaluations: 16,
        production_transcript_kat_unchanged: true,
        production_proof_format_unchanged: true,
        included_work: vec![
            "four second sequential beta/y/mu triples: exact-uniform OOD sampling, canonical QM31 decode, y absorption, and mu sampling".to_string(),
            "four relation-value mu*y updates and four geometric relation-weight insertions, including allocator behavior".to_string(),
            "every later WeightAccumulator fold of the four added components (10 geometric folds total)".to_string(),
            "terminal dot evaluation of the four added components across four final coefficients (16 component evaluations)".to_string(),
        ],
        excluded_work: vec![
            "proof commitments, roots, Merkle openings, query derivation, and transcript-induced query/frontier variance".to_string(),
            "proof-account upload CU and the eventual v4 C2 leaf/claim widening".to_string(),
            "statement constraint composition, masking, and prover-side OOD evaluation work".to_string(),
        ],
        notes: vec![
            "Book only pcs_s2_second_ood_sample_transcript_relation_cu as the isolated pre-v4 projection line; the integrated v4 eight-draw SBF measurement replaces it.".to_string(),
            "The s=1 and s=2 instructions have identical Borsh size and expected-sink comparison overhead; their deterministic mean difference isolates the added second samples and retained relation-weight work.".to_string(),
            "The probe reuses the production canonical OOD sample kernel but does not select a proof format. VERSION=3 and TRANSCRIPT_KAT_EXPECTED remain untouched.".to_string(),
            "The +64-byte figure is the structural four-round record delta only; eventual full-proof bytes can move further when the v4 transcript changes openings.".to_string(),
            format!("The measured {incremental}-CU delta refutes the old 5-12K bracket: that intuition priced transcript work but omitted the four retained components' later folds and terminal evaluations."),
            format!("SUPERSEDED measurement: a first probe version generated and encoded each synthetic y inside the sample loop and measured 49,155 CU. Replacing those probe-only operations with a fixed canonical byte table removed {} CU of contamination; the pinned transcript sinks did not move.", 49_155 - incremental),
        ],
    })
}

/// Same-build host/SBF comparison of four unselected two-point MLE batching
/// shapes. The SBF kernel consumes precomputed relation messages and runs
/// verifier-side checks only; no row is a product projection or ruling.
pub fn run_stage2_two_point_batching_probe() -> Result<TwoPointBatchingProbeSummary> {
    use aspis_core::two_point::{
        two_point_batching_probe, TwoPointBatchingMode, TWO_POINT_BATCHING_EXPECTED_SINKS,
        TWO_POINT_COORDINATES, TWO_POINT_LOG_ROWS, TWO_POINT_POINTS_BYTES, TWO_POINT_ROUNDS,
        TWO_POINT_STATEMENT_VALUES, TWO_POINT_VALUES_BYTES,
    };

    const REPETITIONS: usize = 5;
    const INSTRUCTION_WIRE_ORDINAL: u8 = 25;
    let modes = [
        (
            "one_point_baseline",
            TwoPointBatchingDiagnosticMode::OnePointBaseline,
            TwoPointBatchingMode::OnePointBaseline,
        ),
        (
            "fresh_kappa_single_lane",
            TwoPointBatchingDiagnosticMode::FreshKappaSingleLane,
            TwoPointBatchingMode::FreshKappaSingleLane,
        ),
        (
            "two_independent_relation_lanes",
            TwoPointBatchingDiagnosticMode::TwoIndependentRelationLanes,
            TwoPointBatchingMode::TwoIndependentRelationLanes,
        ),
        (
            "disjoint_gamma51_single_lane",
            TwoPointBatchingDiagnosticMode::DisjointGamma51SingleLane,
            TwoPointBatchingMode::DisjointGamma51SingleLane,
        ),
    ];
    let hex = |bytes: &[u8]| {
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };

    let mut host_rows = Vec::with_capacity(modes.len());
    for (ordinal, (name, program_mode, core_mode)) in modes.into_iter().enumerate() {
        let result = two_point_batching_probe(HOST_HASH, core_mode)
            .map_err(|error| anyhow!("host two-point mode {name} failed: {error:?}"))?;
        let mut host_sink = [0u8; 16];
        result.sink.write_le_bytes(&mut host_sink);
        let expected_sink = TWO_POINT_BATCHING_EXPECTED_SINKS[ordinal];
        ensure!(
            host_sink == expected_sink,
            "host two-point mode {name} sink drifted: expected {}, got {}",
            hex(&expected_sink),
            hex(&host_sink)
        );
        host_rows.push((
            ordinal,
            name,
            program_mode,
            expected_sink,
            host_sink,
            result,
        ));
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let baseline_proof_bytes = host_rows[0].5.relation_proof_bytes;
    let baseline_hash_calls = host_rows[0].5.transcript_hash_calls_no_retry;
    let mut variants = Vec::with_capacity(host_rows.len());
    let mut baseline_cu_mean: Option<f64> = None;
    for (ordinal, name, program_mode, expected_sink, host_sink, result) in host_rows {
        let data = to_vec(&AspisInstruction::TwoPointBatchingDiagnostic {
            mode: program_mode,
            expected_sink,
        })?;
        let instruction_data_bytes = data.len();
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data,
        };
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
        ensure!(
            simulation_cu.windows(2).all(|pair| pair[0] == pair[1]),
            "two-point mode {name} was nondeterministic across five identical simulations: {simulation_cu:?}"
        );
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        let baseline = *baseline_cu_mean.get_or_insert(simulation_cu_mean);
        variants.push(TwoPointBatchingProbeVariant {
            mode: name,
            mode_ordinal: ordinal as u8,
            expected_sink_hex: hex(&expected_sink),
            host_sink_hex: hex(&host_sink),
            host_sink_matched: host_sink == expected_sink,
            sbf_sink_matched: true,
            simulation_cu,
            simulation_cu_mean,
            simulation_cu_delta_vs_one_point: (simulation_cu_mean - baseline).round() as i64,
            relation_lanes: result.relation_lanes,
            point_components: result.point_components,
            relation_polynomials: result.relation_polynomials,
            relation_proof_bytes: result.relation_proof_bytes,
            relation_proof_bytes_delta_vs_one_point: i64::from(result.relation_proof_bytes)
                - i64::from(baseline_proof_bytes),
            instruction_data_bytes,
            transcript_hash_calls_no_retry: result.transcript_hash_calls_no_retry,
            transcript_hash_calls_delta_vs_one_point: result.transcript_hash_calls_no_retry as i32
                - baseline_hash_calls as i32,
        });
    }

    Ok(TwoPointBatchingProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-two-point-batching-probe"
            .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        repetitions: REPETITIONS,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame: "default runtime heap; no request_heap_frame instruction",
        log_rows: TWO_POINT_LOG_ROWS,
        rounds: TWO_POINT_ROUNDS,
        statement_points: 2,
        statement_values: TWO_POINT_STATEMENT_VALUES,
        pre_gamma_point_bytes: TWO_POINT_POINTS_BYTES,
        pre_gamma_value_bytes: TWO_POINT_VALUES_BYTES,
        variants,
        production_rule_selected: false,
        product_projection_updated: false,
        architecture_ruling_made: false,
        included_work: vec![
            format!("the same two {TWO_POINT_COORDINATES}-coordinate MLE points and the same 102-value/1632-byte block are transcript-absorbed before gamma in every mode"),
            "canonical decoding of embedded initial claims, degree-6 relation messages, and terminal four coefficients; no prover polynomial construction runs on SBF".to_string(),
            "four rounds of relation boundary/evaluation checks, shared transcript fold challenges, scaled WeightAccumulator folds, and terminal dots".to_string(),
            "fresh-kappa alone performs one extra exact-uniform challenge squeeze after gamma; independent lanes alone absorb/check a second relation polynomial per round".to_string(),
        ],
        excluded_work: vec![
            "proof roots, Merkle openings, circle encoding, query work, statement composition, hiding, and payment semantics".to_string(),
            "prover-side degree-6 polynomial construction and full 1024-coefficient relation dots".to_string(),
            "any soundness-ledger amendment, KAT re-pin, product CU projection, option selection, or transaction-architecture ruling".to_string(),
        ],
        notes: vec![
            "Raw CU rows are same-build local-validator simulations with five identical repetitions and a 1,400,000-CU limit; no custom heap request is present.".to_string(),
            "relation_proof_bytes counts only the four-round degree-6 relation-message payload (7 canonical QM31 values per lane per round). It is not a full proof-size projection.".to_string(),
            "transcript_hash_calls_no_retry counts SHA-256 backend calls in this diagnostic schedule, including absorb and squeeze-state advance calls; exact-uniform rejection retries would add calls but do not occur in the pinned fixture.".to_string(),
            "The one-point row is a cost baseline and is explicitly insecure for two-point binding; all four rows remain owner-decision inputs only.".to_string(),
        ],
    })
}

/// Build and measure the selected complete fresh-kappa circle-PCS verifier.
pub fn run_stage2_m31_fresh_kappa_sbf() -> Result<M31FreshKappaSbfSummary> {
    use aspis_core::circle_prefix::CANDIDATE_STATEMENT_POINT_COORDINATES;
    use aspis_core::field::{CM31, M31, P, QM31};
    use aspis_prover::circle_candidate::{C1_COLUMNS, C2_COLUMNS, TRACE_LEN};
    use aspis_prover::circle_candidate_prefix::build_fresh_kappa_candidate_proof;
    use sha2::{Digest as _, Sha256};

    #[derive(Clone, Copy)]
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
            self.0
        }
        fn m31(&mut self) -> M31 {
            M31((self.next() as u32) % P)
        }
        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

    let mut rng = Rng(0x5052_4546_4958_4341);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| rng.m31().add(M31((column * 65_537 + row * 257 + 1) as u32)))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut value = rng.qm31();
                    value.c0.a = value.c0.a.add(M31((helper * 4_099 + row + 1) as u32));
                    value
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES] = core::array::from_fn(|coordinate| {
        let mut value = rng.qm31();
        value.c1.b = value.c1.b.add(M31((coordinate * 313 + 17) as u32));
        value
    });
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/m31-circle/sequential-candidate/v1").into();
    let built = build_fresh_kappa_candidate_proof(&c1, &c2, z, statement_digest, HOST_HASH)
        .map_err(|error| anyhow!("build fresh-kappa fixture: {error:?}"))?;
    let proof = built.bytes;
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    ensure!(
        proof_sha256 == "68a536081d60264494206895bb99f18c0633174583000fb7398d86dff50505ca",
        "selected proof fixture drifted: {proof_sha256}"
    );
    let claim_z = z.map(|value| {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        bytes
    });

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof, true)?;

    let simulate = |digest: [u8; 32]| -> Result<SimulationResult> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::VerifyM31CircleFreshKappa {
                statement_digest: digest,
                claim_z: claim_z.to_vec(),
            })?,
        };
        let blockhash = rpc.latest_blockhash()?;
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        rpc.simulate_verbose(&tx)
    };

    let mut simulation_cu = Vec::with_capacity(VERIFY_REPETITIONS);
    let mut markers = Vec::new();
    for repetition in 0..VERIFY_REPETITIONS {
        let result = simulate(statement_digest)?;
        ensure!(
            result.err.is_none(),
            "selected fresh-kappa SBF verifier rejected: {:?}",
            result.err
        );
        if repetition == 0 {
            markers = parse_cu_markers(&result.logs, "aspis-cu:");
        }
        simulation_cu.push(
            result
                .units
                .ok_or_else(|| anyhow!("simulation omitted CU"))?,
        );
    }
    let mut stale_digest = statement_digest;
    stale_digest[0] ^= 1;
    let stale_result = simulate(stale_digest)?;
    ensure!(
        stale_result.err.is_some(),
        "stale statement unexpectedly accepted on SBF"
    );
    let simulation_cu_mean = simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;

    Ok(M31FreshKappaSbfSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-m31-fresh-kappa-sbf".into(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 26,
        proof_bytes: proof.len(),
        proof_sha256,
        upload_chunks,
        simulation_cu,
        simulation_cu_mean,
        isolated_rlc_seam_reference_cu: 501_989,
        reconciliation_rule: "the in-place PCS total already contains the exact-49 RLC seam; never add the isolated seam artifact to this total".into(),
        markers,
        accepted_all_runs: true,
        stale_statement_rejected: true,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        explicit_nonclaims: vec![
            "fixture C2 is not payment-derived".into(),
            "no hiding or economic state transition is executed".into(),
            "this PCS measurement is not a complete one-transaction product total".into(),
        ],
    })
}

/// Measure the literal q74/g32 Johnson query target. The complete verifier is
/// expected to cross the 1.4M transaction ceiling, so exact query work is
/// partitioned and reconciled as `base + sum(segment - base)`.
pub fn run_stage2_m31_johnson_sbf() -> Result<M31JohnsonSbfSummary> {
    use aspis_core::circle_candidate_verify::verify_johnson_candidate_segment;
    use aspis_core::circle_line_merkle::derive_circle_line_query_indices;
    use aspis_core::circle_openings::CircleQuerySegment;
    use aspis_core::circle_prefix::{
        run_candidate_transcript_schedule_host_for_shape, CandidateOneLaneBatchingMode,
        CandidatePrefix, CANDIDATE_STATEMENT_POINT_COORDINATES, JOHNSON_CANDIDATE_GRINDING_BITS,
        JOHNSON_CANDIDATE_QUERY_COUNT, JOHNSON_CANDIDATE_SHAPE,
    };
    use aspis_core::field::{CM31, M31, P, QM31};
    use aspis_prover::circle_candidate::{C1_COLUMNS, C2_COLUMNS, TRACE_LEN};
    use aspis_prover::circle_candidate_prefix::build_fresh_kappa_candidate_proof_for_shape;
    use sha2::{Digest as _, Sha256};

    const QUERY_COUNT: usize = JOHNSON_CANDIDATE_QUERY_COUNT as usize;
    const LAYER0_CHUNK: usize = 20;
    const RHO: f64 = 0.25;
    const ETA: f64 = 0.025;

    #[derive(Clone, Copy)]
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
            self.0
        }
        fn m31(&mut self) -> M31 {
            M31((self.next() as u32) % P)
        }
        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

    let profile = &aspis_core::params::PROFILE_JOHNSON_LR10_Q74_G32;
    ensure!(profile.id == JOHNSON_CANDIDATE_SHAPE.profile_id);
    ensure!(profile.query_count == JOHNSON_CANDIDATE_QUERY_COUNT);
    ensure!(profile.grinding_bits == JOHNSON_CANDIDATE_GRINDING_BITS);

    // Keep the coefficient/public-input fixture byte-identical to the q36
    // selected measurement; only the transcript-bound profile shape changes.
    let mut rng = Rng(0x5052_4546_4958_4341);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| rng.m31().add(M31((column * 65_537 + row * 257 + 1) as u32)))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut value = rng.qm31();
                    value.c0.a = value.c0.a.add(M31((helper * 4_099 + row + 1) as u32));
                    value
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES] = core::array::from_fn(|coordinate| {
        let mut value = rng.qm31();
        value.c1.b = value.c1.b.add(M31((coordinate * 313 + 17) as u32));
        value
    });
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/m31-circle/sequential-candidate/v1").into();

    let root = workspace_root()?;
    let proof_dir = root.join("results/stage2/proofs");
    fs::create_dir_all(&proof_dir)?;
    let proof_path = proof_dir.join("m31_circle_fresh_kappa_johnson_q74_g32.bin");
    let cached = fs::read(&proof_path).ok().filter(|proof| {
        verify_johnson_candidate_segment(
            proof,
            &statement_digest,
            &z,
            HOST_HASH,
            CircleQuerySegment::Full,
        )
        .is_ok()
    });
    let (proof, proof_source, grinding_generation_seconds) = if let Some(proof) = cached {
        (
            proof,
            "reused host-verified literal q74/g32 cache".to_string(),
            None,
        )
    } else {
        eprintln!("stage2-m31-johnson-sbf: searching literal q74/g32 nonce (cached after success)");
        let started = Instant::now();
        let built = build_fresh_kappa_candidate_proof_for_shape::<QUERY_COUNT>(
            &c1,
            &c2,
            z,
            statement_digest,
            HOST_HASH,
            JOHNSON_CANDIDATE_SHAPE,
        )
        .map_err(|error| anyhow!("build Johnson fresh-kappa fixture: {error:?}"))?;
        let elapsed = started.elapsed().as_secs_f64();
        ensure!(
            verify_johnson_candidate_segment(
                &built.bytes,
                &statement_digest,
                &z,
                HOST_HASH,
                CircleQuerySegment::Full,
            )
            .is_ok(),
            "fresh literal q74/g32 proof failed the host verifier"
        );
        fs::write(&proof_path, &built.bytes)?;
        (
            built.bytes,
            "generated and cached literal q74/g32 proof".to_string(),
            Some(elapsed),
        )
    };
    let full_host_verifier_accepted = verify_johnson_candidate_segment(
        &proof,
        &statement_digest,
        &z,
        HOST_HASH,
        CircleQuerySegment::Full,
    )
    .is_ok();
    ensure!(full_host_verifier_accepted);

    let (prefix, _) = CandidatePrefix::parse_from_proof_for_shape(&proof, JOHNSON_CANDIDATE_SHAPE)
        .map_err(|error| anyhow!("parse cached Johnson proof: {error:?}"))?;
    let schedule = run_candidate_transcript_schedule_host_for_shape::<QUERY_COUNT>(
        HOST_HASH,
        &prefix,
        &statement_digest,
        &z,
        CandidateOneLaneBatchingMode::FreshKappa,
        JOHNSON_CANDIDATE_GRINDING_BITS,
    )
    .map_err(|error| anyhow!("replay cached Johnson transcript: {error:?}"))?;
    let indices = derive_circle_line_query_indices(&schedule.queries)
        .map_err(|error| anyhow!("derive Johnson query indices: {error:?}"))?;
    let unique_layer_indices = [
        indices.layer0.len(),
        indices.later[0].len(),
        indices.later[1].len(),
        indices.later[2].len(),
    ];
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let claim_z = z.map(|value| {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        bytes
    });

    let simulate = |digest: [u8; 32],
                    phase: JohnsonM31CircleDiagnosticPhase,
                    start: u16,
                    end: u16|
     -> Result<SimulationResult> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::MeasureM31CircleJohnson {
                statement_digest: digest,
                claim_z: claim_z.to_vec(),
                phase,
                start,
                end,
            })?,
        };
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            rpc.latest_blockhash()?,
        );
        rpc.simulate_verbose(&tx)
    };

    let run_phase = |label: String,
                     phase: JohnsonM31CircleDiagnosticPhase,
                     start: u16,
                     end: u16|
     -> Result<M31JohnsonPhaseRun> {
        let mut simulation_cu = Vec::with_capacity(VERIFY_REPETITIONS);
        for _ in 0..VERIFY_REPETITIONS {
            let result = simulate(statement_digest, phase, start, end)?;
            ensure!(
                result.err.is_none(),
                "Johnson phase {label} rejected: {:?}",
                result.err
            );
            simulation_cu.push(
                result
                    .units
                    .ok_or_else(|| anyhow!("Johnson phase {label} omitted CU"))?,
            );
        }
        ensure!(
            simulation_cu.iter().all(|&value| value == simulation_cu[0]),
            "Johnson phase {label} was not deterministic: {simulation_cu:?}"
        );
        Ok(M31JohnsonPhaseRun {
            label,
            phase: format!("{phase:?}"),
            start,
            end,
            selected_cu: simulation_cu[0],
            simulation_cu,
        })
    };

    let base = run_phase(
        "shared_prefix_transcript_relation_merkle_and_query_setup".to_string(),
        JohnsonM31CircleDiagnosticPhase::PreparedBase,
        0,
        0,
    )?;
    let shared_base_cu = base.selected_cu;
    let mut phase_runs = vec![base];
    let mut start = 0usize;
    while start < indices.layer0.len() {
        let end = (start + LAYER0_CHUNK).min(indices.layer0.len());
        phase_runs.push(run_phase(
            format!("layer0_unique_ordinals_{start}_{end}"),
            JohnsonM31CircleDiagnosticPhase::Layer0Range,
            start as u16,
            end as u16,
        )?);
        start = end;
    }
    phase_runs.push(run_phase(
        "all_unique_later_layer_transitions".to_string(),
        JohnsonM31CircleDiagnosticPhase::LaterAll,
        0,
        0,
    )?);

    let segment_count = phase_runs.len() - 1;
    let segment_sum = phase_runs[1..]
        .iter()
        .map(|run| run.selected_cu)
        .sum::<u64>();
    let repeated_base = (segment_count as u64 - 1) * shared_base_cu;
    let reconciled_integrated_cu = segment_sum
        .checked_sub(repeated_base)
        .context("Johnson overlap subtraction underflow")?;

    let full = simulate(
        statement_digest,
        JohnsonM31CircleDiagnosticPhase::Full,
        0,
        0,
    )?;
    if full.err.is_none() {
        let direct = full
            .units
            .context("successful full Johnson run omitted CU")?;
        ensure!(
            direct.abs_diff(reconciled_integrated_cu) <= 2_000,
            "direct/reconciled Johnson totals diverged: direct={direct}, reconciled={reconciled_integrated_cu}"
        );
    }
    let mut stale_digest = statement_digest;
    stale_digest[0] ^= 1;
    let stale = simulate(
        stale_digest,
        JohnsonM31CircleDiagnosticPhase::PreparedBase,
        0,
        0,
    )?;
    ensure!(
        stale.err.is_some(),
        "stale Johnson statement unexpectedly accepted"
    );

    let bits_per_query = -(RHO.sqrt() + ETA).log2();
    let query_round_bits = f64::from(JOHNSON_CANDIDATE_GRINDING_BITS)
        + f64::from(JOHNSON_CANDIDATE_QUERY_COUNT) * bits_per_query;
    Ok(M31JohnsonSbfSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-m31-johnson-sbf".into(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 27,
        profile: profile.name.to_string(),
        query_count: JOHNSON_CANDIDATE_QUERY_COUNT,
        grinding_bits: JOHNSON_CANDIDATE_GRINDING_BITS,
        johnson_rho: RHO,
        johnson_eta: ETA,
        bits_per_query,
        query_round_bits,
        proof_bytes: proof.len(),
        proof_sha256,
        proof_cache: proof_path.display().to_string(),
        proof_source,
        grinding_generation_seconds,
        upload_chunks,
        unique_layer_indices,
        shared_base_cu,
        phase_runs,
        reconciliation_formula: format!(
            "sum({segment_count} segment totals) - ({} repeated bases * {shared_base_cu} CU); each segment already includes the prefix/transcript/relation/Merkle/query-setup base",
            segment_count - 1
        ),
        reconciled_integrated_cu,
        headroom_vs_1_4m_cu: 1_400_000 - reconciled_integrated_cu as i64,
        full_simulation_cu_at_cap: full.units,
        full_simulation_error: full.err,
        full_host_verifier_accepted,
        stale_statement_rejected: stale.err.is_some(),
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        soundness_caveat: "q74/g32 closes only the pinned Johnson query-round term (100.791 bits). The repository's existing Johnson T1 union remains 73.6534 bits without per-fold PoW, and the exact circle/S-two transport theorem scope must still be closed before claiming 100-bit full-system soundness.".into(),
        explicit_nonclaims: vec![
            "the reconciled number is PCS-only: composition, payment semantics, hiding, and state transition remain excluded".into(),
            "the diagnostic phase instructions are not production acceptance tags".into(),
            "the Johnson query-radius measurement does not promote the capacity-shaped q36/g16 result to proven soundness".into(),
        ],
    })
}

/// Literal rate-1/16 q36/g32 Johnson-query measurement. This is the clean
/// code-rate/query-count trade that can reclaim the q74 query premium without
/// changing the M31 leaf algebra or relying on packed-fiber MCA.
pub fn run_stage2_m31_rate16_sbf() -> Result<M31Rate16SbfSummary> {
    use aspis_core::circle_candidate_verify::verify_rate16_candidate_segment;
    use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
    use aspis_core::circle_openings::CircleQuerySegment;
    use aspis_core::circle_prefix::{
        run_candidate_transcript_schedule_host_for_shape, CandidateOneLaneBatchingMode,
        CandidatePrefix, CANDIDATE_STATEMENT_POINT_COORDINATES, RATE16_CANDIDATE_GRINDING_BITS,
        RATE16_CANDIDATE_QUERY_COUNT, RATE16_CANDIDATE_SHAPE,
    };
    use aspis_core::field::{CM31, M31, P, QM31};
    use aspis_prover::circle_candidate::{C1_COLUMNS, C2_COLUMNS, TRACE_LEN};
    use aspis_prover::circle_candidate_prefix::build_fresh_kappa_candidate_proof_for_shape;
    use sha2::{Digest as _, Sha256};

    const QUERY_COUNT: usize = RATE16_CANDIDATE_QUERY_COUNT as usize;
    const FIBER_COUNT: usize = 1 << 12;
    const RHO: f64 = 1.0 / 16.0;
    const ETA: f64 = 0.0125;

    #[derive(Clone, Copy)]
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
            self.0
        }
        fn m31(&mut self) -> M31 {
            M31((self.next() as u32) % P)
        }
        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

    let profile = &aspis_core::params::PROFILE_JOHNSON_LR10_B4_Q36_G32;
    ensure!(profile.id == RATE16_CANDIDATE_SHAPE.profile_id);
    ensure!(profile.log_blowup == RATE16_CANDIDATE_SHAPE.log_blowup);
    ensure!(profile.query_count == RATE16_CANDIDATE_QUERY_COUNT);
    ensure!(profile.grinding_bits == RATE16_CANDIDATE_GRINDING_BITS);

    let mut rng = Rng(0x5052_4546_4958_4341);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| rng.m31().add(M31((column * 65_537 + row * 257 + 1) as u32)))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut value = rng.qm31();
                    value.c0.a = value.c0.a.add(M31((helper * 4_099 + row + 1) as u32));
                    value
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES] = core::array::from_fn(|coordinate| {
        let mut value = rng.qm31();
        value.c1.b = value.c1.b.add(M31((coordinate * 313 + 17) as u32));
        value
    });
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/m31-circle/sequential-candidate/v1").into();

    let root = workspace_root()?;
    let proof_dir = root.join("results/stage2/proofs");
    fs::create_dir_all(&proof_dir)?;
    let proof_path = proof_dir.join("m31_circle_fresh_kappa_johnson_b4_q36_g32.bin");
    let cached = fs::read(&proof_path).ok().filter(|proof| {
        verify_rate16_candidate_segment(
            proof,
            &statement_digest,
            &z,
            HOST_HASH,
            CircleQuerySegment::Full,
        )
        .is_ok()
    });
    let (proof, proof_source, grinding_generation_seconds) = if let Some(proof) = cached {
        (
            proof,
            "reused host-verified literal rate-1/16 q36/g32 cache".to_string(),
            None,
        )
    } else {
        eprintln!(
            "stage2-m31-rate16-sbf: searching literal rate-1/16 q36/g32 nonce (cached after success)"
        );
        let started = Instant::now();
        let built = build_fresh_kappa_candidate_proof_for_shape::<QUERY_COUNT>(
            &c1,
            &c2,
            z,
            statement_digest,
            HOST_HASH,
            RATE16_CANDIDATE_SHAPE,
        )
        .map_err(|error| anyhow!("build rate-1/16 fresh-kappa fixture: {error:?}"))?;
        let elapsed = started.elapsed().as_secs_f64();
        ensure!(
            verify_rate16_candidate_segment(
                &built.bytes,
                &statement_digest,
                &z,
                HOST_HASH,
                CircleQuerySegment::Full,
            )
            .is_ok(),
            "fresh literal rate-1/16 proof failed the host verifier"
        );
        fs::write(&proof_path, &built.bytes)?;
        (
            built.bytes,
            "generated and cached literal rate-1/16 q36/g32 proof".to_string(),
            Some(elapsed),
        )
    };
    let full_host_verifier_accepted = verify_rate16_candidate_segment(
        &proof,
        &statement_digest,
        &z,
        HOST_HASH,
        CircleQuerySegment::Full,
    )
    .is_ok();
    ensure!(full_host_verifier_accepted);

    let (prefix, _) = CandidatePrefix::parse_from_proof_for_shape(&proof, RATE16_CANDIDATE_SHAPE)
        .map_err(|error| anyhow!("parse cached rate-1/16 proof: {error:?}"))?;
    let schedule = run_candidate_transcript_schedule_host_for_shape::<QUERY_COUNT>(
        HOST_HASH,
        &prefix,
        &statement_digest,
        &z,
        CandidateOneLaneBatchingMode::FreshKappa,
        RATE16_CANDIDATE_GRINDING_BITS,
    )
    .map_err(|error| anyhow!("replay cached rate-1/16 transcript: {error:?}"))?;
    let indices = derive_circle_line_query_indices_for_count(&schedule.queries, FIBER_COUNT)
        .map_err(|error| anyhow!("derive rate-1/16 query indices: {error:?}"))?;
    let unique_layer_indices = [
        indices.layer0.len(),
        indices.later[0].len(),
        indices.later[1].len(),
        indices.later[2].len(),
    ];
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let claim_z = z.map(|value| {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        bytes
    });

    let simulate = |digest: [u8; 32],
                    phase: JohnsonM31CircleDiagnosticPhase,
                    start: u16,
                    end: u16|
     -> Result<SimulationResult> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::MeasureM31CircleRate16 {
                statement_digest: digest,
                claim_z: claim_z.to_vec(),
                phase,
                start,
                end,
            })?,
        };
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            rpc.latest_blockhash()?,
        );
        rpc.simulate_verbose(&tx)
    };

    let run_accepted =
        |phase: JohnsonM31CircleDiagnosticPhase, start: u16, end: u16| -> Result<u64> {
            let mut units = Vec::with_capacity(VERIFY_REPETITIONS);
            for _ in 0..VERIFY_REPETITIONS {
                let result = simulate(statement_digest, phase, start, end)?;
                ensure!(
                    result.err.is_none(),
                    "rate-1/16 phase rejected: {:?}",
                    result.err
                );
                units.push(result.units.context("rate-1/16 phase omitted CU")?);
            }
            ensure!(units.iter().all(|&value| value == units[0]));
            Ok(units[0])
        };

    let shared_base_cu = run_accepted(JohnsonM31CircleDiagnosticPhase::PreparedBase, 0, 0)?;
    let layer0_inclusive_cu = run_accepted(
        JohnsonM31CircleDiagnosticPhase::Layer0Range,
        0,
        indices.layer0.len() as u16,
    )?;
    let later_inclusive_cu = run_accepted(JohnsonM31CircleDiagnosticPhase::LaterAll, 0, 0)?;
    let segment_reconciled_cu = layer0_inclusive_cu + later_inclusive_cu - shared_base_cu;

    let mut full_simulation_cu = Vec::with_capacity(VERIFY_REPETITIONS);
    let mut full_simulation_errors = Vec::with_capacity(VERIFY_REPETITIONS);
    for _ in 0..VERIFY_REPETITIONS {
        let result = simulate(
            statement_digest,
            JohnsonM31CircleDiagnosticPhase::Full,
            0,
            0,
        )?;
        full_simulation_cu.push(result.units);
        full_simulation_errors.push(result.err);
    }
    let direct_integrated_cu = if full_simulation_errors.iter().all(Option::is_none) {
        let direct = full_simulation_cu[0].context("successful rate-1/16 run omitted CU")?;
        ensure!(full_simulation_cu
            .iter()
            .all(|value| *value == Some(direct)));
        Some(direct)
    } else {
        ensure!(full_simulation_errors.iter().all(Option::is_some));
        None
    };
    let segment_delta_vs_direct_cu =
        direct_integrated_cu.map(|direct| segment_reconciled_cu as i64 - direct as i64);
    if let Some(delta) = segment_delta_vs_direct_cu {
        ensure!(
            delta.unsigned_abs() <= 2_000,
            "rate-1/16 direct/segment ledger diverged by {delta} CU"
        );
    }
    let selected_integrated_cu = direct_integrated_cu.unwrap_or(segment_reconciled_cu);

    let simulate_composition = |stress: bool| -> Result<SimulationResult> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::MeasureM31CircleRate16Composition {
                statement_digest,
                claim_z: claim_z.to_vec(),
                stress,
            })?,
        };
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            rpc.latest_blockhash()?,
        );
        rpc.simulate_verbose(&tx)
    };
    let run_composition = |stress: bool| -> Result<(Option<u64>, Option<String>)> {
        let mut first: Option<(Option<u64>, Option<String>)> = None;
        for _ in 0..VERIFY_REPETITIONS {
            let result = simulate_composition(stress)?;
            let current = (result.units, result.err);
            if let Some(expected) = &first {
                ensure!(
                    &current == expected,
                    "rate-1/16 composition was nondeterministic"
                );
            } else {
                first = Some(current);
            }
        }
        Ok(first.unwrap())
    };
    let (composition_central_cu, composition_central_error) = run_composition(false)?;
    let (composition_stress_cu, composition_stress_error) = run_composition(true)?;
    let composition_central_increment_cu =
        composition_central_cu.map(|cu| cu as i64 - selected_integrated_cu as i64);
    let composition_central_headroom_vs_1_4m_cu =
        composition_central_cu.map(|cu| 1_400_000 - cu as i64);
    let composition_stress_increment_cu =
        composition_stress_cu.map(|cu| cu as i64 - selected_integrated_cu as i64);
    let composition_stress_headroom_vs_1_4m_cu =
        composition_stress_cu.map(|cu| 1_400_000 - cu as i64);

    let mut stale_digest = statement_digest;
    stale_digest[0] ^= 1;
    let stale = simulate(
        stale_digest,
        JohnsonM31CircleDiagnosticPhase::PreparedBase,
        0,
        0,
    )?;
    ensure!(
        stale.err.is_some(),
        "stale rate-1/16 statement unexpectedly accepted"
    );

    let bits_per_query = -(RHO.sqrt() + ETA).log2();
    let query_round_bits = f64::from(RATE16_CANDIDATE_GRINDING_BITS)
        + f64::from(RATE16_CANDIDATE_QUERY_COUNT) * bits_per_query;
    Ok(M31Rate16SbfSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-m31-rate16-sbf".into(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 28,
        profile: profile.name.to_string(),
        rate: "1/16".into(),
        query_count: RATE16_CANDIDATE_QUERY_COUNT,
        grinding_bits: RATE16_CANDIDATE_GRINDING_BITS,
        johnson_eta: ETA,
        bits_per_query,
        query_round_bits,
        proof_bytes: proof.len(),
        proof_sha256,
        proof_cache: proof_path.display().to_string(),
        proof_source,
        grinding_generation_seconds,
        upload_chunks,
        unique_layer_indices,
        full_simulation_cu,
        full_simulation_errors,
        direct_integrated_cu,
        shared_base_cu,
        layer0_inclusive_cu,
        later_inclusive_cu,
        segment_reconciled_cu,
        segment_delta_vs_direct_cu,
        selected_integrated_cu,
        headroom_vs_1_4m_cu: 1_400_000 - selected_integrated_cu as i64,
        headroom_vs_1_19m_cu: 1_190_000 - selected_integrated_cu as i64,
        composition_central_cu,
        composition_central_error,
        composition_central_increment_cu,
        composition_central_headroom_vs_1_4m_cu,
        composition_stress_cu,
        composition_stress_error,
        composition_stress_increment_cu,
        composition_stress_headroom_vs_1_4m_cu,
        full_host_verifier_accepted,
        stale_statement_rejected: stale.err.is_some(),
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        soundness_caveat: "Rate 1/16 q36/g32 gives 101.466 bits only for the pinned Johnson query round. The full T1/T2/transport/BCS ledger must be re-derived at rho=1/16; this artifact is not a 100-bit system claim.".into(),
        explicit_nonclaims: vec![
            "fixture C2 is not payment-derived".into(),
            "the same-instruction composition rows are synthetic pricing kernels, not proof-linked payment constraints".into(),
            "hiding, economic state transition, and receipt logic are excluded".into(),
            "the larger-domain profile is diagnostic and does not re-pin tag 26".into(),
        ],
    })
}

/// Literal hardened rate-1/16 proof: q36/g36 plus four work witnesses before
/// the fold challenges. The expensive nonces are cached only after the full
/// host verifier accepts the resulting bytes.
pub fn run_stage2_m31_rate16_hardened_sbf() -> Result<M31Rate16HardenedSbfSummary> {
    use aspis_core::circle_candidate_verify::verify_rate16_hardened_candidate_segment;
    use aspis_core::circle_openings::CircleQuerySegment;
    use aspis_core::circle_prefix::{
        CandidatePrefix, CANDIDATE_LOG_ROWS, CANDIDATE_PREFIX_LEN, CANDIDATE_PREFIX_OFFSETS,
        CANDIDATE_STATEMENT_POINT_COORDINATES, RATE16_CANDIDATE_QUERY_COUNT,
        RATE16_HARDENED_CANDIDATE_GRINDING_BITS, RATE16_HARDENED_CANDIDATE_SHAPE,
        RATE16_HARDENED_FOLD_POW_BITS,
    };
    use aspis_core::field::{CM31, M31, P, QM31};
    use aspis_prover::circle_candidate::{C1_COLUMNS, C2_COLUMNS, TRACE_LEN};
    use aspis_prover::circle_candidate_prefix::build_fresh_kappa_candidate_proof_for_shape;
    use sha2::{Digest as _, Sha256};

    const QUERY_COUNT: usize = RATE16_CANDIDATE_QUERY_COUNT as usize;
    const UNHARDENED_DIRECT_CU: u64 = 1_237_894;

    #[derive(Clone, Copy)]
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
            self.0
        }
        fn m31(&mut self) -> M31 {
            M31((self.next() as u32) % P)
        }
        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

    let profile = &aspis_core::params::PROFILE_JOHNSON_LR10_B4_Q36_G36_POW;
    ensure!(profile.id == RATE16_HARDENED_CANDIDATE_SHAPE.profile_id);
    ensure!(profile.log_rows == CANDIDATE_LOG_ROWS);
    ensure!(profile.log_blowup == RATE16_HARDENED_CANDIDATE_SHAPE.log_blowup);
    ensure!(profile.query_count == RATE16_CANDIDATE_QUERY_COUNT);
    ensure!(profile.grinding_bits == RATE16_HARDENED_CANDIDATE_GRINDING_BITS);

    // Keep the exact witness fixture shared with the q36/g32 measurement so
    // the delta isolates transcript hardening rather than different Merkle
    // collision patterns.
    let mut rng = Rng(0x5052_4546_4958_4341);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| rng.m31().add(M31((column * 65_537 + row * 257 + 1) as u32)))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut value = rng.qm31();
                    value.c0.a = value.c0.a.add(M31((helper * 4_099 + row + 1) as u32));
                    value
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let z: [QM31; CANDIDATE_STATEMENT_POINT_COORDINATES] = core::array::from_fn(|coordinate| {
        let mut value = rng.qm31();
        value.c1.b = value.c1.b.add(M31((coordinate * 313 + 17) as u32));
        value
    });
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/m31-circle/sequential-candidate/v1").into();

    let root = workspace_root()?;
    let proof_dir = root.join("results/stage2/proofs");
    fs::create_dir_all(&proof_dir)?;
    let proof_path = proof_dir.join("m31_circle_fresh_kappa_johnson_b4_q36_g36_foldpow.bin");
    let cached = fs::read(&proof_path).ok().filter(|proof| {
        verify_rate16_hardened_candidate_segment(
            proof,
            &statement_digest,
            &z,
            HOST_HASH,
            CircleQuerySegment::Full,
        )
        .is_ok()
    });
    let (proof, proof_source, grinding_generation_seconds) = if let Some(proof) = cached {
        (
            proof,
            "reused host-verified q36/g36 four-fold-PoW cache".to_string(),
            None,
        )
    } else {
        eprintln!(
            "stage2-m31-rate16-hardened-sbf: searching fold PoW 39/35/31/27 and final g36; this is intentionally prover-heavy"
        );
        let started = Instant::now();
        let built = build_fresh_kappa_candidate_proof_for_shape::<QUERY_COUNT>(
            &c1,
            &c2,
            z,
            statement_digest,
            HOST_HASH,
            RATE16_HARDENED_CANDIDATE_SHAPE,
        )
        .map_err(|error| anyhow!("build hardened rate-1/16 fixture: {error:?}"))?;
        let elapsed = started.elapsed().as_secs_f64();
        ensure!(
            verify_rate16_hardened_candidate_segment(
                &built.bytes,
                &statement_digest,
                &z,
                HOST_HASH,
                CircleQuerySegment::Full,
            )
            .is_ok(),
            "fresh hardened proof failed the host verifier"
        );
        fs::write(&proof_path, &built.bytes)?;
        (
            built.bytes,
            "generated and cached literal q36/g36 four-fold-PoW proof".to_string(),
            Some(elapsed),
        )
    };
    let full_host_verifier_accepted = verify_rate16_hardened_candidate_segment(
        &proof,
        &statement_digest,
        &z,
        HOST_HASH,
        CircleQuerySegment::Full,
    )
    .is_ok();
    ensure!(full_host_verifier_accepted);
    let (prefix, _) =
        CandidatePrefix::parse_from_proof_for_shape(&proof, RATE16_HARDENED_CANDIDATE_SHAPE)
            .map_err(|error| anyhow!("parse hardened proof: {error:?}"))?;
    let fold_nonces = prefix.fold_nonces;
    let query_nonce = prefix.nonce;

    let mut fold_nonce_corruptions_rejected = [false; 4];
    for round in 0..4 {
        let mut bad = proof.clone();
        bad[CANDIDATE_PREFIX_LEN + round * 8] ^= 1;
        fold_nonce_corruptions_rejected[round] = verify_rate16_hardened_candidate_segment(
            &bad,
            &statement_digest,
            &z,
            HOST_HASH,
            CircleQuerySegment::PreparedBase,
        )
        .is_err();
    }
    ensure!(fold_nonce_corruptions_rejected
        .into_iter()
        .all(|rejected| rejected));
    let mut bad_query_nonce = proof.clone();
    bad_query_nonce[CANDIDATE_PREFIX_OFFSETS.nonce_start] ^= 1;
    let query_nonce_corruption_rejected = verify_rate16_hardened_candidate_segment(
        &bad_query_nonce,
        &statement_digest,
        &z,
        HOST_HASH,
        CircleQuerySegment::PreparedBase,
    )
    .is_err();
    ensure!(query_nonce_corruption_rejected);

    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let claim_z = z
        .map(|value| {
            let mut bytes = [0u8; 16];
            value.write_le_bytes(&mut bytes);
            bytes
        })
        .to_vec();

    let simulate = |digest: [u8; 32]| -> Result<SimulationResult> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::MeasureM31CircleRate16Hardened {
                statement_digest: digest,
                claim_z: claim_z.clone(),
                phase: JohnsonM31CircleDiagnosticPhase::Full,
                start: 0,
                end: 0,
            })?,
        };
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            rpc.latest_blockhash()?,
        );
        rpc.simulate_verbose(&tx)
    };
    let mut simulation_cu = Vec::with_capacity(VERIFY_REPETITIONS);
    for _ in 0..VERIFY_REPETITIONS {
        let result = simulate(statement_digest)?;
        ensure!(
            result.err.is_none(),
            "hardened rate-1/16 SBF rejected: {:?}",
            result.err
        );
        simulation_cu.push(result.units.context("hardened simulation omitted CU")?);
    }
    ensure!(simulation_cu.iter().all(|cu| *cu == simulation_cu[0]));
    let selected_integrated_cu = simulation_cu[0];
    let mut stale_digest = statement_digest;
    stale_digest[0] ^= 1;
    let stale_statement_rejected = simulate(stale_digest)?.err.is_some();
    ensure!(stale_statement_rejected);

    Ok(M31Rate16HardenedSbfSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-m31-rate16-hardened-sbf"
            .into(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 30,
        profile: profile.name.to_string(),
        rate: "1/16".into(),
        query_count: RATE16_CANDIDATE_QUERY_COUNT,
        query_grinding_bits: RATE16_HARDENED_CANDIDATE_GRINDING_BITS,
        fold_pow_bits: RATE16_HARDENED_FOLD_POW_BITS,
        proof_bytes: proof.len(),
        proof_sha256,
        proof_cache: proof_path.display().to_string(),
        proof_source,
        grinding_generation_seconds,
        fold_nonces,
        query_nonce,
        upload_chunks,
        simulation_cu,
        selected_integrated_cu,
        incremental_cu_vs_unhardened: selected_integrated_cu as i64
            - UNHARDENED_DIRECT_CU as i64,
        headroom_vs_1_4m_cu: 1_400_000 - selected_integrated_cu as i64,
        full_host_verifier_accepted,
        fold_nonce_corruptions_rejected,
        query_nonce_corruption_rejected,
        stale_statement_rejected,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        explicit_nonclaims: vec![
            "this artifact hardens the PCS transcript only; C2 remains fixture data".into(),
            "payment-derived composition, hiding, and atomic state transition are not yet included".into(),
            "the numeric soundness ledger is emitted separately and remains conditional until its exact transport proof is reviewed".into(),
        ],
    })
}

/// Integrated v3/v4 comparison for an honest public evaluation claim and the
/// synthetic-C2 PCS scaffold. V3 carries one helper claim; v4 carries two
/// helper claims and samples two OOD points per round. This is not a payment
/// proof and must not be described as one.
pub fn run_stage2_v4_s2_pcs_scaffold() -> Result<V4S2PcsScaffoldSummary> {
    const SEEDS: u64 = 8;
    const REPETITIONS_PER_PROOF: usize = 1;
    const PRODUCTION_VERIFY_WIRE_ORDINAL: u8 = 6;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn layer0_unique_fibers(proof: &[u8]) -> Result<u16> {
        let header = aspis_core::proof::Header::parse(proof).context("parse proof header")?;
        let transcript_len = aspis_core::proof::transcript_records_len_for_version(
            header.num_rounds as usize,
            header.flags,
            header.version,
        )
        .context("unsupported proof version")?;
        let final_values = 1usize
            .checked_shl(header.final_poly_log_len)
            .context("final polynomial length overflow")?;
        let offset = aspis_core::proof::HEADER_LEN
            .checked_add(transcript_len)
            .and_then(|value| value.checked_add(final_values * 16))
            .and_then(|value| value.checked_add(8))
            .context("layer-0 opening offset overflow")?;
        let bytes = proof
            .get(offset..offset + 2)
            .context("layer-0 unique count missing")?;
        Ok(u16::from_le_bytes(bytes.try_into().unwrap()))
    }

    fn simulate_verify_with_claim(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        digest: [u8; 32],
        claim: &aspis_core::EvaluationClaim,
    ) -> Result<(Option<u64>, Option<String>)> {
        let claim_z = claim
            .z
            .iter()
            .map(|coordinate| {
                let mut encoded = [0u8; 16];
                coordinate.write_le_bytes(&mut encoded);
                encoded
            })
            .collect();
        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);
        let instruction = AspisInstruction::VerifyWithClaim {
            statement_digest: digest,
            claim_z,
            claim_v,
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                proof_instruction(&payer.pubkey(), proof_account, &instruction)?,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        rpc.simulate(&transaction)
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 20 * LAMPORTS_PER_SOL)?;

    let transcript_kat_v4_s2_pcs_scaffold_host =
        aspis_core::transcript::transcript_kat_v4_s2_pcs_scaffold(HOST_HASH);
    ensure!(
        transcript_kat_v4_s2_pcs_scaffold_host
            == aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        "host v4/s=2 PCS-scaffold transcript KAT drifted"
    );
    let transcript_kat_v3_unchanged = aspis_core::transcript::transcript_kat(HOST_HASH)
        == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED;
    ensure!(
        transcript_kat_v3_unchanged,
        "legacy v3 transcript KAT drifted"
    );
    let kat_instruction = Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::TranscriptKatV4S2PcsScaffold {
            expected: aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        })?,
    };
    let blockhash = rpc.latest_blockhash()?;
    let kat_transaction = Transaction::new_signed_with_payer(
        &[kat_instruction],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (transcript_kat_v4_s2_pcs_scaffold_units, transcript_kat_v4_s2_pcs_scaffold_error) =
        rpc.simulate(&kat_transaction)?;
    ensure!(
        transcript_kat_v4_s2_pcs_scaffold_error.is_none(),
        "v4/s=2 PCS-scaffold KAT failed on SBF: {transcript_kat_v4_s2_pcs_scaffold_error:?}"
    );
    let transcript_kat_v4_s2_pcs_scaffold_simulation_cu =
        transcript_kat_v4_s2_pcs_scaffold_units
            .context("v4/s=2 PCS-scaffold KAT simulation did not report units")?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let options = ProveOptions {
        fold_payload: FoldPayload::RawFibers,
        merkle_mode: MerkleMode::Radix4MinimalSubtree,
    };
    let mut measurements = Vec::with_capacity(SEEDS as usize);
    let mut corruption_source = None;

    for seed in 1..=SEEDS {
        let digest = crate::host_statement_digest(seed);
        let coeffs = seeded_coeffs(profile.log_rows, seed);
        let claim_z = (0..profile.log_rows)
            .map(|coordinate| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(1_000 + (seed as u32).wrapping_mul(37) + coordinate),
                ))
            })
            .collect::<Vec<_>>();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &claim_z),
            z: claim_z,
        };
        let v3_proof = prove_with_claim(profile, &coeffs, &digest, &claim, &options, HOST_HASH);
        let v4_proof = prove_with_claim_v4(profile, &coeffs, &digest, &claim, &options, HOST_HASH);

        ensure!(
            aspis_core::verify_with_claim(&v3_proof, &digest, Some(&claim), HOST_HASH).is_ok(),
            "seed {seed} v3 claim-carrying synthetic-C2 proof failed host verification"
        );
        ensure!(
            aspis_core::verify_with_claim(&v4_proof, &digest, Some(&claim), HOST_HASH).is_ok(),
            "seed {seed} v4/s=2 claim-carrying synthetic-C2 proof failed host verification"
        );
        let v3_header = aspis_core::proof::Header::parse(&v3_proof)
            .context("parse generated v3 proof header")?;
        let v4_header = aspis_core::proof::Header::parse(&v4_proof)
            .context("parse generated v4 proof header")?;
        ensure!(
            v3_header.ood_samples_per_round() == 1,
            "seed {seed} v3 proof did not encode s=1"
        );
        ensure!(
            v4_header.ood_samples_per_round() == 2,
            "seed {seed} v4 proof did not encode s=2"
        );
        ensure!(
            v3_header.second_phase_helper_count() == 1
                && v3_header.second_phase_leaf_len() == 64
                && v3_header.second_phase_claims_len() == 16,
            "seed {seed} v3 helper framing drifted"
        );
        ensure!(
            v4_header.second_phase_helper_count() == 2
                && v4_header.second_phase_leaf_len() == 128
                && v4_header.second_phase_claims_len() == 32,
            "seed {seed} v4 two-helper framing drifted"
        );

        let v3_account = Keypair::new();
        let v4_account = Keypair::new();
        upload_proof(&rpc, &payer, &v3_account, &v3_proof, true)?;
        upload_proof(&rpc, &payer, &v4_account, &v4_proof, true)?;
        let (v3_units, v3_error) =
            simulate_verify_with_claim(&rpc, &payer, &v3_account.pubkey(), digest, &claim)?;
        ensure!(
            v3_error.is_none(),
            "seed {seed} v3 production VerifyWithClaim failed: {v3_error:?}"
        );
        let (v4_units, v4_error) =
            simulate_verify_with_claim(&rpc, &payer, &v4_account.pubkey(), digest, &claim)?;
        ensure!(
            v4_error.is_none(),
            "seed {seed} v4 production VerifyWithClaim failed: {v4_error:?}"
        );
        let v3_verify_cu = v3_units.context("v3 production Verify did not report units")?;
        let v4_verify_cu = v4_units.context("v4 production Verify did not report units")?;
        let v3_hash = HOST_HASH(&[&v3_proof]);
        let v4_hash = HOST_HASH(&[&v4_proof]);
        measurements.push(V4S2PcsScaffoldSeedMeasurement {
            seed,
            v3_proof_bytes: v3_proof.len(),
            v4_proof_bytes: v4_proof.len(),
            proof_bytes_delta: v4_proof.len() as i64 - v3_proof.len() as i64,
            v3_proof_sha256: hex(&v3_hash),
            v4_proof_sha256: hex(&v4_hash),
            v3_layer0_unique_fibers: layer0_unique_fibers(&v3_proof)?,
            v4_layer0_unique_fibers: layer0_unique_fibers(&v4_proof)?,
            v3_verify_cu,
            v4_verify_cu,
            verify_cu_delta: v4_verify_cu as i64 - v3_verify_cu as i64,
        });
        if seed == 1 {
            corruption_source = Some((digest, claim, v4_proof));
        }
        eprintln!(
            "stage2-v4-s2-pcs-scaffold: seed {seed}/{SEEDS} v3={v3_verify_cu} v4={v4_verify_cu} delta={}",
            v4_verify_cu as i64 - v3_verify_cu as i64
        );
    }

    let (corruption_digest, corruption_claim, v4_proof) =
        corruption_source.context("seed-1 v4 proof missing")?;
    let header = aspis_core::proof::Header::parse(&v4_proof)
        .context("parse seed-1 v4 proof for corruption suite")?;
    ensure!(
        header.ood_samples_per_round() == 2,
        "corruption proof is not s=2"
    );
    let mut second_ood_corruptions = Vec::with_capacity(header.num_rounds as usize);
    for layer in 0..header.num_rounds {
        let offset = aspis_core::proof::ood_value_offset(&header, layer as usize, 1)
            .with_context(|| format!("locate layer-{layer} second OOD value"))?;
        let mut corrupted = v4_proof.clone();
        corrupted[offset] ^= 1;
        let host_error = aspis_core::verify_with_claim(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("second-OOD corruption unexpectedly passed host verification");
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
        let (_, sbf_error) = simulate_verify_with_claim(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            corruption_digest,
            &corruption_claim,
        )?;
        ensure!(
            sbf_error.is_some(),
            "layer {layer} second-OOD corruption unexpectedly passed VerifyWithClaim on SBF"
        );
        second_ood_corruptions.push(V4S2PcsScaffoldCorruptionCase {
            seed: 1,
            target: format!("layer_{layer}_second_ood_value"),
            layer: Some(layer),
            sample_index: Some(1),
            helper_claim_index: None,
            helper_leaf_half_index: None,
            proof_byte_offset: offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_rejected: true,
            sbf_error: sbf_error.unwrap(),
        });
    }

    let mut helper_claim_corruptions = Vec::with_capacity(header.second_phase_claim_count());
    for helper in 0..header.second_phase_claim_count() {
        let offset = aspis_core::proof::second_phase_claim_offset(&header, helper)
            .with_context(|| format!("locate helper claim {helper}"))?;
        let mut corrupted = v4_proof.clone();
        corrupted[offset] ^= 1;
        let host_error = aspis_core::verify_with_claim(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("helper-claim corruption unexpectedly passed host verification");
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
        let (_, sbf_error) = simulate_verify_with_claim(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            corruption_digest,
            &corruption_claim,
        )?;
        ensure!(
            sbf_error.is_some(),
            "helper claim {helper} corruption unexpectedly passed VerifyWithClaim on SBF"
        );
        helper_claim_corruptions.push(V4S2PcsScaffoldCorruptionCase {
            seed: 1,
            target: format!("second_phase_helper_claim_{helper}"),
            layer: None,
            sample_index: None,
            helper_claim_index: Some(helper as u8),
            helper_leaf_half_index: None,
            proof_byte_offset: offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_rejected: true,
            sbf_error: sbf_error.unwrap(),
        });
    }

    let mut helper_leaf_half_corruptions = Vec::with_capacity(header.second_phase_helper_count());
    for helper in 0..header.second_phase_helper_count() {
        let offset = aspis_core::proof::first_layer_second_phase_helper_offset(&v4_proof, helper)
            .with_context(|| format!("locate first C2 leaf helper half {helper}"))?;
        ensure!(
            offset + 64 <= v4_proof.len(),
            "helper half {helper} is out of proof bounds"
        );
        let mut corrupted = v4_proof.clone();
        let value = u32::from_le_bytes(corrupted[offset..offset + 4].try_into().unwrap());
        let changed = if value + 1 == aspis_core::field::P {
            0
        } else {
            value + 1
        };
        corrupted[offset..offset + 4].copy_from_slice(&changed.to_le_bytes());
        let host_error = aspis_core::verify_with_claim(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("C2 helper-half corruption unexpectedly passed host verification");
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
        let (_, sbf_error) = simulate_verify_with_claim(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            corruption_digest,
            &corruption_claim,
        )?;
        ensure!(
            sbf_error.is_some(),
            "C2 helper half {helper} corruption unexpectedly passed VerifyWithClaim on SBF"
        );
        helper_leaf_half_corruptions.push(V4S2PcsScaffoldCorruptionCase {
            seed: 1,
            target: format!("first_c2_leaf_helper_half_{helper}"),
            layer: Some(0),
            sample_index: None,
            helper_claim_index: None,
            helper_leaf_half_index: Some(helper as u8),
            proof_byte_offset: offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_rejected: true,
            sbf_error: sbf_error.unwrap(),
        });
    }

    let v3_verify_cu_mean = measurements.iter().map(|row| row.v3_verify_cu).sum::<u64>() as f64
        / measurements.len() as f64;
    let v4_verify_cu_mean = measurements.iter().map(|row| row.v4_verify_cu).sum::<u64>() as f64
        / measurements.len() as f64;
    let v3_layer0_unique_fibers_min = measurements
        .iter()
        .map(|row| row.v3_layer0_unique_fibers)
        .min()
        .context("empty v3 unique-fiber set")?;
    let v3_layer0_unique_fibers_max = measurements
        .iter()
        .map(|row| row.v3_layer0_unique_fibers)
        .max()
        .context("empty v3 unique-fiber set")?;
    let v4_layer0_unique_fibers_min = measurements
        .iter()
        .map(|row| row.v4_layer0_unique_fibers)
        .min()
        .context("empty v4 unique-fiber set")?;
    let v4_layer0_unique_fibers_max = measurements
        .iter()
        .map(|row| row.v4_layer0_unique_fibers)
        .max()
        .context("empty v4 unique-fiber set")?;
    let verify_deltas = measurements
        .iter()
        .map(|row| row.verify_cu_delta)
        .collect::<Vec<_>>();
    let paired_verify_cu_delta_mean =
        verify_deltas.iter().sum::<i64>() as f64 / verify_deltas.len() as f64;
    let paired_verify_cu_delta_min = *verify_deltas.iter().min().context("empty delta set")?;
    let paired_verify_cu_delta_max = *verify_deltas.iter().max().context("empty delta set")?;
    let proof_deltas = measurements
        .iter()
        .map(|row| row.proof_bytes_delta)
        .collect::<Vec<_>>();
    let proof_bytes_delta_min = *proof_deltas.iter().min().context("empty byte-delta set")?;
    let proof_bytes_delta_max = *proof_deltas.iter().max().context("empty byte-delta set")?;
    let every_second_ood_rejected_host =
        second_ood_corruptions.iter().all(|case| case.host_rejected);
    let every_second_ood_rejected_sbf = second_ood_corruptions.iter().all(|case| case.sbf_rejected);
    let every_helper_claim_rejected_host = helper_claim_corruptions
        .iter()
        .all(|case| case.host_rejected);
    let every_helper_claim_rejected_sbf = helper_claim_corruptions
        .iter()
        .all(|case| case.sbf_rejected);
    let every_helper_leaf_half_rejected_host = helper_leaf_half_corruptions
        .iter()
        .all(|case| case.host_rejected);
    let every_helper_leaf_half_rejected_sbf = helper_leaf_half_corruptions
        .iter()
        .all(|case| case.sbf_rejected);

    Ok(V4S2PcsScaffoldSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-v4-s2-pcs-scaffold".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        statement_kind: "honest public evaluation claim with synthetic-C2 PCS scaffold",
        is_payment_proof: false,
        production_verify_instruction_wire_ordinal: PRODUCTION_VERIFY_WIRE_ORDINAL,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + VerifyWithClaim",
        merkle_mode: "radix4_minimal_subtree",
        seeds: SEEDS,
        repetitions_per_proof: REPETITIONS_PER_PROOF,
        v3_samples_per_round: 1,
        v4_samples_per_round: 2,
        v3_second_phase_helper_columns: 1,
        v4_second_phase_helper_columns: 2,
        v3_second_phase_leaf_bytes: 64,
        v4_second_phase_leaf_bytes: 128,
        v3_second_phase_claims: 1,
        v4_second_phase_claims: 2,
        transcript_kat_v4_s2_pcs_scaffold_wire_ordinal: 19,
        transcript_kat_v4_s2_pcs_scaffold_expected_hex: hex(
            &aspis_core::transcript::TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
        ),
        transcript_kat_v4_s2_pcs_scaffold_host_matched: true,
        transcript_kat_v4_s2_pcs_scaffold_sbf_matched: true,
        transcript_kat_v4_s2_pcs_scaffold_simulation_cu,
        transcript_kat_v3_unchanged,
        measurements,
        v3_layer0_unique_fibers_min,
        v3_layer0_unique_fibers_max,
        v4_layer0_unique_fibers_min,
        v4_layer0_unique_fibers_max,
        v3_verify_cu_mean,
        v4_verify_cu_mean,
        paired_verify_cu_delta_mean,
        paired_verify_cu_delta_min,
        paired_verify_cu_delta_max,
        paired_verify_cu_delta_range: (paired_verify_cu_delta_max
            - paired_verify_cu_delta_min) as u64,
        proof_bytes_delta_min,
        proof_bytes_delta_max,
        second_ood_corruptions,
        helper_claim_corruptions,
        helper_leaf_half_corruptions,
        every_second_ood_rejected_host,
        every_second_ood_rejected_sbf,
        every_helper_claim_rejected_host,
        every_helper_claim_rejected_sbf,
        every_helper_leaf_half_rejected_host,
        every_helper_leaf_half_rejected_sbf,
        normative_payment_v4_framing_complete: false,
        missing_payment_v4_components: vec![
            "authenticated wide C1: 49 CM31 columns and 1,568-byte layer-0 fibers".to_string(),
            "the exact k'=51 query recombination: 49 QM31-by-CM31 terms plus two QM31 helper terms at gamma^49 and gamma^50".to_string(),
            "the 102 pre-gamma statement values: 49 C1 plus 2 C2 evaluations at each of z and low-bit-XOR-11(z), with their transcript framing".to_string(),
            "ConstraintId-bound statement framing, LogUp payment relation, constraint composition, and economic-attack corpus".to_string(),
            "masking/hiding and the final q36/g32 measurement".to_string(),
        ],
        notes: vec![
            "Every row is a real v3/s=1/one-helper-claim versus v4/s=2/two-helper-claim pair over identical profile, coefficients, honest public main claim, statement digest, synthetic C2 rule, and radix-4 mode. The changed transcript deliberately produces fresh roots, nonce, queries, and frontiers.".to_string(),
            "The measured transaction invokes production AspisInstruction::VerifyWithClaim (Borsh tag 6); no measurement-only proof verifier or new proof-verification wire tag is involved.".to_string(),
            "This proves and measures only the repository's public evaluation claim with synthetic-C2 PCS scaffold. It is not LogUp, does not prove a payment, and is not hiding.".to_string(),
            "One simulation per proof is enough within a seed because Solana simulation CU is deterministic for fixed account data; the eight independently generated transcripts are the variance population.".to_string(),
            "The seed-1 corruption suite changes every second OOD value, both v4 helper claims, and each committed 64-byte half of the first authenticated C2 leaf, requiring rejection by host and production VerifyWithClaim on SBF.".to_string(),
            "Every paired and corruption simulation uses the standard 1,400,000-CU limit plus 262,144-byte heap-frame request; absolute v3/v4 CU is comparable to the production measurement envelope.".to_string(),
            "The paired CU delta prices s=2 plus the second 128-byte-leaf helper within the scalar-C1 PCS scaffold. It does not price the normative 49-column authenticated C1 representation or its k'=51 recombination.".to_string(),
            "The tag-21 exact-wide diagnostic is a separate replacement seam, not an additive line item: its 36-fiber prepared-byte CU must not be added wholesale to this scalar-C1 verifier total.".to_string(),
            "This g16 result is a PCS-scaffold delta checkpoint, not the final q36/g32 strict-gate measurement or the final payment-v4 KAT.".to_string(),
        ],
    })
}

/// Reconciled exact-wide v4 PCS-scaffold measurement. The diagnostic-only
/// tag invokes the real proof parser, Merkle authentication, folds and final
/// checks, but replaces scalar layer-zero C1/C2 processing in place. No
/// isolated artifact totals are added together.
pub fn run_stage2_reconciled_exact_wide_v4_scaffold() -> Result<ReconciledExactWideSummary> {
    const SEEDS: u64 = 8;
    const DIAGNOSTIC_WIRE_ORDINAL: u8 = 22;
    const PRODUCTION_WIRE_ORDINAL: u8 = 6;
    const STRICT_PROJECT_THRESHOLD_CU: u64 = 1_190_000;
    const ABSOLUTE_EXECUTION_CAP_CU: u64 = VERIFY_CU_LIMIT as u64;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn layer0_unique_fibers(proof: &[u8]) -> Result<u16> {
        let c1_start = aspis_core::proof::first_layer_first_phase_opening_offset(proof)
            .context("locate exact-wide layer-zero C1 section")?;
        let count_start = c1_start
            .checked_sub(2)
            .context("layer-zero unique-count underflow")?;
        Ok(u16::from_le_bytes(
            proof[count_start..c1_start].try_into().unwrap(),
        ))
    }

    fn encoded_claim(claim: &aspis_core::EvaluationClaim) -> (Vec<[u8; 16]>, [u8; 16]) {
        let claim_z = claim
            .z
            .iter()
            .map(|coordinate| {
                let mut bytes = [0u8; 16];
                coordinate.write_le_bytes(&mut bytes);
                bytes
            })
            .collect();
        let mut claim_v = [0u8; 16];
        claim.v.write_le_bytes(&mut claim_v);
        (claim_z, claim_v)
    }

    fn simulate_claim(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        statement_digest: [u8; 32],
        claim: &aspis_core::EvaluationClaim,
        diagnostic: bool,
    ) -> Result<(u64, Option<String>)> {
        let (claim_z, claim_v) = encoded_claim(claim);
        let instruction = if diagnostic {
            AspisInstruction::VerifyExactWideV4Scaffold {
                statement_digest,
                claim_z,
                claim_v,
            }
        } else {
            AspisInstruction::VerifyWithClaim {
                statement_digest,
                claim_z,
                claim_v,
            }
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                proof_instruction(&payer.pubkey(), proof_account, &instruction)?,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        let (units, error) = rpc.simulate(&transaction)?;
        Ok((
            units.context("simulation did not report compute units")?,
            error,
        ))
    }

    fn compute_budget_exhausted(error: &str) -> bool {
        error.contains("ProgramFailedToComplete") && error.contains("exceeded CUs meter")
    }

    fn accepted_threshold_outcome(units: u64, threshold: u64) -> String {
        if units <= threshold {
            format!(
                "accepted at {units} CU; {} CU below the {threshold}-CU threshold",
                threshold - units
            )
        } else {
            format!(
                "accepted at {units} CU; {} CU above the {threshold}-CU threshold",
                units - threshold
            )
        }
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 40 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let options = ProveOptions {
        fold_payload: FoldPayload::RawFibers,
        merkle_mode: MerkleMode::Radix4MinimalSubtree,
    };
    let mut measurements = Vec::with_capacity(SEEDS as usize);
    let mut seed1 = None;
    let mut production_tag6_seed1_sbf = None;

    for seed in 1..=SEEDS {
        let statement_digest = crate::host_statement_digest(seed.wrapping_add(22_000));
        let coeffs = seeded_coeffs(profile.log_rows, seed.wrapping_add(22_000));
        let claim_z = (0..profile.log_rows)
            .map(|coordinate| {
                aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(
                    aspis_core::field::M31(22_000 + (seed as u32).wrapping_mul(53) + coordinate),
                ))
            })
            .collect::<Vec<_>>();
        let claim = aspis_core::EvaluationClaim {
            v: multilinear_eval(&coeffs, &claim_z),
            z: claim_z,
        };
        let proof = prove_exact_wide_v4_scaffold_for_measurement(
            profile,
            &coeffs,
            &statement_digest,
            &claim,
            &options,
            HOST_HASH,
        );
        let header = aspis_core::proof::Header::parse(&proof)
            .with_context(|| format!("seed {seed} exact-wide header"))?;
        ensure!(
            header.has_exact_wide_c1()
                && header.version == aspis_core::proof::VERSION_V4_S2
                && header.second_phase_helper_count() == 2,
            "seed {seed} did not produce the exact-wide v4/two-helper shape"
        );
        ensure!(
            aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
                &proof,
                &statement_digest,
                Some(&claim),
                HOST_HASH,
            )
            .is_ok(),
            "seed {seed} failed diagnostic host verification"
        );
        let production_host_error =
            aspis_core::verify_with_claim(&proof, &statement_digest, Some(&claim), HOST_HASH)
                .expect_err("production host verifier accepted exact-wide scaffold flag");
        ensure!(
            production_host_error == aspis_core::VerifyError::BadHeader,
            "seed {seed} production host rejection drifted: {production_host_error:?}"
        );

        let unique = layer0_unique_fibers(&proof)?;
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
        let (observed_cu_or_cap, simulation_error) = simulate_claim(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            statement_digest,
            &claim,
            true,
        )?;
        let accepted = simulation_error.is_none();
        let exhausted = simulation_error
            .as_deref()
            .map(compute_budget_exhausted)
            .unwrap_or(false);
        ensure!(
            accepted || exhausted,
            "seed {seed} failed for a non-budget reason: {simulation_error:?}"
        );
        if exhausted {
            ensure!(
                observed_cu_or_cap == ABSOLUTE_EXECUTION_CAP_CU,
                "seed {seed} budget failure reported {observed_cu_or_cap}, expected cap {ABSOLUTE_EXECUTION_CAP_CU}"
            );
        }
        let required_lower_bound = exhausted.then_some(ABSOLUTE_EXECUTION_CAP_CU + 1);
        let outcome_vs_1_190_000 = if accepted {
            accepted_threshold_outcome(observed_cu_or_cap, STRICT_PROJECT_THRESHOLD_CU)
        } else {
            format!(
                "compute meter exhausted at {ABSOLUTE_EXECUTION_CAP_CU} CU; requires at least {} CU, at least {} CU above the {STRICT_PROJECT_THRESHOLD_CU}-CU threshold",
                ABSOLUTE_EXECUTION_CAP_CU + 1,
                ABSOLUTE_EXECUTION_CAP_CU + 1 - STRICT_PROJECT_THRESHOLD_CU
            )
        };
        let outcome_vs_1_400_000 = if accepted {
            accepted_threshold_outcome(observed_cu_or_cap, ABSOLUTE_EXECUTION_CAP_CU)
        } else {
            format!(
                "compute meter exhausted at {ABSOLUTE_EXECUTION_CAP_CU} CU; requires more than the execution cap (lower bound {} CU)",
                ABSOLUTE_EXECUTION_CAP_CU + 1
            )
        };

        measurements.push(ReconciledExactWideSeedMeasurement {
            seed,
            proof_bytes: proof.len(),
            proof_sha256: hex(&HOST_HASH(&[&proof])),
            layer0_unique_fibers: unique,
            authenticated_c1_opening_bytes: usize::from(unique)
                * aspis_core::proof::EXACT_WIDE_C1_FIBER_LEN,
            authenticated_c2_opening_bytes: usize::from(unique)
                * aspis_core::proof::SECOND_PHASE_LEAF_LEN_V4_S2,
            diagnostic_host_accepted: true,
            production_host_rejected_bad_header: true,
            observed_cu_or_cap,
            simulation_error: simulation_error.clone(),
            accepted_at_1_400_000_limit: accepted,
            compute_budget_exhausted: exhausted,
            exact_cu_if_accepted: accepted.then_some(observed_cu_or_cap),
            required_cu_lower_bound_if_exhausted: required_lower_bound,
            signed_headroom_vs_1_190_000_if_accepted: accepted
                .then_some(STRICT_PROJECT_THRESHOLD_CU as i64 - observed_cu_or_cap as i64),
            signed_headroom_vs_1_400_000_if_accepted: accepted
                .then_some(ABSOLUTE_EXECUTION_CAP_CU as i64 - observed_cu_or_cap as i64),
            minimum_breach_vs_1_190_000_if_exhausted: required_lower_bound
                .map(|lower| lower - STRICT_PROJECT_THRESHOLD_CU),
            minimum_breach_vs_1_400_000_if_exhausted: required_lower_bound
                .map(|lower| lower - ABSOLUTE_EXECUTION_CAP_CU),
            outcome_vs_1_190_000,
            outcome_vs_1_400_000,
        });

        if seed == 1 {
            let (units, error) = simulate_claim(
                &rpc,
                &payer,
                &proof_account.pubkey(),
                statement_digest,
                &claim,
                false,
            )?;
            let error = error.context("production tag 6 unexpectedly accepted wide flag on SBF")?;
            ensure!(
                !compute_budget_exhausted(&error),
                "production tag 6 reached the wide work instead of rejecting the flag"
            );
            production_tag6_seed1_sbf = Some((units, error));
            seed1 = Some((statement_digest, claim, proof));
        }

        eprintln!(
            "stage2-v4-exact-wide-reconciled: seed {seed}/{SEEDS} unique={unique} cu_or_cap={observed_cu_or_cap} accepted={accepted} exhausted={exhausted}"
        );
    }

    let (corruption_digest, corruption_claim, proof) =
        seed1.context("seed-1 exact-wide corruption source missing")?;
    let c1_start = aspis_core::proof::first_layer_first_phase_opening_offset(&proof)
        .context("locate seed-1 C1 opening")?;
    let c2_start = aspis_core::proof::first_layer_second_phase_opening_offset(&proof)
        .context("locate seed-1 C2 opening")?;
    let mut corrupted_proofs = Vec::with_capacity(4);

    let mut canonical_c1 = proof.clone();
    let limb = u32::from_le_bytes(canonical_c1[c1_start..c1_start + 4].try_into().unwrap());
    let changed = if limb + 1 == aspis_core::field::P {
        0
    } else {
        limb + 1
    };
    canonical_c1[c1_start..c1_start + 4].copy_from_slice(&changed.to_le_bytes());
    corrupted_proofs.push((
        "first_c1_leaf",
        "canonical_committed_mutation",
        c1_start,
        canonical_c1,
    ));

    let mut canonical_c2 = proof.clone();
    let limb = u32::from_le_bytes(canonical_c2[c2_start..c2_start + 4].try_into().unwrap());
    let changed = if limb + 1 == aspis_core::field::P {
        0
    } else {
        limb + 1
    };
    canonical_c2[c2_start..c2_start + 4].copy_from_slice(&changed.to_le_bytes());
    corrupted_proofs.push((
        "first_c2_leaf",
        "canonical_committed_mutation",
        c2_start,
        canonical_c2,
    ));

    let mut noncanonical_c1 = proof.clone();
    noncanonical_c1[c1_start..c1_start + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
    corrupted_proofs.push((
        "first_c1_limb",
        "noncanonical_field_limb",
        c1_start,
        noncanonical_c1,
    ));

    let mut noncanonical_c2 = proof.clone();
    noncanonical_c2[c2_start..c2_start + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
    corrupted_proofs.push((
        "first_c2_limb",
        "noncanonical_field_limb",
        c2_start,
        noncanonical_c2,
    ));

    let mut corruption_cases = Vec::with_capacity(corrupted_proofs.len());
    for (target, kind, proof_byte_offset, corrupted) in corrupted_proofs {
        let host_error = aspis_core::verify::verify_exact_wide_v4_scaffold_for_measurement(
            &corrupted,
            &corruption_digest,
            Some(&corruption_claim),
            HOST_HASH,
        )
        .expect_err("exact-wide corruption unexpectedly passed host verification");
        if kind == "noncanonical_field_limb" {
            ensure!(
                host_error == aspis_core::VerifyError::NonCanonicalValue,
                "{target} host rejection was not NonCanonicalValue: {host_error:?}"
            );
        }
        let account = Keypair::new();
        upload_proof(&rpc, &payer, &account, &corrupted, true)?;
        let (_, sbf_error) = simulate_claim(
            &rpc,
            &payer,
            &account.pubkey(),
            corruption_digest,
            &corruption_claim,
            true,
        )?;
        let sbf_error = sbf_error.context("corruption unexpectedly passed on SBF")?;
        let sbf_compute_budget_exhausted = compute_budget_exhausted(&sbf_error);
        let sbf_rejection_conclusive = !sbf_compute_budget_exhausted;
        if kind == "noncanonical_field_limb" {
            ensure!(
                sbf_rejection_conclusive,
                "{target} hit the compute cap before its noncanonical check"
            );
        }
        corruption_cases.push(ReconciledExactWideCorruptionCase {
            target,
            kind,
            proof_byte_offset,
            host_rejected: true,
            host_error: format!("{host_error:?}"),
            sbf_error,
            sbf_compute_budget_exhausted,
            sbf_rejection_conclusive,
        });
    }

    let accepted_seed_count = measurements
        .iter()
        .filter(|row| row.accepted_at_1_400_000_limit)
        .count();
    let compute_budget_exhausted_seed_count = measurements
        .iter()
        .filter(|row| row.compute_budget_exhausted)
        .count();
    let accepted_units = measurements
        .iter()
        .filter_map(|row| row.exact_cu_if_accepted)
        .collect::<Vec<_>>();
    let exact_accepted_cu_mean = (!accepted_units.is_empty())
        .then(|| accepted_units.iter().sum::<u64>() as f64 / accepted_units.len() as f64);
    let threshold_1_190_000_observation = if compute_budget_exhausted_seed_count > 0 {
        format!(
            "{compute_budget_exhausted_seed_count}/{SEEDS} seeds exhausted the 1,400,000-CU meter; each therefore requires at least 1,400,001 CU, at least 210,001 CU above 1,190,000"
        )
    } else {
        format!(
            "all {SEEDS} seeds returned exact CU under the execution cap; see per-seed signed headroom versus 1,190,000"
        )
    };
    let threshold_1_400_000_observation = if compute_budget_exhausted_seed_count > 0 {
        format!(
            "{compute_budget_exhausted_seed_count}/{SEEDS} seeds exhausted the 1,400,000-CU meter and have a per-seed required-CU lower bound of 1,400,001"
        )
    } else {
        format!("all {SEEDS} seeds accepted at the 1,400,000-CU limit")
    };
    let (production_tag6_seed1_sbf_cu, production_tag6_seed1_sbf_error) =
        production_tag6_seed1_sbf.context("seed-1 production tag-6 check missing")?;

    Ok(ReconciledExactWideSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-v4-exact-wide-reconciled",
        validator_version: validator_version(),
        profile: profile.name,
        statement_kind: "diagnostic exact-wide PCS scaffold: honest column 0, authenticated zero columns 1..48, two synthetic nonzero C2 helpers",
        is_payment_proof: false,
        diagnostic_verify_instruction_wire_ordinal: DIAGNOSTIC_WIRE_ORDINAL,
        production_verify_with_claim_wire_ordinal: PRODUCTION_WIRE_ORDINAL,
        production_verify_with_claim_accepts_wide_flag: false,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        strict_project_threshold_cu: STRICT_PROJECT_THRESHOLD_CU,
        absolute_execution_cap_cu: ABSOLUTE_EXECUTION_CAP_CU,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + diagnostic tag 22 exact-wide scaffold verifier",
        merkle_mode: "radix4_minimal_subtree",
        seeds: SEEDS,
        c1_columns: aspis_core::proof::EXACT_WIDE_C1_COLUMNS,
        c1_leaf_bytes: aspis_core::proof::EXACT_WIDE_C1_FIBER_LEN,
        c2_columns: 2,
        c2_leaf_bytes: aspis_core::proof::SECOND_PHASE_LEAF_LEN_V4_S2,
        auxiliary_c1_columns: "columns 1..48 are committed zero columns; every canonical byte is authenticated, parsed and processed by the 49-lane kernel",
        observed_cu_or_cap_min: measurements
            .iter()
            .map(|row| row.observed_cu_or_cap)
            .min()
            .context("empty exact-wide measurements")?,
        observed_cu_or_cap_max: measurements
            .iter()
            .map(|row| row.observed_cu_or_cap)
            .max()
            .context("empty exact-wide measurements")?,
        measurements,
        accepted_seed_count,
        compute_budget_exhausted_seed_count,
        all_seed_outcomes_classified: accepted_seed_count + compute_budget_exhausted_seed_count
            == SEEDS as usize,
        exact_accepted_cu_mean,
        threshold_1_190_000_observation,
        threshold_1_400_000_observation,
        production_tag6_seed1_sbf_rejected: true,
        production_tag6_seed1_sbf_cu,
        production_tag6_seed1_sbf_error,
        canonical_mutations_rejected_host: corruption_cases
            .iter()
            .filter(|case| case.kind == "canonical_committed_mutation")
            .all(|case| case.host_rejected),
        noncanonical_limbs_rejected_host_and_sbf_conclusively: corruption_cases
            .iter()
            .filter(|case| case.kind == "noncanonical_field_limb")
            .all(|case| case.host_rejected && case.sbf_rejection_conclusive),
        corruption_cases,
        owner_ruling_made: false,
        overlap_replacement: vec![
            "retained: v4/s2 transcript, relation sumchecks, query derivation, C2 authentication, deeper-layer Merkle/folds, final polynomial, and grinding".to_string(),
            "removed in the flagged branch: scalar 32-byte C1 parse/hash plus C1 + gamma*C2[0] + gamma^2*C2[1] materialization".to_string(),
            "inserted at the same layer-zero seam: 1,568-byte C1 authentication and once-prepared canonical-byte 49-CM31 + 2-QM31 combination at gamma powers 0..50".to_string(),
            "no CU total from v4_s2_pcs_scaffold_g16.json or exact_wide_v4_diagnostic.json is arithmetically added to this measurement".to_string(),
        ],
        excluded_work: vec![
            "the second statement point and all 102 pre-gamma C1/C2 evaluation values".to_string(),
            "randomized ConstraintId registry, payment constraint composition, and LogUp payment semantics".to_string(),
            "masking/hiding, pool/nullifier/output transition, and proof-account sealing".to_string(),
            "final q36/g32 grinding profile; this uses the registered q36/g16 variance population".to_string(),
            "the pending M31-column alternative; this artifact measures only the reviewed 49-CM31 basis".to_string(),
        ],
        notes: vec![
            "This is a reconciled in-place PCS-scaffold measurement, not a full payment integration and not a product/architecture ruling.".to_string(),
            "Production VerifyWithClaim tag 6 rejects FLAG_EXACT_WIDE_C1 with BadHeader. Append-only diagnostic tag 22 is the only SBF dispatch that enables the scaffold until final 102-value semantics land.".to_string(),
            "Proof generation and proof-account upload occur outside the measured transaction. Every measured simulation uses the same 1,400,000-CU limit and 262,144-byte heap request.".to_string(),
            "A compute-budget failure reports the exact 1,400,000-CU meter observation and a required-CU lower bound of 1,400,001; it does not invent an exact total above the cap.".to_string(),
            "Canonical committed-leaf mutations are conclusive on host; when SBF reaches the cap before Merkle rejection, the case is labeled non-conclusive rather than credited. Noncanonical C1/C2 limbs must reject conclusively on both host and SBF.".to_string(),
        ],
    })
}

/// Decision-packet-only arithmetic and first-fold controls for the alternative
/// M31-valued circle-polynomial basis. This does not reinterpret an Aspis
/// proof or select a protocol architecture.
pub fn run_stage2_m31_circle_basis_probe() -> Result<M31CircleBasisSummary> {
    use aspis_core::field::{
        m31_batch_inverse, qm31_circle_to_line_fold4, qm31_m31_dot, qm31_m31_dot4,
        qm31_m31_dot4_prepared_bytes, qm31_m31_dot4_prepared_limbs49_bytes,
        qm31_m31_dot4_prepared_limbs49_bytes_two_rows, qm31_power_table, CM31, M31, P, QM31,
    };
    use aspis_core::verify::{domain_point, layer_geometry};

    const REPETITIONS: usize = 5;
    const STRICT_TARGET: i64 = 1_190_000;
    const ABSOLUTE_CAP: i64 = 1_400_000;
    const GAMMA_BYTES: usize = 16;
    const RLC_FIBER_BYTES: usize = M31_CIRCLE_BASIS_C1_LEAF_BYTES + M31_CIRCLE_BASIS_C2_LEAF_BYTES;
    const FOLD_RECORD_BYTES: usize = 2 + 4 * 4 + 4 * 16;
    const SEED: u64 = 0x4d33_3143_4952_434c;

    fn next_m31(state: &mut u64) -> M31 {
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: aspis_core::field::CM31::new(next_m31(state), next_m31(state)),
            c1: aspis_core::field::CM31::new(next_m31(state), next_m31(state)),
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn build_rlc_fixture(mut state: u64) -> Vec<u8> {
        let gamma = next_qm31(&mut state);
        let mut fixture = vec![0u8; M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES];
        gamma.write_le_bytes(&mut fixture[..GAMMA_BYTES]);
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let start = GAMMA_BYTES + fiber * RLC_FIBER_BYTES;
            for value in fixture[start..start + M31_CIRCLE_BASIS_C1_LEAF_BYTES].chunks_exact_mut(4)
            {
                value.copy_from_slice(&next_m31(&mut state).to_le_bytes());
            }
            let c2_start = start + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
            for value in
                fixture[c2_start..c2_start + M31_CIRCLE_BASIS_C2_LEAF_BYTES].chunks_exact_mut(16)
            {
                next_qm31(&mut state).write_le_bytes(value);
            }
        }
        fixture
    }

    fn host_rlc_sink(fixture: &[u8], mode: M31CircleBasisDiagnosticMode) -> Result<[u8; 32]> {
        ensure!(
            fixture.len() == M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES,
            "bad M31 RLC fixture length"
        );
        let gamma = QM31::from_le_bytes(&fixture[..GAMMA_BYTES]).context("M31 gamma")?;
        let powers = qm31_power_table::<51>(gamma);
        let weights: &[QM31; M31_CIRCLE_BASIS_C1_COLUMNS] =
            powers[..M31_CIRCLE_BASIS_C1_COLUMNS].try_into().unwrap();
        let prepared_limbs =
            weights.map(|weight| [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]);
        let mut decoded = vec![M31::ZERO; 4 * M31_CIRCLE_BASIS_C1_COLUMNS];
        let mut streaming = [M31::ZERO; M31_CIRCLE_BASIS_C1_COLUMNS];
        let mut accumulator = [QM31::ZERO; 4];
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let start = GAMMA_BYTES + fiber * RLC_FIBER_BYTES;
            let c2_start = start + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
            let c1 = &fixture[start..c2_start];
            for (index, bytes) in c1.chunks_exact(4).enumerate() {
                decoded[index] =
                    M31::from_le_bytes(bytes.try_into().unwrap()).context("noncanonical M31 C1")?;
            }
            let typed = [
                &decoded[0..49],
                &decoded[49..98],
                &decoded[98..147],
                &decoded[147..196],
            ];
            let reference = core::array::from_fn(|slot| qm31_m31_dot(weights, typed[slot]));
            let four_slot = qm31_m31_dot4(weights, typed);
            ensure!(reference == four_slot, "typed M31 dot4 differential failed");
            let mut combined = match mode {
                M31CircleBasisDiagnosticMode::RlcStructuredFourDots => reference,
                M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes => {
                    qm31_m31_dot4_prepared_bytes(weights, c1).context("canonical-byte M31 dot4")?
                }
                M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4 => four_slot,
                M31CircleBasisDiagnosticMode::RlcStreamingFourDots => {
                    let mut result = [QM31::ZERO; 4];
                    let slot_bytes = M31_CIRCLE_BASIS_C1_COLUMNS * 4;
                    for (slot, result_slot) in result.iter_mut().enumerate() {
                        for (index, bytes) in c1[slot * slot_bytes..(slot + 1) * slot_bytes]
                            .chunks_exact(4)
                            .enumerate()
                        {
                            streaming[index] = M31::from_le_bytes(bytes.try_into().unwrap())
                                .context("noncanonical streaming M31 C1")?;
                        }
                        *result_slot = qm31_m31_dot(weights, &streaming);
                    }
                    result
                }
                M31CircleBasisDiagnosticMode::RlcPreparedLimbs49 => {
                    qm31_m31_dot4_prepared_limbs49_bytes(&prepared_limbs, c1)
                        .context("prepared-limb exact-49 M31 dot4")?
                }
                M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows => {
                    qm31_m31_dot4_prepared_limbs49_bytes_two_rows(&prepared_limbs, c1)
                        .context("prepared-limb two-row exact-49 M31 dot4")?
                }
                _ => bail!("non-RLC mode passed to host M31 RLC sink"),
            };
            ensure!(combined == reference, "M31 RLC mode differential failed");
            let c2 = &fixture[c2_start..c2_start + M31_CIRCLE_BASIS_C2_LEAF_BYTES];
            for helper in 0..2 {
                for (slot, combined_slot) in combined.iter_mut().enumerate() {
                    let offset = (helper * 4 + slot) * 16;
                    let helper_value = QM31::from_le_bytes(&c2[offset..offset + 16])
                        .context("noncanonical QM31 C2")?;
                    *combined_slot = combined_slot.add(powers[49 + helper].mul(helper_value));
                }
            }
            for slot in 0..4 {
                accumulator[slot] = accumulator[slot].add(combined[slot]);
            }
        }
        let mut encoded = [0u8; 64];
        for (slot, value) in accumulator.iter().enumerate() {
            value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
        }
        Ok(HOST_HASH(&[
            b"aspis-m31-circle-basis-rlc-shape-v1",
            &encoded,
        ]))
    }

    fn build_fold_fixture(mut state: u64) -> Result<(Vec<u8>, [u8; 32])> {
        let alpha = next_qm31(&mut state);
        let geometry = layer_geometry(&PROFILE_CAPACITY_LR10_Q36_G16, 0);
        let mut fixture = vec![0u8; M31_CIRCLE_FOLD_FIXTURE_BYTES];
        alpha.write_le_bytes(&mut fixture[..16]);
        let mut reference = QM31::ZERO;
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let index = fiber as u16;
            let point = domain_point(&geometry, u32::from(index));
            ensure!(point.a != M31::ZERO && point.b != M31::ZERO);
            let coefficients = core::array::from_fn::<_, 4, _>(|_| next_qm31(&mut state));
            let evaluate = |x: M31, y: M31| {
                coefficients[0]
                    .add(coefficients[1].mul_m31(y))
                    .add(coefficients[2].mul_m31(x))
                    .add(coefficients[3].mul_m31(x.mul(y)))
            };
            let minus_x = M31::ZERO.sub(point.a);
            let minus_y = M31::ZERO.sub(point.b);
            let values = [
                evaluate(point.a, point.b),
                evaluate(point.a, minus_y),
                evaluate(minus_x, minus_y),
                evaluate(minus_x, point.b),
            ];
            let expected = coefficients[0]
                .add(alpha.mul(coefficients[1]))
                .add(alpha.square().mul(coefficients[2]))
                .add(alpha.square().mul(alpha).mul(coefficients[3]));
            ensure!(
                qm31_circle_to_line_fold4(
                    values,
                    alpha,
                    point.a.double().inv(),
                    point.b.double().inv(),
                ) == expected,
                "circle-fold cubic differential failed"
            );
            reference = reference.add(expected);
            let start = 16 + fiber * FOLD_RECORD_BYTES;
            fixture[start..start + 2].copy_from_slice(&index.to_le_bytes());
            fixture[start + 2..start + 6].copy_from_slice(&point.a.to_le_bytes());
            fixture[start + 6..start + 10].copy_from_slice(&point.b.to_le_bytes());
            fixture[start + 10..start + 14].copy_from_slice(&point.a.inv().to_le_bytes());
            fixture[start + 14..start + 18].copy_from_slice(&point.b.inv().to_le_bytes());
            for (slot, value) in values.iter().enumerate() {
                value.write_le_bytes(&mut fixture[start + 18 + slot * 16..][..16]);
            }
        }
        let mut encoded = [0u8; 16];
        reference.write_le_bytes(&mut encoded);
        Ok((
            fixture,
            HOST_HASH(&[b"aspis-m31-circle-basis-fold-control-v1", &encoded]),
        ))
    }

    fn host_fold_sink(
        fixture: &[u8],
        derive_coordinates: bool,
        batch_invert: bool,
    ) -> Result<[u8; 32]> {
        ensure!(fixture.len() == M31_CIRCLE_FOLD_FIXTURE_BYTES);
        let alpha = QM31::from_le_bytes(&fixture[..16]).context("fold alpha")?;
        let geometry = layer_geometry(&PROFILE_CAPACITY_LR10_Q36_G16, 0);
        let mut omega_powers = [CM31::ONE; aspis_core::params::CIRCLE_LOG_ORDER as usize];
        omega_powers[0] = geometry.omega;
        for bit in 1..omega_powers.len() {
            omega_powers[bit] = omega_powers[bit - 1].square();
        }
        let cached_point = |mut index: u32| {
            let mut point = geometry.offset;
            let mut bit = 0usize;
            while index != 0 {
                if index & 1 != 0 {
                    point = point.mul(omega_powers[bit]);
                }
                index >>= 1;
                bit += 1;
            }
            point
        };
        let mut coords = vec![M31::ZERO; 2 * M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
        let mut inverses = vec![M31::ZERO; 2 * M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
        let mut all_values = vec![[QM31::ZERO; 4]; M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS];
        let mut previous = None;
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            let start = 16 + fiber * FOLD_RECORD_BYTES;
            let index = u16::from_le_bytes(fixture[start..start + 2].try_into().unwrap());
            ensure!(previous.is_none_or(|value| index > value));
            previous = Some(index);
            let x = M31::from_le_bytes(fixture[start + 2..start + 6].try_into().unwrap())
                .context("fold x")?;
            let y = M31::from_le_bytes(fixture[start + 6..start + 10].try_into().unwrap())
                .context("fold y")?;
            if derive_coordinates {
                let point = cached_point(u32::from(index));
                ensure!(point.a == x && point.b == y && x != M31::ZERO && y != M31::ZERO);
                coords[2 * fiber] = x;
                coords[2 * fiber + 1] = y;
            }
            if !batch_invert {
                let inv_x = M31::from_le_bytes(fixture[start + 10..start + 14].try_into().unwrap())
                    .context("fold inv x")?;
                let inv_y = M31::from_le_bytes(fixture[start + 14..start + 18].try_into().unwrap())
                    .context("fold inv y")?;
                inverses[2 * fiber] = inv_x;
                inverses[2 * fiber + 1] = inv_y;
            }
            for slot in 0..4 {
                all_values[fiber][slot] = QM31::from_le_bytes(
                    &fixture[start + 18 + slot * 16..start + 18 + (slot + 1) * 16],
                )
                .context("fold value")?;
            }
        }
        if batch_invert {
            m31_batch_inverse(&coords, &mut inverses);
        }
        let mut accumulator = QM31::ZERO;
        for fiber in 0..M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS {
            accumulator = accumulator.add(qm31_circle_to_line_fold4(
                all_values[fiber],
                alpha,
                inverses[2 * fiber].half(),
                inverses[2 * fiber + 1].half(),
            ));
        }
        let mut encoded = [0u8; 16];
        accumulator.write_le_bytes(&mut encoded);
        Ok(HOST_HASH(&[
            b"aspis-m31-circle-basis-fold-control-v1",
            &encoded,
        ]))
    }

    fn mean(values: &[u64]) -> f64 {
        values.iter().sum::<u64>() as f64 / values.len() as f64
    }

    let rlc_fixture = build_rlc_fixture(SEED);
    let structured_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcStructuredFourDots,
    )?;
    let fused_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
    )?;
    let decoded_fused_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4,
    )?;
    let streaming_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcStreamingFourDots,
    )?;
    let prepared49_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcPreparedLimbs49,
    )?;
    let prepared49_two_rows_sink = host_rlc_sink(
        &rlc_fixture,
        M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows,
    )?;
    ensure!(structured_sink == fused_sink);
    ensure!(structured_sink == decoded_fused_sink);
    ensure!(structured_sink == streaming_sink);
    ensure!(structured_sink == prepared49_sink);
    ensure!(structured_sink == prepared49_two_rows_sink);
    let empty_leaf_sink = aspis_core::merkle::leaf_hash(HOST_HASH, 0, &[]);
    let c1_leaf_sink = aspis_core::merkle::leaf_hash(
        HOST_HASH,
        0,
        &rlc_fixture[GAMMA_BYTES..GAMMA_BYTES + M31_CIRCLE_BASIS_C1_LEAF_BYTES],
    );
    let (fold_fixture, fold_reference_sink) = build_fold_fixture(SEED ^ 0x464f_4c44)?;
    let fold_prevalidated_sink = host_fold_sink(&fold_fixture, false, false)?;
    let fold_cached_sink = host_fold_sink(&fold_fixture, true, false)?;
    let fold_derived_sink = host_fold_sink(&fold_fixture, true, true)?;
    ensure!(fold_reference_sink == fold_prevalidated_sink);
    ensure!(fold_prevalidated_sink == fold_cached_sink);
    ensure!(fold_prevalidated_sink == fold_derived_sink);

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 30 * LAMPORTS_PER_SOL)?;
    let rlc_account = Keypair::new();
    upload_proof(&rpc, &payer, &rlc_account, &rlc_fixture, true)?;
    let fold_account = Keypair::new();
    upload_proof(&rpc, &payer, &fold_account, &fold_fixture, true)?;

    let run_mode = |account: &Pubkey,
                    mode: M31CircleBasisDiagnosticMode,
                    sink: [u8; 32]|
     -> Result<(Vec<u64>, Vec<Option<String>>)> {
        let mut units = Vec::with_capacity(REPETITIONS);
        let mut errors = Vec::with_capacity(REPETITIONS);
        for _ in 0..REPETITIONS {
            let instruction = proof_instruction(
                &payer.pubkey(),
                account,
                &AspisInstruction::M31CircleBasisDiagnostic {
                    mode,
                    expected_sink: sink,
                },
            )?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                    instruction,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                rpc.latest_blockhash()?,
            );
            let (observed, error) = rpc.simulate(&transaction)?;
            units.push(observed.context("M31 diagnostic did not report CU")?);
            errors.push(error);
        }
        Ok((units, errors))
    };

    let mode_specs = [
        (
            "rlc_structured_four_independent_qm31_m31_dot",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcStructuredFourDots,
            structured_sink,
        ),
        (
            "rlc_fused_canonical_bytes_qm31_m31_dot4",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
            fused_sink,
        ),
        (
            "empty_leaf_hash_control",
            &rlc_account,
            M31CircleBasisDiagnosticMode::EmptyLeafHashControl,
            empty_leaf_sink,
        ),
        (
            "c1_leaf_hash_784_bytes",
            &rlc_account,
            M31CircleBasisDiagnosticMode::C1LeafHash784,
            c1_leaf_sink,
        ),
        (
            "fold_prevalidated_coordinates_control",
            &fold_account,
            M31CircleBasisDiagnosticMode::FoldPrevalidatedCoordinates,
            fold_prevalidated_sink,
        ),
        (
            "fold_cached_coordinates_prevalidated_inverses_control",
            &fold_account,
            M31CircleBasisDiagnosticMode::FoldCachedCoordinatesPrevalidatedInverses,
            fold_cached_sink,
        ),
        (
            "fold_cached_coordinates_batch_inverse_syscall",
            &fold_account,
            M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse,
            fold_derived_sink,
        ),
        (
            "rlc_decoded_then_typed_fused_qm31_m31_dot4",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4,
            decoded_fused_sink,
        ),
        (
            "rlc_streaming_one_slot_four_independent_qm31_m31_dot",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcStreamingFourDots,
            streaming_sink,
        ),
        (
            "rlc_prepared_limbs_exact_49_bytes",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcPreparedLimbs49,
            prepared49_sink,
        ),
        (
            "rlc_prepared_limbs_exact_49_bytes_two_rows",
            &rlc_account,
            M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows,
            prepared49_two_rows_sink,
        ),
    ];
    let mut variants = Vec::with_capacity(mode_specs.len());
    for (name, account, mode, sink) in mode_specs {
        let (simulation_cu, errors) = run_mode(&account.pubkey(), mode, sink)?;
        ensure!(
            errors.iter().all(Option::is_none),
            "{name} failed: {errors:?}"
        );
        let simulation_cu_mean = mean(&simulation_cu);
        variants.push(M31CircleBasisVariant {
            mode: name,
            expected_host_sink_hex: hex(&sink),
            accepted_all: true,
            simulation_cu,
            simulation_cu_mean,
            signed_headroom_vs_1_190_000_cu: STRICT_TARGET - simulation_cu_mean.round() as i64,
            signed_headroom_vs_1_400_000_cu: ABSOLUTE_CAP - simulation_cu_mean.round() as i64,
        });
    }

    let mut corruptions = Vec::new();
    let mut noncanonical_c1 = rlc_fixture.clone();
    noncanonical_c1[GAMMA_BYTES..GAMMA_BYTES + 4].copy_from_slice(&P.to_le_bytes());
    let noncanonical_c1_decoded_fused = noncanonical_c1.clone();
    let noncanonical_c1_streaming = noncanonical_c1.clone();
    let noncanonical_c1_two_rows = noncanonical_c1.clone();
    let mut noncanonical_c2 = rlc_fixture.clone();
    let c2_offset = GAMMA_BYTES + M31_CIRCLE_BASIS_C1_LEAF_BYTES;
    noncanonical_c2[c2_offset..c2_offset + 4].copy_from_slice(&P.to_le_bytes());
    let mut wrong_coordinate = fold_fixture.clone();
    let coordinate_offset = 16 + 2;
    let coordinate = u32::from_le_bytes(
        wrong_coordinate[coordinate_offset..coordinate_offset + 4]
            .try_into()
            .unwrap(),
    );
    wrong_coordinate[coordinate_offset..coordinate_offset + 4]
        .copy_from_slice(&((coordinate + 1) % P).to_le_bytes());
    let mut wrong_slot_order = fold_fixture.clone();
    let slot_start = 16 + 18;
    for byte in 0..16 {
        wrong_slot_order.swap(slot_start + byte, slot_start + 16 + byte);
    }

    let corruption_specs = [
        (
            "noncanonical_c1_m31",
            "rlc",
            GAMMA_BYTES,
            noncanonical_c1,
            M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
            fused_sink,
        ),
        (
            "noncanonical_c2_qm31",
            "rlc",
            c2_offset,
            noncanonical_c2,
            M31CircleBasisDiagnosticMode::RlcFusedCanonicalBytes,
            fused_sink,
        ),
        (
            "mutated_domain_coordinate",
            "fold",
            coordinate_offset,
            wrong_coordinate,
            M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse,
            fold_derived_sink,
        ),
        (
            "wrong_four_slot_order",
            "fold",
            slot_start,
            wrong_slot_order,
            M31CircleBasisDiagnosticMode::FoldDerivedCoordinatesBatchInverse,
            fold_derived_sink,
        ),
        (
            "noncanonical_c1_m31_decoded_fused",
            "rlc",
            GAMMA_BYTES,
            noncanonical_c1_decoded_fused,
            M31CircleBasisDiagnosticMode::RlcDecodedFusedDot4,
            decoded_fused_sink,
        ),
        (
            "noncanonical_c1_m31_streaming",
            "rlc",
            GAMMA_BYTES,
            noncanonical_c1_streaming,
            M31CircleBasisDiagnosticMode::RlcStreamingFourDots,
            streaming_sink,
        ),
        (
            "noncanonical_c1_m31_prepared_two_rows",
            "rlc",
            GAMMA_BYTES,
            noncanonical_c1_two_rows,
            M31CircleBasisDiagnosticMode::RlcPreparedLimbs49TwoRows,
            prepared49_two_rows_sink,
        ),
    ];
    for (target, fixture_name, offset, corrupted, mode, expected) in corruption_specs {
        let host_rejected = match fixture_name {
            "rlc" => host_rlc_sink(&corrupted, mode).map_or(true, |sink| sink != expected),
            "fold" => host_fold_sink(&corrupted, true, true).map_or(true, |sink| sink != expected),
            _ => unreachable!(),
        };
        ensure!(host_rejected, "{target} lacked host teeth");
        let account = Keypair::new();
        upload_proof(&rpc, &payer, &account, &corrupted, true)?;
        let (_, errors) = run_mode(&account.pubkey(), mode, expected)?;
        let sbf_rejected = errors.iter().all(Option::is_some);
        ensure!(sbf_rejected, "{target} accepted on SBF");
        corruptions.push(M31CircleBasisCorruptionCase {
            target,
            fixture: fixture_name,
            fixture_byte_offset: offset,
            host_rejected,
            sbf_rejected,
            sbf_error: errors.into_iter().flatten().next().unwrap(),
        });
    }

    let structured = variants[0].simulation_cu_mean;
    let fused = variants[1].simulation_cu_mean;
    let empty_leaf = variants[2].simulation_cu_mean;
    let c1_leaf = variants[3].simulation_cu_mean;
    let fold_control = variants[4].simulation_cu_mean;
    let fold_cached = variants[5].simulation_cu_mean;
    let fold_derived = variants[6].simulation_cu_mean;
    let decoded_fused = variants[7].simulation_cu_mean;
    let streaming = variants[8].simulation_cu_mean;
    let winning_rlc_variant = variants
        .iter()
        .filter(|variant| variant.mode.starts_with("rlc_"))
        .min_by(|left, right| left.simulation_cu_mean.total_cmp(&right.simulation_cu_mean))
        .context("missing M31 RLC variant")?;
    let winning_rlc_mode = winning_rlc_variant.mode;
    let winning_rlc_cu_mean = winning_rlc_variant.simulation_cu_mean;
    Ok(M31CircleBasisSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-m31-circle-basis-probe",
        validator_version: validator_version(),
        status: "decision_packet_only_provisional_shape_probe",
        diagnostic_instruction_wire_ordinal: 23,
        repetitions: REPETITIONS,
        compute_unit_limit: VERIFY_CU_LIMIT,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + diagnostic tag 23",
        structural_fibers: M31_CIRCLE_BASIS_DIAGNOSTIC_FIBERS,
        c1_field: "M31 candidate circle-polynomial code symbols",
        c1_columns: M31_CIRCLE_BASIS_C1_COLUMNS,
        c1_leaf_bytes: M31_CIRCLE_BASIS_C1_LEAF_BYTES,
        c2_field: "QM31 helpers, unchanged shape",
        c2_columns: 2,
        c2_leaf_bytes: M31_CIRCLE_BASIS_C2_LEAF_BYTES,
        gamma_powers: "0..50 prepared exactly once per measured instruction; helpers use 49 and 50",
        rlc_fixture_bytes: M31_CIRCLE_BASIS_RLC_FIXTURE_BYTES,
        fold_fixture_bytes: M31_CIRCLE_FOLD_FIXTURE_BYTES,
        host_structured_equals_fused: true,
        host_all_rlc_modes_equal: true,
        host_normalized_fold_matches_cubic_reference: true,
        variants,
        fused_rlc_savings_cu: (structured - fused).round() as i64,
        fused_rlc_savings_percent: (structured - fused) / structured * 100.0,
        decoded_fused_rlc_savings_vs_structured_cu: (structured - decoded_fused).round() as i64,
        decoded_fused_rlc_savings_vs_structured_percent: (structured - decoded_fused) / structured
            * 100.0,
        streaming_rlc_savings_vs_structured_cu: (structured - streaming).round() as i64,
        streaming_rlc_savings_vs_structured_percent: (structured - streaming) / structured * 100.0,
        winning_rlc_mode,
        winning_rlc_cu_mean,
        winning_rlc_savings_vs_structured_cu: (structured - winning_rlc_cu_mean).round() as i64,
        winning_rlc_savings_vs_structured_percent: (structured - winning_rlc_cu_mean) / structured
            * 100.0,
        c1_leaf_hash_incremental_over_empty_cu: (c1_leaf - empty_leaf).round() as i64,
        fold_cached_coordinate_derivation_increment_cu: (fold_cached - fold_control).round() as i64,
        fold_batch_inverse_syscall_increment_cu: (fold_derived - fold_cached).round() as i64,
        fold_coordinate_and_batch_inverse_increment_cu: (fold_derived - fold_control).round() as i64,
        fold_batch_inverse_backend: "one sol_big_mod_exp M31 inverse for 72 denominators, with Montgomery prefix/suffix products; host differential uses software M31::inv",
        all_corruptions_rejected: corruptions
            .iter()
            .all(|case| case.host_rejected && case.sbf_rejected),
        corruption_cases: corruptions,
        current_aspis_serialization: false,
        genuine_circle_pcs_integration_implemented: false,
        protocol_or_architecture_ruling_made: false,
        included_work: vec![
            "RLC control: 36 structural fibers, 4x49 canonical M31 C1 values, 2x4 canonical QM31 C2 helpers, and gamma powers 0..50 prepared once".to_string(),
            "fold control: normalized circle-to-line then line fold over 36 already-combined four-QM31 fibers".to_string(),
            "bookable fold row includes public-domain coordinate derivation and one 72-element M31 batch inversion; the prevalidated row is a separately labeled control".to_string(),
            "append-only RLC separation rows isolate canonical decode plus typed dot4 from a one-slot fixed-buffer streaming decode plus four independent dots".to_string(),
        ],
        excluded_work: vec![
            "no current Aspis proof parsing, serialization, root, Merkle frontier, or authentication".to_string(),
            "no circle FFT encoder, bit-reversed trace-to-codeword conformance, query sampling, or later line-FRI layers".to_string(),
            "no OOD relation, statement sumcheck, final polynomial, payment constraints, hiding, pool transition, or proof-account sealing".to_string(),
            "RLC and fold rows are disjoint controls and must not be added as an integrated-v4 total".to_string(),
        ],
        notes: vec![
            "M31 C1 is valid only under a genuine circle-polynomial PCS; dropping the imaginary CM31 limb from the current ordinary-univariate Aspis PCS would be unsound".to_string(),
            "The fold slot order is (x,y),(x,-y),(-x,-y),(-x,y); normalization is mechanically checked against c0+alpha*c1+alpha^2*c2+alpha^3*c3".to_string(),
            "This artifact supplies costs and headrooms to a decision packet. It adopts neither a one-transaction M31 architecture nor a split architecture and changes no production verifier".to_string(),
            "The legacy fused_rlc_savings fields compare the original canonical-byte fused row with the original structured row; the explicitly named decoded-fused, streaming, and winner fields carry the reopened separation result".to_string(),
        ],
    })
}

/// Account-backed measurement of the exact candidate v4 layer-zero width.
/// Fixture generation and upload happen before every measured simulation.
pub fn run_stage2_exact_wide_v4_diagnostic() -> Result<ExactWideV4DiagnosticSummary> {
    use aspis_core::field::{qm31_power_table, CM31, M31, P, QM31};
    use aspis_statement::wide_v4::{
        ExactWideFiber, C1_COLUMNS, C1_FIBER_BYTES, C2_COLUMNS, C2_FIBER_BYTES, FIBER_SLOTS,
        TOTAL_COLUMNS,
    };

    const REPETITIONS: usize = 5;
    const FIXTURE_SEED: u64 = 0x4558_4143_5457_5634;
    const GAMMA_BYTES: usize = 16;
    const FIXTURE_BYTES: usize = GAMMA_BYTES + C1_FIBER_BYTES + C2_FIBER_BYTES;

    fn next_m31(state: &mut u64) -> M31 {
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        M31((state.wrapping_mul(0x2545_f491_4f6c_dd1d) as u32) % P)
    }

    fn next_cm31(state: &mut u64) -> CM31 {
        CM31::new(next_m31(state), next_m31(state))
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: next_cm31(state),
            c1: next_cm31(state),
        }
    }

    fn build_fixture(seed: u64) -> (Vec<u8>, QM31, ExactWideFiber) {
        let mut state = seed;
        let gamma = next_qm31(&mut state);
        let fiber = ExactWideFiber {
            c1: core::array::from_fn(|_| core::array::from_fn(|_| next_cm31(&mut state))),
            c2: core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state))),
        };
        let mut encoded = vec![0u8; FIXTURE_BYTES];
        gamma.write_le_bytes(&mut encoded[..GAMMA_BYTES]);
        let c1_start = GAMMA_BYTES;
        for slot in 0..FIBER_SLOTS {
            for column in 0..C1_COLUMNS {
                let offset = c1_start + (slot * C1_COLUMNS + column) * 8;
                fiber.c1[slot][column].write_le_bytes(&mut encoded[offset..offset + 8]);
            }
        }
        // Canonical v4 C2 wire order is helper-major, while the arithmetic
        // seam is slot-major.
        let c2_start = c1_start + C1_FIBER_BYTES;
        for helper in 0..C2_COLUMNS {
            for slot in 0..FIBER_SLOTS {
                let offset = c2_start + (helper * FIBER_SLOTS + slot) * 16;
                fiber.c2[slot][helper].write_le_bytes(&mut encoded[offset..offset + 16]);
            }
        }
        (encoded, gamma, fiber)
    }

    fn build_batch_fixture(seed: u64, fibers: usize) -> (Vec<u8>, QM31, Vec<ExactWideFiber>) {
        let mut state = seed;
        let gamma = next_qm31(&mut state);
        let values = (0..fibers)
            .map(|_| ExactWideFiber {
                c1: core::array::from_fn(|_| core::array::from_fn(|_| next_cm31(&mut state))),
                c2: core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state))),
            })
            .collect::<Vec<_>>();
        let fiber_bytes = C1_FIBER_BYTES + C2_FIBER_BYTES;
        let mut encoded = vec![0u8; GAMMA_BYTES + fibers * fiber_bytes];
        gamma.write_le_bytes(&mut encoded[..GAMMA_BYTES]);
        for (index, fiber) in values.iter().enumerate() {
            let base = GAMMA_BYTES + index * fiber_bytes;
            for slot in 0..FIBER_SLOTS {
                for column in 0..C1_COLUMNS {
                    let offset = base + (slot * C1_COLUMNS + column) * 8;
                    fiber.c1[slot][column].write_le_bytes(&mut encoded[offset..offset + 8]);
                }
            }
            let c2_start = base + C1_FIBER_BYTES;
            for helper in 0..C2_COLUMNS {
                for slot in 0..FIBER_SLOTS {
                    let offset = c2_start + (helper * FIBER_SLOTS + slot) * 16;
                    fiber.c2[slot][helper].write_le_bytes(&mut encoded[offset..offset + 16]);
                }
            }
        }
        (encoded, gamma, values)
    }

    fn decode_fixture(bytes: &[u8]) -> Result<(QM31, ExactWideFiber)> {
        ensure!(
            bytes.len() == FIXTURE_BYTES,
            "bad exact-wide fixture length"
        );
        let gamma =
            QM31::from_le_bytes(&bytes[..GAMMA_BYTES]).context("decode exact-wide gamma")?;
        let mut fiber = ExactWideFiber {
            c1: [[CM31::ZERO; C1_COLUMNS]; FIBER_SLOTS],
            c2: [[QM31::ZERO; C2_COLUMNS]; FIBER_SLOTS],
        };
        let c1_start = GAMMA_BYTES;
        let c2_start = c1_start + C1_FIBER_BYTES;
        for slot in 0..FIBER_SLOTS {
            for column in 0..C1_COLUMNS {
                let offset = c1_start + (slot * C1_COLUMNS + column) * 8;
                fiber.c1[slot][column] = CM31::from_le_bytes(&bytes[offset..offset + 8])
                    .context("decode exact-wide C1 value")?;
            }
        }
        for helper in 0..C2_COLUMNS {
            for slot in 0..FIBER_SLOTS {
                let offset = c2_start + (helper * FIBER_SLOTS + slot) * 16;
                fiber.c2[slot][helper] = QM31::from_le_bytes(&bytes[offset..offset + 16])
                    .context("decode exact-wide C2 value")?;
            }
        }
        Ok((gamma, fiber))
    }

    fn host_sink(mode: ExactWideV4DiagnosticMode, fixture: &[u8]) -> Result<[u8; 32]> {
        let c1_start = GAMMA_BYTES;
        let c2_start = c1_start + C1_FIBER_BYTES;
        Ok(match mode {
            ExactWideV4DiagnosticMode::BaselineFourDots | ExactWideV4DiagnosticMode::FusedDot4 => {
                let (gamma, fiber) = decode_fixture(fixture)?;
                let combined = match mode {
                    ExactWideV4DiagnosticMode::BaselineFourDots => {
                        aspis_statement::wide_v4::combine_exact_wide_fiber_baseline(&fiber, gamma)
                    }
                    ExactWideV4DiagnosticMode::FusedDot4 => {
                        aspis_statement::wide_v4::combine_exact_wide_fiber(&fiber, gamma)
                    }
                    _ => unreachable!(),
                };
                let mut encoded = [0u8; FIBER_SLOTS * 16];
                for (slot, value) in combined.iter().enumerate() {
                    value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
                }
                HOST_HASH(&[b"aspis-exact-wide-v4-combined", &encoded])
            }
            ExactWideV4DiagnosticMode::EmptyLeafHashControl => {
                aspis_core::merkle::leaf_hash(HOST_HASH, 0, &[])
            }
            ExactWideV4DiagnosticMode::C1LeafHash => {
                aspis_core::merkle::leaf_hash(HOST_HASH, 0, &fixture[c1_start..c2_start])
            }
            ExactWideV4DiagnosticMode::C2LeafHash => aspis_core::merkle::leaf_hash(
                HOST_HASH,
                aspis_core::proof::SECOND_PHASE_LAYER_TAG,
                &fixture[c2_start..],
            ),
            ExactWideV4DiagnosticMode::GammaPowersControl
            | ExactWideV4DiagnosticMode::GammaPowers0To50 => {
                let gamma = QM31::from_le_bytes(&fixture[..GAMMA_BYTES])
                    .context("decode gamma for host power sink")?;
                let mut encoded = [0u8; TOTAL_COLUMNS * 16];
                match mode {
                    ExactWideV4DiagnosticMode::GammaPowersControl => {
                        for chunk in encoded.chunks_exact_mut(16) {
                            QM31::ONE.write_le_bytes(chunk);
                        }
                    }
                    ExactWideV4DiagnosticMode::GammaPowers0To50 => {
                        let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
                        for (power, chunk) in powers.iter().zip(encoded.chunks_exact_mut(16)) {
                            power.write_le_bytes(chunk);
                        }
                    }
                    _ => unreachable!(),
                }
                HOST_HASH(&[b"aspis-exact-wide-v4-powers", &encoded])
            }
            ExactWideV4DiagnosticMode::FusedBatch36Unprepared
            | ExactWideV4DiagnosticMode::FusedBatch36Prepared
            | ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes => {
                let fiber_bytes = C1_FIBER_BYTES + C2_FIBER_BYTES;
                ensure!(
                    fixture.len()
                        == GAMMA_BYTES
                            + aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS * fiber_bytes,
                    "bad exact-wide batch fixture length"
                );
                let gamma = QM31::from_le_bytes(&fixture[..GAMMA_BYTES])
                    .context("decode exact-wide batch gamma")?;
                let prepared = if matches!(
                    mode,
                    ExactWideV4DiagnosticMode::FusedBatch36Prepared
                        | ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes
                ) {
                    Some(aspis_statement::wide_v4::prepare_exact_wide_weights(gamma))
                } else {
                    None
                };
                let bytes_mode =
                    matches!(mode, ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes);
                let mut accumulator = [QM31::ZERO; FIBER_SLOTS];
                for index in 0..aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS {
                    let start = GAMMA_BYTES + index * fiber_bytes;
                    let combined = if bytes_mode {
                        let c2_start = start + C1_FIBER_BYTES;
                        aspis_statement::wide_v4::combine_exact_wide_bytes_prepared(
                            &fixture[start..c2_start],
                            &fixture[c2_start..c2_start + C2_FIBER_BYTES],
                            prepared.as_ref().unwrap(),
                        )
                        .context("decode exact-wide prepared byte fiber")?
                    } else {
                        let mut single = Vec::with_capacity(FIXTURE_BYTES);
                        single.extend_from_slice(&fixture[..GAMMA_BYTES]);
                        single.extend_from_slice(&fixture[start..start + fiber_bytes]);
                        let (_, fiber) = decode_fixture(&single)?;
                        if let Some(weights) = prepared.as_ref() {
                            aspis_statement::wide_v4::combine_exact_wide_fiber_prepared(
                                &fiber, weights,
                            )
                        } else {
                            aspis_statement::wide_v4::combine_exact_wide_fiber(&fiber, gamma)
                        }
                    };
                    for slot in 0..FIBER_SLOTS {
                        accumulator[slot] = accumulator[slot].add(combined[slot]);
                    }
                }
                let mut encoded = [0u8; FIBER_SLOTS * 16];
                for (slot, value) in accumulator.iter().enumerate() {
                    value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
                }
                HOST_HASH(&[b"aspis-exact-wide-v4-batch36", &encoded])
            }
        })
    }

    fn mode_name(mode: ExactWideV4DiagnosticMode) -> &'static str {
        match mode {
            ExactWideV4DiagnosticMode::BaselineFourDots => "baseline_four_qm31_cm31_dot_49",
            ExactWideV4DiagnosticMode::FusedDot4 => "optimized_fused_qm31_cm31_dot4_49",
            ExactWideV4DiagnosticMode::EmptyLeafHashControl => "empty_leaf_hash_control",
            ExactWideV4DiagnosticMode::C1LeafHash => "c1_leaf_hash_1568_bytes",
            ExactWideV4DiagnosticMode::C2LeafHash => "c2_leaf_hash_128_bytes",
            ExactWideV4DiagnosticMode::GammaPowersControl => {
                "gamma_power_serialization_hash_control"
            }
            ExactWideV4DiagnosticMode::GammaPowers0To50 => "gamma_powers_0_through_50",
            ExactWideV4DiagnosticMode::FusedBatch36Unprepared => {
                "q36_structural_max_36_fibers_fused_unprepared"
            }
            ExactWideV4DiagnosticMode::FusedBatch36Prepared => {
                "q36_structural_max_36_fibers_fused_prepared_once"
            }
            ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes => {
                "q36_structural_max_36_fibers_prepared_bytes"
            }
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn simulate_diagnostic(
        rpc: &Rpc,
        payer: &Keypair,
        fixture_account: &Pubkey,
        mode: ExactWideV4DiagnosticMode,
        expected_sink: [u8; 32],
    ) -> Result<(Option<u64>, Option<String>)> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(*fixture_account, false)],
            data: to_vec(&AspisInstruction::ExactWideV4Diagnostic {
                mode,
                expected_sink,
            })?,
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        rpc.simulate(&transaction)
    }

    let (fixture, gamma, fiber) = build_fixture(FIXTURE_SEED);
    ensure!(
        fixture.len() == FIXTURE_BYTES,
        "fixture encoder length drifted"
    );
    let host_baseline = aspis_statement::wide_v4::combine_exact_wide_fiber_baseline(&fiber, gamma);
    let host_fused = aspis_statement::wide_v4::combine_exact_wide_fiber(&fiber, gamma);
    ensure!(
        host_baseline == host_fused,
        "host exact-wide baseline/fused differential failed"
    );
    let (batch_fixture, batch_gamma, batch_fibers) = build_batch_fixture(
        FIXTURE_SEED,
        aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS,
    );
    ensure!(
        batch_gamma == gamma && batch_fibers.first() == Some(&fiber),
        "single and batch fixture prefixes diverged"
    );
    let host_batch_unprepared = host_sink(
        ExactWideV4DiagnosticMode::FusedBatch36Unprepared,
        &batch_fixture,
    )?;
    let host_batch_prepared = host_sink(
        ExactWideV4DiagnosticMode::FusedBatch36Prepared,
        &batch_fixture,
    )?;
    let host_batch_prepared_bytes = host_sink(
        ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
        &batch_fixture,
    )?;
    ensure!(
        host_batch_unprepared == host_batch_prepared
            && host_batch_prepared == host_batch_prepared_bytes,
        "host unprepared/structured-prepared/byte-prepared batch differential failed"
    );

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 5 * LAMPORTS_PER_SOL)?;
    let fixture_account = Keypair::new();
    let (fixture_upload_chunks, fixture_upload_cu_excluded) =
        upload_proof(&rpc, &payer, &fixture_account, &fixture, true)?;
    let batch_fixture_account = Keypair::new();
    let (batch_fixture_upload_chunks, batch_fixture_upload_cu_excluded) =
        upload_proof(&rpc, &payer, &batch_fixture_account, &batch_fixture, true)?;

    let modes = [
        ExactWideV4DiagnosticMode::BaselineFourDots,
        ExactWideV4DiagnosticMode::FusedDot4,
        ExactWideV4DiagnosticMode::EmptyLeafHashControl,
        ExactWideV4DiagnosticMode::C1LeafHash,
        ExactWideV4DiagnosticMode::C2LeafHash,
        ExactWideV4DiagnosticMode::GammaPowersControl,
        ExactWideV4DiagnosticMode::GammaPowers0To50,
        ExactWideV4DiagnosticMode::FusedBatch36Unprepared,
        ExactWideV4DiagnosticMode::FusedBatch36Prepared,
        ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
    ];
    let mut variants = Vec::with_capacity(modes.len());
    for mode in modes {
        let batch_mode = matches!(
            mode,
            ExactWideV4DiagnosticMode::FusedBatch36Unprepared
                | ExactWideV4DiagnosticMode::FusedBatch36Prepared
                | ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes
        );
        let selected_fixture = if batch_mode { &batch_fixture } else { &fixture };
        let selected_account = if batch_mode {
            batch_fixture_account.pubkey()
        } else {
            fixture_account.pubkey()
        };
        let expected_sink = host_sink(mode, selected_fixture)?;
        let mut simulation_cu = Vec::with_capacity(REPETITIONS);
        let mut simulation_errors = Vec::with_capacity(REPETITIONS);
        for _ in 0..REPETITIONS {
            let (units, error) =
                simulate_diagnostic(&rpc, &payer, &selected_account, mode, expected_sink)?;
            simulation_cu.push(units.context("exact-wide diagnostic did not report CU")?);
            simulation_errors.push(error);
        }
        ensure!(
            simulation_cu.windows(2).all(|pair| pair[0] == pair[1]),
            "{} was not deterministic: {simulation_cu:?}",
            mode_name(mode)
        );
        ensure!(
            simulation_errors.windows(2).all(|pair| pair[0] == pair[1]),
            "{} error result was not deterministic: {simulation_errors:?}",
            mode_name(mode)
        );
        let accepted_all = simulation_errors.iter().all(Option::is_none);
        if !matches!(mode, ExactWideV4DiagnosticMode::FusedBatch36Unprepared) {
            ensure!(
                accepted_all,
                "{} failed on SBF: {simulation_errors:?}",
                mode_name(mode)
            );
        }
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        variants.push(ExactWideV4DiagnosticVariant {
            mode: mode_name(mode),
            expected_host_sink_hex: hex(&expected_sink),
            sbf_matched_host_sink: accepted_all,
            accepted_all,
            simulation_cu,
            simulation_errors,
            simulation_cu_mean,
        });
    }

    fn mutate_canonical_m31(bytes: &mut [u8], offset: usize) {
        let value = u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap());
        let changed = if value + 1 == P { 0 } else { value + 1 };
        bytes[offset..offset + 4].copy_from_slice(&changed.to_le_bytes());
    }

    let c1_offset = GAMMA_BYTES;
    let c2_offset = GAMMA_BYTES + C1_FIBER_BYTES;
    let mut corrupted_c1 = fixture.clone();
    mutate_canonical_m31(&mut corrupted_c1, c1_offset);
    let mut corrupted_c2 = fixture.clone();
    mutate_canonical_m31(&mut corrupted_c2, c2_offset);
    let corrupted_inputs = [
        (
            "c1_first_cm31_limb",
            c1_offset,
            &corrupted_c1,
            ExactWideV4DiagnosticMode::BaselineFourDots,
        ),
        (
            "c1_first_cm31_limb",
            c1_offset,
            &corrupted_c1,
            ExactWideV4DiagnosticMode::FusedDot4,
        ),
        (
            "c1_first_cm31_limb",
            c1_offset,
            &corrupted_c1,
            ExactWideV4DiagnosticMode::C1LeafHash,
        ),
        (
            "c2_first_qm31_limb",
            c2_offset,
            &corrupted_c2,
            ExactWideV4DiagnosticMode::FusedDot4,
        ),
        (
            "c2_first_qm31_limb",
            c2_offset,
            &corrupted_c2,
            ExactWideV4DiagnosticMode::C2LeafHash,
        ),
    ];
    let mut corruption_cases = Vec::with_capacity(corrupted_inputs.len());
    for (target, offset, corrupted, mode) in corrupted_inputs {
        let canonical_sink = host_sink(mode, &fixture)?;
        let corrupted_sink = host_sink(mode, corrupted)?;
        ensure!(
            canonical_sink != corrupted_sink,
            "{target} did not change {} host sink",
            mode_name(mode)
        );
        let corrupt_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_account, corrupted, true)?;
        let (_, error) = simulate_diagnostic(
            &rpc,
            &payer,
            &corrupt_account.pubkey(),
            mode,
            canonical_sink,
        )?;
        ensure!(
            error.is_some(),
            "{target} unexpectedly matched canonical {} sink on SBF",
            mode_name(mode)
        );
        corruption_cases.push(ExactWideV4CorruptionCase {
            target,
            mode: mode_name(mode),
            fixture_byte_offset: offset,
            host_corrupted_sink_differs: true,
            host_rejected_malformed: false,
            sbf_rejected_canonical_sink: true,
            sbf_error: error.unwrap(),
        });
    }

    let malformed_batch_inputs = [
        ("noncanonical_c1_m31_limb", GAMMA_BYTES, {
            let mut bytes = batch_fixture.clone();
            bytes[GAMMA_BYTES..GAMMA_BYTES + 4].copy_from_slice(&P.to_le_bytes());
            bytes
        }),
        ("noncanonical_c2_m31_limb", GAMMA_BYTES + C1_FIBER_BYTES, {
            let mut bytes = batch_fixture.clone();
            let offset = GAMMA_BYTES + C1_FIBER_BYTES;
            bytes[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            bytes
        }),
    ];
    for (target, offset, malformed) in malformed_batch_inputs {
        ensure!(
            host_sink(
                ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
                &malformed,
            )
            .is_err(),
            "{target} unexpectedly decoded on host"
        );
        let malformed_account = Keypair::new();
        upload_proof(&rpc, &payer, &malformed_account, &malformed, true)?;
        let (_, error) = simulate_diagnostic(
            &rpc,
            &payer,
            &malformed_account.pubkey(),
            ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes,
            host_batch_prepared_bytes,
        )?;
        let sbf_error = error.context(format!("{target} unexpectedly accepted on SBF"))?;
        ensure!(
            sbf_error.contains("InvalidAccountData"),
            "{target} rejected for the wrong SBF reason: {sbf_error}"
        );
        corruption_cases.push(ExactWideV4CorruptionCase {
            target,
            mode: mode_name(ExactWideV4DiagnosticMode::FusedBatch36PreparedBytes),
            fixture_byte_offset: offset,
            host_corrupted_sink_differs: false,
            host_rejected_malformed: true,
            sbf_rejected_canonical_sink: true,
            sbf_error,
        });
    }

    let baseline_mean = variants[0].simulation_cu_mean;
    let fused_mean = variants[1].simulation_cu_mean;
    let empty_hash_mean = variants[2].simulation_cu_mean;
    let fused_dot4_savings_cu = (baseline_mean - fused_mean).round() as i64;
    let batch_unprepared_accepted = variants[7].accepted_all;
    let batch_unprepared_compute_budget_exhausted = !batch_unprepared_accepted
        && variants[7].simulation_errors.iter().all(|error| {
            error.as_ref().is_some_and(|text| {
                text.contains("ComputationalBudgetExceeded")
                    || (text.contains("ProgramFailedToComplete")
                        && text.contains("exceeded CUs meter"))
            })
        });
    ensure!(
        batch_unprepared_accepted || batch_unprepared_compute_budget_exhausted,
        "unprepared q36 batch failed for a reason other than compute-budget exhaustion: {:?}",
        variants[7].simulation_errors
    );
    let batch_prepared_accepted = variants[8].accepted_all;
    let batch_unprepared_cu_mean_or_cap = variants[7].simulation_cu_mean;
    let batch_prepared_cu_mean = variants[8].simulation_cu_mean;
    let batch_prepared_bytes_accepted = variants[9].accepted_all;
    let batch_prepared_bytes_cu_mean = variants[9].simulation_cu_mean;
    let batch_prepared_savings_cu_if_exact = batch_unprepared_accepted
        .then_some((batch_unprepared_cu_mean_or_cap - batch_prepared_cu_mean).round() as i64);
    Ok(ExactWideV4DiagnosticSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-exact-wide-v4-diagnostic"
            .to_string(),
        validator_version: validator_version(),
        diagnostic_instruction_wire_ordinal: 21,
        final_payment_kat_reserved_wire_ordinal: 20,
        final_payment_kat_implemented: false,
        repetitions: REPETITIONS,
        fixture_seed: FIXTURE_SEED,
        fixture_payload_bytes: FIXTURE_BYTES,
        fixture_upload_chunks,
        fixture_upload_cu_excluded,
        batch_fixture_payload_bytes: batch_fixture.len(),
        batch_fixture_upload_chunks,
        batch_fixture_upload_cu_excluded,
        fixture_generation_in_measured_instruction: false,
        c1_columns: C1_COLUMNS,
        c2_columns: C2_COLUMNS,
        total_gamma_powers: TOTAL_COLUMNS,
        c1_leaf_bytes: C1_FIBER_BYTES,
        c2_leaf_bytes: C2_FIBER_BYTES,
        c1_layout: "slot-major: 4 slots x 49 CM31 x 8 bytes",
        c2_layout: "helper-major wire order: 2 helpers x 4 slots x 16 bytes",
        host_baseline_equals_fused: true,
        fused_dot4_savings_cu,
        fused_dot4_savings_percent: fused_dot4_savings_cu as f64 / baseline_mean * 100.0,
        c1_leaf_hash_incremental_over_empty_cu: (variants[3].simulation_cu_mean
            - empty_hash_mean)
            .round() as i64,
        c2_leaf_hash_incremental_over_empty_cu: (variants[4].simulation_cu_mean
            - empty_hash_mean)
            .round() as i64,
        gamma_powers_incremental_over_control_cu: (variants[6].simulation_cu_mean
            - variants[5].simulation_cu_mean)
            .round() as i64,
        gate_q36_batch_unique_fibers:
            aspis_verifier::EXACT_WIDE_V4_DIAGNOSTIC_BATCH_FIBERS,
        gate_batch_count_provenance: "structural collision-free q36 maximum; verifier cost cannot rely on transcript collisions".to_string(),
        frozen_q36_fixture_unique_fibers: [35, 35],
        theoretical_q36_unique_fibers_max: 36,
        transaction_compute_limit_cu: VERIFY_CU_LIMIT,
        strict_transaction_target_cu: 1_190_000,
        heap_frame_bytes: HEAP_FRAME_BYTES,
        transaction_envelope: "set_compute_unit_limit(1,400,000) + request_heap_frame(262,144) + ExactWideV4Diagnostic",
        batch_unprepared_accepted,
        batch_unprepared_compute_budget_exhausted,
        batch_prepared_accepted,
        batch_unprepared_cu_mean_or_cap,
        batch_prepared_cu_mean,
        batch_prepared_headroom_vs_compute_cap_cu: VERIFY_CU_LIMIT as i64
            - batch_prepared_cu_mean.round() as i64,
        batch_prepared_headroom_vs_strict_target_cu: 1_190_000
            - batch_prepared_cu_mean.round() as i64,
        batch_prepared_bytes_accepted,
        batch_prepared_bytes_cu_mean,
        batch_prepared_bytes_headroom_vs_compute_cap_cu: VERIFY_CU_LIMIT as i64
            - batch_prepared_bytes_cu_mean.round() as i64,
        batch_prepared_bytes_headroom_vs_strict_target_cu: 1_190_000
            - batch_prepared_bytes_cu_mean.round() as i64,
        batch_prepared_bytes_savings_vs_structured_cu: (batch_prepared_cu_mean
            - batch_prepared_bytes_cu_mean)
            .round() as i64,
        batch_prepared_bytes_savings_vs_structured_percent: (batch_prepared_cu_mean
            - batch_prepared_bytes_cu_mean)
            / batch_prepared_cu_mean
            * 100.0,
        batch_prepared_savings_cu_if_exact,
        batch_prepared_savings_lower_bound_cu: (batch_unprepared_cu_mean_or_cap
            - batch_prepared_cu_mean)
            .round() as i64,
        batch_prepared_bytes_savings_lower_bound_cu: (batch_unprepared_cu_mean_or_cap
            - batch_prepared_bytes_cu_mean)
            .round() as i64,
        variants,
        all_corruptions_rejected_sbf: corruption_cases
            .iter()
            .all(|case| case.sbf_rejected_canonical_sink),
        corruption_cases,
        included_work: vec![
            "account borrow, canonical field decoding, gamma powers 0..50, four independent 49-term QM31-by-CM31 dots, gamma^49/gamma^50 helper products, result serialization, and observable sink hash in baseline mode".to_string(),
            "the identical path with fused qm31_cm31_dot4 in optimized mode; the paired delta isolates the arithmetic-kernel change".to_string(),
            "Merkle leaf_hash domain framing plus SHA-256 syscall over exactly 1,568 C1 bytes or 128 C2 bytes; empty-leaf control is reported".to_string(),
            "standalone gamma power-table construction with matched 816-byte serialization/hash control".to_string(),
            "gate-relevant q36 structural maximum of 36 distinct account-backed fibers: unprepared fused setup per fiber versus one prepared gamma/weight table reused across all fibers".to_string(),
            "prepared-byte batch over the same 36 fibers: canonical CM31/QM31 parsing is fused into the dot kernel without materializing a 1,696-byte ExactWideFiber matrix".to_string(),
        ],
        excluded_work: vec![
            "fixture generation, account creation, upload transactions, rent, and upload CU".to_string(),
            "Merkle frontier/node hashing, query derivation, proof parsing beyond the fixture account envelope, and full PCS verification".to_string(),
            "102-value two-point statement framing (49 C1 + 2 C2 at z and XOR-11(z)), LogUp/payment constraints, composition, masking/hiding, and g32 grinding".to_string(),
        ],
        notes: vec![
            "This is an exact-width SBF diagnostic, not a proof and not the final payment-v4 KAT. ABI tag 20 remains reserved/inactive; this diagnostic is append-only tag 21.".to_string(),
            "All five simulations per mode are asserted bit-for-bit deterministic. Acceptance means the SBF sink equals the independently computed host sink.".to_string(),
            "C1 arithmetic is 49 CM31 values per slot because this diagnostic prices Aspis's current custom CM31-coset PCS; the two C2 helpers are QM31 terms weighted by gamma^49 and gamma^50. An M31 circle-polynomial PCS is a separate candidate protocol measured separately, not a reinterpretation of these bytes.".to_string(),
            "Absolute transaction CU includes compute-budget dispatch, program/account dispatch, fixture framing, and sink comparison. Use the paired/control deltas for kernel attribution.".to_string(),
            "Headroom fields name their denominator explicitly: the 1.4M execution cap and the separate 1.19M project target. They apply to this diagnostic transaction alone, not a composed payment proof.".to_string(),
            "The gate batch uses the collision-free q36 maximum of 36. Both checked-in q36/g32 v3 fixtures happen to encode 35 unique layer-0 fibers; sampling luck does not lower the fixed verifier requirement.".to_string(),
            "If the unprepared batch exhausts the transaction budget, its reported CU is a cap/failure observation and the prepared savings field is a lower bound, not an exact total delta.".to_string(),
            "The prepared-byte parser is differential-tested against the structured path and explicitly rejects noncanonical C1 and C2 M31 limbs on both host and SBF.".to_string(),
            "The corruption matrix changes canonical C1/C2 field bytes in uploaded accounts and proves both arithmetic implementations and exact leaf hashes consume those bytes.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct CompositionProbeVariant {
    pub name: &'static str,
    pub kernel: &'static str,
    pub parameters: CompositionProbeParameters,
    pub host_qm31_multiplications: u32,
    pub host_qm31_by_cm31_multiplications: u32,
    pub host_additions_or_subtractions: u32,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub matching_rlc_only_cu: Vec<u64>,
    pub matching_rlc_only_cu_mean: f64,
    pub composition_incremental_cu_over_matching_rlc: i64,
    pub rlc_delta_from_frozen_k64_cu: i64,
    pub projected_total_cu: i64,
    pub headroom_vs_1_19m_cu: i64,
    pub meets_10_percent_slack: bool,
}

#[derive(Clone, Copy, Serialize)]
pub struct CompositionProbeParameters {
    pub opened_values: u16,
    pub poseidon_sbox_terms: u16,
    pub poseidon_linear_terms: u16,
    pub logup_degree3_terms: u16,
    pub range_bit_terms: u16,
    pub eq_variables: u8,
}

impl From<aspis_statement::CompositionProbe> for CompositionProbeParameters {
    fn from(value: aspis_statement::CompositionProbe) -> Self {
        Self {
            opened_values: value.opened_values,
            poseidon_sbox_terms: value.poseidon_sbox_terms,
            poseidon_linear_terms: value.poseidon_linear_terms,
            logup_degree3_terms: value.logup_degree3_terms,
            range_bit_terms: value.range_bit_terms,
            eq_variables: value.eq_variables,
        }
    }
}

#[derive(Serialize)]
pub struct CompositionProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub baseline_cu: Vec<u64>,
    pub baseline_cu_mean: f64,
    pub frozen_k64_rlc_only_cu: Vec<u64>,
    pub frozen_k64_rlc_only_cu_mean: f64,
    pub pre_composition_projection_cu: i64,
    pub transaction_target_cu: i64,
    pub ten_percent_slack_maximum_cu: i64,
    pub variants: Vec<CompositionProbeVariant>,
    pub notes: Vec<String>,
}

fn composition_instruction(
    probe: aspis_statement::CompositionProbe,
    optimized: bool,
) -> Result<Instruction> {
    Ok(Instruction {
        program_id: aspis_verifier::id(),
        accounts: vec![],
        data: to_vec(&AspisInstruction::ConstraintCompositionProbe {
            opened_values: probe.opened_values,
            poseidon_sbox_terms: probe.poseidon_sbox_terms,
            poseidon_linear_terms: probe.poseidon_linear_terms,
            logup_degree3_terms: probe.logup_degree3_terms,
            range_bit_terms: probe.range_bit_terms,
            eq_variables: probe.eq_variables,
            optimized,
        })?,
    })
}

fn simulate_pure_instruction(
    rpc: &Rpc,
    payer: &Keypair,
    instruction: Instruction,
    repetitions: usize,
) -> Result<Vec<u64>> {
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            instruction,
        ],
        Some(&payer.pubkey()),
        &[payer],
        blockhash,
    );
    let mut units = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        let (run_units, error) = rpc.simulate(&transaction)?;
        anyhow::ensure!(
            error.is_none(),
            "composition probe simulation failed: {error:?}"
        );
        units.push(run_units.context("composition probe did not report units")?);
    }
    Ok(units)
}

#[derive(Serialize)]
pub struct PaymentHidingPlacementVariant {
    pub placement: &'static str,
    pub placement_ordinal: u8,
    pub expected_sink_hex: String,
    pub host_sink_matched: bool,
    pub sbf_sink_matched: bool,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct PaymentHidingPlacementSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub query_count: usize,
    pub mask_oracle_count: usize,
    pub in_batch_c2_columns: usize,
    pub in_batch_leaf_bytes: usize,
    pub separate_h1_leaf_bytes: usize,
    pub separate_mask_leaf_bytes: usize,
    pub variants: Vec<PaymentHidingPlacementVariant>,
    pub separate_minus_in_batch_cu: i64,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

pub fn run_stage2_payment_hiding_placement_v4() -> Result<PaymentHidingPlacementSummary> {
    const REPETITIONS: usize = 5;
    const INSTRUCTION_WIRE_ORDINAL: u8 = 32;
    let layouts = [
        (
            0u8,
            "in_batch_one_c2_tree",
            aspis_core::statement_hiding::PaymentHidingPlacement::InBatch,
        ),
        (
            1u8,
            "separate_h1_and_mask_trees",
            aspis_core::statement_hiding::PaymentHidingPlacement::SeparateCommitment,
        ),
    ];
    let mut host_rows = Vec::new();
    for (ordinal, name, placement) in layouts {
        let sink =
            aspis_core::statement_hiding::payment_hiding_placement_probe(HOST_HASH, placement)
                .map_err(|_| anyhow!("host hiding placement probe exhausted a challenge"))?;
        let mut bytes = [0u8; 16];
        sink.write_le_bytes(&mut bytes);
        host_rows.push((ordinal, name, bytes));
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let to_hex = |bytes: &[u8]| bytes.iter().map(|byte| format!("{byte:02x}")).collect();
    let mut variants = Vec::new();
    for (ordinal, name, expected_sink) in host_rows {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::MeasurePaymentHidingPlacementV4 {
                placement: ordinal,
                expected_sink,
            })?,
        };
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        variants.push(PaymentHidingPlacementVariant {
            placement: name,
            placement_ordinal: ordinal,
            expected_sink_hex: to_hex(&expected_sink),
            host_sink_matched: true,
            sbf_sink_matched: true,
            simulation_cu,
            simulation_cu_mean,
        });
    }
    let delta = (variants[1].simulation_cu_mean - variants[0].simulation_cu_mean).round() as i64;
    Ok(PaymentHidingPlacementSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-payment-hiding-placement-v4"
            .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        repetitions: REPETITIONS,
        query_count: aspis_core::statement_hiding::PAYMENT_HIDING_PLACEMENT_QUERY_COUNT,
        mask_oracle_count: aspis_core::statement_hiding::PAYMENT_MASK_ORACLE_COUNT,
        in_batch_c2_columns: 7,
        in_batch_leaf_bytes:
            aspis_core::statement_hiding::PAYMENT_HIDING_IN_BATCH_LEAF_BYTES,
        separate_h1_leaf_bytes:
            aspis_core::statement_hiding::PAYMENT_HIDING_SEPARATE_H1_LEAF_BYTES,
        separate_mask_leaf_bytes:
            aspis_core::statement_hiding::PAYMENT_HIDING_SEPARATE_MASK_LEAF_BYTES,
        variants,
        separate_minus_in_batch_cu: delta,
        included_work: vec![
            "ten-round degree-10 masked payment-sumcheck verifier transcript".to_string(),
            "nonzero kappa and eta Fiat-Shamir sampling".to_string(),
            "six-factor H(z) terminal aggregation".to_string(),
            "q36 seven-column QM31 RLC arithmetic".to_string(),
            "q36 leaf hashing and six radix-4 authentication levels".to_string(),
        ],
        excluded_work: vec![
            "main payment constraint terminal evaluation".to_string(),
            "common mask-aggregate fold/relation proof".to_string(),
            "proof parsing and account transport".to_string(),
            "atomic state transition".to_string(),
        ],
        notes: vec![
            "This A/B chooses the placement only; it is not an additive integrated-CU total."
                .to_string(),
            "The in-batch row hashes one 448-byte leaf/tree; the separate row hashes 64-byte h1 and 384-byte mask leaves under two trees."
                .to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct PaymentHidingAggregatePhaseRow {
    pub phase: &'static str,
    pub phase_ordinal: u8,
    pub expected_sink_hex: String,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
}

#[derive(Serialize)]
pub struct PaymentHidingAggregateRelationSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub repetitions: usize,
    pub host_sink_matched: bool,
    pub sbf_sink_matched: bool,
    pub phases: Vec<PaymentHidingAggregatePhaseRow>,
    pub simulation_cu_mean: f64,
    pub overlap_subtracted_phase_total_cu: i64,
    pub full_minus_overlap_subtracted_cu: i64,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

pub fn run_stage2_payment_hiding_aggregate_v4() -> Result<PaymentHidingAggregateRelationSummary> {
    const REPETITIONS: usize = 5;
    const INSTRUCTION_WIRE_ORDINAL: u8 = 33;
    let phases = [
        (
            0u8,
            "empty_control",
            aspis_core::statement_hiding::PaymentHidingAggregatePhase::EmptyControl,
        ),
        (
            1u8,
            "relation",
            aspis_core::statement_hiding::PaymentHidingAggregatePhase::Relation,
        ),
        (
            2u8,
            "layer0",
            aspis_core::statement_hiding::PaymentHidingAggregatePhase::Layer0,
        ),
        (
            3u8,
            "later_folds",
            aspis_core::statement_hiding::PaymentHidingAggregatePhase::LaterFolds,
        ),
        (
            4u8,
            "later_merkle",
            aspis_core::statement_hiding::PaymentHidingAggregatePhase::LaterMerkle,
        ),
        (
            5u8,
            "full",
            aspis_core::statement_hiding::PaymentHidingAggregatePhase::Full,
        ),
    ];
    let mut host_rows = Vec::new();
    for (ordinal, name, phase) in phases {
        let sink = aspis_core::statement_hiding::payment_hiding_aggregate_relation_probe_phase(
            HOST_HASH, phase,
        )
        .map_err(|_| anyhow!("host hiding aggregate phase {name} exhausted a challenge"))?;
        let mut expected_sink = [0u8; 16];
        sink.write_le_bytes(&mut expected_sink);
        host_rows.push((ordinal, name, expected_sink));
    }
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let mut phase_rows = Vec::new();
    for (ordinal, name, expected_sink) in host_rows {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::MeasurePaymentHidingAggregateRelationV4 {
                phase: ordinal,
                expected_sink,
            })?,
        };
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        phase_rows.push(PaymentHidingAggregatePhaseRow {
            phase: name,
            phase_ordinal: ordinal,
            expected_sink_hex: expected_sink
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect(),
            simulation_cu,
            simulation_cu_mean,
        });
    }
    let empty = phase_rows[0].simulation_cu_mean;
    let full = phase_rows[5].simulation_cu_mean;
    let overlap_subtracted = empty
        + phase_rows[1..5]
            .iter()
            .map(|row| row.simulation_cu_mean - empty)
            .sum::<f64>();
    Ok(PaymentHidingAggregateRelationSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-payment-hiding-aggregate-v4"
            .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: INSTRUCTION_WIRE_ORDINAL,
        repetitions: REPETITIONS,
        host_sink_matched: true,
        sbf_sink_matched: true,
        phases: phase_rows,
        simulation_cu_mean: full,
        overlap_subtracted_phase_total_cu: overlap_subtracted.round() as i64,
        full_minus_overlap_subtracted_cu: (full - overlap_subtracted).round() as i64,
        included_work: vec![
            "one mask-aggregate MLE/OOD/four-round relation accumulator".to_string(),
            "six-column H_z layer-zero aggregation at q36".to_string(),
            "four prepared arity-4 fold layers and final tensor evaluations".to_string(),
            "three later-layer q36 radix-4 authentication shapes".to_string(),
            "relation transcript hashing".to_string(),
        ],
        excluded_work: vec![
            "mask layer-zero tree already priced by the placement object".to_string(),
            "main payment PCS and terminal".to_string(),
            "proof parser/account transport".to_string(),
            "atomic state transition".to_string(),
        ],
        notes: vec![
            "This synthetic verifier-operation object is common to both mask placements; it is not yet an accepting proof parser."
                .to_string(),
            "Phase components subtract the repeated empty/setup control. The full row remains the authoritative object; the residual is reported explicitly."
                .to_string(),
            "Only an overlap-subtracted same-instruction integration may combine this with the main proof."
                .to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct PaymentHidingProfile15Phase {
    pub label: String,
    pub phase: String,
    pub start: u16,
    pub end: u16,
    pub simulation_cu: Vec<u64>,
    pub simulation_errors: Vec<Option<String>>,
    pub selected_cu: Option<u64>,
    pub markers: Vec<CuMarker>,
}

#[derive(Serialize)]
pub struct PaymentHidingProfile15Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub profile_id: u8,
    pub rho: String,
    pub query_count: u16,
    pub grinding_bits: u8,
    pub fold_pow_bits: [u8; 4],
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_path: String,
    pub fixture_pow_valid: bool,
    pub upload_chunks: usize,
    pub unique_layer0_queries: usize,
    pub phases: Vec<PaymentHidingProfile15Phase>,
    pub overlap_subtracted_integrated_cu: i64,
    pub full_measured_cu: Option<u64>,
    pub full_minus_reconciled_cu: Option<i64>,
    pub headroom_under_1_4m: i64,
    pub stale_statement_rejected: bool,
    pub changed_public_rejected: bool,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

pub fn run_stage2_payment_hiding_profile15() -> Result<PaymentHidingProfile15Summary> {
    use aspis_core::circle_hiding_prefix::{
        PAYMENT_HIDING_GRINDING_BITS, PAYMENT_HIDING_PROFILE_ID, PAYMENT_HIDING_QUERY_COUNT,
    };
    use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
    use aspis_core::field::{CM31, M31, P, QM31};
    use aspis_prover::payment_hiding_candidate_prefix::{
        build_payment_hiding_proof, PaymentHidingPowMode,
    };
    use aspis_statement::{
        apply_direct_range_c1_masks_v4, apply_direct_range_witness_v4, build_spend_trace_v4,
        derive_nullifier, derive_owner_key, direct_range_c1_mask_cells_v4, merkle_root,
        note_commitment, output_commitment, Digest, MerklePath, SpendPublic, SpendWitness,
        COPY_HELPER_MASK_VARIABLES, PAYMENT_MASK_ORACLE_VALUES,
    };
    use sha2::{Digest as _, Sha256};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }
    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed), M31(seed + 1)),
            c1: CM31::new(M31(seed + 2), M31(seed + 3)),
        }
    }
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let owner_key = derive_owner_key(&nullifier_key);
    let note = note_commitment(&owner_key, value, asset_id, &input_salt);
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
        index: 0x5_4321,
    };
    let public = SpendPublic {
        anchor: merkle_root(note, &merkle_path)
            .map_err(|error| anyhow!("profile-15 Merkle fixture: {error:?}"))?,
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output_commitment(&output_owner_key, value_out, asset_id, &output_salt),
        asset_id,
        fee: 1,
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
    let mut trace = build_spend_trace_v4(&public, &witness)
        .map_err(|error| anyhow!("profile-15 spend trace: {error:?}"))?;
    apply_direct_range_witness_v4(&mut trace)
        .map_err(|error| anyhow!("profile-15 direct range witness: {error:?}"))?;
    let c1_masks = (0..direct_range_c1_mask_cells_v4().len())
        .map(|index| M31(((index as u64 * 2_246_822_519 + 0x5a17) % u64::from(P)) as u32))
        .collect::<Vec<_>>();
    apply_direct_range_c1_masks_v4(&mut trace, &c1_masks)
        .map_err(|error| anyhow!("profile-15 C1 masks: {error:?}"))?;
    let helper_masks = (0..COPY_HELPER_MASK_VARIABLES)
        .map(|index| q(11 + index as u32 * 29))
        .collect::<Vec<_>>();
    let payment_mask = (0..PAYMENT_MASK_ORACLE_VALUES)
        .map(|row| q(101 + row as u32 * 31))
        .collect::<Vec<_>>();
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/payment-hiding/profile15/depth20/v1").into();
    let built = build_payment_hiding_proof(
        &public,
        &trace,
        &helper_masks,
        &payment_mask,
        statement_digest,
        HOST_HASH,
        PaymentHidingPowMode::UnminedZero,
    )
    .map_err(|error| anyhow!("build profile-15 hiding proof: {error:?}"))?;
    ensure!(
        !built.pow_valid,
        "unmined profile-15 fixture unexpectedly met every PoW target"
    );
    aspis_core::circle_hiding_verify::verify_payment_hiding_candidate_unmined_for_diagnostics(
        &built.bytes,
        &statement_digest,
        HOST_HASH,
        aspis_core::circle_openings::CircleQuerySegment::Full,
    )
    .map_err(|error| anyhow!("host profile-15 diagnostic verifier: {error:?}"))?;
    let proof_sha256 = Sha256::digest(&built.bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let root = workspace_root()?;
    let proof_path = root.join("results/stage2/proofs/payment_hiding_profile15_unmined.bin");
    if let Some(parent) = proof_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&proof_path, &built.bytes)?;
    let indices = derive_circle_line_query_indices_for_count(&built.schedule.queries, 1 << 12)
        .map_err(|error| anyhow!("profile-15 query indices: {error:?}"))?;
    let unique = indices.layer0.len();
    let cuts = [0usize, unique / 4, unique / 2, 3 * unique / 4, unique];

    let mut public_input = [0u8; 104];
    for (index, value) in public
        .anchor
        .iter()
        .chain(&public.nullifier)
        .chain(&public.output_commitment)
        .chain(core::iter::once(&public.asset_id))
        .enumerate()
    {
        public_input[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    public_input[100..104].copy_from_slice(&public.fee.to_le_bytes());

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &built.bytes, true)?;

    let simulate = |digest: [u8; 32],
                    public_input: [u8; 104],
                    phase: JohnsonM31CircleDiagnosticPhase,
                    start: u16,
                    end: u16|
     -> Result<SimulationResult> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::MeasurePaymentHidingProfile15 {
                statement_digest: digest,
                public_input,
                phase,
                start,
                end,
            })?,
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        rpc.simulate_verbose(&transaction)
    };
    let phase_specs = [
        (
            "prepared_base",
            JohnsonM31CircleDiagnosticPhase::PreparedBase,
            0u16,
            0u16,
        ),
        (
            "layer0_quarter_0",
            JohnsonM31CircleDiagnosticPhase::Layer0Range,
            0u16,
            cuts[1] as u16,
        ),
        (
            "layer0_quarter_1",
            JohnsonM31CircleDiagnosticPhase::Layer0Range,
            cuts[1] as u16,
            cuts[2] as u16,
        ),
        (
            "layer0_quarter_2",
            JohnsonM31CircleDiagnosticPhase::Layer0Range,
            cuts[2] as u16,
            cuts[3] as u16,
        ),
        (
            "layer0_quarter_3",
            JohnsonM31CircleDiagnosticPhase::Layer0Range,
            cuts[3] as u16,
            cuts[4] as u16,
        ),
        (
            "later_all",
            JohnsonM31CircleDiagnosticPhase::LaterAll,
            0u16,
            0u16,
        ),
        ("full", JohnsonM31CircleDiagnosticPhase::Full, 0u16, 0u16),
    ];
    let mut phases = Vec::new();
    for (label, phase, start, end) in phase_specs {
        let mut simulation_cu = Vec::new();
        let mut simulation_errors = Vec::new();
        let mut markers = Vec::new();
        for repetition in 0..VERIFY_REPETITIONS {
            let result = simulate(statement_digest, public_input, phase, start, end)?;
            if repetition == 0 {
                markers = parse_cu_markers(&result.logs, "aspis-cu:");
            }
            simulation_cu.push(result.units.unwrap_or(VERIFY_CU_LIMIT as u64));
            simulation_errors.push(result.err.map(|error| format!("{error:?}")));
        }
        let accepted = simulation_errors.iter().all(Option::is_none);
        let selected_cu =
            accepted.then(|| simulation_cu.iter().sum::<u64>() / simulation_cu.len() as u64);
        phases.push(PaymentHidingProfile15Phase {
            label: label.to_string(),
            phase: format!("{phase:?}"),
            start,
            end,
            simulation_cu,
            simulation_errors,
            selected_cu,
            markers,
        });
    }
    for phase in &phases[..6] {
        ensure!(
            phase.selected_cu.is_some(),
            "profile-15 phase {} exceeded/rejected",
            phase.label
        );
    }
    let base = phases[0].selected_cu.unwrap() as i64;
    let reconciled = base
        + phases[1..6]
            .iter()
            .map(|phase| phase.selected_cu.unwrap() as i64 - base)
            .sum::<i64>();
    let full_measured_cu = phases[6].selected_cu;
    let full_minus_reconciled_cu = full_measured_cu.map(|full| full as i64 - reconciled);

    let mut stale_digest = statement_digest;
    stale_digest[0] ^= 1;
    let stale_statement_rejected = simulate(
        stale_digest,
        public_input,
        JohnsonM31CircleDiagnosticPhase::PreparedBase,
        0,
        0,
    )?
    .err
    .is_some();
    let mut changed_public = public_input;
    changed_public[100] ^= 1;
    let changed_public_rejected = simulate(
        statement_digest,
        changed_public,
        JohnsonM31CircleDiagnosticPhase::PreparedBase,
        0,
        0,
    )?
    .err
    .is_some();

    Ok(PaymentHidingProfile15Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-payment-hiding-profile15"
            .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 34,
        profile_id: PAYMENT_HIDING_PROFILE_ID,
        rho: "1/16".to_string(),
        query_count: PAYMENT_HIDING_QUERY_COUNT,
        grinding_bits: PAYMENT_HIDING_GRINDING_BITS,
        fold_pow_bits: aspis_core::circle_prefix::RATE16_HARDENED_FOLD_POW_BITS,
        proof_bytes: built.bytes.len(),
        proof_sha256,
        proof_path: proof_path.strip_prefix(&root).unwrap_or(&proof_path).display().to_string(),
        fixture_pow_valid: built.pow_valid,
        upload_chunks,
        unique_layer0_queries: unique,
        phases,
        overlap_subtracted_integrated_cu: reconciled,
        full_measured_cu,
        full_minus_reconciled_cu,
        headroom_under_1_4m: i64::from(VERIFY_CU_LIMIT) - reconciled,
        stale_statement_rejected,
        changed_public_rejected,
        included_work: vec![
            "profile-15 parser and full hiding Fiat-Shamir schedule".to_string(),
            "masked ten-round degree-10 payment zerocheck transcript".to_string(),
            "standard gamma RLC over 49 C1 + h1 + one payment-mask rate-1/16 PCS relation".to_string(),
            "both layer-zero Merkle trees, three later trees, and q36 folds".to_string(),
            "direct-range payment terminal and masked-terminal equality".to_string(),
        ],
        excluded_work: vec![
            "PoW search is prover work; the diagnostic executes all five verifier hash checks and skips only rejection for its zero nonce records; mined-nonce query geometry must still be measured before the final fit claim".to_string(),
            "atomic account mutation/nullifier insertion is not yet in this measurement tag".to_string(),
            "formal HVZK and Johnson circle-transport lemmas remain separate proof obligations".to_string(),
        ],
        notes: vec![
            "The integrated total is base + four disjoint layer0-quarter increments + the later-layer increment; repeated parser/transcript/relation/Merkle/statement work is retained once.".to_string(),
            "The full row, when it fits, is the authoritative same-instruction measurement and should agree with the overlap-subtracted reconstruction.".to_string(),
            "This instruction is measurement-only and cannot authorize state because its PoW predicates are disabled by construction.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct StateOnlyWidth28PhaseRow {
    pub phase: String,
    pub simulation_cu: Option<u64>,
    pub simulation_error: Option<String>,
    pub markers: Vec<CuMarker>,
}

#[derive(Serialize)]
pub struct StateOnlyWidth28Ledger {
    pub transaction_setup_cu: u64,
    pub proof_load_cu: u64,
    pub parse_cu: u64,
    pub transcript_cu: u64,
    pub terminal_cu: u64,
    pub relation_including_reusable_query_powers_cu: u64,
    pub merkle_openings_cu: u64,
    pub query_arithmetic_cu: u64,
    pub verifier_return_cu: u64,
    pub post_last_marker_cu: u64,
    pub segmented_queries_duplicate_power_setup_cu: u64,
    pub query_shared_setup_cu: u64,
    pub query_layer0_only_cu: u64,
    pub query_later_all_only_cu: u64,
    pub query_segment_reconciliation: String,
    pub overlap_reconciled_total_cu: u64,
    pub headroom_under_1_4m_cu: i64,
    pub formula: String,
    pub reuse_explanation: String,
}

#[derive(Serialize)]
pub struct StateOnlyWidth28Row {
    pub profile_id: u8,
    pub rho: String,
    pub query_count: u16,
    pub proof_bytes: usize,
    pub prefix_bytes: usize,
    pub suffix_bytes: usize,
    pub proof_sha256: String,
    pub proof_path: String,
    pub fixture_pow_valid: bool,
    pub upload_chunks: usize,
    pub simulation_cu: Option<u64>,
    pub simulation_error: Option<String>,
    pub markers: Vec<CuMarker>,
    pub pre_first_marker_cu: Option<u64>,
    pub marker_span_cu: Option<u64>,
    pub post_last_marker_cu: Option<u64>,
    pub marker_reconciled_cu: Option<u64>,
    pub simulation_minus_reconciled_cu: Option<i64>,
    pub phase_runs: Vec<StateOnlyWidth28PhaseRow>,
    pub overlap_ledger: Option<StateOnlyWidth28Ledger>,
}

#[derive(Serialize)]
pub struct StateOnlyWidth28Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub segmented_instruction_wire_ordinal: u8,
    pub label: String,
    pub c1_columns: usize,
    pub c2_columns: usize,
    pub generator_width: usize,
    pub statement_values: usize,
    pub rows: Vec<StateOnlyWidth28Row>,
    pub included_work: Vec<String>,
    pub excluded_work: Vec<String>,
    pub notes: Vec<String>,
}

pub fn run_stage2_state_only_width28() -> Result<StateOnlyWidth28Summary> {
    use aspis_core::field::M31;
    use aspis_core::state_only_prefix::{
        StateOnlyProfileShape, STATE_ONLY_PREFIX_LEN, STATE_ONLY_RATE16_SHAPE,
        STATE_ONLY_RATE32_SHAPE, STATE_ONLY_RATE512_SHAPE,
    };
    use aspis_prover::state_only_candidate_prefix::StateOnlyPowMode;
    use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
    use aspis_prover::state_only_proof::{build_hiding_state_only_proof, BuiltStateOnlyProof};
    use aspis_statement::{
        build_spend_trace_v4, derive_nullifier, derive_owner_key, merkle_root, note_commitment,
        output_commitment, project_state_only_trace_v4, Digest, MerklePath, SpendPublic,
        SpendWitness,
    };
    use sha2::{Digest as _, Sha256};

    struct MeasurementProof {
        shape: StateOnlyProfileShape,
        bytes: Vec<u8>,
        pow_valid: bool,
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn fixture() -> Result<(SpendPublic, aspis_statement::StateOnlyTraceFoundation)> {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let owner_key = derive_owner_key(&nullifier_key);
        let note = note_commitment(&owner_key, value, asset_id, &input_salt);
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
            index: 0x5_4321,
        };
        let public = SpendPublic {
            anchor: merkle_root(note, &merkle_path)
                .map_err(|error| anyhow!("state28 Merkle fixture: {error:?}"))?,
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee: 1,
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
        let trace = project_state_only_trace_v4(
            &build_spend_trace_v4(&public, &witness)
                .map_err(|error| anyhow!("state28 spend trace: {error:?}"))?,
        )
        .map_err(|error| anyhow!("state28 trace projection: {error:?}"))?;
        Ok((public, trace))
    }

    fn build(
        public: &SpendPublic,
        trace: &aspis_statement::StateOnlyTraceFoundation,
        shape: StateOnlyProfileShape,
        statement_digest: [u8; 32],
    ) -> Result<BuiltStateOnlyProof> {
        let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
        build_hiding_state_only_proof(
            public,
            trace.clone(),
            statement_digest,
            [shape.profile_id; 32],
            [0xd3; 32],
            &mut nonce_store,
            shape,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .map_err(|error| anyhow!("build state28 profile {}: {error:?}", shape.profile_id))
    }

    fn public_bytes(public: &SpendPublic) -> [u8; 104] {
        let mut output = [0u8; 104];
        for (index, value) in public
            .anchor
            .iter()
            .chain(&public.nullifier)
            .chain(&public.output_commitment)
            .chain(core::iter::once(&public.asset_id))
            .enumerate()
        {
            output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        output[100..].copy_from_slice(&public.fee.to_le_bytes());
        output
    }

    let root = workspace_root()?;
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/state-only/width28/global-copy-inactive-hiding/v1").into();
    let (public, trace) = fixture()?;
    let reuse_proofs = std::env::var_os("ASPIS_STATE28_REUSE_PROOFS").is_some();
    let built = [
        STATE_ONLY_RATE16_SHAPE,
        STATE_ONLY_RATE32_SHAPE,
        STATE_ONLY_RATE512_SHAPE,
    ]
    .into_iter()
    .map(|shape| {
        if reuse_proofs {
            let path = root.join(format!(
                "results/stage2/proofs/state_only_width28_global_inactive_p{}_unmined.bin",
                shape.profile_id
            ));
            Ok(MeasurementProof {
                shape,
                bytes: fs::read(&path)
                    .with_context(|| format!("read replay proof {}", path.display()))?,
                pow_valid: false,
            })
        } else {
            let proof = build(&public, &trace, shape, statement_digest)?;
            Ok(MeasurementProof {
                shape,
                bytes: proof.bytes,
                pow_valid: proof.pow_valid,
            })
        }
    })
    .collect::<Result<Vec<_>>>()?;

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    // Three exact proof accounts are uploaded in this diagnostic (profiles
    // 18, 19, and 20). Fund their rent independently of verifier CU.
    rpc.airdrop_and_wait(&payer.pubkey(), 3 * LAMPORTS_PER_SOL)?;
    let mut rows = Vec::new();
    for proof in built {
        let shape = proof.shape;
        let proof_path = root.join(format!(
            "results/stage2/proofs/state_only_width28_global_inactive_p{}_unmined.bin",
            shape.profile_id
        ));
        if let Some(parent) = proof_path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&proof_path, &proof.bytes)?;
        let proof_sha256 = Sha256::digest(&proof.bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let proof_account = Keypair::new();
        let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &proof.bytes, true)?;
        let mut phase_runs = Vec::new();
        for (phase_name, phase) in [
            (
                "prepared_base",
                StateOnlyWidth28DiagnosticPhase::PreparedBase,
            ),
            ("terminal", StateOnlyWidth28DiagnosticPhase::Terminal),
            ("relation", StateOnlyWidth28DiagnosticPhase::Relation),
            ("openings", StateOnlyWidth28DiagnosticPhase::Openings),
            ("queries", StateOnlyWidth28DiagnosticPhase::Queries),
            ("query_layer0", StateOnlyWidth28DiagnosticPhase::QueryLayer0),
            (
                "query_later_all",
                StateOnlyWidth28DiagnosticPhase::QueryLaterAll,
            ),
            (
                "terminal_breakdown",
                StateOnlyWidth28DiagnosticPhase::TerminalBreakdown,
            ),
            (
                "terminal_no_mask",
                StateOnlyWidth28DiagnosticPhase::TerminalNoMask,
            ),
        ] {
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
                data: to_vec(&AspisInstruction::MeasureStateOnlyWidth28 {
                    statement_digest,
                    public_input: public_bytes(&public),
                    phase,
                })?,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                    instruction,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let simulation = rpc.simulate_verbose(&transaction)?;
            phase_runs.push(StateOnlyWidth28PhaseRow {
                phase: phase_name.to_string(),
                simulation_cu: simulation.units,
                simulation_error: simulation.err.map(|error| format!("{error:?}")),
                markers: parse_cu_markers(&simulation.logs, "aspis-cu:"),
            });
        }
        let overlap_ledger = (|| {
            let run = |name: &str| phase_runs.iter().find(|run| run.phase == name);
            let delta = |phase: &str, label: &str| -> Option<u64> {
                run(phase)?
                    .markers
                    .iter()
                    .find(|marker| marker.label == label)?
                    .delta_from_previous?
                    .try_into()
                    .ok()
            };
            let base = run("prepared_base")?;
            let first_remaining = base.markers.first()?.remaining;
            let transaction_setup_cu = u64::from(VERIFY_CU_LIMIT).checked_sub(first_remaining)?;
            let proof_load_cu = delta("prepared_base", "state28_proof_loaded")?;
            let parse_cu = delta("prepared_base", "state28_parse_done")?;
            let transcript_cu = delta("prepared_base", "state28_transcript_done")?;
            let terminal_cu = delta("terminal", "state28_terminal_done")?;
            let relation_cu = delta("relation", "state28_relation_done")?;
            let merkle_openings_cu = delta("openings", "state28_openings_parse_done")?;
            let query_run_openings_cu = delta("queries", "state28_openings_parse_done")?;
            let query_arithmetic_cu = delta("queries", "state28_queries_done")?;
            let verifier_return_cu = delta("queries", "state28_done")?;
            let query_run = run("queries")?;
            let query_last_remaining = query_run.markers.last()?.remaining;
            let consumed_through_last =
                u64::from(VERIFY_CU_LIMIT).checked_sub(query_last_remaining)?;
            let post_last_marker_cu = query_run
                .simulation_cu?
                .checked_sub(consumed_through_last)?;
            let segmented_queries_duplicate_power_setup_cu =
                query_run_openings_cu.checked_sub(merkle_openings_cu)?;
            let query_layer0_including_setup_cu = delta("query_layer0", "state28_queries_done")?;
            let query_later_all_including_setup_cu =
                delta("query_later_all", "state28_queries_done")?;
            let query_shared_setup_cu = query_layer0_including_setup_cu
                .checked_add(query_later_all_including_setup_cu)?
                .checked_sub(query_arithmetic_cu)?;
            let query_layer0_only_cu =
                query_layer0_including_setup_cu.checked_sub(query_shared_setup_cu)?;
            let query_later_all_only_cu =
                query_later_all_including_setup_cu.checked_sub(query_shared_setup_cu)?;
            let buckets = [
                transaction_setup_cu,
                proof_load_cu,
                parse_cu,
                transcript_cu,
                terminal_cu,
                relation_cu,
                merkle_openings_cu,
                query_arithmetic_cu,
                verifier_return_cu,
                post_last_marker_cu,
            ];
            let overlap_reconciled_total_cu = buckets
                .iter()
                .try_fold(0u64, |sum: u64, &value| sum.checked_add(value))?;
            Some(StateOnlyWidth28Ledger {
                transaction_setup_cu,
                proof_load_cu,
                parse_cu,
                transcript_cu,
                terminal_cu,
                relation_including_reusable_query_powers_cu: relation_cu,
                merkle_openings_cu,
                query_arithmetic_cu,
                verifier_return_cu,
                post_last_marker_cu,
                segmented_queries_duplicate_power_setup_cu,
                query_shared_setup_cu,
                query_layer0_only_cu,
                query_later_all_only_cu,
                query_segment_reconciliation: format!(
                    "{} shared setup + {} layer0-only + {} later-all-only = {} full query arithmetic; the two segmented runs each include the shared setup once",
                    query_shared_setup_cu,
                    query_layer0_only_cu,
                    query_later_all_only_cu,
                    query_arithmetic_cu,
                ),
                overlap_reconciled_total_cu,
                headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT)
                    - overlap_reconciled_total_cu as i64,
                formula: buckets
                    .iter()
                    .map(u64::to_string)
                    .collect::<Vec<_>>()
                    .join(" + "),
                reuse_explanation: "The Queries diagnostic constructs StateOnlyQueryPowers::new before its openings marker. The integrated verifier instead reuses relation.query_powers, already priced inside the relation bucket, so the standalone Openings marker is the integrated Merkle bucket and the Queries-branch opening premium is reported but overlap-subtracted.".to_string(),
            })
        })();
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::VerifyStateOnlyWidth28 {
                statement_digest,
                public_input: public_bytes(&public),
                diagnostic_unmined: true,
            })?,
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let simulation = rpc.simulate_verbose(&transaction)?;
        let markers = parse_cu_markers(&simulation.logs, "aspis-cu:");
        let first_remaining = markers.first().map(|marker| marker.remaining);
        let last_remaining = markers.last().map(|marker| marker.remaining);
        let pre_first_marker_cu =
            first_remaining.and_then(|remaining| u64::from(VERIFY_CU_LIMIT).checked_sub(remaining));
        let marker_span_cu = first_remaining
            .zip(last_remaining)
            .and_then(|(first, last)| first.checked_sub(last));
        let post_last_marker_cu =
            simulation
                .units
                .zip(last_remaining)
                .and_then(|(total, remaining)| {
                    let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(remaining)?;
                    total.checked_sub(through_last)
                });
        let marker_reconciled_cu = pre_first_marker_cu
            .zip(marker_span_cu)
            .zip(post_last_marker_cu)
            .and_then(|((pre, span), post)| pre.checked_add(span)?.checked_add(post));
        let simulation_minus_reconciled_cu = simulation
            .units
            .zip(marker_reconciled_cu)
            .map(|(total, reconciled)| total as i64 - reconciled as i64);
        rows.push(StateOnlyWidth28Row {
            profile_id: shape.profile_id,
            rho: match shape.log_blowup {
                4 => "1/16",
                5 => "1/32",
                9 => "1/512",
                _ => "unsupported",
            }
            .to_string(),
            query_count: shape.query_count,
            proof_bytes: proof.bytes.len(),
            prefix_bytes: STATE_ONLY_PREFIX_LEN,
            suffix_bytes: proof.bytes.len() - STATE_ONLY_PREFIX_LEN,
            proof_sha256,
            proof_path: proof_path
                .strip_prefix(&root)
                .unwrap_or(&proof_path)
                .display()
                .to_string(),
            fixture_pow_valid: proof.pow_valid,
            upload_chunks,
            simulation_cu: simulation.units,
            simulation_error: simulation.err.map(|error| format!("{error:?}")),
            markers,
            pre_first_marker_cu,
            marker_span_cu,
            post_last_marker_cu,
            marker_reconciled_cu,
            simulation_minus_reconciled_cu,
            phase_runs,
            overlap_ledger,
        });
    }
    Ok(StateOnlyWidth28Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: if reuse_proofs {
            "NO_DNA=1 ASPIS_STATE28_REUSE_PROOFS=1 cargo run --release -p aspis-xtask -- stage2-state-only-width28"
        } else {
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-state-only-width28"
        }
        .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 39,
        segmented_instruction_wire_ordinal: 40,
        label: "global-copy-inactive-hiding".to_string(),
        c1_columns: aspis_core::state_only_query::STATE_ONLY_C1_COLUMNS,
        c2_columns: aspis_core::state_only_query::STATE_ONLY_C2_COLUMNS,
        generator_width: aspis_core::state_only_query::STATE_ONLY_TOTAL_COLUMNS,
        statement_values: aspis_core::state_only_prefix::STATE_ONLY_STATEMENT_VALUE_COUNT,
        rows,
        included_work: vec![
            "private-entropy semantic masking, ten mask-only C1 columns, and explicit G".to_string(),
            "private balanced h1 mask over all 854 copy-inactive rows, with one dense public zero claim and 853 free QM31 coordinates".to_string(),
            "complete width-28 prefix/transcript, degree-27 masked zerocheck terminal, three-point relation, all roots and queries".to_string(),
            "rate16 q36, rate32 q29, and diagnostic rate512 q16 geometries over exact serialized proof accounts".to_string(),
        ],
        excluded_work: vec![
            "only PoW acceptance predicates are bypassed; nonce absorption and all downstream Fiat-Shamir work execute".to_string(),
            "atomic nullifier/pool mutation is not included; tag39 is read-only and cannot authorize state".to_string(),
        ],
        notes: vec![
            "Proof generation is host-only prover work and excluded from SBF CU.".to_string(),
            "A simulation error at 1.4M is a measured cap failure, not an extrapolated total; phase segmentation is required to price the excess.".to_string(),
            "The marker reconciliation is pre-first-marker + first-to-last marker span + post-last-marker; it must equal the simulation total exactly whenever the instruction completes.".to_string(),
            "The frozen complete-view rank gate is q36 mask=augmented=292 and q29 mask=augmented=256; active-row registry fingerprint 0xdfba37ae14a1a2cc, factor fingerprint 0x12672251efe5eafb.".to_string(),
        ],
    })
}

/// Freehand plus evaluator-confirmed extension-field composition bracket.
pub fn run_stage2_composition_probe() -> Result<CompositionProbeSummary> {
    const REPETITIONS: usize = 5;
    const PRE_COMPOSITION_PROJECTION: i64 = 1_175_086;
    const TARGET: i64 = 1_190_000;
    const TEN_PERCENT_SLACK_MAXIMUM: i64 = 1_071_000;

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let baseline_probe = aspis_statement::CompositionProbe {
        opened_values: 1,
        poseidon_sbox_terms: 0,
        poseidon_linear_terms: 0,
        logup_degree3_terms: 0,
        range_bit_terms: 0,
        eq_variables: 0,
    };
    let baseline_cu = simulate_pure_instruction(
        &rpc,
        &payer,
        composition_instruction(baseline_probe, false)?,
        REPETITIONS,
    )?;
    let baseline_mean = baseline_cu.iter().sum::<u64>() as f64 / baseline_cu.len() as f64;
    let k64_rlc_probe = aspis_statement::CompositionProbe {
        opened_values: 64,
        ..baseline_probe
    };
    let frozen_k64_rlc_only_cu = simulate_pure_instruction(
        &rpc,
        &payer,
        composition_instruction(k64_rlc_probe, false)?,
        REPETITIONS,
    )?;
    let frozen_k64_rlc_mean =
        frozen_k64_rlc_only_cu.iter().sum::<u64>() as f64 / frozen_k64_rlc_only_cu.len() as f64;

    let profiles = [
        (
            "freehand_optimistic",
            aspis_statement::CompositionProbe::OPTIMISTIC,
            false,
        ),
        (
            "evaluator_confirmed_low",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                poseidon_linear_terms: 64,
                logup_degree3_terms: 1,
                range_bit_terms: 64,
                eq_variables: 10,
            },
            false,
        ),
        (
            "evaluator_confirmed_low_optimized",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                poseidon_linear_terms: 64,
                logup_degree3_terms: 1,
                range_bit_terms: 64,
                eq_variables: 10,
            },
            true,
        ),
        (
            "evaluator_low_lookup_range_optimized",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                // Six 10-bit limbs reconstruct the two bounded values.
                poseidon_linear_terms: 70,
                // Wiring LogUp plus a 10-bit fixed-table range LogUp.
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "evaluator_lookup_range_stress_linear128",
            aspis_statement::CompositionProbe {
                opened_values: 80,
                poseidon_sbox_terms: 64,
                // Stress row: the lookup candidate at the top of the
                // evaluator's per-row linear bracket [64, 128], instead of
                // the 70 terms the shared-output layout assumes.
                poseidon_linear_terms: 128,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r3_lookup_range_optimized",
            aspis_statement::CompositionProbe {
                // 3 Poseidon2 rounds per row: 48 S-box outputs, 48 + 6
                // reconstruction linear terms, 67 opened columns
                // (64 main + multiplicity + two helpers open at the row,
                // matching the r=3 layout candidate's k').
                opened_values: 67,
                poseidon_sbox_terms: 48,
                poseidon_linear_terms: 54,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r3_lookup_range_stress_linear102",
            aspis_statement::CompositionProbe {
                // r=3 bracket top: 3/4 of the r=4 [64,128] bracket plus the
                // six reconstruction terms.
                opened_values: 67,
                poseidon_sbox_terms: 48,
                poseidon_linear_terms: 102,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r2_lookup_range_optimized",
            aspis_statement::CompositionProbe {
                // 2 Poseidon2 rounds per row (the sweep floor: r=1 exceeds
                // the 2^10 row cap): 32 S-box outputs, 32 + 6 linear terms,
                // k' = 51 opened columns.
                opened_values: 51,
                poseidon_sbox_terms: 32,
                poseidon_linear_terms: 38,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "r2_lookup_range_stress_linear70",
            aspis_statement::CompositionProbe {
                // r=2 bracket top: 2/4 of the r=4 [64,128] bracket plus the
                // six reconstruction terms.
                opened_values: 51,
                poseidon_sbox_terms: 32,
                poseidon_linear_terms: 70,
                logup_degree3_terms: 2,
                range_bit_terms: 0,
                eq_variables: 10,
            },
            true,
        ),
        (
            "realistic",
            aspis_statement::CompositionProbe::REALISTIC,
            false,
        ),
        (
            "realistic_optimized",
            aspis_statement::CompositionProbe::REALISTIC,
            true,
        ),
        (
            "pessimistic",
            aspis_statement::CompositionProbe::PESSIMISTIC,
            false,
        ),
    ];
    let mut variants = Vec::new();
    for (name, probe, optimized) in profiles {
        let host = if optimized {
            aspis_statement::evaluate_composition_probe_optimized(probe)
        } else {
            aspis_statement::evaluate_composition_probe(probe)
        };
        let simulation_cu = simulate_pure_instruction(
            &rpc,
            &payer,
            composition_instruction(probe, optimized)?,
            REPETITIONS,
        )?;
        let mean = simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        let matching_rlc_probe = aspis_statement::CompositionProbe {
            opened_values: probe.opened_values,
            ..baseline_probe
        };
        let matching_rlc_only_cu = simulate_pure_instruction(
            &rpc,
            &payer,
            composition_instruction(matching_rlc_probe, optimized)?,
            REPETITIONS,
        )?;
        let matching_rlc_mean =
            matching_rlc_only_cu.iter().sum::<u64>() as f64 / matching_rlc_only_cu.len() as f64;
        let composition_incremental = (mean - matching_rlc_mean).round() as i64;
        let rlc_delta = (matching_rlc_mean - frozen_k64_rlc_mean).round() as i64;
        let projected = PRE_COMPOSITION_PROJECTION + rlc_delta + composition_incremental;
        variants.push(CompositionProbeVariant {
            name,
            kernel: if optimized {
                "structured_horner"
            } else {
                "naive"
            },
            parameters: probe.into(),
            host_qm31_multiplications: host.qm31_multiplications,
            host_qm31_by_cm31_multiplications: host.qm31_by_cm31_multiplications,
            host_additions_or_subtractions: host.additions_or_subtractions,
            simulation_cu,
            simulation_cu_mean: mean,
            matching_rlc_only_cu,
            matching_rlc_only_cu_mean: matching_rlc_mean,
            composition_incremental_cu_over_matching_rlc: composition_incremental,
            rlc_delta_from_frozen_k64_cu: rlc_delta,
            projected_total_cu: projected,
            headroom_vs_1_19m_cu: TARGET - projected,
            meets_10_percent_slack: projected <= TEN_PERCENT_SLACK_MAXIMUM,
        });
    }

    Ok(CompositionProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-composition-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        baseline_cu,
        baseline_cu_mean: baseline_mean,
        frozen_k64_rlc_only_cu,
        frozen_k64_rlc_only_cu_mean: frozen_k64_rlc_mean,
        pre_composition_projection_cu: PRE_COMPOSITION_PROJECTION,
        transaction_target_cu: TARGET,
        ten_percent_slack_maximum_cu: TEN_PERCENT_SLACK_MAXIMUM,
        variants,
        notes: vec![
            "Synthetic bracket only: runtime term counts are explicit and must be replaced/confirmed by the evaluator-derived layout.".to_string(),
            "Composition deltas subtract a matching RLC-only run so the gamma RLC already represented in the frozen 201,114-CU layout allowance is not double-counted. Projected totals add the measured k64-to-k' RLC delta and composition-only delta to 1,175,086 CU.".to_string(),
            "Wide-leaf hashing for k'=80 is not updated by this arithmetic-only probe; it is measured separately before a final product decision.".to_string(),
            "The lookup-range candidate replaces 64 Boolean terms with six 10-bit limbs, one additional LogUp relation, and six reconstruction terms. It is an isolated cost candidate, not yet a frozen statement rule.".to_string(),
            "The stress row prices the lookup candidate at linear_terms=128, the top of the evaluator's per-row bracket. If only the 70-term reading fits the slack ceiling, candidate-green is bracket-conditional and the gate note must say so.".to_string(),
            "The 10% slack maximum is 1,071,000 CU. The frozen pre-composition projection already exceeds it by 104,086 CU, so no positive composition result can pass that gate without a named reclaim or rule change.".to_string(),
        ],
    })
}

/// Re-probe the frozen synthetic wide-leaf + gamma-RLC loop at the
/// evaluator's real candidate k'=80, with k64 retained as the exact baseline.
pub fn run_stage2_layout_probe() -> Result<Stage2LayoutSummary> {
    const LOG_ROWS: u8 = 10;
    const QUERY_COUNT: u16 = 36;
    const REPETITIONS: usize = 5;

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 10 * LAMPORTS_PER_SOL)?;
    let probe_account = Keypair::new();
    create_program_account(&rpc, &payer, &probe_account, PROOF_ACCOUNT_HEADER_LEN)?;

    let mut raw = Vec::new();
    // 51/67 = r=2 and r=3 layout candidate widths, 84 = the k' <= 84 pin.
    for columns in [51u16, 64, 67, 80, 82, 84] {
        let leaf_bytes = columns * 4;
        let instruction = AspisInstruction::LayoutProbe {
            log_rows: LOG_ROWS,
            columns,
            query_count: QUERY_COUNT,
            leaf_bytes,
        };
        let ix = proof_instruction(&payer.pubkey(), &probe_account.pubkey(), &instruction)?;
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ix,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let mut units = Vec::with_capacity(REPETITIONS);
        for _ in 0..REPETITIONS {
            let (run_units, error) = rpc.simulate(&transaction)?;
            anyhow::ensure!(error.is_none(), "stage2 layout probe failed: {error:?}");
            units.push(run_units.context("stage2 layout probe did not report units")?);
        }
        let mean = units.iter().sum::<u64>() as f64 / units.len() as f64;
        let diagnostic = rpc.simulate_verbose(&transaction)?;
        anyhow::ensure!(
            diagnostic.err.is_none(),
            "stage2 layout diagnostic failed: {:?}",
            diagnostic.err
        );
        let markers = parse_cu_markers(&diagnostic.logs, "aspis-layout:");
        raw.push((columns, leaf_bytes, units, mean, markers));
    }
    let baseline = raw[0].3;
    let variants = raw
        .into_iter()
        .map(
            |(columns, leaf_bytes, simulation_cu, simulation_cu_mean, diagnostic_markers)| {
                let marker_delta = |label: &str| {
                    diagnostic_markers
                        .iter()
                        .find(|marker| marker.label == label)
                        .and_then(|marker| marker.delta_from_previous)
                };
                Stage2LayoutVariant {
                    columns,
                    leaf_bytes,
                    simulation_cu,
                    simulation_cu_mean,
                    delta_vs_k64_cu: (simulation_cu_mean - baseline).round() as i64,
                    wide_leaf_hash_cu: marker_delta("leaf_hash_done"),
                    synthetic_merkle_cu: marker_delta("merkle_done"),
                    obsolete_same_gamma_rlc_cu: marker_delta("rlc_done"),
                    diagnostic_markers,
                }
            },
        )
        .collect();

    Ok(Stage2LayoutSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-layout-probe".to_string(),
        validator_version: validator_version(),
        log_rows: LOG_ROWS,
        query_count: QUERY_COUNT,
        repetitions: REPETITIONS,
        variants,
        notes: vec![
            "The leaf-hash and synthetic path markers remain useful for k80/q36 geometry. The historical RLC marker is explicitly obsolete because that loop multiplies every column by the same gamma rather than gamma powers.".to_string(),
            "Use results/stage2/wide_rlc_probe.json for the correct q-by-k RLC; lazy_dot4 is the measured winner. Do not quote the old k80-minus-k64 total as an RLC projection.".to_string(),
            "This is still not an integrated wide-row PCS measurement.".to_string(),
        ],
    })
}

/// Measure the pinned software Poseidon2-M31 permutation directly on SBF.
pub fn run_stage2_poseidon2_probe() -> Result<Poseidon2ProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for (implementation, optimized) in [("canonical", false), ("lazy_m31", true)] {
        for permutations in [0u16, 1, 8, 20, 40, 49, 73] {
            let probe = if optimized {
                AspisInstruction::Poseidon2OptimizedProbe { permutations }
            } else {
                AspisInstruction::Poseidon2Probe { permutations }
            };
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&probe)?,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    instruction,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let mut simulation_cu = Vec::new();
            let mut simulation_errors = Vec::new();
            for _ in 0..REPETITIONS {
                let (units, error) = rpc.simulate(&transaction)?;
                simulation_cu.push(units);
                simulation_errors.push(error);
            }
            let accepted_all = simulation_errors.iter().all(Option::is_none);
            let mean = if accepted_all {
                Some(
                    simulation_cu.iter().flatten().sum::<u64>() as f64 / simulation_cu.len() as f64,
                )
            } else {
                None
            };
            variants.push(Poseidon2ProbeVariant {
                implementation,
                permutations,
                simulation_cu,
                simulation_errors,
                accepted_all,
                mean_cu_if_accepted: mean,
                incremental_cu_over_zero_if_accepted: None,
            });
        }
    }
    for implementation in ["canonical", "lazy_m31"] {
        let zero = variants
            .iter()
            .find(|variant| variant.implementation == implementation && variant.permutations == 0)
            .and_then(|variant| variant.mean_cu_if_accepted);
        for variant in variants
            .iter_mut()
            .filter(|variant| variant.implementation == implementation)
        {
            variant.incremental_cu_over_zero_if_accepted = match (variant.mean_cu_if_accepted, zero)
            {
                (Some(mean), Some(zero)) => Some((mean - zero).round() as i64),
                _ => None,
            };
        }
    }
    let per_permutation = variants
        .iter()
        .find(|variant| variant.implementation == "lazy_m31" && variant.permutations == 8)
        .and_then(|variant| variant.incremental_cu_over_zero_if_accepted)
        .map(|delta| delta as f64 / 8.0);

    Ok(Poseidon2ProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-poseidon2-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        variants,
        measured_incremental_cu_per_permutation_from_8: per_permutation,
        notes: vec![
            "Canonical and lazy-M31 software Poseidon2 width-16 permutations use the exact p3-mersenne-31 0.6.1 constants; differential tests require identical outputs.".to_string(),
            "The lazy-M31 candidate reduces each linear-layer output once and replaces partial-round power-of-two multiplications with shifts. It is the first measured solmath-zk kernel candidate.".to_string(),
            "20 and 40 permutations price the v3 one-per-level node compression and the retired two-per-level sponge walk exactly. 49 is the current depth-20 SpendV0 evaluator schedule; 73 is the depth-32 sensitivity. A capped run is recorded as a failure, not extrapolated into an accepted measurement.".to_string(),
            "This is deposit/direct-evaluator cost evidence, not proof-verifier constraint-composition cost.".to_string(),
        ],
    })
}

/// Measure small reusable field kernels before they become a standalone
/// `solmath-zk` API. Every point subtracts a zero-iteration instruction with
/// the same enum variant and dispatch path.
pub fn run_stage2_zk_kernel_probe() -> Result<ZkKernelProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let kernels = [
        ("m31_inverse_software", ZkKernelKind::M31InverseSoftware, 32),
        ("m31_inverse_syscall", ZkKernelKind::M31InverseSyscall, 32),
        ("qm31_square_generic", ZkKernelKind::Qm31SquareGeneric, 512),
        (
            "qm31_square_specialized",
            ZkKernelKind::Qm31SquareSpecialized,
            512,
        ),
        ("m31_pow2_generic", ZkKernelKind::M31Pow2Generic, 4_096),
        ("m31_pow2_shift", ZkKernelKind::M31Pow2Shift, 4_096),
        ("sha256_append_chain", ZkKernelKind::Sha256AppendChain, 256),
    ];
    let mut variants = Vec::new();
    for (kernel, kind, iterations) in kernels {
        let mut means = Vec::new();
        let mut samples_by_count = Vec::new();
        for count in [0, iterations] {
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&AspisInstruction::ZkKernelProbe {
                    kind,
                    iterations: count,
                })?,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    instruction,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let mut samples = Vec::new();
            for _ in 0..REPETITIONS {
                let (units, error) = rpc.simulate(&transaction)?;
                anyhow::ensure!(error.is_none(), "{kernel} probe failed: {error:?}");
                samples.push(units.ok_or_else(|| anyhow!("no unitsConsumed for {kernel}"))?);
            }
            means.push(samples.iter().sum::<u64>() as f64 / samples.len() as f64);
            samples_by_count.push(samples);
        }
        let delta = (means[1] - means[0]).round() as i64;
        variants.push(ZkKernelProbeVariant {
            kernel,
            iterations,
            simulation_cu: samples_by_count.pop().unwrap(),
            simulation_cu_mean: means[1],
            incremental_cu_over_zero: delta,
            incremental_cu_per_iteration: delta as f64 / iterations as f64,
        });
    }

    let profile = &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32;
    let digest = crate::host_statement_digest(0);
    let proof_path = root.join("results/stage1/proofs/capacity_lr10_q36_g32_v3_c2.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read frozen proof {}", proof_path.display()))?;
    anyhow::ensure!(
        aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
        "frozen Stage 1 proof no longer verifies on host"
    );
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let measure_verifier = |mode: u8| -> Result<Vec<u64>> {
        let instruction = if mode == 2 {
            AspisInstruction::VerifySyscallInverse {
                statement_digest: digest,
            }
        } else if mode == 1 {
            AspisInstruction::VerifyFast {
                statement_digest: digest,
            }
        } else {
            AspisInstruction::VerifyLegacySoftware {
                statement_digest: digest,
            }
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let mut samples = Vec::new();
        for _ in 0..REPETITIONS {
            let (units, error) = rpc.simulate(&transaction)?;
            anyhow::ensure!(error.is_none(), "full verifier probe failed: {error:?}");
            samples.push(units.context("full verifier probe did not report units")?);
        }
        Ok(samples)
    };
    let software_inverse_cu = measure_verifier(0)?;
    let syscall_inverse_cu = measure_verifier(2)?;
    let circle_conjugate_cu = measure_verifier(1)?;
    let software_inverse_cu_mean =
        software_inverse_cu.iter().sum::<u64>() as f64 / software_inverse_cu.len() as f64;
    let syscall_inverse_cu_mean =
        syscall_inverse_cu.iter().sum::<u64>() as f64 / syscall_inverse_cu.len() as f64;
    let circle_conjugate_cu_mean =
        circle_conjugate_cu.iter().sum::<u64>() as f64 / circle_conjugate_cu.len() as f64;

    let profile_instruction = AspisInstruction::VerifyProfile {
        statement_digest: digest,
    };
    let blockhash = rpc.latest_blockhash()?;
    let profile_transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            proof_instruction(
                &payer.pubkey(),
                &proof_account.pubkey(),
                &profile_instruction,
            )?,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let diagnostic_profile = rpc.simulate_verbose(&profile_transaction)?;
    anyhow::ensure!(
        diagnostic_profile.err.is_none(),
        "diagnostic full verifier probe failed: {:?}",
        diagnostic_profile.err
    );
    let full_pcs_verifier = FullPcsVerifierComparison {
        profile: profile.name,
        proof_bytes: proof.len(),
        software_inverse_cu,
        software_inverse_cu_mean,
        syscall_inverse_cu,
        syscall_inverse_cu_mean,
        syscall_savings_cu: (software_inverse_cu_mean - syscall_inverse_cu_mean).round() as i64,
        circle_conjugate_cu,
        circle_conjugate_cu_mean,
        circle_conjugate_savings_vs_software_cu: (software_inverse_cu_mean
            - circle_conjugate_cu_mean)
            .round() as i64,
        diagnostic_profile_cu: diagnostic_profile.units,
        diagnostic_profile_markers: parse_cu_markers(&diagnostic_profile.logs, "aspis-cu:"),
    };

    Ok(ZkKernelProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-zk-kernel-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        variants,
        full_pcs_verifier,
        notes: vec![
            "Candidate reusable solmath-zk kernels measured on Agave SBF; these are instruction-level deltas, not host timings.".to_string(),
            "The M31 syscall inversion uses sol_big_mod_exp with stack-backed four-byte base/exponent/modulus/output and no Vec allocation on SBF.".to_string(),
            "Specialized QM31 squaring uses seven M31 products versus nine for generic multiplication; power-of-two multiplication uses a shift plus Mersenne reduction.".to_string(),
        ],
    })
}

/// Measure the actual q-by-k gamma RLC shape for wide base-field columns.
pub fn run_stage2_wide_rlc_probe() -> Result<WideRlcProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let kernels = [
        ("precomputed_powers", 0u8),
        ("lazy_dot4", 1u8),
        ("per_query_horner", 2u8),
        ("packed4_lazy_dot", 3u8),
        ("packed4_naive", 4u8),
        ("packed2_lazy_dot", 5u8),
        ("raw_u128_dot", 6u8),
        ("lazy_dot4_outer_lazy", 7u8),
        ("fixed80_outer_lazy", 8u8),
        ("fixed84_outer_lazy", 9u8),
        ("fixed67_outer_lazy", 10u8),
        ("fixed65_outer_lazy", 11u8),
        ("fixed51_outer_lazy", 12u8),
        ("fixed49_outer_lazy", 13u8),
    ];
    // Fixed-width kernels run only at their own width; k84 is the k' <= 84
    // pin, k67/k51 the r=3 and r=2 layout candidates, k65/k49 those layouts
    // under LogUp-GKR (helper-free).
    let shapes = [(64u16, 32u16), (80u16, 36u16)];
    let fixed_width: [(u8, u16); 6] = [(8, 80), (9, 84), (10, 67), (11, 65), (12, 51), (13, 49)];
    let mut variants = Vec::new();
    for (kernel, kernel_id) in kernels {
        for (columns, query_count) in shapes {
            if let Some(&(_, width)) = fixed_width.iter().find(|(id, _)| *id == kernel_id) {
                if query_count != 36 {
                    continue;
                }
                let columns = width;
                let mut means = Vec::new();
                let mut full_samples = Vec::new();
                for measured_queries in [0, query_count] {
                    let instruction = Instruction {
                        program_id: aspis_verifier::id(),
                        accounts: vec![],
                        data: to_vec(&AspisInstruction::WideRlcProbe {
                            columns,
                            query_count: measured_queries,
                            kernel: kernel_id,
                        })?,
                    };
                    let samples =
                        simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
                    means.push(samples.iter().sum::<u64>() as f64 / samples.len() as f64);
                    full_samples = samples;
                }
                variants.push(WideRlcProbeVariant {
                    kernel,
                    columns,
                    query_count,
                    simulation_cu: full_samples,
                    simulation_cu_mean: means[1],
                    baseline_cu_mean: means[0],
                    incremental_cu: (means[1] - means[0]).round() as i64,
                });
                continue;
            }
            let mut means = Vec::new();
            let mut full_samples = Vec::new();
            for measured_queries in [0, query_count] {
                let instruction = Instruction {
                    program_id: aspis_verifier::id(),
                    accounts: vec![],
                    data: to_vec(&AspisInstruction::WideRlcProbe {
                        columns,
                        query_count: measured_queries,
                        kernel: kernel_id,
                    })?,
                };
                let samples = simulate_pure_instruction(&rpc, &payer, instruction, REPETITIONS)?;
                means.push(samples.iter().sum::<u64>() as f64 / samples.len() as f64);
                full_samples = samples;
            }
            variants.push(WideRlcProbeVariant {
                kernel,
                columns,
                query_count,
                simulation_cu: full_samples,
                simulation_cu_mean: means[1],
                baseline_cu_mean: means[0],
                incremental_cu: (means[1] - means[0]).round() as i64,
            });
        }
    }
    Ok(WideRlcProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-wide-rlc-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        variants,
        notes: vec![
            "Unlike the historical layout loop, this probe uses gamma powers and measures all q*k base-column contributions required at the wide PCS seam.".to_string(),
            "lazy_dot4 fuses four raw-M31 scalar products per reduction. lazy_dot4_outer_lazy then accumulates those canonical block results in u64 and performs one final reduction per QM31 limb; both are differential-tested against the eager reference.".to_string(),
            "fixed80_outer_lazy uses qm31_power_table::<80> and stack-backed fixed arrays for the ruled k=80 shape; it is the selected 201,990-CU kernel. The generic outer-lazy slice API remains available for other widths.".to_string(),
            "packed4_lazy_dot injectively maps four raw M31 columns into one QM31 coefficient before batching; the k=80 shape therefore has degree 19 in gamma rather than 79 and no column information is discarded.".to_string(),
            "This still excludes wide-leaf hashing and must be integrated with real proof parsing before a gate closes.".to_string(),
        ],
    })
}

pub fn run_stage2_merkle_arity_probe() -> Result<MerkleArityProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let shapes = [
        ("c1_layer_0", 10u8, 36u16),
        ("c2_layer_0", 10, 36),
        ("c1_layer_1", 8, 36),
        ("c1_layer_2", 6, 36),
        ("c1_layer_3", 4, 36),
    ];
    let mut points = Vec::new();
    for (tree, depth, query_count) in shapes {
        let mut runs = Vec::new();
        for arity in [2u8, 4u8] {
            let instruction = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&AspisInstruction::MerkleArityProbe {
                    depth,
                    query_count,
                    arity,
                })?,
            };
            runs.push(simulate_pure_instruction(
                &rpc,
                &payer,
                instruction,
                REPETITIONS,
            )?);
        }
        let binary_mean = runs[0].iter().sum::<u64>() as f64 / runs[0].len() as f64;
        let radix4_mean = runs[1].iter().sum::<u64>() as f64 / runs[1].len() as f64;
        points.push(MerkleArityProbePoint {
            tree,
            depth,
            query_count,
            binary_cu: runs.remove(0),
            binary_cu_mean: binary_mean,
            radix4_cu: runs.remove(0),
            radix4_cu_mean: radix4_mean,
            radix4_savings_cu: (binary_mean - radix4_mean).round() as i64,
        });
    }
    let binary_total = points
        .iter()
        .map(|point| point.binary_cu_mean.round() as i64)
        .sum();
    let radix4_total = points
        .iter()
        .map(|point| point.radix4_cu_mean.round() as i64)
        .sum();
    Ok(MerkleArityProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-merkle-arity-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        points,
        modeled_binary_total_cu: binary_total,
        modeled_radix4_total_cu: radix4_total,
        modeled_radix4_savings_cu: binary_total - radix4_total,
        notes: vec![
            "Pure minimal-subtree traversal/hash model over deterministic query indices; leaf hashing and proof-byte parsing are excluded equally.".to_string(),
            "Radix-4 is tailored to the arity-4 fold: all frozen depths are even, and one 129-byte SHA call replaces up to three 65-byte binary-node calls.".to_string(),
            "A positive model is not authorization to re-pin roots or the transcript; a real g16 proof comparison must precede any g32 fixture change.".to_string(),
        ],
    })
}

fn hvzk_mask_queries(log_rate: u8, johnson: bool, pow_bits: u8) -> u8 {
    // Nine full-system branches (the upstream eight, plus the external
    // zerocheck mask group) need ceil(log2(9)) = 4 union bits.
    let target = (104usize.saturating_sub(pow_bits as usize)) as f64;
    let bits_per_query = if johnson {
        log_rate as f64 / 2.0 - 1.05f64.log2()
    } else {
        log_rate as f64
    };
    (target / bits_per_query).ceil() as u8
}

fn hvzk_probe_depth_host(message_len: usize, queries: usize, log_rate: u8) -> u32 {
    (message_len + queries).next_power_of_two().ilog2() + log_rate as u32
}

fn hvzk_probe_indices(depth: u32, queries: usize) -> Vec<u32> {
    let mask = (1u32 << depth) - 1;
    let mut indices = (0..queries)
        .map(|query| {
            (query as u32)
                .wrapping_mul(0x9e37_79b9)
                .wrapping_add(0x7f4a_7c15)
                & mask
        })
        .collect::<Vec<_>>();
    indices.sort_unstable();
    indices.dedup();
    indices
}

fn hvzk_frontier_nodes(depth: u32, queries: usize) -> usize {
    let mut level = hvzk_probe_indices(depth, queries);
    let mut frontier = 0usize;
    for _ in 0..depth / 2 {
        let mut next = Vec::with_capacity(level.len());
        let mut position = 0usize;
        while position < level.len() {
            let parent = level[position] >> 2;
            let mut present = 0usize;
            while position < level.len() && level[position] >> 2 == parent {
                present += 1;
                position += 1;
            }
            frontier += 4 - present;
            next.push(parent);
        }
        level = next;
    }
    if depth & 1 != 0 {
        let mut next = Vec::with_capacity(level.len());
        let mut position = 0usize;
        while position < level.len() {
            let parent = level[position] >> 1;
            let mut present = 0usize;
            while position < level.len() && level[position] >> 1 == parent {
                present += 1;
                position += 1;
            }
            frontier += 2 - present;
            next.push(parent);
        }
        level = next;
    }
    debug_assert_eq!(level.len(), 1);
    frontier
}

fn hvzk_incremental_proof_bytes(log_rate: u8, queries: u8, batched: bool) -> usize {
    let q = queries as usize;
    let sc_depth = hvzk_probe_depth_host(7, q, log_rate);
    let switch_depth = hvzk_probe_depth_host(31, q, log_rate);
    let external_depth = hvzk_probe_depth_host(28, q, log_rate);
    let mask_roots = if batched { 5 } else { 16 };
    let mask_frontier_nodes = if batched {
        5 * hvzk_frontier_nodes(switch_depth, q)
    } else {
        8 * hvzk_frontier_nodes(sc_depth, q)
            + 6 * hvzk_frontier_nodes(switch_depth, q)
            + 2 * hvzk_frontier_nodes(external_depth, q)
    };
    let mask_reveal_elements = 8 * (7 + q) + 3 * (31 + q) + 10 * (28 + q);
    let mask_opened_elements = 2 * 21 * q;
    let fresh_main_depth = 7u32;
    let fresh_main_queries = 29usize;
    // Roots, fresh-side claim, source reveals, all mask reveals, mask rows,
    // Merkle frontiers, and fresh-main rows/frontier. The already-required
    // source-oracle opening is excluded as non-incremental PCS work.
    (mask_roots + 1) * 32
        + 16
        + (4 + 29) * 16
        + mask_reveal_elements * 16
        + mask_opened_elements * 16
        + mask_frontier_nodes * 32
        + fresh_main_queries * 16
        + hvzk_frontier_nodes(fresh_main_depth, fresh_main_queries) * 32
}

pub fn run_stage2_hvzk_whir_mask_probe() -> Result<HvzkMaskProbeSummary> {
    const SCOPE_TOTAL: u8 = 2;
    const MODE_UPSTREAM: u8 = 0;
    const MODE_BATCHED: u8 = 1;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let simulate = |log_rate: u8,
                    queries: u8,
                    mode: u8,
                    phase: u8,
                    start: u8,
                    end: u8|
     -> Result<u64> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::HvzkWhirMaskProbe {
                mask_log_inv_rate: log_rate,
                mask_queries: queries,
                scope: SCOPE_TOTAL,
                mode,
                phase,
                start,
                end,
            })?,
        };
        Ok(simulate_pure_instruction(&rpc, &payer, instruction, 1)
                .with_context(|| {
                    format!(
                        "HVZK mask probe rate={log_rate} q={queries} mode={mode} phase={phase} range={start}..{end}"
                    )
                })?[0])
    };
    let simulate_one_switch = |mode: u8, phase: u8, start: u8, end: u8| -> Result<u64> {
        let instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::HvzkWhirMaskProbe {
                mask_log_inv_rate: 5,
                mask_queries: 29,
                scope: 3,
                mode,
                phase,
                start,
                end,
            })?,
        };
        Ok(
            simulate_pure_instruction(&rpc, &payer, instruction, 1).with_context(|| {
                format!("minimal one-switch HVZK mode={mode} phase={phase} range={start}..{end}")
            })?[0],
        )
    };

    let measure_batched_with_pow = |log_rate: u8, queries: u8| -> Result<(i64, usize, i64)> {
        let control = simulate(log_rate, queries, MODE_BATCHED, 0, 0, 0)?;
        let independent = simulate(log_rate, queries, MODE_BATCHED, 1, 0, 1)?;
        let switch = simulate(log_rate, queries, MODE_BATCHED, 1, 1, 2)?;
        let fresh = simulate(log_rate, queries, MODE_BATCHED, 1, 4, 5)?;
        let merkle = control as i64
            + (independent as i64 - control as i64)
            + 3 * (switch as i64 - control as i64)
            + (fresh as i64 - control as i64);
        let setup = simulate(log_rate, queries, MODE_BATCHED, 3, 0, 0)?;
        let one = simulate(log_rate, queries, MODE_BATCHED, 3, 0, 1)?;
        let spots = setup as i64 + queries as i64 * (one as i64 - setup as i64);
        let target = simulate(log_rate, queries, MODE_BATCHED, 5, 0, 0)?;
        let transcript = simulate(log_rate, queries, MODE_BATCHED, 6, 0, 0)?;
        let pow = simulate(log_rate, queries, MODE_BATCHED, 4, 0, 0)?;
        let total = control as i64
            + (merkle - control as i64)
            + (spots - control as i64)
            + (target as i64 - control as i64)
            + (transcript as i64 - control as i64)
            + (pow as i64 - control as i64);
        Ok((
            total,
            hvzk_incremental_proof_bytes(log_rate, queries, true) + 8,
            pow as i64 - control as i64,
        ))
    };

    let mut rows = Vec::new();
    for log_rate in [4u8, 5, 6, 8] {
        let mut pow_candidates = Vec::new();
        for bits in [20u8, 40] {
            let johnson_queries = hvzk_mask_queries(log_rate, true, bits);
            let (mask_cu, proof_bytes, pow_delta) =
                measure_batched_with_pow(log_rate, johnson_queries)?;
            pow_candidates.push(HvzkMaskPowRow {
                bits,
                root_bound_queries: hvzk_mask_queries(log_rate, false, bits),
                johnson_queries,
                verifier_incremental_cu: pow_delta,
                proof_bytes: 8,
                honest_expected_trials: format!("2^{bits}"),
                johnson_timing_batched_mask_verifier_cu: mask_cu,
                johnson_timing_batched_incremental_proof_bytes: proof_bytes,
            });
        }
        for (soundness_model, johnson, conditional_root_bound) in [
            ("conditional_polynomial_root_bound", false, true),
            ("upstream_johnson_proven", true, false),
        ] {
            let queries = hvzk_mask_queries(log_rate, johnson, 0);
            let control = simulate(log_rate, queries, MODE_UPSTREAM, 0, 0, 0)?;
            let upstream_sc_tree = simulate(log_rate, queries, MODE_UPSTREAM, 1, 0, 1)?;
            let upstream_switch_tree = simulate(log_rate, queries, MODE_UPSTREAM, 1, 4, 5)?;
            let upstream_external_tree = simulate(log_rate, queries, MODE_UPSTREAM, 1, 14, 15)?;
            let upstream_merkle = (control as i64
                + 8 * (upstream_sc_tree as i64 - control as i64)
                + 6 * (upstream_switch_tree as i64 - control as i64)
                + 2 * (upstream_external_tree as i64 - control as i64))
                as u64;
            let batched_independent_tree = simulate(log_rate, queries, MODE_BATCHED, 1, 0, 1)?;
            let batched_switch_tree = simulate(log_rate, queries, MODE_BATCHED, 1, 1, 2)?;
            let batched_fresh_tree = simulate(log_rate, queries, MODE_BATCHED, 1, 4, 5)?;
            let batched_merkle = (control as i64
                + (batched_independent_tree as i64 - control as i64)
                + 3 * (batched_switch_tree as i64 - control as i64)
                + (batched_fresh_tree as i64 - control as i64))
                as u64;
            let scalar_one = simulate(log_rate, queries, MODE_UPSTREAM, 2, 0, 1)?;
            let scalar_total =
                control as i64 + queries as i64 * (scalar_one as i64 - control as i64);
            let batched_setup = simulate(log_rate, queries, MODE_BATCHED, 3, 0, 0)?;
            let batched_one = simulate(log_rate, queries, MODE_BATCHED, 3, 0, 1)?;
            let batched_total =
                batched_setup as i64 + queries as i64 * (batched_one as i64 - batched_setup as i64);
            let target = simulate(log_rate, queries, MODE_BATCHED, 5, 0, 0)?;
            let upstream_transcript = simulate(log_rate, queries, MODE_UPSTREAM, 6, 0, 0)?;
            let batched_transcript = simulate(log_rate, queries, MODE_BATCHED, 6, 0, 0)?;
            let reconcile = |merkle: u64, spots: i64, transcript: u64| {
                control as i64
                    + (merkle as i64 - control as i64)
                    + (spots - control as i64)
                    + (target as i64 - control as i64)
                    + (transcript as i64 - control as i64)
            };
            rows.push(HvzkMaskProbeRow {
                mask_log_inv_rate: log_rate,
                soundness_model,
                mask_queries: queries,
                bits_per_query: if johnson {
                    log_rate as f64 / 2.0 - 1.05f64.log2()
                } else {
                    log_rate as f64
                },
                mask_domain_depths: [
                    hvzk_probe_depth_host(7, queries as usize, log_rate),
                    hvzk_probe_depth_host(31, queries as usize, log_rate),
                    hvzk_probe_depth_host(28, queries as usize, log_rate),
                ],
                conditional_root_bound,
                control_cu: control,
                upstream_merkle_cu: upstream_merkle,
                timing_batched_merkle_cu: batched_merkle,
                scalar_one_query_cu: scalar_one,
                scalar_spot_checks_reconciled_cu: scalar_total,
                batched_setup_cu: batched_setup,
                batched_one_query_cu: batched_one,
                batched_spot_checks_reconciled_cu: batched_total,
                target_identity_cu: target,
                upstream_transcript_cu: upstream_transcript,
                timing_batched_transcript_cu: batched_transcript,
                upstream_reconciled_mask_verifier_cu: reconcile(
                    upstream_merkle,
                    scalar_total,
                    upstream_transcript,
                ),
                timing_batched_reconciled_mask_verifier_cu: reconcile(
                    batched_merkle,
                    batched_total,
                    batched_transcript,
                ),
                upstream_incremental_proof_bytes: hvzk_incremental_proof_bytes(
                    log_rate, queries, false,
                ),
                timing_batched_incremental_proof_bytes: hvzk_incremental_proof_bytes(
                    log_rate, queries, true,
                ),
                optional_pow: pow_candidates.clone(),
            });
        }
    }
    let source_control = simulate(5, 29, MODE_BATCHED, 0, 0, 0)?;
    let source_current_merkle = simulate(5, 29, MODE_BATCHED, 8, 0, 0)?;
    let source_padded_merkle = simulate(5, 29, MODE_BATCHED, 9, 0, 0)?;
    let source_base_spot = simulate(5, 29, MODE_BATCHED, 7, 0, 0)?;
    let fresh_main_merkle = simulate(5, 29, MODE_BATCHED, 10, 0, 0)?;
    let dimensions = [285usize, 93, 45, 33];
    let current_domains = [8_192usize, 2_048, 512, 128];
    let padded_domains = [16_384usize, 4_096, 2_048, 2_048];
    let padded_actual_rates =
        core::array::from_fn(|i| dimensions[i] as f64 / padded_domains[i] as f64);
    let current_depths = [13u32, 11, 9, 7];
    let padded_depths = [14u32, 12, 11, 11];
    let current_frontier: usize = current_depths
        .into_iter()
        .map(|depth| hvzk_frontier_nodes(depth, 29))
        .sum();
    let padded_frontier: usize = padded_depths
        .into_iter()
        .map(|depth| hvzk_frontier_nodes(depth, 29))
        .sum();
    let source_padding = HvzkSourcePaddingProbe {
        dimensions,
        current_domains,
        padded_domains,
        padded_actual_rates,
        every_padded_rate_at_most_one_over_32: padded_actual_rates
            .iter()
            .all(|&rate| rate <= 1.0 / 32.0),
        query_count: 29,
        current_merkle_cu: source_current_merkle,
        padded_merkle_cu: source_padded_merkle,
        padded_minus_current_merkle_cu: source_padded_merkle as i64 - source_current_merkle as i64,
        padded_minus_current_frontier_bytes: (padded_frontier as i64 - current_frontier as i64)
            * 32,
        source_base_spot_reencode_cu: source_base_spot,
        source_base_spot_reencode_incremental_cu: source_base_spot as i64 - source_control as i64,
        fresh_main_merkle_cu: fresh_main_merkle,
        fresh_main_merkle_incremental_cu: fresh_main_merkle as i64 - source_control as i64,
        total_new_source_side_incremental_cu: (source_padded_merkle as i64
            - source_current_merkle as i64)
            + (source_base_spot as i64 - source_control as i64)
            + (fresh_main_merkle as i64 - source_control as i64),
        q29_g36_johnson_shape_survives_rate_check: padded_actual_rates
            .iter()
            .all(|&rate| rate <= 1.0 / 32.0),
    };
    // Conservative measured proxy: adding a second M31 limb to every one of
    // 16 columns is represented by the exact q36 width17->33 delta, scaled
    // only by the q29 loop count. A dedicated QM31xCM31 kernel may beat this.
    let cm31_arithmetic_proxy = ((388_564i64 - 270_049) * 29 + 18) / 36;
    // The 784-byte leaf probe adds twelve SHA-256 compression blocks over its
    // empty control for 382 CU. Doubling a width16 leaf 256->512 bytes adds
    // four blocks per query.
    let cm31_leaf_hash_proxy = (382i64 * 4 * 29 + 6) / 12;
    let direct_cm31_rs_decision = HvzkDirectCm31RsDecision {
        state_only_columns: 16,
        query_count: 29,
        circle_m31_leaf_bytes: 256,
        direct_cm31_leaf_bytes: 512,
        incremental_opened_leaf_bytes: (512 - 256) * 29,
        measured_double_limb_arithmetic_proxy_cu: cm31_arithmetic_proxy,
        derived_leaf_hash_proxy_cu: cm31_leaf_hash_proxy,
        combined_verifier_delta_proxy_cu: cm31_arithmetic_proxy + cm31_leaf_hash_proxy,
        arithmetic_proxy_source: "layer0_dot_width_probe q36 width17->33 delta, scaled by 29/36; conservative separate-M31-limb proxy",
        hash_proxy_source: "m31_circle_basis_probe 382 CU over twelve extra SHA-256 blocks; direct CM31 adds four blocks/query",
        theorem_transfer_status: "ordinary multiplicative-subgroup RS is the upstream theorem family, but exact QM31/CM31 domain, code-switch, and state-only adapter instantiation remains a proof obligation",
    };
    let one_control = simulate_one_switch(MODE_UPSTREAM, 0, 0, 0)?;
    let one_tree = simulate_one_switch(MODE_UPSTREAM, 1, 0, 1)?;
    let one_merkle = one_control as i64 + 2 * (one_tree as i64 - one_control as i64);
    let one_scalar_query = simulate_one_switch(MODE_UPSTREAM, 2, 0, 1)?;
    let one_scalar_spots = one_control as i64 + 29 * (one_scalar_query as i64 - one_control as i64);
    let one_optimized_setup = simulate_one_switch(MODE_BATCHED, 3, 0, 0)?;
    let one_optimized_query = simulate_one_switch(MODE_BATCHED, 3, 0, 1)?;
    let one_optimized_spots =
        one_optimized_setup as i64 + 29 * (one_optimized_query as i64 - one_optimized_setup as i64);
    let one_target = simulate_one_switch(MODE_BATCHED, 5, 0, 0)?;
    let one_transcript = simulate_one_switch(MODE_BATCHED, 6, 0, 0)?;
    let one_overlap_transcript = simulate_one_switch(MODE_BATCHED, 11, 0, 0)?;
    let one_leaf64 = simulate_one_switch(MODE_UPSTREAM, 12, 0, 0)?;
    let one_leaf80 = simulate_one_switch(MODE_BATCHED, 12, 0, 0)?;
    let one_leaf_lane_delta = one_leaf80 as i64 - one_leaf64 as i64;
    let one_reconcile = |spots: i64| {
        one_control as i64
            + (one_merkle - one_control as i64)
            + (spots - one_control as i64)
            + (one_target as i64 - one_control as i64)
            + (one_transcript as i64 - one_control as i64)
    };
    let one_frontier = hvzk_frontier_nodes(11, 29);
    let one_switch_proof_bytes = 2 * 32 + 16 + (31 + 29) * 16 + 2 * 29 * 16 + 2 * one_frontier * 32;
    let one_switch_bits = 29.0 * (5.0 / 2.0 - 1.05f64.log2()) + 36.0;
    let minimal_one_switch = HvzkOneSwitchProbe {
        message_len: 31,
        randomness_len: 29,
        domain_size: 2_048,
        domain_depth: 11,
        query_count: 29,
        johnson_query_bits: 29.0 * (5.0 / 2.0 - 1.05f64.log2()),
        positioned_work_bits: 36,
        combined_query_work_bits: one_switch_bits,
        reaches_104_bits: one_switch_bits >= 104.0,
        roots_fixed_before_work_required: true,
        scalar_merkle_cu: one_merkle,
        scalar_spot_cu: one_scalar_spots,
        optimized_single_word_spot_cu: one_optimized_spots,
        target_identity_cu: one_target as i64 - one_control as i64,
        transcript_cu: one_transcript as i64 - one_control as i64,
        scalar_reconciled_cu: one_reconcile(one_scalar_spots),
        optimized_reconciled_cu: one_reconcile(one_optimized_spots),
        incremental_proof_bytes: one_switch_proof_bytes,
        shared_root_leaf_hash_delta_cu_per_lane: one_leaf_lane_delta,
        shared_root_transcript_cu: one_overlap_transcript as i64 - one_control as i64,
        shared_root_lower_bound_cu: one_control as i64
            + (one_optimized_spots - one_control as i64)
            + (one_target as i64 - one_control as i64)
            + (one_overlap_transcript as i64 - one_control as i64)
            + 2 * one_leaf_lane_delta,
        shared_root_lower_bound_proof_bytes: 16 + (31 + 29) * 16 + 2 * 29 * 16,
        shared_root_conditions: "carried lane must be committed inside an already-required later-fold root at the same causal point; fresh lane must share a base root committed before gamma; both existing trees must expose the same q29 mask-domain rows; otherwise use the standalone 17,136-byte/two-tree row",
        optional_source_reencode_incremental_cu: source_padding
            .source_base_spot_reencode_incremental_cu,
        source_reencode_required_for_isolated_switch_identity: false,
        soundness_status: "q29 plus the existing correctly positioned g36 reaches 106.46 Johnson bits only if both roots, the reveal, and the target claim are fixed before the nonce and shared query-position squeeze",
    };
    Ok(HvzkMaskProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-hvzk-whir-mask-probe".into(),
        validator_version: validator_version(),
        upstream_commit: "Plonky3/Plonky3@6b6a3b4d40fca2187d368c9dc1fca417c84ae8c3".into(),
        instruction_wire_ordinal: 41,
        internal_carried_groups: [2, 1, 2, 1, 2, 1, 2],
        internal_mask_codewords: 11,
        external_zerocheck_group_width: 10,
        source_padding,
        direct_cm31_rs_decision,
        minimal_one_switch,
        rows,
        notes: vec![
            "The seven internal carried groups and eleven mask codewords are read from upstream ZkWhirConfig::mask_groups for three switch rounds and arity-four folding.".into(),
            "PCS-internal sumcheck masks use ell_zk=7 (degree-six relation); the separate state-only external zerocheck uses width ten and ell_zk=28; switch messages are q29+two OOD pads=31.".into(),
            "Raw root-bound rows are conditional on every committed mask oracle already being a valid RS codeword. Upstream Merkle commitments do not establish that invariant, so only Johnson rows are labeled proven.".into(),
            "Timing batching precommits only challenge-independent sumcheck masks, keeps all three switch masks sequential, uses a common padded mask domain, groups fresh base-case masks, and samples eta after reveals but before shared positions.".into(),
            "The eta batch has an additional at-most 20/|QM31| identity-collision term. It is not included in the query exponent and must be unioned in the full soundness ledger.".into(),
            "CU totals are overlap-subtracted isolated models: control + each phase-minus-control. Per-query arithmetic is one measured query extrapolated by exact loop count; it is not an integrated production verifier measurement.".into(),
            "Proof bytes exclude the source-oracle opening already required by the plain PCS and exclude serializer framing; they include new roots, reveals, mask/fresh rows, and deterministic-query radix-four frontiers.".into(),
            "Dedicated PoW rows are optional new transcript moves after eta/reveals and before positions. Their verifier delta is one hash; 20/40-bit honest grinding is 2^20/2^40 expected trials and is not free.".into(),
            "The separate source-padding row compares leaf-domain sizes [8192,2048,512,128] with [16384,4096,2048,2048] for dimensions [285,93,45,33]. The padded rates are all <=1/32, which preserves the q29/g36 Johnson rate premise but is not by itself a full soundness proof.".into(),
            "The direct-CM31 RS decision row is a conservative arithmetic/hash delta only. It prices the second limb as 16 additional M31 columns; a dedicated mixed QM31xCM31 kernel may reduce that delta. Ordinary subgroup RS is closer to upstream theorem scope, but transfer is not claimed complete.".into(),
            "The minimal one-switch row prices one width-one ell31 mask at rate1/32 with the main q29 positions. Existing g36 work is credited only under the pinned pre-work binding order; the isolated switch identity does not require Construction7.2's fresh-main/source re-encoding.".into(),
        ],
    })
}

pub fn run_stage2_radix8_merkle_probe() -> Result<Radix8MerkleDepth12Summary> {
    const REPETITIONS: usize = 5;
    const DEPTH: u8 = 12;
    const QUERIES: u16 = 36;
    const OPENED_DIGEST_ENTRY_BYTES: usize = QUERIES as usize * (4 + 32);

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for (arity, parent_hash_calls, frontier_hashes, preimage_bytes, compression_blocks) in [
        (4u8, 112usize, 301usize, 14_448usize, 336usize),
        (8, 72, 469, 18_504, 360),
    ] {
        let clean_instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::Radix8MerkleDepth12Probe {
                arity,
                corrupt_frontier: false,
            })?,
        };
        let simulation_cu =
            simulate_pure_instruction(&rpc, &payer, clean_instruction, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;

        let corrupt_instruction = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::Radix8MerkleDepth12Probe {
                arity,
                corrupt_frontier: true,
            })?,
        };
        let corrupted_frontier_probe =
            simulate_pure_instruction(&rpc, &payer, corrupt_instruction, 1)?;
        let frontier_bytes = frontier_hashes * 32;
        variants.push(Radix8MerkleDepth12Variant {
            arity,
            parent_hash_calls,
            frontier_hashes,
            frontier_bytes,
            opened_digest_entry_bytes: OPENED_DIGEST_ENTRY_BYTES,
            synthetic_minimal_subtree_bytes: OPENED_DIGEST_ENTRY_BYTES + frontier_bytes,
            parent_preimage_bytes: preimage_bytes,
            sha256_compression_blocks: compression_blocks,
            simulation_cu,
            simulation_cu_mean,
            corrupted_frontier_probe_cu: corrupted_frontier_probe[0],
            corrupted_frontier_rejected: true,
        });
    }

    let delta = (variants[1].simulation_cu_mean - variants[0].simulation_cu_mean).round() as i64;
    let frontier_delta = variants[1].frontier_bytes as i64 - variants[0].frontier_bytes as i64;
    Ok(Radix8MerkleDepth12Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-radix8-merkle-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        depth: DEPTH,
        distinct_queries: QUERIES,
        variants,
        radix8_minus_radix4_cu: delta,
        two_layer0_tree_projection_cu: delta * 2,
        two_layer0_tree_frontier_byte_delta: frontier_delta * 2,
        notes: vec![
            "Append-only tag 35 hashes the same 36 sorted depth-12 leaf digests under both arities; production roots, proof framing, transcript, and profile remain radix-4.".to_string(),
            "The frontier is embedded read-only and leaf hashing is excluded equally. The measured object is minimal-subtree verification/traversal, not proof construction or a whole PCS.".to_string(),
            "Synthetic minimal-subtree bytes count (u32 index + 32-byte opened digest) per query plus frontier hashes. Real Aspis leaves are larger but identical across this A/B, so the exact arity-dependent proof delta is the frontier-byte delta.".to_string(),
            "The corruption instruction flips one built-in frontier bit and returns success only if the selected verifier rejects; host tests separately cover truncation, extension, malformed hashes, leaf/root mutations, duplicate/order/range failures, and invalid depths.".to_string(),
            "Pure radix-8 directly supports depths divisible by three. Current later trees at depths 10 and 8 require a separately specified hybrid-arity commitment; this artifact does not project or authorize one.".to_string(),
            "The two-layer0 projection multiplies only the isolated same-shape delta for C1 and C2. It is overlap-safe for those two calls but is not an integrated verifier total.".to_string(),
        ],
    })
}

pub fn run_stage2_merkle_forest_probe() -> Result<MerkleForestProbeSummary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for (fused, mode) in [(false, "five_independent"), (true, "staggered_forest")] {
        let clean = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::MerkleForestProbe {
                fused,
                corrupt_lane: u8::MAX,
            })?,
        };
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, clean, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        let mut corrupted_lane_probe_cu = Vec::with_capacity(5);
        for corrupt_lane in 0..5u8 {
            let corrupt = Instruction {
                program_id: aspis_verifier::id(),
                accounts: vec![],
                data: to_vec(&AspisInstruction::MerkleForestProbe {
                    fused,
                    corrupt_lane,
                })?,
            };
            corrupted_lane_probe_cu.push(simulate_pure_instruction(&rpc, &payer, corrupt, 1)?[0]);
        }
        variants.push(MerkleForestProbeVariant {
            mode,
            simulation_cu,
            simulation_cu_mean,
            corrupted_lane_probe_cu,
            all_five_corrupted_lanes_rejected: true,
        });
    }
    let fused_minus_independent_cu =
        (variants[1].simulation_cu_mean - variants[0].simulation_cu_mean).round() as i64;
    Ok(MerkleForestProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-merkle-forest-probe"
            .to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        depth: 12,
        distinct_queries: 36,
        tree_start_levels: [0, 0, 1, 2, 3],
        unique_leaves: [36, 36, 34, 33, 27],
        parent_hash_calls: 365,
        frontier_hashes: 934,
        frontier_bytes: 29_888,
        variants,
        fused_minus_independent_cu,
        notes: vec![
            "Append-only tag 36 runs five independent roots/frontiers/hash lanes over the exact profile-15 q36 stagger; production verification is unchanged.".to_string(),
            "Both variants construct identical shifted indices, leaf digests, all-zero frontier bytes, and roots. The forest shares only public parent grouping and present-slot discovery; it retains 365 SHA calls and 934 frontier hashes.".to_string(),
            "Each mode separately rejects a one-bit mutation in every one of the five frontier streams. Host tests additionally cover roots, leaves, framing, ordering, duplicates, range, and wrong stagger.".to_string(),
            "The delta is an isolated traversal/temporary-layout measurement. It excludes real leaf hashing/canonical decoding equally and is not an integrated verifier saving until production integration is measured.".to_string(),
        ],
    })
}

pub fn run_stage2_layer0_dot_width_probe() -> Result<Layer0DotWidthProbeSummary> {
    use aspis_core::field::{CM31, M31, QM31};

    const REPETITIONS: usize = 5;
    const QUERY_COUNT: u8 = 36;

    fn host_sink<const N: usize>() -> [u8; 32] {
        let gamma = QM31 {
            c0: CM31::new(M31(7), M31(11)),
            c1: CM31::new(M31(13), M31(17)),
        };
        let mut power = QM31::ONE;
        let weights: [QM31; N] = core::array::from_fn(|_| {
            let result = power;
            power = power.mul(gamma);
            result
        });
        let helper_weights = [power, power.mul(gamma)];
        let mut values: [[M31; N]; 4] = core::array::from_fn(|slot| {
            core::array::from_fn(|column| {
                M31(1 + ((slot as u32 * 1_009 + column as u32 * 131) % 1_000_003))
            })
        });
        let mut helper_values: [[QM31; 4]; 2] = core::array::from_fn(|helper| {
            core::array::from_fn(|slot| QM31 {
                c0: CM31::new(
                    M31(10_001 + helper as u32 * 101 + slot as u32 * 11),
                    M31(20_003 + helper as u32 * 103 + slot as u32 * 13),
                ),
                c1: CM31::new(
                    M31(30_007 + helper as u32 * 107 + slot as u32 * 17),
                    M31(40_009 + helper as u32 * 109 + slot as u32 * 19),
                ),
            })
        });
        let mut accumulator = [QM31::ZERO; 4];
        for query in 0..u32::from(QUERY_COUNT) {
            values[0][0] = M31(100_003 + query * 997);
            helper_values[0][0].c0.a = M31(200_003 + query * 991);
            let mut combined: [QM31; 4] = core::array::from_fn(|slot| {
                weights
                    .iter()
                    .zip(values[slot].iter())
                    .fold(QM31::ZERO, |sum, (weight, value)| {
                        sum.add(weight.mul_m31(*value))
                    })
            });
            for helper in 0..2 {
                for slot in 0..4 {
                    combined[slot] =
                        combined[slot].add(helper_weights[helper].mul(helper_values[helper][slot]));
                }
            }
            for slot in 0..4 {
                accumulator[slot] = accumulator[slot].add(combined[slot]);
            }
        }
        let mut encoded = [0u8; 64];
        for (slot, value) in accumulator.iter().enumerate() {
            value.write_le_bytes(&mut encoded[slot * 16..(slot + 1) * 16]);
        }
        let width = [N as u8];
        HOST_HASH(&[b"aspis-layer0-dot-width-probe-v1", &width, &encoded])
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for columns in [49u8, 33, 17, 16] {
        let expected_sink = match columns {
            49 => host_sink::<49>(),
            33 => host_sink::<33>(),
            17 => host_sink::<17>(),
            16 => host_sink::<16>(),
            _ => unreachable!(),
        };
        let clean = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::Layer0DotWidthProbe {
                columns,
                corrupt: 0,
                expected_sink,
            })?,
        };
        ensure!(
            clean.data[0] == 37,
            "layer-zero width probe wire tag drifted"
        );
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, clean, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;

        let corrupt_c1 = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::Layer0DotWidthProbe {
                columns,
                corrupt: 1,
                expected_sink,
            })?,
        };
        let noncanonical_c1_probe_cu = simulate_pure_instruction(&rpc, &payer, corrupt_c1, 1)?[0];
        let corrupt_c2 = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::Layer0DotWidthProbe {
                columns,
                corrupt: 2,
                expected_sink,
            })?,
        };
        let noncanonical_c2_probe_cu = simulate_pure_instruction(&rpc, &payer, corrupt_c2, 1)?[0];
        variants.push(Layer0DotWidthProbeVariant {
            columns,
            c1_leaf_bytes: 4 * usize::from(columns) * 4,
            c2_leaf_bytes: 2 * 4 * 16,
            query_count: QUERY_COUNT,
            expected_sink_hex: hex(&expected_sink),
            simulation_cu,
            simulation_cu_mean,
            savings_vs_49_columns_cu: 0,
            noncanonical_c1_probe_cu,
            noncanonical_c2_probe_cu,
            both_noncanonical_cases_rejected: true,
        });
    }
    let baseline = variants[0].simulation_cu_mean;
    for variant in &mut variants {
        variant.savings_vs_49_columns_cu = (baseline - variant.simulation_cu_mean).round() as i64;
    }
    let savings_49_to_33_cu =
        (variants[0].simulation_cu_mean - variants[1].simulation_cu_mean).round() as i64;
    let savings_49_to_17_cu =
        (variants[0].simulation_cu_mean - variants[2].simulation_cu_mean).round() as i64;
    let savings_49_to_16_cu =
        (variants[0].simulation_cu_mean - variants[3].simulation_cu_mean).round() as i64;
    let marginal_cu_per_removed_column_49_to_33 = savings_49_to_33_cu as f64 / 16.0;
    let marginal_cu_per_removed_column_33_to_17 =
        (variants[1].simulation_cu_mean - variants[2].simulation_cu_mean) / 16.0;
    let marginal_cu_for_removed_tail_17_to_16 =
        (variants[2].simulation_cu_mean - variants[3].simulation_cu_mean).round() as i64;

    Ok(Layer0DotWidthProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-layer0-dot-width-probe"
            .to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 37,
        repetitions: REPETITIONS,
        query_count: QUERY_COUNT,
        variants,
        savings_49_to_33_cu,
        savings_49_to_17_cu,
        savings_49_to_16_cu,
        marginal_cu_per_removed_column_49_to_33,
        marginal_cu_per_removed_column_33_to_17,
        marginal_cu_for_removed_tail_17_to_16,
        notes: vec![
            "Append-only tag 37 is a production-neutral q36 arithmetic diagnostic. It changes no proof format, commitment, transcript, query sampler, verifier acceptance path, or payment state transition.".to_string(),
            "Every clean row canonical-decodes four slot-major M31 byte vectors with an exact fixed-width prepared-limb dot4 kernel (4b+1 for 49/33/17, four complete blocks and no tail for 16), then canonical-decodes and applies exactly two fixed QM31 C2 helpers per slot. Gamma powers are prepared once outside q36; the established exact-49 production entrypoint is unchanged.".to_string(),
            "The 49/33/17/16 variants differ only in C1 column width and the corresponding helper exponents gamma^N and gamma^(N+1). N16 uses a literal four-block/no-tail primitive because multiplicity is absent from the direct-range semantic target. The same deterministic leaf is reused but one canonical C1 and C2 limb changes per query to prevent loop-invariant hoisting.".to_string(),
            "Expected sinks come from an independent host path using four ordinary QM31-by-M31 folds and generic QM31 helper products. Separate SBF teeth replace the final C1 and C2 coordinates by the noncanonical value P and succeed only when decoding rejects.".to_string(),
            "The measured savings isolate state-width arithmetic and canonical decode only. They do not include the Merkle leaf-byte/hash reduction, proof-byte reduction, composition-width reduction, or any soundness argument for removing columns, and therefore are not an integrated verifier projection.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_routing_partition_probe() -> Result<AtomicRoutingPartitionProbeSummary> {
    const REPETITIONS: usize = 5;
    const SEED: u32 = 0x4154_4f4d;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let legacy_sink = aspis_verifier::atomic_routing_partition_probe_sink(false, SEED);
    let optimized_sink = aspis_verifier::atomic_routing_partition_probe_sink(true, SEED);
    ensure!(
        legacy_sink == optimized_sink,
        "atomic routing partitions diverged"
    );

    let metadata = [
        (
            false,
            "legacy_rank103",
            "0x000f",
            103usize,
            84usize,
            1_021usize,
        ),
        (
            true,
            "repartitioned_rank74",
            "0x03c0",
            74usize,
            61usize,
            798usize,
        ),
    ];
    let mut variants = Vec::new();
    for (optimized, mode, mask, rank, products, entries) in metadata {
        let clean = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::AtomicRoutingPartitionProbe {
                optimized,
                seed: SEED,
                expected_sink: legacy_sink,
            })?,
        };
        let simulation_cu = simulate_pure_instruction(&rpc, &payer, clean, REPETITIONS)?;
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;

        let mut wrong_sink = legacy_sink;
        wrong_sink[0] ^= 1;
        let wrong = Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::AtomicRoutingPartitionProbe {
                optimized,
                seed: SEED,
                expected_sink: wrong_sink,
            })?,
        };
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                wrong,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let (wrong_sink_probe_cu, wrong_sink_error) = rpc.simulate(&transaction)?;
        ensure!(
            wrong_sink_error.is_some(),
            "wrong atomic routing sink accepted"
        );
        let wrong_sink_probe_cu = wrong_sink_probe_cu.unwrap_or(VERIFY_CU_LIMIT as u64);
        variants.push(AtomicRoutingPartitionProbeVariant {
            mode,
            low_row_bit_mask_hex: mask,
            tensor_routing_rank: rank,
            shared_outer_products: products,
            factor_entries: entries,
            expected_sink_hex: hex(&legacy_sink),
            simulation_cu,
            simulation_cu_mean,
            wrong_sink_probe_cu,
            wrong_sink_rejected: true,
        });
    }
    let optimized_savings_cu =
        (variants[0].simulation_cu_mean - variants[1].simulation_cu_mean).round() as i64;
    Ok(AtomicRoutingPartitionProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-routing-partition-probe".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 42,
        repetitions: REPETITIONS,
        seed: SEED,
        registry_fingerprint_hex: "0xa5249dda67f75888",
        copy_terms: 183,
        active_rows: 210,
        variants,
        optimized_savings_cu,
        outputs_identical: true,
        measurement_scope: "isolated atomic-v3 copy terminal lane only; not integrated verifier CU",
        notes: vec![
            "Both paths evaluate the same 183-link replacement-statement copy polynomial; only the exact row-bit tensor factorization changes.".to_string(),
            "The optimized 0x03c0 split was selected by exhaustive search over every 3..7-bit row partition, then pinned by 64 fresh random-QM31 compiled/reference identities and opening/challenge corruption teeth.".to_string(),
            "Append-only tag 42 has no accounts and cannot authorize payment-state mutation. The public append-index candidate is separately rejected at the 69-permutation layout-capacity gate.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile20_cost_candidate() -> Result<AtomicProfile20CostSummary> {
    use aspis_core::field::M31;
    use aspis_core::state_only_prefix::{
        run_state_only_transcript_schedule_host_unmined_for_diagnostics, StateOnlyCandidatePrefix,
        STATE_ONLY_RATE512_SHAPE, STATE_ONLY_STATEMENT_VALUE_COUNT,
    };
    use aspis_statement::{
        derive_nullifier, derive_owner_key, merkle_root, note_commitment, output_commitment,
        AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic,
    };
    use sha2::{Digest as _, Sha256};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }
    fn public_bytes(public: &SpendPublic) -> [u8; 104] {
        let mut output = [0u8; 104];
        for (index, value) in public
            .anchor
            .iter()
            .chain(&public.nullifier)
            .chain(&public.output_commitment)
            .chain(core::iter::once(&public.asset_id))
            .enumerate()
        {
            output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        output[100..].copy_from_slice(&public.fee.to_le_bytes());
        output
    }
    fn marker_delta(markers: &[CuMarker], label: &str) -> Option<u64> {
        markers
            .iter()
            .find(|marker| marker.label == label)?
            .delta_from_previous?
            .try_into()
            .ok()
    }
    fn literal_ledger(markers: &[CuMarker], total: u64) -> Option<AtomicProfile20CostLedger> {
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.first()?.remaining)?;
        let proof_load = marker_delta(markers, "atomic20_proof_loaded")?;
        let parse = marker_delta(markers, "atomic20_parse_done")?;
        let transcript = marker_delta(markers, "atomic20_transcript_done")?;
        let terminal = marker_delta(markers, "atomic20_terminal_done")?;
        let relation = marker_delta(markers, "atomic20_relation_done")?;
        let openings = marker_delta(markers, "atomic20_openings_parse_done")?;
        let queries = marker_delta(markers, "atomic20_queries_done")?;
        let verifier_return = marker_delta(markers, "atomic20_done")?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.last()?.remaining)?;
        let post = total.checked_sub(through_last)?;
        Some(make_atomic20_ledger(
            setup,
            proof_load,
            parse,
            transcript,
            terminal,
            relation,
            openings,
            queries,
            verifier_return,
            post,
            "single literal tag-43 instruction; no segmented overlap",
        ))
    }

    let root = workspace_root()?;
    let proof_path =
        root.join("results/stage2/proofs/state_only_width28_global_inactive_p20_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read profile20 fixture {}", proof_path.display()))?;
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/state-only/width28/global-copy-inactive-hiding/v1").into();
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
        index: 0x5_4321,
    };
    let note = note_commitment(
        &derive_owner_key(&nullifier_key),
        value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
    let public = SpendPublic {
        anchor: merkle_root(note, &path).map_err(|error| anyhow!("anchor: {error:?}"))?,
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output,
        asset_id,
        fee: 1,
    };
    let output_anchor = merkle_root(output, &path)
        .map_err(|error| anyhow!("output replacement root: {error:?}"))?;
    let statement = AtomicPaymentStatementV3 {
        pool: [0u8; 32],
        sequence: 0,
        spend: public.clone(),
        output_anchor,
    };
    let (prefix, _) = StateOnlyCandidatePrefix::parse_from_proof(&proof)
        .map_err(|error| anyhow!("parse profile20 fixture: {error:?}"))?;
    ensure!(
        prefix.shape == STATE_ONLY_RATE512_SHAPE,
        "fixture is not profile20"
    );
    let schedule = run_state_only_transcript_schedule_host_unmined_for_diagnostics(
        HOST_HASH,
        &prefix,
        &statement_digest,
    )
    .map_err(|error| anyhow!("profile20 transcript: {error:?}"))?;
    let values: Box<[aspis_core::field::QM31; STATE_ONLY_STATEMENT_VALUE_COUNT]> = (0
        ..STATE_ONLY_STATEMENT_VALUE_COUNT)
        .map(|index| prefix.statement_evaluation(index).unwrap())
        .collect::<Vec<_>>()
        .into_boxed_slice()
        .try_into()
        .map_err(|_| anyhow!("profile20 statement values"))?;
    let expected_atomic_terminal = aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_v3(
        &statement,
        &values,
        &schedule.prefix.z,
        schedule.prefix.lambda,
        schedule.prefix.chi,
        schedule.prefix.batching.theta,
        &schedule.prefix.batching.zerocheck_point,
        schedule.prefix.batching.mu,
        schedule.prefix.eta,
    )
    .map_err(|error| anyhow!("atomic terminal: {error:?}"))?;
    let mut expected_bytes = [0u8; 16];
    expected_atomic_terminal.write_le_bytes(&mut expected_bytes);
    let output_anchor_bytes = aspis_statement::encode_digest_canonical(&output_anchor);

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let make_instruction = |expected_atomic_terminal| -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::AtomicStateOnlyProfile20CostCandidate {
                statement_digest,
                public_input: public_bytes(&public),
                output_anchor: output_anchor_bytes,
                expected_atomic_terminal,
            })?,
        })
    };
    let simulate = |instruction: Instruction| -> Result<SimulationResult> {
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        rpc.simulate_verbose(&transaction)
    };
    let literal = simulate(make_instruction(expected_bytes)?)?;
    let markers = parse_cu_markers(&literal.logs, "aspis-cu:");
    let literal_ledger = literal
        .units
        .and_then(|total| literal_ledger(&markers, total));
    let mut wrong = expected_bytes;
    wrong[0] ^= 1;
    let wrong_result = simulate(make_instruction(wrong)?)?;
    ensure!(wrong_result.err.is_some(), "wrong atomic terminal accepted");

    let base_artifact: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/state_only_width28_global_inactive.json"),
    )?)?;
    let base = base_artifact["rows"]
        .as_array()
        .and_then(|rows| rows.iter().find(|row| row["profile_id"] == 20))
        .and_then(|row| row["overlap_ledger"].as_object())
        .context("profile20 overlap ledger is not available")?;
    let old = |field: &str| -> Result<u64> {
        base.get(field)
            .and_then(Value::as_u64)
            .with_context(|| format!("profile20 ledger field {field}"))
    };
    let setup = u64::from(VERIFY_CU_LIMIT)
        .checked_sub(markers.first().context("atomic20 first marker")?.remaining)
        .unwrap();
    let overlap_substituted_ledger = make_atomic20_ledger(
        setup,
        marker_delta(&markers, "atomic20_proof_loaded").context("proof load")?,
        marker_delta(&markers, "atomic20_parse_done").context("parse")?,
        marker_delta(&markers, "atomic20_transcript_done").context("transcript")?,
        marker_delta(&markers, "atomic20_terminal_done").context("atomic terminal")?,
        old("relation_including_reusable_query_powers_cu")?,
        old("merkle_openings_cu")?,
        old("query_arithmetic_cu")?,
        old("verifier_return_cu")?,
        old("post_last_marker_cu")?,
        "tag43 measured setup/load/parse/transcript/atomic-terminal + profile20 tag40 measured overlap-subtracted relation/openings/queries/return/post",
    );
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    let expected_hex = expected_bytes
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    Ok(AtomicProfile20CostSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile20-cost".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 43,
        profile_id: 20,
        rho: "1/512",
        query_count: 16,
        proof_bytes: proof.len(),
        proof_sha256,
        expected_atomic_terminal_hex: expected_hex,
        literal_simulation_cu: literal.units,
        literal_simulation_error: literal.err.map(|error| format!("{error:?}")),
        literal_markers: markers,
        literal_ledger,
        headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT)
            - overlap_substituted_ledger.overlap_reconciled_total_cu as i64,
        overlap_substituted_ledger,
        wrong_terminal_rejected: true,
        sound_acceptance_complete: false,
        blockers: vec![
            "expected atomic terminal is diagnostic input, not the proof transcript's masked terminal claim".to_string(),
            "committed fixture is the existing state-only trace, not atomic_state_only_trace_v3".to_string(),
            "atomic hiding factors and complete-view rank are not repinned".to_string(),
            "no atomic prover constructs the rank-74 helper and atomic zerocheck relation".to_string(),
        ],
        notes: vec![
            "Tag43 executes the full atomic terminal instead of the old terminal, then the unchanged relation, openings, and all profile20 queries. It has no writable accounts or mutation path.".to_string(),
            "The overlap ledger never adds tag42's 26,272-CU saving: rank74 is already inside the measured atomic terminal.".to_string(),
            "Literal tag43 CU and the measurement-vs-measurement overlap substitution are separate; neither is labeled a sound integrated verifier.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile20_acceptance() -> Result<AtomicProfile20AcceptanceSummary> {
    use aspis_core::field::M31;
    use aspis_core::state_only_prefix::{STATE_ONLY_PREFIX_OFFSETS, STATE_ONLY_RATE512_SHAPE};
    use aspis_prover::state_only_candidate_prefix::StateOnlyPowMode;
    use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
    use aspis_prover::state_only_proof::build_hiding_atomic_state_only_proof_v3;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, note_commitment, output_commitment,
        verify_atomic_state_only_candidate_unmined_for_diagnostics_v3,
        verify_atomic_state_only_candidate_v3, AtomicPaymentStatementV3, Digest, MerklePath,
        SpendPublic, SpendWitness,
    };
    use sha2::{Digest as _, Sha256};

    struct MeasurementAtomicProof {
        bytes: Vec<u8>,
        pow_valid: bool,
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }
    fn fixture() -> Result<(AtomicPaymentStatementV3, SpendWitness)> {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
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
        let statement = AtomicPaymentStatementV3 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &witness.merkle_path)
                    .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path)
                .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
        };
        Ok((statement, witness))
    }
    fn public_bytes(public: &SpendPublic) -> [u8; 104] {
        let mut output = [0u8; 104];
        for (index, value) in public
            .anchor
            .iter()
            .chain(&public.nullifier)
            .chain(&public.output_commitment)
            .chain(core::iter::once(&public.asset_id))
            .enumerate()
        {
            output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        output[100..].copy_from_slice(&public.fee.to_le_bytes());
        output
    }
    fn marker_delta(markers: &[CuMarker], label: &str) -> Option<u64> {
        markers
            .iter()
            .find(|marker| marker.label == label)?
            .delta_from_previous?
            .try_into()
            .ok()
    }
    fn marker_span(markers: &[CuMarker], start: &str, end: &str) -> Option<u64> {
        let start = markers
            .iter()
            .find(|marker| marker.label == start)?
            .remaining;
        let end = markers.iter().find(|marker| marker.label == end)?.remaining;
        start.checked_sub(end)
    }
    fn literal_ledger(markers: &[CuMarker], total: u64) -> Option<AtomicProfile20CostLedger> {
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.first()?.remaining)?;
        let proof_load = marker_delta(markers, "atomic46_proof_loaded")?;
        let parse = marker_delta(markers, "atomic46_parse_done")?;
        let transcript = marker_delta(markers, "atomic46_transcript_done")?;
        let terminal = marker_span(
            markers,
            "atomic46_transcript_done",
            "atomic46_terminal_done",
        )?;
        let relation = marker_delta(markers, "atomic46_relation_done")?;
        let openings = marker_delta(markers, "atomic46_openings_parse_done")?;
        let queries = marker_delta(markers, "atomic46_queries_done")?;
        let verifier_return = marker_delta(markers, "atomic46_done")?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.last()?.remaining)?;
        let post = total.checked_sub(through_last)?;
        Some(make_atomic20_ledger(
            setup,
            proof_load,
            parse,
            transcript,
            terminal,
            relation,
            openings,
            queries,
            verifier_return,
            post,
            "single literal tag-46 acceptance-complete read-only instruction; no segmented or cross-artifact substitution",
        ))
    }

    let root = workspace_root()?;
    let (statement, witness) = fixture()?;
    let statement_digest =
        aspis_statement::atomic_payment_statement_digest_v3(&statement, HOST_HASH)
            .map_err(|error| anyhow!("atomic statement digest: {error:?}"))?;
    let statement_digest_sha256 = statement_digest
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let proof_path = root.join("results/stage2/proofs/atomic_state_only_profile20_v3_unmined.bin");
    let reuse_proof = std::env::var_os("ASPIS_ATOMIC20_REUSE_PROOF").is_some();
    let built = if reuse_proof {
        MeasurementAtomicProof {
            bytes: fs::read(&proof_path)
                .with_context(|| format!("read atomic replay proof {}", proof_path.display()))?,
            pow_valid: false,
        }
    } else {
        let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
        let built = build_hiding_atomic_state_only_proof_v3(
            &statement,
            &witness,
            [20; 32],
            [0xd3; 32],
            &mut nonces,
            STATE_ONLY_RATE512_SHAPE,
            HOST_HASH,
            StateOnlyPowMode::UnminedZero,
        )
        .map_err(|error| anyhow!("build atomic profile20 proof: {error:?}"))?;
        MeasurementAtomicProof {
            bytes: built.bytes,
            pow_valid: built.pow_valid,
        }
    };
    ensure!(
        !built.pow_valid,
        "diagnostic fixture unexpectedly reports mined PoW"
    );
    ensure!(
        built.bytes.len() == 56_044,
        "atomic profile20 proof geometry drift"
    );
    verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
        &built.bytes,
        &statement,
        HOST_HASH,
        None,
    )
    .map_err(|error| anyhow!("host atomic acceptance: {error:?}"))?;
    ensure!(
        verify_atomic_state_only_candidate_v3(&built.bytes, &statement, HOST_HASH).is_err(),
        "unmined diagnostic fixture passed production PoW"
    );

    let mut public_variants = Vec::new();
    let mut changed = statement.clone();
    changed.pool[0] ^= 1;
    public_variants.push(changed);
    let mut changed = statement.clone();
    changed.sequence += 1;
    public_variants.push(changed);
    for selector in 0..4 {
        let mut changed = statement.clone();
        let value = match selector {
            0 => &mut changed.spend.anchor,
            1 => &mut changed.spend.nullifier,
            2 => &mut changed.spend.output_commitment,
            _ => &mut changed.output_anchor,
        };
        value[0] = value[0].add(M31::ONE);
        public_variants.push(changed);
    }
    let mut changed = statement.clone();
    changed.spend.asset_id = changed.spend.asset_id.add(M31::ONE);
    public_variants.push(changed);
    let mut changed = statement.clone();
    changed.spend.fee += 1;
    public_variants.push(changed);
    for (index, changed) in public_variants.iter().enumerate() {
        ensure!(
            verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
                &built.bytes,
                changed,
                HOST_HASH,
                None,
            )
            .is_err(),
            "accepted changed atomic public field {index} on host"
        );
    }

    let corruption_offsets = [
        STATE_ONLY_PREFIX_OFFSETS.initial_mask_claim_start,
        STATE_ONLY_PREFIX_OFFSETS.sumcheck_start,
        STATE_ONLY_PREFIX_OFFSETS.statement_evaluations_start,
        STATE_ONLY_PREFIX_OFFSETS.rounds[0].ood_values_start,
        STATE_ONLY_PREFIX_OFFSETS.rounds[2].sumcheck_start,
        STATE_ONLY_PREFIX_OFFSETS.final_polynomial_start,
        STATE_ONLY_PREFIX_OFFSETS.openings_start + 2,
        built.bytes.len() - 1,
    ];
    for &offset in &corruption_offsets {
        let mut corrupt = built.bytes.clone();
        corrupt[offset] ^= 1;
        ensure!(
            verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
                &corrupt, &statement, HOST_HASH, None,
            )
            .is_err(),
            "accepted atomic proof corruption at {offset} on host"
        );
    }

    if let Some(parent) = proof_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&proof_path, &built.bytes)?;
    let proof_sha256 = Sha256::digest(&built.bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &built.bytes, true)?;
    let output_anchor = aspis_statement::encode_digest_canonical(&statement.output_anchor);
    let make_instruction = |candidate: &AtomicPaymentStatementV3| -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data: to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile20V3 {
                pool: candidate.pool,
                sequence: candidate.sequence,
                public_input: public_bytes(&candidate.spend),
                output_anchor: if candidate.output_anchor == statement.output_anchor {
                    output_anchor
                } else {
                    aspis_statement::encode_digest_canonical(&candidate.output_anchor)
                },
                diagnostic_unmined: true,
            })?,
        })
    };
    let simulate = |instruction: Instruction| -> Result<SimulationResult> {
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        rpc.simulate_verbose(&transaction)
    };
    let literal = simulate(make_instruction(&statement)?)?;
    ensure!(
        literal.err.is_none(),
        "tag46 atomic acceptance failed: {:?}",
        literal.err
    );
    let markers = parse_cu_markers(&literal.logs, "aspis-cu:");
    let literal_ledger = literal
        .units
        .and_then(|total| literal_ledger(&markers, total));
    let total = literal.units.context("tag46 simulation omitted CU")?;
    let ledger = literal_ledger
        .as_ref()
        .context("tag46 did not emit a complete literal phase ledger")?;
    ensure!(
        ledger.overlap_reconciled_total_cu == total,
        "tag46 marker ledger does not reconcile to literal simulation"
    );
    let optimized_copy_patterns_cu = marker_delta(&markers, "atomic46_terminal_copy_patterns")
        .context("tag46 atomic copy-pattern marker")?;
    let selected_shared_prepared_cu = marker_delta(&markers, "atomic46_terminal_prepared")
        .context("tag46 atomic prepared marker")?;
    let selected_shared_copy_routing_cu = marker_delta(&markers, "atomic46_terminal_copy_routing")
        .context("tag46 atomic copy-routing marker")?;
    let wrong_public = simulate(make_instruction(&public_variants[1])?)?;
    ensure!(
        wrong_public.err.is_some(),
        "changed atomic sequence accepted on SBF"
    );

    Ok(AtomicProfile20AcceptanceSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: if reuse_proof {
            "NO_DNA=1 ASPIS_ATOMIC20_REUSE_PROOF=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile20-acceptance"
        } else {
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile20-acceptance"
        }.to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 46,
        profile_id: 20,
        rho: "1/512",
        query_count: 16,
        proof_bytes: built.bytes.len(),
        proof_sha256,
        statement_digest_sha256,
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        host_read_only_acceptance: true,
        host_public_field_teeth: public_variants.len(),
        host_corruption_teeth: corruption_offsets.len(),
        literal_simulation_cu: literal.units,
        literal_simulation_error: literal.err.map(|error| format!("{error:?}")),
        literal_markers: markers,
        literal_ledger,
        headroom_under_1_4m_cu: Some(i64::from(VERIFY_CU_LIMIT) - total as i64),
        pre_rewrite_literal_simulation_cu: 1_279_180,
        pre_rewrite_atomic_terminal_cu: 484_442,
        pre_rewrite_copy_patterns_cu: 82_582,
        optimized_copy_patterns_cu,
        pre_rewrite_prepared_cu: 66_973,
        selected_shared_prepared_cu,
        pre_rewrite_copy_routing_cu: 108_007,
        rank74_lazy_copy_routing_cu: 79_334,
        selected_shared_copy_routing_cu,
        post_pattern_literal_simulation_cu: 1_217_906,
        rank74_lazy_literal_simulation_cu: 1_189_233,
        literal_savings_vs_pre_rewrite_cu: 1_279_180i64 - total as i64,
        random_qm31_pattern_identity_points: 64,
        wrong_public_field_rejected_sbf: true,
        production_pow_mined: false,
        read_only_acceptance_complete: true,
        live_mutation_enabled: false,
        atomic_hiding_rank_complete: false,
        notes: vec![
            "Tag46 verifies the actual 56,044-byte atomic-v3 profile20 proof, including its transcript-bound masked terminal, exact 183-link atomic copy polynomial, relation, Merkle openings, and every q16 query. No expected terminal is supplied out of band.".to_string(),
            "The CU number is the literal single-instruction simulation and its marker ledger reconciles exactly; no segmented, overlap-subtracted, or cross-artifact phase is substituted.".to_string(),
            "Five shared QM31 dots reconstruct all fifteen generated patterns, four M31 coefficient products are lazily reduced per routing limb, and the selected rank-103 routing partition reuses the semantic selector tensor. Together these exact rewrites cut tag46 by 99,729 CU; the generated minimum-rank rank-74 path remains an independent reference.".to_string(),
            "Seven terminal guards cover 64 fresh random-QM31 pattern identities, semantic-tensor/selected-partition identity, all 1,024 active/inactive rows, rank-74 routing versus the independent 183-link walk, diagnostic/production terminal identity, constants provenance, and every compiled-copy corruption tooth.".to_string(),
            "The diagnostic fixture is intentionally unmined: nonce absorption and all downstream Fiat-Shamir challenges execute, but production acceptance rejects it at the PoW predicate.".to_string(),
            "This instruction is read-only and rejects writable proof accounts. Pool/nullifier mutation remains disabled until the atomic complete-view hiding-rank artifact and live account-transition teeth are green.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile20_mutation() -> Result<AtomicProfile20MutationSummary> {
    use aspis_core::field::M31;
    use aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, encode_digest_canonical, note_commitment,
        output_commitment, verify_atomic_state_only_candidate_unmined_for_diagnostics_v3,
        verify_atomic_state_only_candidate_v3, AtomicPaymentStatementV3, Digest, MerklePath,
        SpendPublic, SpendWitness,
    };
    use aspis_verifier::atomic_payment::{
        atomic_nullifier_address, AtomicPaymentPublicInputs, AtomicPoolStateV1,
        ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED, ATOMIC_NULLIFIER_MAGIC, ATOMIC_NULLIFIER_MARKER_LEN,
        ATOMIC_NULLIFIER_VERSION, ATOMIC_POOL_STATE_LEN,
    };
    use sha2::{Digest as _, Sha256};

    const READ_ONLY_TAG46_CU: u64 = 1_179_451;
    const DIAGNOSTIC_FEATURES: [&str; 2] = [
        "diagnostic-unmined-mutation",
        "profile20-mutation-candidate",
    ];

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture() -> Result<(AtomicPaymentStatementV3, SpendWitness)> {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
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
        Ok((
            AtomicPaymentStatementV3 {
                pool: [0x5a; 32],
                sequence: 73,
                spend: SpendPublic {
                    anchor: atomic_merkle_root_v3(input, &witness.merkle_path)
                        .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
                    nullifier: derive_nullifier(&nullifier_key, &input_salt),
                    output_commitment: output,
                    asset_id,
                    fee: 1,
                },
                output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path)
                    .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
            },
            witness,
        ))
    }

    fn public_inputs(statement: &AtomicPaymentStatementV3) -> AtomicPaymentPublicInputs {
        AtomicPaymentPublicInputs {
            current_anchor: encode_digest_canonical(&statement.spend.anchor),
            nullifier: encode_digest_canonical(&statement.spend.nullifier),
            output_commitment: encode_digest_canonical(&statement.spend.output_commitment),
            output_anchor: encode_digest_canonical(&statement.output_anchor),
            asset_id: statement.spend.asset_id.0,
            fee: statement.spend.fee,
        }
    }

    fn instruction_data(public: &AtomicPaymentPublicInputs, diagnostic: bool) -> Result<Vec<u8>> {
        let instruction = if diagnostic {
            AspisInstruction::MeasureAtomicStateOnlyProfile20MutationV3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        } else {
            AspisInstruction::ApplyAtomicStateOnlyProfile20V3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        };
        Ok(to_vec(&instruction)?)
    }

    fn transition_instruction(
        proof: Pubkey,
        pool: Pubkey,
        marker: Pubkey,
        payer: Pubkey,
        public: &AtomicPaymentPublicInputs,
        diagnostic: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![
                AccountMeta::new_readonly(proof, false),
                AccountMeta::new(pool, false),
                AccountMeta::new(marker, false),
                AccountMeta::new(payer, true),
                AccountMeta::new_readonly(solana_sdk::system_program::id(), false),
            ],
            data: instruction_data(public, diagnostic)?,
        })
    }

    fn signed_transition(
        payer: &Keypair,
        instruction: Instruction,
        blockhash: solana_sdk::hash::Hash,
    ) -> Transaction {
        Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        )
    }

    fn patch_proof_byte(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        offset: usize,
        byte: u8,
    ) -> Result<()> {
        let instruction = proof_instruction(
            &payer.pubkey(),
            proof_account,
            &AspisInstruction::UploadChunk {
                offset: offset as u32,
                chunk: vec![byte],
            },
        )?;
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[instruction],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        );
        rpc.send_and_confirm(&transaction)?;
        Ok(())
    }

    fn marker_is_exact(snapshot: &RpcAccountSnapshot, pool: Pubkey, nullifier: &[u8; 32]) -> bool {
        snapshot.owner == aspis_verifier::id()
            && snapshot.data.len() == ATOMIC_NULLIFIER_MARKER_LEN
            && snapshot.data[0..4] == ATOMIC_NULLIFIER_MAGIC
            && snapshot.data[4] == ATOMIC_NULLIFIER_VERSION
            && snapshot.data[5..8] == [0u8; 3]
            && snapshot.data[8..40] == pool.to_bytes()
            && snapshot.data[40..72] == *nullifier
    }

    fn marker_span(markers: &[CuMarker], start: &str, end: &str) -> Option<u64> {
        let start = markers
            .iter()
            .find(|marker| marker.label == start)?
            .remaining;
        let end = markers.iter().find(|marker| marker.label == end)?.remaining;
        start.checked_sub(end)
    }

    fn mutation_ledger(
        markers: &[CuMarker],
        total: u64,
        program_owned: bool,
    ) -> Option<AtomicProfile20MutationLedger> {
        let first = markers.first()?;
        let last = markers.last()?;
        let account_label = if program_owned {
            "atomic48_accounts_validated_program_owned"
        } else {
            "atomic48_accounts_validated_system_owned"
        };
        let marker_label = if program_owned {
            "atomic48_program_marker_ready"
        } else {
            "atomic48_system_marker_created"
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(first.remaining)?;
        let validation = marker_span(markers, "atomic48_instruction_start", account_label)?;
        let digest = marker_span(markers, account_label, "atomic48_statement_digest_done")?;
        let verifier = marker_span(
            markers,
            "atomic48_statement_digest_done",
            "atomic48_proof_verified",
        )?;
        let marker = marker_span(markers, "atomic48_proof_verified", marker_label)?;
        let recheck = marker_span(markers, marker_label, "atomic48_state_rechecked")?;
        let writes = marker_span(
            markers,
            "atomic48_state_rechecked",
            "atomic48_state_applied",
        )?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(last.remaining)?;
        let post = total.checked_sub(through_last)?;
        let reconciled = setup
            .checked_add(validation)?
            .checked_add(digest)?
            .checked_add(verifier)?
            .checked_add(marker)?
            .checked_add(recheck)?
            .checked_add(writes)?
            .checked_add(post)?;
        Some(AtomicProfile20MutationLedger {
            transaction_setup_cu: setup,
            account_validation_cu: validation,
            statement_decode_and_digest_cu: digest,
            exact_profile20_verifier_cu: verifier,
            marker_prepare_or_cpi_cu: marker,
            mutable_state_recheck_cu: recheck,
            final_account_writes_cu: writes,
            post_last_marker_cu: post,
            reconciled_total_cu: reconciled,
            formula: format!(
                "{setup} + {validation} + {digest} + {verifier} + {marker} + {recheck} + {writes} + {post}"
            ),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn run_path(
        root: &Path,
        so: &Path,
        proof: &[u8],
        statement: &AtomicPaymentStatementV3,
        preowned_marker: bool,
        exercise_candidate_tag47: bool,
        exercise_concurrency: bool,
    ) -> Result<(AtomicProfile20MutationPathSummary, bool, bool)> {
        let public = public_inputs(statement);
        let pool_key = Pubkey::new_from_array(statement.pool);
        let (marker_key, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
        let mut pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV1 {
            sequence: statement.sequence,
            anchor: public.current_anchor,
        }
        .encode(&mut pool_bytes)?;
        let pool_fixture = write_validator_account_fixture(
            root,
            if preowned_marker {
                "atomic-mutation-program-pool"
            } else {
                "atomic-mutation-system-pool"
            },
            pool_key,
            aspis_verifier::id(),
            &pool_bytes,
        )?;
        let mut fixtures = vec![(pool_key, pool_fixture)];
        if preowned_marker {
            let marker_fixture = write_validator_account_fixture(
                root,
                "atomic-mutation-program-marker",
                marker_key,
                aspis_verifier::id(),
                &[0u8; ATOMIC_NULLIFIER_MARKER_LEN],
            )?;
            fixtures.push((marker_key, marker_fixture));
        }

        let validator = start_validator_with_accounts(root, so, &fixtures)?;
        let rpc = Rpc {
            url: validator.rpc_url.clone(),
            http: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()?,
        };
        let payer = Keypair::new();
        rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, proof, true)?;

        let clean_instruction = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            true,
        )?;
        let clean_tx =
            signed_transition(&payer, clean_instruction.clone(), rpc.latest_blockhash()?);
        let clean = rpc.simulate_verbose(&clean_tx)?;
        ensure!(
            clean.err.is_none(),
            "{} marker clean mutation simulation failed: {:?}",
            if preowned_marker {
                "program-owned"
            } else {
                "system-owned"
            },
            clean.err
        );
        let total = clean
            .units
            .context("atomic mutation simulation omitted CU")?;
        let markers = parse_cu_markers(&clean.logs, "aspis-cu:");
        let ledger = mutation_ledger(&markers, total, preowned_marker)
            .context("atomic mutation marker ledger incomplete")?;
        ensure!(
            ledger.reconciled_total_cu == total,
            "atomic mutation ledger did not reconcile"
        );

        let pool_before =
            rpc_account_snapshot(&rpc, &pool_key)?.context("preloaded pool account missing")?;
        let marker_before = rpc_account_snapshot(&rpc, &marker_key)?;
        if preowned_marker {
            ensure!(
                marker_before
                    .as_ref()
                    .is_some_and(|snapshot| snapshot.owner == aspis_verifier::id()
                        && snapshot.data == [0u8; ATOMIC_NULLIFIER_MARKER_LEN]),
                "program-owned marker fixture is not exact zeroed state"
            );
        } else {
            ensure!(
                marker_before.is_none(),
                "system-owned create PDA unexpectedly exists"
            );
        }

        let corruption_offset = STATE_ONLY_PREFIX_OFFSETS.sumcheck_start;
        let original_byte = proof[corruption_offset];
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte ^ 1,
        )?;
        let corrupt_instruction = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            true,
        )?;
        let corrupt_tx = signed_transition(&payer, corrupt_instruction, rpc.latest_blockhash()?);
        let corrupt = rpc.simulate_verbose(&corrupt_tx)?;
        let corrupt_rejected = corrupt.err.is_some()
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_before)
            && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
        ensure!(corrupt_rejected, "corrupt proof changed atomic state");
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte,
        )?;

        let mut candidate_rejects_unmined = true;
        let mut candidate_rollback = true;
        if exercise_candidate_tag47 {
            let candidate_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                false,
            )?;
            let candidate_tx =
                signed_transition(&payer, candidate_instruction, rpc.latest_blockhash()?);
            let candidate = rpc.simulate_verbose(&candidate_tx)?;
            candidate_rejects_unmined = candidate.err.is_some();
            candidate_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref()
                == Some(&pool_before)
                && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
            ensure!(candidate_rejects_unmined, "tag47 accepted unmined proof");
            ensure!(candidate_rollback, "tag47 PoW rejection changed state");
        }

        let concurrent_exactly_one = if exercise_concurrency {
            let second_payer = Keypair::new();
            rpc.airdrop_and_wait(&second_payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
            let first_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?;
            let second_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                second_payer.pubkey(),
                &public,
                true,
            )?;
            let blockhash = rpc.latest_blockhash()?;
            let first_tx = signed_transition(&payer, first_instruction, blockhash);
            let second_tx = signed_transition(&second_payer, second_instruction, blockhash);
            let rpc_a = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let rpc_b = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let (first_result, second_result) = thread::scope(|scope| {
                let first = scope.spawn(|| rpc_a.send_and_confirm(&first_tx));
                let second = scope.spawn(|| rpc_b.send_and_confirm(&second_tx));
                (first.join().unwrap(), second.join().unwrap())
            });
            let exactly_one = first_result.is_ok() ^ second_result.is_ok();
            ensure!(
                exactly_one,
                "concurrent atomic spends did not commit exactly once"
            );
            Some(exactly_one)
        } else {
            rpc.send_and_confirm(&clean_tx)?;
            None
        };

        let pool_after = rpc_account_snapshot(&rpc, &pool_key)?
            .context("pool account disappeared after transition")?;
        let marker_after = rpc_account_snapshot(&rpc, &marker_key)?
            .context("nullifier marker missing after transition")?;
        let decoded_pool = AtomicPoolStateV1::decode(&pool_after.data)?;
        let sequence_advanced = decoded_pool.sequence == statement.sequence + 1;
        let anchor_replaced = decoded_pool.anchor == public.output_anchor;
        let marker_written = marker_is_exact(&marker_after, pool_key, &public.nullifier);
        ensure!(sequence_advanced && anchor_replaced && marker_written);

        let mut duplicate_public = public;
        duplicate_public.current_anchor = duplicate_public.output_anchor;
        let duplicate_instruction = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &duplicate_public,
            true,
        )?;
        let duplicate_tx =
            signed_transition(&payer, duplicate_instruction, rpc.latest_blockhash()?);
        let duplicate_rejected = rpc.send_and_confirm(&duplicate_tx).is_err();
        let duplicate_no_mutation = duplicate_rejected
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_after)
            && rpc_account_snapshot(&rpc, &marker_key)?.as_ref() == Some(&marker_after);
        ensure!(duplicate_no_mutation, "duplicate changed atomic state");

        drop(validator);
        Ok((
            AtomicProfile20MutationPathSummary {
                marker_path: if preowned_marker {
                    "program_owned_zeroed"
                } else {
                    "canonical_system_owned_create"
                },
                literal_simulation_cu: total,
                headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
                incremental_over_tag46_cu: total as i64 - READ_ONLY_TAG46_CU as i64,
                markers,
                ledger,
                clean_simulation_accepted: true,
                corrupt_proof_rejected_without_mutation: corrupt_rejected,
                committed_transition_succeeded: true,
                pool_sequence_advanced_once: sequence_advanced,
                pool_anchor_replaced: anchor_replaced,
                nullifier_marker_written: marker_written,
                duplicate_rejected_without_second_mutation: duplicate_no_mutation,
                concurrent_exactly_one_committed: concurrent_exactly_one,
            },
            candidate_rejects_unmined,
            candidate_rollback,
        ))
    }

    let root = workspace_root()?;
    let proof_path = root.join("results/stage2/proofs/atomic_state_only_profile20_v3_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read atomic proof {}", proof_path.display()))?;
    ensure!(
        proof.len() == 56_044,
        "atomic profile20 proof geometry drift"
    );
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    ensure!(
        proof_sha256 == "fdd1097f702b411b6bcd26d0e195322d7683ff93ec4cb70828b9459fe7cef007",
        "atomic profile20 proof KAT changed"
    );
    let (statement, _witness) = fixture()?;
    verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
        &proof, &statement, HOST_HASH, None,
    )
    .map_err(|error| anyhow!("atomic fixture replay: {error:?}"))?;
    ensure!(
        verify_atomic_state_only_candidate_v3(&proof, &statement, HOST_HASH).is_err(),
        "unmined fixture passed production PoW"
    );

    let default_tag47 = instruction_data(&public_inputs(&statement), false)?;
    let default_tag47_fail_closed_host =
        aspis_verifier::process_instruction(&aspis_verifier::id(), &[], &default_tag47)
            == Err(solana_sdk::program_error::ProgramError::Custom(
                ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
    ensure!(
        default_tag47_fail_closed_host,
        "default tag47 is not fail-closed"
    );

    let diagnostic_so = build_sbf_with_features(
        &root,
        &DIAGNOSTIC_FEATURES,
        "aspis_verifier_atomic_mutation_diagnostic.so",
    )?;
    let (program_path, candidate_rejects_unmined_sbf, candidate_tag47_rollback_green) =
        run_path(&root, &diagnostic_so, &proof, &statement, true, true, false)?;
    let (system_path, _, _) = run_path(
        &root,
        &diagnostic_so,
        &proof,
        &statement,
        false,
        false,
        true,
    )?;

    Ok(AtomicProfile20MutationSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile20-mutation".to_string(),
        validator_version: validator_version(),
        production_instruction_wire_ordinal: 47,
        diagnostic_instruction_wire_ordinal: 48,
        diagnostic_sbf_features: DIAGNOSTIC_FEATURES.to_vec(),
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        proof_sha256,
        proof_unmined: true,
        production_pow_bypass_exposed: false,
        default_tag47_fail_closed_host,
        candidate_tag47_rejects_unmined_sbf: candidate_rejects_unmined_sbf,
        candidate_tag47_rollback_green,
        paths: vec![program_path, system_path],
        production_profile21_mutation_enabled: false,
        atomic_complete_view_hiding_closed: false,
        notes: vec![
            "Default SBF builds keep tag47 fail-closed while atomic complete-view hiding is red. Its nondefault candidate arm has no diagnostic selector and rejects the committed unmined proof through the exact production PoW verifier before any CPI or write.".to_string(),
            "Tag48 exists only in the nondefault diagnostic-unmined-mutation build. It uses the same proof bytes, parser, transcript, terminal, relation, openings, and q16 verifier core as tag46, then executes the exact account-transition kernel for CU measurement.".to_string(),
            "Program-owned-zeroed and canonical zero-lamport System-owned PDA creation are measured separately. Each literal marker ledger reconciles to its single simulation total; no overlap substitution is used.".to_string(),
            "Rollback, duplicate, and writable-lock concurrency teeth inspect exact pool and nullifier account images. The System-owned path races two differently signed transactions and requires exactly one commit.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile21_acceptance() -> Result<AtomicProfile21AcceptanceSummary> {
    use aspis_core::field::M31;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, encode_digest_canonical, note_commitment,
        output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic,
    };
    use sha2::{Digest as _, Sha256};

    const READ_ONLY_BRIDGE_CU: u64 = 1_363_429;
    const PROGRAM_MARKER_BRIDGE_CU: u64 = 1_373_158;
    const SYSTEM_CREATE_BRIDGE_CU: u64 = 1_375_491;
    const PROFILE21_BASIS_FINGERPRINT_PIN: u64 = 0xceb3_5dd3_ee50_e051;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn statement() -> Result<AtomicPaymentStatementV3> {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
        };
        let input = note_commitment(
            &derive_owner_key(&nullifier_key),
            value,
            asset_id,
            &input_salt,
        );
        let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
        Ok(AtomicPaymentStatementV3 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &path)
                    .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &path)
                .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
        })
    }

    fn public_bytes(public: &SpendPublic) -> [u8; 104] {
        let mut output = [0u8; 104];
        for (index, value) in public
            .anchor
            .iter()
            .chain(&public.nullifier)
            .chain(&public.output_commitment)
            .chain(core::iter::once(&public.asset_id))
            .enumerate()
        {
            output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        output[100..].copy_from_slice(&public.fee.to_le_bytes());
        output
    }

    fn instruction(
        proof_account: Pubkey,
        statement: &AtomicPaymentStatementV3,
        diagnostic_unmined: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account, false)],
            data: to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile21V3 {
                pool: statement.pool,
                sequence: statement.sequence,
                public_input: public_bytes(&statement.spend),
                output_anchor: encode_digest_canonical(&statement.output_anchor),
                diagnostic_unmined,
            })?,
        })
    }

    fn ledger(markers: &[CuMarker], total: u64) -> Option<AtomicProfile21AcceptanceLedger> {
        let delta = |label: &str| {
            markers
                .iter()
                .find(|marker| marker.label == label)?
                .delta_from_previous?
                .try_into()
                .ok()
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.first()?.remaining)?;
        let proof_load = delta("atomic50_proof_loaded")?;
        let parse = delta("atomic50_parse_base")?;
        let transcript = delta("atomic50_transcript_base")?;
        let terminal = delta("atomic50_terminal")?;
        let relation = delta("atomic50_relation")?;
        let existing_openings = delta("atomic50_existing_openings")?;
        let existing_queries = delta("atomic50_existing_queries")?;
        let source_xf = delta("atomic50_source_xf_shared_c2")?;
        let source_work = delta("atomic50_source_work")?;
        let translated = delta("atomic50_translated_splice")?;
        let direct_u_query = delta("atomic50_direct_u_query")?;
        let final_query = delta("atomic50_final_query_work")?;
        let completion = delta("atomic50_core_complete")?;
        let wrapper_return = delta("atomic50_done")?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.last()?.remaining)?;
        let post = total.checked_sub(through_last)?;
        let buckets = [
            setup,
            proof_load,
            parse,
            transcript,
            terminal,
            relation,
            existing_openings,
            existing_queries,
            source_xf,
            source_work,
            translated,
            direct_u_query,
            final_query,
            completion,
            wrapper_return,
            post,
        ];
        Some(AtomicProfile21AcceptanceLedger {
            transaction_setup_cu: setup,
            proof_load_cu: proof_load,
            parse_base_cu: parse,
            transcript_base_cu: transcript,
            terminal_cu: terminal,
            relation_cu: relation,
            existing_openings_cu: existing_openings,
            existing_queries_cu: existing_queries,
            source_xf_shared_c2_cu: source_xf,
            source_work_cu: source_work,
            translated_splice_cu: translated,
            direct_u_query_cu: direct_u_query,
            final_query_work_cu: final_query,
            completion_cu: completion,
            wrapper_return_cu: wrapper_return,
            post_last_marker_cu: post,
            reconciled_total_cu: buckets.iter().sum(),
            formula: buckets
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(" + "),
        })
    }

    let root = workspace_root()?;
    let masked_switch_basis_fingerprint =
        aspis_core::state_only_masked_switch_basis::MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT;
    ensure!(
        masked_switch_basis_fingerprint == PROFILE21_BASIS_FINGERPRINT_PIN,
        "profile21 masked-switch basis fingerprint drift"
    );
    let statement = statement()?;
    let proof_path = root.join("results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read integrated profile21 proof {}", proof_path.display()))?;
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();

    let default_data = to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile21V3 {
        pool: statement.pool,
        sequence: statement.sequence,
        public_input: public_bytes(&statement.spend),
        output_anchor: encode_digest_canonical(&statement.output_anchor),
        diagnostic_unmined: true,
    })?;
    let default_tag50_fail_closed_host =
        aspis_verifier::process_instruction(&aspis_verifier::id(), &[], &default_data)
            == Err(solana_sdk::program_error::ProgramError::Custom(
                aspis_verifier::atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
    ensure!(
        default_tag50_fail_closed_host,
        "default tag50 is not fail-closed"
    );

    let so = build_sbf_with_features(
        &root,
        &["profile21-integrated-candidate"],
        "aspis_verifier_atomic_profile21_candidate.so",
    )?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let simulate = |diagnostic_unmined| -> Result<SimulationResult> {
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction(proof_account.pubkey(), &statement, diagnostic_unmined)?,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            rpc.latest_blockhash()?,
        );
        rpc.simulate_verbose(&transaction)
    };
    let production = simulate(false)?;
    ensure!(
        production.err.is_some(),
        "unmined profile21 proof passed production API"
    );
    let diagnostic = simulate(true)?;
    ensure!(
        diagnostic.err.is_none(),
        "integrated profile21 diagnostic failed: {:?}",
        diagnostic.err
    );
    let total = diagnostic.units.context("tag50 simulation omitted CU")?;
    let markers = parse_cu_markers(&diagnostic.logs, "aspis-cu:");
    let ledger = ledger(&markers, total).context("tag50 marker ledger incomplete")?;
    ensure!(ledger.reconciled_total_cu == total, "tag50 ledger mismatch");

    let soundness_audit: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/profile21_soundness_hvzk_audit.json"),
    )?)?;
    let privacy_audit: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/profile21_atomic_hvzk_privacy_audit.json"),
    )?)?;
    let soundness_reduction_complete = soundness_audit["complete_system_claim_quotable"]
        .as_bool()
        .unwrap_or(false);
    let complete_view_hvzk_simulator_complete = privacy_audit
        ["complete_view_hvzk_simulator_complete"]
        .as_bool()
        .unwrap_or(false);

    Ok(AtomicProfile21AcceptanceSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile21-acceptance".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 50,
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        proof_bytes: proof.len(),
        proof_sha256,
        proof_unmined: true,
        masked_switch_basis_fingerprint: format!("0x{masked_switch_basis_fingerprint:016x}"),
        masked_switch_basis_fingerprint_matches_pin: true,
        default_tag50_fail_closed_host,
        production_api_rejected_unmined_sbf: true,
        literal_simulation_cu: total,
        headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
        markers,
        ledger,
        nonintegrated_read_only_bridge_cu: READ_ONLY_BRIDGE_CU,
        nonintegrated_program_marker_bridge_cu: PROGRAM_MARKER_BRIDGE_CU,
        nonintegrated_system_create_bridge_cu: SYSTEM_CREATE_BRIDGE_CU,
        bridge_inputs: vec![
            "read-only tag46=1,179,451 CU".to_string(),
            "fused profile21 increment=214,881 CU".to_string(),
            "shared X/F conservative saving=30,903 CU".to_string(),
            "program-owned mutation increment=9,729 CU".to_string(),
            "System-create mutation increment=12,062 CU".to_string(),
        ],
        soundness_reduction_complete,
        complete_view_hvzk_simulator_complete,
        production_mutation_enabled: false,
        notes: vec![
            "The literal tag50 number replaces all three non-integrated bridges. Its phase ledger is emitted by the single integrated parser/verifier call; no profile20/switch proof-byte splice occurs in this wrapper.".to_string(),
            "Phase attribution is causal and explicit: TranscriptBase includes source/final PoW predicate hashing and q16 sampling; ExistingOpenings authenticates all five salted trees. SourceXfSharedC2 is the entry boundary, and SourceWork prices raw X/F decoding, both alpha0 folds, and the affine delta combination rather than claiming to isolate the earlier transcript predicate.".to_string(),
            "Tag50 is read-only. Default builds remain fail-closed; the candidate build accepts only diagnostic-unmined for CU and the production arm rejects the same fixture at its PoW predicates.".to_string(),
            "A CU fit does not override the soundness or complete-view HVZK audit booleans read from their independent artifacts.".to_string(),
            "The integrated wrapper and measurement harness both hard-bind the shared q16 logical-to-natural basis fingerprint 0xceb35dd3ee50e051; no duplicate transform is defined here.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile22_acceptance() -> Result<AtomicProfile22AcceptanceSummary> {
    use aspis_core::circle_prefix::RATE16_HARDENED_FOLD_POW_BITS;
    use aspis_core::field::M31;
    use aspis_core::state_only_prefix::{
        STATE_ONLY_PROFILE22_BATCH_GRINDING_BITS, STATE_ONLY_PROFILE22_GRINDING_BITS,
    };
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::state_only_profile22::{
        verify_atomic_state_only_profile22_unmined_for_diagnostics_v3,
        verify_atomic_state_only_profile22_v3,
    };
    use aspis_statement::{
        derive_nullifier, derive_owner_key, encode_digest_canonical, note_commitment,
        output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic,
    };
    use sha2::{Digest as _, Sha256};

    const PROOF_BYTES: usize = 56_686;
    const PROOF_SHA256: &str = "77736f0ea30ae9e2516537213e7dce386c9be69e3c772e5b50f03c57892136f8";

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn statement() -> Result<AtomicPaymentStatementV3> {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
        };
        let input = note_commitment(
            &derive_owner_key(&nullifier_key),
            value,
            asset_id,
            &input_salt,
        );
        let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
        Ok(AtomicPaymentStatementV3 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &path)
                    .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &path)
                .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
        })
    }

    fn public_bytes(public: &SpendPublic) -> [u8; 104] {
        let mut output = [0u8; 104];
        for (index, value) in public
            .anchor
            .iter()
            .chain(&public.nullifier)
            .chain(&public.output_commitment)
            .chain(core::iter::once(&public.asset_id))
            .enumerate()
        {
            output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        output[100..].copy_from_slice(&public.fee.to_le_bytes());
        output
    }

    fn instruction(
        proof_account: Pubkey,
        statement: &AtomicPaymentStatementV3,
        diagnostic_unmined: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account, false)],
            data: to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile22V3 {
                pool: statement.pool,
                sequence: statement.sequence,
                public_input: public_bytes(&statement.spend),
                output_anchor: encode_digest_canonical(&statement.output_anchor),
                diagnostic_unmined,
            })?,
        })
    }

    fn ledger(markers: &[CuMarker], total: u64) -> Option<AtomicProfile22AcceptanceLedger> {
        let delta = |label: &str| {
            markers
                .iter()
                .find(|marker| marker.label == label)?
                .delta_from_previous?
                .try_into()
                .ok()
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.first()?.remaining)?;
        let proof_load = delta("atomic56_proof_loaded")?;
        let parsed = delta("atomic56_parsed")?;
        let transcript = delta("atomic56_transcript")?;
        let terminal = delta("atomic56_terminal")?;
        let relation = delta("atomic56_relation")?;
        let openings = delta("atomic56_openings")?;
        let layer0_queries = delta("atomic56_layer0_queries")?;
        let later_queries = delta("atomic56_later_queries")?;
        let completion = delta("atomic56_core_complete")?;
        let wrapper_return = delta("atomic56_done")?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.last()?.remaining)?;
        let post = total.checked_sub(through_last)?;
        let buckets = [
            setup,
            proof_load,
            parsed,
            transcript,
            terminal,
            relation,
            openings,
            layer0_queries,
            later_queries,
            completion,
            wrapper_return,
            post,
        ];
        Some(AtomicProfile22AcceptanceLedger {
            transaction_setup_cu: setup,
            proof_load_cu: proof_load,
            parsed_cu: parsed,
            transcript_cu: transcript,
            terminal_cu: terminal,
            relation_cu: relation,
            openings_cu: openings,
            layer0_queries_cu: layer0_queries,
            later_queries_cu: later_queries,
            completion_cu: completion,
            wrapper_return_cu: wrapper_return,
            post_last_marker_cu: post,
            reconciled_total_cu: buckets.iter().sum(),
            formula: buckets
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(" + "),
        })
    }

    let root = workspace_root()?;
    let statement = statement()?;
    let proof_path = root.join("results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read profile22 proof {}", proof_path.display()))?;
    ensure!(proof.len() == PROOF_BYTES, "profile22 proof length drift");
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    ensure!(proof_sha256 == PROOF_SHA256, "profile22 proof KAT drift");
    verify_atomic_state_only_profile22_unmined_for_diagnostics_v3(
        &proof, &statement, HOST_HASH, None,
    )
    .map_err(|error| anyhow!("profile22 host replay: {error:?}"))?;
    ensure!(
        verify_atomic_state_only_profile22_v3(&proof, &statement, HOST_HASH, None).is_err(),
        "unmined profile22 proof passed production host API"
    );

    let default_data = to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile22V3 {
        pool: statement.pool,
        sequence: statement.sequence,
        public_input: public_bytes(&statement.spend),
        output_anchor: encode_digest_canonical(&statement.output_anchor),
        diagnostic_unmined: true,
    })?;
    let default_tag56_fail_closed_host =
        aspis_verifier::process_instruction(&aspis_verifier::id(), &[], &default_data)
            == Err(solana_sdk::program_error::ProgramError::Custom(
                aspis_verifier::atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
    ensure!(
        default_tag56_fail_closed_host,
        "default tag56 is not fail-closed"
    );

    let so = build_sbf_with_features(
        &root,
        &["diagnostic-unmined-profile22-acceptance"],
        "aspis_verifier_atomic_profile22_candidate.so",
    )?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    let simulate = |diagnostic_unmined| -> Result<SimulationResult> {
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction(proof_account.pubkey(), &statement, diagnostic_unmined)?,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            rpc.latest_blockhash()?,
        );
        rpc.simulate_verbose(&transaction)
    };
    let production = simulate(false)?;
    ensure!(
        production.err.is_some(),
        "unmined profile22 proof passed production SBF API"
    );
    let diagnostic = simulate(true)?;
    ensure!(
        diagnostic.err.is_none(),
        "profile22 diagnostic failed: {:?}",
        diagnostic.err
    );
    let total = diagnostic.units.context("tag56 simulation omitted CU")?;
    let markers = parse_cu_markers(&diagnostic.logs, "aspis-cu:");
    let ledger = ledger(&markers, total).context("tag56 marker ledger incomplete")?;
    ensure!(ledger.reconciled_total_cu == total, "tag56 ledger mismatch");

    Ok(AtomicProfile22AcceptanceSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile22-acceptance".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 56,
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        proof_bytes: proof.len(),
        proof_sha256,
        proof_unmined: true,
        batch_grinding_bits: STATE_ONLY_PROFILE22_BATCH_GRINDING_BITS,
        final_grinding_bits: STATE_ONLY_PROFILE22_GRINDING_BITS,
        fold_grinding_bits: RATE16_HARDENED_FOLD_POW_BITS,
        soundness_bits_factor31: 102.4649,
        soundness_bits_factor40: 102.0972,
        default_tag56_fail_closed_host,
        production_api_rejected_unmined_sbf: true,
        literal_simulation_cu: total,
        headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
        markers,
        ledger,
        production_mutation_enabled: false,
        notes: vec![
            "Tag56 is one integrated parse/transcript/terminal/relation/private-opening/q16 call. The phase ledger reconciles to the literal simulation total without overlap substitution.".to_string(),
            "All five Merkle sections authenticate value||salt32 records. Salts are not transcript messages; their roots bind them before downstream challenges.".to_string(),
            "The committed fixture is unmined. The diagnostic arm bypasses only PoW; both host and SBF production entrypoints reject those same bytes.".to_string(),
            "Tags57/58 remain feature-gated; production mutation stays disabled until the complete-view HVZK audit and mined KAT are green.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile23_acceptance() -> Result<AtomicProfile23AcceptanceSummary> {
    use aspis_core::circle_prefix::RATE16_HARDENED_FOLD_POW_BITS;
    use aspis_core::state_only_prefix::{
        STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS, STATE_ONLY_PROFILE23_GRINDING_BITS,
    };
    use aspis_statement::state_only_profile23::{
        verify_atomic_state_only_profile23_unmined_for_diagnostics_v3,
        verify_atomic_state_only_profile23_v3,
    };
    use aspis_statement::{encode_digest_canonical, AtomicPaymentStatementV3, SpendPublic};
    use sha2::{Digest as _, Sha256};

    const PROOF_BYTES: usize = 59_679;
    const PROOF_SHA256: &str = "07f8258f9297bd19d007b5bebdfbb710e8e9e44dcc2277f8cf7a6148db6ce902";

    fn public_bytes(public: &SpendPublic) -> [u8; 104] {
        let mut output = [0u8; 104];
        for (index, value) in public
            .anchor
            .iter()
            .chain(&public.nullifier)
            .chain(&public.output_commitment)
            .chain(core::iter::once(&public.asset_id))
            .enumerate()
        {
            output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        output[100..].copy_from_slice(&public.fee.to_le_bytes());
        output
    }

    fn instruction(
        proof_account: Pubkey,
        statement: &AtomicPaymentStatementV3,
        diagnostic_unmined: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account, false)],
            data: to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile23V3 {
                pool: statement.pool,
                sequence: statement.sequence,
                public_input: public_bytes(&statement.spend),
                output_anchor: encode_digest_canonical(&statement.output_anchor),
                diagnostic_unmined,
            })?,
        })
    }

    fn ledger(markers: &[CuMarker], total: u64) -> Option<AtomicProfile23AcceptanceLedger> {
        let delta = |label: &str| {
            markers
                .iter()
                .find(|marker| marker.label == label)?
                .delta_from_previous?
                .try_into()
                .ok()
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.first()?.remaining)?;
        let proof_load = delta("atomic59_proof_loaded")?;
        let parsed = delta("atomic59_parsed")?;
        let transcript = delta("atomic59_transcript")?;
        let terminal = delta("atomic59_terminal")?;
        let relation = delta("atomic59_relation")?;
        let openings = delta("atomic59_openings")?;
        let layer0_queries = delta("atomic59_layer0_queries")?;
        let later_queries = delta("atomic59_later_queries")?;
        let completion = delta("atomic59_core_complete")?;
        let wrapper_return = delta("atomic59_done")?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(markers.last()?.remaining)?;
        let post = total.checked_sub(through_last)?;
        let buckets = [
            setup,
            proof_load,
            parsed,
            transcript,
            terminal,
            relation,
            openings,
            layer0_queries,
            later_queries,
            completion,
            wrapper_return,
            post,
        ];
        Some(AtomicProfile23AcceptanceLedger {
            transaction_setup_cu: setup,
            proof_load_cu: proof_load,
            parsed_cu: parsed,
            transcript_cu: transcript,
            terminal_cu: terminal,
            relation_cu: relation,
            openings_cu: openings,
            layer0_queries_cu: layer0_queries,
            later_queries_cu: later_queries,
            completion_cu: completion,
            wrapper_return_cu: wrapper_return,
            post_last_marker_cu: post,
            reconciled_total_cu: buckets.iter().sum(),
            formula: buckets
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(" + "),
        })
    }

    let root = workspace_root()?;
    let (proof_path, proof_source_override) = profile23_proof_path(&root);
    let statement_selection = profile23_statement_selection(&root, proof_source_override)?;
    let statement = &statement_selection.statement;
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read profile23 proof {}", proof_path.display()))?;
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    if !proof_source_override {
        ensure!(proof.len() == PROOF_BYTES, "profile23 proof length drift");
        ensure!(proof_sha256 == PROOF_SHA256, "profile23 proof KAT drift");
    }
    verify_atomic_state_only_profile23_unmined_for_diagnostics_v3(
        &proof, statement, HOST_HASH, None,
    )
    .map_err(|error| anyhow!("profile23 host replay: {error:?}"))?;
    let proof_unmined =
        verify_atomic_state_only_profile23_v3(&proof, statement, HOST_HASH, None).is_err();

    let default_data = to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile23V3 {
        pool: statement.pool,
        sequence: statement.sequence,
        public_input: public_bytes(&statement.spend),
        output_anchor: encode_digest_canonical(&statement.output_anchor),
        diagnostic_unmined: true,
    })?;
    let default_tag59_fail_closed_host =
        aspis_verifier::process_instruction(&aspis_verifier::id(), &[], &default_data)
            == Err(solana_sdk::program_error::ProgramError::Custom(
                aspis_verifier::atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
    ensure!(
        default_tag59_fail_closed_host,
        "default tag59 is not fail-closed"
    );

    let so = build_sbf_with_features(
        &root,
        &["diagnostic-unmined-profile23-acceptance"],
        "aspis_verifier_atomic_profile23_candidate.so",
    )?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
    finalize_proof(&rpc, &payer, &proof_account.pubkey())?;
    let simulate = |diagnostic_unmined| -> Result<SimulationResult> {
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction(proof_account.pubkey(), statement, diagnostic_unmined)?,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            rpc.latest_blockhash()?,
        );
        rpc.simulate_verbose(&transaction)
    };
    let production = simulate(false)?;
    ensure!(
        production.err.is_some() == proof_unmined,
        "profile23 production host/SBF PoW classification mismatch: host_unmined={proof_unmined}, sbf_error={:?}",
        production.err
    );
    let diagnostic = simulate(true)?;
    ensure!(
        diagnostic.err.is_none(),
        "profile23 diagnostic failed: {:?}",
        diagnostic.err
    );
    let measured = if proof_unmined {
        &diagnostic
    } else {
        &production
    };
    let total = measured.units.context("tag59 simulation omitted CU")?;
    let markers = parse_cu_markers(&measured.logs, "aspis-cu:");
    let ledger = ledger(&markers, total).context("tag59 marker ledger incomplete")?;
    ensure!(ledger.reconciled_total_cu == total, "tag59 ledger mismatch");

    Ok(AtomicProfile23AcceptanceSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: if proof_source_override {
            if let Some(statement_path) = statement_selection.path.as_ref() {
                format!(
                    "ASPIS_PROFILE23_PROOF={} ASPIS_PROFILE23_STATEMENT={} NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile23-acceptance",
                    proof_path.display(),
                    statement_path.display()
                )
            } else {
                format!(
                    "ASPIS_PROFILE23_PROOF={} NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile23-acceptance",
                    proof_path.display()
                )
            }
        } else {
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile23-acceptance".to_string()
        },
        validator_version: validator_version(),
        instruction_wire_ordinal: 59,
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        proof_source_override,
        proof_bytes: proof.len(),
        proof_sha256,
        proof_unmined,
        statement_path: statement_selection
            .path
            .as_deref()
            .map(|path| profile23_recorded_path(&root, path)),
        statement_source_override: statement_selection.source_override,
        statement_sha256: statement_selection.sha256.clone(),
        statement_pool_hex: profile23_hex(&statement.pool),
        statement_sequence: statement.sequence,
        canonical_public_input_digest: statement_selection
            .canonical_public_input_digest
            .clone(),
        batch_grinding_bits: STATE_ONLY_PROFILE23_BATCH_GRINDING_BITS,
        final_grinding_bits: STATE_ONLY_PROFILE23_GRINDING_BITS,
        fold_grinding_bits: RATE16_HARDENED_FOLD_POW_BITS,
        query_selector_candidates: 3,
        rank_exhaustion_cap16_bits: 105.41017865405837,
        whole_soundness_bits_after_selector: 101.30230658283051,
        soundness_bookable: true,
        proof_account_finalized_before_verification: true,
        default_tag59_fail_closed_host,
        production_api_rejected_unmined_sbf: proof_unmined && production.err.is_some(),
        production_api_accepted_mined_sbf: !proof_unmined && production.err.is_none(),
        literal_simulation_cu: total,
        headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
        markers,
        ledger,
        production_mutation_enabled: false,
        notes: vec![
            "Tag59 is one integrated parse/transcript/terminal/relation/private-opening/q16 call. The phase ledger is overlap-free and reconciles exactly to the literal simulation total.".to_string(),
            "All five Merkle sections authenticate value||salt32 records. Salts are not transcript messages; their roots bind them before downstream challenges.".to_string(),
            if proof_unmined {
                "The selected proof is unmined. The diagnostic arm bypasses only PoW; both host and SBF production entrypoints reject those same bytes.".to_string()
            } else {
                "The ASPIS_PROFILE23_PROOF override supplied a mined proof; production host and SBF tag59 both accepted it without a PoW bypass.".to_string()
            },
            if statement_selection.source_override {
                "ASPIS_PROFILE23_STATEMENT supplied an exact-schema canonical public-statement sidecar; its path, byte SHA-256, pool, sequence, and transcript public-input digest are pinned in this artifact.".to_string()
            } else {
                "No statement sidecar was supplied; this artifact uses the unchanged built-in Profile23 fixture statement.".to_string()
            },
            "Tags60/61 remain feature-gated; production mutation stays disabled until the complete-view HVZK audit and mined tag60 KAT are green.".to_string(),
        ],
    })
}

/// Literal tag-51/tag-52 mutation closure. The command is allocated now so
/// the final profile-21 proof fixture can be measured immediately after the
/// integrated verifier seam emits its frozen length and SHA-256 KAT.
pub fn run_stage2_atomic_profile21_mutation() -> Result<AtomicProfile21MutationSummary> {
    use aspis_core::field::M31;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, encode_digest_canonical, note_commitment,
        output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic,
    };
    use aspis_verifier::atomic_payment::{
        atomic_nullifier_address, AtomicPaymentPublicInputs, AtomicPoolStateV1,
        ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED, ATOMIC_NULLIFIER_MAGIC, ATOMIC_NULLIFIER_MARKER_LEN,
        ATOMIC_NULLIFIER_VERSION, ATOMIC_POOL_STATE_LEN,
    };
    use sha2::{Digest as _, Sha256};

    const DIAGNOSTIC_FEATURES: [&str; 2] = [
        "diagnostic-unmined-profile21-mutation",
        "profile21-mutation-candidate",
    ];
    const PROFILE21_BASIS_FINGERPRINT_PIN: u64 = 0xceb3_5dd3_ee50_e051;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn statement() -> Result<AtomicPaymentStatementV3> {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
        };
        let input = note_commitment(
            &derive_owner_key(&nullifier_key),
            value,
            asset_id,
            &input_salt,
        );
        let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
        Ok(AtomicPaymentStatementV3 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &path)
                    .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &path)
                .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
        })
    }

    fn public_inputs(statement: &AtomicPaymentStatementV3) -> AtomicPaymentPublicInputs {
        AtomicPaymentPublicInputs {
            current_anchor: encode_digest_canonical(&statement.spend.anchor),
            nullifier: encode_digest_canonical(&statement.spend.nullifier),
            output_commitment: encode_digest_canonical(&statement.spend.output_commitment),
            output_anchor: encode_digest_canonical(&statement.output_anchor),
            asset_id: statement.spend.asset_id.0,
            fee: statement.spend.fee,
        }
    }

    fn instruction_data(public: &AtomicPaymentPublicInputs, diagnostic: bool) -> Result<Vec<u8>> {
        let instruction = if diagnostic {
            AspisInstruction::MeasureAtomicStateOnlyProfile21MutationV3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        } else {
            AspisInstruction::ApplyAtomicStateOnlyProfile21V3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        };
        Ok(to_vec(&instruction)?)
    }

    fn transition_instruction(
        proof: Pubkey,
        pool: Pubkey,
        marker: Pubkey,
        payer: Pubkey,
        public: &AtomicPaymentPublicInputs,
        diagnostic: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![
                AccountMeta::new_readonly(proof, false),
                AccountMeta::new(pool, false),
                AccountMeta::new(marker, false),
                AccountMeta::new(payer, true),
                AccountMeta::new_readonly(solana_sdk::system_program::id(), false),
            ],
            data: instruction_data(public, diagnostic)?,
        })
    }

    fn signed_transition(
        payer: &Keypair,
        instruction: Instruction,
        blockhash: solana_sdk::hash::Hash,
    ) -> Transaction {
        Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        )
    }

    fn patch_proof_byte(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        offset: usize,
        byte: u8,
    ) -> Result<()> {
        let instruction = proof_instruction(
            &payer.pubkey(),
            proof_account,
            &AspisInstruction::UploadChunk {
                offset: offset as u32,
                chunk: vec![byte],
            },
        )?;
        let transaction = Transaction::new_signed_with_payer(
            &[instruction],
            Some(&payer.pubkey()),
            &[payer],
            rpc.latest_blockhash()?,
        );
        rpc.send_and_confirm(&transaction)?;
        Ok(())
    }

    fn marker_is_exact(snapshot: &RpcAccountSnapshot, pool: Pubkey, nullifier: &[u8; 32]) -> bool {
        snapshot.owner == aspis_verifier::id()
            && snapshot.data.len() == ATOMIC_NULLIFIER_MARKER_LEN
            && snapshot.data[0..4] == ATOMIC_NULLIFIER_MAGIC
            && snapshot.data[4] == ATOMIC_NULLIFIER_VERSION
            && snapshot.data[5..8] == [0u8; 3]
            && snapshot.data[8..40] == pool.to_bytes()
            && snapshot.data[40..72] == *nullifier
    }

    fn marker_span(markers: &[CuMarker], start: &str, end: &str) -> Option<u64> {
        let start = markers
            .iter()
            .find(|marker| marker.label == start)?
            .remaining;
        let end = markers.iter().find(|marker| marker.label == end)?.remaining;
        start.checked_sub(end)
    }

    fn mutation_ledger(
        markers: &[CuMarker],
        total: u64,
        program_owned: bool,
    ) -> Option<AtomicProfile21MutationLedger> {
        let first = markers.first()?;
        let last = markers.last()?;
        let account_label = if program_owned {
            "atomic52_accounts_validated_program_owned"
        } else {
            "atomic52_accounts_validated_system_owned"
        };
        let marker_label = if program_owned {
            "atomic52_program_marker_ready"
        } else {
            "atomic52_system_marker_created"
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(first.remaining)?;
        let validation = marker_span(markers, "atomic52_instruction_start", account_label)?;
        let digest = marker_span(markers, account_label, "atomic52_statement_digest_done")?;
        let verifier = marker_span(
            markers,
            "atomic52_statement_digest_done",
            "atomic52_proof_verified",
        )?;
        let marker = marker_span(markers, "atomic52_proof_verified", marker_label)?;
        let recheck = marker_span(markers, marker_label, "atomic52_state_rechecked")?;
        let writes = marker_span(
            markers,
            "atomic52_state_rechecked",
            "atomic52_state_applied",
        )?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(last.remaining)?;
        let post = total.checked_sub(through_last)?;
        let reconciled = setup
            .checked_add(validation)?
            .checked_add(digest)?
            .checked_add(verifier)?
            .checked_add(marker)?
            .checked_add(recheck)?
            .checked_add(writes)?
            .checked_add(post)?;
        Some(AtomicProfile21MutationLedger {
            transaction_setup_cu: setup,
            account_validation_cu: validation,
            statement_decode_and_digest_cu: digest,
            exact_profile21_verifier_cu: verifier,
            marker_prepare_or_cpi_cu: marker,
            mutable_state_recheck_cu: recheck,
            final_account_writes_cu: writes,
            post_last_marker_cu: post,
            reconciled_total_cu: reconciled,
            formula: format!(
                "{setup} + {validation} + {digest} + {verifier} + {marker} + {recheck} + {writes} + {post}"
            ),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn run_path(
        root: &Path,
        so: &Path,
        proof: &[u8],
        statement: &AtomicPaymentStatementV3,
        read_only_tag50_cu: u64,
        preowned_marker: bool,
        exercise_candidate_tag51: bool,
        exercise_concurrency: bool,
    ) -> Result<(AtomicProfile21MutationPathSummary, bool, bool)> {
        let public = public_inputs(statement);
        let pool_key = Pubkey::new_from_array(statement.pool);
        let (marker_key, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
        let mut pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV1 {
            sequence: statement.sequence,
            anchor: public.current_anchor,
        }
        .encode(&mut pool_bytes)?;
        let pool_fixture = write_validator_account_fixture(
            root,
            if preowned_marker {
                "atomic-profile21-program-pool"
            } else {
                "atomic-profile21-system-pool"
            },
            pool_key,
            aspis_verifier::id(),
            &pool_bytes,
        )?;
        let mut fixtures = vec![(pool_key, pool_fixture)];
        if preowned_marker {
            let marker_fixture = write_validator_account_fixture(
                root,
                "atomic-profile21-program-marker",
                marker_key,
                aspis_verifier::id(),
                &[0u8; ATOMIC_NULLIFIER_MARKER_LEN],
            )?;
            fixtures.push((marker_key, marker_fixture));
        }

        let validator = start_validator_with_accounts(root, so, &fixtures)?;
        let rpc = Rpc {
            url: validator.rpc_url.clone(),
            http: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()?,
        };
        let payer = Keypair::new();
        rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, proof, true)?;

        let clean_instruction = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            true,
        )?;
        let clean_tx =
            signed_transition(&payer, clean_instruction.clone(), rpc.latest_blockhash()?);
        let clean = rpc.simulate_verbose(&clean_tx)?;
        ensure!(
            clean.err.is_none(),
            "{} marker profile21 mutation simulation failed: {:?}",
            if preowned_marker {
                "program-owned"
            } else {
                "system-owned"
            },
            clean.err
        );
        let total = clean
            .units
            .context("profile21 mutation simulation omitted CU")?;
        let markers = parse_cu_markers(&clean.logs, "aspis-cu:");
        let ledger = mutation_ledger(&markers, total, preowned_marker)
            .context("profile21 mutation marker ledger incomplete")?;
        ensure!(
            ledger.reconciled_total_cu == total,
            "profile21 mutation ledger mismatch"
        );

        let pool_before = rpc_account_snapshot(&rpc, &pool_key)?
            .context("preloaded profile21 pool account missing")?;
        let marker_before = rpc_account_snapshot(&rpc, &marker_key)?;
        if preowned_marker {
            ensure!(
                marker_before.as_ref().is_some_and(|snapshot| {
                    snapshot.owner == aspis_verifier::id()
                        && snapshot.data == [0u8; ATOMIC_NULLIFIER_MARKER_LEN]
                }),
                "profile21 program-owned marker fixture drift"
            );
        } else {
            ensure!(
                marker_before.is_none(),
                "profile21 System PDA unexpectedly exists"
            );
        }

        let corruption_offset = proof
            .len()
            .checked_sub(1)
            .context("empty profile21 proof")?;
        let original_byte = proof[corruption_offset];
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte ^ 1,
        )?;
        let corrupt_tx = signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?,
            rpc.latest_blockhash()?,
        );
        let corrupt = rpc.simulate_verbose(&corrupt_tx)?;
        let corrupt_rejected = corrupt.err.is_some()
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_before)
            && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
        ensure!(
            corrupt_rejected,
            "corrupt profile21 proof changed atomic state"
        );
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte,
        )?;

        let mut candidate_rejects_unmined = true;
        let mut candidate_rollback = true;
        if exercise_candidate_tag51 {
            let candidate_tx = signed_transition(
                &payer,
                transition_instruction(
                    proof_account.pubkey(),
                    pool_key,
                    marker_key,
                    payer.pubkey(),
                    &public,
                    false,
                )?,
                rpc.latest_blockhash()?,
            );
            let candidate = rpc.simulate_verbose(&candidate_tx)?;
            candidate_rejects_unmined = candidate.err.is_some();
            candidate_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref()
                == Some(&pool_before)
                && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
            ensure!(candidate_rejects_unmined, "tag51 accepted unmined proof");
            ensure!(candidate_rollback, "tag51 PoW rejection changed state");
        }

        let concurrent_exactly_one = if exercise_concurrency {
            let second_payer = Keypair::new();
            rpc.airdrop_and_wait(&second_payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
            let first_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?;
            let second_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                second_payer.pubkey(),
                &public,
                true,
            )?;
            let blockhash = rpc.latest_blockhash()?;
            let first_tx = signed_transition(&payer, first_instruction, blockhash);
            let second_tx = signed_transition(&second_payer, second_instruction, blockhash);
            let rpc_a = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let rpc_b = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let (first_result, second_result) = thread::scope(|scope| {
                let first = scope.spawn(|| rpc_a.send_and_confirm(&first_tx));
                let second = scope.spawn(|| rpc_b.send_and_confirm(&second_tx));
                (first.join().unwrap(), second.join().unwrap())
            });
            let exactly_one = first_result.is_ok() ^ second_result.is_ok();
            ensure!(
                exactly_one,
                "concurrent profile21 spends did not commit exactly once"
            );
            Some(exactly_one)
        } else {
            rpc.send_and_confirm(&clean_tx)?;
            None
        };

        let pool_after = rpc_account_snapshot(&rpc, &pool_key)?
            .context("profile21 pool disappeared after transition")?;
        let marker_after = rpc_account_snapshot(&rpc, &marker_key)?
            .context("profile21 nullifier marker missing")?;
        let decoded_pool = AtomicPoolStateV1::decode(&pool_after.data)?;
        let sequence_advanced = decoded_pool.sequence == statement.sequence + 1;
        let anchor_replaced = decoded_pool.anchor == public.output_anchor;
        let marker_written = marker_is_exact(&marker_after, pool_key, &public.nullifier);
        ensure!(sequence_advanced && anchor_replaced && marker_written);

        let mut duplicate_public = public;
        duplicate_public.current_anchor = duplicate_public.output_anchor;
        let duplicate_tx = signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &duplicate_public,
                true,
            )?,
            rpc.latest_blockhash()?,
        );
        let duplicate_rejected = rpc.send_and_confirm(&duplicate_tx).is_err();
        let duplicate_no_mutation = duplicate_rejected
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_after)
            && rpc_account_snapshot(&rpc, &marker_key)?.as_ref() == Some(&marker_after);
        ensure!(
            duplicate_no_mutation,
            "duplicate profile21 spend changed state"
        );

        drop(validator);
        Ok((
            AtomicProfile21MutationPathSummary {
                marker_path: if preowned_marker {
                    "program_owned_zeroed"
                } else {
                    "canonical_system_owned_create"
                },
                literal_simulation_cu: total,
                headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
                incremental_over_tag50_cu: total as i64 - read_only_tag50_cu as i64,
                markers,
                ledger,
                clean_simulation_accepted: true,
                corrupt_proof_rejected_without_mutation: corrupt_rejected,
                committed_transition_succeeded: true,
                pool_sequence_advanced_once: sequence_advanced,
                pool_anchor_replaced: anchor_replaced,
                nullifier_marker_written: marker_written,
                duplicate_rejected_without_second_mutation: duplicate_no_mutation,
                concurrent_exactly_one_committed: concurrent_exactly_one,
            },
            candidate_rejects_unmined,
            candidate_rollback,
        ))
    }

    let root = workspace_root()?;
    let proof_path = root.join("results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read integrated profile21 proof {}", proof_path.display()))?;
    ensure!(!proof.is_empty(), "integrated profile21 proof is empty");
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let basis_fingerprint =
        aspis_core::state_only_masked_switch_basis::MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT;
    ensure!(basis_fingerprint == PROFILE21_BASIS_FINGERPRINT_PIN);
    let statement = statement()?;

    let acceptance: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/atomic_state_only_profile21_acceptance.json"),
    )?)?;
    ensure!(
        acceptance["proof_sha256"].as_str() == Some(&proof_sha256),
        "tag50/tag52 proof KAT mismatch"
    );
    let read_only_tag50_cu = acceptance["literal_simulation_cu"]
        .as_u64()
        .context("profile21 acceptance artifact omitted literal CU")?;
    let soundness_reduction_complete = acceptance["soundness_reduction_complete"]
        .as_bool()
        .unwrap_or(false);
    let complete_view_hvzk_simulator_complete = acceptance["complete_view_hvzk_simulator_complete"]
        .as_bool()
        .unwrap_or(false);

    let default_tag51 = instruction_data(&public_inputs(&statement), false)?;
    let default_tag51_fail_closed_host =
        aspis_verifier::process_instruction(&aspis_verifier::id(), &[], &default_tag51)
            == Err(solana_sdk::program_error::ProgramError::Custom(
                ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
    ensure!(
        default_tag51_fail_closed_host,
        "default tag51 is not fail-closed"
    );

    let diagnostic_so = build_sbf_with_features(
        &root,
        &DIAGNOSTIC_FEATURES,
        "aspis_verifier_atomic_profile21_mutation_diagnostic.so",
    )?;
    let (program_path, candidate_tag51_rejects_unmined_sbf, candidate_tag51_rollback_green) =
        run_path(
            &root,
            &diagnostic_so,
            &proof,
            &statement,
            read_only_tag50_cu,
            true,
            true,
            false,
        )?;
    let (system_path, _, _) = run_path(
        &root,
        &diagnostic_so,
        &proof,
        &statement,
        read_only_tag50_cu,
        false,
        false,
        true,
    )?;

    Ok(AtomicProfile21MutationSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile21-mutation".to_string(),
        validator_version: validator_version(),
        production_instruction_wire_ordinal: 51,
        diagnostic_instruction_wire_ordinal: 52,
        diagnostic_sbf_features: DIAGNOSTIC_FEATURES.to_vec(),
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        proof_bytes: proof.len(),
        proof_sha256,
        proof_unmined: true,
        masked_switch_basis_fingerprint: format!("0x{basis_fingerprint:016x}"),
        production_pow_bypass_exposed: false,
        default_tag51_fail_closed_host,
        candidate_tag51_rejects_unmined_sbf,
        candidate_tag51_rollback_green,
        paths: vec![program_path, system_path],
        soundness_reduction_complete,
        complete_view_hvzk_simulator_complete,
        production_profile21_mutation_enabled: false,
        notes: vec![
            "Tag51 has no diagnostic selector and calls the exact tag50 parser/verifier with production PoW before the first CPI or account write. Default builds remain fail-closed.".to_string(),
            "Tag52 exists only in a nondefault local-validator build and reuses the same integrated proof bytes. Its sole acceptance difference is bypassing the transcript-bound PoW predicate.".to_string(),
            "Both marker paths emit single-instruction, overlap-free ledgers. Corruption rollback, exact pool/marker images, duplicate rejection, and a two-signer System-path race are tested.".to_string(),
            "The mutation artifact records, but cannot override, the independent soundness-reduction and complete-view HVZK gates from the literal tag50 acceptance artifact.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile22_mutation() -> Result<AtomicProfile22MutationSummary> {
    use aspis_core::field::M31;
    use aspis_statement::atomic_state_only_trace::atomic_merkle_root_v3;
    use aspis_statement::{
        derive_nullifier, derive_owner_key, encode_digest_canonical, note_commitment,
        output_commitment, AtomicPaymentStatementV3, Digest, MerklePath, SpendPublic,
    };
    use aspis_verifier::atomic_payment::{
        atomic_nullifier_address, AtomicPaymentPublicInputs, AtomicPoolStateV1,
        ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED, ATOMIC_NULLIFIER_MAGIC, ATOMIC_NULLIFIER_MARKER_LEN,
        ATOMIC_NULLIFIER_VERSION, ATOMIC_POOL_STATE_LEN,
    };
    use sha2::{Digest as _, Sha256};

    const DIAGNOSTIC_FEATURES: [&str; 2] = [
        "diagnostic-unmined-profile22-mutation",
        "profile22-mutation-candidate",
    ];
    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn statement() -> Result<AtomicPaymentStatementV3> {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
        };
        let input = note_commitment(
            &derive_owner_key(&nullifier_key),
            value,
            asset_id,
            &input_salt,
        );
        let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
        Ok(AtomicPaymentStatementV3 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &path)
                    .map_err(|error| anyhow!("atomic input root: {error:?}"))?,
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &path)
                .map_err(|error| anyhow!("atomic output root: {error:?}"))?,
        })
    }

    fn public_inputs(statement: &AtomicPaymentStatementV3) -> AtomicPaymentPublicInputs {
        AtomicPaymentPublicInputs {
            current_anchor: encode_digest_canonical(&statement.spend.anchor),
            nullifier: encode_digest_canonical(&statement.spend.nullifier),
            output_commitment: encode_digest_canonical(&statement.spend.output_commitment),
            output_anchor: encode_digest_canonical(&statement.output_anchor),
            asset_id: statement.spend.asset_id.0,
            fee: statement.spend.fee,
        }
    }

    fn instruction_data(public: &AtomicPaymentPublicInputs, diagnostic: bool) -> Result<Vec<u8>> {
        let instruction = if diagnostic {
            AspisInstruction::MeasureAtomicStateOnlyProfile22MutationV3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        } else {
            AspisInstruction::ApplyAtomicStateOnlyProfile22V3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        };
        Ok(to_vec(&instruction)?)
    }

    fn transition_instruction(
        proof: Pubkey,
        pool: Pubkey,
        marker: Pubkey,
        payer: Pubkey,
        public: &AtomicPaymentPublicInputs,
        diagnostic: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![
                AccountMeta::new_readonly(proof, false),
                AccountMeta::new(pool, false),
                AccountMeta::new(marker, false),
                AccountMeta::new(payer, true),
                AccountMeta::new_readonly(solana_sdk::system_program::id(), false),
            ],
            data: instruction_data(public, diagnostic)?,
        })
    }

    fn signed_transition(
        payer: &Keypair,
        instruction: Instruction,
        blockhash: solana_sdk::hash::Hash,
    ) -> Transaction {
        Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        )
    }

    fn patch_proof_byte(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        offset: usize,
        byte: u8,
    ) -> Result<()> {
        let instruction = proof_instruction(
            &payer.pubkey(),
            proof_account,
            &AspisInstruction::UploadChunk {
                offset: offset as u32,
                chunk: vec![byte],
            },
        )?;
        let transaction = Transaction::new_signed_with_payer(
            &[instruction],
            Some(&payer.pubkey()),
            &[payer],
            rpc.latest_blockhash()?,
        );
        rpc.send_and_confirm(&transaction)?;
        Ok(())
    }

    fn marker_is_exact(snapshot: &RpcAccountSnapshot, pool: Pubkey, nullifier: &[u8; 32]) -> bool {
        snapshot.owner == aspis_verifier::id()
            && snapshot.data.len() == ATOMIC_NULLIFIER_MARKER_LEN
            && snapshot.data[0..4] == ATOMIC_NULLIFIER_MAGIC
            && snapshot.data[4] == ATOMIC_NULLIFIER_VERSION
            && snapshot.data[5..8] == [0u8; 3]
            && snapshot.data[8..40] == pool.to_bytes()
            && snapshot.data[40..72] == *nullifier
    }

    fn marker_span(markers: &[CuMarker], start: &str, end: &str) -> Option<u64> {
        let start = markers
            .iter()
            .find(|marker| marker.label == start)?
            .remaining;
        let end = markers.iter().find(|marker| marker.label == end)?.remaining;
        start.checked_sub(end)
    }

    fn mutation_ledger(
        markers: &[CuMarker],
        total: u64,
        program_owned: bool,
    ) -> Option<AtomicProfile22MutationLedger> {
        let first = markers.first()?;
        let last = markers.last()?;
        let account_label = if program_owned {
            "atomic58_accounts_validated_program_owned"
        } else {
            "atomic58_accounts_validated_system_owned"
        };
        let marker_label = if program_owned {
            "atomic58_program_marker_ready"
        } else {
            "atomic58_system_marker_created"
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(first.remaining)?;
        let validation = marker_span(markers, "atomic58_instruction_start", account_label)?;
        let digest = marker_span(markers, account_label, "atomic58_statement_digest_done")?;
        let verifier = marker_span(
            markers,
            "atomic58_statement_digest_done",
            "atomic58_proof_verified",
        )?;
        let marker = marker_span(markers, "atomic58_proof_verified", marker_label)?;
        let recheck = marker_span(markers, marker_label, "atomic58_state_rechecked")?;
        let writes = marker_span(
            markers,
            "atomic58_state_rechecked",
            "atomic58_state_applied",
        )?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(last.remaining)?;
        let post = total.checked_sub(through_last)?;
        let reconciled = setup
            .checked_add(validation)?
            .checked_add(digest)?
            .checked_add(verifier)?
            .checked_add(marker)?
            .checked_add(recheck)?
            .checked_add(writes)?
            .checked_add(post)?;
        Some(AtomicProfile22MutationLedger {
            transaction_setup_cu: setup,
            account_validation_cu: validation,
            statement_decode_and_digest_cu: digest,
            exact_profile22_verifier_cu: verifier,
            marker_prepare_or_cpi_cu: marker,
            mutable_state_recheck_cu: recheck,
            final_account_writes_cu: writes,
            post_last_marker_cu: post,
            reconciled_total_cu: reconciled,
            formula: format!(
                "{setup} + {validation} + {digest} + {verifier} + {marker} + {recheck} + {writes} + {post}"
            ),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn run_path(
        root: &Path,
        so: &Path,
        proof: &[u8],
        statement: &AtomicPaymentStatementV3,
        read_only_tag56_cu: u64,
        preowned_marker: bool,
        exercise_candidate_tag57: bool,
        exercise_concurrency: bool,
    ) -> Result<(AtomicProfile22MutationPathSummary, bool, bool)> {
        let public = public_inputs(statement);
        let pool_key = Pubkey::new_from_array(statement.pool);
        let (marker_key, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
        let mut pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV1 {
            sequence: statement.sequence,
            anchor: public.current_anchor,
        }
        .encode(&mut pool_bytes)?;
        let pool_fixture = write_validator_account_fixture(
            root,
            if preowned_marker {
                "atomic-profile22-program-pool"
            } else {
                "atomic-profile22-system-pool"
            },
            pool_key,
            aspis_verifier::id(),
            &pool_bytes,
        )?;
        let mut fixtures = vec![(pool_key, pool_fixture)];
        if preowned_marker {
            let marker_fixture = write_validator_account_fixture(
                root,
                "atomic-profile22-program-marker",
                marker_key,
                aspis_verifier::id(),
                &[0u8; ATOMIC_NULLIFIER_MARKER_LEN],
            )?;
            fixtures.push((marker_key, marker_fixture));
        }

        let validator = start_validator_with_accounts(root, so, &fixtures)?;
        let rpc = Rpc {
            url: validator.rpc_url.clone(),
            http: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()?,
        };
        let payer = Keypair::new();
        rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, proof, true)?;

        let clean_instruction = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            true,
        )?;
        let clean_tx =
            signed_transition(&payer, clean_instruction.clone(), rpc.latest_blockhash()?);
        let clean = rpc.simulate_verbose(&clean_tx)?;
        ensure!(
            clean.err.is_none(),
            "{} marker profile22 mutation simulation failed: {:?}",
            if preowned_marker {
                "program-owned"
            } else {
                "system-owned"
            },
            clean.err
        );
        let total = clean
            .units
            .context("profile22 mutation simulation omitted CU")?;
        let markers = parse_cu_markers(&clean.logs, "aspis-cu:");
        let ledger = mutation_ledger(&markers, total, preowned_marker)
            .context("profile22 mutation marker ledger incomplete")?;
        ensure!(
            ledger.reconciled_total_cu == total,
            "profile22 mutation ledger mismatch"
        );

        let pool_before = rpc_account_snapshot(&rpc, &pool_key)?
            .context("preloaded profile22 pool account missing")?;
        let marker_before = rpc_account_snapshot(&rpc, &marker_key)?;
        if preowned_marker {
            ensure!(
                marker_before.as_ref().is_some_and(|snapshot| {
                    snapshot.owner == aspis_verifier::id()
                        && snapshot.data == [0u8; ATOMIC_NULLIFIER_MARKER_LEN]
                }),
                "profile22 program-owned marker fixture drift"
            );
        } else {
            ensure!(
                marker_before.is_none(),
                "profile22 System PDA unexpectedly exists"
            );
        }

        let corruption_offset = proof
            .len()
            .checked_sub(1)
            .context("empty profile22 proof")?;
        let original_byte = proof[corruption_offset];
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte ^ 1,
        )?;
        let corrupt_tx = signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?,
            rpc.latest_blockhash()?,
        );
        let corrupt = rpc.simulate_verbose(&corrupt_tx)?;
        let corrupt_rejected = corrupt.err.is_some()
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_before)
            && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
        ensure!(
            corrupt_rejected,
            "corrupt profile22 proof changed atomic state"
        );
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte,
        )?;

        let mut candidate_rejects_unmined = true;
        let mut candidate_rollback = true;
        if exercise_candidate_tag57 {
            let candidate_tx = signed_transition(
                &payer,
                transition_instruction(
                    proof_account.pubkey(),
                    pool_key,
                    marker_key,
                    payer.pubkey(),
                    &public,
                    false,
                )?,
                rpc.latest_blockhash()?,
            );
            let candidate = rpc.simulate_verbose(&candidate_tx)?;
            candidate_rejects_unmined = candidate.err.is_some();
            candidate_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref()
                == Some(&pool_before)
                && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
            ensure!(candidate_rejects_unmined, "tag57 accepted unmined proof");
            ensure!(candidate_rollback, "tag57 PoW rejection changed state");
        }

        let concurrent_exactly_one = if exercise_concurrency {
            let second_payer = Keypair::new();
            rpc.airdrop_and_wait(&second_payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
            let first_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?;
            let second_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                second_payer.pubkey(),
                &public,
                true,
            )?;
            let blockhash = rpc.latest_blockhash()?;
            let first_tx = signed_transition(&payer, first_instruction, blockhash);
            let second_tx = signed_transition(&second_payer, second_instruction, blockhash);
            let rpc_a = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let rpc_b = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let (first_result, second_result) = thread::scope(|scope| {
                let first = scope.spawn(|| rpc_a.send_and_confirm(&first_tx));
                let second = scope.spawn(|| rpc_b.send_and_confirm(&second_tx));
                (first.join().unwrap(), second.join().unwrap())
            });
            let exactly_one = first_result.is_ok() ^ second_result.is_ok();
            ensure!(
                exactly_one,
                "concurrent profile22 spends did not commit exactly once"
            );
            Some(exactly_one)
        } else {
            rpc.send_and_confirm(&clean_tx)?;
            None
        };

        let pool_after = rpc_account_snapshot(&rpc, &pool_key)?
            .context("profile22 pool disappeared after transition")?;
        let marker_after = rpc_account_snapshot(&rpc, &marker_key)?
            .context("profile22 nullifier marker missing")?;
        let decoded_pool = AtomicPoolStateV1::decode(&pool_after.data)?;
        let sequence_advanced = decoded_pool.sequence == statement.sequence + 1;
        let anchor_replaced = decoded_pool.anchor == public.output_anchor;
        let marker_written = marker_is_exact(&marker_after, pool_key, &public.nullifier);
        ensure!(sequence_advanced && anchor_replaced && marker_written);

        let mut duplicate_public = public;
        duplicate_public.current_anchor = duplicate_public.output_anchor;
        let duplicate_tx = signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &duplicate_public,
                true,
            )?,
            rpc.latest_blockhash()?,
        );
        let duplicate_rejected = rpc.send_and_confirm(&duplicate_tx).is_err();
        let duplicate_no_mutation = duplicate_rejected
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_after)
            && rpc_account_snapshot(&rpc, &marker_key)?.as_ref() == Some(&marker_after);
        ensure!(
            duplicate_no_mutation,
            "duplicate profile22 spend changed state"
        );

        drop(validator);
        Ok((
            AtomicProfile22MutationPathSummary {
                marker_path: if preowned_marker {
                    "program_owned_zeroed"
                } else {
                    "canonical_system_owned_create"
                },
                literal_simulation_cu: total,
                headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
                incremental_over_tag56_cu: total as i64 - read_only_tag56_cu as i64,
                markers,
                ledger,
                clean_simulation_accepted: true,
                corrupt_proof_rejected_without_mutation: corrupt_rejected,
                committed_transition_succeeded: true,
                pool_sequence_advanced_once: sequence_advanced,
                pool_anchor_replaced: anchor_replaced,
                nullifier_marker_written: marker_written,
                duplicate_rejected_without_second_mutation: duplicate_no_mutation,
                concurrent_exactly_one_committed: concurrent_exactly_one,
            },
            candidate_rejects_unmined,
            candidate_rollback,
        ))
    }

    let root = workspace_root()?;
    let proof_path = root.join("results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read integrated profile22 proof {}", proof_path.display()))?;
    ensure!(
        proof.len() == 56_686,
        "integrated profile22 proof geometry drift"
    );
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    ensure!(
        proof_sha256 == "77736f0ea30ae9e2516537213e7dce386c9be69e3c772e5b50f03c57892136f8",
        "integrated profile22 proof KAT drift"
    );
    let statement = statement()?;

    let acceptance: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/atomic_state_only_profile22_acceptance.json"),
    )?)?;
    ensure!(
        acceptance["proof_sha256"].as_str() == Some(&proof_sha256),
        "tag56/tag58 proof KAT mismatch"
    );
    let read_only_tag56_cu = acceptance["literal_simulation_cu"]
        .as_u64()
        .context("profile22 acceptance artifact omitted literal CU")?;
    let soundness_audit: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/profile22_no_source_soundness_epro.json"),
    )?)?;
    let privacy_audit: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/profile22_universal_affine_privacy.json"),
    )?)?;
    let complete_system_claim_quotable = soundness_audit["complete_system_claim_quotable"]
        .as_bool()
        .unwrap_or(false);
    let complete_view_hvzk_simulator_complete = privacy_audit["remaining_lemma"]["closed"]
        .as_bool()
        .unwrap_or(false);

    let default_tag57 = instruction_data(&public_inputs(&statement), false)?;
    let default_tag57_fail_closed_host =
        aspis_verifier::process_instruction(&aspis_verifier::id(), &[], &default_tag57)
            == Err(solana_sdk::program_error::ProgramError::Custom(
                ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
    ensure!(
        default_tag57_fail_closed_host,
        "default tag57 is not fail-closed"
    );

    let diagnostic_so = build_sbf_with_features(
        &root,
        &DIAGNOSTIC_FEATURES,
        "aspis_verifier_atomic_profile22_mutation_diagnostic.so",
    )?;
    let (program_path, candidate_tag57_rejects_unmined_sbf, candidate_tag57_rollback_green) =
        run_path(
            &root,
            &diagnostic_so,
            &proof,
            &statement,
            read_only_tag56_cu,
            true,
            true,
            false,
        )?;
    let (system_path, _, _) = run_path(
        &root,
        &diagnostic_so,
        &proof,
        &statement,
        read_only_tag56_cu,
        false,
        false,
        true,
    )?;

    Ok(AtomicProfile22MutationSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile22-mutation".to_string(),
        validator_version: validator_version(),
        production_instruction_wire_ordinal: 57,
        diagnostic_instruction_wire_ordinal: 58,
        diagnostic_sbf_features: DIAGNOSTIC_FEATURES.to_vec(),
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        proof_bytes: proof.len(),
        proof_sha256,
        proof_unmined: true,
        production_pow_bypass_exposed: false,
        default_tag57_fail_closed_host,
        candidate_tag57_rejects_unmined_sbf,
        candidate_tag57_rollback_green,
        paths: vec![program_path, system_path],
        complete_system_claim_quotable,
        complete_view_hvzk_simulator_complete,
        production_profile22_mutation_enabled: false,
        notes: vec![
            "Tag57 has no diagnostic selector and calls the exact tag56 parser/verifier with production PoW before the first CPI or account write. Default builds remain fail-closed.".to_string(),
            "Tag58 exists only in a nondefault local-validator build and reuses the same integrated proof bytes. Its sole acceptance difference is bypassing the transcript-bound PoW predicate.".to_string(),
            "Both marker paths emit single-instruction, overlap-free ledgers. Corruption rollback, exact pool/marker images, duplicate rejection, and a two-signer System-path race are tested.".to_string(),
            "The mutation artifact records, but cannot override, the independent soundness-reduction and complete-view HVZK gates from the literal tag56 acceptance artifact.".to_string(),
        ],
    })
}

pub fn run_stage2_atomic_profile23_mutation() -> Result<AtomicProfile23MutationSummary> {
    use aspis_statement::state_only_profile23::{
        verify_atomic_state_only_profile23_unmined_for_diagnostics_v3,
        verify_atomic_state_only_profile23_v3,
    };
    use aspis_statement::{encode_digest_canonical, AtomicPaymentStatementV3, SpendPublic};
    use aspis_verifier::atomic_payment::{
        atomic_nullifier_address, AtomicPaymentPublicInputs, AtomicPoolStateV1,
        ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED, ATOMIC_NULLIFIER_MAGIC, ATOMIC_NULLIFIER_MARKER_LEN,
        ATOMIC_NULLIFIER_VERSION, ATOMIC_POOL_STATE_LEN,
    };
    use sha2::{Digest as _, Sha256};

    const DIAGNOSTIC_FEATURES: [&str; 2] = [
        "diagnostic-unmined-profile23-mutation",
        "profile23-mutation-candidate",
    ];
    const PRODUCTION_ONLY_FEATURES: [&str; 1] = ["profile23-production"];
    const COMMITTED_UNMINED_PROOF_BYTES: usize = 59_679;
    const COMMITTED_UNMINED_PROOF_SHA256: &str =
        "07f8258f9297bd19d007b5bebdfbb710e8e9e44dcc2277f8cf7a6148db6ce902";
    fn public_inputs(statement: &AtomicPaymentStatementV3) -> AtomicPaymentPublicInputs {
        AtomicPaymentPublicInputs {
            current_anchor: encode_digest_canonical(&statement.spend.anchor),
            nullifier: encode_digest_canonical(&statement.spend.nullifier),
            output_commitment: encode_digest_canonical(&statement.spend.output_commitment),
            output_anchor: encode_digest_canonical(&statement.output_anchor),
            asset_id: statement.spend.asset_id.0,
            fee: statement.spend.fee,
        }
    }

    fn spend_public_bytes(public: &SpendPublic) -> [u8; 104] {
        let mut output = [0u8; 104];
        for (index, value) in public
            .anchor
            .iter()
            .chain(&public.nullifier)
            .chain(&public.output_commitment)
            .chain(core::iter::once(&public.asset_id))
            .enumerate()
        {
            output[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        output[100..].copy_from_slice(&public.fee.to_le_bytes());
        output
    }

    fn read_only_instruction(
        proof: Pubkey,
        statement: &AtomicPaymentStatementV3,
        diagnostic_unmined: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof, false)],
            data: to_vec(&AspisInstruction::VerifyAtomicStateOnlyProfile23V3 {
                pool: statement.pool,
                sequence: statement.sequence,
                public_input: spend_public_bytes(&statement.spend),
                output_anchor: encode_digest_canonical(&statement.output_anchor),
                diagnostic_unmined,
            })?,
        })
    }

    fn instruction_data(public: &AtomicPaymentPublicInputs, diagnostic: bool) -> Result<Vec<u8>> {
        let instruction = if diagnostic {
            AspisInstruction::MeasureAtomicStateOnlyProfile23MutationV3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        } else {
            AspisInstruction::ApplyAtomicStateOnlyProfile23V3 {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            }
        };
        Ok(to_vec(&instruction)?)
    }

    fn transition_instruction(
        proof: Pubkey,
        pool: Pubkey,
        marker: Pubkey,
        payer: Pubkey,
        public: &AtomicPaymentPublicInputs,
        diagnostic: bool,
    ) -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![
                AccountMeta::new_readonly(proof, false),
                AccountMeta::new(pool, false),
                AccountMeta::new(marker, false),
                AccountMeta::new(payer, true),
                AccountMeta::new_readonly(solana_sdk::system_program::id(), false),
            ],
            data: instruction_data(public, diagnostic)?,
        })
    }

    fn signed_transition(
        payer: &Keypair,
        instruction: Instruction,
        blockhash: solana_sdk::hash::Hash,
    ) -> Transaction {
        Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[payer],
            blockhash,
        )
    }

    fn patch_proof_byte(
        rpc: &Rpc,
        payer: &Keypair,
        proof_account: &Pubkey,
        offset: usize,
        byte: u8,
    ) -> Result<()> {
        let instruction = proof_instruction(
            &payer.pubkey(),
            proof_account,
            &AspisInstruction::UploadChunk {
                offset: offset as u32,
                chunk: vec![byte],
            },
        )?;
        let transaction = Transaction::new_signed_with_payer(
            &[instruction],
            Some(&payer.pubkey()),
            &[payer],
            rpc.latest_blockhash()?,
        );
        rpc.send_and_confirm(&transaction)?;
        Ok(())
    }

    fn marker_is_exact(snapshot: &RpcAccountSnapshot, pool: Pubkey, nullifier: &[u8; 32]) -> bool {
        snapshot.owner == aspis_verifier::id()
            && snapshot.data.len() == ATOMIC_NULLIFIER_MARKER_LEN
            && snapshot.data[0..4] == ATOMIC_NULLIFIER_MAGIC
            && snapshot.data[4] == ATOMIC_NULLIFIER_VERSION
            && snapshot.data[5..8] == [0u8; 3]
            && snapshot.data[8..40] == pool.to_bytes()
            && snapshot.data[40..72] == *nullifier
    }

    fn marker_span(markers: &[CuMarker], start: &str, end: &str) -> Option<u64> {
        let start = markers
            .iter()
            .find(|marker| marker.label == start)?
            .remaining;
        let end = markers.iter().find(|marker| marker.label == end)?.remaining;
        start.checked_sub(end)
    }

    fn mutation_ledger(
        markers: &[CuMarker],
        total: u64,
        program_owned: bool,
    ) -> Option<AtomicProfile23MutationLedger> {
        let first = markers.first()?;
        let last = markers.last()?;
        let account_label = if program_owned {
            "atomic61_accounts_validated_program_owned"
        } else {
            "atomic61_accounts_validated_system_owned"
        };
        let marker_label = if program_owned {
            "atomic61_program_marker_ready"
        } else {
            "atomic61_system_marker_created"
        };
        let setup = u64::from(VERIFY_CU_LIMIT).checked_sub(first.remaining)?;
        let validation = marker_span(markers, "atomic61_instruction_start", account_label)?;
        let digest = marker_span(markers, account_label, "atomic61_statement_digest_done")?;
        let verifier = marker_span(
            markers,
            "atomic61_statement_digest_done",
            "atomic61_proof_verified",
        )?;
        let marker = marker_span(markers, "atomic61_proof_verified", marker_label)?;
        let recheck = marker_span(markers, marker_label, "atomic61_state_rechecked")?;
        let writes = marker_span(
            markers,
            "atomic61_state_rechecked",
            "atomic61_state_applied",
        )?;
        let through_last = u64::from(VERIFY_CU_LIMIT).checked_sub(last.remaining)?;
        let post = total.checked_sub(through_last)?;
        let reconciled = setup
            .checked_add(validation)?
            .checked_add(digest)?
            .checked_add(verifier)?
            .checked_add(marker)?
            .checked_add(recheck)?
            .checked_add(writes)?
            .checked_add(post)?;
        Some(AtomicProfile23MutationLedger {
            transaction_setup_cu: setup,
            account_validation_cu: validation,
            statement_decode_and_digest_cu: digest,
            exact_profile23_verifier_cu: verifier,
            marker_prepare_or_cpi_cu: marker,
            mutable_state_recheck_cu: recheck,
            final_account_writes_cu: writes,
            post_last_marker_cu: post,
            reconciled_total_cu: reconciled,
            formula: format!(
                "{setup} + {validation} + {digest} + {verifier} + {marker} + {recheck} + {writes} + {post}"
            ),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn run_path(
        root: &Path,
        so: &Path,
        proof: &[u8],
        statement: &AtomicPaymentStatementV3,
        read_only_tag59_cu: u64,
        preowned_marker: bool,
        exercise_candidate_tag60: bool,
        exercise_concurrency: bool,
        proof_unmined: bool,
    ) -> Result<(AtomicProfile23MutationPathSummary, bool, bool, bool)> {
        let public = public_inputs(statement);
        let pool_key = Pubkey::new_from_array(statement.pool);
        let (marker_key, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
        let mut pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV1 {
            sequence: statement.sequence,
            anchor: public.current_anchor,
        }
        .encode(&mut pool_bytes)?;
        let pool_fixture = write_validator_account_fixture(
            root,
            if preowned_marker {
                "atomic-profile23-program-pool"
            } else {
                "atomic-profile23-system-pool"
            },
            pool_key,
            aspis_verifier::id(),
            &pool_bytes,
        )?;
        let mut fixtures = vec![(pool_key, pool_fixture)];
        if preowned_marker {
            let marker_fixture = write_validator_account_fixture(
                root,
                "atomic-profile23-program-marker",
                marker_key,
                aspis_verifier::id(),
                &[0u8; ATOMIC_NULLIFIER_MARKER_LEN],
            )?;
            fixtures.push((marker_key, marker_fixture));
        }

        let validator = start_validator_with_accounts(root, so, &fixtures)?;
        let rpc = Rpc {
            url: validator.rpc_url.clone(),
            http: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()?,
        };
        let payer = Keypair::new();
        rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, proof, true)?;

        let clean_instruction = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            true,
        )?;
        let clean_tx =
            signed_transition(&payer, clean_instruction.clone(), rpc.latest_blockhash()?);
        let clean = rpc.simulate_verbose(&clean_tx)?;
        ensure!(
            clean.err.is_none(),
            "{} marker profile23 mutation simulation failed: {:?}",
            if preowned_marker {
                "program-owned"
            } else {
                "system-owned"
            },
            clean.err
        );
        let total = clean
            .units
            .context("profile23 mutation simulation omitted CU")?;
        let markers = parse_cu_markers(&clean.logs, "aspis-cu:");
        let ledger = mutation_ledger(&markers, total, preowned_marker)
            .context("profile23 mutation marker ledger incomplete")?;
        ensure!(
            ledger.reconciled_total_cu == total,
            "profile23 mutation ledger mismatch"
        );

        let pool_before = rpc_account_snapshot(&rpc, &pool_key)?
            .context("preloaded profile23 pool account missing")?;
        let marker_before = rpc_account_snapshot(&rpc, &marker_key)?;
        if preowned_marker {
            ensure!(
                marker_before.as_ref().is_some_and(|snapshot| {
                    snapshot.owner == aspis_verifier::id()
                        && snapshot.data == [0u8; ATOMIC_NULLIFIER_MARKER_LEN]
                }),
                "profile23 program-owned marker fixture drift"
            );
        } else {
            ensure!(
                marker_before.is_none(),
                "profile23 System PDA unexpectedly exists"
            );
        }

        let corruption_offset = proof
            .len()
            .checked_sub(1)
            .context("empty profile23 proof")?;
        let original_byte = proof[corruption_offset];
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte ^ 1,
        )?;
        let corrupt_tx = signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?,
            rpc.latest_blockhash()?,
        );
        let corrupt = rpc.simulate_verbose(&corrupt_tx)?;
        let corrupt_rejected = corrupt.err.is_some()
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_before)
            && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
        ensure!(
            corrupt_rejected,
            "corrupt profile23 proof changed atomic state"
        );
        patch_proof_byte(
            &rpc,
            &payer,
            &proof_account.pubkey(),
            corruption_offset,
            original_byte,
        )?;
        // The diagnostic corruption tooth must run while the upload authority
        // is still live. Restore the canonical bytes, then seal once before
        // exercising any production tag-60 surface or committing state.
        finalize_proof(&rpc, &payer, &proof_account.pubkey())?;

        let mut candidate_rejects_unmined = false;
        let mut candidate_accepts_mined = false;
        let mut candidate_rollback = true;
        if exercise_candidate_tag60 {
            let candidate_tx = signed_transition(
                &payer,
                transition_instruction(
                    proof_account.pubkey(),
                    pool_key,
                    marker_key,
                    payer.pubkey(),
                    &public,
                    false,
                )?,
                rpc.latest_blockhash()?,
            );
            let candidate = rpc.simulate_verbose(&candidate_tx)?;
            candidate_rejects_unmined = proof_unmined && candidate.err.is_some();
            candidate_accepts_mined = !proof_unmined && candidate.err.is_none();
            candidate_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref()
                == Some(&pool_before)
                && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
            ensure!(
                candidate_rejects_unmined || candidate_accepts_mined,
                "tag60 outcome disagreed with host PoW classification: proof_unmined={proof_unmined}, error={:?}",
                candidate.err
            );
            ensure!(candidate_rollback, "tag60 simulation changed state");
        }

        let concurrent_exactly_one = if exercise_concurrency {
            let second_payer = Keypair::new();
            rpc.airdrop_and_wait(&second_payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
            let first_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?;
            let second_instruction = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                second_payer.pubkey(),
                &public,
                true,
            )?;
            let blockhash = rpc.latest_blockhash()?;
            let first_tx = signed_transition(&payer, first_instruction, blockhash);
            let second_tx = signed_transition(&second_payer, second_instruction, blockhash);
            let rpc_a = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let rpc_b = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let (first_result, second_result) = thread::scope(|scope| {
                let first = scope.spawn(|| rpc_a.send_and_confirm(&first_tx));
                let second = scope.spawn(|| rpc_b.send_and_confirm(&second_tx));
                (first.join().unwrap(), second.join().unwrap())
            });
            let exactly_one = first_result.is_ok() ^ second_result.is_ok();
            ensure!(
                exactly_one,
                "concurrent profile23 spends did not commit exactly once"
            );
            Some(exactly_one)
        } else {
            rpc.send_and_confirm(&clean_tx)?;
            None
        };

        let pool_after = rpc_account_snapshot(&rpc, &pool_key)?
            .context("profile23 pool disappeared after transition")?;
        let marker_after = rpc_account_snapshot(&rpc, &marker_key)?
            .context("profile23 nullifier marker missing")?;
        let decoded_pool = AtomicPoolStateV1::decode(&pool_after.data)?;
        let sequence_advanced = decoded_pool.sequence == statement.sequence + 1;
        let anchor_replaced = decoded_pool.anchor == public.output_anchor;
        let marker_written = marker_is_exact(&marker_after, pool_key, &public.nullifier);
        ensure!(sequence_advanced && anchor_replaced && marker_written);

        let mut duplicate_public = public;
        duplicate_public.current_anchor = duplicate_public.output_anchor;
        let duplicate_tx = signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &duplicate_public,
                true,
            )?,
            rpc.latest_blockhash()?,
        );
        let duplicate_rejected = rpc.send_and_confirm(&duplicate_tx).is_err();
        let duplicate_no_mutation = duplicate_rejected
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_after)
            && rpc_account_snapshot(&rpc, &marker_key)?.as_ref() == Some(&marker_after);
        ensure!(
            duplicate_no_mutation,
            "duplicate profile23 spend changed state"
        );

        drop(validator);
        Ok((
            AtomicProfile23MutationPathSummary {
                marker_path: if preowned_marker {
                    "program_owned_zeroed"
                } else {
                    "canonical_system_owned_create"
                },
                literal_simulation_cu: total,
                headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - total as i64,
                incremental_over_tag59_cu: total as i64 - read_only_tag59_cu as i64,
                markers,
                ledger,
                clean_simulation_accepted: true,
                corrupt_proof_rejected_without_mutation: corrupt_rejected,
                committed_transition_succeeded: true,
                pool_sequence_advanced_once: sequence_advanced,
                pool_anchor_replaced: anchor_replaced,
                nullifier_marker_written: marker_written,
                duplicate_rejected_without_second_mutation: duplicate_no_mutation,
                concurrent_exactly_one_committed: concurrent_exactly_one,
            },
            candidate_rejects_unmined,
            candidate_accepts_mined,
            candidate_rollback,
        ))
    }

    /// Run the exact production-only binary. Only production tags 59 and 60
    /// are exercised as accepting surfaces; neither diagnostic feature is
    /// present in `so`.
    #[allow(clippy::too_many_lines)]
    fn run_production_path(
        root: &Path,
        so: &Path,
        proof: &[u8],
        unmined_proof: &[u8],
        statement: &AtomicPaymentStatementV3,
        preowned_marker: bool,
        exercise_concurrency: bool,
    ) -> Result<(AtomicProfile23ProductionMutationPathSummary, bool, bool)> {
        let public = public_inputs(statement);
        let pool_key = Pubkey::new_from_array(statement.pool);
        let (marker_key, _) = atomic_nullifier_address(&aspis_verifier::id(), &public.nullifier);
        let mut pool_bytes = [0u8; ATOMIC_POOL_STATE_LEN];
        AtomicPoolStateV1 {
            sequence: statement.sequence,
            anchor: public.current_anchor,
        }
        .encode(&mut pool_bytes)?;
        let pool_fixture = write_validator_account_fixture(
            root,
            if preowned_marker {
                "atomic-profile23-production-program-pool"
            } else {
                "atomic-profile23-production-system-pool"
            },
            pool_key,
            aspis_verifier::id(),
            &pool_bytes,
        )?;
        let mut fixtures = vec![(pool_key, pool_fixture)];
        if preowned_marker {
            fixtures.push((
                marker_key,
                write_validator_account_fixture(
                    root,
                    "atomic-profile23-production-program-marker",
                    marker_key,
                    aspis_verifier::id(),
                    &[0u8; ATOMIC_NULLIFIER_MARKER_LEN],
                )?,
            ));
        }

        let validator = start_validator_with_accounts(root, so, &fixtures)?;
        let rpc = Rpc {
            url: validator.rpc_url.clone(),
            http: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()?,
        };
        let payer = Keypair::new();
        rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, proof, true)?;
        finalize_proof(&rpc, &payer, &proof_account.pubkey())?;
        let unmined_proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &unmined_proof_account, unmined_proof, true)?;
        finalize_proof(&rpc, &payer, &unmined_proof_account.pubkey())?;

        let pool_before = rpc_account_snapshot(&rpc, &pool_key)?
            .context("preloaded production profile23 pool account missing")?;
        let marker_before = rpc_account_snapshot(&rpc, &marker_key)?;
        if preowned_marker {
            ensure!(
                marker_before.as_ref().is_some_and(|snapshot| {
                    snapshot.owner == aspis_verifier::id()
                        && snapshot.data == [0u8; ATOMIC_NULLIFIER_MARKER_LEN]
                }),
                "production profile23 program marker fixture drift"
            );
        } else {
            ensure!(
                marker_before.is_none(),
                "production profile23 System marker already exists"
            );
        }

        // Retain the negative production-PoW tooth in the mined artifact.
        // The committed unmined KAT lives in a distinct proof account, so
        // both outcomes are measured against the same production-only SBF.
        let production_unmined_tag59 = rpc.simulate_verbose(&signed_transition(
            &payer,
            read_only_instruction(unmined_proof_account.pubkey(), statement, false)?,
            rpc.latest_blockhash()?,
        ))?;
        let production_unmined_tag59_error = production_unmined_tag59
            .err
            .clone()
            .context("production-only tag59 accepted the committed unmined KAT")?;
        let production_unmined_tag59_rejected = true;

        let production_unmined_tag60 = signed_transition(
            &payer,
            transition_instruction(
                unmined_proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                false,
            )?,
            rpc.latest_blockhash()?,
        );
        let production_unmined_tag60_landed_error =
            rpc.send_and_confirm_failure(&production_unmined_tag60)?;
        let production_unmined_tag60_rejected = true;
        let production_unmined_tag60_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref()
            == Some(&pool_before)
            && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
        ensure!(
            production_unmined_tag60_rollback,
            "unmined production tag60 changed state"
        );

        // Negative feature-surface teeth. The same mined bytes must succeed
        // on production tags 59/60 immediately afterwards.
        let diagnostic_tag59 = rpc.simulate_verbose(&signed_transition(
            &payer,
            read_only_instruction(proof_account.pubkey(), statement, true)?,
            rpc.latest_blockhash()?,
        ))?;
        let tag59_diagnostic_bit_unavailable = diagnostic_tag59
            .err
            .as_deref()
            .is_some_and(|error| error.contains("InvalidInstructionData"));
        ensure!(
            tag59_diagnostic_bit_unavailable,
            "production-only SBF exposed tag59 diagnostic_unmined or returned the wrong error: {:?}",
            diagnostic_tag59.err
        );
        let unavailable_tag61 = rpc.simulate_verbose(&signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                true,
            )?,
            rpc.latest_blockhash()?,
        ))?;
        let expected_tag61_error = format!(
            "\"Custom\":{}",
            aspis_verifier::atomic_payment::ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED
        );
        let tag61_unavailable = unavailable_tag61
            .err
            .as_deref()
            .is_some_and(|error| error.contains(&expected_tag61_error))
            && unavailable_tag61
                .logs
                .iter()
                .all(|log| !log.contains("aspis-cu:atomic61_instruction_start"));
        ensure!(
            tag61_unavailable,
            "production-only SBF exposed tag61 or returned the wrong error: {:?}",
            unavailable_tag61.err
        );
        ensure!(
            rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_before)
                && rpc_account_snapshot(&rpc, &marker_key)? == marker_before,
            "unavailable diagnostic surface changed state"
        );

        let production_tag59 = rpc.simulate_verbose(&signed_transition(
            &payer,
            read_only_instruction(proof_account.pubkey(), statement, false)?,
            rpc.latest_blockhash()?,
        ))?;
        ensure!(
            production_tag59.err.is_none(),
            "production-only tag59 rejected mined proof: {:?}",
            production_tag59.err
        );
        let tag59_total = production_tag59
            .units
            .context("production-only tag59 omitted CU")?;

        let clean_instruction = transition_instruction(
            proof_account.pubkey(),
            pool_key,
            marker_key,
            payer.pubkey(),
            &public,
            false,
        )?;
        let clean = rpc.simulate_verbose(&signed_transition(
            &payer,
            clean_instruction.clone(),
            rpc.latest_blockhash()?,
        ))?;
        ensure!(
            clean.err.is_none(),
            "production-only tag60 rejected mined proof on {} marker path: {:?}",
            if preowned_marker { "program" } else { "System" },
            clean.err
        );
        let tag60_total = clean.units.context("production-only tag60 omitted CU")?;
        let increment = tag60_total as i64 - tag59_total as i64;
        let reconciled: u64 = (tag59_total as i128 + i128::from(increment))
            .try_into()
            .context("production-only profile23 CU reconciliation overflow")?;
        ensure!(
            reconciled == tag60_total,
            "production tag60 ledger mismatch"
        );
        let ledger = AtomicProfile23ProductionMutationLedger {
            production_read_only_tag59_cu: tag59_total,
            production_tag60_increment_over_tag59_cu: increment,
            production_tag60_total_cu: tag60_total,
            reconciled_total_cu: reconciled,
            formula: format!("{tag59_total} + ({increment})"),
        };

        // Use a real failed transaction, not only simulation, for rollback.
        let corruption_offset = proof
            .len()
            .checked_sub(1)
            .context("empty profile23 proof")?;
        let mut corrupt_proof = proof.to_vec();
        corrupt_proof[corruption_offset] ^= 1;
        let corrupt_proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &corrupt_proof_account, &corrupt_proof, true)?;
        finalize_proof(&rpc, &payer, &corrupt_proof_account.pubkey())?;
        let corrupt = signed_transition(
            &payer,
            transition_instruction(
                corrupt_proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                false,
            )?,
            rpc.latest_blockhash()?,
        );
        let corrupt_landed_error = rpc.send_and_confirm_failure(&corrupt)?;
        let corrupt_rollback = rpc_account_snapshot(&rpc, &pool_key)?.as_ref()
            == Some(&pool_before)
            && rpc_account_snapshot(&rpc, &marker_key)? == marker_before;
        ensure!(corrupt_rollback, "corrupt production tag60 failed rollback");

        let concurrent_exactly_one = if exercise_concurrency {
            let second_payer = Keypair::new();
            rpc.airdrop_and_wait(&second_payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;
            let first = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &public,
                false,
            )?;
            let second = transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                second_payer.pubkey(),
                &public,
                false,
            )?;
            let blockhash = rpc.latest_blockhash()?;
            let first = signed_transition(&payer, first, blockhash);
            let second = signed_transition(&second_payer, second, blockhash);
            let rpc_a = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let rpc_b = Rpc {
                url: validator.rpc_url.clone(),
                http: reqwest::blocking::Client::builder()
                    .timeout(Duration::from_secs(30))
                    .build()?,
            };
            let (a, b) = thread::scope(|scope| {
                let a = scope.spawn(|| rpc_a.send_and_confirm(&first));
                let b = scope.spawn(|| rpc_b.send_and_confirm(&second));
                (a.join().unwrap(), b.join().unwrap())
            });
            let exactly_one = a.is_ok() ^ b.is_ok();
            ensure!(
                exactly_one,
                "production tag60 race did not commit exactly once"
            );
            Some(exactly_one)
        } else {
            rpc.send_and_confirm(&signed_transition(
                &payer,
                clean_instruction,
                rpc.latest_blockhash()?,
            ))?;
            None
        };

        let pool_after = rpc_account_snapshot(&rpc, &pool_key)?
            .context("production profile23 pool missing after tag60")?;
        let marker_after = rpc_account_snapshot(&rpc, &marker_key)?
            .context("production profile23 marker missing after tag60")?;
        let decoded_pool = AtomicPoolStateV1::decode(&pool_after.data)?;
        let sequence_advanced = decoded_pool.sequence == statement.sequence + 1;
        let anchor_replaced = decoded_pool.anchor == public.output_anchor;
        let marker_written = marker_is_exact(&marker_after, pool_key, &public.nullifier);
        ensure!(sequence_advanced && anchor_replaced && marker_written);

        let mut duplicate_public = public;
        duplicate_public.current_anchor = duplicate_public.output_anchor;
        let duplicate = signed_transition(
            &payer,
            transition_instruction(
                proof_account.pubkey(),
                pool_key,
                marker_key,
                payer.pubkey(),
                &duplicate_public,
                false,
            )?,
            rpc.latest_blockhash()?,
        );
        let duplicate_no_mutation = rpc.send_and_confirm(&duplicate).is_err()
            && rpc_account_snapshot(&rpc, &pool_key)?.as_ref() == Some(&pool_after)
            && rpc_account_snapshot(&rpc, &marker_key)?.as_ref() == Some(&marker_after);
        ensure!(
            duplicate_no_mutation,
            "duplicate production tag60 changed state"
        );

        drop(validator);
        Ok((
            AtomicProfile23ProductionMutationPathSummary {
                marker_path: if preowned_marker {
                    "program_owned_zeroed"
                } else {
                    "canonical_system_owned_create"
                },
                proof_accounts_finalized_before_production_verification: true,
                literal_tag59_simulation_cu: tag59_total,
                literal_tag60_simulation_cu: tag60_total,
                headroom_under_1_4m_cu: i64::from(VERIFY_CU_LIMIT) - tag60_total as i64,
                ledger,
                production_unmined_tag59_rejected,
                production_unmined_tag59_error,
                production_unmined_tag60_rejected,
                production_unmined_tag60_rollback_green: production_unmined_tag60_rollback,
                production_unmined_tag60_landed_error,
                production_tag59_accepted_mined_sbf: true,
                production_tag60_clean_simulation_accepted: true,
                corrupt_proof_rejected_with_transaction_rollback: corrupt_rollback,
                corrupt_transaction_landed_error: corrupt_landed_error,
                committed_transition_succeeded: true,
                pool_sequence_advanced_once: sequence_advanced,
                pool_anchor_replaced: anchor_replaced,
                nullifier_marker_written: marker_written,
                duplicate_rejected_without_second_mutation: duplicate_no_mutation,
                concurrent_exactly_one_committed: concurrent_exactly_one,
            },
            tag59_diagnostic_bit_unavailable,
            tag61_unavailable,
        ))
    }

    let root = workspace_root()?;
    let committed_unmined_path =
        root.join("results/stage2/proofs/atomic_state_only_profile23_v3_unmined.bin");
    let committed_unmined_proof = fs::read(&committed_unmined_path).with_context(|| {
        format!(
            "read committed unmined profile23 proof {}",
            committed_unmined_path.display()
        )
    })?;
    let committed_unmined_sha256 = Sha256::digest(&committed_unmined_proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    ensure!(
        committed_unmined_proof.len() == COMMITTED_UNMINED_PROOF_BYTES,
        "committed unmined profile23 proof geometry drift"
    );
    ensure!(
        committed_unmined_sha256 == COMMITTED_UNMINED_PROOF_SHA256,
        "committed unmined profile23 proof KAT drift"
    );
    let (proof_path, proof_source_override) = profile23_proof_path(&root);
    let statement_selection = profile23_statement_selection(&root, proof_source_override)?;
    let statement = &statement_selection.statement;
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read integrated profile23 proof {}", proof_path.display()))?;
    let proof_sha256 = Sha256::digest(&proof)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    if !proof_source_override {
        ensure!(
            proof.len() == COMMITTED_UNMINED_PROOF_BYTES,
            "integrated profile23 proof geometry drift"
        );
        ensure!(
            proof_sha256 == COMMITTED_UNMINED_PROOF_SHA256,
            "integrated profile23 proof KAT drift"
        );
    }
    verify_atomic_state_only_profile23_unmined_for_diagnostics_v3(
        &proof, statement, HOST_HASH, None,
    )
    .map_err(|error| anyhow!("profile23 mutation host replay: {error:?}"))?;
    let proof_unmined =
        verify_atomic_state_only_profile23_v3(&proof, statement, HOST_HASH, None).is_err();
    let committed_unmined_statement = profile23_fixture_statement()?;
    verify_atomic_state_only_profile23_unmined_for_diagnostics_v3(
        &committed_unmined_proof,
        &committed_unmined_statement,
        HOST_HASH,
        None,
    )
    .map_err(|error| anyhow!("committed unmined profile23 host replay: {error:?}"))?;
    ensure!(
        verify_atomic_state_only_profile23_v3(
            &committed_unmined_proof,
            &committed_unmined_statement,
            HOST_HASH,
            None,
        )
        .is_err(),
        "committed unmined profile23 KAT passed production host verification"
    );

    let acceptance_artifact = root.join(if proof_source_override {
        "results/stage2/atomic_state_only_profile23_acceptance_production_mined.json"
    } else {
        "results/stage2/atomic_state_only_profile23_acceptance.json"
    });
    let acceptance: Value =
        serde_json::from_slice(&fs::read(&acceptance_artifact).with_context(|| {
            format!(
                "read matching profile23 acceptance artifact {}",
                acceptance_artifact.display()
            )
        })?)?;
    ensure!(
        acceptance["proof_sha256"].as_str() == Some(&proof_sha256),
        "tag59/tag61 proof mismatch; run stage2-atomic-profile23-acceptance with the same ASPIS_PROFILE23_PROOF first"
    );
    ensure!(
        acceptance["proof_unmined"].as_bool() == Some(proof_unmined),
        "tag59/tag61 PoW classification mismatch"
    );
    let recorded_statement_path = statement_selection
        .path
        .as_deref()
        .map(|path| profile23_recorded_path(&root, path));
    ensure!(
        acceptance["statement_source_override"].as_bool()
            == Some(statement_selection.source_override),
        "tag59/tag61 statement-source classification mismatch"
    );
    ensure!(
        match recorded_statement_path.as_deref() {
            Some(path) => acceptance["statement_path"].as_str() == Some(path),
            None => acceptance["statement_path"].is_null(),
        },
        "tag59/tag61 statement path mismatch; run acceptance with the same ASPIS_PROFILE23_STATEMENT"
    );
    ensure!(
        match statement_selection.sha256.as_deref() {
            Some(sha256) => acceptance["statement_sha256"].as_str() == Some(sha256),
            None => acceptance["statement_sha256"].is_null(),
        },
        "tag59/tag61 statement sidecar SHA-256 mismatch"
    );
    ensure!(
        acceptance["statement_pool_hex"].as_str() == Some(profile23_hex(&statement.pool).as_str())
            && acceptance["statement_sequence"].as_u64() == Some(statement.sequence)
            && acceptance["canonical_public_input_digest"].as_str()
                == Some(statement_selection.canonical_public_input_digest.as_str()),
        "tag59/tag61 canonical public statement binding mismatch"
    );
    let read_only_tag59_cu = acceptance["literal_simulation_cu"]
        .as_u64()
        .context("profile23 acceptance artifact omitted literal CU")?;
    let soundness_audit: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/profile23_d_after_g_soundness_epro.json"),
    )?)?;
    let soundness_bookable = soundness_audit["bookable"].as_bool().unwrap_or(false);
    let hvzk_closure: Value = serde_json::from_slice(&fs::read(
        root.join("results/stage2/profile23_computational_hvzk_closure.json"),
    )?)?;
    ensure!(
        hvzk_closure["artifact"].as_str() == Some("profile23_computational_hvzk_closure"),
        "profile23 HVZK closure artifact identity drift"
    );
    let complete_view_hvzk_simulator_complete = hvzk_closure["theorem_gates"]
        ["complete_view_computational_hvzk_in_declared_model"]
        .as_bool()
        .context("profile23 HVZK closure omitted complete-view theorem gate")?;
    ensure!(
        complete_view_hvzk_simulator_complete,
        "profile23 complete-view computational HVZK gate is not closed"
    );
    ensure!(
        hvzk_closure["claim"]["complete_system_computational_privacy_quotable_in_declared_model"]
            .as_bool()
            == Some(true),
        "profile23 HVZK closure does not quote the complete-system claim"
    );
    let expected_layout_fingerprint = format!(
        "0x{:016x}",
        aspis_core::state_only_hiding::state_only_profile23_hiding_layout_factor_fingerprint_v3()
    );
    ensure!(
        hvzk_closure["affine_closure"]["layout_factor_fingerprint"].as_str()
            == Some(expected_layout_fingerprint.as_str()),
        "profile23 HVZK closure layout fingerprint drift"
    );
    let expected_good23_fingerprint =
        aspis_prover::state_only_good23::profile23_good_schedule_definition_fingerprint(HOST_HASH)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
    let expected_good23_fingerprint = format!("0x{expected_good23_fingerprint}");
    ensure!(
        hvzk_closure["affine_closure"]["good23_definition_fingerprint"].as_str()
            == Some(expected_good23_fingerprint.as_str()),
        "profile23 HVZK closure Good23 definition fingerprint drift"
    );
    if proof_source_override {
        ensure!(
            hvzk_closure["complete_public_view"]["proof_bytes_production"].as_u64()
                == Some(proof.len() as u64),
            "profile23 HVZK closure production proof geometry drift"
        );
        ensure!(
            hvzk_closure["complete_public_view"]["proof_sha256_production"].as_str()
                == Some(proof_sha256.as_str()),
            "profile23 HVZK closure production proof KAT drift"
        );
    } else {
        ensure!(
            hvzk_closure["complete_public_view"]["proof_bytes"].as_u64()
                == Some(proof.len() as u64),
            "profile23 HVZK closure unmined proof geometry drift"
        );
        ensure!(
            hvzk_closure["complete_public_view"]["proof_sha256_unmined_fixture"].as_str()
                == Some(proof_sha256.as_str()),
            "profile23 HVZK closure unmined proof KAT drift"
        );
    }
    ensure!(
        hvzk_closure["production_release"]["enabled_by_this_artifact"].as_bool() == Some(false),
        "profile23 HVZK closure must not independently authorize production"
    );

    let default_tag60 = instruction_data(&public_inputs(statement), false)?;
    let default_tag60_fail_closed_host =
        aspis_verifier::process_instruction(&aspis_verifier::id(), &[], &default_tag60)
            == Err(solana_sdk::program_error::ProgramError::Custom(
                ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED,
            ));
    ensure!(
        default_tag60_fail_closed_host,
        "default tag60 is not fail-closed"
    );

    let diagnostic_so = build_sbf_with_features(
        &root,
        &DIAGNOSTIC_FEATURES,
        "aspis_verifier_atomic_profile23_mutation_diagnostic.so",
    )?;
    let (
        program_path,
        candidate_tag60_rejects_unmined_sbf,
        candidate_tag60_accepts_mined_sbf,
        candidate_tag60_rollback_green,
    ) = run_path(
        &root,
        &diagnostic_so,
        &proof,
        statement,
        read_only_tag59_cu,
        true,
        true,
        false,
        proof_unmined,
    )?;
    let (system_path, _, _, _) = run_path(
        &root,
        &diagnostic_so,
        &proof,
        statement,
        read_only_tag59_cu,
        false,
        false,
        true,
        proof_unmined,
    )?;

    // Preserve the committed unmined diagnostic workflow.  The exact
    // production binary is exercised only when the caller explicitly points
    // at mined bytes, so an accidental default-fixture run cannot be mistaken
    // for a production closure artifact.
    let production_only_mined_override_exercised = proof_source_override && !proof_unmined;
    let (
        production_alias_forbidden_feature_unions_rejected,
        production_alias_forbidden_feature_unions_tested,
    ) = if production_only_mined_override_exercised {
        check_profile23_production_feature_isolation(&root, &PRODUCTION_ONLY_FEATURES)?
    } else {
        (None, Vec::new())
    };
    let (
        production_paths,
        production_only_sbf_bytes,
        production_only_sbf_sha256,
        production_only_unmined_tag59_rejected,
        production_only_unmined_tag60_rejected,
        production_only_unmined_tag60_rollback_green,
        production_only_tag59_diagnostic_bit_unavailable,
        production_only_tag61_unavailable,
    ) = if production_only_mined_override_exercised {
        let production_so = build_profile23_production_default_sbf(
            &root,
            &PRODUCTION_ONLY_FEATURES,
            "aspis_verifier_atomic_profile23_mutation_production.so",
        )?;
        let production_so_bytes = fs::read(&production_so).with_context(|| {
            format!(
                "read production-only profile23 SBF {}",
                production_so.display()
            )
        })?;
        let production_so_sha256 = Sha256::digest(&production_so_bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let (program, program_tag59_closed, program_tag61_closed) = run_production_path(
            &root,
            &production_so,
            &proof,
            &committed_unmined_proof,
            statement,
            true,
            false,
        )?;
        let (system, system_tag59_closed, system_tag61_closed) = run_production_path(
            &root,
            &production_so,
            &proof,
            &committed_unmined_proof,
            statement,
            false,
            true,
        )?;
        let unmined_tag59_rejected =
            program.production_unmined_tag59_rejected && system.production_unmined_tag59_rejected;
        let unmined_tag60_rejected =
            program.production_unmined_tag60_rejected && system.production_unmined_tag60_rejected;
        let unmined_tag60_rollback = program.production_unmined_tag60_rollback_green
            && system.production_unmined_tag60_rollback_green;
        (
            vec![program, system],
            Some(production_so_bytes.len()),
            Some(production_so_sha256),
            Some(unmined_tag59_rejected),
            Some(unmined_tag60_rejected),
            Some(unmined_tag60_rollback),
            Some(program_tag59_closed && system_tag59_closed),
            Some(program_tag61_closed && system_tag61_closed),
        )
    } else {
        (Vec::new(), None, None, None, None, None, None, None)
    };

    Ok(AtomicProfile23MutationSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: if proof_source_override {
            if let Some(statement_path) = statement_selection.path.as_ref() {
                format!(
                    "ASPIS_PROFILE23_PROOF={} ASPIS_PROFILE23_STATEMENT={} NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile23-mutation",
                    proof_path.display(),
                    statement_path.display()
                )
            } else {
                format!(
                    "ASPIS_PROFILE23_PROOF={} NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile23-mutation",
                    proof_path.display()
                )
            }
        } else {
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-atomic-profile23-mutation".to_string()
        },
        validator_version: validator_version(),
        production_instruction_wire_ordinal: 60,
        diagnostic_instruction_wire_ordinal: 61,
        finalize_proof_instruction_wire_ordinal: 62,
        diagnostic_sbf_features: DIAGNOSTIC_FEATURES.to_vec(),
        proof_path: proof_path
            .strip_prefix(&root)
            .unwrap_or(&proof_path)
            .display()
            .to_string(),
        proof_source_override,
        proof_bytes: proof.len(),
        proof_sha256,
        proof_unmined,
        statement_path: recorded_statement_path,
        statement_source_override: statement_selection.source_override,
        statement_sha256: statement_selection.sha256.clone(),
        statement_pool_hex: profile23_hex(&statement.pool),
        statement_sequence: statement.sequence,
        canonical_public_input_digest: statement_selection
            .canonical_public_input_digest
            .clone(),
        production_pow_bypass_exposed: false,
        default_tag60_fail_closed_host,
        candidate_tag60_rejects_unmined_sbf,
        candidate_tag60_accepts_mined_sbf,
        candidate_tag60_outcome_matches_pow: candidate_tag60_rejects_unmined_sbf
            || candidate_tag60_accepts_mined_sbf,
        candidate_tag60_rollback_green,
        paths: vec![program_path, system_path],
        production_only_sbf_features: PRODUCTION_ONLY_FEATURES.to_vec(),
        production_only_sbf_bytes,
        production_only_sbf_sha256,
        production_only_mined_override_exercised,
        production_only_unmined_tag59_rejected,
        production_only_unmined_tag60_rejected,
        production_only_unmined_tag60_rollback_green,
        production_only_tag59_diagnostic_bit_unavailable,
        production_only_tag61_unavailable,
        production_alias_forbidden_feature_unions_rejected,
        production_alias_forbidden_feature_unions_tested,
        production_paths,
        soundness_bookable,
        complete_view_hvzk_simulator_complete,
        production_profile23_mutation_enabled: false,
        notes: vec![
            "Tag60 has no diagnostic selector and calls the exact tag59 parser/verifier with production PoW before the first CPI or account write. Its simulated outcome is required to match the host mined/unmined classification. Default builds remain fail-closed.".to_string(),
            if proof_unmined {
                "Tag61 exists only in a nondefault local-validator build and reuses the same integrated unmined proof bytes. Its sole acceptance difference is bypassing the transcript-bound PoW predicate.".to_string()
            } else {
                format!(
                    "ASPIS_PROFILE23_PROOF supplied mined bytes: the command additionally built with the isolated feature set {}, proved tag59's diagnostic bit and tag61 unavailable, and ran exact production tags59/60 on both marker paths.",
                    PRODUCTION_ONLY_FEATURES.join(",")
                )
            },
            if statement_selection.source_override {
                "ASPIS_PROFILE23_STATEMENT supplied the canonical public statement used by host, diagnostic SBF, and production SBF paths; its exact file and canonical transcript digest match the tag59 acceptance artifact.".to_string()
            } else {
                "No statement sidecar was supplied; this artifact uses the unchanged built-in Profile23 fixture statement.".to_string()
            },
            "Both marker paths emit single-instruction, overlap-free ledgers. Corruption rollback, exact pool/marker images, duplicate rejection, and a two-signer System-path race are tested.".to_string(),
            if production_only_mined_override_exercised {
                "The production-only paths load the committed unmined KAT into a second proof account, require production tags59/60 to reject it (with a landed failed tag60 transaction and exact rollback), submit a separately corrupted mined tag60 transaction to prove rollback, commit mined tag60 on both marker paths, and reconcile each exact tag60 total as same-binary tag59 plus the net mutation wrapper increment.".to_string()
            } else {
                "Production-only tag60 execution is intentionally skipped for the default unmined fixture; supply a mined ASPIS_PROFILE23_PROOF override to populate production_paths.".to_string()
            },
            if production_alias_forbidden_feature_unions_rejected == Some(true) {
                "The explicit profile23-production KAT additionally compile-failed every diagnostic and legacy Profile20/21/22 candidate union, both individually and as one grouped feature-unification tooth, with the dedicated isolation marker.".to_string()
            } else {
                "The production-alias feature-isolation compile-fail tooth remains dormant until the measured SBF feature is exactly profile23-production.".to_string()
            },
            "The mutation artifact records, but cannot override, the independent complete-Good/q3 soundness audit and complete-view HVZK release gate.".to_string(),
        ],
    })
}
pub fn run_stage2_state_only_relation_structural_probe(
) -> Result<StateOnlyRelationStructuralSummary> {
    use aspis_statement::state_only_verify::StateOnlyRelationStructuralPhase;
    use sha2::{Digest as _, Sha256};

    const REPETITIONS: usize = 5;
    const LEGACY_RELATION_BUCKET_CU: u64 = 225_230;
    fn ignore_relation_trace(_: StateOnlyRelationStructuralPhase) {}

    let root = workspace_root()?;
    let proof_path =
        root.join("results/stage2/proofs/state_only_width28_global_inactive_p20_unmined.bin");
    let proof = fs::read(&proof_path)
        .with_context(|| format!("read profile20 fixture {}", proof_path.display()))?;
    let statement_digest: [u8; 32] =
        Sha256::digest(b"aspis/state-only/width28/global-copy-inactive-hiding/v1").into();

    for deferred_binary_copy in [false, true] {
        aspis_statement::state_only_verify::verify_state_only_relation_structural_probe_unmined_traced(
            &proof,
            &statement_digest,
            HOST_HASH,
            deferred_binary_copy,
            false,
            ignore_relation_trace,
        )
        .map_err(|error| anyhow!("host clean relation mode={deferred_binary_copy}: {error:?}"))?;
        aspis_statement::state_only_verify::verify_state_only_relation_structural_probe_unmined_traced(
            &proof,
            &statement_digest,
            HOST_HASH,
            deferred_binary_copy,
            true,
            ignore_relation_trace,
        )
        .map_err(|error| anyhow!("host corruption tooth mode={deferred_binary_copy}: {error:?}"))?;
    }

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    upload_proof(&rpc, &payer, &proof_account, &proof, true)?;

    let make_instruction = |deferred_binary_copy, corrupt_claim| -> Result<Instruction> {
        let instruction = AspisInstruction::StateOnlyRelationStructuralProbe {
            statement_digest,
            deferred_binary_copy,
            corrupt_claim,
        };
        let data = to_vec(&instruction)?;
        ensure!(
            data.first() == Some(&44),
            "relation structural probe tag drifted"
        );
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![AccountMeta::new_readonly(proof_account.pubkey(), false)],
            data,
        })
    };
    let simulate = |instruction: Instruction| -> Result<SimulationResult> {
        let blockhash = rpc.latest_blockhash()?;
        let transaction = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
                instruction,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        rpc.simulate_verbose(&transaction)
    };

    let mut variants = Vec::new();
    for (deferred_binary_copy, mode) in [
        (false, "legacy_grouped_binary"),
        (true, "deferred_two_fold_binary"),
    ] {
        let mut simulation_cu = Vec::with_capacity(REPETITIONS);
        let mut markers = Vec::new();
        for repetition in 0..REPETITIONS {
            let result = simulate(make_instruction(deferred_binary_copy, false)?)?;
            ensure!(
                result.err.is_none(),
                "clean relation mode={mode} failed: {:?}",
                result.err
            );
            simulation_cu.push(result.units.context("relation probe omitted CU")?);
            if repetition == 0 {
                markers = parse_cu_markers(&result.logs, "aspis-cu:");
            }
        }
        let simulation_cu_mean =
            simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
        let corruption = simulate(make_instruction(deferred_binary_copy, true)?)?;
        ensure!(
            corruption.err.is_none(),
            "relation corruption was not rejected in mode={mode}: {:?}",
            corruption.err
        );
        variants.push(StateOnlyRelationStructuralVariant {
            mode,
            deferred_binary_copy,
            simulation_cu,
            simulation_cu_mean,
            markers,
            corruption_probe_cu: corruption.units,
            corruption_rejected_host: true,
            corruption_rejected_sbf: true,
        });
    }
    let optimized_savings_cu =
        (variants[0].simulation_cu_mean - variants[1].simulation_cu_mean).round() as i64;
    let projected_optimized_relation_bucket_cu =
        LEGACY_RELATION_BUCKET_CU as i64 - optimized_savings_cu;
    Ok(StateOnlyRelationStructuralSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-state-only-relation-structural-probe".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 44,
        repetitions: REPETITIONS,
        profile_id: 20,
        rho: "1/512",
        query_count: 16,
        proof_bytes: proof.len(),
        variants,
        optimized_savings_cu,
        legacy_relation_bucket_cu: LEGACY_RELATION_BUCKET_CU,
        projected_optimized_relation_bucket_cu,
        random_off_domain_identity_points: 64,
        exact_equivalence_scope: "same fixed 64x16 inactive-copy covector before folding and after each of four random-QM31 dual folds; same full profile20 relation acceptance",
        overlap_scope: "the A/B delta replaces only the 225230-CU relation bucket; parser, transcript, terminal, Merkle openings, queries, and return are identical and excluded",
        notes: vec![
            "The optimized component retains the eight distinct public u16 masks through round zero, then evaluates both low dual folds with nine shared alpha1^h*alpha0^l cross-products and selected additions. It becomes the same 64-value dense component before rounds two and three.".to_string(),
            "The core guard compares legacy and optimized weights, terminal dots, and all four fold states at 64 fresh random QM31 challenge sequences. Both full profile20 paths accept the same proof; a prepared point-claim perturbation is rejected on host and SBF in each mode.".to_string(),
            "Tag44 is read-only and unmined-diagnostic only. It changes no proof bytes, transcript labels/order, challenges, OOD samples, sumcheck equations, query powers, openings, or production acceptance path.".to_string(),
        ],
    })
}

fn make_atomic20_ledger(
    setup: u64,
    proof_load: u64,
    parse: u64,
    transcript: u64,
    terminal: u64,
    relation: u64,
    openings: u64,
    queries: u64,
    verifier_return: u64,
    post: u64,
    source: &str,
) -> AtomicProfile20CostLedger {
    let buckets = [
        setup,
        proof_load,
        parse,
        transcript,
        terminal,
        relation,
        openings,
        queries,
        verifier_return,
        post,
    ];
    AtomicProfile20CostLedger {
        transaction_setup_and_public_decode_cu: setup,
        proof_load_cu: proof_load,
        parse_cu: parse,
        transcript_cu: transcript,
        atomic_terminal_cu: terminal,
        relation_cu: relation,
        merkle_openings_cu: openings,
        query_arithmetic_cu: queries,
        verifier_return_cu: verifier_return,
        post_last_marker_cu: post,
        overlap_reconciled_total_cu: buckets.iter().sum(),
        formula: buckets
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(" + "),
        source: source.to_string(),
    }
}

/// Real two-phase proof comparison at g16. The transcript header and every
/// Merkle root are genuinely changed for the radix-4 variant; this is the
/// teeth-first checkpoint before regenerating the expensive frozen g32 KAT.
pub fn run_stage2_radix4_g16() -> Result<Radix4G16Summary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 2 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let digest = crate::host_statement_digest(0);
    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let mut variants = Vec::new();
    let mut radix4_proof = None;

    for mode in [MerkleMode::MinimalSubtree, MerkleMode::Radix4MinimalSubtree] {
        let proof = prove_with_synthetic_second_phase(
            profile,
            &coeffs,
            &digest,
            &ProveOptions {
                fold_payload: FoldPayload::RawFibers,
                merkle_mode: mode,
            },
            HOST_HASH,
        );
        ensure!(
            aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
            "generated {mode:?} proof failed host verification"
        );
        let corruption = crate::host::corruption_suite(profile, &proof, &digest);
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, &proof, true)?;

        let mut samples = Vec::new();
        for _ in 0..REPETITIONS {
            let instruction = AspisInstruction::Verify {
                statement_digest: digest,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let (units, error) = rpc.simulate(&transaction)?;
            ensure!(
                error.is_none(),
                "{mode:?} production Verify failed: {error:?}"
            );
            samples.push(units.context("production Verify did not report units")?);
        }
        let mean = samples.iter().sum::<u64>() as f64 / samples.len() as f64;
        let proof_hash = HOST_HASH(&[&proof]);
        let proof_sha256 = proof_hash
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        variants.push(Radix4ProofVariant {
            merkle_mode: match mode {
                MerkleMode::MinimalSubtree => "binary_minimal_subtree",
                MerkleMode::Radix4MinimalSubtree => "radix4_minimal_subtree",
                MerkleMode::SinglePaths => unreachable!(),
            },
            proof_bytes: proof.len(),
            proof_sha256,
            verify_cu: samples,
            verify_cu_mean: mean,
            host_corruption_cases: corruption.len(),
            host_corruption_all_rejected: corruption.iter().all(|case| case.rejected),
        });
        if mode == MerkleMode::Radix4MinimalSubtree {
            radix4_proof = Some(proof);
        }
    }

    let mut corrupted = radix4_proof.context("radix-4 proof missing")?;
    let header = aspis_core::proof::Header::parse(&corrupted).context("radix-4 header")?;
    let body_offset = aspis_core::proof::HEADER_LEN
        + aspis_core::proof::transcript_records_len(profile.num_rounds() as usize, header.flags)
        + profile.final_poly_len() as usize * 16
        + 8;
    let unique_count =
        u16::from_le_bytes(corrupted[body_offset..body_offset + 2].try_into().unwrap()) as usize;
    let main_node_count_offset = body_offset + 2 + unique_count * (32 + 64);
    let node_count = u32::from_le_bytes(
        corrupted[main_node_count_offset..main_node_count_offset + 4]
            .try_into()
            .unwrap(),
    );
    ensure!(
        node_count > 0,
        "radix-4 layer-0 frontier unexpectedly empty"
    );
    corrupted[main_node_count_offset + 4] ^= 1;
    let host_corruption = matches!(
        aspis_core::verify(&corrupted, &digest, HOST_HASH),
        Err(aspis_core::VerifyError::MerkleMismatch { layer: 0 })
    );

    let corrupted_account = Keypair::new();
    upload_proof(&rpc, &payer, &corrupted_account, &corrupted, true)?;
    let instruction = AspisInstruction::Verify {
        statement_digest: digest,
    };
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            proof_instruction(&payer.pubkey(), &corrupted_account.pubkey(), &instruction)?,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (_, sbf_corruption_error) = rpc.simulate(&transaction)?;

    let binary_mean = variants[0].verify_cu_mean;
    let radix4_mean = variants[1].verify_cu_mean;
    let savings = (binary_mean - radix4_mean).round() as i64;
    let proof_bytes_delta = variants[1].proof_bytes as i64 - variants[0].proof_bytes as i64;
    Ok(Radix4G16Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-radix4-g16".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        repetitions: REPETITIONS,
        second_phase_enabled: true,
        variants,
        radix4_savings_cu: savings,
        radix4_savings_percent: savings as f64 / binary_mean * 100.0,
        radix4_proof_bytes_delta: proof_bytes_delta,
        radix4_frontier_corruption_rejected_host: host_corruption,
        radix4_frontier_corruption_rejected_sbf: sbf_corruption_error.is_some(),
        notes: vec![
            "Both rows are real claim-free Stage-1 synthetic-C2 proofs over identical coefficients and statement bytes; only the transcript-bound Merkle mode differs.".to_string(),
            "Production Verify uses the cached-domain and unit-circle-conjugate verifier kernels selected by the Stage-2 kernel probe; VerifyFast remains a wire-compatible alias of the same path.".to_string(),
            "The radix-4 root uses domain byte 0x12 and one SHA-256 input containing four ordered child hashes. It is not a reinterpretation of a binary root.".to_string(),
            "A layer-0 radix-4 frontier hash is deliberately corrupted after proof construction and must reject both on host and SBF.".to_string(),
            "This g16 checkpoint does not re-pin the frozen g32 proof or transcript KAT; that happens only after this comparison is accepted.".to_string(),
        ],
    })
}

pub fn run_stage2_radix4_g32() -> Result<Radix4G32Summary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let profile = &aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G32;
    let digest = crate::host_statement_digest(0);
    let coeffs = seeded_coeffs(profile.log_rows, 1);

    let binary_path = root.join("results/stage1/proofs/capacity_lr10_q36_g32_v3_c2.bin");
    let binary_proof = fs::read(&binary_path)
        .with_context(|| format!("read frozen binary proof {}", binary_path.display()))?;
    ensure!(
        aspis_core::verify(&binary_proof, &digest, HOST_HASH).is_ok(),
        "frozen binary g32 proof failed current host verification"
    );

    let proof_dir = root.join("results/stage2/proofs");
    fs::create_dir_all(&proof_dir)?;
    let radix4_path = proof_dir.join("capacity_lr10_q36_g32_v3_c2_radix4.bin");
    let cached_radix4 = fs::read(&radix4_path).ok().filter(|proof| {
        let correct_mode = aspis_core::proof::Header::parse(proof)
            .map(|header| header.merkle_mode == MerkleMode::Radix4MinimalSubtree as u8)
            .unwrap_or(false);
        correct_mode && aspis_core::verify(proof, &digest, HOST_HASH).is_ok()
    });
    let (radix4_proof, radix4_source, generation_seconds) = if let Some(proof) = cached_radix4 {
        (
            proof,
            format!("reused host-verified cache {}", radix4_path.display()),
            None,
        )
    } else {
        eprintln!("stage2-radix4-g32: searching a fresh 32-bit grinding nonce");
        let started = Instant::now();
        let proof = prove_with_synthetic_second_phase(
            profile,
            &coeffs,
            &digest,
            &ProveOptions {
                fold_payload: FoldPayload::RawFibers,
                merkle_mode: MerkleMode::Radix4MinimalSubtree,
            },
            HOST_HASH,
        );
        let elapsed = started.elapsed().as_secs_f64();
        ensure!(
            aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
            "fresh radix-4 g32 proof failed host verification"
        );
        fs::write(&radix4_path, &proof)?;
        (
            proof,
            format!("generated and cached {}", radix4_path.display()),
            Some(elapsed),
        )
    };

    let hex = |bytes: &[u8]| {
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };
    let root_start = aspis_core::proof::HEADER_LEN;
    let binary_first_root = hex(&binary_proof[root_start..root_start + 32]);
    let radix4_first_root = hex(&radix4_proof[root_start..root_start + 32]);
    ensure!(
        binary_first_root != radix4_first_root,
        "radix-4 and binary C1 roots unexpectedly match"
    );
    let transcript_kat_unchanged = aspis_core::transcript::transcript_kat(HOST_HASH)
        == aspis_core::transcript::TRANSCRIPT_KAT_EXPECTED;
    ensure!(
        transcript_kat_unchanged,
        "schedule-level transcript KAT drifted"
    );

    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 3 * LAMPORTS_PER_SOL)?;

    let mut variants = Vec::new();
    for (mode_name, proof) in [
        ("binary_minimal_subtree", &binary_proof),
        ("radix4_minimal_subtree", &radix4_proof),
    ] {
        let corruption = crate::host::corruption_suite(profile, proof, &digest);
        let proof_account = Keypair::new();
        upload_proof(&rpc, &payer, &proof_account, proof, true)?;
        let mut samples = Vec::new();
        for _ in 0..REPETITIONS {
            let instruction = AspisInstruction::Verify {
                statement_digest: digest,
            };
            let blockhash = rpc.latest_blockhash()?;
            let transaction = Transaction::new_signed_with_payer(
                &[
                    ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                    proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                ],
                Some(&payer.pubkey()),
                &[&payer],
                blockhash,
            );
            let (units, error) = rpc.simulate(&transaction)?;
            ensure!(
                error.is_none(),
                "{mode_name} production Verify failed: {error:?}"
            );
            samples.push(units.context("production Verify did not report units")?);
        }
        let proof_hash = HOST_HASH(&[proof]);
        variants.push(Radix4ProofVariant {
            merkle_mode: mode_name,
            proof_bytes: proof.len(),
            proof_sha256: hex(&proof_hash),
            verify_cu_mean: samples.iter().sum::<u64>() as f64 / samples.len() as f64,
            verify_cu: samples,
            host_corruption_cases: corruption.len(),
            host_corruption_all_rejected: corruption.iter().all(|case| case.rejected),
        });
    }

    let mut corrupted = radix4_proof.clone();
    let header = aspis_core::proof::Header::parse(&corrupted).context("radix-4 header")?;
    let body_offset = aspis_core::proof::HEADER_LEN
        + aspis_core::proof::transcript_records_len(profile.num_rounds() as usize, header.flags)
        + profile.final_poly_len() as usize * 16
        + 8;
    let unique_count =
        u16::from_le_bytes(corrupted[body_offset..body_offset + 2].try_into().unwrap()) as usize;
    let main_node_count_offset = body_offset + 2 + unique_count * (32 + 64);
    let node_count = u32::from_le_bytes(
        corrupted[main_node_count_offset..main_node_count_offset + 4]
            .try_into()
            .unwrap(),
    );
    ensure!(node_count > 0, "radix-4 g32 frontier unexpectedly empty");
    corrupted[main_node_count_offset + 4] ^= 1;
    let host_corruption = matches!(
        aspis_core::verify(&corrupted, &digest, HOST_HASH),
        Err(aspis_core::VerifyError::MerkleMismatch { layer: 0 })
    );
    let corrupted_account = Keypair::new();
    upload_proof(&rpc, &payer, &corrupted_account, &corrupted, true)?;
    let instruction = AspisInstruction::Verify {
        statement_digest: digest,
    };
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            proof_instruction(&payer.pubkey(), &corrupted_account.pubkey(), &instruction)?,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let (_, sbf_corruption_error) = rpc.simulate(&transaction)?;

    let binary_mean = variants[0].verify_cu_mean;
    let radix4_mean = variants[1].verify_cu_mean;
    let savings = (binary_mean - radix4_mean).round() as i64;
    let proof_bytes_delta = variants[1].proof_bytes as i64 - variants[0].proof_bytes as i64;
    Ok(Radix4G32Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-radix4-g32".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        repetitions: REPETITIONS,
        binary_proof_source: binary_path.display().to_string(),
        radix4_proof_source: radix4_source,
        radix4_generation_seconds: generation_seconds,
        binary_first_root,
        radix4_first_root,
        root_changed: true,
        transcript_kat_unchanged,
        variants,
        radix4_savings_cu: savings,
        radix4_savings_percent: savings as f64 / binary_mean * 100.0,
        radix4_proof_bytes_delta: proof_bytes_delta,
        radix4_frontier_corruption_rejected_host: host_corruption,
        radix4_frontier_corruption_rejected_sbf: sbf_corruption_error.is_some(),
        notes: vec![
            "Both proofs use the literal q36/g32 profile, synthetic C2, identical coefficients, and identical statement bytes. Production Verify selects the optimized denominator/domain path.".to_string(),
            "The Merkle-mode header byte is transcript-absorbed, so roots, challenges, grinding nonce, query positions, proof digest, and proof bytes are all freshly generated for radix-4.".to_string(),
            "TRANSCRIPT_KAT_EXPECTED intentionally does not move: radix-4 changes a transcript input, not the schedule or sampler that the standalone KAT pins.".to_string(),
            "A real radix-4 layer-0 frontier node is corrupted and must reject on both host and SBF.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct SumcheckProbeVariant {
    pub name: &'static str,
    pub rounds: u8,
    pub coefficients: u8,
    pub claims: u8,
    pub selector_terms: u16,
    pub selector_exceptions: u8,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub incremental_cu_over_baseline: i64,
}

#[derive(Serialize)]
pub struct SumcheckProbeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub repetitions: usize,
    pub baseline_cu_mean: f64,
    pub synthetic_allowance_cu: i64,
    pub variants: Vec<SumcheckProbeVariant>,
    pub central_replaces_allowance_cu: i64,
    pub allowance_error_cu: i64,
    pub notes: Vec<String>,
}

/// Measure the fused statement-sumcheck verifier work that the synthetic
/// 30,000-CU allowance stands in for. Risk retirement: every registered
/// gate statistic silently assumes the allowance.
pub fn run_stage2_sumcheck_probe() -> Result<SumcheckProbeSummary> {
    const REPETITIONS: usize = 5;
    const ALLOWANCE: i64 = 30_000;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;

    let probe_instruction = |rounds: u8,
                             coefficients: u8,
                             claims: u8,
                             selector_terms: u16,
                             selector_exceptions: u8|
     -> Result<Instruction> {
        Ok(Instruction {
            program_id: aspis_verifier::id(),
            accounts: vec![],
            data: to_vec(&AspisInstruction::StatementSumcheckProbe {
                rounds,
                coefficients,
                claims,
                selector_terms,
                selector_exceptions,
            })?,
        })
    };

    let baseline =
        simulate_pure_instruction(&rpc, &payer, probe_instruction(0, 1, 0, 0, 0)?, REPETITIONS)?;
    let baseline_mean = baseline.iter().sum::<u64>() as f64 / baseline.len() as f64;

    // (rounds, coefficients, claims, selector_terms, selector_exceptions):
    // optimistic assumes degree-6 messages and lean selectors; central is
    // the nu=10 / degree-7 / three-claim / b=4-5 block-periodic reading;
    // pessimistic is the T3 nu<=14 budget with heavier selectors.
    let shapes: [(&'static str, u8, u8, u8, u16, u8); 5] = [
        ("optimistic", 10, 7, 3, 16, 3),
        ("central", 10, 8, 3, 24, 5),
        ("pessimistic", 14, 8, 4, 48, 8),
        // Same claims/selectors, isolating only the polynomial-width cost.
        // The probe carries the full polynomial here; the production wire
        // reconstructs one coefficient from the boundary identity.  Comparing
        // 28 against 11 therefore preserves the exact +17 coefficient delta
        // of a degree-27 two-round-fused statement versus degree 10.
        ("payment_degree10", 10, 11, 2, 24, 5),
        ("two_round_fused_degree27", 10, 28, 2, 24, 5),
    ];
    let mut variants = Vec::new();
    for (name, rounds, coefficients, claims, selector_terms, selector_exceptions) in shapes {
        let samples = simulate_pure_instruction(
            &rpc,
            &payer,
            probe_instruction(
                rounds,
                coefficients,
                claims,
                selector_terms,
                selector_exceptions,
            )?,
            REPETITIONS,
        )?;
        let mean = samples.iter().sum::<u64>() as f64 / samples.len() as f64;
        variants.push(SumcheckProbeVariant {
            name,
            rounds,
            coefficients,
            claims,
            selector_terms,
            selector_exceptions,
            simulation_cu: samples,
            simulation_cu_mean: mean,
            incremental_cu_over_baseline: (mean - baseline_mean).round() as i64,
        });
    }
    let central = variants[1].incremental_cu_over_baseline;
    Ok(SumcheckProbeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-sumcheck-probe".to_string(),
        validator_version: validator_version(),
        repetitions: REPETITIONS,
        baseline_cu_mean: baseline_mean,
        synthetic_allowance_cu: ALLOWANCE,
        variants,
        central_replaces_allowance_cu: central,
        allowance_error_cu: central - ALLOWANCE,
        notes: vec![
            "Prices mu-batched zero claims, transcript-absorbed round messages with boundary checks and Horner terminal evaluation, and block-periodic selector evaluation with enumerated exception rows.".to_string(),
            "eq(r,z) and the composition C(v_1..v_k) are deliberately excluded: the constraint-composition probe already prices them; adding them here would double-count the seam.".to_string(),
            "The central incremental value REPLACES the synthetic 30,000-CU statement-sumcheck allowance in every projection from this artifact onward.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct PaymentStatementV4Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub instruction_wire_ordinal: u8,
    pub constraint_count: usize,
    pub randomized_claim_count: usize,
    pub sumcheck_rounds: usize,
    pub sumcheck_degree: usize,
    pub fixture_bytes: usize,
    pub upload_chunks: usize,
    pub simulation_cu: Vec<u64>,
    pub simulation_cu_mean: f64,
    pub first_simulation_remaining_cu_markers: Vec<u64>,
    pub first_simulation_phase_cu: Vec<u64>,
    pub first_simulation_pre_terminal_phase_cu: Vec<u64>,
    pub first_simulation_terminal_phase_cu: Vec<u64>,
    pub first_simulation_unmarked_transaction_cu: u64,
    pub corruption_rejected: bool,
    pub notes: Vec<String>,
}

fn payment_statement_fixture() -> Result<Vec<u8>> {
    use aspis_core::circle_prefix::RATE16_PAYMENT_CANDIDATE_SHAPE;
    use aspis_core::field::M31;
    use aspis_core::proof::M31_CIRCLE_BASIS_DISCRIMINATOR;
    use aspis_core::statement_sumcheck::encode_wire;
    use aspis_core::transcript::{label, Transcript};
    use aspis_prover::circle_candidate::{
        c1_layer0_root_for_codeword_len, c2_layer0_root_for_codeword_len,
        candidate_payment_statement_evaluations, candidate_prefix_header_for_shape, CircleEncoder,
    };
    use aspis_prover::statement_zerocheck::prove_spend_payment_zerocheck;
    use aspis_statement::{
        build_payment_helpers_v4, build_spend_trace_v4, derive_nullifier, derive_owner_key,
        merkle_root, note_commitment, output_commitment, Digest, MerklePath, SpendPublic,
        SpendWitness,
    };

    let digest =
        |seed: u32| -> Digest { core::array::from_fn(|index| M31(seed + index as u32 * 17)) };
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let value = 1_000_000;
    let value_out = 999_999;
    let owner_key = derive_owner_key(&nullifier_key);
    let note = note_commitment(&owner_key, value, asset_id, &input_salt);
    let merkle_path = MerklePath {
        siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
        index: 0x5_4321,
    };
    let public = SpendPublic {
        anchor: merkle_root(note, &merkle_path)
            .map_err(|error| anyhow!("fixture Merkle root: {error:?}"))?,
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output_commitment(&output_owner_key, value_out, asset_id, &output_salt),
        asset_id,
        fee: 1,
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
    let trace = build_spend_trace_v4(&public, &witness)
        .map_err(|error| anyhow!("build payment trace: {error:?}"))?;

    let header = candidate_prefix_header_for_shape(RATE16_PAYMENT_CANDIDATE_SHAPE);
    let mut header_bytes = [0u8; aspis_core::proof::HEADER_LEN];
    header.write(&mut header_bytes);
    let mut public_bytes = Vec::with_capacity(104);
    for value in public
        .anchor
        .iter()
        .chain(&public.nullifier)
        .chain(&public.output_commitment)
        .chain(core::iter::once(&public.asset_id))
    {
        public_bytes.extend_from_slice(&value.to_le_bytes());
    }
    public_bytes.extend_from_slice(&public.fee.to_le_bytes());
    let statement_digest = HOST_HASH(&[b"aspis:payment-statement-v4", &public_bytes]);

    let domain_log_size = 14;
    let codeword_len = 1usize << domain_log_size;
    let encoder = CircleEncoder::new_for_domain_log(domain_log_size);
    let encoded_c1 = encoder.encode_c1_columns(&trace.c1)?;
    let c1_root = c1_layer0_root_for_codeword_len(&encoded_c1, codeword_len, HOST_HASH)?;

    let mut transcript = Transcript::new(HOST_HASH);
    transcript.absorb(label::PROFILE, &header_bytes);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, &statement_digest);
    let mut root_record = [0u8; 33];
    root_record[1..].copy_from_slice(&c1_root);
    transcript.absorb(label::M31_CIRCLE_ROUND_ROOT, &root_record);
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| anyhow!("fixture lambda sampler exhausted"))?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| anyhow!("fixture chi sampler exhausted"))?;
    let helpers = build_payment_helpers_v4(&trace, lambda, chi)
        .map_err(|error| anyhow!("build payment helpers: {error:?}"))?;
    let c2_messages = [helpers.h1.clone(), helpers.h2.clone()];
    let encoded_c2 = encoder.encode_c2_columns(&c2_messages)?;
    let c2_root = c2_layer0_root_for_codeword_len(&encoded_c2, codeword_len, HOST_HASH)?;
    transcript.absorb(label::M31_CIRCLE_C2_ROOT, &c2_root);
    let payment =
        prove_spend_payment_zerocheck(&mut transcript, &public, &trace, &helpers, lambda, chi)
            .map_err(|error| anyhow!("prove payment zerocheck: {error:?}"))?;
    let evaluations = candidate_payment_statement_evaluations(
        &trace.c1,
        &c2_messages,
        &payment.sumcheck.challenges,
    )?;

    let mut fixture = Vec::new();
    fixture.extend_from_slice(b"APST");
    fixture.push(1);
    fixture.extend_from_slice(&header_bytes);
    fixture.extend_from_slice(&statement_digest);
    fixture.extend_from_slice(&c1_root);
    fixture.extend_from_slice(&c2_root);
    fixture.extend_from_slice(&public_bytes);
    for message in &payment.sumcheck.messages {
        fixture.extend_from_slice(&encode_wire(message));
    }
    for value in evaluations {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        fixture.extend_from_slice(&bytes);
    }
    Ok(fixture)
}

pub fn run_stage2_payment_statement_v4() -> Result<PaymentStatementV4Summary> {
    const REPETITIONS: usize = 5;
    let root = workspace_root()?;
    let fixture = payment_statement_fixture()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), LAMPORTS_PER_SOL)?;
    let proof_account = Keypair::new();
    let (upload_chunks, _) = upload_proof(&rpc, &payer, &proof_account, &fixture, true)?;
    let instruction = proof_instruction(
        &payer.pubkey(),
        &proof_account.pubkey(),
        &AspisInstruction::MeasurePaymentStatementV4,
    )?;
    let blockhash = rpc.latest_blockhash()?;
    let transaction = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            instruction,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        blockhash,
    );
    let mut simulation_cu = Vec::with_capacity(REPETITIONS);
    let mut remaining_markers = Vec::new();
    for repetition in 0..REPETITIONS {
        let result = rpc.simulate_verbose(&transaction)?;
        ensure!(
            result.err.is_none(),
            "payment statement simulation failed: {:?}",
            result.err
        );
        if repetition == 0 {
            remaining_markers = result
                .logs
                .iter()
                .filter_map(|log| {
                    log.strip_prefix("Program consumption: ")?
                        .split_whitespace()
                        .next()?
                        .parse::<u64>()
                        .ok()
                })
                .collect();
        }
        simulation_cu.push(
            result
                .units
                .context("payment statement simulation omitted CU")?,
        );
    }
    let phase_cu = remaining_markers
        .windows(2)
        .map(|markers| markers[0].saturating_sub(markers[1]))
        .collect::<Vec<_>>();
    ensure!(
        phase_cu.len() == 12,
        "unexpected payment phase marker count: {}",
        phase_cu.len()
    );
    let pre_terminal_phase_cu = phase_cu[..5].to_vec();
    let terminal_phase_cu = phase_cu[5..].to_vec();
    let marked_cu = phase_cu.iter().sum::<u64>();
    let unmarked_transaction_cu = simulation_cu[0].saturating_sub(marked_cu);

    let mut corrupted = fixture.clone();
    let message_start = 4 + 1 + aspis_core::proof::HEADER_LEN + 32 + 32 + 32 + 104;
    corrupted[message_start] ^= 1;
    let corrupt_account = Keypair::new();
    upload_proof(&rpc, &payer, &corrupt_account, &corrupted, true)?;
    let corrupt_instruction = proof_instruction(
        &payer.pubkey(),
        &corrupt_account.pubkey(),
        &AspisInstruction::MeasurePaymentStatementV4,
    )?;
    let corrupt_tx = Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            corrupt_instruction,
        ],
        Some(&payer.pubkey()),
        &[&payer],
        rpc.latest_blockhash()?,
    );
    let (_, corrupt_error) = rpc.simulate(&corrupt_tx)?;
    let corruption_rejected = corrupt_error.is_some();
    ensure!(
        corruption_rejected,
        "corrupted payment sumcheck unexpectedly accepted"
    );

    let mean = simulation_cu.iter().sum::<u64>() as f64 / simulation_cu.len() as f64;
    Ok(PaymentStatementV4Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-payment-statement-v4".to_string(),
        validator_version: validator_version(),
        instruction_wire_ordinal: 31,
        constraint_count: aspis_statement::CONSTRAINT_COUNT,
        randomized_claim_count: aspis_statement::RANDOMIZED_CLAIM_COUNT,
        sumcheck_rounds: aspis_core::statement_sumcheck::PAYMENT_SUMCHECK_ROUNDS,
        sumcheck_degree: aspis_core::statement_sumcheck::PAYMENT_SUMCHECK_DEGREE,
        fixture_bytes: fixture.len(),
        upload_chunks,
        simulation_cu: simulation_cu.clone(),
        simulation_cu_mean: mean,
        first_simulation_remaining_cu_markers: remaining_markers,
        first_simulation_phase_cu: phase_cu,
        first_simulation_pre_terminal_phase_cu: pre_terminal_phase_cu,
        first_simulation_terminal_phase_cu: terminal_phase_cu,
        first_simulation_unmarked_transaction_cu: unmarked_transaction_cu,
        corruption_rejected,
        notes: vec![
            "Runs the exact 252-constraint terminal, two helper-sum claims, and ten transcript-bound degree-10 sumcheck messages derived from a real depth-20 spend trace.".to_string(),
            "The 102 values are fixture-account inputs in this diagnostic. The integrated PCS must authenticate the identical values before this work can authorize a spend.".to_string(),
            "Pre-terminal phase order: fixture parse/decode; prefix transcript and challenge derivation; ten-round sumcheck verification; point/evaluation absorption plus gamma; opening assembly. Terminal phase order: selector tensor; Poseidon; fixed relations; copy routing/LogUp; range LogUp; packed theta batching; terminal equality wrapper.".to_string(),
            "Unmarked transaction CU includes both ComputeBudget instructions, instruction dispatch before the entry marker, marker logging overhead outside measured windows, and return bookkeeping after the final marker.".to_string(),
        ],
    })
}

#[derive(Serialize)]
pub struct QueryTradeProfileStats {
    pub profile: &'static str,
    pub query_count: u16,
    pub per_seed_cu: Vec<u64>,
    pub mean_cu: f64,
    pub min_cu: u64,
    pub max_cu: u64,
    pub range_cu: u64,
}

#[derive(Serialize)]
pub struct QueryTradeSummary {
    pub generated_at_utc: String,
    pub command: String,
    pub validator_version: String,
    pub seeds: u64,
    pub repetitions_per_seed: usize,
    pub profiles: Vec<QueryTradeProfileStats>,
    pub q36_to_q34_mean_saving_cu: f64,
    pub q36_to_q32_mean_saving_cu: f64,
    pub marginal_cu_per_query_q36_q32: f64,
    pub notes: Vec<String>,
}

/// Multi-seed q36/q34/q32 comparison at fixed g16 shape for the
/// query/grinding trade (production pairings q34/g36, q32/g40 hold
/// 2q + g = 104). Per the pre-registered evidence standard, generation-
/// changing candidates are evaluated on >= 8-seed means.
pub fn run_stage2_query_trade_g16() -> Result<QueryTradeSummary> {
    const REPETITIONS: usize = 5;
    const SEEDS: u64 = 8;
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 40 * LAMPORTS_PER_SOL)?;

    let profiles = [
        &PROFILE_CAPACITY_LR10_Q36_G16,
        &aspis_core::params::PROFILE_CAPACITY_LR10_Q34_G16,
        &aspis_core::params::PROFILE_CAPACITY_LR10_Q32_G16,
    ];
    let mut stats = Vec::new();
    for profile in profiles {
        let mut per_seed = Vec::new();
        for seed in 1..=SEEDS {
            let digest = crate::host_statement_digest(seed);
            let coeffs = seeded_coeffs(profile.log_rows, seed);
            let proof = prove_with_synthetic_second_phase(
                profile,
                &coeffs,
                &digest,
                &ProveOptions {
                    fold_payload: FoldPayload::RawFibers,
                    merkle_mode: MerkleMode::Radix4MinimalSubtree,
                },
                HOST_HASH,
            );
            ensure!(
                aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
                "{} seed {seed} proof failed host verification",
                profile.name
            );
            let proof_account = Keypair::new();
            upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
            let mut reps = Vec::new();
            for _ in 0..REPETITIONS {
                let instruction = AspisInstruction::Verify {
                    statement_digest: digest,
                };
                let blockhash = rpc.latest_blockhash()?;
                let transaction = Transaction::new_signed_with_payer(
                    &[
                        ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                        proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                    ],
                    Some(&payer.pubkey()),
                    &[&payer],
                    blockhash,
                );
                let (units, error) = rpc.simulate(&transaction)?;
                ensure!(
                    error.is_none(),
                    "{} seed {seed} production Verify failed: {error:?}",
                    profile.name
                );
                reps.push(units.context("production Verify did not report units")?);
            }
            ensure!(
                reps.windows(2).all(|pair| pair[0] == pair[1]),
                "{} seed {seed} simulation was not deterministic: {reps:?}",
                profile.name
            );
            per_seed.push(reps[0]);
            eprintln!(
                "stage2-query-trade-g16: {} seed {seed}/{SEEDS} {}",
                profile.name, reps[0]
            );
        }
        let mean = per_seed.iter().sum::<u64>() as f64 / per_seed.len() as f64;
        let min = *per_seed.iter().min().expect("nonempty");
        let max = *per_seed.iter().max().expect("nonempty");
        stats.push(QueryTradeProfileStats {
            profile: profile.name,
            query_count: profile.query_count,
            per_seed_cu: per_seed,
            mean_cu: mean,
            min_cu: min,
            max_cu: max,
            range_cu: max - min,
        });
    }
    let q36_q34 = stats[0].mean_cu - stats[1].mean_cu;
    let q36_q32 = stats[0].mean_cu - stats[2].mean_cu;
    Ok(QueryTradeSummary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-query-trade-g16".to_string(),
        validator_version: validator_version(),
        seeds: SEEDS,
        repetitions_per_seed: REPETITIONS,
        profiles: stats,
        q36_to_q34_mean_saving_cu: q36_q34,
        q36_to_q32_mean_saving_cu: q36_q32,
        marginal_cu_per_query_q36_q32: q36_q32 / 4.0,
        notes: vec![
            "Radix-4 synthetic-C2 g16 proofs, production Verify, 8 fresh draws per query count; means are the comparison statistic per the pre-registered evidence standard.".to_string(),
            "This measures the PCS-side query scaling only. The q-linear statement terms (wide RLC and leaf, ~ (k' RLC + leaf)/36 per query) add to the projected saving arithmetically and are called out in the hunt ledger.".to_string(),
            "Production pairings hold 2q + g = 104: q34/g36 and q32/g40. Each traded query improves the proven Johnson floor by ~1.07 bits net (0.93 proven query-bits out, 2 proven ROM work-bits in).".to_string(),
        ],
    })
}

/// Multi-seed transcript-draw variance study at fixed g16 shape.
///
/// This is the pre-registered decider for whether the strict candidate's
/// 29,056-CU single-draw headroom survives draw-to-draw spread. The
/// criterion string is committed before any multi-seed data exists; the
/// runner only evaluates it.
pub fn run_stage2_variance_g16() -> Result<VarianceG16Summary> {
    const REPETITIONS: usize = 5;
    const SEEDS: u64 = 16;
    const STRICT_CANDIDATE_PROJECTION: i64 = 1_041_944;
    const TEN_PERCENT_SLACK_MAXIMUM: i64 = 1_071_000;
    const CRITERION: &str = "Pre-registered before any multi-seed run: let R = max - min of \
        production Verify CU for the radix-4 minimal-subtree variant over 16 fresh transcript \
        draws (seed s in 1..=16; statement digest seed s, coefficient seed s) at fixed shape \
        capacity_lr10_q36_g16 with RawFibers and synthetic C2. The strict candidate stays green \
        only if 1,041,944 + R <= 1,071,000. Rationale: the single measured g32 radix-4 draw \
        (678,407 CU) may sit anywhere in its own draw distribution, including at its minimum, \
        so the full observed fixed-shape range bounds a worst-case redraw under the stated \
        g16-to-g32 spread-transfer assumption (the query-index and frontier-collision mechanism \
        is identical; grinding bits enter only as a header byte and a threshold). mean+2*sigma \
        and the binary-mode spread are reported as secondary diagnostics and are not binding. \
        On failure, projection_status downgrades to variance_conditional before any \
        integration nonce is ground.";

    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 40 * LAMPORTS_PER_SOL)?;

    let profile = &PROFILE_CAPACITY_LR10_Q36_G16;
    let mut samples = Vec::new();
    let mut binary_cu = Vec::new();
    let mut radix4_cu = Vec::new();
    for seed in 1..=SEEDS {
        let digest = crate::host_statement_digest(seed);
        let coeffs = seeded_coeffs(profile.log_rows, seed);
        let mut per_mode = Vec::new();
        for mode in [MerkleMode::MinimalSubtree, MerkleMode::Radix4MinimalSubtree] {
            let proof = prove_with_synthetic_second_phase(
                profile,
                &coeffs,
                &digest,
                &ProveOptions {
                    fold_payload: FoldPayload::RawFibers,
                    merkle_mode: mode,
                },
                HOST_HASH,
            );
            ensure!(
                aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
                "seed {seed} {mode:?} proof failed host verification"
            );
            let proof_account = Keypair::new();
            upload_proof(&rpc, &payer, &proof_account, &proof, true)?;
            let mut reps = Vec::new();
            for _ in 0..REPETITIONS {
                let instruction = AspisInstruction::Verify {
                    statement_digest: digest,
                };
                let blockhash = rpc.latest_blockhash()?;
                let transaction = Transaction::new_signed_with_payer(
                    &[
                        ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                        proof_instruction(&payer.pubkey(), &proof_account.pubkey(), &instruction)?,
                    ],
                    Some(&payer.pubkey()),
                    &[&payer],
                    blockhash,
                );
                let (units, error) = rpc.simulate(&transaction)?;
                ensure!(
                    error.is_none(),
                    "seed {seed} {mode:?} production Verify failed: {error:?}"
                );
                reps.push(units.context("production Verify did not report units")?);
            }
            ensure!(
                reps.windows(2).all(|pair| pair[0] == pair[1]),
                "seed {seed} {mode:?} simulation was not deterministic: {reps:?}"
            );
            per_mode.push((proof.len(), reps[0]));
        }
        binary_cu.push(per_mode[0].1);
        radix4_cu.push(per_mode[1].1);
        samples.push(VarianceSeedSample {
            seed,
            binary_proof_bytes: per_mode[0].0,
            binary_verify_cu: per_mode[0].1,
            radix4_proof_bytes: per_mode[1].0,
            radix4_verify_cu: per_mode[1].1,
            radix4_saving_cu: per_mode[0].1 as i64 - per_mode[1].1 as i64,
        });
        eprintln!(
            "stage2-variance-g16: seed {seed}/{SEEDS} binary {} radix4 {}",
            per_mode[0].1, per_mode[1].1
        );
    }

    let binary_stats = variance_stats("binary_minimal_subtree", binary_cu);
    let radix4_stats = variance_stats("radix4_minimal_subtree", radix4_cu);
    let penalty = radix4_stats.range_cu;
    let adjusted = STRICT_CANDIDATE_PROJECTION + penalty as i64;
    let two_sigma = 2.0 * radix4_stats.population_std_dev_cu;
    let secondary_adjusted = STRICT_CANDIDATE_PROJECTION + two_sigma.round() as i64;
    Ok(VarianceG16Summary {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run --release -p aspis-xtask -- stage2-variance-g16".to_string(),
        validator_version: validator_version(),
        profile: profile.name,
        seeds: SEEDS,
        repetitions_per_seed: REPETITIONS,
        criterion: CRITERION.to_string(),
        samples,
        binary_stats,
        radix4_stats,
        strict_candidate_projection_cu: STRICT_CANDIDATE_PROJECTION,
        ten_percent_slack_maximum_cu: TEN_PERCENT_SLACK_MAXIMUM,
        single_draw_headroom_cu: TEN_PERCENT_SLACK_MAXIMUM - STRICT_CANDIDATE_PROJECTION,
        criterion_penalty_range_cu: penalty,
        criterion_adjusted_projection_cu: adjusted,
        criterion_passes: adjusted <= TEN_PERCENT_SLACK_MAXIMUM,
        secondary_two_sigma_penalty_cu: two_sigma,
        secondary_adjusted_projection_cu: secondary_adjusted,
        notes: vec![
            "Each row is a real claim-free synthetic-C2 g16 proof; g16 grinding makes 16 fresh draws affordable where 16 fresh 32-bit nonce searches are not.".to_string(),
            "Spread mechanism: the statement digest and coefficients move every absorbed root, so challenges, grinding nonce, query positions, unique-fiber counts, and minimal-subtree frontiers are fresh per seed; the verifier code path is fixed.".to_string(),
            "All five repetitions per seed are asserted identical; per-seed CU is a deterministic function of the draw, so the across-seed spread is exactly the transcript-draw variance.".to_string(),
            "The g16-to-g32 spread transfer is an assumption stated inside the criterion, not a measurement; the integrated g32 payment proof remains the final word.".to_string(),
        ],
    })
}

pub fn run_layout_sweep() -> Result<LayoutSweep> {
    let root = workspace_root()?;
    let so = build_sbf(&root)?;
    let validator = start_validator(&root, &so)?;
    let rpc = Rpc {
        url: validator.rpc_url.clone(),
        http: reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(30))
            .build()?,
    };
    let payer = Keypair::new();
    rpc.airdrop_and_wait(&payer.pubkey(), 10 * LAMPORTS_PER_SOL)?;

    let probe_account = Keypair::new();
    create_program_account(&rpc, &payer, &probe_account, PROOF_ACCOUNT_HEADER_LEN)?;

    let sweep: [(u8, u16, u16); 6] = [
        (12, 16, 32),
        (11, 32, 32),
        (10, 64, 32),
        (9, 128, 32),
        (8, 256, 32),
        (6, 400, 32),
    ];
    let mut points = Vec::new();
    for (log_rows, columns, query_count) in sweep {
        let leaf_bytes = columns.saturating_mul(4);
        let instruction = AspisInstruction::LayoutProbe {
            log_rows,
            columns,
            query_count,
            leaf_bytes,
        };
        let ix = proof_instruction(&payer.pubkey(), &probe_account.pubkey(), &instruction)?;
        let blockhash = rpc.latest_blockhash()?;
        let tx = Transaction::new_signed_with_payer(
            &[
                ComputeBudgetInstruction::set_compute_unit_limit(VERIFY_CU_LIMIT),
                ix,
            ],
            Some(&payer.pubkey()),
            &[&payer],
            blockhash,
        );
        let sim = rpc.simulate_verbose(&tx)?;
        points.push(LayoutPoint {
            log_rows,
            columns,
            query_count,
            leaf_bytes,
            simulation_units: sim.units,
            simulation_error: sim.err,
            markers: parse_cu_markers(&sim.logs, "aspis-layout:"),
        });
    }

    Ok(LayoutSweep {
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command: "cargo run -p aspis-xtask -- stage0-layout-sweep".to_string(),
        validator_version: validator_version(),
        points,
        notes: vec![
            "Synthetic Stage 2 layout probe: SHA-256 leaf/path hashing plus QM31 RLC recombination over k columns.".to_string(),
            "This does not prove statement correctness; it pulls design item 13.8 forward so lr14 is not treated as a frozen target.".to_string(),
        ],
    })
}

fn run_onchain_variant(
    rpc: &Rpc,
    payer: &Keypair,
    profile: &'static Profile,
    payload: FoldPayload,
    mode: MerkleMode,
) -> Result<OnchainVariant> {
    run_onchain_variant_with_proof(rpc, payer, profile, payload, mode, None)
}

fn run_onchain_variant_with_proof(
    rpc: &Rpc,
    payer: &Keypair,
    profile: &'static Profile,
    payload: FoldPayload,
    mode: MerkleMode,
    proof_override: Option<Vec<u8>>,
) -> Result<OnchainVariant> {
    let payload_name = match payload {
        FoldPayload::RawFibers => "raw_fibers",
        FoldPayload::ProofCarriedRoundLocal => "proof_carried_round_local",
    };
    let mode_name = match mode {
        MerkleMode::SinglePaths => "single_paths",
        MerkleMode::MinimalSubtree => "minimal_subtree",
        MerkleMode::Radix4MinimalSubtree => "radix4_minimal_subtree",
    };
    eprintln!(
        "stage0-onchain: {} / {payload_name} / {mode_name}",
        profile.name
    );

    let coeffs = seeded_coeffs(profile.log_rows, 1);
    let digest = crate::host_statement_digest(0);
    let options = ProveOptions {
        fold_payload: payload,
        merkle_mode: mode,
    };
    let proof =
        proof_override.unwrap_or_else(|| prove(profile, &coeffs, &digest, &options, HOST_HASH));
    anyhow::ensure!(
        aspis_core::verify(&proof, &digest, HOST_HASH).is_ok(),
        "proof override failed current host verification"
    );

    let proof_account = Keypair::new();
    let (chunks, upload_cu) = upload_proof(rpc, payer, &proof_account, &proof, true)?;

    let mut verify_cu = Vec::new();
    let mut verify_error = None;
    for _ in 0..VERIFY_REPETITIONS {
        let blockhash = rpc.latest_blockhash()?;
        let tx = verify_tx(payer, &proof_account.pubkey(), digest, blockhash, false)?;
        let (units, err) = rpc.simulate(&tx)?;
        if let Some(err) = err {
            if let Some(units) = units {
                verify_cu.push(units);
            }
            verify_error = Some(err);
            break;
        }
        verify_cu.push(units.ok_or_else(|| anyhow!("no unitsConsumed"))?);
    }

    if verify_error.is_some() {
        let mean = if verify_cu.is_empty() {
            0.0
        } else {
            verify_cu.iter().sum::<u64>() as f64 / verify_cu.len() as f64
        };
        return Ok(OnchainVariant {
            profile: profile.name,
            soundness_label: profile.soundness_label,
            fold_payload: payload_name,
            merkle_mode: mode_name,
            status: "verify_failed",
            verify_error,
            proof_bytes: proof.len(),
            upload_chunks: chunks,
            upload_cu_total: upload_cu,
            verify_cu,
            verify_cu_mean: mean,
            verify_repetitions_requested: VERIFY_REPETITIONS,
            corruption_rejected_onchain: Vec::new(),
        });
    }

    // On-chain corruption suite: re-upload each corrupted proof, expect the
    // verify simulation to error.
    let mut corruption_rejected = Vec::new();
    let host_results = crate::host::corruption_suite(profile, &proof, &digest);
    for case in &host_results {
        let mut corrupted = proof.to_vec();
        match case.name {
            "trailing_byte" => corrupted.push(0),
            "truncation" => {
                corrupted.truncate(corrupted.len() - 1);
            }
            "statement_digest_mismatch" => {}
            _ => corrupted[case.byte_offset] ^= 0x01,
        }
        let corrupt_account = Keypair::new();
        upload_proof(rpc, payer, &corrupt_account, &corrupted, true)?;
        let check_digest = if case.name == "statement_digest_mismatch" {
            crate::host_statement_digest(0xDEAD_BEEF)
        } else {
            digest
        };
        let blockhash = rpc.latest_blockhash()?;
        let tx = verify_tx(
            payer,
            &corrupt_account.pubkey(),
            check_digest,
            blockhash,
            false,
        )?;
        let (_, err) = rpc.simulate(&tx)?;
        corruption_rejected.push((case.name.to_string(), err.is_some()));
    }

    let mean = verify_cu.iter().sum::<u64>() as f64 / verify_cu.len() as f64;
    Ok(OnchainVariant {
        profile: profile.name,
        soundness_label: profile.soundness_label,
        fold_payload: payload_name,
        merkle_mode: mode_name,
        status: "accepted",
        verify_error: None,
        proof_bytes: proof.len(),
        upload_chunks: chunks,
        upload_cu_total: upload_cu,
        verify_cu,
        verify_cu_mean: mean,
        verify_repetitions_requested: VERIFY_REPETITIONS,
        corruption_rejected_onchain: corruption_rejected,
    })
}
