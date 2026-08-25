//! Aspis SpendV0 statement layer, built evaluator-first.
//!
//! This crate deliberately contains no proof system. It defines the exact
//! M31-native hash, spend relations, economic failure modes, and isolated
//! constraint-composition kernel that Stage 2 must make correct before any
//! statement proof is wired into the PCS.

#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

#[cfg(not(target_os = "solana"))]
pub mod atomic_state_only_registry;
pub mod atomic_state_only_terminal;
#[cfg(not(target_os = "solana"))]
pub mod atomic_state_only_trace;
pub mod atomic_statement;
pub mod constraints_v4;
pub mod direct_range_hiding_v4;
pub mod hiding_v4;
pub mod logup;
#[cfg(any(not(target_os = "solana"), feature = "pool-v1-kernel"))]
pub mod pool_v1;
pub mod poseidon2;
pub mod spend;
#[cfg(not(target_os = "solana"))]
pub mod state_only_constraints;
pub mod state_only_poseidon;
#[cfg(not(target_os = "solana"))]
pub mod state_only_semantic;
pub mod state_only_spend;
pub mod state_only_terminal;
#[cfg(not(target_os = "solana"))]
pub mod state_only_trace;
pub mod state_only_verify;
pub mod trace_v4;
pub mod wide_v4;

pub use atomic_statement::{
    atomic_append_chain_anchor, atomic_deployment_domain, atomic_payment_statement_digest_v4,
    decode_asset_id_canonical, decode_digest_canonical, encode_atomic_payment_statement_v4,
    encode_digest_canonical, insertion_root, verify_output_insertion, AtomicPaymentStatementV4,
    AtomicStatementError, ATOMIC_APPEND_CHAIN_DOMAIN, ATOMIC_DEPLOYMENT_DOMAIN_SEPARATOR,
    ATOMIC_PAYMENT_EMPTY_LEAF, ATOMIC_PAYMENT_STATEMENT_DOMAIN,
    ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES, ATOMIC_PAYMENT_STATEMENT_V4_KAT_EXPECTED,
    ATOMIC_PAYMENT_STATEMENT_VERSION, ATOMIC_PAYMENT_TREE_DEPTH,
};
pub use constraints_v4::{
    build_payment_helpers_v4, constraint_registry, direct_range_hiding_masked_terminal_value,
    direct_range_hiding_payment_terminal_value,
    direct_range_hiding_payment_terminal_value_with_trace, evaluate_constraint_point,
    evaluate_constraint_point_with_trace, evaluate_direct_range_hiding_constraint_point,
    evaluate_direct_range_hiding_constraint_point_with_trace, helper_sums, multilinear_evaluate,
    multilinear_evaluate_qm31, payment_terminal_value, payment_terminal_value_with_trace,
    verify_payment_helpers_v4, xor11_point, ConstraintBuildError, ConstraintContextV4,
    ConstraintDescriptor, ConstraintId, ConstraintKind, DirectRangeHidingPointOpeningsV4,
    PaymentHelpersV4, PointOpeningsV4, BASE_FIELD_CONSTRAINT_COUNT, CONSTRAINT_COUNT,
    COPY_ROUTING_LAYOUT_FINGERPRINT, DIRECT_RANGE_CONSTRAINT_SOURCE_COUNT,
    DIRECT_RANGE_GLOBAL_HELPER_SUM_CLAIMS, DIRECT_RANGE_PACKED_LANE_COUNT,
    DIRECT_RANGE_RANDOMIZED_CLAIM_COUNT, DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT,
    DIRECT_RANGE_SOURCE_RESIDUAL_COUNT, DIRECT_RANGE_THETA_COLLISION_DEGREE,
    GLOBAL_HELPER_SUM_CLAIMS, PACKED_BASE_CONSTRAINT_COUNT, PINNED_COPY_ROUTING_LAYOUT_FINGERPRINT,
    RANDOMIZED_CLAIM_COUNT, RANDOMIZED_CONSTRAINT_COUNT,
};
#[cfg(not(target_os = "solana"))]
pub use constraints_v4::{
    compose_constraint_row, constraint_composition_table, direct_range_hiding_composition_table,
    direct_range_hiding_trace_openings_at_point, evaluate_constraint_row, trace_openings_at_point,
};
pub use direct_range_hiding_v4::{
    apply_copy_helper_padding_v4, apply_direct_range_c1_masks_v4, apply_direct_range_witness_v4,
    build_direct_range_hiding_helpers_v4, direct_range_c1_mask_cells_v4,
    direct_range_c1_mask_layout_fingerprint, direct_range_copy_links_v4,
    direct_range_row_residuals_v4, verify_direct_range_c1_mask_sums_v4,
    verify_direct_range_witness_v4, verify_padded_copy_helper_v4, DirectRangeHidingError,
    DirectRangeHidingHelpersV4, COPY_HELPER_MASK_VARIABLES, COPY_HELPER_PADDING_ROW_COUNT,
    COPY_HELPER_PADDING_ROW_START, DIRECT_RANGE_BITS_PER_LIMB, DIRECT_RANGE_BITS_PER_ROW,
    DIRECT_RANGE_BIT_ROW_COUNT, DIRECT_RANGE_BIT_ROW_START, DIRECT_RANGE_C1_COLUMN_COUNT,
    DIRECT_RANGE_C1_MASK_CELL_COUNT, DIRECT_RANGE_COPY_LINK_COUNT, DIRECT_RANGE_LIMBS_PER_ROW,
    DIRECT_RANGE_LIMB_COUNT, DIRECT_RANGE_RECONSTRUCTION_COLUMN_START,
    DIRECT_RANGE_TOTAL_COPY_LINK_COUNT, PAYMENT_MASK_ORACLE_VALUES,
    PINNED_DIRECT_RANGE_C1_MASK_LAYOUT_FINGERPRINT,
};
pub use hiding_v4::{
    apply_expanded_hiding_padding_v4, apply_hiding_padding_v4, expanded_hiding_padding_cells_v4,
    expanded_hiding_padding_layout_fingerprint, hiding_padding_cells_v4, HidingPaddingError,
    EXPANDED_HIDING_PADDING_CELL_COUNT, HIDING_PADDING_CELL_COUNT, HIDING_PADDING_COLUMN_COUNT,
    HIDING_PADDING_ROW_COUNT, HIDING_PADDING_ROW_START,
    PINNED_EXPANDED_HIDING_PADDING_LAYOUT_FINGERPRINT,
};
#[cfg(feature = "insecure-test-logup-compression")]
pub use logup::compress_tagged_tuple_insecure_lambda_zero;
pub use logup::{
    build_10bit_range_logup_rows, build_copy_logup_helper, build_logup_helper,
    build_range_logup_helper, compress_tagged_tuple, copy_logup_residual,
    forge_post_chi_multiplicities, logup_compression_kat, range_logup_residual,
    verify_copy_logup_constraints, verify_logup_constraints, verify_range_logup_constraints,
    CopyLogUpRow, LogUpError, LogUpMainRow, LogUpSide, RangeLogUpRow,
    LOGUP_COMPRESSION_KAT_EXPECTED, RANGE_TABLE_SIZE,
};
pub use poseidon2::{
    hash_merkle_node_sponge, hash_note_commitment, hash_nullifier, hash_owner_key,
    merkle_node_compress_v3, permute, permute_optimized_with_trace, Digest, Poseidon2RoundKind,
    Poseidon2RoundTransition, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_KAT,
    MERKLE_NODE_COMPRESSION_V3_TWEAK, MERKLE_NODE_DOMAIN_V2, POSEIDON2_ROUNDS, POSEIDON2_WIDTH,
    RATE,
};
pub use spend::{
    decompose_10bit_limbs, derive_nullifier, derive_owner_key, evaluate_spend,
    evaluate_spend_with_range_lookup, merkle_root, note_commitment, output_commitment,
    verify_10bit_range_lookup, EvaluationContext, MerklePath, RangeLookupWitness, SpendError,
    SpendPublic, SpendWitness, RANGE_LIMBS_PER_VALUE, RANGE_LIMB_BITS, RANGE_LIMB_LIMIT,
    VALUE_LIMIT,
};
#[cfg(not(target_os = "solana"))]
pub use state_only_constraints::*;
#[cfg(not(target_os = "solana"))]
pub use state_only_poseidon::state_only_poseidon_openings_at_point;
pub use state_only_poseidon::{
    evaluate_state_only_poseidon_oracle, StateOnlyPoseidonOpenings, StateOnlyPoseidonSelectors,
    STATE_ONLY_POSEIDON_ABSORPTION_LOCAL_ROW, STATE_ONLY_POSEIDON_ACTIVE_LOCAL_ROWS,
    STATE_ONLY_POSEIDON_BLOCKS, STATE_ONLY_POSEIDON_BLOCK_ROWS, STATE_ONLY_POSEIDON_COLUMNS,
    STATE_ONLY_POSEIDON_FINAL_LOCAL_ROW, STATE_ONLY_POSEIDON_ORACLE_INDIVIDUAL_DEGREE,
    STATE_ONLY_POSEIDON_PACKED_LANES, STATE_ONLY_POSEIDON_TRACE_ROWS,
    STATE_ONLY_POSEIDON_ZEROCHECK_INDIVIDUAL_DEGREE,
};
#[cfg(not(target_os = "solana"))]
pub use state_only_semantic::{
    build_state_only_copy_helper_v4, evaluate_state_only_semantic_oracle,
    evaluate_state_only_semantic_oracle_prepared, prepare_state_only_semantic_oracle,
    state_only_copy_helper_sum, state_only_semantic_openings_at_point, StateOnlySemanticError,
    StateOnlySemanticOpenings, StateOnlySemanticPrepared, StateOnlySemanticResiduals,
    STATE_ONLY_ABSORPTION_ZERO_LANES, STATE_ONLY_BASE_SOURCE_LANE_COUNT, STATE_ONLY_COPY_LANES,
    STATE_ONLY_COPY_LINK_COUNT, STATE_ONLY_DIRECT_RANGE_LANES, STATE_ONLY_INITIAL_LANES,
    STATE_ONLY_MERKLE_LANES, STATE_ONLY_PACKED_BASE_LANE_COUNT, STATE_ONLY_PUBLIC_ASSET_LANES,
    STATE_ONLY_PUBLIC_DIGEST_LANES, STATE_ONLY_RANDOMIZED_SEMANTIC_LANE_COUNT,
    STATE_ONLY_SEMANTIC_LANE_COUNT, STATE_ONLY_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE,
    STATE_ONLY_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE, STATE_ONLY_STRUCTURAL_SOURCE_ALIAS_COUNT,
    STATE_ONLY_VALUE_LANES,
};
pub use state_only_terminal::{
    state_only_copy_active_rows_v4, state_only_copy_inactive_indicator_v4,
    state_only_copy_inactive_row_masks_v4, state_only_masked_terminal_value_compiled,
    state_only_selected_masked_terminal_value_compiled, StateOnlyTerminalError,
    PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT, STATE_ONLY_COPY_ACTIVE_ROW_COUNT,
    STATE_ONLY_SELECTED_TERMINAL_CLAIMS, STATE_ONLY_SELECTED_TERMINAL_COLUMNS,
    STATE_ONLY_TERMINAL_CLAIMS, STATE_ONLY_TERMINAL_COLUMNS,
    STATE_ONLY_TERMINAL_LAYOUT_FINGERPRINT, STATE_ONLY_TERMINAL_POINTS,
    STATE_ONLY_TERMINAL_RANDOMIZED_LANES,
};
#[cfg(not(target_os = "solana"))]
pub use state_only_trace::{
    binary_successor_point, build_state_only_cell_map_v4, project_state_only_trace_v4,
    state_only_copy_layout_v4, state_only_layout_fingerprint_v4,
    state_only_relation_free_mask_cells_v4, state_only_relation_free_mask_fingerprint_v4,
    state_only_required_old_cells_v4, state_only_witness_aux_layout_v4,
    validate_state_only_projection, xor12_point, StateOnlyCellMap, StateOnlyCopyLayout,
    StateOnlyDegreeBounds, StateOnlyLayoutError, StateOnlyTraceError, StateOnlyTraceFoundation,
    PINNED_STATE_ONLY_LAYOUT_FINGERPRINT, PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT,
    STATE_ONLY_ABSORPTION_ROW_IN_BLOCK, STATE_ONLY_AUX_ROW_COUNT, STATE_ONLY_AUX_ROW_END,
    STATE_ONLY_AUX_ROW_START, STATE_ONLY_C1_COLUMNS, STATE_ONLY_DEGREE_BOUNDS,
    STATE_ONLY_DIRECT_RANGE_BALANCE_OUTPUT_COLUMN, STATE_ONLY_DIRECT_RANGE_BITS,
    STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN, STATE_ONLY_DIRECT_RANGE_LIMB_COUNT,
    STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN, STATE_ONLY_DIRECT_RANGE_ROWS,
    STATE_ONLY_DIRECT_RANGE_ROW_END, STATE_ONLY_DIRECT_RANGE_ROW_START,
    STATE_ONLY_FINAL_ROW_IN_BLOCK, STATE_ONLY_PADDING_ROW_START_IN_BLOCK,
    STATE_ONLY_SURVIVING_COPY_LINK_COUNT, STATE_ONLY_TRANSITIONS_PER_BLOCK,
    STATE_ONLY_TRANSITION_COUNT,
};
pub use state_only_verify::{
    state_only_geometry, verify_atomic_state_only_candidate_unmined_for_diagnostics_v3,
    verify_atomic_state_only_candidate_v3, verify_atomic_state_only_profile21_relation,
    verify_state_only_candidate, verify_state_only_relation, StateOnlyCandidateVerifyError,
    StateOnlyRelationVerifyError, StateOnlyVerifyDiagnosticPhase, StateOnlyVerifyPhase,
    StateOnlyVerifyTrace, VerifiedStateOnlyCandidate,
};
pub use state_only_verify::{
    verify_state_only_atomic_terminal_cost_candidate_unmined_traced,
    verify_state_only_candidate_phase_unmined_for_diagnostics,
    verify_state_only_candidate_unmined_for_diagnostics,
    verify_state_only_candidate_unmined_for_diagnostics_traced,
};
pub use trace_v4::{
    build_spend_trace_v4, copy_layout, is_absorption_row, is_poseidon_active_row,
    is_poseidon_padding_row, merkle_boundary_layout, permutation_block_schedule, poseidon_row_kind,
    validate_spend_trace_v4, visit_copy_links, witness_aux_layout, CopyLayout, CopyLink,
    CopyLinkKind, CopyTuple, HashInvocationKind, MerkleBoundaryBinding, PermutationBlock,
    PoseidonRowKind, SourceEqualityBinding, SpendTraceV4, TraceBuildError, TraceCell,
    TracePublicOutputs, TraceValidationError, TupleLimb, WitnessAuxLayout,
    ABSORPTION_COPY_LINK_COUNT, ABSORPTION_ROW_IN_BLOCK, ACTIVE_ROWS_PER_BLOCK,
    ALLOCATED_PERMUTATION_ROWS, AUX_ABSORPTION_PRODUCER_ROW_START, AUX_WITNESS_ROW_START,
    BALANCE_COPY_LINK_COUNT, BLOCK_ROWS, COPY_LINK_COUNT, DEAD_ROW_START_IN_BLOCK,
    INPUT_VALUE_RANGE_ROW, MULTIPLICITY_COLUMN, OUTPUT_VALUE_RANGE_ROW, PERMUTATION_COUNT,
    POSEIDON_ACTIVE_ROWS, SEMANTIC_INGRESS_COPY_LINK_COUNT, STATE_AND_INTERFACE_COLUMNS,
    STATE_COPY_LINK_COUNT, TRACE_ROWS, VALUE_RECONSTRUCTION_COLUMN,
    VALUE_RECONSTRUCTION_COPY_LINK_COUNT,
};
pub use wide_v4::{
    combine_exact_wide_bytes_prepared, combine_exact_wide_fiber, combine_exact_wide_fiber_baseline,
    combine_exact_wide_fiber_prepared, prepare_exact_wide_weights, ExactWideFiber,
    ExactWideWeights, C1_COLUMNS as WIDE_V4_C1_COLUMNS, C1_FIBER_BYTES as WIDE_V4_C1_FIBER_BYTES,
    C2_COLUMNS as WIDE_V4_C2_COLUMNS, C2_FIBER_BYTES as WIDE_V4_C2_FIBER_BYTES,
    TOTAL_COLUMNS as WIDE_V4_TOTAL_COLUMNS,
};
