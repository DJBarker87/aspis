//! Pure Pool V1 formats and append-only state kernels.
//!
//! This module is deliberately independent of the frozen same-path
//! `AtomicPoolStateV2` program account.  It contains no Solana account access,
//! CPI, deposit, spend, withdrawal, or verifier dispatch.  A later program
//! integration may wrap these byte-exact components in new Pool V1 accounts;
//! it must not reinterpret an existing atomic-v2 account as Pool V1.

pub mod authorization_receipt;
pub mod authorization_receipt_account;
pub mod deposit;
pub mod format;
pub mod historical_anchor;
pub mod incremental_merkle;
pub mod nullifier_marker;
#[cfg(not(target_os = "solana"))]
pub mod pair_constraint_residuals;
pub mod pair_forest_accounts;
#[cfg(not(target_os = "solana"))]
pub mod pair_forest_constraint_residuals;
#[cfg(not(target_os = "solana"))]
pub mod pair_forest_hiding;
#[cfg(not(target_os = "solana"))]
pub mod pair_forest_trace;
pub mod pair_terminal;
#[cfg(not(target_os = "solana"))]
pub mod pair_trace;
#[cfg(not(target_os = "solana"))]
pub mod pair_tree_hiding;
pub mod pair_tree_profile;
#[cfg(not(target_os = "solana"))]
pub mod payment_constraint_residuals;
#[cfg(not(target_os = "solana"))]
pub mod payment_hiding;
pub mod payment_relation;
#[cfg(not(target_os = "solana"))]
pub mod payment_semantic_oracle;
#[cfg(not(target_os = "solana"))]
pub mod payment_semantic_registry;
pub mod payment_semantic_terminal;
#[cfg(not(target_os = "solana"))]
pub mod payment_trace;
pub mod root_history;
pub mod tag73_native_profile;
pub mod verifier_dispatch;
pub mod verifier_registry;

pub use authorization_receipt::{
    decode_pool_v1_authorization_receipt_v1, encode_pool_v1_authorization_receipt_v1,
    validate_pool_v1_authorization_receipt_for_settlement_v1, PoolV1AuthorizationReceiptError,
    PoolV1AuthorizationReceiptV1, POOL_V1_AUTHORIZATION_RECEIPT_BYTES,
    POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_BYTES, POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN,
    POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256, POOL_V1_AUTHORIZATION_RECEIPT_MAGIC,
    POOL_V1_AUTHORIZATION_RECEIPT_PREFIX_BYTES, POOL_V1_AUTHORIZATION_RECEIPT_SEED,
    POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED, POOL_V1_AUTHORIZATION_RECEIPT_VERSION,
};
pub use authorization_receipt_account::{
    authorize_close_pool_v1_authorization_receipt_account_v1,
    decode_pool_v1_authorization_receipt_account_v1,
    finalize_pool_v1_authorization_receipt_account_v1,
    initialize_pool_v1_authorization_receipt_account_v1,
    pool_v1_authorization_receipt_binding_digest_v1,
    pool_v1_authorization_receipt_pda_inputs_for_binding_v1,
    pool_v1_authorization_receipt_request_digest_v1,
    validate_pool_v1_authorization_receipt_account_pda_inputs_v1,
    validate_pool_v1_authorization_receipt_account_request_v1,
    PoolV1AuthorizationReceiptAccountErrorV1, PoolV1AuthorizationReceiptAccountStatusV1,
    PoolV1AuthorizationReceiptAccountV1, PoolV1AuthorizationReceiptCloseAuthorizationV1,
    PoolV1AuthorizationReceiptPdaInputsV1, POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_BYTES,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_DOMAIN,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HASH_SHA256,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HEADER_BYTES,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_MAGIC,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_PENDING,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_VERIFIED,
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_VERSION,
    POOL_V1_AUTHORIZATION_RECEIPT_BINDING_DIGEST_DOMAIN,
    POOL_V1_AUTHORIZATION_RECEIPT_REQUEST_DIGEST_DOMAIN,
};

pub use deposit::{
    decode_deposit_receipt_v1, encode_deposit_receipt_v1, validate_deposit_event_v1,
    validate_deposit_receipt_v1, DepositEventV1, DepositReceiptV1, PoolV1DepositFormatError,
    POOL_V1_DEPOSIT_RECEIPT_BYTES, POOL_V1_DEPOSIT_RECEIPT_MAGIC, POOL_V1_DEPOSIT_RECEIPT_VERSION,
    POOL_V1_DEPOSIT_RETURN_MAX_BYTES, POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES,
};
pub use format::{
    decode_pool_identity_v1, decode_verifier_policy_v1, encode_pool_identity_v1,
    encode_verifier_policy_v1, pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent,
    validate_verifier_policy_v1, PoolIdentityV1, PoolV1FormatError, VerifierPolicyV1,
    POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_FORMAT_BINDING, POOL_V1_FORMAT_VERSION,
    POOL_V1_IDENTITY_BYTES, POOL_V1_NOTE_COMMITMENT_VERSION, POOL_V1_NULLIFIER_FORMAT_VERSION,
    POOL_V1_TREE_DEPTH, POOL_V1_TREE_HASH_VERSION, POOL_V1_VERIFIER_POLICY_BYTES,
    POOL_V1_VERIFIER_POLICY_FLAGS_MASK, POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
    POOL_V1_VERIFIER_POLICY_MAGIC, POOL_V1_VERIFIER_POLICY_VERSION,
};
pub use historical_anchor::{
    decode_historical_anchor_envelope_v1, encode_historical_anchor_envelope_v1,
    validate_historical_anchor_envelope_v1, HistoricalAnchorEnvelopeV1,
    PoolV1HistoricalAnchorFormatError, PoolV1TransitionKind,
    POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES, POOL_V1_HISTORICAL_ANCHOR_MAGIC,
    POOL_V1_HISTORICAL_ANCHOR_VERSION,
};
pub use incremental_merkle::{
    pool_v1_empty_roots, AppendOneV1, AppendTwoV1, IncrementalMerkleTreeV1, PoolV1TreeError,
    ValidatedIncrementalMerkleTreeV1, POOL_V1_LEAF_CAPACITY, POOL_V1_TREE_STATE_ACCOUNT_BYTES,
    POOL_V1_TREE_STATE_MAGIC, POOL_V1_TREE_STATE_VERSION,
};
pub use nullifier_marker::{
    decode_pool_v1_nullifier_marker, encode_pool_v1_nullifier_marker,
    validate_pool_v1_nullifier_marker, PoolV1NullifierMarkerFormatError, PoolV1NullifierMarkerV1,
    POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES, POOL_V1_NULLIFIER_MARKER_MAGIC,
    POOL_V1_NULLIFIER_MARKER_SEED, POOL_V1_NULLIFIER_MARKER_VERSION,
};
#[cfg(not(target_os = "solana"))]
pub use pair_constraint_residuals::{
    evaluate_pool_v1_pair_private_transfer_constraint_residuals_v1,
    evaluate_pool_v1_pair_withdrawal_constraint_residuals_v1, PoolV1PairConstraintResidualErrorV1,
    PoolV1PairConstraintResidualsV1, PoolV1PairResidualClassV1,
    POOL_V1_PAIR_AFFINE_INTRINSIC_DEGREE, POOL_V1_PAIR_APPEND_PATH_RESIDUAL_COUNT,
    POOL_V1_PAIR_BOOLEAN_INTRINSIC_DEGREE, POOL_V1_PAIR_CANDIDATE_FRONTIER_RESIDUAL_COUNT,
    POOL_V1_PAIR_CANDIDATE_ROOT_RESIDUAL_COUNT, POOL_V1_PAIR_COPY_ALIAS_RESIDUAL_COUNT,
    POOL_V1_PAIR_INDEX_SEQUENCE_RESIDUAL_COUNT, POOL_V1_PAIR_MAX_INTRINSIC_DEGREE,
    POOL_V1_PAIR_OCCUPANCY_RESIDUAL_COUNT, POOL_V1_PAIR_PATH_ORDERING_RESIDUAL_COUNT,
    POOL_V1_PAIR_POSEIDON_RESIDUAL_COUNT, POOL_V1_PAIR_POSEIDON_SBOX_DEGREE,
    POOL_V1_PAIR_SELECTED_ORACLE_INDIVIDUAL_DEGREE, POOL_V1_PAIR_TRANSFER_PUBLIC_RESIDUAL_COUNT,
    POOL_V1_PAIR_TRANSFER_SCHEDULE_RESIDUAL_COUNT, POOL_V1_PAIR_TRANSFER_TOTAL_RESIDUAL_COUNT,
    POOL_V1_PAIR_TWO_ROUND_INTRINSIC_DEGREE, POOL_V1_PAIR_VALUE_BOOLEAN_RESIDUAL_COUNT,
    POOL_V1_PAIR_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT, POOL_V1_PAIR_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT,
    POOL_V1_PAIR_WITHDRAWAL_TOTAL_RESIDUAL_COUNT, POOL_V1_PAIR_ZEROCHECK_INDIVIDUAL_DEGREE,
    POOL_V1_PAIR_ZERO_PADDING_RESIDUAL_COUNT,
};
pub use pair_forest_accounts::{
    decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
    decode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_checkpoint_v1,
    encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
    plan_pool_v1_pair_forest_checkpoint_v1, pool_v1_pair_forest_deposit_lane_v1,
    pool_v1_pair_forest_output_lane_v1, PoolV1PairForestAccountErrorV1,
    PoolV1PairForestCheckpointPlanV1, PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1,
    PoolV1PairForestMasterV1, POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING,
    POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    POOL_V1_PAIR_FOREST_CHECKPOINT_MAGIC, POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION,
    POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_COUNT,
    POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES, POOL_V1_PAIR_FOREST_LANE_MAGIC,
    POOL_V1_PAIR_FOREST_LANE_VERSION, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
    POOL_V1_PAIR_FOREST_MASTER_MAGIC, POOL_V1_PAIR_FOREST_MASTER_VERSION,
};
#[cfg(not(target_os = "solana"))]
pub use pair_forest_hiding::{
    build_pool_v1_pair_forest_copy_row_schedule_v1, pool_v1_pair_forest_copy_active_row_masks_v1,
    pool_v1_pair_forest_copy_active_rows_fingerprint_v1, pool_v1_pair_forest_copy_active_rows_v1,
    pool_v1_pair_forest_copy_inactive_row_masks_v1,
    pool_v1_pair_forest_copy_row_schedule_fingerprint_v1,
    pool_v1_pair_forest_membership_hash_block_v1, pool_v1_pair_forest_path_base_row_v1,
    pool_v1_pair_forest_relation_free_mask_cells_v1,
    pool_v1_pair_forest_relation_free_mask_fingerprint_v1,
    PINNED_POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_FINGERPRINT_V1,
    PINNED_POOL_V1_PAIR_FOREST_COPY_ROW_SCHEDULE_FINGERPRINT_V1,
    PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
    POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_V1, POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1,
    POOL_V1_PAIR_FOREST_FIRST_SUPER_ROOT_BLOCK_V1, POOL_V1_PAIR_FOREST_LANES_V1,
    POOL_V1_PAIR_FOREST_POSEIDON_BLOCKS_V1, POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1,
    POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_CELLS_V1, POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1,
};
pub use pair_terminal::{
    decode_pool_v1_pair_afterstate_verifier_request_v1, decode_pool_v1_pair_verified_afterstate_v1,
    decode_pool_v1_pair_verifier_request_v1, decode_pool_v1_pair_verifier_result_v1,
    encode_pool_v1_pair_afterstate_verifier_request_v1, encode_pool_v1_pair_verified_afterstate_v1,
    encode_pool_v1_pair_verifier_request_v1, encode_pool_v1_pair_verifier_result_v1,
    pool_v1_pair_statement_digest_v1, validate_pool_v1_pair_verifier_binding_v1,
    PoolV1PairAfterstateVerifierRequestV1, PoolV1PairVerifiedAfterstateV1,
    PoolV1PairVerifierBindingV1, PoolV1PairVerifierRequestV1, PoolV1PairVerifierResultV1,
    PoolV1PairVerifierTransportErrorV1, POOL_V1_PAIR_AFTERSTATE_VERIFIER_REQUEST_MAGIC,
    POOL_V1_PAIR_STATEMENT_BINDING_DOMAIN, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC, POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES,
    POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES, POOL_V1_PAIR_VERIFIER_REQUEST_MAGIC,
    POOL_V1_PAIR_VERIFIER_RESULT_BYTES, POOL_V1_PAIR_VERIFIER_RESULT_MAGIC,
    POOL_V1_PAIR_VERIFIER_SUCCESS_CODE, POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,
};
#[cfg(not(target_os = "solana"))]
pub use pair_tree_hiding::{
    build_pool_v1_pair_copy_row_schedule_v1, pool_v1_pair_aux_cell_is_relation_used_v1,
    pool_v1_pair_copy_active_row_masks_v1, pool_v1_pair_copy_active_rows_fingerprint_v1,
    pool_v1_pair_copy_active_rows_v1, pool_v1_pair_copy_inactive_row_masks_v1,
    pool_v1_pair_copy_row_schedule_fingerprint_v1, pool_v1_pair_relation_free_mask_cells_v1,
    pool_v1_pair_relation_free_mask_fingerprint_v1, PoolV1PairCopyRowLinkKindV1,
    PoolV1PairCopyRowLinkV1, PoolV1PairHidingLayoutErrorV1,
    PINNED_POOL_V1_PAIR_COPY_ACTIVE_ROWS_FINGERPRINT_V1,
    PINNED_POOL_V1_PAIR_COPY_ROW_SCHEDULE_FINGERPRINT_V1,
    PINNED_POOL_V1_PAIR_RELATION_FREE_MASK_FINGERPRINT_V1, POOL_V1_PAIR_COPY_ACTIVE_ROWS_V1,
    POOL_V1_PAIR_COPY_ROW_LINKS_V1, POOL_V1_PAIR_RELATION_FREE_MASK_CELLS_V1,
    POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1,
};
pub use pair_tree_profile::{
    absorb_pool_v1_pair_public_statement_before_c1_root_v1,
    decode_pool_v1_pair_late_public_statement_v1, decode_pool_v1_pair_live_snapshot_v1,
    encode_pool_v1_pair_late_public_statement_v1, encode_pool_v1_pair_live_snapshot_v1,
    pool_v1_pair_path_base_row_v1, pool_v1_pair_poseidon_block_role_v1,
    PoolV1PairHistoricalMembershipAnchorV1, PoolV1PairLatePublicStatementErrorV1,
    PoolV1PairLatePublicStatementV1, PoolV1PairLeafErrorV1, PoolV1PairLeafWitnessV1,
    PoolV1PairLiveSnapshotErrorV1, PoolV1PairLiveSnapshotV1, PoolV1PairPoseidonBlockRoleV1,
    PoolV1PairTranscriptStepV1, POOL_V1_PAIR_ALLOCATED_BLOCKS, POOL_V1_PAIR_ALLOCATED_ROWS,
    POOL_V1_PAIR_CAPACITY, POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
    POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN, POOL_V1_PAIR_LATE_APPEND_POSEIDON_BLOCKS,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES, POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT, POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION, POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
    POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC, POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION,
    POOL_V1_PAIR_MAX_DEPLOYED_DEGREE, POOL_V1_PAIR_NEW_RESIDUAL_MAX_INTRINSIC_DEGREE,
    POOL_V1_PAIR_NOTE_DEPTH, POOL_V1_PAIR_NOTE_SLOT_CAPACITY, POOL_V1_PAIR_OCCUPANCY_BIT_COLUMN,
    POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_END, POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_START,
    POOL_V1_PAIR_OCCUPANCY_INVERSE_COLUMN, POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
    POOL_V1_PAIR_PATH_AUX_BLOCKS, POOL_V1_PAIR_PATH_AUX_ROW_END, POOL_V1_PAIR_PATH_AUX_ROW_START,
    POOL_V1_PAIR_PATH_LOCAL_ROW_OFFSET, POOL_V1_PAIR_POSEIDON_BLOCKS,
    POOL_V1_PAIR_POSEIDON_INTRINSIC_DEGREE, POOL_V1_PAIR_POSEIDON_ROW_END,
    POOL_V1_PAIR_PRIVATE_DIRECTIONS, POOL_V1_PAIR_PUBLIC_STATEMENT_TRANSCRIPT_DOMAIN,
    POOL_V1_PAIR_SEMANTIC_ROW_END, POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS,
    POOL_V1_PAIR_STAGED_TRANSCRIPT_PREFIX_V1, POOL_V1_PAIR_TRACE_BLOCK_ROWS,
    POOL_V1_PAIR_TRACE_COLUMNS, POOL_V1_PAIR_TRACE_ROWS, POOL_V1_PAIR_TREE_DEPTH,
    POOL_V1_PAIR_TREE_FORMAT_BINDING, POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
    POOL_V1_PAIR_UNALLOCATED_SEMANTIC_ROWS, POOL_V1_PAIR_VALUE_AUX_ROW_START,
};
#[cfg(not(target_os = "solana"))]
pub use payment_constraint_residuals::{
    evaluate_pool_v1_private_transfer_constraint_residuals_v1,
    evaluate_pool_v1_withdrawal_constraint_residuals_v1, PoolV1PaymentConstraintResidualErrorV1,
    PoolV1PaymentConstraintResidualsV1, PoolV1PaymentResidualClassV1,
    POOL_V1_PAYMENT_AFFINE_INTRINSIC_DEGREE, POOL_V1_PAYMENT_BOOLEAN_INTRINSIC_DEGREE,
    POOL_V1_PAYMENT_MAX_INTRINSIC_DEGREE, POOL_V1_PAYMENT_PATH_ORDERING_INTRINSIC_DEGREE,
    POOL_V1_PAYMENT_PATH_ORDERING_RESIDUAL_COUNT, POOL_V1_PAYMENT_POSEIDON_RESIDUAL_COUNT,
    POOL_V1_PAYMENT_POSEIDON_SBOX_DEGREE, POOL_V1_PAYMENT_SELECTED_ORACLE_INDIVIDUAL_DEGREE,
    POOL_V1_PAYMENT_TWO_ROUND_INTRINSIC_DEGREE, POOL_V1_PAYMENT_VALUE_BOOLEAN_RESIDUAL_COUNT,
    POOL_V1_PAYMENT_ZEROCHECK_INDIVIDUAL_DEGREE,
};
#[cfg(not(target_os = "solana"))]
pub use payment_hiding::{
    pool_v1_payment_relation_free_mask_cells_v1, pool_v1_payment_relation_free_mask_fingerprint_v1,
    POOL_V1_PAYMENT_RELATION_FREE_PADDING_LOCAL_ROW_START_V1,
};
pub use payment_relation::{
    decode_pool_v1_private_transfer_public_v1, decode_pool_v1_withdrawal_public_v1,
    encode_pool_v1_private_transfer_public_v1, encode_pool_v1_withdrawal_public_v1,
    evaluate_pool_v1_private_transfer_v1, evaluate_pool_v1_withdrawal_v1,
    pool_v1_membership_root_v1, validate_pool_v1_private_transfer_envelope_binding_v1,
    validate_pool_v1_private_transfer_public_v1, validate_pool_v1_withdrawal_envelope_binding_v1,
    validate_pool_v1_withdrawal_public_v1, PoolV1InputNoteWitnessV1, PoolV1MembershipWitnessV1,
    PoolV1OutputNoteWitnessV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRelationError,
    PoolV1PaymentRuntimeBindingV1, PoolV1PaymentStatementFormatError,
    PoolV1PrivateTransferPublicV1, PoolV1PrivateTransferWitnessV1, PoolV1WithdrawalPublicV1,
    PoolV1WithdrawalWitnessV1, POOL_V1_CANONICAL_FEE, POOL_V1_PAYMENT_STATEMENT_BYTES,
    POOL_V1_PAYMENT_STATEMENT_VERSION, POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
    POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
};
pub use payment_semantic_terminal::{
    evaluate_pool_v1_private_transfer_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_private_transfer_selected_unmasked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_withdrawal_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_withdrawal_selected_unmasked_terminal_compiled_tag73_v1,
    pool_v1_private_transfer_copy_active_at_point_compiled_v1,
    pool_v1_private_transfer_copy_active_row_masks_compiled_v1,
    pool_v1_withdrawal_copy_active_at_point_compiled_v1,
    pool_v1_withdrawal_copy_active_row_masks_compiled_v1, PoolV1PaymentSemanticTerminalErrorV1,
    PINNED_POOL_V1_PAYMENT_AUXILIARY_LAYOUT_FINGERPRINT_V1,
    PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT_V1,
    PINNED_POOL_V1_PRIVATE_TRANSFER_COPY_ACTIVE_ROWS_FINGERPRINT_V1,
    PINNED_POOL_V1_PRIVATE_TRANSFER_SEMANTIC_REGISTRY_FINGERPRINT_V1,
    PINNED_POOL_V1_WITHDRAWAL_COPY_ACTIVE_ROWS_FINGERPRINT_V1,
    PINNED_POOL_V1_WITHDRAWAL_SEMANTIC_REGISTRY_FINGERPRINT_V1, POOL_V1_PAYMENT_COPY_LANES,
    POOL_V1_PAYMENT_MASKED_TERMINAL_DEGREE, POOL_V1_PAYMENT_PACKED_SEMANTIC_LANES,
    POOL_V1_PAYMENT_POSEIDON_LANES, POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS,
    POOL_V1_PAYMENT_SELECTED_TERMINAL_COLUMNS, POOL_V1_PAYMENT_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE,
    POOL_V1_PAYMENT_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE, POOL_V1_PAYMENT_SOURCE_SEMANTIC_LANES,
    POOL_V1_PAYMENT_TAG73_MU_AGGREGATE_DEGREE, POOL_V1_PAYMENT_TAG73_MU_COLLISION_ROOT_BOUND,
    POOL_V1_PAYMENT_TERMINAL_C1_COLUMNS, POOL_V1_PAYMENT_TERMINAL_FIXED_HEAP_ALLOCATIONS,
    POOL_V1_PAYMENT_TERMINAL_POINTS, POOL_V1_PAYMENT_TERMINAL_ROWS,
    POOL_V1_PAYMENT_TERMINAL_SELECTOR_HEAP_BYTES, POOL_V1_PAYMENT_THETA_COLLISION_DEGREE,
    POOL_V1_PAYMENT_THETA_LANES,
};
#[cfg(not(target_os = "solana"))]
pub use payment_trace::{
    build_pool_v1_private_transfer_trace_v1, build_pool_v1_withdrawal_trace_v1,
    pool_v1_payment_trace_block_v1, validate_pool_v1_private_transfer_trace_v1,
    validate_pool_v1_withdrawal_trace_v1, PoolV1PaymentTraceBlockV1, PoolV1PaymentTraceErrorV1,
    PoolV1PaymentTracePublicOutputsV1, PoolV1PaymentTraceV1, PoolV1PaymentTraceVariantV1,
    POOL_V1_PAYMENT_AUX_ROW_END, POOL_V1_PAYMENT_DIRECTION_BITS,
    POOL_V1_PAYMENT_DIRECTION_ROW_START, POOL_V1_PAYMENT_TRACE_BLOCKS,
    POOL_V1_PAYMENT_TRACE_BLOCK_ROWS, POOL_V1_PAYMENT_TRACE_C1_COLUMNS,
    POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS, POOL_V1_PAYMENT_TRACE_ROWS,
    POOL_V1_PAYMENT_TRACE_TWO_ROUND_ROWS_PER_BLOCK, POOL_V1_PAYMENT_TRACE_TWO_ROUND_TRANSITIONS,
    POOL_V1_PAYMENT_VALUE_BITS, POOL_V1_PAYMENT_VALUE_COUNT, POOL_V1_PAYMENT_VALUE_ROW_START,
    POOL_V1_TAG73_PROOF_GRAMMAR_BYTES,
};
pub use root_history::{
    root_history_location, PoolV1RootHistoryError, RootHistoryLocationV1, RootHistoryPageAddressV1,
    RootHistoryPageV1, POOL_V1_ROOT_HISTORY_CAPACITY, POOL_V1_ROOT_HISTORY_CAPACITY_LOG2,
    POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES, POOL_V1_ROOT_HISTORY_PAGE_MAGIC,
    POOL_V1_ROOT_HISTORY_PAGE_SEED, POOL_V1_ROOT_HISTORY_PAGE_VERSION,
};
pub use tag73_native_profile::{
    v7_pool_native_tag73_proof_body_bytes, V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES,
    V7_POOL_NATIVE_TAG73_PROFILE_BINDING, V7_POOL_NATIVE_TAG73_PROFILE_BINDING_PREIMAGE,
    V7_POOL_NATIVE_TAG73_RELEASE_BINDING, V7_POOL_NATIVE_TAG73_RELEASE_BINDING_PREIMAGE,
    V7_POOL_NATIVE_TAG73_REQUEST_BYTES,
};
pub use verifier_dispatch::{
    decode_verifier_dispatch_request_v1, decode_verifier_dispatch_result_v1,
    encode_verifier_dispatch_request_v1, encode_verifier_dispatch_result_v1,
    historical_anchor_envelope_digest_v1, validate_verifier_dispatch_binding_v1,
    verifier_dispatch_binding_from_envelope_v1, verifier_proof_body_digest_v1,
    verifier_statement_payload_digest_v1, PoolV1VerifierDispatchFormatError,
    VerifierDispatchBindingV1, VerifierDispatchRequestV1, VerifierDispatchResultV1,
    POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_DIGEST_DOMAIN,
    POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES, POOL_V1_VERIFIER_DISPATCH_HASH_SHA256,
    POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC, POOL_V1_VERIFIER_DISPATCH_REQUEST_MAX_BYTES,
    POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES, POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC,
    POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE, POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE,
    POOL_V1_VERIFIER_DISPATCH_VERSION, POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
    POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC, POOL_V1_VERIFIER_RETURN_DATA_MAX_BYTES,
    POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION, POOL_V1_VERIFIER_STATEMENT_PAYLOAD_DIGEST_DOMAIN,
    POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES,
};
pub use verifier_registry::{
    decode_verifier_registry_entry_v1, decode_verifier_registry_v1,
    encode_verifier_registry_entry_v1, encode_verifier_registry_v1,
    validate_verifier_registry_entry_v1, validate_verifier_registry_v1,
    PoolV1VerifierRegistryFormatError, VerifierEntryStatusV1, VerifierRegistryEntryV1,
    VerifierRegistryV1, POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_MAGIC,
    POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT, POOL_V1_VERIFIER_ENTRY_VERSION,
    POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK,
    POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE, POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED,
    POOL_V1_VERIFIER_REGISTRY_MAGIC, POOL_V1_VERIFIER_REGISTRY_VERSION,
};
