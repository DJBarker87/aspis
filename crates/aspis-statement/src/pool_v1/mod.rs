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
pub mod payment_relation;
#[cfg(not(target_os = "solana"))]
pub mod payment_trace;
pub mod root_history;
pub mod verifier_dispatch;
pub mod verifier_registry;

pub use authorization_receipt::{
    decode_pool_v1_authorization_receipt_v1, encode_pool_v1_authorization_receipt_v1,
    validate_pool_v1_authorization_receipt_for_settlement_v1,
    PoolV1AuthorizationReceiptError, PoolV1AuthorizationReceiptV1,
    POOL_V1_AUTHORIZATION_RECEIPT_BYTES, POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_BYTES,
    POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN, POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256,
    POOL_V1_AUTHORIZATION_RECEIPT_MAGIC, POOL_V1_AUTHORIZATION_RECEIPT_PREFIX_BYTES,
    POOL_V1_AUTHORIZATION_RECEIPT_SEED, POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED,
    POOL_V1_AUTHORIZATION_RECEIPT_VERSION,
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
