//! Pool V1 authenticated state-transition kernel.
//!
//! The native entrypoint exposes exact V1 initialization, vault-backed
//! deposit, proof-authorized 1-to-2 private transfer and withdrawal ABIs.  It
//! deliberately declares no static program id: every PDA binds the runtime
//! `program_id`, while release tooling must separately pin the deployment id.
//! No raw append instruction exists.

#![no_std]
#![allow(unexpected_cfgs)]

#[cfg(test)]
extern crate std;

pub mod anchor;
pub mod cancel_prepared_settlement_instruction;
pub mod deposit;
pub mod deposit_transport;
pub mod empty_roots;
pub mod error;
pub mod history;
pub mod instruction;
pub mod nullifier;
pub mod pair_dispatch;
#[cfg(feature = "pair-forest-account-evidence")]
pub mod pair_forest;
#[cfg(feature = "pair-forest-account-evidence")]
pub(crate) mod pair_forest_dispatch;
pub(crate) mod pair_processor;
pub mod pair_state;
pub(crate) mod prepared_settlement;
pub(crate) mod prepared_settlement_format;
pub mod prepared_settlement_instruction;
pub mod processor;
pub mod registry;
pub mod settle_prepared_instruction;
pub mod state;
mod transition;
pub mod vault;
pub mod verifier_dispatch;

pub use anchor::{
    authenticate_historical_anchor_v1, AuthenticatedHistoricalAnchorV1,
    HistoricalAnchorAuthorizationV1,
};
pub use cancel_prepared_settlement_instruction::{
    decode_cancel_prepared_settlement_instruction_v1,
    encode_cancel_prepared_settlement_instruction_v1, CancelPreparedSettlementAccountShapeV1,
    CancelPreparedSettlementInstructionFormatErrorV1, CancelPreparedSettlementInstructionV1,
    POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_BYTES,
    POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_MAGIC,
};
pub use deposit::{apply_vault_backed_deposit_v1, DepositRequestV1};
pub use deposit_transport::process_vault_backed_deposit_instruction_v1;
pub use empty_roots::{POOL_V1_EMPTY_ROOTS, POOL_V1_PAIR_EMPTY_ROOTS};
pub use error::PoolV1ProgramError;
pub use history::{pool_v1_root_page_address, RootPageHeaderV1};
pub use instruction::{
    decode_initialize_instruction_v1, decode_pair_private_transfer_instruction_v1,
    decode_pair_withdrawal_instruction_v1, decode_private_transfer_instruction_v1,
    decode_withdrawal_instruction_v1, encode_initialize_instruction_v1,
    encode_pair_private_transfer_instruction_v1, encode_pair_withdrawal_instruction_v1,
    encode_private_transfer_instruction_v1, encode_withdrawal_instruction_v1,
    PoolInstructionFormatErrorV1, PrivateTransferInstructionV1, PrivateTransferStatementV1,
    TransitionReceiptV1, WithdrawalInstructionV1, WithdrawalStatementV1,
    POOL_V1_INITIALIZATION_RECEIPT_BYTES, POOL_V1_INITIALIZE_INSTRUCTION_BYTES,
    POOL_V1_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_PAIR_PRIVATE_TRANSFER_INSTRUCTION_MAGIC,
    POOL_V1_PAIR_WITHDRAWAL_INSTRUCTION_MAGIC, POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC,
    POOL_V1_SPEND_INSTRUCTION_BYTES, POOL_V1_TRANSITION_RECEIPT_BYTES,
    POOL_V1_TRANSITION_RECEIPT_MAGIC, POOL_V1_TRANSITION_STATEMENT_BYTES,
    POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC,
};
pub use nullifier::{
    plan_nullifier_marker_consumption_v1, pool_v1_nullifier_marker_address,
    NullifierMarkerPreparationV1, PlannedNullifierMarkerV1,
};
pub use pair_dispatch::{
    derive_pair_verifier_account_claim_v1, dispatch_pair_verifier_readonly_v1,
    plan_pair_verifier_dispatch_v1, PairVerifierAccountClaimV1, PlannedPairVerifierDispatchV1,
};
#[cfg(feature = "pair-forest-account-evidence")]
pub use pair_forest::{
    decode_pair_forest_checkpoint_instruction_v1, decode_pair_forest_deposit_instruction_v1,
    decode_pair_forest_initialize_instruction_v1,
    decode_retained_pair_forest_checkpoint_account_v1,
    encode_pair_forest_checkpoint_instruction_v1, encode_pair_forest_deposit_instruction_v1,
    encode_pair_forest_initialize_instruction_v1, plan_pair_forest_checkpoint_accounts_v1,
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_global_root_v1,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_lane_root_page_address,
    pool_v1_pair_forest_master_address, PlannedPairForestCheckpointAccountsV1,
    POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT, POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES,
    POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC, POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
    POOL_V1_PAIR_FOREST_DEPOSIT_INSTRUCTION_MAGIC, POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT,
    POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_PAIR_FOREST_LANE_SEED,
    POOL_V1_PAIR_FOREST_MASTER_SEED,
};
pub use pair_state::{
    pool_v1_pair_state_address, PairAppendReceiptV1, PairPoolStateV1,
    PairVerifiedAfterstateReceiptV1, POOL_V1_PAIR_STATE_ACCOUNT_BYTES,
    POOL_V1_PAIR_STATE_ACCOUNT_MAGIC, POOL_V1_PAIR_STATE_ACCOUNT_VERSION, POOL_V1_PAIR_STATE_SEED,
};
pub use prepared_settlement_format::{
    pool_v1_prepared_settlement_plan_address, pool_v1_prepared_settlement_rollover_address,
    POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES,
    POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES, POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,
    POOL_V1_PREPARED_SETTLEMENT_SEED,
};
pub use prepared_settlement_instruction::{
    decode_prepare_settlement_instruction_v1, encode_prepare_settlement_instruction_v1,
    PrepareSettlementInstructionFormatErrorV1, PrepareSettlementInstructionV1,
    POOL_V1_PREPARE_SETTLEMENT_HEADER_BYTES, POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES,
    POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC,
};
pub use processor::process_instruction;
pub use registry::{
    pool_v1_verifier_entry_address, pool_v1_verifier_registry_address, POOL_V1_VERIFIER_ENTRY_SEED,
    POOL_V1_VERIFIER_REGISTRY_SEED,
};
pub use settle_prepared_instruction::{
    decode_settle_prepared_instruction_v1, encode_settle_prepared_instruction_v1,
    SettlePreparedInstructionFormatErrorV1, SettlePreparedInstructionV1,
    POOL_V1_SETTLE_PREPARED_HEADER_BYTES, POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES,
    POOL_V1_SETTLE_PREPARED_INSTRUCTION_MAGIC,
};
pub use state::{
    pool_v1_state_address, PoolInitializationV1, PoolStateV1, POOL_V1_STATE_ACCOUNT_BYTES,
    POOL_V1_STATE_ACCOUNT_MAGIC, POOL_V1_STATE_ACCOUNT_VERSION, POOL_V1_STATE_SEED,
};
pub use vault::{
    pool_v1_vault_authority_address, pool_v1_vault_token_account_address,
    LEGACY_SPL_TOKEN_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES,
    LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_VAULT_AUTHORITY_SEED, POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,
};
pub use verifier_dispatch::{
    authenticate_verifier_return_data_v1, dispatch_authenticated_verifier_readonly_v1,
    plan_authenticated_verifier_dispatch_v1, AuthenticatedVerifierDispatchV1,
    PlannedVerifierDispatchV1, VerifierDispatchClaimV1,
};
