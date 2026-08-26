//! Fail-closed ingestion of the exact Solana `getBlock`/root-account fields
//! needed by the Pool V1 wallet scanner.
//!
//! This module deliberately stops at the JSON/RPC trust boundary: an HTTP
//! client or serde layer must map the named RPC fields into these borrowed
//! views and assert the commitment used for each request. From there the
//! indexer strictly decodes Solana binary strings, resolves v0 loaded
//! addresses, authenticates every top-level Pool invocation in transaction
//! order, verifies every reconstructed append root against a deployment-owned
//! canonical root-page account, and applies the complete block transactionally
//! to `ScanStateV1`. Transaction-global return data is only an optional exact
//! check on the final Pool setter; a later program may overwrite it.

use std::collections::BTreeSet;

use aspis_pool::{
    instruction::encode_transition_receipt_v1, pool_v1_root_page_address, TransitionReceiptV1,
};
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        root_history::{read_root_history_page_root_v1, validate_root_history_page_bytes_v1},
        root_history_location, DepositEventV1, DepositReceiptV1, PoolV1RootHistoryError,
        POOL_V1_DEPOSIT_RETURN_MAX_BYTES, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    },
};
use solana_program::pubkey::Pubkey;

use crate::{
    pool_transport::{
        authenticate_top_level_pool_instruction_v1, AuthenticatedCancelledSettlementV1,
        AuthenticatedDepositInstructionV1, AuthenticatedPreparedSettlementPlanIdentityV1,
        AuthenticatedPreparedSettlementV1, AuthenticatedTopLevelPoolInstructionV1,
        AuthenticatedTransitionInstructionV1, PoolRpcAdapterErrorV1,
    },
    rpc_adapter::{
        DepositRpcAdapterErrorV1, DepositRpcBindingV1, FinalizedRpcTransactionV1,
        ResolvedRpcInstructionV1, ResolvedRpcReturnDataV1,
    },
    rpc_wire::{
        decode_base58_bounded_v1, decode_base58_fixed_v1, decode_base64_standard_bounded_v1,
        RpcBinaryDecodeErrorV1,
    },
    scan_state::{
        encode_deposit_event_record_v1, DepositEventIdV1, DepositEventRecordErrorV1,
        DepositScanOutcomeV1, FinalizedBlockAdvanceV1, FinalizedBlockV1, FinalizedChainPointV1,
        FinalizedDepositRecordV1, FinalizedPublicOutputRecordV1, LocalOwnerKeyStoreV1,
        PublicOutputScanOutcomeV1, RollbackSummaryV1, ScanStateErrorV1, ScanStateV1,
    },
    ViewingSecretKeyV1,
};

/// Solana packet payload limit. It is a conservative allocation ceiling for
/// each already-JSON-decoded compiled-instruction data string.
pub const SOLANA_PACKET_DATA_BYTES_V1: usize = 1_232;
pub const SOLANA_RETURN_DATA_MAX_BYTES_V1: usize = 1_024;
pub const SOLANA_ACCOUNT_KEY_LIMIT_V1: usize = 256;
pub const SOLANA_SIGNATURE_LIMIT_V1: usize = (SOLANA_PACKET_DATA_BYTES_V1 - 1) / 64;
/// Each serialized compiled instruction consumes at least its program index
/// and two one-byte compact lengths.
pub const SOLANA_TOP_LEVEL_INSTRUCTION_LIMIT_V1: usize = SOLANA_PACKET_DATA_BYTES_V1 / 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolanaRpcCommitmentV1 {
    Processed,
    Confirmed,
    Finalized,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolanaRpcTransactionVersionV1 {
    Legacy,
    V0,
    Unsupported(u8),
}

/// One RPC `[data, encoding]` tuple. Return data accepts strict bounded
/// `"base58"` or `"base64"`; raw account data remains exact `"base64"`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcEncodedBinaryV1<'a> {
    pub data: &'a str,
    pub encoding: &'a str,
}

/// `meta.loadedAddresses`, retained separately so the resolver can enforce
/// the v0 ordering: static, loaded writable, loaded readonly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcLoadedAddressesV1<'a> {
    pub writable: &'a [&'a str],
    pub readonly: &'a [&'a str],
}

/// One top-level compiled instruction from `transaction.message.instructions`.
/// Wider indices are intentional: a deserializer cannot silently truncate an
/// invalid JSON integer into Solana's u8 index domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcCompiledInstructionV1<'a> {
    pub program_id_index: u16,
    pub account_indices: &'a [u16],
    pub data_base58: &'a str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcReturnDataV1<'a> {
    pub program_id_base58: &'a str,
    pub binary: SolanaRpcEncodedBinaryV1<'a>,
}

/// Exact transaction fields required from a `getBlock` response requested
/// with `encoding: "json"`, `transactionDetails: "full"` and
/// `maxSupportedTransactionVersion: 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcTransactionV1<'a> {
    pub version: SolanaRpcTransactionVersionV1,
    pub signatures_base58: &'a [&'a str],
    pub static_account_keys_base58: &'a [&'a str],
    pub loaded_addresses: Option<SolanaRpcLoadedAddressesV1<'a>>,
    pub top_level_instructions: &'a [SolanaRpcCompiledInstructionV1<'a>],
    /// Must be derived exactly from `meta.err == null`.
    pub succeeded: bool,
    pub return_data: Option<SolanaRpcReturnDataV1<'a>>,
}

/// One non-skipped `getBlock(slot)` response. `slot` is the exact requested
/// slot; Solana returns `parentSlot`, which may be less than `slot - 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcBlockV1<'a> {
    pub asserted_commitment: SolanaRpcCommitmentV1,
    pub slot: u64,
    pub blockhash_base58: &'a str,
    pub previous_blockhash_base58: &'a str,
    pub parent_slot: u64,
    pub transactions: &'a [SolanaRpcTransactionV1<'a>],
}

/// Deployment-pinned root-page address. Ingestion independently re-derives
/// this PDA from the pinned program id, Pool and page number before trusting
/// the binding or any RPC account response.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootPageAddressBindingV1 {
    pub page_number: u64,
    pub address: [u8; 32],
}

/// One value in a `getMultipleAccounts` response. `page_number` and `address`
/// are the corresponding requested binding, made explicit so response-order
/// mistakes cannot silently authenticate the wrong page.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcRootPageAccountV1<'a> {
    pub page_number: u64,
    pub address_base58: &'a str,
    pub owner_base58: &'a str,
    pub executable: bool,
    pub data: SolanaRpcEncodedBinaryV1<'a>,
}

/// A single-context account batch requested with `commitment: "finalized"`
/// and `minContextSlot` equal to the deposit block slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaRpcRootPageBatchV1<'a> {
    pub asserted_commitment: SolanaRpcCommitmentV1,
    pub context_slot: u64,
    pub accounts: &'a [SolanaRpcRootPageAccountV1<'a>],
}

/// Public proof trail connecting one accepted deposit id/root to one pinned,
/// finalized, deployment-owned root-history account snapshot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistoricalRootEvidenceV1 {
    pub event_id: DepositEventIdV1,
    pub root_sequence: u64,
    pub root: [u8; 32],
    pub page_number: u64,
    pub page_address: [u8; 32],
    pub snapshot_context_slot: u64,
}

/// Exact public append stream reconstructed from authenticated top-level Pool
/// instructions and finalized root-history pages.  This includes unrelated
/// recipients: a wallet needs every leaf in exact order to maintain its own
/// Merkle authentication paths without trusting an indexer-supplied witness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedAppendEvidenceV1 {
    pub event_id: DepositEventIdV1,
    pub leaf_index: u64,
    pub root_sequence: u64,
    pub note_commitment: [u8; 32],
    pub root: [u8; 32],
}

pub struct FinalizedBlockIngestResultV1 {
    pub advance: FinalizedBlockAdvanceV1,
    pub rollback: Option<RollbackSummaryV1>,
    /// Stable identities in exact positional correspondence with
    /// `deposit_outcomes`. Durable note stores use this explicit pairing to
    /// commit recovered ciphertext without guessing transaction/event order.
    pub deposit_event_ids: Vec<DepositEventIdV1>,
    pub deposit_outcomes: Vec<DepositScanOutcomeV1>,
    pub transition_outcomes: Vec<PublicOutputScanOutcomeV1>,
    /// Owned, public evidence for atomically marking locally held inputs spent
    /// by nullifier and reconciling recipient/change delivery. Rollback uses
    /// the included output ids; no note opening or secret is retained.
    pub transition_evidence: Vec<FinalizedTransitionEvidenceV1>,
    /// Every successful append in exact top-level instruction/output order.
    pub append_evidence: Vec<FinalizedAppendEvidenceV1>,
    /// Successful non-appending `ASPP` preparations in transaction order.
    /// These public addresses let callers reconcile core/shard plan creation
    /// without treating preparation as a spend or leaf append.
    pub prepared_settlements: Vec<AuthenticatedPreparedSettlementV1>,
    /// Successful non-appending `ASPX` cancellations in transaction order.
    pub cancelled_settlements: Vec<AuthenticatedCancelledSettlementV1>,
    /// All `ASPP`/`ASPF`/`ASPX` lifecycle observations in exact successful
    /// top-level invocation order. Durable reconciliation must use this list,
    /// not independently sorted transaction signatures.
    pub plan_lifecycle: Vec<FinalizedPreparedSettlementLifecycleV1>,
    pub root_evidence: Vec<HistoricalRootEvidenceV1>,
    pub ignored_failed_pool_transactions: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizedPreparedSettlementLifecycleV1 {
    Prepared(AuthenticatedPreparedSettlementV1),
    Settled {
        id: DepositEventIdV1,
        plan: AuthenticatedPreparedSettlementPlanIdentityV1,
    },
    Cancelled(AuthenticatedCancelledSettlementV1),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedTransitionEvidenceV1 {
    pub receipt: TransitionReceiptV1,
    pub output_ids: Vec<DepositEventIdV1>,
    pub authenticated_transport: Vec<u8>,
    pub settled_plan: Option<AuthenticatedPreparedSettlementPlanIdentityV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizedIndexerErrorV1 {
    BlockNotFinalized,
    InvalidBlockHash(RpcBinaryDecodeErrorV1),
    InvalidPreviousBlockHash(RpcBinaryDecodeErrorV1),
    UnsupportedTransactionVersion,
    MissingLoadedAddresses,
    UnexpectedLoadedAddresses,
    MissingAccountKey,
    TooManyAccountKeys,
    TooManySignatures,
    TooManyTopLevelInstructions,
    MissingSignature,
    ZeroSignature,
    DuplicateTransactionSignature,
    InvalidAccountKey(RpcBinaryDecodeErrorV1),
    InvalidSignature(RpcBinaryDecodeErrorV1),
    ProgramIndexOutsideU8,
    ProgramIndexOutOfBounds,
    AccountIndexOutsideU8,
    AccountIndexOutOfBounds,
    CompiledInstructionSetExceedsPacket,
    InvalidInstructionData(RpcBinaryDecodeErrorV1),
    InvalidReturnDataProgram(RpcBinaryDecodeErrorV1),
    WrongReturnDataEncoding,
    InvalidReturnData(RpcBinaryDecodeErrorV1),
    InvalidRootPageBinding,
    WrongRootPageAddressBinding,
    DuplicateRootPageBinding,
    DuplicateRootPageAddressBinding,
    MissingRootPageBatch,
    UnexpectedRootPageBatch,
    RootPagesNotFinalized,
    RootPageContextTooOld,
    DuplicateRootPageSnapshot,
    UnexpectedRootPageSnapshot,
    MissingRootPageSnapshot,
    InvalidRootPageAddress(RpcBinaryDecodeErrorV1),
    InvalidRootPageOwner(RpcBinaryDecodeErrorV1),
    WrongRootPageAddress,
    WrongRootPageOwner,
    ExecutableRootPage,
    WrongRootPageDataEncoding,
    InvalidRootPageData(RpcBinaryDecodeErrorV1),
    RootPage(PoolV1RootHistoryError),
    WrongRootPagePool,
    WrongRootPageNumber,
    HistoricalRootMismatch,
    StaleFinalizedBlock,
    ReplayEventSetMismatch,
    CountOverflow,
    DepositTransport(DepositRpcAdapterErrorV1),
    DepositRecord(DepositEventRecordErrorV1),
    PoolTransport(PoolRpcAdapterErrorV1),
    ScanState(ScanStateErrorV1),
}

enum PreparedPoolInvocationV1 {
    Initialization,
    PreparedSettlement(AuthenticatedPreparedSettlementV1),
    CancelledSettlement(AuthenticatedCancelledSettlementV1),
    Deposit(AuthenticatedDepositInstructionV1),
    Transition(AuthenticatedTransitionInstructionV1),
}

struct PreparedBlockTransportV1 {
    finalized_block: FinalizedBlockV1,
    invocations: Vec<PreparedPoolInvocationV1>,
    ignored_failed_pool_transactions: usize,
}

struct AuthenticatedRootPageV1 {
    page_number: u64,
    address: [u8; 32],
    context_slot: u64,
    bytes: Vec<u8>,
}

fn validate_root_page_bindings_v1(
    program_id: &[u8; 32],
    pool: &[u8; 32],
    bindings: &[RootPageAddressBindingV1],
) -> Result<(), FinalizedIndexerErrorV1> {
    let program_id = Pubkey::new_from_array(*program_id);
    let pool = Pubkey::new_from_array(*pool);
    let mut page_numbers = BTreeSet::new();
    let mut addresses = BTreeSet::new();
    for binding in bindings {
        if binding.address == [0u8; 32] {
            return Err(FinalizedIndexerErrorV1::InvalidRootPageBinding);
        }
        let expected = pool_v1_root_page_address(&program_id, &pool, binding.page_number)
            .0
            .to_bytes();
        if binding.address != expected {
            return Err(FinalizedIndexerErrorV1::WrongRootPageAddressBinding);
        }
        if !page_numbers.insert(binding.page_number) {
            return Err(FinalizedIndexerErrorV1::DuplicateRootPageBinding);
        }
        if !addresses.insert(binding.address) {
            return Err(FinalizedIndexerErrorV1::DuplicateRootPageAddressBinding);
        }
    }
    Ok(())
}

fn resolve_account_keys_v1(
    transaction: &SolanaRpcTransactionV1<'_>,
) -> Result<Vec<[u8; 32]>, FinalizedIndexerErrorV1> {
    let (loaded_writable, loaded_readonly) = match transaction.version {
        SolanaRpcTransactionVersionV1::Legacy => {
            if transaction.loaded_addresses.is_some() {
                return Err(FinalizedIndexerErrorV1::UnexpectedLoadedAddresses);
            }
            (&[][..], &[][..])
        }
        SolanaRpcTransactionVersionV1::V0 => {
            let loaded = transaction
                .loaded_addresses
                .ok_or(FinalizedIndexerErrorV1::MissingLoadedAddresses)?;
            (loaded.writable, loaded.readonly)
        }
        SolanaRpcTransactionVersionV1::Unsupported(_) => {
            return Err(FinalizedIndexerErrorV1::UnsupportedTransactionVersion);
        }
    };

    let total_keys = transaction
        .static_account_keys_base58
        .len()
        .checked_add(loaded_writable.len())
        .and_then(|count| count.checked_add(loaded_readonly.len()))
        .ok_or(FinalizedIndexerErrorV1::CountOverflow)?;
    if total_keys == 0 {
        return Err(FinalizedIndexerErrorV1::MissingAccountKey);
    }
    if total_keys > SOLANA_ACCOUNT_KEY_LIMIT_V1 {
        return Err(FinalizedIndexerErrorV1::TooManyAccountKeys);
    }

    let mut account_keys = Vec::with_capacity(total_keys);
    for encoded_key in transaction
        .static_account_keys_base58
        .iter()
        .chain(loaded_writable.iter())
        .chain(loaded_readonly.iter())
    {
        account_keys.push(
            decode_base58_fixed_v1::<32>(encoded_key)
                .map_err(FinalizedIndexerErrorV1::InvalidAccountKey)?,
        );
    }
    Ok(account_keys)
}

fn prepare_transaction_v1(
    point: FinalizedChainPointV1,
    binding: &DepositRpcBindingV1,
    identity: &crate::scan_state::DepositScanIdentityV1,
    mut current_root_sequence: u64,
    transaction: &SolanaRpcTransactionV1<'_>,
    seen_primary_signatures: &mut BTreeSet<[u8; 64]>,
) -> Result<(Vec<PreparedPoolInvocationV1>, bool), FinalizedIndexerErrorV1> {
    let account_keys = resolve_account_keys_v1(transaction)?;
    if transaction.signatures_base58.is_empty() {
        return Err(FinalizedIndexerErrorV1::MissingSignature);
    }
    if transaction.signatures_base58.len() > SOLANA_SIGNATURE_LIMIT_V1 {
        return Err(FinalizedIndexerErrorV1::TooManySignatures);
    }
    let mut signatures = Vec::with_capacity(transaction.signatures_base58.len());
    for encoded_signature in transaction.signatures_base58 {
        let signature = decode_base58_fixed_v1::<64>(encoded_signature)
            .map_err(FinalizedIndexerErrorV1::InvalidSignature)?;
        if signature == [0u8; 64] {
            return Err(FinalizedIndexerErrorV1::ZeroSignature);
        }
        signatures.push(signature);
    }
    let primary_signature = signatures[0];
    if !seen_primary_signatures.insert(primary_signature) {
        return Err(FinalizedIndexerErrorV1::DuplicateTransactionSignature);
    }

    if transaction.top_level_instructions.len() > SOLANA_TOP_LEVEL_INSTRUCTION_LIMIT_V1 {
        return Err(FinalizedIndexerErrorV1::TooManyTopLevelInstructions);
    }
    let mut program_ids = Vec::with_capacity(transaction.top_level_instructions.len());
    let mut instruction_account_keys = Vec::with_capacity(transaction.top_level_instructions.len());
    let mut instruction_data = Vec::with_capacity(transaction.top_level_instructions.len());
    // One byte for the instruction-vector compact length. This lower bound is
    // deliberately permissive about its multi-byte form, but no real packet
    // can be smaller than the value accumulated here.
    let mut instruction_wire_lower_bound = 1usize;
    for instruction in transaction.top_level_instructions {
        if instruction.program_id_index > u16::from(u8::MAX) {
            return Err(FinalizedIndexerErrorV1::ProgramIndexOutsideU8);
        }
        let program_id = account_keys
            .get(usize::from(instruction.program_id_index))
            .copied()
            .ok_or(FinalizedIndexerErrorV1::ProgramIndexOutOfBounds)?;
        let mut resolved_accounts = Vec::with_capacity(instruction.account_indices.len());
        for account_index in instruction.account_indices {
            if *account_index > u16::from(u8::MAX) {
                return Err(FinalizedIndexerErrorV1::AccountIndexOutsideU8);
            }
            let account_key = account_keys
                .get(usize::from(*account_index))
                .copied()
                .ok_or(FinalizedIndexerErrorV1::AccountIndexOutOfBounds)?;
            resolved_accounts.push(account_key);
        }
        let data = decode_base58_bounded_v1(instruction.data_base58, SOLANA_PACKET_DATA_BYTES_V1)
            .map_err(FinalizedIndexerErrorV1::InvalidInstructionData)?;
        instruction_wire_lower_bound = instruction_wire_lower_bound
            .checked_add(3)
            .and_then(|length| length.checked_add(instruction.account_indices.len()))
            .and_then(|length| length.checked_add(data.len()))
            .ok_or(FinalizedIndexerErrorV1::CountOverflow)?;
        if instruction_wire_lower_bound > SOLANA_PACKET_DATA_BYTES_V1 {
            return Err(FinalizedIndexerErrorV1::CompiledInstructionSetExceedsPacket);
        }
        program_ids.push(program_id);
        instruction_account_keys.push(resolved_accounts);
        instruction_data.push(data);
    }

    let decoded_return_data = match transaction.return_data {
        None => None,
        Some(return_data) => {
            let program_id = decode_base58_fixed_v1::<32>(return_data.program_id_base58)
                .map_err(FinalizedIndexerErrorV1::InvalidReturnDataProgram)?;
            let maximum = if program_id == *binding.program_id() {
                POOL_V1_DEPOSIT_RETURN_MAX_BYTES
            } else {
                SOLANA_RETURN_DATA_MAX_BYTES_V1
            };
            let data = match return_data.binary.encoding {
                "base64" => decode_base64_standard_bounded_v1(return_data.binary.data, maximum),
                "base58" => decode_base58_bounded_v1(return_data.binary.data, maximum),
                _ => return Err(FinalizedIndexerErrorV1::WrongReturnDataEncoding),
            }
            .map_err(FinalizedIndexerErrorV1::InvalidReturnData)?;
            Some((program_id, data))
        }
    };

    let resolved_instructions: Vec<_> = program_ids
        .iter()
        .zip(&instruction_data)
        .zip(&instruction_account_keys)
        .map(
            |((program_id, data), account_keys)| ResolvedRpcInstructionV1 {
                program_id: *program_id,
                account_keys,
                data,
            },
        )
        .collect();
    let invokes_pool = resolved_instructions
        .iter()
        .any(|instruction| instruction.program_id == *binding.program_id());
    if !transaction.succeeded {
        return Ok((Vec::new(), invokes_pool));
    }
    if !invokes_pool {
        return Ok((Vec::new(), false));
    }

    let resolved_return_data =
        decoded_return_data
            .as_ref()
            .map(|(program_id, data)| ResolvedRpcReturnDataV1 {
                program_id: *program_id,
                data,
            });
    let resolved_transaction = FinalizedRpcTransactionV1 {
        point,
        transaction_signature: primary_signature,
        succeeded: true,
        top_level_instructions: &resolved_instructions,
        return_data: resolved_return_data,
    };
    let pool_instruction_indices: Vec<_> = resolved_transaction
        .top_level_instructions
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| {
            (instruction.program_id == *binding.program_id()).then_some(index)
        })
        .collect();
    let last_pool_instruction =
        pool_instruction_indices
            .last()
            .copied()
            .ok_or(FinalizedIndexerErrorV1::PoolTransport(
                PoolRpcAdapterErrorV1::PoolInstructionMissing,
            ))?;
    let pool_owned_return = resolved_return_data
        .filter(|return_data| return_data.program_id == *binding.program_id())
        .map(|return_data| return_data.data);
    let mut prepared_invocations = Vec::with_capacity(pool_instruction_indices.len());
    for instruction_index in pool_instruction_indices {
        let observed_pool_return_data = (instruction_index == last_pool_instruction)
            .then_some(pool_owned_return)
            .flatten();
        let authenticated = authenticate_top_level_pool_instruction_v1(
            binding,
            identity,
            current_root_sequence,
            &resolved_transaction,
            instruction_index,
            observed_pool_return_data,
        )
        .map_err(|error| match error {
            PoolRpcAdapterErrorV1::DepositInstruction(deposit) => {
                FinalizedIndexerErrorV1::DepositTransport(
                    DepositRpcAdapterErrorV1::DepositInstruction(deposit),
                )
            }
            other => FinalizedIndexerErrorV1::PoolTransport(other),
        })?;
        let prepared = match authenticated {
            AuthenticatedTopLevelPoolInstructionV1::Initialization(_) => {
                PreparedPoolInvocationV1::Initialization
            }
            AuthenticatedTopLevelPoolInstructionV1::PreparedSettlement(prepared) => {
                PreparedPoolInvocationV1::PreparedSettlement(prepared)
            }
            AuthenticatedTopLevelPoolInstructionV1::CancelledSettlement(cancelled) => {
                PreparedPoolInvocationV1::CancelledSettlement(cancelled)
            }
            AuthenticatedTopLevelPoolInstructionV1::Deposit(deposit) => {
                current_root_sequence = deposit.root_sequence;
                PreparedPoolInvocationV1::Deposit(deposit)
            }
            AuthenticatedTopLevelPoolInstructionV1::Transition(transition) => {
                current_root_sequence = transition
                    .outputs
                    .last()
                    .ok_or(FinalizedIndexerErrorV1::PoolTransport(
                        PoolRpcAdapterErrorV1::WrongOutputCount,
                    ))?
                    .root_sequence;
                PreparedPoolInvocationV1::Transition(transition)
            }
        };
        prepared_invocations.push(prepared);
    }
    Ok((prepared_invocations, false))
}

fn prepare_block_transport_v1(
    state: &ScanStateV1,
    binding: &DepositRpcBindingV1,
    block: &SolanaRpcBlockV1<'_>,
) -> Result<PreparedBlockTransportV1, FinalizedIndexerErrorV1> {
    if block.asserted_commitment != SolanaRpcCommitmentV1::Finalized {
        return Err(FinalizedIndexerErrorV1::BlockNotFinalized);
    }
    let block_hash = decode_base58_fixed_v1::<32>(block.blockhash_base58)
        .map_err(FinalizedIndexerErrorV1::InvalidBlockHash)?;
    let previous_block_hash = decode_base58_fixed_v1::<32>(block.previous_blockhash_base58)
        .map_err(FinalizedIndexerErrorV1::InvalidPreviousBlockHash)?;
    let point = FinalizedChainPointV1::new(block.slot, block_hash)
        .map_err(FinalizedIndexerErrorV1::ScanState)?;
    let parent = FinalizedChainPointV1::new(block.parent_slot, previous_block_hash)
        .map_err(FinalizedIndexerErrorV1::ScanState)?;
    let finalized_block =
        FinalizedBlockV1::new(point, parent).map_err(FinalizedIndexerErrorV1::ScanState)?;

    let mut current_root_sequence =
        if finalized_block.point() == state.head() && state.retained_block_count() != 0 {
            let mut before_replay = state.clone();
            before_replay
                .rollback_to_v1(finalized_block.parent())
                .map_err(FinalizedIndexerErrorV1::ScanState)?;
            before_replay.root_sequence()
        } else if finalized_block.parent() == state.head() {
            state.root_sequence()
        } else if state.retains_chain_point_v1(finalized_block.parent()) {
            let mut before_fork = state.clone();
            before_fork
                .rollback_to_v1(finalized_block.parent())
                .map_err(FinalizedIndexerErrorV1::ScanState)?;
            before_fork.root_sequence()
        } else {
            return Err(FinalizedIndexerErrorV1::ScanState(
                ScanStateErrorV1::NoRetainedAncestor,
            ));
        };
    let mut seen_primary_signatures = BTreeSet::new();
    let mut invocations = Vec::new();
    let mut ignored_failed_pool_transactions = 0usize;
    for transaction in block.transactions {
        let (transaction_invocations, ignored_failed_pool) = prepare_transaction_v1(
            point,
            binding,
            state.identity(),
            current_root_sequence,
            transaction,
            &mut seen_primary_signatures,
        )?;
        if ignored_failed_pool {
            ignored_failed_pool_transactions = ignored_failed_pool_transactions
                .checked_add(1)
                .ok_or(FinalizedIndexerErrorV1::CountOverflow)?;
        }
        for invocation in transaction_invocations {
            current_root_sequence = match &invocation {
                PreparedPoolInvocationV1::Deposit(deposit) => deposit.root_sequence,
                PreparedPoolInvocationV1::Transition(transition) => {
                    transition
                        .outputs
                        .last()
                        .ok_or(FinalizedIndexerErrorV1::PoolTransport(
                            PoolRpcAdapterErrorV1::WrongOutputCount,
                        ))?
                        .root_sequence
                }
                PreparedPoolInvocationV1::Initialization
                | PreparedPoolInvocationV1::PreparedSettlement(_)
                | PreparedPoolInvocationV1::CancelledSettlement(_) => current_root_sequence,
            };
            invocations.push(invocation);
        }
    }
    Ok(PreparedBlockTransportV1 {
        finalized_block,
        invocations,
        ignored_failed_pool_transactions,
    })
}

/// Perform the complete read-only finalized block/transaction transport pass
/// and return the sorted, unique root-history page numbers that must be fetched
/// in one finalized account batch. Ingestion deliberately repeats this pass so
/// a caller cannot substitute different block contents after planning.
pub fn required_root_page_numbers_for_finalized_rpc_block_v1(
    state: &ScanStateV1,
    binding: &DepositRpcBindingV1,
    block: &SolanaRpcBlockV1<'_>,
) -> Result<Vec<u64>, FinalizedIndexerErrorV1> {
    let prepared = prepare_block_transport_v1(state, binding, block)?;
    let mut pages = BTreeSet::new();
    for invocation in &prepared.invocations {
        match invocation {
            PreparedPoolInvocationV1::Initialization
            | PreparedPoolInvocationV1::PreparedSettlement(_)
            | PreparedPoolInvocationV1::CancelledSettlement(_) => {}
            PreparedPoolInvocationV1::Deposit(deposit) => {
                pages.insert(root_history_location(deposit.root_sequence).page_number);
            }
            PreparedPoolInvocationV1::Transition(transition) => {
                for output in &transition.outputs {
                    pages.insert(root_history_location(output.root_sequence).page_number);
                }
            }
        }
    }
    Ok(pages.into_iter().collect())
}

fn authenticate_root_pages_v1(
    program_id: &[u8; 32],
    pool: &[u8; 32],
    block_slot: u64,
    bindings: &[RootPageAddressBindingV1],
    invocations: &[PreparedPoolInvocationV1],
    batch: Option<&SolanaRpcRootPageBatchV1<'_>>,
) -> Result<Vec<HistoricalRootEvidenceV1>, FinalizedIndexerErrorV1> {
    let mut needed_pages = BTreeSet::new();
    for invocation in invocations {
        match invocation {
            PreparedPoolInvocationV1::Initialization
            | PreparedPoolInvocationV1::PreparedSettlement(_)
            | PreparedPoolInvocationV1::CancelledSettlement(_) => {}
            PreparedPoolInvocationV1::Deposit(deposit) => {
                needed_pages.insert(root_history_location(deposit.root_sequence).page_number);
            }
            PreparedPoolInvocationV1::Transition(transition) => {
                for output in &transition.outputs {
                    needed_pages.insert(root_history_location(output.root_sequence).page_number);
                }
            }
        }
    }
    if needed_pages.is_empty() {
        return match batch {
            None => Ok(Vec::new()),
            Some(batch) if batch.accounts.is_empty() => {
                if batch.asserted_commitment != SolanaRpcCommitmentV1::Finalized {
                    Err(FinalizedIndexerErrorV1::RootPagesNotFinalized)
                } else if batch.context_slot < block_slot {
                    Err(FinalizedIndexerErrorV1::RootPageContextTooOld)
                } else {
                    Ok(Vec::new())
                }
            }
            Some(_) => Err(FinalizedIndexerErrorV1::UnexpectedRootPageBatch),
        };
    }

    let batch = batch.ok_or(FinalizedIndexerErrorV1::MissingRootPageBatch)?;
    if batch.asserted_commitment != SolanaRpcCommitmentV1::Finalized {
        return Err(FinalizedIndexerErrorV1::RootPagesNotFinalized);
    }
    if batch.context_slot < block_slot {
        return Err(FinalizedIndexerErrorV1::RootPageContextTooOld);
    }

    let mut seen_pages = BTreeSet::new();
    let mut authenticated_pages = Vec::with_capacity(batch.accounts.len());
    for account in batch.accounts {
        if !seen_pages.insert(account.page_number) {
            return Err(FinalizedIndexerErrorV1::DuplicateRootPageSnapshot);
        }
        if !needed_pages.contains(&account.page_number) {
            return Err(FinalizedIndexerErrorV1::UnexpectedRootPageSnapshot);
        }
        let binding = bindings
            .iter()
            .find(|binding| binding.page_number == account.page_number)
            .ok_or(FinalizedIndexerErrorV1::UnexpectedRootPageSnapshot)?;
        let address = decode_base58_fixed_v1::<32>(account.address_base58)
            .map_err(FinalizedIndexerErrorV1::InvalidRootPageAddress)?;
        if address != binding.address {
            return Err(FinalizedIndexerErrorV1::WrongRootPageAddress);
        }
        let owner = decode_base58_fixed_v1::<32>(account.owner_base58)
            .map_err(FinalizedIndexerErrorV1::InvalidRootPageOwner)?;
        if owner != *program_id {
            return Err(FinalizedIndexerErrorV1::WrongRootPageOwner);
        }
        if account.executable {
            return Err(FinalizedIndexerErrorV1::ExecutableRootPage);
        }
        if account.data.encoding != "base64" {
            return Err(FinalizedIndexerErrorV1::WrongRootPageDataEncoding);
        }
        let bytes = decode_base64_standard_bounded_v1(
            account.data.data,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        )
        .map_err(FinalizedIndexerErrorV1::InvalidRootPageData)?;
        let header = validate_root_history_page_bytes_v1(&bytes)
            .map_err(FinalizedIndexerErrorV1::RootPage)?;
        if header.pool != *pool {
            return Err(FinalizedIndexerErrorV1::WrongRootPagePool);
        }
        if header.page_number != account.page_number {
            return Err(FinalizedIndexerErrorV1::WrongRootPageNumber);
        }
        authenticated_pages.push(AuthenticatedRootPageV1 {
            page_number: account.page_number,
            address,
            context_slot: batch.context_slot,
            bytes,
        });
    }
    if seen_pages != needed_pages {
        return Err(FinalizedIndexerErrorV1::MissingRootPageSnapshot);
    }

    let mut evidence = Vec::new();
    for invocation in invocations {
        let requirements: Vec<_> = match invocation {
            PreparedPoolInvocationV1::Initialization
            | PreparedPoolInvocationV1::PreparedSettlement(_)
            | PreparedPoolInvocationV1::CancelledSettlement(_) => Vec::new(),
            PreparedPoolInvocationV1::Deposit(deposit) => {
                vec![(deposit.id, deposit.root_sequence, None)]
            }
            PreparedPoolInvocationV1::Transition(transition) => transition
                .outputs
                .iter()
                .map(|output| (output.id, output.root_sequence, output.expected_root))
                .collect(),
        };
        for (event_id, root_sequence, expected_root) in requirements {
            let page_number = root_history_location(root_sequence).page_number;
            let page = authenticated_pages
                .iter()
                .find(|page| page.page_number == page_number)
                .ok_or(FinalizedIndexerErrorV1::MissingRootPageSnapshot)?;
            let authenticated_root = read_root_history_page_root_v1(&page.bytes, root_sequence)
                .map_err(FinalizedIndexerErrorV1::RootPage)?;
            let root = encode_digest_canonical(&authenticated_root);
            if expected_root.is_some_and(|expected| expected != root) {
                return Err(FinalizedIndexerErrorV1::HistoricalRootMismatch);
            }
            evidence.push(HistoricalRootEvidenceV1 {
                event_id,
                root_sequence,
                root,
                page_number,
                page_address: page.address,
                snapshot_context_slot: page.context_slot,
            });
        }
    }
    Ok(evidence)
}

/// Strictly authenticate and ingest one complete finalized block.
///
/// All RPC decoding, transport checks, root authentication and replay-set
/// checks complete before a cloned scan state is changed. The original state
/// is replaced only after every deposit succeeds, so an error leaves the
/// cursor byte-for-byte unchanged. Returned rollback ids and recovered note
/// outcomes must be committed atomically with the newly encoded scan state by
/// the caller.
pub fn ingest_finalized_rpc_block_v1(
    state: &mut ScanStateV1,
    binding: &DepositRpcBindingV1,
    root_page_bindings: &[RootPageAddressBindingV1],
    block: &SolanaRpcBlockV1<'_>,
    root_page_batch: Option<&SolanaRpcRootPageBatchV1<'_>>,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> Result<FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1> {
    validate_root_page_bindings_v1(
        binding.program_id(),
        state.identity().pool(),
        root_page_bindings,
    )?;
    let prepared = prepare_block_transport_v1(state, binding, block)?;
    let finalized_block = prepared.finalized_block;
    let point = finalized_block.point();
    let invocations = prepared.invocations;

    let root_evidence = authenticate_root_pages_v1(
        binding.program_id(),
        state.identity().pool(),
        block.slot,
        root_page_bindings,
        &invocations,
        root_page_batch,
    )?;

    let is_current_replay = point == state.head() && state.retained_block_count() != 0;
    if is_current_replay {
        let mut presented_ids = Vec::new();
        for invocation in &invocations {
            match invocation {
                PreparedPoolInvocationV1::Initialization
                | PreparedPoolInvocationV1::PreparedSettlement(_)
                | PreparedPoolInvocationV1::CancelledSettlement(_) => {}
                PreparedPoolInvocationV1::Deposit(deposit) => presented_ids.push(deposit.id),
                PreparedPoolInvocationV1::Transition(transition) => {
                    presented_ids.extend(transition.outputs.iter().map(|output| output.id));
                }
            }
        }
        if state.retained_event_ids_in_block_v1(point) != presented_ids {
            return Err(FinalizedIndexerErrorV1::ReplayEventSetMismatch);
        }
    } else if state.retains_chain_point_v1(point) {
        return Err(FinalizedIndexerErrorV1::StaleFinalizedBlock);
    }

    let mut working = state.clone();
    let mut rollback = None;
    if !is_current_replay && finalized_block.parent() != working.head() {
        if !working.retains_chain_point_v1(finalized_block.parent()) {
            return Err(FinalizedIndexerErrorV1::ScanState(
                ScanStateErrorV1::NoRetainedAncestor,
            ));
        }
        rollback = Some(
            working
                .rollback_to_v1(finalized_block.parent())
                .map_err(FinalizedIndexerErrorV1::ScanState)?,
        );
    }
    let advance = working
        .advance_finalized_block_v1(finalized_block)
        .map_err(FinalizedIndexerErrorV1::ScanState)?;

    let mut deposit_event_ids = Vec::new();
    let mut deposit_outcomes = Vec::new();
    let mut transition_outcomes = Vec::new();
    let mut transition_evidence = Vec::new();
    let mut append_evidence = Vec::new();
    let mut prepared_settlements = Vec::new();
    let mut cancelled_settlements = Vec::new();
    let mut plan_lifecycle = Vec::new();
    for invocation in &invocations {
        match invocation {
            PreparedPoolInvocationV1::Initialization => {}
            PreparedPoolInvocationV1::PreparedSettlement(prepared) => {
                prepared_settlements.push(*prepared);
                plan_lifecycle.push(FinalizedPreparedSettlementLifecycleV1::Prepared(*prepared));
            }
            PreparedPoolInvocationV1::CancelledSettlement(cancelled) => {
                cancelled_settlements.push(*cancelled);
                plan_lifecycle.push(FinalizedPreparedSettlementLifecycleV1::Cancelled(
                    *cancelled,
                ));
            }
            PreparedPoolInvocationV1::Deposit(deposit) => {
                let root = root_evidence
                    .iter()
                    .find(|evidence| evidence.event_id == deposit.id)
                    .ok_or(FinalizedIndexerErrorV1::MissingRootPageSnapshot)?
                    .root;
                let root = decode_digest_canonical(&root)
                    .map_err(|_| FinalizedIndexerErrorV1::HistoricalRootMismatch)?;
                let note_commitment = decode_digest_canonical(&deposit.note_commitment)
                    .map_err(|_| FinalizedIndexerErrorV1::HistoricalRootMismatch)?;
                append_evidence.push(FinalizedAppendEvidenceV1 {
                    event_id: deposit.id,
                    leaf_index: deposit.leaf_index,
                    root_sequence: deposit.root_sequence,
                    note_commitment: deposit.note_commitment,
                    root: encode_digest_canonical(&root),
                });
                let encrypted_note_payload_bytes =
                    u16::try_from(deposit.encrypted_note_payload.len())
                        .map_err(|_| FinalizedIndexerErrorV1::CountOverflow)?;
                let record_bytes = encode_deposit_event_record_v1(&DepositEventV1 {
                    receipt: DepositReceiptV1 {
                        pool: *working.identity().pool(),
                        asset_mint: *working.identity().asset_mint(),
                        source_token_account: deposit.source_token_account,
                        vault_token_account: *working.identity().vault_token_account(),
                        amount: deposit.amount,
                        encrypted_note_payload_bytes,
                        note_commitment,
                        leaf_index: deposit.leaf_index,
                        root_sequence: deposit.root_sequence,
                        root,
                    },
                    encrypted_note_payload: &deposit.encrypted_note_payload,
                })
                .map_err(FinalizedIndexerErrorV1::DepositRecord)?;
                if deposit
                    .observed_pool_return_data
                    .as_deref()
                    .is_some_and(|observed| observed != record_bytes)
                {
                    return Err(FinalizedIndexerErrorV1::PoolTransport(
                        PoolRpcAdapterErrorV1::ReturnDataMismatch,
                    ));
                }
                let observation = FinalizedDepositRecordV1::new(deposit.id, &record_bytes);
                deposit_event_ids.push(deposit.id);
                deposit_outcomes.push(
                    working
                        .ingest_finalized_deposit_v1(observation, viewing_secret, local_keys)
                        .map_err(FinalizedIndexerErrorV1::ScanState)?,
                );
            }
            PreparedPoolInvocationV1::Transition(transition) => {
                let last_output =
                    transition
                        .outputs
                        .last()
                        .ok_or(FinalizedIndexerErrorV1::PoolTransport(
                            PoolRpcAdapterErrorV1::WrongOutputCount,
                        ))?;
                let root = root_evidence
                    .iter()
                    .find(|evidence| evidence.event_id == last_output.id)
                    .ok_or(FinalizedIndexerErrorV1::MissingRootPageSnapshot)?
                    .root;
                let receipt = TransitionReceiptV1 {
                    transition_kind: transition.transition_kind,
                    pool: *working.identity().pool(),
                    nullifier: transition.nullifier,
                    first_output: transition.first_output,
                    second_output_or_destination: transition.second_output_or_destination,
                    withdrawal_amount: transition.withdrawal_amount,
                    first_leaf_index: transition.outputs[0].leaf_index,
                    second_leaf_index: transition
                        .outputs
                        .get(1)
                        .map_or(0, |output| output.leaf_index),
                    root_sequence: last_output.root_sequence,
                    root: decode_digest_canonical(&root)
                        .map_err(|_| FinalizedIndexerErrorV1::HistoricalRootMismatch)?,
                };
                let receipt_bytes = encode_transition_receipt_v1(&receipt).map_err(|error| {
                    FinalizedIndexerErrorV1::PoolTransport(PoolRpcAdapterErrorV1::PoolInstruction(
                        error,
                    ))
                })?;
                if transition
                    .observed_pool_return_data
                    .as_deref()
                    .is_some_and(|observed| observed != receipt_bytes)
                {
                    return Err(FinalizedIndexerErrorV1::PoolTransport(
                        PoolRpcAdapterErrorV1::ReturnDataMismatch,
                    ));
                }
                let mut authenticated_transport =
                    Vec::with_capacity(transition.instruction_bytes.len() + receipt_bytes.len());
                authenticated_transport.extend_from_slice(&transition.instruction_bytes);
                authenticated_transport.extend_from_slice(&receipt_bytes);
                for output in &transition.outputs {
                    let root = root_evidence
                        .iter()
                        .find(|evidence| evidence.event_id == output.id)
                        .ok_or(FinalizedIndexerErrorV1::MissingRootPageSnapshot)?
                        .root;
                    transition_outcomes.push(
                        working
                            .ingest_finalized_public_output_v1(FinalizedPublicOutputRecordV1 {
                                id: output.id,
                                pool: *working.identity().pool(),
                                leaf_index: output.leaf_index,
                                root_sequence: output.root_sequence,
                                note_commitment: output.commitment,
                                root,
                                authenticated_transport: &authenticated_transport,
                            })
                            .map_err(FinalizedIndexerErrorV1::ScanState)?,
                    );
                    append_evidence.push(FinalizedAppendEvidenceV1 {
                        event_id: output.id,
                        leaf_index: output.leaf_index,
                        root_sequence: output.root_sequence,
                        note_commitment: output.commitment,
                        root,
                    });
                }
                transition_evidence.push(FinalizedTransitionEvidenceV1 {
                    receipt,
                    output_ids: transition.outputs.iter().map(|output| output.id).collect(),
                    authenticated_transport,
                    settled_plan: transition.settled_plan,
                });
                if let Some(plan) = transition.settled_plan {
                    plan_lifecycle.push(FinalizedPreparedSettlementLifecycleV1::Settled {
                        id: transition.outputs[0].id,
                        plan,
                    });
                }
            }
        }
    }

    *state = working;
    Ok(FinalizedBlockIngestResultV1 {
        advance,
        rollback,
        deposit_event_ids,
        deposit_outcomes,
        transition_outcomes,
        transition_evidence,
        append_evidence,
        prepared_settlements,
        cancelled_settlements,
        plan_lifecycle,
        root_evidence,
        ignored_failed_pool_transactions: prepared.ignored_failed_pool_transactions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_pool::{
        instruction::{encode_transition_receipt_v1, TransitionReceiptV1},
        PrivateTransferStatementV1, WithdrawalStatementV1,
    };
    use aspis_statement::{
        pool_v1::{
            pool_v1_note_commitment, root_history::initialize_root_history_page_bytes_v1,
            DepositEventV1, DepositReceiptV1, HistoricalAnchorEnvelopeV1, PoolV1TransitionKind,
        },
        poseidon2::Digest,
    };

    use crate::{
        derive_viewing_keypair_v1,
        rpc_adapter::{
            DepositInstructionFormatErrorV1, POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES,
            POOL_V1_DEPOSIT_INSTRUCTION_MAGIC, POOL_V1_DEPOSIT_INSTRUCTION_VERSION,
        },
        scan_state::{encode_deposit_event_record_v1, DepositScanIdentityV1, LocalOwnerKeyStoreV1},
        transaction_builder::{
            build_prepare_withdrawal_instruction_v1, build_private_transfer_instruction_v1,
            PreparedSettlementRouteAccountsV1, VerifierRouteAccountsV1,
        },
        PoolV1WalletError,
    };

    const PROGRAM_ID: [u8; 32] = [0x91; 32];

    fn root_page_address(page_number: u64) -> [u8; 32] {
        pool_v1_root_page_address(
            &Pubkey::new_from_array(PROGRAM_ID),
            &Pubkey::new_from_array(*identity().pool()),
            page_number,
        )
        .0
        .to_bytes()
    }

    struct EmptyKeyStore;

    impl LocalOwnerKeyStoreV1 for EmptyKeyStore {
        fn contains_owner_key_v1(&self, _: &[u8; 32]) -> bool {
            false
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn digest_bytes(seed: u32) -> [u8; 32] {
        encode_digest_canonical(&digest(seed))
    }

    fn identity() -> DepositScanIdentityV1 {
        let program_id = Pubkey::new_from_array(PROGRAM_ID);
        let mint = Pubkey::new_from_array([0x33; 32]);
        let pool = aspis_pool::pool_v1_state_address(&program_id, &mint).0;
        let vault = aspis_pool::pool_v1_vault_token_account_address(&program_id, &pool).0;
        DepositScanIdentityV1::new(
            pool.to_bytes(),
            [0x22; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap()
    }

    fn initial_state() -> ScanStateV1 {
        ScanStateV1::new(
            identity(),
            FinalizedChainPointV1::new(100, [0xa0; 32]).unwrap(),
            7,
            digest_bytes(600),
        )
        .unwrap()
    }

    fn viewing_secret() -> ViewingSecretKeyV1 {
        derive_viewing_keypair_v1(&[0x51; 32]).unwrap().0
    }

    fn encode_base58(bytes: &[u8]) -> String {
        const ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
        let leading_zeroes = bytes.iter().take_while(|byte| **byte == 0).count();
        let mut digits = Vec::<u8>::new();
        for byte in &bytes[leading_zeroes..] {
            let mut carry = u32::from(*byte);
            for digit in &mut digits {
                let value = u32::from(*digit) * 256 + carry;
                *digit = (value % 58) as u8;
                carry = value / 58;
            }
            while carry != 0 {
                digits.push((carry % 58) as u8);
                carry /= 58;
            }
        }
        let mut output = String::with_capacity(leading_zeroes + digits.len());
        output.extend(core::iter::repeat_n('1', leading_zeroes));
        output.extend(
            digits
                .iter()
                .rev()
                .map(|digit| char::from(ALPHABET[usize::from(*digit)])),
        );
        output
    }

    fn encode_base64(bytes: &[u8]) -> String {
        const ALPHABET: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut output = String::with_capacity(bytes.len().div_ceil(3) * 4);
        for chunk in bytes.chunks(3) {
            let a = chunk[0];
            let b = chunk.get(1).copied().unwrap_or(0);
            let c = chunk.get(2).copied().unwrap_or(0);
            output.push(char::from(ALPHABET[usize::from(a >> 2)]));
            output.push(char::from(
                ALPHABET[usize::from(((a & 0x03) << 4) | (b >> 4))],
            ));
            if chunk.len() > 1 {
                output.push(char::from(
                    ALPHABET[usize::from(((b & 0x0f) << 2) | (c >> 6))],
                ));
            } else {
                output.push('=');
            }
            if chunk.len() > 2 {
                output.push(char::from(ALPHABET[usize::from(c & 0x3f)]));
            } else {
                output.push('=');
            }
        }
        output
    }

    fn instruction_bytes(payload: &[u8]) -> Vec<u8> {
        let owner_key = digest(10);
        let salt = digest(100);
        let mut bytes = vec![0u8; POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES + payload.len()];
        bytes[..4].copy_from_slice(&POOL_V1_DEPOSIT_INSTRUCTION_MAGIC);
        bytes[4] = POOL_V1_DEPOSIT_INSTRUCTION_VERSION;
        bytes[6..8].copy_from_slice(&(payload.len() as u16).to_le_bytes());
        bytes[8..40].copy_from_slice(&encode_digest_canonical(&owner_key));
        bytes[40..44].copy_from_slice(&77u32.to_le_bytes());
        bytes[48..80].copy_from_slice(&encode_digest_canonical(&salt));
        bytes[80..].copy_from_slice(payload);
        bytes
    }

    fn deposit_record(leaf_index: u64, root: Digest, payload: &[u8]) -> Vec<u8> {
        deposit_record_for_source(leaf_index, root, payload, [0x55; 32])
    }

    fn deposit_record_for_source(
        leaf_index: u64,
        root: Digest,
        payload: &[u8],
        source_token_account: [u8; 32],
    ) -> Vec<u8> {
        let receipt = DepositReceiptV1 {
            pool: *identity().pool(),
            asset_mint: *identity().asset_mint(),
            source_token_account,
            vault_token_account: *identity().vault_token_account(),
            amount: 77,
            encrypted_note_payload_bytes: payload.len() as u16,
            note_commitment: pool_v1_note_commitment(&digest(10), 77, M31(9), &digest(100)),
            leaf_index,
            root_sequence: leaf_index + 1,
            root,
        };
        encode_deposit_event_record_v1(&DepositEventV1 {
            receipt,
            encrypted_note_payload: payload,
        })
        .unwrap()
    }

    fn history_roots(sequence: u64, root: Digest) -> Vec<Digest> {
        let mut roots: Vec<_> = (0..=sequence)
            .map(|index| digest(1_000 + index as u32))
            .collect();
        roots[sequence as usize] = root;
        roots
    }

    #[allow(clippy::too_many_arguments)]
    fn ingest_private_transition(
        state: &mut ScanStateV1,
        block: (u64, u8, u64, u8),
        signature_byte: u8,
        nullifier_seed: u32,
        recipient: Digest,
        change: Digest,
        intermediate_root: Digest,
        final_root: Digest,
        trailing_return_byte: bool,
    ) -> Result<FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1> {
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: *identity().pool(),
            deployment_domain: *identity().deployment_domain(),
            anchor_sequence: 7,
            anchor_root: digest(600),
            nullifier: digest(nullifier_seed),
            verifier_profile: [0x61; 32],
            verifier_release: [0x62; 32],
        };
        let statement = PrivateTransferStatementV1 {
            pool: *identity().pool(),
            deployment_domain: *identity().deployment_domain(),
            anchor_sequence: 7,
            anchor_root: digest(600),
            nullifier: envelope.nullifier,
            asset_id: M31(identity().asset_id()),
            recipient_commitment: recipient,
            change_commitment: change,
        };
        let built_instruction = build_private_transfer_instruction_v1(
            Pubkey::new_from_array(PROGRAM_ID),
            7,
            &envelope,
            &statement,
            VerifierRouteAccountsV1 {
                payer: Pubkey::new_from_array([0x63; 32]),
                registry_program: Pubkey::new_from_array([0x64; 32]),
                verifier_program: Pubkey::new_from_array([0x65; 32]),
                sealed_proof_account: Pubkey::new_from_array([0x66; 32]),
            },
        )
        .unwrap();
        let instruction_wire = built_instruction.data;
        let mut return_wire = encode_transition_receipt_v1(&TransitionReceiptV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: *identity().pool(),
            nullifier: envelope.nullifier,
            first_output: recipient,
            second_output_or_destination: encode_digest_canonical(&change),
            withdrawal_amount: 0,
            first_leaf_index: 7,
            second_leaf_index: 8,
            root_sequence: 9,
            root: final_root,
        })
        .unwrap()
        .to_vec();
        if trailing_return_byte {
            return_wire.push(0);
        }

        let instruction_data = encode_base58(&instruction_wire);
        let return_data = encode_base64(&return_wire);
        let mut encoded_keys = Vec::with_capacity(built_instruction.accounts.len() + 1);
        encoded_keys.push(encode_base58(&PROGRAM_ID));
        encoded_keys.extend(
            built_instruction
                .accounts
                .iter()
                .map(|account| encode_base58(account.pubkey.as_ref())),
        );
        let static_keys: Vec<_> = encoded_keys.iter().map(String::as_str).collect();
        let account_indices: Vec<_> = (1..=built_instruction.accounts.len() as u16).collect();
        let instructions = [SolanaRpcCompiledInstructionV1 {
            program_id_index: 0,
            account_indices: &account_indices,
            data_base58: &instruction_data,
        }];
        let signature = encode_base58(&[signature_byte; 64]);
        let signatures = [signature.as_str()];
        let transaction = SolanaRpcTransactionV1 {
            version: SolanaRpcTransactionVersionV1::Legacy,
            signatures_base58: &signatures,
            static_account_keys_base58: &static_keys,
            loaded_addresses: None,
            top_level_instructions: &instructions,
            succeeded: true,
            return_data: Some(SolanaRpcReturnDataV1 {
                program_id_base58: &static_keys[0],
                binary: SolanaRpcEncodedBinaryV1 {
                    data: &return_data,
                    encoding: "base64",
                },
            }),
        };
        let transactions = [transaction];
        let block_hash = encode_base58(&[block.1; 32]);
        let parent_hash = encode_base58(&[block.3; 32]);
        let rpc_block = SolanaRpcBlockV1 {
            asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            slot: block.0,
            blockhash_base58: &block_hash,
            previous_blockhash_base58: &parent_hash,
            parent_slot: block.2,
            transactions: &transactions,
        };

        let mut roots = history_roots(9, final_root);
        roots[8] = intermediate_root;
        let mut page_bytes = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(&mut page_bytes, *identity().pool(), 0, &roots)
            .unwrap();
        let page_data = encode_base64(&page_bytes);
        let page_address_bytes = root_page_address(0);
        let page_address = encode_base58(&page_address_bytes);
        let page_owner = encode_base58(&PROGRAM_ID);
        let accounts = [SolanaRpcRootPageAccountV1 {
            page_number: 0,
            address_base58: &page_address,
            owner_base58: &page_owner,
            executable: false,
            data: SolanaRpcEncodedBinaryV1 {
                data: &page_data,
                encoding: "base64",
            },
        }];
        let root_batch = SolanaRpcRootPageBatchV1 {
            asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            context_slot: block.0,
            accounts: &accounts,
        };
        ingest_finalized_rpc_block_v1(
            state,
            &DepositRpcBindingV1::new(PROGRAM_ID).unwrap(),
            &[RootPageAddressBindingV1 {
                page_number: 0,
                address: page_address_bytes,
            }],
            &rpc_block,
            Some(&root_batch),
            &viewing_secret(),
            &EmptyKeyStore,
        )
    }

    #[derive(Clone)]
    struct DepositFixture {
        slot: u64,
        block_hash_byte: u8,
        parent_slot: u64,
        parent_hash_byte: u8,
        signature_byte: u8,
        leaf_index: u64,
        root: Digest,
        roots: Vec<Digest>,
        block_commitment: SolanaRpcCommitmentV1,
        version: SolanaRpcTransactionVersionV1,
        include_loaded_addresses: bool,
        program_id_index: u16,
        instruction_version: u8,
        append_non_pool_instruction: bool,
        succeeded: bool,
        return_encoding: &'static str,
        return_program: [u8; 32],
        root_commitment: SolanaRpcCommitmentV1,
        root_context_slot: u64,
        root_owner: [u8; 32],
        root_address: [u8; 32],
        include_root_page: bool,
    }

    impl DepositFixture {
        fn new(
            block: (u64, u8, u64, u8),
            signature_byte: u8,
            leaf_index: u64,
            root: Digest,
            roots: Vec<Digest>,
        ) -> Self {
            Self {
                slot: block.0,
                block_hash_byte: block.1,
                parent_slot: block.2,
                parent_hash_byte: block.3,
                signature_byte,
                leaf_index,
                root,
                roots,
                block_commitment: SolanaRpcCommitmentV1::Finalized,
                version: SolanaRpcTransactionVersionV1::V0,
                include_loaded_addresses: true,
                program_id_index: 9,
                instruction_version: POOL_V1_DEPOSIT_INSTRUCTION_VERSION,
                append_non_pool_instruction: false,
                succeeded: true,
                return_encoding: "base64",
                return_program: PROGRAM_ID,
                root_commitment: SolanaRpcCommitmentV1::Finalized,
                root_context_slot: block.0,
                root_owner: PROGRAM_ID,
                root_address: root_page_address(0),
                include_root_page: true,
            }
        }

        fn ingest(
            &self,
            state: &mut ScanStateV1,
            secret: &ViewingSecretKeyV1,
        ) -> Result<FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1> {
            let binding = DepositRpcBindingV1::new(PROGRAM_ID).unwrap();
            let page_bindings = [RootPageAddressBindingV1 {
                page_number: 0,
                address: root_page_address(0),
            }];
            let payload = [0xaa];
            let mut instruction_wire = instruction_bytes(&payload);
            instruction_wire[4] = self.instruction_version;
            let instruction_data = encode_base58(&instruction_wire);
            let return_record = deposit_record(self.leaf_index, self.root, &payload);
            let return_data = match self.return_encoding {
                "base58" => encode_base58(&return_record),
                _ => encode_base64(&return_record),
            };
            let payer = encode_base58(&[0x61; 32]);
            let non_pool_program = encode_base58(&[0x62; 32]);
            let pool_program = encode_base58(&PROGRAM_ID);
            let pool = encode_base58(identity().pool());
            let current_page = encode_base58(&root_page_address(0));
            let asset_mint = encode_base58(identity().asset_mint());
            let source_token_account = encode_base58(&[0x55; 32]);
            let source_owner = encode_base58(&[0x56; 32]);
            let vault = encode_base58(identity().vault_token_account());
            let token_program = encode_base58(aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID.as_ref());
            let base_keys = vec![
                payer.as_str(),
                pool.as_str(),
                current_page.as_str(),
                asset_mint.as_str(),
                source_token_account.as_str(),
                source_owner.as_str(),
                vault.as_str(),
                token_program.as_str(),
            ];
            let static_keys = match self.version {
                SolanaRpcTransactionVersionV1::Legacy => {
                    let mut keys = base_keys.clone();
                    keys.push(non_pool_program.as_str());
                    keys.push(pool_program.as_str());
                    keys
                }
                SolanaRpcTransactionVersionV1::V0
                | SolanaRpcTransactionVersionV1::Unsupported(_) => base_keys,
            };
            let loaded_writable = [non_pool_program.as_str()];
            let loaded_readonly = [pool_program.as_str()];
            let loaded_addresses =
                self.include_loaded_addresses
                    .then_some(SolanaRpcLoadedAddressesV1 {
                        writable: &loaded_writable,
                        readonly: &loaded_readonly,
                    });
            let instruction_accounts = [1u16, 2, 3, 4, 5, 6, 7];
            let mut instructions = vec![SolanaRpcCompiledInstructionV1 {
                program_id_index: self.program_id_index,
                account_indices: &instruction_accounts,
                data_base58: &instruction_data,
            }];
            let non_pool_data = encode_base58(&[7]);
            if self.append_non_pool_instruction {
                instructions.push(SolanaRpcCompiledInstructionV1 {
                    program_id_index: 8,
                    account_indices: &[0],
                    data_base58: &non_pool_data,
                });
            }
            let signature = encode_base58(&[self.signature_byte; 64]);
            let signatures = [signature.as_str()];
            let return_program = encode_base58(&self.return_program);
            let transaction = SolanaRpcTransactionV1 {
                version: self.version,
                signatures_base58: &signatures,
                static_account_keys_base58: &static_keys,
                loaded_addresses,
                top_level_instructions: &instructions,
                succeeded: self.succeeded,
                return_data: Some(SolanaRpcReturnDataV1 {
                    program_id_base58: &return_program,
                    binary: SolanaRpcEncodedBinaryV1 {
                        data: &return_data,
                        encoding: self.return_encoding,
                    },
                }),
            };
            let transactions = [transaction];
            let block_hash = encode_base58(&[self.block_hash_byte; 32]);
            let parent_hash = encode_base58(&[self.parent_hash_byte; 32]);
            let block = SolanaRpcBlockV1 {
                asserted_commitment: self.block_commitment,
                slot: self.slot,
                blockhash_base58: &block_hash,
                previous_blockhash_base58: &parent_hash,
                parent_slot: self.parent_slot,
                transactions: &transactions,
            };

            let _required_pages =
                required_root_page_numbers_for_finalized_rpc_block_v1(state, &binding, &block)?;

            if !self.include_root_page {
                return ingest_finalized_rpc_block_v1(
                    state,
                    &binding,
                    &page_bindings,
                    &block,
                    None,
                    secret,
                    &EmptyKeyStore,
                );
            }

            let mut page_bytes = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
            initialize_root_history_page_bytes_v1(
                &mut page_bytes,
                *identity().pool(),
                0,
                &self.roots,
            )
            .unwrap();
            let page_data = encode_base64(&page_bytes);
            let page_address = encode_base58(&self.root_address);
            let page_owner = encode_base58(&self.root_owner);
            let accounts = [SolanaRpcRootPageAccountV1 {
                page_number: 0,
                address_base58: &page_address,
                owner_base58: &page_owner,
                executable: false,
                data: SolanaRpcEncodedBinaryV1 {
                    data: &page_data,
                    encoding: "base64",
                },
            }];
            let root_batch = SolanaRpcRootPageBatchV1 {
                asserted_commitment: self.root_commitment,
                context_slot: self.root_context_slot,
                accounts: &accounts,
            };
            ingest_finalized_rpc_block_v1(
                state,
                &binding,
                &page_bindings,
                &block,
                Some(&root_batch),
                secret,
                &EmptyKeyStore,
            )
        }
    }

    fn ingest_empty_block(
        state: &mut ScanStateV1,
        block: (u64, u8, u64, u8),
        secret: &ViewingSecretKeyV1,
    ) -> Result<FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1> {
        let binding = DepositRpcBindingV1::new(PROGRAM_ID).unwrap();
        let block_hash = encode_base58(&[block.1; 32]);
        let parent_hash = encode_base58(&[block.3; 32]);
        ingest_finalized_rpc_block_v1(
            state,
            &binding,
            &[],
            &SolanaRpcBlockV1 {
                asserted_commitment: SolanaRpcCommitmentV1::Finalized,
                slot: block.0,
                blockhash_base58: &block_hash,
                previous_blockhash_base58: &parent_hash,
                parent_slot: block.2,
                transactions: &[],
            },
            None,
            secret,
            &EmptyKeyStore,
        )
    }

    #[test]
    fn finalized_v0_loaded_program_and_base58_base64_transport_ingest_exact_root() {
        let root = digest(700);
        let fixture = DepositFixture::new(
            (101, 0xa1, 100, 0xa0),
            0x71,
            7,
            root,
            history_roots(8, root),
        );
        let mut state = initial_state();
        let result = fixture.ingest(&mut state, &viewing_secret()).unwrap();

        assert_eq!(result.advance, FinalizedBlockAdvanceV1::Advanced);
        assert!(result.rollback.is_none());
        assert_eq!(result.ignored_failed_pool_transactions, 0);
        assert_eq!(result.deposit_outcomes.len(), 1);
        assert!(matches!(
            result.deposit_outcomes[0],
            DepositScanOutcomeV1::InvalidEncryptedPayload(PoolV1WalletError::WrongEnvelopeLength)
        ));
        assert_eq!(result.root_evidence.len(), 1);
        assert_eq!(result.root_evidence[0].root_sequence, 8);
        assert_eq!(result.root_evidence[0].root, encode_digest_canonical(&root));
        assert_eq!(result.root_evidence[0].page_address, root_page_address(0));
        assert_eq!(result.root_evidence[0].snapshot_context_slot, 101);
        assert_eq!(state.next_leaf_index(), 8);
        assert_eq!(state.root(), &encode_digest_canonical(&root));
        assert_eq!(state.head().slot(), 101);

        let mut base58_fixture = fixture.clone();
        base58_fixture.return_encoding = "base58";
        let mut base58_state = initial_state();
        let base58_result = base58_fixture
            .ingest(&mut base58_state, &viewing_secret())
            .unwrap();
        assert_eq!(base58_result.deposit_outcomes.len(), 1);
        assert_eq!(base58_state.next_leaf_index(), 8);

        // A later top-level program may both follow the Pool call and replace
        // transaction-global return data. The append remains reconstructible
        // from ASDI plus the authenticated history page.
        let mut overwritten = fixture;
        overwritten.append_non_pool_instruction = true;
        overwritten.return_program = [0x62; 32];
        let mut overwritten_state = initial_state();
        let overwritten_result = overwritten
            .ingest(&mut overwritten_state, &viewing_secret())
            .unwrap();
        assert_eq!(overwritten_result.deposit_outcomes.len(), 1);
        assert_eq!(overwritten_state.next_leaf_index(), 8);
    }

    #[test]
    fn two_pool_deposits_in_one_transaction_ingest_in_instruction_order() {
        let first_root = digest(701);
        let final_root = digest(702);
        let first_payload = [0xaa];
        let second_payload = [0xbb];
        let first_wire = instruction_bytes(&first_payload);
        let second_wire = instruction_bytes(&second_payload);
        let first_data = encode_base58(&first_wire);
        let second_data = encode_base58(&second_wire);
        let return_wire = deposit_record_for_source(8, final_root, &second_payload, [0x57; 32]);
        let return_data = encode_base64(&return_wire);

        let encoded_keys = [
            encode_base58(&PROGRAM_ID),
            encode_base58(identity().pool()),
            encode_base58(&root_page_address(0)),
            encode_base58(identity().asset_mint()),
            encode_base58(&[0x55; 32]),
            encode_base58(&[0x56; 32]),
            encode_base58(identity().vault_token_account()),
            encode_base58(aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID.as_ref()),
            encode_base58(&[0x57; 32]),
            encode_base58(&[0x58; 32]),
        ];
        let keys: Vec<_> = encoded_keys.iter().map(String::as_str).collect();
        let first_accounts = [1u16, 2, 3, 4, 5, 6, 7];
        let second_accounts = [1u16, 2, 3, 8, 9, 6, 7];
        let instructions = [
            SolanaRpcCompiledInstructionV1 {
                program_id_index: 0,
                account_indices: &first_accounts,
                data_base58: &first_data,
            },
            SolanaRpcCompiledInstructionV1 {
                program_id_index: 0,
                account_indices: &second_accounts,
                data_base58: &second_data,
            },
        ];
        let signature = encode_base58(&[0x75; 64]);
        let signatures = [signature.as_str()];
        let transaction = SolanaRpcTransactionV1 {
            version: SolanaRpcTransactionVersionV1::Legacy,
            signatures_base58: &signatures,
            static_account_keys_base58: &keys,
            loaded_addresses: None,
            top_level_instructions: &instructions,
            succeeded: true,
            return_data: Some(SolanaRpcReturnDataV1 {
                program_id_base58: keys[0],
                binary: SolanaRpcEncodedBinaryV1 {
                    data: &return_data,
                    encoding: "base64",
                },
            }),
        };
        let transactions = [transaction];
        let block_hash = encode_base58(&[0xa1; 32]);
        let parent_hash = encode_base58(&[0xa0; 32]);
        let block = SolanaRpcBlockV1 {
            asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            slot: 101,
            blockhash_base58: &block_hash,
            previous_blockhash_base58: &parent_hash,
            parent_slot: 100,
            transactions: &transactions,
        };

        let mut roots = history_roots(9, final_root);
        roots[8] = first_root;
        let mut page_bytes = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(&mut page_bytes, *identity().pool(), 0, &roots)
            .unwrap();
        let page_data = encode_base64(&page_bytes);
        let page_address_bytes = root_page_address(0);
        let page_address = encode_base58(&page_address_bytes);
        let owner = encode_base58(&PROGRAM_ID);
        let accounts = [SolanaRpcRootPageAccountV1 {
            page_number: 0,
            address_base58: &page_address,
            owner_base58: &owner,
            executable: false,
            data: SolanaRpcEncodedBinaryV1 {
                data: &page_data,
                encoding: "base64",
            },
        }];
        let batch = SolanaRpcRootPageBatchV1 {
            asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            context_slot: 101,
            accounts: &accounts,
        };
        let mut state = initial_state();
        let result = ingest_finalized_rpc_block_v1(
            &mut state,
            &DepositRpcBindingV1::new(PROGRAM_ID).unwrap(),
            &[RootPageAddressBindingV1 {
                page_number: 0,
                address: page_address_bytes,
            }],
            &block,
            Some(&batch),
            &viewing_secret(),
            &EmptyKeyStore,
        )
        .unwrap();
        assert_eq!(result.deposit_event_ids.len(), 2);
        assert_eq!(result.deposit_event_ids[0].instruction_index(), 0);
        assert_eq!(result.deposit_event_ids[1].instruction_index(), 1);
        assert_eq!(result.root_evidence[0].root_sequence, 8);
        assert_eq!(result.root_evidence[1].root_sequence, 9);
        assert_eq!(result.append_evidence.len(), 2);
        assert_eq!(
            result.append_evidence[0].event_id,
            result.deposit_event_ids[0]
        );
        assert_eq!(result.append_evidence[0].leaf_index, 7);
        assert_eq!(result.append_evidence[0].root_sequence, 8);
        let deposit_commitment = encode_digest_canonical(&pool_v1_note_commitment(
            &digest(10),
            77,
            M31(9),
            &digest(100),
        ));
        assert_eq!(
            result.append_evidence[0].note_commitment,
            deposit_commitment
        );
        assert_eq!(
            result.append_evidence[1].event_id,
            result.deposit_event_ids[1]
        );
        assert_eq!(result.append_evidence[1].leaf_index, 8);
        assert_eq!(result.append_evidence[1].root_sequence, 9);
        assert_eq!(
            result.append_evidence[1].note_commitment,
            deposit_commitment
        );
        assert_eq!(state.next_leaf_index(), 9);
        assert_eq!(state.root(), &encode_digest_canonical(&final_root));
    }

    #[test]
    fn finalized_preparation_is_non_appending_metadata_and_exact_replay_is_idempotent() {
        let program_id = Pubkey::new_from_array(PROGRAM_ID);
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: *identity().pool(),
            deployment_domain: *identity().deployment_domain(),
            anchor_sequence: 7,
            anchor_root: digest(600),
            nullifier: digest(610),
            verifier_profile: [0x61; 32],
            verifier_release: [0x62; 32],
        };
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(identity().asset_id()),
            amount: 25,
            destination_token_account: [0x63; 32],
            change_commitment: digest(620),
        };
        let instruction = build_prepare_withdrawal_instruction_v1(
            program_id,
            7,
            &envelope,
            &statement,
            101,
            140,
            PreparedSettlementRouteAccountsV1 {
                plan_authority: Pubkey::new_from_array([0x64; 32]),
                registry_program: Pubkey::new_from_array([0x65; 32]),
                authorization_receipt: Pubkey::new_from_array([0x66; 32]),
            },
        )
        .unwrap();
        let mut encoded_keys = Vec::with_capacity(instruction.accounts.len() + 1);
        encoded_keys.push(encode_base58(&PROGRAM_ID));
        encoded_keys.extend(
            instruction
                .accounts
                .iter()
                .map(|account| encode_base58(account.pubkey.as_ref())),
        );
        let key_refs: Vec<_> = encoded_keys.iter().map(String::as_str).collect();
        let account_indices: Vec<_> = (1..=instruction.accounts.len() as u16).collect();
        let instruction_data = encode_base58(&instruction.data);
        let compiled = [SolanaRpcCompiledInstructionV1 {
            program_id_index: 0,
            account_indices: &account_indices,
            data_base58: &instruction_data,
        }];
        let failed_signature = encode_base58(&[0x70; 64]);
        let failed_signatures = [failed_signature.as_str()];
        let signature = encode_base58(&[0x71; 64]);
        let signatures = [signature.as_str()];
        let transactions = [
            SolanaRpcTransactionV1 {
                version: SolanaRpcTransactionVersionV1::Legacy,
                signatures_base58: &failed_signatures,
                static_account_keys_base58: &key_refs,
                loaded_addresses: None,
                top_level_instructions: &compiled,
                succeeded: false,
                return_data: None,
            },
            SolanaRpcTransactionV1 {
                version: SolanaRpcTransactionVersionV1::Legacy,
                signatures_base58: &signatures,
                static_account_keys_base58: &key_refs,
                loaded_addresses: None,
                top_level_instructions: &compiled,
                succeeded: true,
                return_data: None,
            },
        ];
        let block_hash = encode_base58(&[0xa1; 32]);
        let parent_hash = encode_base58(&[0xa0; 32]);
        let block = SolanaRpcBlockV1 {
            asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            slot: 101,
            blockhash_base58: &block_hash,
            previous_blockhash_base58: &parent_hash,
            parent_slot: 100,
            transactions: &transactions,
        };
        let binding = DepositRpcBindingV1::new(PROGRAM_ID).unwrap();
        let mut state = initial_state();
        let unfinalized = SolanaRpcBlockV1 {
            asserted_commitment: SolanaRpcCommitmentV1::Confirmed,
            ..block
        };
        assert_eq!(
            required_root_page_numbers_for_finalized_rpc_block_v1(&state, &binding, &unfinalized),
            Err(FinalizedIndexerErrorV1::BlockNotFinalized)
        );
        assert!(
            required_root_page_numbers_for_finalized_rpc_block_v1(&state, &binding, &block)
                .unwrap()
                .is_empty()
        );
        let result = ingest_finalized_rpc_block_v1(
            &mut state,
            &binding,
            &[],
            &block,
            None,
            &viewing_secret(),
            &EmptyKeyStore,
        )
        .unwrap();
        assert_eq!(result.advance, FinalizedBlockAdvanceV1::Advanced);
        assert_eq!(result.ignored_failed_pool_transactions, 1);
        assert_eq!(result.prepared_settlements.len(), 1);
        assert_eq!(result.prepared_settlements[0].source_root_sequence, 7);
        assert_eq!(
            result.prepared_settlements[0].core_plan,
            instruction.accounts[6].pubkey.to_bytes()
        );
        assert_eq!(state.next_leaf_index(), 7);
        assert_eq!(state.root(), &digest_bytes(600));

        let replay = ingest_finalized_rpc_block_v1(
            &mut state,
            &binding,
            &[],
            &block,
            None,
            &viewing_secret(),
            &EmptyKeyStore,
        )
        .unwrap();
        assert_eq!(replay.advance, FinalizedBlockAdvanceV1::AlreadyCurrent);
        assert_eq!(replay.prepared_settlements, result.prepared_settlements);
    }

    #[test]
    fn adversarial_finality_loaded_address_transport_and_root_fail_without_mutation() {
        let root = digest(700);
        let canonical = DepositFixture::new(
            (101, 0xa1, 100, 0xa0),
            0x71,
            7,
            root,
            history_roots(8, root),
        );
        let secret = viewing_secret();

        assert_eq!(
            validate_root_page_bindings_v1(
                &PROGRAM_ID,
                identity().pool(),
                &[RootPageAddressBindingV1 {
                    page_number: 0,
                    address: [0x92; 32],
                }],
            ),
            Err(FinalizedIndexerErrorV1::WrongRootPageAddressBinding)
        );

        let mut cases = Vec::new();
        let mut unfinalized = canonical.clone();
        unfinalized.block_commitment = SolanaRpcCommitmentV1::Confirmed;
        cases.push((unfinalized, FinalizedIndexerErrorV1::BlockNotFinalized));

        let mut missing_loaded = canonical.clone();
        missing_loaded.include_loaded_addresses = false;
        cases.push((
            missing_loaded,
            FinalizedIndexerErrorV1::MissingLoadedAddresses,
        ));

        let mut index_overflow = canonical.clone();
        index_overflow.program_id_index = 256;
        cases.push((
            index_overflow,
            FinalizedIndexerErrorV1::ProgramIndexOutsideU8,
        ));

        let mut wrong_return_encoding = canonical.clone();
        wrong_return_encoding.return_encoding = "base32";
        cases.push((
            wrong_return_encoding,
            FinalizedIndexerErrorV1::WrongReturnDataEncoding,
        ));

        let mut old_root_snapshot = canonical.clone();
        old_root_snapshot.root_context_slot = 100;
        cases.push((
            old_root_snapshot,
            FinalizedIndexerErrorV1::RootPageContextTooOld,
        ));

        let mut unfinalized_root_snapshot = canonical.clone();
        unfinalized_root_snapshot.root_commitment = SolanaRpcCommitmentV1::Confirmed;
        cases.push((
            unfinalized_root_snapshot,
            FinalizedIndexerErrorV1::RootPagesNotFinalized,
        ));

        let mut wrong_root_owner = canonical.clone();
        wrong_root_owner.root_owner = [0x93; 32];
        cases.push((
            wrong_root_owner,
            FinalizedIndexerErrorV1::WrongRootPageOwner,
        ));

        let mut forged_root = canonical;
        forged_root.roots = history_roots(8, digest(701));
        cases.push((
            forged_root,
            FinalizedIndexerErrorV1::PoolTransport(PoolRpcAdapterErrorV1::ReturnDataMismatch),
        ));

        for (fixture, expected_error) in cases {
            let mut state = initial_state();
            let before = state.clone();
            assert_eq!(
                fixture.ingest(&mut state, &secret).err(),
                Some(expected_error)
            );
            assert_eq!(state, before);
        }
    }

    #[test]
    fn failed_pool_has_no_event_and_current_replay_requires_the_exact_event_set() {
        let root = digest(700);
        let mut failed = DepositFixture::new(
            (101, 0xa1, 100, 0xa0),
            0x71,
            7,
            root,
            history_roots(8, root),
        );
        failed.succeeded = false;
        failed.include_root_page = false;
        failed.version = SolanaRpcTransactionVersionV1::Legacy;
        failed.include_loaded_addresses = false;
        let secret = viewing_secret();
        let mut state = initial_state();

        let failed_result = failed.ingest(&mut state, &secret).unwrap();
        assert_eq!(failed_result.advance, FinalizedBlockAdvanceV1::Advanced);
        assert_eq!(failed_result.ignored_failed_pool_transactions, 1);
        assert!(failed_result.deposit_outcomes.is_empty());
        assert!(failed_result.root_evidence.is_empty());
        assert_eq!(state.next_leaf_index(), 7);

        let failed_replay = failed.ingest(&mut state, &secret).unwrap();
        assert_eq!(
            failed_replay.advance,
            FinalizedBlockAdvanceV1::AlreadyCurrent
        );
        assert_eq!(state.next_leaf_index(), 7);

        let deposit = DepositFixture::new(
            (102, 0xa2, 101, 0xa1),
            0x72,
            7,
            root,
            history_roots(8, root),
        );
        deposit.ingest(&mut state, &secret).unwrap();
        let replay = deposit.ingest(&mut state, &secret).unwrap();
        assert_eq!(replay.advance, FinalizedBlockAdvanceV1::AlreadyCurrent);
        assert!(matches!(
            replay.deposit_outcomes[0],
            DepositScanOutcomeV1::Duplicate
        ));

        let before = state.clone();
        assert_eq!(
            ingest_empty_block(&mut state, (102, 0xa2, 101, 0xa1), &secret).err(),
            Some(FinalizedIndexerErrorV1::ReplayEventSetMismatch)
        );
        assert_eq!(state, before);
    }

    #[test]
    fn retained_parent_reorg_rolls_back_deterministically_and_stale_or_unknown_forks_fail() {
        let root_a = digest(700);
        let root_b = digest(701);
        let root_b_replacement = digest(702);
        let secret = viewing_secret();
        let mut state = initial_state();

        let block_a = DepositFixture::new(
            (101, 0xa1, 100, 0xa0),
            0x71,
            7,
            root_a,
            history_roots(8, root_a),
        );
        let result_a = block_a.ingest(&mut state, &secret).unwrap();
        let event_a = result_a.root_evidence[0].event_id;

        let mut roots_b = history_roots(9, root_b);
        roots_b[8] = root_a;
        let block_b = DepositFixture::new((102, 0xa2, 101, 0xa1), 0x72, 8, root_b, roots_b);
        let result_b = block_b.ingest(&mut state, &secret).unwrap();
        let event_b = result_b.root_evidence[0].event_id;

        let mut replacement_roots = history_roots(9, root_b_replacement);
        replacement_roots[8] = root_a;
        let replacement = DepositFixture::new(
            (102, 0xb2, 101, 0xa1),
            0x73,
            8,
            root_b_replacement,
            replacement_roots,
        );
        let replacement_result = replacement.ingest(&mut state, &secret).unwrap();
        let rollback = replacement_result.rollback.unwrap();
        assert_eq!(rollback.removed_events, vec![event_b]);
        assert_eq!(rollback.head, event_a.point());
        assert_eq!(
            replacement_result.advance,
            FinalizedBlockAdvanceV1::Advanced
        );
        assert_eq!(state.next_leaf_index(), 9);
        assert_eq!(state.root(), &encode_digest_canonical(&root_b_replacement));

        // The forged transaction-global receipt claims a skipped leaf even
        // though instruction-order reconstruction starts from the retained
        // parent. Its byte mismatch rejects before the working clone commits.
        let bad_root = digest(703);
        let bad_replacement = DepositFixture::new(
            (102, 0xc2, 101, 0xa1),
            0x74,
            9,
            bad_root,
            history_roots(10, bad_root),
        );
        let before_partial_failure = state.clone();
        assert_eq!(
            bad_replacement.ingest(&mut state, &secret).err(),
            Some(FinalizedIndexerErrorV1::PoolTransport(
                PoolRpcAdapterErrorV1::ReturnDataMismatch
            ))
        );
        assert_eq!(state, before_partial_failure);

        let before_stale = state.clone();
        assert_eq!(
            block_a.ingest(&mut state, &secret).err(),
            Some(FinalizedIndexerErrorV1::StaleFinalizedBlock)
        );
        assert_eq!(state, before_stale);

        let before_unknown = state.clone();
        assert_eq!(
            ingest_empty_block(&mut state, (103, 0xb3, 99, 0x99), &secret).err(),
            Some(FinalizedIndexerErrorV1::ScanState(
                ScanStateErrorV1::NoRetainedAncestor
            ))
        );
        assert_eq!(state, before_unknown);
    }

    #[test]
    fn malformed_asdi_version_is_rejected_before_any_block_state_change() {
        let root = digest(700);
        let mut fixture = DepositFixture::new(
            (101, 0xa1, 100, 0xa0),
            0x71,
            7,
            root,
            history_roots(8, root),
        );
        fixture.instruction_version = 2;
        let mut state = initial_state();
        let before = state.clone();
        assert_eq!(
            fixture.ingest(&mut state, &viewing_secret()).err(),
            Some(FinalizedIndexerErrorV1::DepositTransport(
                DepositRpcAdapterErrorV1::DepositInstruction(
                    DepositInstructionFormatErrorV1::WrongVersion
                )
            ))
        );
        assert_eq!(state, before);
    }

    #[test]
    fn finalized_private_outputs_authenticate_intermediate_root_and_reorg_atomically() {
        let mut state = initial_state();
        let first_intermediate = digest(710);
        let first_final = digest(711);
        let first = ingest_private_transition(
            &mut state,
            (101, 0xa1, 100, 0xa0),
            0x71,
            800,
            digest(810),
            digest(820),
            first_intermediate,
            first_final,
            false,
        )
        .unwrap();
        assert_eq!(first.transition_outcomes.len(), 2);
        assert!(first
            .transition_outcomes
            .iter()
            .all(|outcome| *outcome == PublicOutputScanOutcomeV1::Advanced));
        assert_eq!(first.transition_evidence.len(), 1);
        assert_eq!(first.transition_evidence[0].receipt.nullifier, digest(800));
        assert_eq!(
            first.transition_evidence[0].output_ids,
            first
                .root_evidence
                .iter()
                .map(|evidence| evidence.event_id)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            &first.transition_evidence[0].authenticated_transport[..4],
            b"ASPT"
        );
        assert_eq!(first.root_evidence.len(), 2);
        assert_eq!(first.root_evidence[0].root_sequence, 8);
        assert_eq!(
            first.root_evidence[0].root,
            encode_digest_canonical(&first_intermediate)
        );
        assert_eq!(first.root_evidence[1].root_sequence, 9);
        assert_eq!(first.append_evidence.len(), 2);
        assert_eq!(first.append_evidence[0].leaf_index, 7);
        assert_eq!(first.append_evidence[0].root_sequence, 8);
        assert_eq!(first.append_evidence[0].note_commitment, digest_bytes(810));
        assert_eq!(first.append_evidence[1].leaf_index, 8);
        assert_eq!(first.append_evidence[1].root_sequence, 9);
        assert_eq!(first.append_evidence[1].note_commitment, digest_bytes(820));
        assert_eq!(state.next_leaf_index(), 9);
        assert_eq!(state.root(), &encode_digest_canonical(&first_final));

        let replacement_final = digest(713);
        let replacement = ingest_private_transition(
            &mut state,
            (101, 0xb1, 100, 0xa0),
            0x72,
            801,
            digest(811),
            digest(821),
            digest(712),
            replacement_final,
            false,
        )
        .unwrap();
        assert_eq!(
            replacement.rollback.as_ref().unwrap().removed_events.len(),
            2
        );
        assert_eq!(replacement.transition_evidence.len(), 1);
        assert_eq!(
            replacement.transition_evidence[0].receipt.nullifier,
            digest(801)
        );
        assert_eq!(state.next_leaf_index(), 9);
        assert_eq!(state.root(), &encode_digest_canonical(&replacement_final));

        let replay = ingest_private_transition(
            &mut state,
            (101, 0xb1, 100, 0xa0),
            0x72,
            801,
            digest(811),
            digest(821),
            digest(712),
            replacement_final,
            false,
        )
        .unwrap();
        assert!(replay
            .transition_outcomes
            .iter()
            .all(|outcome| *outcome == PublicOutputScanOutcomeV1::Duplicate));

        let mut fresh = initial_state();
        let before = fresh.clone();
        assert_eq!(
            ingest_private_transition(
                &mut fresh,
                (101, 0xc1, 100, 0xa0),
                0x73,
                802,
                digest(812),
                digest(822),
                digest(714),
                digest(715),
                true,
            )
            .err(),
            Some(FinalizedIndexerErrorV1::PoolTransport(
                PoolRpcAdapterErrorV1::ReturnDataMismatch
            ))
        );
        assert_eq!(fresh, before);
    }
}
