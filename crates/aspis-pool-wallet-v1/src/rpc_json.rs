//! Strict owned JSON-RPC plumbing for the finalized Pool V1 indexer.
//!
//! The lower [`crate::finalized_indexer`] layer deliberately accepts borrowed,
//! already-mapped RPC fields.  This module owns the corresponding production
//! boundary: it emits the exact finalized requests, rejects response-id and
//! JSON-shape drift, preserves version-0 loaded-address ordering, associates
//! root accounts with the exact requested PDA order, and invokes the existing
//! fail-closed transport/indexer.

use std::collections::BTreeSet;

use aspis_pool::pool_v1_root_page_address;
use aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES;
use serde::{de::IgnoredAny, Deserialize, Serialize};
use solana_program::pubkey::Pubkey;

use crate::{
    finalized_indexer::{
        ingest_finalized_rpc_block_v1, required_root_page_numbers_for_finalized_rpc_block_v1,
        FinalizedBlockIngestResultV1, FinalizedIndexerErrorV1, RootPageAddressBindingV1,
        SolanaRpcBlockV1, SolanaRpcCommitmentV1, SolanaRpcCompiledInstructionV1,
        SolanaRpcEncodedBinaryV1, SolanaRpcLoadedAddressesV1, SolanaRpcReturnDataV1,
        SolanaRpcRootPageAccountV1, SolanaRpcRootPageBatchV1, SolanaRpcTransactionV1,
        SolanaRpcTransactionVersionV1, SOLANA_ACCOUNT_KEY_LIMIT_V1, SOLANA_SIGNATURE_LIMIT_V1,
        SOLANA_TOP_LEVEL_INSTRUCTION_LIMIT_V1,
    },
    rpc_adapter::DepositRpcBindingV1,
    rpc_wire::decode_base58_fixed_v1,
    scan_state::{FinalizedChainPointV1, LocalOwnerKeyStoreV1, ScanStateV1},
    ViewingSecretKeyV1,
};

pub const POOL_V1_GET_BLOCK_JSON_MAX_BYTES: usize = 64 * 1024 * 1024;
pub const POOL_V1_ROOT_PAGE_JSON_MAX_BYTES_PER_ACCOUNT: usize = 16 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RpcJsonErrorV1 {
    ZeroRequestId,
    ResponseTooLarge,
    InvalidJson,
    WrongJsonRpcVersion,
    WrongResponseId,
    RpcServerError,
    MissingResult,
    SkippedBlock,
    UnexpectedBlockSignatures,
    MissingTransactionMeta,
    UnsupportedTransactionVersion,
    InvalidMessageHeader,
    InvalidRecentBlockhash,
    InvalidAddressTableLookup,
    LegacyAddressTableLookup,
    LoadedAddressCountMismatch,
    InvalidTopLevelStackHeight,
    RequestPlanMismatch,
    RootResponsePresenceMismatch,
    RootAccountCountMismatch,
    MissingRootAccount,
    EmptyRootAccount,
    WrongRootAccountSpace,
    TransactionNotFound,
    DuplicateTransaction,
    TransactionFailed,
    MissingExecutionMetadata,
    FinalizedIndexer(FinalizedIndexerErrorV1),
}

impl From<FinalizedIndexerErrorV1> for RpcJsonErrorV1 {
    fn from(error: FinalizedIndexerErrorV1) -> Self {
        Self::FinalizedIndexer(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedGetBlockRequestV1 {
    request_id: u64,
    slot: u64,
}

impl FinalizedGetBlockRequestV1 {
    pub fn new(request_id: u64, slot: u64) -> Result<Self, RpcJsonErrorV1> {
        if request_id == 0 {
            return Err(RpcJsonErrorV1::ZeroRequestId);
        }
        Ok(Self { request_id, slot })
    }

    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    pub fn slot(&self) -> u64 {
        self.slot
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        serde_json::to_vec(&GetBlockRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getBlock",
            params: (
                self.slot,
                GetBlockConfigWireV1 {
                    commitment: "finalized",
                    encoding: "json",
                    transaction_details: "full",
                    max_supported_transaction_version: 0,
                    rewards: false,
                },
            ),
        })
        .expect("fixed JSON-RPC request serialization cannot fail")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedRootPagesRequestV1 {
    request_id: u64,
    min_context_slot: u64,
    bindings: Vec<RootPageAddressBindingV1>,
}

impl FinalizedRootPagesRequestV1 {
    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    pub fn min_context_slot(&self) -> u64 {
        self.min_context_slot
    }

    pub fn bindings(&self) -> &[RootPageAddressBindingV1] {
        &self.bindings
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        let addresses: Vec<String> = self
            .bindings
            .iter()
            .map(|binding| Pubkey::new_from_array(binding.address).to_string())
            .collect();
        serde_json::to_vec(&GetMultipleAccountsRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getMultipleAccounts",
            params: (
                addresses,
                GetMultipleAccountsConfigWireV1 {
                    commitment: "finalized",
                    encoding: "base64",
                    min_context_slot: self.min_context_slot,
                },
            ),
        })
        .expect("fixed JSON-RPC request serialization cannot fail")
    }
}

#[derive(Serialize)]
struct GetBlockRequestWireV1<'a> {
    jsonrpc: &'a str,
    id: u64,
    method: &'a str,
    params: (u64, GetBlockConfigWireV1<'a>),
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct GetBlockConfigWireV1<'a> {
    commitment: &'a str,
    encoding: &'a str,
    transaction_details: &'a str,
    max_supported_transaction_version: u8,
    rewards: bool,
}

#[derive(Serialize)]
struct GetMultipleAccountsRequestWireV1<'a> {
    jsonrpc: &'a str,
    id: u64,
    method: &'a str,
    params: (Vec<String>, GetMultipleAccountsConfigWireV1<'a>),
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct GetMultipleAccountsConfigWireV1<'a> {
    commitment: &'a str,
    encoding: &'a str,
    min_context_slot: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonRpcResponseV1<T> {
    jsonrpc: String,
    id: u64,
    result: Option<T>,
    error: Option<IgnoredAny>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct GetBlockResultJsonV1 {
    blockhash: String,
    previous_blockhash: String,
    parent_slot: u64,
    transactions: Vec<BlockTransactionJsonV1>,
    #[serde(default)]
    signatures: Option<Vec<String>>,
    #[serde(default)]
    rewards: Option<Vec<IgnoredAny>>,
    #[serde(default)]
    block_time: Option<i64>,
    #[serde(default)]
    block_height: Option<u64>,
    #[serde(default)]
    num_reward_partitions: Option<u64>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BlockTransactionJsonV1 {
    transaction: TransactionJsonV1,
    meta: Option<TransactionMetaJsonV1>,
    version: serde_json::Value,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TransactionJsonV1 {
    signatures: Vec<String>,
    message: MessageJsonV1,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct MessageJsonV1 {
    header: MessageHeaderJsonV1,
    account_keys: Vec<String>,
    recent_blockhash: String,
    instructions: Vec<CompiledInstructionJsonV1>,
    #[serde(default)]
    address_table_lookups: Option<Vec<AddressTableLookupJsonV1>>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct MessageHeaderJsonV1 {
    num_required_signatures: u16,
    num_readonly_signed_accounts: u16,
    num_readonly_unsigned_accounts: u16,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AddressTableLookupJsonV1 {
    account_key: String,
    writable_indexes: Vec<u16>,
    readonly_indexes: Vec<u16>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CompiledInstructionJsonV1 {
    program_id_index: u16,
    accounts: Vec<u16>,
    data: String,
    #[serde(default)]
    stack_height: Option<u16>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TransactionMetaJsonV1 {
    err: Option<IgnoredAny>,
    #[serde(default)]
    loaded_addresses: Option<LoadedAddressesJsonV1>,
    #[serde(default)]
    return_data: Option<ReturnDataJsonV1>,
    #[serde(default)]
    fee: Option<u64>,
    #[serde(default)]
    pre_balances: Option<Vec<u64>>,
    #[serde(default)]
    post_balances: Option<Vec<u64>>,
    #[serde(default)]
    inner_instructions: Option<IgnoredAny>,
    #[serde(default)]
    log_messages: Option<IgnoredAny>,
    #[serde(default)]
    pre_token_balances: Option<IgnoredAny>,
    #[serde(default)]
    post_token_balances: Option<IgnoredAny>,
    #[serde(default)]
    rewards: Option<IgnoredAny>,
    #[serde(default)]
    status: Option<IgnoredAny>,
    #[serde(default)]
    compute_units_consumed: Option<u64>,
    #[serde(default)]
    cost_units: Option<u64>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LoadedAddressesJsonV1 {
    writable: Vec<String>,
    readonly: Vec<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReturnDataJsonV1 {
    program_id: String,
    data: (String, String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedInstructionV1 {
    program_id_index: u16,
    accounts: Vec<u16>,
    data_base58: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedLoadedAddressesV1 {
    writable: Vec<String>,
    readonly: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedReturnDataV1 {
    program_id_base58: String,
    data: String,
    encoding: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedTransactionV1 {
    version: SolanaRpcTransactionVersionV1,
    signatures: Vec<String>,
    static_account_keys: Vec<String>,
    loaded_addresses: Option<OwnedLoadedAddressesV1>,
    instructions: Vec<OwnedInstructionV1>,
    succeeded: bool,
    fee_lamports: Option<u64>,
    compute_units_consumed: Option<u64>,
    return_data: Option<OwnedReturnDataV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedBlockV1 {
    slot: u64,
    blockhash: String,
    previous_blockhash: String,
    parent_slot: u64,
    transactions: Vec<OwnedTransactionV1>,
}

struct TransactionViewBackingV1<'a> {
    transaction: &'a OwnedTransactionV1,
    signatures: Vec<&'a str>,
    static_account_keys: Vec<&'a str>,
    loaded_writable: Vec<&'a str>,
    loaded_readonly: Vec<&'a str>,
    instructions: Vec<SolanaRpcCompiledInstructionV1<'a>>,
}

impl<'a> TransactionViewBackingV1<'a> {
    fn new(transaction: &'a OwnedTransactionV1) -> Self {
        let signatures = transaction.signatures.iter().map(String::as_str).collect();
        let static_account_keys = transaction
            .static_account_keys
            .iter()
            .map(String::as_str)
            .collect();
        let (loaded_writable, loaded_readonly) = transaction.loaded_addresses.as_ref().map_or_else(
            || (Vec::new(), Vec::new()),
            |loaded| {
                (
                    loaded.writable.iter().map(String::as_str).collect(),
                    loaded.readonly.iter().map(String::as_str).collect(),
                )
            },
        );
        let instructions = transaction
            .instructions
            .iter()
            .map(|instruction| SolanaRpcCompiledInstructionV1 {
                program_id_index: instruction.program_id_index,
                account_indices: &instruction.accounts,
                data_base58: &instruction.data_base58,
            })
            .collect();
        Self {
            transaction,
            signatures,
            static_account_keys,
            loaded_writable,
            loaded_readonly,
            instructions,
        }
    }

    fn view(&self) -> SolanaRpcTransactionV1<'_> {
        SolanaRpcTransactionV1 {
            version: self.transaction.version,
            signatures_base58: &self.signatures,
            static_account_keys_base58: &self.static_account_keys,
            loaded_addresses: self.transaction.loaded_addresses.as_ref().map(|_| {
                SolanaRpcLoadedAddressesV1 {
                    writable: &self.loaded_writable,
                    readonly: &self.loaded_readonly,
                }
            }),
            top_level_instructions: &self.instructions,
            succeeded: self.transaction.succeeded,
            return_data: self.transaction.return_data.as_ref().map(|return_data| {
                SolanaRpcReturnDataV1 {
                    program_id_base58: &return_data.program_id_base58,
                    binary: SolanaRpcEncodedBinaryV1 {
                        data: &return_data.data,
                        encoding: &return_data.encoding,
                    },
                }
            }),
        }
    }
}

impl OwnedBlockV1 {
    fn with_view<R>(&self, consume: impl FnOnce(&SolanaRpcBlockV1<'_>) -> R) -> R {
        let backings: Vec<_> = self
            .transactions
            .iter()
            .map(TransactionViewBackingV1::new)
            .collect();
        let transactions: Vec<_> = backings
            .iter()
            .map(TransactionViewBackingV1::view)
            .collect();
        consume(&SolanaRpcBlockV1 {
            asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            slot: self.slot,
            blockhash_base58: &self.blockhash,
            previous_blockhash_base58: &self.previous_blockhash,
            parent_slot: self.parent_slot,
            transactions: &transactions,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedRpcJsonPlanV1 {
    block_request: FinalizedGetBlockRequestV1,
    block: OwnedBlockV1,
    root_page_bindings: Vec<RootPageAddressBindingV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedTransactionExecutionV1 {
    point: FinalizedChainPointV1,
    transaction_signature: [u8; 64],
    fee_lamports: u64,
    compute_units_consumed: u64,
}

/// Exact fee/CU/result metadata for a transaction found in an authenticated
/// finalized block. Unlike `FinalizedTransactionExecutionV1`, this record also
/// represents a transaction whose Solana execution failed, allowing the
/// relayer journal to distinguish a landed failure from blockhash expiry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedTransactionObservationV1 {
    point: FinalizedChainPointV1,
    transaction_signature: [u8; 64],
    succeeded: bool,
    fee_lamports: u64,
    compute_units_consumed: u64,
}

impl FinalizedTransactionObservationV1 {
    #[cfg(test)]
    pub(crate) fn test_only_v1(
        point: FinalizedChainPointV1,
        transaction_signature: [u8; 64],
        succeeded: bool,
        fee_lamports: u64,
        compute_units_consumed: u64,
    ) -> Self {
        assert_ne!(transaction_signature, [0u8; 64]);
        assert_ne!(fee_lamports, 0);
        assert_ne!(compute_units_consumed, 0);
        Self {
            point,
            transaction_signature,
            succeeded,
            fee_lamports,
            compute_units_consumed,
        }
    }

    pub fn point(&self) -> FinalizedChainPointV1 {
        self.point
    }

    pub fn transaction_signature(&self) -> &[u8; 64] {
        &self.transaction_signature
    }

    pub fn succeeded(&self) -> bool {
        self.succeeded
    }

    pub fn fee_lamports(&self) -> u64 {
        self.fee_lamports
    }

    pub fn compute_units_consumed(&self) -> u64 {
        self.compute_units_consumed
    }
}

impl FinalizedTransactionExecutionV1 {
    #[cfg(test)]
    pub(crate) fn test_only_v1(
        point: FinalizedChainPointV1,
        transaction_signature: [u8; 64],
        fee_lamports: u64,
        compute_units_consumed: u64,
    ) -> Self {
        assert_ne!(transaction_signature, [0u8; 64]);
        assert_ne!(fee_lamports, 0);
        assert_ne!(compute_units_consumed, 0);
        Self {
            point,
            transaction_signature,
            fee_lamports,
            compute_units_consumed,
        }
    }

    pub fn point(&self) -> FinalizedChainPointV1 {
        self.point
    }

    pub fn transaction_signature(&self) -> &[u8; 64] {
        &self.transaction_signature
    }

    pub fn fee_lamports(&self) -> u64 {
        self.fee_lamports
    }

    pub fn compute_units_consumed(&self) -> u64 {
        self.compute_units_consumed
    }
}

impl FinalizedRpcJsonPlanV1 {
    pub fn block_request(&self) -> FinalizedGetBlockRequestV1 {
        self.block_request
    }

    pub fn root_page_bindings(&self) -> &[RootPageAddressBindingV1] {
        &self.root_page_bindings
    }

    /// Return fee/CU evidence only from the exact successful finalized block
    /// transaction whose primary signature matches `transaction_signature`.
    /// A status response alone is deliberately insufficient for this record.
    pub fn transaction_execution_v1(
        &self,
        transaction_signature: [u8; 64],
    ) -> Result<FinalizedTransactionExecutionV1, RpcJsonErrorV1> {
        let observation = self.transaction_observation_v1(transaction_signature)?;
        if !observation.succeeded {
            return Err(RpcJsonErrorV1::TransactionFailed);
        }
        Ok(FinalizedTransactionExecutionV1 {
            point: observation.point,
            transaction_signature: observation.transaction_signature,
            fee_lamports: observation.fee_lamports,
            compute_units_consumed: observation.compute_units_consumed,
        })
    }

    /// Return exact finalized block metadata for either a successful or failed
    /// execution. The transaction must occur exactly once and must carry the
    /// fee/CU metadata needed to reconcile it against the signed simulation.
    pub fn transaction_observation_v1(
        &self,
        transaction_signature: [u8; 64],
    ) -> Result<FinalizedTransactionObservationV1, RpcJsonErrorV1> {
        let mut matched = None;
        for transaction in &self.block.transactions {
            let Some(primary_signature) = transaction.signatures.first() else {
                continue;
            };
            let primary_signature = decode_base58_fixed_v1::<64>(primary_signature)
                .map_err(|_| RpcJsonErrorV1::TransactionNotFound)?;
            if primary_signature != transaction_signature {
                continue;
            }
            if matched.is_some() {
                return Err(RpcJsonErrorV1::DuplicateTransaction);
            }
            matched = Some(transaction);
        }
        let transaction = matched.ok_or(RpcJsonErrorV1::TransactionNotFound)?;
        let fee_lamports = transaction
            .fee_lamports
            .filter(|fee| *fee != 0)
            .ok_or(RpcJsonErrorV1::MissingExecutionMetadata)?;
        let compute_units_consumed = transaction
            .compute_units_consumed
            .filter(|units| *units != 0)
            .ok_or(RpcJsonErrorV1::MissingExecutionMetadata)?;
        let blockhash = decode_base58_fixed_v1::<32>(&self.block.blockhash)
            .map_err(|_| RpcJsonErrorV1::InvalidRecentBlockhash)?;
        let point = FinalizedChainPointV1::new(self.block.slot, blockhash)
            .map_err(|_| RpcJsonErrorV1::InvalidRecentBlockhash)?;
        Ok(FinalizedTransactionObservationV1 {
            point,
            transaction_signature,
            succeeded: transaction.succeeded,
            fee_lamports,
            compute_units_consumed,
        })
    }

    pub fn root_pages_request_v1(
        &self,
        request_id: u64,
    ) -> Result<Option<FinalizedRootPagesRequestV1>, RpcJsonErrorV1> {
        if self.root_page_bindings.is_empty() {
            return Ok(None);
        }
        if request_id == 0 {
            return Err(RpcJsonErrorV1::ZeroRequestId);
        }
        Ok(Some(FinalizedRootPagesRequestV1 {
            request_id,
            min_context_slot: self.block.slot,
            bindings: self.root_page_bindings.clone(),
        }))
    }
}

fn parse_response_v1<T: for<'de> Deserialize<'de>>(
    expected_request_id: u64,
    bytes: &[u8],
    max_bytes: usize,
) -> Result<T, RpcJsonErrorV1> {
    if bytes.len() > max_bytes {
        return Err(RpcJsonErrorV1::ResponseTooLarge);
    }
    let response: JsonRpcResponseV1<T> =
        serde_json::from_slice(bytes).map_err(|_| RpcJsonErrorV1::InvalidJson)?;
    if response.jsonrpc != "2.0" {
        return Err(RpcJsonErrorV1::WrongJsonRpcVersion);
    }
    if response.id != expected_request_id {
        return Err(RpcJsonErrorV1::WrongResponseId);
    }
    if response.error.is_some() {
        return Err(RpcJsonErrorV1::RpcServerError);
    }
    response.result.ok_or(RpcJsonErrorV1::MissingResult)
}

fn decode_version_v1(
    value: &serde_json::Value,
) -> Result<SolanaRpcTransactionVersionV1, RpcJsonErrorV1> {
    match value {
        serde_json::Value::String(version) if version == "legacy" => {
            Ok(SolanaRpcTransactionVersionV1::Legacy)
        }
        serde_json::Value::Number(version) if version.as_u64() == Some(0) => {
            Ok(SolanaRpcTransactionVersionV1::V0)
        }
        _ => Err(RpcJsonErrorV1::UnsupportedTransactionVersion),
    }
}

fn validate_message_v1(
    version: SolanaRpcTransactionVersionV1,
    signatures: &[String],
    message: &MessageJsonV1,
    loaded_addresses: Option<&LoadedAddressesJsonV1>,
) -> Result<(), RpcJsonErrorV1> {
    let required = usize::from(message.header.num_required_signatures);
    let readonly_signed = usize::from(message.header.num_readonly_signed_accounts);
    let readonly_unsigned = usize::from(message.header.num_readonly_unsigned_accounts);
    if required == 0
        || required != signatures.len()
        || required > message.account_keys.len()
        || readonly_signed > required
        || readonly_unsigned > message.account_keys.len().saturating_sub(required)
        || signatures.len() > SOLANA_SIGNATURE_LIMIT_V1
        || message.account_keys.len() > SOLANA_ACCOUNT_KEY_LIMIT_V1
        || message.instructions.len() > SOLANA_TOP_LEVEL_INSTRUCTION_LIMIT_V1
    {
        return Err(RpcJsonErrorV1::InvalidMessageHeader);
    }
    decode_base58_fixed_v1::<32>(&message.recent_blockhash)
        .map_err(|_| RpcJsonErrorV1::InvalidRecentBlockhash)?;
    if message
        .instructions
        .iter()
        .any(|instruction| instruction.stack_height.is_some_and(|height| height != 1))
    {
        return Err(RpcJsonErrorV1::InvalidTopLevelStackHeight);
    }

    match version {
        SolanaRpcTransactionVersionV1::Legacy => {
            if message
                .address_table_lookups
                .as_ref()
                .is_some_and(|lookups| !lookups.is_empty())
            {
                return Err(RpcJsonErrorV1::LegacyAddressTableLookup);
            }
        }
        SolanaRpcTransactionVersionV1::V0 => {
            let loaded = loaded_addresses.ok_or(RpcJsonErrorV1::LoadedAddressCountMismatch)?;
            let lookups = message.address_table_lookups.as_deref().unwrap_or_default();
            let mut writable_count = 0usize;
            let mut readonly_count = 0usize;
            for lookup in lookups {
                decode_base58_fixed_v1::<32>(&lookup.account_key)
                    .map_err(|_| RpcJsonErrorV1::InvalidAddressTableLookup)?;
                let mut indices = BTreeSet::new();
                for index in lookup
                    .writable_indexes
                    .iter()
                    .chain(&lookup.readonly_indexes)
                {
                    if *index > u16::from(u8::MAX) || !indices.insert(*index) {
                        return Err(RpcJsonErrorV1::InvalidAddressTableLookup);
                    }
                }
                writable_count = writable_count
                    .checked_add(lookup.writable_indexes.len())
                    .ok_or(RpcJsonErrorV1::LoadedAddressCountMismatch)?;
                readonly_count = readonly_count
                    .checked_add(lookup.readonly_indexes.len())
                    .ok_or(RpcJsonErrorV1::LoadedAddressCountMismatch)?;
            }
            if writable_count != loaded.writable.len() || readonly_count != loaded.readonly.len() {
                return Err(RpcJsonErrorV1::LoadedAddressCountMismatch);
            }
        }
        SolanaRpcTransactionVersionV1::Unsupported(_) => {
            return Err(RpcJsonErrorV1::UnsupportedTransactionVersion)
        }
    }
    Ok(())
}

/// Parse and authenticate the owned JSON shape, then run the existing
/// read-only transport pass to derive the exact root-page request.
pub fn plan_finalized_get_block_json_v1(
    state: &ScanStateV1,
    binding: &DepositRpcBindingV1,
    request: FinalizedGetBlockRequestV1,
    response_json: &[u8],
) -> Result<FinalizedRpcJsonPlanV1, RpcJsonErrorV1> {
    let result: GetBlockResultJsonV1 = match parse_response_v1(
        request.request_id,
        response_json,
        POOL_V1_GET_BLOCK_JSON_MAX_BYTES,
    ) {
        Err(RpcJsonErrorV1::MissingResult) => return Err(RpcJsonErrorV1::SkippedBlock),
        other => other?,
    };
    if result.signatures.is_some() {
        return Err(RpcJsonErrorV1::UnexpectedBlockSignatures);
    }
    let _ = (
        result.rewards,
        result.block_time,
        result.block_height,
        result.num_reward_partitions,
    );

    let mut transactions = Vec::with_capacity(result.transactions.len());
    for transaction in result.transactions {
        let meta = transaction
            .meta
            .ok_or(RpcJsonErrorV1::MissingTransactionMeta)?;
        let version = decode_version_v1(&transaction.version)?;
        validate_message_v1(
            version,
            &transaction.transaction.signatures,
            &transaction.transaction.message,
            meta.loaded_addresses.as_ref(),
        )?;
        let _ = (
            &meta.pre_balances,
            &meta.post_balances,
            &meta.inner_instructions,
            &meta.log_messages,
            &meta.pre_token_balances,
            &meta.post_token_balances,
            &meta.rewards,
            &meta.status,
            &meta.cost_units,
        );
        let message = transaction.transaction.message;
        let instructions = message
            .instructions
            .into_iter()
            .map(|instruction| OwnedInstructionV1 {
                program_id_index: instruction.program_id_index,
                accounts: instruction.accounts,
                data_base58: instruction.data,
            })
            .collect();
        let loaded_addresses = meta.loaded_addresses.map(|loaded| OwnedLoadedAddressesV1 {
            writable: loaded.writable,
            readonly: loaded.readonly,
        });
        let return_data = meta.return_data.map(|return_data| OwnedReturnDataV1 {
            program_id_base58: return_data.program_id,
            data: return_data.data.0,
            encoding: return_data.data.1,
        });
        transactions.push(OwnedTransactionV1 {
            version,
            signatures: transaction.transaction.signatures,
            static_account_keys: message.account_keys,
            loaded_addresses,
            instructions,
            succeeded: meta.err.is_none(),
            fee_lamports: meta.fee,
            compute_units_consumed: meta.compute_units_consumed,
            return_data,
        });
    }
    let block = OwnedBlockV1 {
        slot: request.slot,
        blockhash: result.blockhash,
        previous_blockhash: result.previous_blockhash,
        parent_slot: result.parent_slot,
        transactions,
    };
    let page_numbers = block.with_view(|view| {
        required_root_page_numbers_for_finalized_rpc_block_v1(state, binding, view)
    })?;
    let program = Pubkey::new_from_array(*binding.program_id());
    let pool = Pubkey::new_from_array(*state.identity().pool());
    let root_page_bindings = page_numbers
        .into_iter()
        .map(|page_number| RootPageAddressBindingV1 {
            page_number,
            address: pool_v1_root_page_address(&program, &pool, page_number)
                .0
                .to_bytes(),
        })
        .collect();
    Ok(FinalizedRpcJsonPlanV1 {
        block_request: request,
        block,
        root_page_bindings,
    })
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct GetMultipleAccountsResultJsonV1 {
    context: RpcContextJsonV1,
    value: Vec<Option<AccountJsonV1>>,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RpcContextJsonV1 {
    slot: u64,
    #[serde(default)]
    api_version: Option<String>,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AccountJsonV1 {
    data: (String, String),
    executable: bool,
    lamports: u64,
    owner: String,
    rent_epoch: u64,
    space: u64,
}

pub(crate) fn root_page_responses_semantically_equal_v1(
    request: &FinalizedRootPagesRequestV1,
    first_response_json: &[u8],
    second_response_json: &[u8],
) -> Result<bool, RpcJsonErrorV1> {
    let max_bytes = request
        .bindings
        .len()
        .checked_mul(POOL_V1_ROOT_PAGE_JSON_MAX_BYTES_PER_ACCOUNT)
        .and_then(|size| size.checked_add(4_096))
        .ok_or(RpcJsonErrorV1::ResponseTooLarge)?;
    let first: GetMultipleAccountsResultJsonV1 =
        parse_response_v1(request.request_id, first_response_json, max_bytes)?;
    let second: GetMultipleAccountsResultJsonV1 =
        parse_response_v1(request.request_id, second_response_json, max_bytes)?;
    Ok(first == second)
}

/// Consume the exact root-page response planned above and atomically invoke
/// the lower indexer. The lower layer still clones `ScanStateV1`, so any JSON,
/// root-page, scan or reorg failure leaves the caller's state unchanged.
pub fn ingest_finalized_rpc_json_plan_v1(
    state: &mut ScanStateV1,
    binding: &DepositRpcBindingV1,
    plan: &FinalizedRpcJsonPlanV1,
    root_request: Option<&FinalizedRootPagesRequestV1>,
    root_response_json: Option<&[u8]>,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> Result<FinalizedBlockIngestResultV1, RpcJsonErrorV1> {
    let expected_root_presence = !plan.root_page_bindings.is_empty();
    if root_request.is_some() != expected_root_presence
        || root_response_json.is_some() != expected_root_presence
    {
        return Err(RpcJsonErrorV1::RootResponsePresenceMismatch);
    }

    let mut root_accounts = Vec::new();
    let mut root_context_slot = 0u64;
    if let (Some(request), Some(response_json)) = (root_request, root_response_json) {
        if request.min_context_slot != plan.block.slot
            || request.bindings != plan.root_page_bindings
        {
            return Err(RpcJsonErrorV1::RequestPlanMismatch);
        }
        let max_bytes = request
            .bindings
            .len()
            .checked_mul(POOL_V1_ROOT_PAGE_JSON_MAX_BYTES_PER_ACCOUNT)
            .and_then(|size| size.checked_add(4_096))
            .ok_or(RpcJsonErrorV1::ResponseTooLarge)?;
        let result: GetMultipleAccountsResultJsonV1 =
            parse_response_v1(request.request_id, response_json, max_bytes)?;
        if result.value.len() != request.bindings.len() {
            return Err(RpcJsonErrorV1::RootAccountCountMismatch);
        }
        root_context_slot = result.context.slot;
        let _ = result.context.api_version;
        for (binding, account) in request.bindings.iter().zip(result.value) {
            let account = account.ok_or(RpcJsonErrorV1::MissingRootAccount)?;
            if account.lamports == 0 {
                return Err(RpcJsonErrorV1::EmptyRootAccount);
            }
            if account.space != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES as u64 {
                return Err(RpcJsonErrorV1::WrongRootAccountSpace);
            }
            let _ = account.rent_epoch;
            root_accounts.push((binding.page_number, binding.address, account));
        }
    }

    let root_address_strings: Vec<_> = root_accounts
        .iter()
        .map(|(_, address, _)| Pubkey::new_from_array(*address).to_string())
        .collect();
    let root_views: Vec<_> = root_accounts
        .iter()
        .zip(&root_address_strings)
        .map(
            |((page_number, _, account), address)| SolanaRpcRootPageAccountV1 {
                page_number: *page_number,
                address_base58: address,
                owner_base58: &account.owner,
                executable: account.executable,
                data: SolanaRpcEncodedBinaryV1 {
                    data: &account.data.0,
                    encoding: &account.data.1,
                },
            },
        )
        .collect();
    let root_batch = expected_root_presence.then_some(SolanaRpcRootPageBatchV1 {
        asserted_commitment: SolanaRpcCommitmentV1::Finalized,
        context_slot: root_context_slot,
        accounts: &root_views,
    });

    plan.block
        .with_view(|block| {
            ingest_finalized_rpc_block_v1(
                state,
                binding,
                &plan.root_page_bindings,
                block,
                root_batch.as_ref(),
                viewing_secret,
                local_keys,
            )
        })
        .map_err(RpcJsonErrorV1::FinalizedIndexer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{encode_digest_canonical, poseidon2::Digest};

    use crate::{
        derive_viewing_keypair_v1,
        scan_state::{DepositScanIdentityV1, FinalizedChainPointV1},
    };

    struct EmptyKeys;

    impl LocalOwnerKeyStoreV1 for EmptyKeys {
        fn contains_owner_key_v1(&self, _: &[u8; 32]) -> bool {
            false
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
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
        let mut output = String::new();
        output.extend(core::iter::repeat_n('1', leading_zeroes));
        output.extend(
            digits
                .iter()
                .rev()
                .map(|digit| char::from(ALPHABET[usize::from(*digit)])),
        );
        output
    }

    fn fixture() -> (ScanStateV1, DepositRpcBindingV1, ViewingSecretKeyV1) {
        let program = Pubkey::new_from_array([0x91; 32]);
        let mint = Pubkey::new_from_array([0x33; 32]);
        let pool = aspis_pool::pool_v1_state_address(&program, &mint).0;
        let vault = aspis_pool::pool_v1_vault_token_account_address(&program, &pool).0;
        let identity = DepositScanIdentityV1::new(
            pool.to_bytes(),
            [0x22; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap();
        let state = ScanStateV1::new(
            identity,
            FinalizedChainPointV1::new(100, [0xa0; 32]).unwrap(),
            7,
            encode_digest_canonical(&digest(20)),
        )
        .unwrap();
        let binding = DepositRpcBindingV1::new(program.to_bytes()).unwrap();
        let viewing = derive_viewing_keypair_v1(&[0x51; 32]).unwrap().0;
        (state, binding, viewing)
    }

    fn v0_block_response(request_id: u64, include_loaded: bool) -> Vec<u8> {
        let signature = encode_base58(&[0x55; 64]);
        let static_key = encode_base58(&[0x71; 32]);
        let recent = encode_base58(&[0x72; 32]);
        let blockhash = encode_base58(&[0xa1; 32]);
        let previous = encode_base58(&[0xa0; 32]);
        let loaded = include_loaded.then(|| {
            serde_json::json!({
                "writable": [],
                "readonly": []
            })
        });
        serde_json::to_vec(&serde_json::json!({
            "jsonrpc": "2.0",
            "id": request_id,
            "result": {
                "blockhash": blockhash,
                "previousBlockhash": previous,
                "parentSlot": 100,
                "transactions": [{
                    "transaction": {
                        "signatures": [signature],
                        "message": {
                            "header": {
                                "numRequiredSignatures": 1,
                                "numReadonlySignedAccounts": 0,
                                "numReadonlyUnsignedAccounts": 0
                            },
                            "accountKeys": [static_key],
                            "recentBlockhash": recent,
                            "instructions": [],
                            "addressTableLookups": []
                        }
                    },
                    "meta": {
                        "err": null,
                        "loadedAddresses": loaded,
                        "fee": 5_000,
                        "computeUnitsConsumed": 777
                    },
                    "version": 0
                }],
                "rewards": []
            }
        }))
        .unwrap()
    }

    #[test]
    fn canonical_requests_and_v0_owned_ingestion_survive_restart_boundary() {
        let (mut state, binding, viewing) = fixture();
        let request = FinalizedGetBlockRequestV1::new(41, 101).unwrap();
        let request_value: serde_json::Value =
            serde_json::from_slice(&request.encode_json_v1()).unwrap();
        assert_eq!(request_value["params"][1]["commitment"], "finalized");
        assert_eq!(
            request_value["params"][1]["maxSupportedTransactionVersion"],
            0
        );
        assert_eq!(request_value["params"][1]["rewards"], false);

        let plan = plan_finalized_get_block_json_v1(
            &state,
            &binding,
            request,
            &v0_block_response(41, true),
        )
        .unwrap();
        assert!(plan.root_page_bindings().is_empty());
        let execution = plan.transaction_execution_v1([0x55; 64]).unwrap();
        assert_eq!(execution.point().slot(), 101);
        assert_eq!(execution.point().block_hash(), &[0xa1; 32]);
        assert_eq!(execution.transaction_signature(), &[0x55; 64]);
        assert_eq!(execution.fee_lamports(), 5_000);
        assert_eq!(execution.compute_units_consumed(), 777);
        let result = ingest_finalized_rpc_json_plan_v1(
            &mut state, &binding, &plan, None, None, &viewing, &EmptyKeys,
        )
        .unwrap();
        assert_eq!(
            result.advance,
            crate::scan_state::FinalizedBlockAdvanceV1::Advanced
        );
        assert_eq!(state.head().slot(), 101);
    }

    #[test]
    fn finalized_execution_requires_exact_success_fee_and_compute_metadata() {
        let (state, binding, _) = fixture();
        let request = FinalizedGetBlockRequestV1::new(41, 101).unwrap();
        let mut response: serde_json::Value =
            serde_json::from_slice(&v0_block_response(41, true)).unwrap();
        response["result"]["transactions"][0]["meta"]
            .as_object_mut()
            .unwrap()
            .remove("computeUnitsConsumed");
        let plan = plan_finalized_get_block_json_v1(
            &state,
            &binding,
            request,
            &serde_json::to_vec(&response).unwrap(),
        )
        .unwrap();
        assert_eq!(
            plan.transaction_execution_v1([0x55; 64]),
            Err(RpcJsonErrorV1::MissingExecutionMetadata)
        );
        assert_eq!(
            plan.transaction_execution_v1([0x56; 64]),
            Err(RpcJsonErrorV1::TransactionNotFound)
        );

        let mut failed_response: serde_json::Value =
            serde_json::from_slice(&v0_block_response(41, true)).unwrap();
        failed_response["result"]["transactions"][0]["meta"]["err"] =
            serde_json::json!({"InstructionError": [2, {"Custom": 0x1771}]});
        let failed_plan = plan_finalized_get_block_json_v1(
            &state,
            &binding,
            request,
            &serde_json::to_vec(&failed_response).unwrap(),
        )
        .unwrap();
        let failed = failed_plan.transaction_observation_v1([0x55; 64]).unwrap();
        assert!(!failed.succeeded());
        assert_eq!(failed.point().slot(), 101);
        assert_eq!(failed.transaction_signature(), &[0x55; 64]);
        assert_eq!(failed.fee_lamports(), 5_000);
        assert_eq!(failed.compute_units_consumed(), 777);
        assert_eq!(
            failed_plan.transaction_execution_v1([0x55; 64]),
            Err(RpcJsonErrorV1::TransactionFailed)
        );
    }

    #[test]
    fn malformed_or_mismatched_json_fails_before_state_mutation() {
        let (mut state, binding, viewing) = fixture();
        let original = state.clone();
        let request = FinalizedGetBlockRequestV1::new(41, 101).unwrap();
        assert_eq!(
            plan_finalized_get_block_json_v1(
                &state,
                &binding,
                request,
                &v0_block_response(42, true),
            )
            .err(),
            Some(RpcJsonErrorV1::WrongResponseId)
        );
        assert!(matches!(
            plan_finalized_get_block_json_v1(
                &state,
                &binding,
                request,
                &v0_block_response(41, false),
            ),
            Err(RpcJsonErrorV1::LoadedAddressCountMismatch) | Err(RpcJsonErrorV1::InvalidJson)
        ));
        let duplicate = br#"{"jsonrpc":"2.0","id":41,"result":{"blockhash":"x","blockhash":"y","previousBlockhash":"z","parentSlot":100,"transactions":[]}}"#;
        assert_eq!(
            plan_finalized_get_block_json_v1(&state, &binding, request, duplicate).err(),
            Some(RpcJsonErrorV1::InvalidJson)
        );
        assert_eq!(state, original);

        let plan = plan_finalized_get_block_json_v1(
            &state,
            &binding,
            request,
            &v0_block_response(41, true),
        )
        .unwrap();
        assert_eq!(
            ingest_finalized_rpc_json_plan_v1(
                &mut state,
                &binding,
                &plan,
                Some(&FinalizedRootPagesRequestV1 {
                    request_id: 99,
                    min_context_slot: 101,
                    bindings: Vec::new(),
                }),
                Some(br#"{}"#),
                &viewing,
                &EmptyKeys,
            )
            .err(),
            Some(RpcJsonErrorV1::RootResponsePresenceMismatch)
        );
        assert_eq!(state, original);
    }

    #[test]
    fn root_page_semantic_agreement_ignores_json_formatting_but_not_account_state() {
        let request = FinalizedRootPagesRequestV1 {
            request_id: 77,
            min_context_slot: 101,
            bindings: vec![RootPageAddressBindingV1 {
                page_number: 0,
                address: [0x31; 32],
            }],
        };
        let response = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 77,
            "result": {
                "context": {"slot": 101},
                "value": [{
                    "data": ["AA==", "base64"],
                    "executable": false,
                    "lamports": 1,
                    "owner": encode_base58(&[0x41; 32]),
                    "rentEpoch": 2,
                    "space": 1
                }]
            }
        });
        let compact = serde_json::to_vec(&response).unwrap();
        let pretty = serde_json::to_vec_pretty(&response).unwrap();
        assert_eq!(
            root_page_responses_semantically_equal_v1(&request, &compact, &pretty),
            Ok(true)
        );

        let mut changed = response;
        changed["result"]["value"][0]["lamports"] = serde_json::json!(2);
        assert_eq!(
            root_page_responses_semantically_equal_v1(
                &request,
                &compact,
                &serde_json::to_vec(&changed).unwrap(),
            ),
            Ok(false)
        );
    }
}
