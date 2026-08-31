//! Owned, finalized two-provider RPC boundary for 4 KiB Solana TxV1 Pool
//! terminals.
//!
//! The older finalized indexer consumes JSON-expanded legacy/V0 messages and
//! inherits their 1,232-byte ceiling. This default-off V2 boundary requests
//! canonical base64 transaction wires, decodes legacy/V0/V1 only to preserve
//! exact block order, and emits Pool terminals only from literal TxV1 messages.
//! The transaction-array index is retained separately from the stable
//! signature-based event ID and is committed into ASL2 by the terminal intent
//! builder.

use std::collections::BTreeSet;

use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_terminal_request_v1, decode_pool_v1_pair_forest_terminal_result_v1,
    root_history::{read_root_history_page_root_v1, validate_root_history_page_bytes_v1},
    root_history_location, POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC,
    POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use serde::{de::IgnoredAny, Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use solana_message_v1::VersionedMessage as V1VersionedMessage;
use solana_transaction_v1::versioned::VersionedTransaction as V1VersionedTransaction;

use crate::{
    finalized_indexer::SolanaRpcCommitmentV1,
    lane_forest_durable_v2::canonical_lane_root_page_cursor_v2,
    lane_forest_rpc_v2::{
        FinalizedForestAccountV2, FinalizedForestRootPageV2,
        FinalizedPairForestTerminalObservationV2,
    },
    lane_forest_transaction_v1::{
        SOLANA_LEGACY_V0_TRANSACTION_MAX_BYTES_V2, SOLANA_V1_TRANSACTION_MAX_BYTES_V2,
    },
    lane_forest_v2::LaneIdV2,
    relayer_rpc_quorum::{ExactProviderRpcExchangeV1, ExactTwoProviderRelayerRpcV1},
    rpc_wire::decode_base58_fixed_v1,
    scan_state::{DepositEventIdV1, FinalizedBlockV1, FinalizedChainPointV1},
};

pub const FINALIZED_TX_V1_GET_BLOCK_JSON_MAX_BYTES_V2: usize = 64 * 1024 * 1024;
pub const FINALIZED_TX_V1_ROOT_PAGE_JSON_MAX_BYTES_V2: usize = 16 * 1024;
const FINALIZED_TX_V1_REQUEST_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:tx-v1-finalized-rpc-request:sha256:v2";
const FINALIZED_TX_V1_TERMINAL_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:tx-v1-finalized-terminal:sha256:v2";
const GET_BLOCK_ENDPOINT_V2: u8 = 1;
const ROOT_PAGE_ENDPOINT_V2: u8 = 2;
const MAX_RETURN_DATA_BYTES_V2: usize = 1_024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizedTxV1RpcErrorV2 {
    ZeroRequestId,
    ZeroProgram,
    BlockBeforeStartupCheckpoint,
    ResponseTooLarge,
    InvalidJson,
    WrongJsonRpcVersion,
    WrongResponseId,
    RpcServerError,
    MissingResult,
    SkippedBlock,
    WrongProviderOrder { provider_index: u8 },
    WrongRequestBytes { provider_index: u8 },
    ProviderResponse { provider_index: u8 },
    ProviderDisagreement,
    InvalidChainPoint,
    MissingTransactionMeta,
    UnsupportedTransactionVersion,
    TransactionVersionMismatch,
    InvalidTransactionEncoding,
    TransactionTooLarge,
    NonCanonicalTransaction,
    InvalidTransaction,
    DuplicateTransaction,
    InvalidReturnData,
    TerminalNotTxV1,
    InvalidTerminal,
    WrongTerminalPosition,
    TerminalOrder,
    WrongProgram,
    InvalidEventId,
    InvalidRootRequest,
    RootContextTooOld,
    MissingRootAccount,
    WrongRootOwner,
    WrongRootSpace,
    WrongRootPage,
    RootBindingMismatch,
    LengthOverflow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedTxV1GetBlockRequestV2 {
    request_id: u64,
    slot: u64,
}

impl FinalizedTxV1GetBlockRequestV2 {
    pub fn new_v2(request_id: u64, slot: u64) -> Result<Self, FinalizedTxV1RpcErrorV2> {
        if request_id == 0 {
            return Err(FinalizedTxV1RpcErrorV2::ZeroRequestId);
        }
        Ok(Self { request_id, slot })
    }

    pub fn request_id_v2(self) -> u64 {
        self.request_id
    }

    pub fn slot_v2(self) -> u64 {
        self.slot
    }

    pub fn encode_json_v2(self) -> Vec<u8> {
        serde_json::to_vec(&GetBlockRequestWireV2 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getBlock",
            params: (
                self.slot,
                GetBlockConfigWireV2 {
                    commitment: "finalized",
                    encoding: "base64",
                    transaction_details: "full",
                    max_supported_transaction_version: 1,
                    rewards: false,
                },
            ),
        })
        .expect("fixed finalized TxV1 request serialization cannot fail")
    }
}

#[derive(Serialize)]
struct GetBlockRequestWireV2<'a> {
    jsonrpc: &'a str,
    id: u64,
    method: &'a str,
    params: (u64, GetBlockConfigWireV2<'a>),
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct GetBlockConfigWireV2<'a> {
    commitment: &'a str,
    encoding: &'a str,
    transaction_details: &'a str,
    max_supported_transaction_version: u8,
    rewards: bool,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonRpcResponseV2<T> {
    jsonrpc: String,
    id: u64,
    result: Option<T>,
    error: Option<IgnoredAny>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct GetBlockResultJsonV2 {
    blockhash: String,
    previous_blockhash: String,
    parent_slot: u64,
    transactions: Vec<BlockTransactionJsonV2>,
    #[serde(default)]
    signatures: Option<Vec<String>>,
    #[serde(default)]
    #[serde(rename = "rewards")]
    _rewards: Option<Vec<IgnoredAny>>,
    #[serde(default)]
    #[serde(rename = "blockTime")]
    _block_time: Option<i64>,
    #[serde(default)]
    #[serde(rename = "blockHeight")]
    _block_height: Option<u64>,
    #[serde(default)]
    #[serde(rename = "numRewardPartitions")]
    _num_reward_partitions: Option<u64>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BlockTransactionJsonV2 {
    transaction: (String, String),
    meta: Option<TransactionMetaJsonV2>,
    version: serde_json::Value,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TransactionMetaJsonV2 {
    err: serde_json::Value,
    #[serde(default)]
    loaded_addresses: Option<LoadedAddressesJsonV2>,
    #[serde(default)]
    return_data: Option<ReturnDataJsonV2>,
    #[serde(default)]
    #[serde(rename = "fee")]
    _fee: Option<u64>,
    #[serde(default)]
    #[serde(rename = "preBalances")]
    _pre_balances: Option<Vec<u64>>,
    #[serde(default)]
    #[serde(rename = "postBalances")]
    _post_balances: Option<Vec<u64>>,
    #[serde(default)]
    #[serde(rename = "innerInstructions")]
    _inner_instructions: Option<IgnoredAny>,
    #[serde(default)]
    #[serde(rename = "logMessages")]
    _log_messages: Option<IgnoredAny>,
    #[serde(default)]
    #[serde(rename = "preTokenBalances")]
    _pre_token_balances: Option<IgnoredAny>,
    #[serde(default)]
    #[serde(rename = "postTokenBalances")]
    _post_token_balances: Option<IgnoredAny>,
    #[serde(default)]
    #[serde(rename = "rewards")]
    _rewards: Option<IgnoredAny>,
    #[serde(default)]
    #[serde(rename = "status")]
    _status: Option<IgnoredAny>,
    #[serde(default)]
    #[serde(rename = "computeUnitsConsumed")]
    _compute_units_consumed: Option<u64>,
    #[serde(default)]
    #[serde(rename = "costUnits")]
    _cost_units: Option<u64>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct LoadedAddressesJsonV2 {
    writable: Vec<String>,
    readonly: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReturnDataJsonV2 {
    program_id: String,
    data: (String, String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DecodedTransactionVersionV2 {
    Legacy,
    V0,
    V1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedReturnDataV2 {
    program_id: [u8; 32],
    data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedBlockTransactionV2 {
    version: DecodedTransactionVersionV2,
    wire: Vec<u8>,
    primary_signature: [u8; 64],
    succeeded: bool,
    return_data: Option<OwnedReturnDataV2>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedFinalizedTxV1BlockV2 {
    block: FinalizedBlockV1,
    transactions: Vec<OwnedBlockTransactionV2>,
    terminals: Vec<OwnedFinalizedTxV1TerminalV2>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedFinalizedTxV1TerminalV2 {
    transaction_index: u32,
    transaction_signature: [u8; 64],
    instruction_index: u16,
    top_level_instruction_count: u16,
    instruction_program: [u8; 32],
    instruction_bytes: Vec<u8>,
    return_data_program: [u8; 32],
    return_data: Vec<u8>,
    event_id: DepositEventIdV1,
    binding_sha256: [u8; 32],
}

/// Constructor-sealed finalized block decoded independently by both pinned
/// providers. The terminal vector preserves the exact `transactions` array
/// order; event identity remains `(point, signature, instruction, output)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgreedFinalizedTxV1BlockV2 {
    provider_ids: [[u8; 32]; 2],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    startup_checkpoint_slot: u64,
    request_binding_sha256: [u8; 32],
    block: OwnedFinalizedTxV1BlockV2,
}

impl AgreedFinalizedTxV1BlockV2 {
    pub fn block_v2(&self) -> FinalizedBlockV1 {
        self.block.block
    }

    pub fn terminal_count_v2(&self) -> usize {
        self.block.terminals.len()
    }

    pub fn terminal_event_id_v2(&self, terminal_index: usize) -> Option<DepositEventIdV1> {
        self.block
            .terminals
            .get(terminal_index)
            .map(|terminal| terminal.event_id)
    }

    pub fn terminal_transaction_index_v2(&self, terminal_index: usize) -> Option<u32> {
        self.block
            .terminals
            .get(terminal_index)
            .map(|terminal| terminal.transaction_index)
    }

    pub fn provider_set_digest_v2(&self) -> &[u8; 32] {
        &self.provider_set_digest
    }

    pub fn startup_receipt_digest_v2(&self) -> &[u8; 32] {
        &self.startup_receipt_digest
    }

    pub fn request_binding_sha256_v2(&self) -> &[u8; 32] {
        &self.request_binding_sha256
    }

    pub(crate) fn validate_terminal_progress_v2(
        &self,
        terminal_index: usize,
        previous_transaction_index: Option<u32>,
    ) -> Result<(), FinalizedTxV1RpcErrorV2> {
        if self.block.terminals.get(terminal_index).is_none() {
            return Err(FinalizedTxV1RpcErrorV2::TerminalOrder);
        }
        let maximum_allowed = match previous_transaction_index {
            None => 0,
            Some(previous) => self
                .block
                .terminals
                .iter()
                .position(|terminal| terminal.transaction_index == previous)
                .and_then(|ordinal| ordinal.checked_add(1))
                .ok_or(FinalizedTxV1RpcErrorV2::TerminalOrder)?,
        };
        // Any already-consumed ordinal is an admissible exact replay; the
        // ASL2 content digest rejects a different event at that ordinal. New
        // progress must be exactly the next terminal, never a later one.
        if terminal_index > maximum_allowed {
            return Err(FinalizedTxV1RpcErrorV2::TerminalOrder);
        }
        Ok(())
    }

    pub fn root_page_request_v2(
        &self,
        request_id: u64,
        terminal_index: usize,
        pool_program: [u8; 32],
        master: [u8; 32],
    ) -> Result<FinalizedTxV1RootPageRequestV2, FinalizedTxV1RpcErrorV2> {
        if request_id == 0 {
            return Err(FinalizedTxV1RpcErrorV2::ZeroRequestId);
        }
        if pool_program == [0u8; 32] || master == [0u8; 32] {
            return Err(FinalizedTxV1RpcErrorV2::ZeroProgram);
        }
        let terminal = self
            .block
            .terminals
            .get(terminal_index)
            .ok_or(FinalizedTxV1RpcErrorV2::InvalidRootRequest)?;
        if terminal.instruction_program != pool_program {
            return Err(FinalizedTxV1RpcErrorV2::WrongProgram);
        }
        let result = decode_pool_v1_pair_forest_terminal_result_v1(&terminal.return_data)
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTerminal)?;
        if result.master_account != master {
            return Err(FinalizedTxV1RpcErrorV2::InvalidRootRequest);
        }
        let lane_id = LaneIdV2::new(result.output_lane)
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidRootRequest)?;
        let expected_lane = aspis_pool::pool_v1_pair_forest_lane_address(
            &solana_program::pubkey::Pubkey::new_from_array(pool_program),
            &solana_program::pubkey::Pubkey::new_from_array(master),
            lane_id.as_u8(),
        )
        .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidRootRequest)?
        .0
        .to_bytes();
        if result.selected_lane_account != expected_lane {
            return Err(FinalizedTxV1RpcErrorV2::InvalidRootRequest);
        }
        let cursor = canonical_lane_root_page_cursor_v2(
            pool_program,
            master,
            lane_id,
            result.verified_afterstate.next_pair_index,
        )
        .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidRootRequest)?;
        Ok(FinalizedTxV1RootPageRequestV2 {
            request_id,
            min_context_slot: self.block.block.point().slot(),
            pool_program,
            master,
            lane_id,
            lane_account: result.selected_lane_account,
            root_sequence: result.verified_afterstate.next_pair_index,
            expected_root: aspis_statement::encode_digest_canonical(
                &result.verified_afterstate.next_root,
            ),
            page_number: cursor.page_number,
            address: cursor.address,
            terminal_binding_sha256: terminal.binding_sha256,
            provider_ids: self.provider_ids,
            provider_set_digest: self.provider_set_digest,
            startup_receipt_digest: self.startup_receipt_digest,
        })
    }

    pub fn terminal_observation_v2(
        &self,
        terminal_index: usize,
        root_page: &AgreedFinalizedTxV1RootPageV2,
    ) -> Result<FinalizedPairForestTerminalObservationV2, FinalizedTxV1RpcErrorV2> {
        let terminal = self
            .block
            .terminals
            .get(terminal_index)
            .ok_or(FinalizedTxV1RpcErrorV2::RootBindingMismatch)?;
        if root_page.terminal_binding_sha256 != terminal.binding_sha256
            || root_page.provider_ids != self.provider_ids
            || root_page.provider_set_digest != self.provider_set_digest
            || root_page.startup_receipt_digest != self.startup_receipt_digest
            || root_page.context_slot < self.block.block.point().slot()
        {
            return Err(FinalizedTxV1RpcErrorV2::RootBindingMismatch);
        }
        Ok(FinalizedPairForestTerminalObservationV2 {
            asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            accounts_asserted_commitment: SolanaRpcCommitmentV1::Finalized,
            block: self.block.block,
            account_context_slot: root_page.context_slot,
            transaction_index: terminal.transaction_index,
            transaction_signature: terminal.transaction_signature,
            transaction_succeeded: true,
            instruction_index: terminal.instruction_index,
            top_level_instruction_count: terminal.top_level_instruction_count,
            instruction_program: terminal.instruction_program,
            instruction_bytes: terminal.instruction_bytes.clone(),
            return_data_program: terminal.return_data_program,
            return_data: terminal.return_data.clone(),
            root_page: root_page.root_page.clone(),
        })
    }
}

fn parse_response_v2<T: for<'de> Deserialize<'de>>(
    expected_request_id: u64,
    bytes: &[u8],
    max_bytes: usize,
) -> Result<Option<T>, FinalizedTxV1RpcErrorV2> {
    if bytes.len() > max_bytes {
        return Err(FinalizedTxV1RpcErrorV2::ResponseTooLarge);
    }
    let response: JsonRpcResponseV2<T> =
        serde_json::from_slice(bytes).map_err(|_| FinalizedTxV1RpcErrorV2::InvalidJson)?;
    if response.jsonrpc != "2.0" {
        return Err(FinalizedTxV1RpcErrorV2::WrongJsonRpcVersion);
    }
    if response.id != expected_request_id {
        return Err(FinalizedTxV1RpcErrorV2::WrongResponseId);
    }
    if response.error.is_some() {
        return Err(FinalizedTxV1RpcErrorV2::RpcServerError);
    }
    Ok(response.result)
}

fn json_transaction_version_v2(
    value: &serde_json::Value,
) -> Result<DecodedTransactionVersionV2, FinalizedTxV1RpcErrorV2> {
    match value {
        serde_json::Value::String(value) if value == "legacy" => {
            Ok(DecodedTransactionVersionV2::Legacy)
        }
        serde_json::Value::Number(value) if value.as_u64() == Some(0) => {
            Ok(DecodedTransactionVersionV2::V0)
        }
        serde_json::Value::Number(value) if value.as_u64() == Some(1) => {
            Ok(DecodedTransactionVersionV2::V1)
        }
        _ => Err(FinalizedTxV1RpcErrorV2::UnsupportedTransactionVersion),
    }
}

fn decoded_transaction_version_v2(message: &V1VersionedMessage) -> DecodedTransactionVersionV2 {
    match message {
        V1VersionedMessage::Legacy(_) => DecodedTransactionVersionV2::Legacy,
        V1VersionedMessage::V0(_) => DecodedTransactionVersionV2::V0,
        V1VersionedMessage::V1(_) => DecodedTransactionVersionV2::V1,
    }
}

fn decode_return_data_v2(
    value: Option<ReturnDataJsonV2>,
) -> Result<Option<OwnedReturnDataV2>, FinalizedTxV1RpcErrorV2> {
    value
        .map(|value| {
            if value.data.1 != "base64" {
                return Err(FinalizedTxV1RpcErrorV2::InvalidReturnData);
            }
            let data = BASE64_STANDARD
                .decode(value.data.0)
                .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidReturnData)?;
            if data.len() > MAX_RETURN_DATA_BYTES_V2 {
                return Err(FinalizedTxV1RpcErrorV2::InvalidReturnData);
            }
            Ok(OwnedReturnDataV2 {
                program_id: decode_base58_fixed_v1::<32>(&value.program_id)
                    .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidReturnData)?,
                data,
            })
        })
        .transpose()
}

fn terminal_binding_v2(
    block: FinalizedBlockV1,
    transaction_index: u32,
    signature: [u8; 64],
    instruction_index: u16,
    instruction: &[u8],
    return_data: &[u8],
) -> Result<[u8; 32], FinalizedTxV1RpcErrorV2> {
    let instruction_length =
        u64::try_from(instruction.len()).map_err(|_| FinalizedTxV1RpcErrorV2::LengthOverflow)?;
    let return_length =
        u64::try_from(return_data.len()).map_err(|_| FinalizedTxV1RpcErrorV2::LengthOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(FINALIZED_TX_V1_TERMINAL_DOMAIN_V2);
    hasher.update(block.point().slot().to_le_bytes());
    hasher.update(block.point().block_hash());
    hasher.update(transaction_index.to_le_bytes());
    hasher.update(signature);
    hasher.update(instruction_index.to_le_bytes());
    hasher.update(instruction_length.to_le_bytes());
    hasher.update(instruction);
    hasher.update(return_length.to_le_bytes());
    hasher.update(return_data);
    Ok(hasher.finalize().into())
}

fn parse_finalized_tx_v1_block_v2(
    request: FinalizedTxV1GetBlockRequestV2,
    pool_program: [u8; 32],
    response_json: &[u8],
) -> Result<OwnedFinalizedTxV1BlockV2, FinalizedTxV1RpcErrorV2> {
    let result: GetBlockResultJsonV2 = parse_response_v2(
        request.request_id,
        response_json,
        FINALIZED_TX_V1_GET_BLOCK_JSON_MAX_BYTES_V2,
    )?
    .ok_or(FinalizedTxV1RpcErrorV2::SkippedBlock)?;
    if result.signatures.is_some() {
        return Err(FinalizedTxV1RpcErrorV2::InvalidJson);
    }
    let point = FinalizedChainPointV1::new(
        request.slot,
        decode_base58_fixed_v1::<32>(&result.blockhash)
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidChainPoint)?,
    )
    .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidChainPoint)?;
    let parent = FinalizedChainPointV1::new(
        result.parent_slot,
        decode_base58_fixed_v1::<32>(&result.previous_blockhash)
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidChainPoint)?,
    )
    .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidChainPoint)?;
    let block = FinalizedBlockV1::new(point, parent)
        .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidChainPoint)?;
    let mut signatures = BTreeSet::new();
    let mut transactions = Vec::with_capacity(result.transactions.len());
    let mut terminals = Vec::new();
    for (transaction_index, transaction_json) in result.transactions.into_iter().enumerate() {
        let transaction_index = u32::try_from(transaction_index)
            .map_err(|_| FinalizedTxV1RpcErrorV2::LengthOverflow)?;
        let meta = transaction_json
            .meta
            .ok_or(FinalizedTxV1RpcErrorV2::MissingTransactionMeta)?;
        if transaction_json.transaction.1 != "base64" {
            return Err(FinalizedTxV1RpcErrorV2::InvalidTransactionEncoding);
        }
        let wire = BASE64_STANDARD
            .decode(transaction_json.transaction.0)
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTransactionEncoding)?;
        if wire.len() > SOLANA_V1_TRANSACTION_MAX_BYTES_V2 {
            return Err(FinalizedTxV1RpcErrorV2::TransactionTooLarge);
        }
        let transaction: V1VersionedTransaction =
            wincode::deserialize(&wire).map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTransaction)?;
        transaction
            .sanitize()
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTransaction)?;
        let version = decoded_transaction_version_v2(&transaction.message);
        if version != json_transaction_version_v2(&transaction_json.version)? {
            return Err(FinalizedTxV1RpcErrorV2::TransactionVersionMismatch);
        }
        let wire_limit = if version == DecodedTransactionVersionV2::V1 {
            SOLANA_V1_TRANSACTION_MAX_BYTES_V2
        } else {
            SOLANA_LEGACY_V0_TRANSACTION_MAX_BYTES_V2
        };
        if wire.len() > wire_limit {
            return Err(FinalizedTxV1RpcErrorV2::TransactionTooLarge);
        }
        if wincode::serialize(&transaction)
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTransaction)?
            != wire
        {
            return Err(FinalizedTxV1RpcErrorV2::NonCanonicalTransaction);
        }
        let primary_signature = transaction
            .signatures
            .first()
            .map(|signature| *signature.as_array())
            .ok_or(FinalizedTxV1RpcErrorV2::InvalidTransaction)?;
        if primary_signature == [0u8; 64] || !signatures.insert(primary_signature) {
            return Err(FinalizedTxV1RpcErrorV2::DuplicateTransaction);
        }
        if version == DecodedTransactionVersionV2::V1
            && meta
                .loaded_addresses
                .as_ref()
                .is_some_and(|loaded| !loaded.writable.is_empty() || !loaded.readonly.is_empty())
        {
            return Err(FinalizedTxV1RpcErrorV2::TransactionVersionMismatch);
        }
        let succeeded = meta.err.is_null();
        let return_data = decode_return_data_v2(meta.return_data)?;
        let account_keys = transaction.message.static_account_keys();
        let instructions = transaction.message.instructions();
        let top_level_instruction_count = u16::try_from(instructions.len())
            .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTransaction)?;
        for (instruction_index, instruction) in instructions.iter().enumerate() {
            let Some(program) = account_keys.get(usize::from(instruction.program_id_index)) else {
                return Err(FinalizedTxV1RpcErrorV2::InvalidTransaction);
            };
            if program.to_bytes() == pool_program
                && instruction
                    .data
                    .starts_with(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC)
            {
                if version != DecodedTransactionVersionV2::V1 {
                    return Err(FinalizedTxV1RpcErrorV2::TerminalNotTxV1);
                }
                if instruction_index + 1 != instructions.len() {
                    return Err(FinalizedTxV1RpcErrorV2::WrongTerminalPosition);
                }
                decode_pool_v1_pair_forest_terminal_request_v1(&instruction.data)
                    .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTerminal)?;
                if succeeded {
                    let return_data = return_data
                        .as_ref()
                        .ok_or(FinalizedTxV1RpcErrorV2::InvalidReturnData)?;
                    if return_data.program_id != pool_program {
                        return Err(FinalizedTxV1RpcErrorV2::WrongProgram);
                    }
                    decode_pool_v1_pair_forest_terminal_result_v1(&return_data.data)
                        .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTerminal)?;
                    let instruction_index = u16::try_from(instruction_index)
                        .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidTransaction)?;
                    let event_id = DepositEventIdV1::new(
                        block.point(),
                        primary_signature,
                        instruction_index,
                        0,
                    )
                    .map_err(|_| FinalizedTxV1RpcErrorV2::InvalidEventId)?;
                    terminals.push(OwnedFinalizedTxV1TerminalV2 {
                        transaction_index,
                        transaction_signature: primary_signature,
                        instruction_index,
                        top_level_instruction_count,
                        instruction_program: pool_program,
                        instruction_bytes: instruction.data.clone(),
                        return_data_program: return_data.program_id,
                        return_data: return_data.data.clone(),
                        event_id,
                        binding_sha256: terminal_binding_v2(
                            block,
                            transaction_index,
                            primary_signature,
                            instruction_index,
                            &instruction.data,
                            &return_data.data,
                        )?,
                    });
                }
            }
        }
        transactions.push(OwnedBlockTransactionV2 {
            version,
            wire,
            primary_signature,
            succeeded,
            return_data,
        });
    }
    Ok(OwnedFinalizedTxV1BlockV2 {
        block,
        transactions,
        terminals,
    })
}

fn request_binding_v2(
    endpoint: u8,
    request_id: u64,
    context_slot: u64,
    request_json: &[u8],
) -> Result<[u8; 32], FinalizedTxV1RpcErrorV2> {
    let length =
        u64::try_from(request_json.len()).map_err(|_| FinalizedTxV1RpcErrorV2::LengthOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(FINALIZED_TX_V1_REQUEST_DOMAIN_V2);
    hasher.update([endpoint]);
    hasher.update(request_id.to_le_bytes());
    hasher.update(context_slot.to_le_bytes());
    hasher.update(length.to_le_bytes());
    hasher.update(request_json);
    Ok(hasher.finalize().into())
}

fn validate_exchanges_v2(
    provider_ids: &[[u8; 32]; 2],
    expected_request_json: &[u8],
    exchanges: &[ExactProviderRpcExchangeV1<'_>; 2],
) -> Result<(), FinalizedTxV1RpcErrorV2> {
    for (provider_index, exchange) in exchanges.iter().enumerate() {
        if exchange.provider_id() != &provider_ids[provider_index] {
            return Err(FinalizedTxV1RpcErrorV2::WrongProviderOrder {
                provider_index: provider_index as u8,
            });
        }
        if exchange.request_json() != expected_request_json {
            return Err(FinalizedTxV1RpcErrorV2::WrongRequestBytes {
                provider_index: provider_index as u8,
            });
        }
    }
    Ok(())
}

pub fn agree_finalized_tx_v1_block_v2(
    quorum: &ExactTwoProviderRelayerRpcV1,
    pool_program: [u8; 32],
    request: FinalizedTxV1GetBlockRequestV2,
    exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
) -> Result<AgreedFinalizedTxV1BlockV2, FinalizedTxV1RpcErrorV2> {
    if pool_program == [0u8; 32] {
        return Err(FinalizedTxV1RpcErrorV2::ZeroProgram);
    }
    if request.slot < quorum.startup_checkpoint_slot() {
        return Err(FinalizedTxV1RpcErrorV2::BlockBeforeStartupCheckpoint);
    }
    let request_json = request.encode_json_v2();
    validate_exchanges_v2(quorum.provider_ids(), &request_json, &exchanges)?;
    let first = parse_finalized_tx_v1_block_v2(request, pool_program, exchanges[0].response_json())
        .map_err(|_| FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })?;
    let second =
        parse_finalized_tx_v1_block_v2(request, pool_program, exchanges[1].response_json())
            .map_err(|_| FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 1 })?;
    if first != second {
        return Err(FinalizedTxV1RpcErrorV2::ProviderDisagreement);
    }
    Ok(AgreedFinalizedTxV1BlockV2 {
        provider_ids: *quorum.provider_ids(),
        provider_set_digest: *quorum.provider_set_digest(),
        startup_receipt_digest: *quorum.startup_receipt_digest(),
        startup_checkpoint_slot: quorum.startup_checkpoint_slot(),
        request_binding_sha256: request_binding_v2(
            GET_BLOCK_ENDPOINT_V2,
            request.request_id,
            request.slot,
            &request_json,
        )?,
        block: first,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedTxV1RootPageRequestV2 {
    request_id: u64,
    min_context_slot: u64,
    pool_program: [u8; 32],
    master: [u8; 32],
    lane_id: LaneIdV2,
    lane_account: [u8; 32],
    root_sequence: u64,
    expected_root: [u8; 32],
    page_number: u64,
    address: [u8; 32],
    terminal_binding_sha256: [u8; 32],
    provider_ids: [[u8; 32]; 2],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
}

impl FinalizedTxV1RootPageRequestV2 {
    pub fn request_id_v2(&self) -> u64 {
        self.request_id
    }

    pub fn min_context_slot_v2(&self) -> u64 {
        self.min_context_slot
    }

    pub fn address_v2(&self) -> &[u8; 32] {
        &self.address
    }

    pub fn encode_json_v2(&self) -> Vec<u8> {
        serde_json::to_vec(&GetAccountInfoRequestWireV2 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getAccountInfo",
            params: (
                solana_program::pubkey::Pubkey::new_from_array(self.address).to_string(),
                GetAccountInfoConfigWireV2 {
                    commitment: "finalized",
                    encoding: "base64",
                    min_context_slot: self.min_context_slot,
                },
            ),
        })
        .expect("fixed finalized root-page request serialization cannot fail")
    }
}

#[derive(Serialize)]
struct GetAccountInfoRequestWireV2<'a> {
    jsonrpc: &'a str,
    id: u64,
    method: &'a str,
    params: (String, GetAccountInfoConfigWireV2<'a>),
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct GetAccountInfoConfigWireV2<'a> {
    commitment: &'a str,
    encoding: &'a str,
    min_context_slot: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct GetAccountInfoResultJsonV2 {
    context: AccountContextJsonV2,
    value: Option<AccountJsonV2>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AccountContextJsonV2 {
    slot: u64,
    #[serde(default)]
    #[serde(rename = "apiVersion")]
    _api_version: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AccountJsonV2 {
    data: (String, String),
    executable: bool,
    #[serde(rename = "lamports")]
    _lamports: u64,
    owner: String,
    #[serde(rename = "rentEpoch")]
    _rent_epoch: u64,
    space: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgreedFinalizedTxV1RootPageV2 {
    provider_ids: [[u8; 32]; 2],
    provider_set_digest: [u8; 32],
    startup_receipt_digest: [u8; 32],
    terminal_binding_sha256: [u8; 32],
    request_binding_sha256: [u8; 32],
    context_slot: u64,
    root_page: FinalizedForestRootPageV2,
}

impl AgreedFinalizedTxV1RootPageV2 {
    pub fn request_binding_sha256_v2(&self) -> &[u8; 32] {
        &self.request_binding_sha256
    }
}

fn parse_root_page_v2(
    request: &FinalizedTxV1RootPageRequestV2,
    response_json: &[u8],
) -> Result<(u64, FinalizedForestRootPageV2), FinalizedTxV1RpcErrorV2> {
    let response: GetAccountInfoResultJsonV2 = parse_response_v2(
        request.request_id,
        response_json,
        FINALIZED_TX_V1_ROOT_PAGE_JSON_MAX_BYTES_V2,
    )?
    .ok_or(FinalizedTxV1RpcErrorV2::MissingResult)?;
    if response.context.slot < request.min_context_slot {
        return Err(FinalizedTxV1RpcErrorV2::RootContextTooOld);
    }
    let account = response
        .value
        .ok_or(FinalizedTxV1RpcErrorV2::MissingRootAccount)?;
    if account.executable
        || decode_base58_fixed_v1::<32>(&account.owner)
            .map_err(|_| FinalizedTxV1RpcErrorV2::WrongRootOwner)?
            != request.pool_program
    {
        return Err(FinalizedTxV1RpcErrorV2::WrongRootOwner);
    }
    if account.space != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES as u64 || account.data.1 != "base64"
    {
        return Err(FinalizedTxV1RpcErrorV2::WrongRootSpace);
    }
    let data = BASE64_STANDARD
        .decode(account.data.0)
        .map_err(|_| FinalizedTxV1RpcErrorV2::WrongRootPage)?;
    if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES {
        return Err(FinalizedTxV1RpcErrorV2::WrongRootSpace);
    }
    let header = validate_root_history_page_bytes_v1(&data)
        .map_err(|_| FinalizedTxV1RpcErrorV2::WrongRootPage)?;
    let cursor = canonical_lane_root_page_cursor_v2(
        request.pool_program,
        request.master,
        request.lane_id,
        request.root_sequence,
    )
    .map_err(|_| FinalizedTxV1RpcErrorV2::WrongRootPage)?;
    let expected_root = aspis_statement::decode_digest_canonical(&request.expected_root)
        .map_err(|_| FinalizedTxV1RpcErrorV2::WrongRootPage)?;
    if cursor.address != request.address
        || cursor.page_number != request.page_number
        || header.pool != request.lane_account
        || header.page_number != request.page_number
        || read_root_history_page_root_v1(&data, request.root_sequence)
            .map_err(|_| FinalizedTxV1RpcErrorV2::WrongRootPage)?
            != expected_root
        || root_history_location(request.root_sequence).page_number != request.page_number
    {
        return Err(FinalizedTxV1RpcErrorV2::WrongRootPage);
    }
    Ok((
        response.context.slot,
        FinalizedForestRootPageV2 {
            lane_id: request.lane_id,
            page_number: request.page_number,
            account: FinalizedForestAccountV2 {
                address: request.address,
                owner: request.pool_program,
                executable: false,
                data,
            },
        },
    ))
}

pub fn agree_finalized_tx_v1_root_page_v2(
    quorum: &ExactTwoProviderRelayerRpcV1,
    request: &FinalizedTxV1RootPageRequestV2,
    exchanges: [ExactProviderRpcExchangeV1<'_>; 2],
) -> Result<AgreedFinalizedTxV1RootPageV2, FinalizedTxV1RpcErrorV2> {
    if quorum.provider_ids() != &request.provider_ids
        || quorum.provider_set_digest() != &request.provider_set_digest
        || quorum.startup_receipt_digest() != &request.startup_receipt_digest
        || request.min_context_slot < quorum.startup_checkpoint_slot()
    {
        return Err(FinalizedTxV1RpcErrorV2::RootBindingMismatch);
    }
    let request_json = request.encode_json_v2();
    validate_exchanges_v2(quorum.provider_ids(), &request_json, &exchanges)?;
    let first = parse_root_page_v2(request, exchanges[0].response_json())
        .map_err(|_| FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })?;
    let second = parse_root_page_v2(request, exchanges[1].response_json())
        .map_err(|_| FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 1 })?;
    // Later entries in the same append-only page may legitimately differ
    // between providers. The exact consumed entry, header and address were
    // independently validated above; compare those semantics, not trailing
    // future page contents.
    if first.1.lane_id != second.1.lane_id
        || first.1.page_number != second.1.page_number
        || first.1.account.address != second.1.account.address
        || first.1.account.owner != second.1.account.owner
    {
        return Err(FinalizedTxV1RpcErrorV2::ProviderDisagreement);
    }
    let context_slot = first.0.min(second.0);
    let request_binding_sha256 = request_binding_v2(
        ROOT_PAGE_ENDPOINT_V2,
        request.request_id,
        request.min_context_slot,
        &request_json,
    )?;
    Ok(AgreedFinalizedTxV1RootPageV2 {
        provider_ids: request.provider_ids,
        provider_set_digest: request.provider_set_digest,
        startup_receipt_digest: request.startup_receipt_digest,
        terminal_binding_sha256: request.terminal_binding_sha256,
        request_binding_sha256,
        context_slot,
        root_page: first.1,
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_statement::{
        encode_digest_canonical,
        pool_v1::{
            encode_pool_v1_pair_forest_terminal_request_v1,
            encode_pool_v1_pair_forest_terminal_result_v1, PoolV1PairForestTerminalPaymentV1,
            PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalResultV1,
            PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
            RootHistoryPageV1, POOL_V1_PAIR_TREE_DEPTH,
        },
    };
    use serde_json::json;
    use solana_address_v1::Address;
    use solana_hash_v1::Hash;
    use solana_instruction_v1::Instruction;
    use solana_message_v1::{v1, VersionedMessage};
    use solana_program::pubkey::Pubkey;
    use solana_signature_v1::Signature;

    use super::*;
    use crate::operator_startup::{
        provider_set_digest_v1, FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1,
    };

    const PROVIDERS: [[u8; 32]; 2] = [[0x11; 32], [0x22; 32]];
    const STARTUP_SLOT: u64 = 700;
    const BLOCK_SLOT: u64 = 701;

    fn digest(seed: u32) -> aspis_statement::poseidon2::Digest {
        core::array::from_fn(|index| M31(seed + 13 * index as u32 + 1))
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

    fn quorum() -> ExactTwoProviderRelayerRpcV1 {
        let startup = OperatorStartupReceiptV1::test_only_v1(
            [0x31; 32],
            provider_set_digest_v1(&PROVIDERS),
            FinalizedReleaseCheckpointV1 {
                point: FinalizedChainPointV1::new(STARTUP_SLOT, [0x41; 32]).unwrap(),
                pool_state_sha256: [0x42; 32],
                root_sequence: 0,
                root: encode_digest_canonical(&digest(5)),
            },
        );
        ExactTwoProviderRelayerRpcV1::new(PROVIDERS, &startup).unwrap()
    }

    struct TerminalFixtureV2 {
        program: [u8; 32],
        master: [u8; 32],
        lane_id: LaneIdV2,
        lane_account: [u8; 32],
        request: Vec<u8>,
        result: Vec<u8>,
        next_root: aspis_statement::poseidon2::Digest,
    }

    fn terminal_fixture() -> TerminalFixtureV2 {
        let program = Pubkey::new_from_array([0x51; 32]);
        let master = Pubkey::new_from_array([0x52; 32]);
        let nullifier = digest(20);
        let lane_id = LaneIdV2::new(encode_digest_canonical(&nullifier)[0] & 7).unwrap();
        let lane_account =
            aspis_pool::pool_v1_pair_forest_lane_address(&program, &master, lane_id.as_u8())
                .unwrap()
                .0;
        let public = PoolV1PrivateTransferPublicV1 {
            pool: master.to_bytes(),
            deployment_domain: [0x53; 32],
            anchor_sequence: 0,
            anchor_root: digest(21),
            nullifier,
            asset_id: M31(7),
            recipient_commitment: digest(22),
            change_commitment: digest(23),
        };
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [0x54; 32],
            verifier_release: [0x55; 32],
            pool_program: program.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),
        };
        let next_root = digest(24);
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            master_account: master.to_bytes(),
            selected_lane_account: lane_account.to_bytes(),
            output_lane: lane_id.as_u8(),
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: 1,
                next_root,
                next_frontier: [digest(25); POOL_V1_PAIR_TREE_DEPTH],
            },
        };
        TerminalFixtureV2 {
            program: program.to_bytes(),
            master: master.to_bytes(),
            lane_id,
            lane_account: lane_account.to_bytes(),
            request: encode_pool_v1_pair_forest_terminal_request_v1(&request)
                .unwrap()
                .to_vec(),
            result: encode_pool_v1_pair_forest_terminal_result_v1(&result)
                .unwrap()
                .to_vec(),
            next_root,
        }
    }

    fn tx_v1_wire(fixture: &TerminalFixtureV2, signature: u8) -> Vec<u8> {
        let payer = Address::new_from_array([0x61; 32]);
        let padding_program = Address::new_from_array([0x62; 32]);
        let instructions = vec![
            Instruction {
                program_id: padding_program,
                accounts: Vec::new(),
                data: vec![0x63; 1_300],
            },
            Instruction {
                program_id: Address::new_from_array(fixture.program),
                accounts: Vec::new(),
                data: fixture.request.clone(),
            },
        ];
        let message = v1::Message::try_compile_with_config(
            &payer,
            &instructions,
            Hash::new_from_array([0x64; 32]),
            v1::TransactionConfig::empty().with_compute_unit_limit(1_300_000),
        )
        .unwrap();
        let transaction = V1VersionedTransaction {
            signatures: vec![Signature::from([signature; 64])],
            message: VersionedMessage::V1(message),
        };
        let wire = wincode::serialize(&transaction).unwrap();
        assert_eq!(wire.len(), 1_834);
        assert!(wire.len() > SOLANA_LEGACY_V0_TRANSACTION_MAX_BYTES_V2);
        assert!(wire.len() < SOLANA_V1_TRANSACTION_MAX_BYTES_V2);
        wire
    }

    fn block_response(request_id: u64, fixture: &TerminalFixtureV2, signatures: &[u8]) -> Vec<u8> {
        let transactions = signatures
            .iter()
            .map(|signature| {
                json!({
                    "transaction": [
                        BASE64_STANDARD.encode(tx_v1_wire(fixture, *signature)),
                        "base64"
                    ],
                    "meta": {
                        "err": null,
                        "loadedAddresses": { "writable": [], "readonly": [] },
                        "returnData": {
                            "programId": Pubkey::new_from_array(fixture.program).to_string(),
                            "data": [BASE64_STANDARD.encode(&fixture.result), "base64"]
                        }
                    },
                    "version": 1
                })
            })
            .collect::<Vec<_>>();
        serde_json::to_vec(&json!({
            "jsonrpc": "2.0",
            "id": request_id,
            "result": {
                "blockhash": encode_base58(&[0x71; 32]),
                "previousBlockhash": encode_base58(&[0x41; 32]),
                "parentSlot": STARTUP_SLOT,
                "transactions": transactions
            }
        }))
        .unwrap()
    }

    fn block_exchanges<'a>(
        request: &'a [u8],
        first: &'a [u8],
        second: &'a [u8],
    ) -> [ExactProviderRpcExchangeV1<'a>; 2] {
        [
            ExactProviderRpcExchangeV1::new(PROVIDERS[0], request, first),
            ExactProviderRpcExchangeV1::new(PROVIDERS[1], request, second),
        ]
    }

    fn root_response(
        request_id: u64,
        context_slot: u64,
        fixture: &TerminalFixtureV2,
        root: aspis_statement::poseidon2::Digest,
    ) -> Vec<u8> {
        let mut page = RootHistoryPageV1::genesis(
            fixture.lane_account,
            aspis_pool::POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        );
        page.push(1, root).unwrap();
        let data = page.encode().unwrap();
        serde_json::to_vec(&json!({
            "jsonrpc": "2.0",
            "id": request_id,
            "result": {
                "context": { "slot": context_slot },
                "value": {
                    "data": [BASE64_STANDARD.encode(data), "base64"],
                    "executable": false,
                    "lamports": 1_000_000,
                    "owner": Pubkey::new_from_array(fixture.program).to_string(),
                    "rentEpoch": 0,
                    "space": POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
                }
            }
        }))
        .unwrap()
    }

    #[test]
    fn finalized_tx_v1_quorum_preserves_ledger_order_and_binds_root_page() {
        let fixture = terminal_fixture();
        let quorum = quorum();
        let request = FinalizedTxV1GetBlockRequestV2::new_v2(9, BLOCK_SLOT).unwrap();
        let request_json = request.encode_json_v2();
        assert!(String::from_utf8(request_json.clone())
            .unwrap()
            .contains("\"maxSupportedTransactionVersion\":1"));
        assert!(String::from_utf8(request_json.clone())
            .unwrap()
            .contains("\"commitment\":\"finalized\""));
        // Signature byte order is deliberately opposite to ledger order.
        let first = block_response(9, &fixture, &[0xf0, 0x10]);
        let second_value: serde_json::Value = serde_json::from_slice(&first).unwrap();
        let second = serde_json::to_vec_pretty(&second_value).unwrap();
        let agreed = agree_finalized_tx_v1_block_v2(
            &quorum,
            fixture.program,
            request,
            block_exchanges(&request_json, &first, &second),
        )
        .unwrap();
        assert_eq!(agreed.terminal_count_v2(), 2);
        assert_eq!(agreed.terminal_transaction_index_v2(0), Some(0));
        assert_eq!(agreed.terminal_transaction_index_v2(1), Some(1));
        assert_eq!(agreed.validate_terminal_progress_v2(0, None), Ok(()));
        assert_eq!(
            agreed.validate_terminal_progress_v2(1, None),
            Err(FinalizedTxV1RpcErrorV2::TerminalOrder)
        );
        assert_eq!(agreed.validate_terminal_progress_v2(0, Some(0)), Ok(()));
        assert_eq!(agreed.validate_terminal_progress_v2(1, Some(0)), Ok(()));
        assert_eq!(
            agreed.validate_terminal_progress_v2(0, Some(99)),
            Err(FinalizedTxV1RpcErrorV2::TerminalOrder)
        );
        assert_eq!(
            agreed
                .terminal_event_id_v2(0)
                .unwrap()
                .transaction_signature(),
            &[0xf0; 64]
        );
        assert_eq!(
            agreed
                .terminal_event_id_v2(1)
                .unwrap()
                .transaction_signature(),
            &[0x10; 64]
        );
        assert_eq!(
            agreed.terminal_event_id_v2(0).unwrap().instruction_index(),
            1
        );

        let root_request = agreed
            .root_page_request_v2(10, 0, fixture.program, fixture.master)
            .unwrap();
        let root_request_json = root_request.encode_json_v2();
        let root_first = root_response(10, BLOCK_SLOT, &fixture, fixture.next_root);
        // Different later finalized contexts are safe: the exact immutable
        // target entry is independently checked at both providers.
        let root_second = root_response(10, BLOCK_SLOT + 4, &fixture, fixture.next_root);
        let root = agree_finalized_tx_v1_root_page_v2(
            &quorum,
            &root_request,
            block_exchanges(&root_request_json, &root_first, &root_second),
        )
        .unwrap();
        let observation = agreed.terminal_observation_v2(0, &root).unwrap();
        assert_eq!(observation.transaction_index, 0);
        assert_eq!(observation.transaction_signature, [0xf0; 64]);
        assert_eq!(observation.account_context_slot, BLOCK_SLOT);
        assert_eq!(observation.root_page.lane_id, fixture.lane_id);
        assert_eq!(observation.root_page.account.owner, fixture.program);
    }

    #[test]
    fn finalized_tx_v1_quorum_fails_closed_on_disagreement_version_duplicates_and_finality() {
        let fixture = terminal_fixture();
        let quorum = quorum();
        let request = FinalizedTxV1GetBlockRequestV2::new_v2(11, BLOCK_SLOT).unwrap();
        let request_json = request.encode_json_v2();
        let first = block_response(11, &fixture, &[0xf0, 0x10]);
        let reordered = block_response(11, &fixture, &[0x10, 0xf0]);
        assert_eq!(
            agree_finalized_tx_v1_block_v2(
                &quorum,
                fixture.program,
                request,
                block_exchanges(&request_json, &first, &reordered),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderDisagreement)
        );

        let duplicate = block_response(11, &fixture, &[0x10, 0x10]);
        assert_eq!(
            agree_finalized_tx_v1_block_v2(
                &quorum,
                fixture.program,
                request,
                block_exchanges(&request_json, &duplicate, &duplicate),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );

        let mut wrong_version: serde_json::Value = serde_json::from_slice(&first).unwrap();
        wrong_version["result"]["transactions"][0]["version"] = json!(0);
        let wrong_version = serde_json::to_vec(&wrong_version).unwrap();
        assert_eq!(
            agree_finalized_tx_v1_block_v2(
                &quorum,
                fixture.program,
                request,
                block_exchanges(&request_json, &wrong_version, &wrong_version),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );

        let mut malformed: serde_json::Value = serde_json::from_slice(&first).unwrap();
        malformed["result"]["transactions"][0]["transaction"][0] = json!("not-base64!");
        let malformed = serde_json::to_vec(&malformed).unwrap();
        assert_eq!(
            agree_finalized_tx_v1_block_v2(
                &quorum,
                fixture.program,
                request,
                block_exchanges(&request_json, &malformed, &malformed),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );

        let mut trailing: serde_json::Value = serde_json::from_slice(&first).unwrap();
        let encoded = trailing["result"]["transactions"][0]["transaction"][0]
            .as_str()
            .unwrap();
        let mut trailing_wire = BASE64_STANDARD.decode(encoded).unwrap();
        trailing_wire.push(0);
        trailing["result"]["transactions"][0]["transaction"][0] =
            json!(BASE64_STANDARD.encode(trailing_wire));
        let trailing = serde_json::to_vec(&trailing).unwrap();
        assert_eq!(
            agree_finalized_tx_v1_block_v2(
                &quorum,
                fixture.program,
                request,
                block_exchanges(&request_json, &trailing, &trailing),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );

        let mut oversized: serde_json::Value = serde_json::from_slice(&first).unwrap();
        let encoded = oversized["result"]["transactions"][0]["transaction"][0]
            .as_str()
            .unwrap();
        let mut oversized_wire = BASE64_STANDARD.decode(encoded).unwrap();
        oversized_wire.resize(SOLANA_V1_TRANSACTION_MAX_BYTES_V2 + 1, 0);
        oversized["result"]["transactions"][0]["transaction"][0] =
            json!(BASE64_STANDARD.encode(oversized_wire));
        let oversized = serde_json::to_vec(&oversized).unwrap();
        assert_eq!(
            agree_finalized_tx_v1_block_v2(
                &quorum,
                fixture.program,
                request,
                block_exchanges(&request_json, &oversized, &oversized),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );

        let mut confirmed: serde_json::Value = serde_json::from_slice(&request_json).unwrap();
        confirmed["params"][1]["commitment"] = json!("confirmed");
        let confirmed = serde_json::to_vec(&confirmed).unwrap();
        assert_eq!(
            agree_finalized_tx_v1_block_v2(
                &quorum,
                fixture.program,
                request,
                block_exchanges(&confirmed, &first, &first),
            ),
            Err(FinalizedTxV1RpcErrorV2::WrongRequestBytes { provider_index: 0 })
        );
    }

    #[test]
    fn finalized_root_quorum_rejects_stale_wrong_owner_and_mutated_entry() {
        let fixture = terminal_fixture();
        let quorum = quorum();
        let request = FinalizedTxV1GetBlockRequestV2::new_v2(12, BLOCK_SLOT).unwrap();
        let request_json = request.encode_json_v2();
        let block = block_response(12, &fixture, &[0x90]);
        let agreed = agree_finalized_tx_v1_block_v2(
            &quorum,
            fixture.program,
            request,
            block_exchanges(&request_json, &block, &block),
        )
        .unwrap();
        let root_request = agreed
            .root_page_request_v2(13, 0, fixture.program, fixture.master)
            .unwrap();
        let root_request_json = root_request.encode_json_v2();

        let stale = root_response(13, BLOCK_SLOT - 1, &fixture, fixture.next_root);
        assert_eq!(
            agree_finalized_tx_v1_root_page_v2(
                &quorum,
                &root_request,
                block_exchanges(&root_request_json, &stale, &stale),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );

        let valid = root_response(13, BLOCK_SLOT, &fixture, fixture.next_root);
        let mut wrong_owner: serde_json::Value = serde_json::from_slice(&valid).unwrap();
        wrong_owner["result"]["value"]["owner"] =
            json!(Pubkey::new_from_array([0x99; 32]).to_string());
        let wrong_owner = serde_json::to_vec(&wrong_owner).unwrap();
        assert_eq!(
            agree_finalized_tx_v1_root_page_v2(
                &quorum,
                &root_request,
                block_exchanges(&root_request_json, &wrong_owner, &wrong_owner),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );

        let mutated = root_response(13, BLOCK_SLOT, &fixture, digest(99));
        assert_eq!(
            agree_finalized_tx_v1_root_page_v2(
                &quorum,
                &root_request,
                block_exchanges(&root_request_json, &mutated, &mutated),
            ),
            Err(FinalizedTxV1RpcErrorV2::ProviderResponse { provider_index: 0 })
        );
    }
}
