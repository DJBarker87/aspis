//! Strict, transport-free JSON-RPC codec for Pool V1 relayer execution.
//!
//! This module emits the exact finalized Solana RPC requests needed by a
//! production [`crate::operator_execution::RelayerExecutionPortV1`] and maps
//! bounded responses into owned, authenticated evidence. It deliberately does
//! not select providers, perform HTTP, hold signer material, or submit bytes on
//! its own.

use bincode::Options as _;
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::Value;
use sha2::{Digest as _, Sha256};
use solana_address_lookup_table_interface::state::AddressLookupTable;
use solana_message::VersionedMessage;
use solana_program::pubkey::Pubkey;
use solana_signature::Signature;
use solana_transaction::versioned::VersionedTransaction;

use crate::{
    finalized_indexer::SolanaRpcCommitmentV1,
    relayer_execution_journal::{
        SignedTransactionInspectorV1, SolanaSdkSignedTransactionInspectorV1,
    },
    relayer_transaction::{AuthenticatedAddressLookupTableV1, RelayerTransactionErrorV1},
    rpc_wire::{decode_base58_fixed_v1, decode_base64_standard_bounded_v1, RpcBinaryDecodeErrorV1},
};

pub const RELAYER_RPC_MAX_LOOKUP_TABLES_V1: usize = 256;
pub const RELAYER_RPC_MAX_LOOKUP_TABLE_DATA_BYTES_V1: usize = 56 + 256 * 32;
pub const RELAYER_RPC_MAX_TRANSACTION_WIRE_BYTES_V1: usize = 4096;
pub const RELAYER_RPC_MAX_MESSAGE_BYTES_V1: usize = 4096;
pub const RELAYER_RPC_MAX_SIMULATION_LOGS_V1: usize = 256;
pub const RELAYER_RPC_MAX_SIMULATION_LOG_BYTES_V1: usize = 4096;
pub const RELAYER_RPC_MAX_SIMULATION_LOG_TOTAL_BYTES_V1: usize = 512 * 1024;
pub const RELAYER_RPC_MAX_RETURN_DATA_BYTES_V1: usize = 4096;

const SMALL_RESPONSE_MAX_BYTES_V1: usize = 16 * 1024;
const ALT_RESPONSE_BASE_MAX_BYTES_V1: usize = 16 * 1024;
const ALT_RESPONSE_MAX_BYTES_PER_ACCOUNT_V1: usize = 16 * 1024;
const SIMULATION_RESPONSE_MAX_BYTES_V1: usize = 8 * 1024 * 1024;
const STATUS_RESPONSE_MAX_BYTES_V1: usize = 128 * 1024;
const MAX_CANONICAL_JSON_DEPTH_V1: usize = 16;
const MAX_CANONICAL_JSON_ITEMS_V1: usize = 256;
const MAX_CANONICAL_JSON_STRING_BYTES_V1: usize = 64 * 1024;

const SIMULATION_RESULT_DOMAIN_V1: &[u8] = b"aspis:pool-v1:relayer-rpc-simulation-result:sha256:v1";
const SIGNATURE_STATUS_DOMAIN_V1: &[u8] = b"aspis:pool-v1:relayer-rpc-signature-status:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerRpcJsonErrorV1 {
    ZeroRequestId,
    ZeroMinContextSlot,
    ZeroProviderSetDigest,
    EmptyLookupTableSet,
    TooManyLookupTables,
    NonCanonicalLookupTableOrder,
    InvalidTransactionWire,
    InvalidMessageWire,
    InvalidExpectedSignature,
    InvalidComputeUnitLimit,
    InvalidFeeLimit,
    ResponseTooLarge,
    InvalidJson,
    WrongJsonRpcVersion,
    WrongResponseId,
    RpcServerError,
    MissingResult,
    ContextTooOld,
    InvalidBlockhash,
    InvalidLastValidBlockHeight,
    AccountCountMismatch,
    MissingAccount,
    InvalidAccount,
    WrongAccountOwner,
    WrongAccountEncoding,
    InvalidAccountData,
    InactiveLookupTable,
    SameSlotLookupTableExtension,
    SimulationFailed,
    InvalidSimulationResult,
    SimulationLogsTooLarge,
    InvalidReturnData,
    FeeUnavailable,
    InvalidFee,
    WrongSignature,
    InvalidSignatureStatus,
    InvalidBlockHeight,
    UnsupportedJsonEvidence,
    Binary(RpcBinaryDecodeErrorV1),
    Transaction(RelayerTransactionErrorV1),
}

impl From<RpcBinaryDecodeErrorV1> for RelayerRpcJsonErrorV1 {
    fn from(error: RpcBinaryDecodeErrorV1) -> Self {
        Self::Binary(error)
    }
}

impl From<RelayerTransactionErrorV1> for RelayerRpcJsonErrorV1 {
    fn from(error: RelayerTransactionErrorV1) -> Self {
        Self::Transaction(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedLatestBlockhashV1 {
    pub context_slot: u64,
    pub blockhash: [u8; 32],
    pub last_valid_block_height: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedAddressLookupTableBatchV1 {
    pub context_slot: u64,
    pub lookup_tables: Vec<AuthenticatedAddressLookupTableV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelayerSimulationReturnDataV1 {
    pub program_id: [u8; 32],
    pub data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccessfulRelayerSimulationRpcV1 {
    pub simulated_at_slot: u64,
    pub compute_units_consumed: u64,
    pub simulation_result_sha256: [u8; 32],
    pub lookup_tables: Vec<AuthenticatedAddressLookupTableV1>,
    pub return_data: Option<RelayerSimulationReturnDataV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedFeeForMessageV1 {
    pub context_slot: u64,
    pub fee_lamports: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerRpcConfirmationStatusV1 {
    Processed,
    Confirmed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerSignatureStatusRpcV1 {
    NotFound {
        context_slot: u64,
        evidence_sha256: [u8; 32],
    },
    Pending {
        context_slot: u64,
        landed_slot: u64,
        confirmation_status: RelayerRpcConfirmationStatusV1,
        confirmations: u64,
        execution_result_sha256: [u8; 32],
    },
    Finalized {
        context_slot: u64,
        landed_slot: u64,
        succeeded: bool,
        execution_result_sha256: [u8; 32],
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedLatestBlockhashRequestV1 {
    request_id: u64,
    min_context_slot: u64,
}

impl FinalizedLatestBlockhashRequestV1 {
    pub fn new(request_id: u64, min_context_slot: u64) -> Result<Self, RelayerRpcJsonErrorV1> {
        validate_request_context_v1(request_id, min_context_slot)?;
        Ok(Self {
            request_id,
            min_context_slot,
        })
    }

    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    pub fn min_context_slot(&self) -> u64 {
        self.min_context_slot
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        serde_json::to_vec(&RpcRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getLatestBlockhash",
            params: (FinalizedMinContextConfigWireV1 {
                commitment: "finalized",
                min_context_slot: self.min_context_slot,
            },),
        })
        .expect("fixed latest-blockhash request serialization cannot fail")
    }

    pub fn decode_response_v1(
        &self,
        response_json: &[u8],
    ) -> Result<FinalizedLatestBlockhashV1, RelayerRpcJsonErrorV1> {
        let result: ContextResultJsonV1<LatestBlockhashValueJsonV1> =
            parse_result_v1(self.request_id, response_json, SMALL_RESPONSE_MAX_BYTES_V1)?;
        validate_context_v1(&result.context, self.min_context_slot)?;
        let blockhash = decode_base58_fixed_v1::<32>(&result.value.blockhash)
            .map_err(|_| RelayerRpcJsonErrorV1::InvalidBlockhash)?;
        if blockhash == [0u8; 32] {
            return Err(RelayerRpcJsonErrorV1::InvalidBlockhash);
        }
        if result.value.last_valid_block_height == 0 {
            return Err(RelayerRpcJsonErrorV1::InvalidLastValidBlockHeight);
        }
        Ok(FinalizedLatestBlockhashV1 {
            context_slot: result.context.slot,
            blockhash,
            last_valid_block_height: result.value.last_valid_block_height,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedAddressLookupTablesRequestV1 {
    request_id: u64,
    min_context_slot: u64,
    addresses: Vec<Pubkey>,
}

impl FinalizedAddressLookupTablesRequestV1 {
    pub fn new(
        request_id: u64,
        min_context_slot: u64,
        addresses: Vec<Pubkey>,
    ) -> Result<Self, RelayerRpcJsonErrorV1> {
        validate_request_context_v1(request_id, min_context_slot)?;
        if addresses.is_empty() {
            return Err(RelayerRpcJsonErrorV1::EmptyLookupTableSet);
        }
        validate_lookup_addresses_v1(&addresses)?;
        Ok(Self {
            request_id,
            min_context_slot,
            addresses,
        })
    }

    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    pub fn min_context_slot(&self) -> u64 {
        self.min_context_slot
    }

    pub fn addresses(&self) -> &[Pubkey] {
        &self.addresses
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        let addresses: Vec<_> = self.addresses.iter().map(ToString::to_string).collect();
        serde_json::to_vec(&RpcRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getMultipleAccounts",
            params: (
                addresses,
                FinalizedAccountConfigWireV1 {
                    commitment: "finalized",
                    encoding: "base64",
                    min_context_slot: self.min_context_slot,
                },
            ),
        })
        .expect("fixed lookup-table request serialization cannot fail")
    }

    pub fn decode_response_v1(
        &self,
        response_json: &[u8],
        provider_set_digest: [u8; 32],
    ) -> Result<FinalizedAddressLookupTableBatchV1, RelayerRpcJsonErrorV1> {
        validate_provider_set_digest_v1(provider_set_digest)?;
        let max_bytes = response_bound_for_accounts_v1(self.addresses.len())?;
        let result: ContextResultJsonV1<Vec<Option<AccountJsonV1>>> =
            parse_result_v1(self.request_id, response_json, max_bytes)?;
        validate_context_v1(&result.context, self.min_context_slot)?;
        let lookup_tables = decode_lookup_table_accounts_v1(
            &self.addresses,
            result.context.slot,
            provider_set_digest,
            result.value,
        )?;
        Ok(FinalizedAddressLookupTableBatchV1 {
            context_slot: result.context.slot,
            lookup_tables,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactRelayerSimulationRequestV1 {
    request_id: u64,
    min_context_slot: u64,
    compute_unit_limit: u32,
    unsigned_transaction_wire: Vec<u8>,
    lookup_addresses: Vec<Pubkey>,
}

impl ExactRelayerSimulationRequestV1 {
    pub fn new(
        request_id: u64,
        min_context_slot: u64,
        compute_unit_limit: u32,
        unsigned_transaction_wire: Vec<u8>,
        lookup_addresses: Vec<Pubkey>,
    ) -> Result<Self, RelayerRpcJsonErrorV1> {
        validate_request_context_v1(request_id, min_context_slot)?;
        if compute_unit_limit == 0 {
            return Err(RelayerRpcJsonErrorV1::InvalidComputeUnitLimit);
        }
        validate_unsigned_transaction_wire_v1(&unsigned_transaction_wire, &lookup_addresses)?;
        Ok(Self {
            request_id,
            min_context_slot,
            compute_unit_limit,
            unsigned_transaction_wire,
            lookup_addresses,
        })
    }

    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    pub fn min_context_slot(&self) -> u64 {
        self.min_context_slot
    }

    pub fn unsigned_transaction_wire(&self) -> &[u8] {
        &self.unsigned_transaction_wire
    }

    pub fn lookup_addresses(&self) -> &[Pubkey] {
        &self.lookup_addresses
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        let accounts =
            (!self.lookup_addresses.is_empty()).then(|| SimulationAccountsConfigWireV1 {
                encoding: "base64",
                addresses: self
                    .lookup_addresses
                    .iter()
                    .map(ToString::to_string)
                    .collect(),
            });
        serde_json::to_vec(&RpcRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "simulateTransaction",
            params: (
                encode_base64_standard_v1(&self.unsigned_transaction_wire),
                SimulateTransactionConfigWireV1 {
                    encoding: "base64",
                    commitment: "finalized",
                    sig_verify: false,
                    replace_recent_blockhash: false,
                    min_context_slot: self.min_context_slot,
                    inner_instructions: false,
                    accounts,
                },
            ),
        })
        .expect("fixed simulation request serialization cannot fail")
    }

    pub fn decode_success_response_v1(
        &self,
        response_json: &[u8],
        provider_set_digest: [u8; 32],
    ) -> Result<SuccessfulRelayerSimulationRpcV1, RelayerRpcJsonErrorV1> {
        validate_provider_set_digest_v1(provider_set_digest)?;
        let result: ContextResultJsonV1<SimulationValueJsonV1> = parse_result_v1(
            self.request_id,
            response_json,
            SIMULATION_RESPONSE_MAX_BYTES_V1,
        )?;
        validate_context_v1(&result.context, self.min_context_slot)?;
        if result.value.err != Value::Null {
            return Err(RelayerRpcJsonErrorV1::SimulationFailed);
        }
        if result.value.inner_instructions.is_some() || result.value.replacement_blockhash.is_some()
        {
            return Err(RelayerRpcJsonErrorV1::InvalidSimulationResult);
        }
        let compute_units_consumed = result
            .value
            .units_consumed
            .ok_or(RelayerRpcJsonErrorV1::InvalidSimulationResult)?;
        if compute_units_consumed == 0
            || compute_units_consumed > u64::from(self.compute_unit_limit)
        {
            return Err(RelayerRpcJsonErrorV1::InvalidSimulationResult);
        }
        let logs = result.value.logs.unwrap_or_default();
        validate_simulation_logs_v1(&logs)?;
        let return_data = decode_return_data_v1(result.value.return_data)?;
        let lookup_tables = match (self.lookup_addresses.is_empty(), result.value.accounts) {
            (true, None) => Vec::new(),
            (true, Some(accounts)) if accounts.is_empty() => Vec::new(),
            (true, Some(_)) => return Err(RelayerRpcJsonErrorV1::AccountCountMismatch),
            (false, None) => return Err(RelayerRpcJsonErrorV1::AccountCountMismatch),
            (false, Some(accounts)) => decode_lookup_table_accounts_v1(
                &self.lookup_addresses,
                result.context.slot,
                provider_set_digest,
                accounts,
            )?,
        };
        let simulation_result_sha256 = simulation_result_digest_v1(
            result.context.slot,
            compute_units_consumed,
            result.value.loaded_accounts_data_size,
            &logs,
            return_data.as_ref(),
        )?;
        Ok(SuccessfulRelayerSimulationRpcV1 {
            simulated_at_slot: result.context.slot,
            compute_units_consumed,
            simulation_result_sha256,
            lookup_tables,
            return_data,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedFeeForMessageRequestV1 {
    request_id: u64,
    min_context_slot: u64,
    max_fee_lamports: u64,
    serialized_message: Vec<u8>,
}

impl FinalizedFeeForMessageRequestV1 {
    pub fn new(
        request_id: u64,
        min_context_slot: u64,
        max_fee_lamports: u64,
        serialized_message: Vec<u8>,
    ) -> Result<Self, RelayerRpcJsonErrorV1> {
        validate_request_context_v1(request_id, min_context_slot)?;
        if max_fee_lamports == 0 {
            return Err(RelayerRpcJsonErrorV1::InvalidFeeLimit);
        }
        if serialized_message.is_empty()
            || serialized_message.len() > RELAYER_RPC_MAX_MESSAGE_BYTES_V1
        {
            return Err(RelayerRpcJsonErrorV1::InvalidMessageWire);
        }
        Ok(Self {
            request_id,
            min_context_slot,
            max_fee_lamports,
            serialized_message,
        })
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        serde_json::to_vec(&RpcRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getFeeForMessage",
            params: (
                encode_base64_standard_v1(&self.serialized_message),
                FinalizedMinContextConfigWireV1 {
                    commitment: "finalized",
                    min_context_slot: self.min_context_slot,
                },
            ),
        })
        .expect("fixed fee request serialization cannot fail")
    }

    pub fn decode_response_v1(
        &self,
        response_json: &[u8],
    ) -> Result<FinalizedFeeForMessageV1, RelayerRpcJsonErrorV1> {
        let result: ContextResultJsonV1<Option<u64>> =
            parse_result_v1(self.request_id, response_json, SMALL_RESPONSE_MAX_BYTES_V1)?;
        validate_context_v1(&result.context, self.min_context_slot)?;
        let fee_lamports = result.value.ok_or(RelayerRpcJsonErrorV1::FeeUnavailable)?;
        if fee_lamports == 0 || fee_lamports > self.max_fee_lamports {
            return Err(RelayerRpcJsonErrorV1::InvalidFee);
        }
        Ok(FinalizedFeeForMessageV1 {
            context_slot: result.context.slot,
            fee_lamports,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSendTransactionRequestV1 {
    request_id: u64,
    min_context_slot: u64,
    transaction_signature: [u8; 64],
    signed_wire: Vec<u8>,
}

impl ExactSendTransactionRequestV1 {
    pub fn new(
        request_id: u64,
        min_context_slot: u64,
        transaction_signature: [u8; 64],
        signed_wire: Vec<u8>,
    ) -> Result<Self, RelayerRpcJsonErrorV1> {
        validate_request_context_v1(request_id, min_context_slot)?;
        if transaction_signature == [0u8; 64] {
            return Err(RelayerRpcJsonErrorV1::InvalidExpectedSignature);
        }
        let inspected = SolanaSdkSignedTransactionInspectorV1
            .inspect_and_verify_signed_transaction_v1(&signed_wire)
            .ok_or(RelayerRpcJsonErrorV1::InvalidTransactionWire)?;
        if inspected.transaction_signature != transaction_signature {
            return Err(RelayerRpcJsonErrorV1::WrongSignature);
        }
        Ok(Self {
            request_id,
            min_context_slot,
            transaction_signature,
            signed_wire,
        })
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        serde_json::to_vec(&RpcRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "sendTransaction",
            params: (
                encode_base64_standard_v1(&self.signed_wire),
                SendTransactionConfigWireV1 {
                    encoding: "base64",
                    skip_preflight: true,
                    preflight_commitment: "finalized",
                    max_retries: 0,
                    min_context_slot: self.min_context_slot,
                },
            ),
        })
        .expect("fixed send request serialization cannot fail")
    }

    pub fn decode_response_v1(
        &self,
        response_json: &[u8],
    ) -> Result<[u8; 64], RelayerRpcJsonErrorV1> {
        let encoded: String =
            parse_result_v1(self.request_id, response_json, SMALL_RESPONSE_MAX_BYTES_V1)?;
        let signature = decode_base58_fixed_v1::<64>(&encoded)?;
        if signature == [0u8; 64] || signature != self.transaction_signature {
            return Err(RelayerRpcJsonErrorV1::WrongSignature);
        }
        Ok(signature)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignatureStatusesRequestV1 {
    request_id: u64,
    transaction_signature: [u8; 64],
}

impl SignatureStatusesRequestV1 {
    pub fn new(
        request_id: u64,
        transaction_signature: [u8; 64],
    ) -> Result<Self, RelayerRpcJsonErrorV1> {
        if request_id == 0 {
            return Err(RelayerRpcJsonErrorV1::ZeroRequestId);
        }
        if transaction_signature == [0u8; 64] {
            return Err(RelayerRpcJsonErrorV1::InvalidExpectedSignature);
        }
        Ok(Self {
            request_id,
            transaction_signature,
        })
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        let signature = Signature::from(self.transaction_signature).to_string();
        serde_json::to_vec(&RpcRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getSignatureStatuses",
            params: (
                vec![signature],
                SignatureStatusesConfigWireV1 {
                    search_transaction_history: true,
                },
            ),
        })
        .expect("fixed signature-status request serialization cannot fail")
    }

    pub fn decode_response_v1(
        &self,
        response_json: &[u8],
    ) -> Result<RelayerSignatureStatusRpcV1, RelayerRpcJsonErrorV1> {
        let result: ContextResultJsonV1<Vec<Option<SignatureStatusJsonV1>>> =
            parse_result_v1(self.request_id, response_json, STATUS_RESPONSE_MAX_BYTES_V1)?;
        validate_context_v1(&result.context, 1)?;
        if result.value.len() != 1 {
            return Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus);
        }
        let Some(status) = result.value.into_iter().next().flatten() else {
            let evidence_sha256 =
                signature_status_digest_v1(self.transaction_signature, result.context.slot, None)?;
            return Ok(RelayerSignatureStatusRpcV1::NotFound {
                context_slot: result.context.slot,
                evidence_sha256,
            });
        };
        if status.slot == 0 || status.slot > result.context.slot {
            return Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus);
        }
        validate_status_object_v1(&status.err, &status.status)?;
        let execution_result_sha256 = signature_status_digest_v1(
            self.transaction_signature,
            result.context.slot,
            Some(&status),
        )?;
        let confirmations = status.confirmations_v1()?;
        match status.confirmation_status.as_str() {
            "processed" | "confirmed" => {
                let confirmations =
                    confirmations.ok_or(RelayerRpcJsonErrorV1::InvalidSignatureStatus)?;
                let confirmation_status = if status.confirmation_status == "processed" {
                    RelayerRpcConfirmationStatusV1::Processed
                } else {
                    RelayerRpcConfirmationStatusV1::Confirmed
                };
                Ok(RelayerSignatureStatusRpcV1::Pending {
                    context_slot: result.context.slot,
                    landed_slot: status.slot,
                    confirmation_status,
                    confirmations,
                    execution_result_sha256,
                })
            }
            "finalized" => {
                if confirmations.is_some() {
                    return Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus);
                }
                Ok(RelayerSignatureStatusRpcV1::Finalized {
                    context_slot: result.context.slot,
                    landed_slot: status.slot,
                    succeeded: status.err == Value::Null,
                    execution_result_sha256,
                })
            }
            _ => Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedBlockHeightRequestV1 {
    request_id: u64,
    min_context_slot: u64,
}

impl FinalizedBlockHeightRequestV1 {
    pub fn new(request_id: u64, min_context_slot: u64) -> Result<Self, RelayerRpcJsonErrorV1> {
        validate_request_context_v1(request_id, min_context_slot)?;
        Ok(Self {
            request_id,
            min_context_slot,
        })
    }

    pub fn encode_json_v1(&self) -> Vec<u8> {
        serde_json::to_vec(&RpcRequestWireV1 {
            jsonrpc: "2.0",
            id: self.request_id,
            method: "getBlockHeight",
            params: (FinalizedMinContextConfigWireV1 {
                commitment: "finalized",
                min_context_slot: self.min_context_slot,
            },),
        })
        .expect("fixed block-height request serialization cannot fail")
    }

    pub fn decode_response_v1(&self, response_json: &[u8]) -> Result<u64, RelayerRpcJsonErrorV1> {
        let block_height: u64 =
            parse_result_v1(self.request_id, response_json, SMALL_RESPONSE_MAX_BYTES_V1)?;
        if block_height == 0 {
            return Err(RelayerRpcJsonErrorV1::InvalidBlockHeight);
        }
        Ok(block_height)
    }
}

#[derive(Serialize)]
struct RpcRequestWireV1<'a, T> {
    jsonrpc: &'a str,
    id: u64,
    method: &'a str,
    params: T,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct FinalizedMinContextConfigWireV1<'a> {
    commitment: &'a str,
    min_context_slot: u64,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct FinalizedAccountConfigWireV1<'a> {
    commitment: &'a str,
    encoding: &'a str,
    min_context_slot: u64,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SimulateTransactionConfigWireV1<'a> {
    encoding: &'a str,
    commitment: &'a str,
    sig_verify: bool,
    replace_recent_blockhash: bool,
    min_context_slot: u64,
    inner_instructions: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    accounts: Option<SimulationAccountsConfigWireV1<'a>>,
}

#[derive(Serialize)]
struct SimulationAccountsConfigWireV1<'a> {
    encoding: &'a str,
    addresses: Vec<String>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SendTransactionConfigWireV1<'a> {
    encoding: &'a str,
    skip_preflight: bool,
    preflight_commitment: &'a str,
    max_retries: u8,
    min_context_slot: u64,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureStatusesConfigWireV1 {
    search_transaction_history: bool,
}

#[derive(Clone, Debug, Default)]
enum PresenceV1<T> {
    #[default]
    Missing,
    Present(T),
}

fn deserialize_presence_v1<'de, D, T>(deserializer: D) -> Result<PresenceV1<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    T::deserialize(deserializer).map(PresenceV1::Present)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonRpcResponseV1 {
    jsonrpc: String,
    id: u64,
    #[serde(default, deserialize_with = "deserialize_presence_v1")]
    result: PresenceV1<Value>,
    #[serde(default, deserialize_with = "deserialize_presence_v1")]
    error: PresenceV1<Value>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ContextResultJsonV1<T> {
    context: RpcContextJsonV1,
    value: T,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RpcContextJsonV1 {
    slot: u64,
    #[serde(default)]
    api_version: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LatestBlockhashValueJsonV1 {
    blockhash: String,
    last_valid_block_height: u64,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AccountJsonV1 {
    data: (String, String),
    executable: bool,
    lamports: u64,
    owner: String,
    rent_epoch: u64,
    space: u64,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SimulationValueJsonV1 {
    err: Value,
    #[serde(default)]
    logs: Option<Vec<String>>,
    #[serde(default)]
    accounts: Option<Vec<Option<AccountJsonV1>>>,
    #[serde(default)]
    units_consumed: Option<u64>,
    #[serde(default)]
    return_data: Option<ReturnDataJsonV1>,
    #[serde(default)]
    inner_instructions: Option<Value>,
    #[serde(default)]
    replacement_blockhash: Option<Value>,
    #[serde(default)]
    loaded_accounts_data_size: Option<u64>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReturnDataJsonV1 {
    program_id: String,
    data: (String, String),
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SignatureStatusJsonV1 {
    slot: u64,
    #[serde(default, deserialize_with = "deserialize_presence_v1")]
    confirmations: PresenceV1<Option<u64>>,
    err: Value,
    confirmation_status: String,
    status: Value,
}

impl SignatureStatusJsonV1 {
    fn confirmations_v1(&self) -> Result<Option<u64>, RelayerRpcJsonErrorV1> {
        match &self.confirmations {
            PresenceV1::Missing => Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus),
            PresenceV1::Present(confirmations) => Ok(*confirmations),
        }
    }
}

fn parse_result_v1<T: for<'de> Deserialize<'de>>(
    expected_request_id: u64,
    bytes: &[u8],
    max_bytes: usize,
) -> Result<T, RelayerRpcJsonErrorV1> {
    if bytes.len() > max_bytes {
        return Err(RelayerRpcJsonErrorV1::ResponseTooLarge);
    }
    let response: JsonRpcResponseV1 =
        serde_json::from_slice(bytes).map_err(|_| RelayerRpcJsonErrorV1::InvalidJson)?;
    if response.jsonrpc != "2.0" {
        return Err(RelayerRpcJsonErrorV1::WrongJsonRpcVersion);
    }
    if response.id != expected_request_id {
        return Err(RelayerRpcJsonErrorV1::WrongResponseId);
    }
    if matches!(response.error, PresenceV1::Present(_)) {
        return Err(RelayerRpcJsonErrorV1::RpcServerError);
    }
    let PresenceV1::Present(result) = response.result else {
        return Err(RelayerRpcJsonErrorV1::MissingResult);
    };
    serde_json::from_value(result).map_err(|_| RelayerRpcJsonErrorV1::InvalidJson)
}

fn validate_request_context_v1(
    request_id: u64,
    min_context_slot: u64,
) -> Result<(), RelayerRpcJsonErrorV1> {
    if request_id == 0 {
        return Err(RelayerRpcJsonErrorV1::ZeroRequestId);
    }
    if min_context_slot == 0 {
        return Err(RelayerRpcJsonErrorV1::ZeroMinContextSlot);
    }
    Ok(())
}

fn validate_context_v1(
    context: &RpcContextJsonV1,
    min_context_slot: u64,
) -> Result<(), RelayerRpcJsonErrorV1> {
    if context.slot == 0 || context.slot < min_context_slot {
        return Err(RelayerRpcJsonErrorV1::ContextTooOld);
    }
    if context
        .api_version
        .as_ref()
        .is_some_and(|version| version.is_empty() || version.len() > 64)
    {
        return Err(RelayerRpcJsonErrorV1::InvalidJson);
    }
    Ok(())
}

fn validate_provider_set_digest_v1(
    provider_set_digest: [u8; 32],
) -> Result<(), RelayerRpcJsonErrorV1> {
    if provider_set_digest == [0u8; 32] {
        return Err(RelayerRpcJsonErrorV1::ZeroProviderSetDigest);
    }
    Ok(())
}

fn validate_lookup_addresses_v1(addresses: &[Pubkey]) -> Result<(), RelayerRpcJsonErrorV1> {
    if addresses.len() > RELAYER_RPC_MAX_LOOKUP_TABLES_V1 {
        return Err(RelayerRpcJsonErrorV1::TooManyLookupTables);
    }
    if addresses
        .iter()
        .any(|address| *address == Pubkey::default())
        || addresses.windows(2).any(|pair| pair[0] >= pair[1])
    {
        return Err(RelayerRpcJsonErrorV1::NonCanonicalLookupTableOrder);
    }
    Ok(())
}

fn validate_unsigned_transaction_wire_v1(
    wire: &[u8],
    lookup_addresses: &[Pubkey],
) -> Result<(), RelayerRpcJsonErrorV1> {
    if wire.is_empty() || wire.len() > RELAYER_RPC_MAX_TRANSACTION_WIRE_BYTES_V1 {
        return Err(RelayerRpcJsonErrorV1::InvalidTransactionWire);
    }
    validate_lookup_addresses_v1(lookup_addresses)?;
    let transaction: VersionedTransaction = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(RELAYER_RPC_MAX_TRANSACTION_WIRE_BYTES_V1 as u64)
        .reject_trailing_bytes()
        .deserialize(wire)
        .map_err(|_| RelayerRpcJsonErrorV1::InvalidTransactionWire)?;
    transaction
        .sanitize()
        .map_err(|_| RelayerRpcJsonErrorV1::InvalidTransactionWire)?;
    if transaction
        .signatures
        .iter()
        .any(|signature| *signature != Signature::default())
        || transaction.message.recent_blockhash().as_ref() == [0u8; 32]
    {
        return Err(RelayerRpcJsonErrorV1::InvalidTransactionWire);
    }
    match &transaction.message {
        VersionedMessage::Legacy(_) if lookup_addresses.is_empty() => Ok(()),
        VersionedMessage::V0(message)
            if !message.address_table_lookups.is_empty()
                && message.address_table_lookups.len() == lookup_addresses.len()
                && message
                    .address_table_lookups
                    .iter()
                    .zip(lookup_addresses)
                    .all(|(lookup, address)| lookup.account_key == *address) =>
        {
            Ok(())
        }
        _ => Err(RelayerRpcJsonErrorV1::NonCanonicalLookupTableOrder),
    }
}

fn response_bound_for_accounts_v1(count: usize) -> Result<usize, RelayerRpcJsonErrorV1> {
    count
        .checked_mul(ALT_RESPONSE_MAX_BYTES_PER_ACCOUNT_V1)
        .and_then(|bytes| bytes.checked_add(ALT_RESPONSE_BASE_MAX_BYTES_V1))
        .ok_or(RelayerRpcJsonErrorV1::ResponseTooLarge)
}

fn decode_lookup_table_accounts_v1(
    requested_addresses: &[Pubkey],
    observed_slot: u64,
    provider_set_digest: [u8; 32],
    accounts: Vec<Option<AccountJsonV1>>,
) -> Result<Vec<AuthenticatedAddressLookupTableV1>, RelayerRpcJsonErrorV1> {
    if accounts.len() != requested_addresses.len() {
        return Err(RelayerRpcJsonErrorV1::AccountCountMismatch);
    }
    let mut output = Vec::with_capacity(accounts.len());
    for (address, account) in requested_addresses.iter().copied().zip(accounts) {
        let account = account.ok_or(RelayerRpcJsonErrorV1::MissingAccount)?;
        if account.data.1 != "base64" {
            return Err(RelayerRpcJsonErrorV1::WrongAccountEncoding);
        }
        let data = decode_base64_standard_bounded_v1(
            &account.data.0,
            RELAYER_RPC_MAX_LOOKUP_TABLE_DATA_BYTES_V1,
        )?;
        if !(56..=RELAYER_RPC_MAX_LOOKUP_TABLE_DATA_BYTES_V1).contains(&data.len())
            || account.space != data.len() as u64
        {
            return Err(RelayerRpcJsonErrorV1::InvalidAccountData);
        }
        let owner = Pubkey::new_from_array(decode_base58_fixed_v1::<32>(&account.owner)?);
        if owner != solana_sdk_ids::address_lookup_table::id() {
            return Err(RelayerRpcJsonErrorV1::WrongAccountOwner);
        }
        if account.executable || account.lamports == 0 {
            return Err(RelayerRpcJsonErrorV1::InvalidAccount);
        }
        let decoded = AddressLookupTable::deserialize(&data)
            .map_err(|_| RelayerRpcJsonErrorV1::InvalidAccountData)?;
        if decoded.meta.deactivation_slot != u64::MAX {
            return Err(RelayerRpcJsonErrorV1::InactiveLookupTable);
        }
        if decoded.meta.last_extended_slot >= observed_slot {
            return Err(RelayerRpcJsonErrorV1::SameSlotLookupTableExtension);
        }
        if usize::from(decoded.meta.last_extended_slot_start_index) > decoded.addresses.len() {
            return Err(RelayerRpcJsonErrorV1::InvalidAccountData);
        }
        output.push(AuthenticatedAddressLookupTableV1::new(
            address,
            owner,
            observed_slot,
            account.lamports,
            account.executable,
            account.rent_epoch,
            SolanaRpcCommitmentV1::Finalized,
            provider_set_digest,
            data,
        )?);
    }
    Ok(output)
}

fn validate_simulation_logs_v1(logs: &[String]) -> Result<(), RelayerRpcJsonErrorV1> {
    if logs.len() > RELAYER_RPC_MAX_SIMULATION_LOGS_V1 {
        return Err(RelayerRpcJsonErrorV1::SimulationLogsTooLarge);
    }
    let total = logs.iter().try_fold(0usize, |total, log| {
        if log.len() > RELAYER_RPC_MAX_SIMULATION_LOG_BYTES_V1 {
            return Err(RelayerRpcJsonErrorV1::SimulationLogsTooLarge);
        }
        total
            .checked_add(log.len())
            .ok_or(RelayerRpcJsonErrorV1::SimulationLogsTooLarge)
    })?;
    if total > RELAYER_RPC_MAX_SIMULATION_LOG_TOTAL_BYTES_V1 {
        return Err(RelayerRpcJsonErrorV1::SimulationLogsTooLarge);
    }
    Ok(())
}

fn decode_return_data_v1(
    return_data: Option<ReturnDataJsonV1>,
) -> Result<Option<RelayerSimulationReturnDataV1>, RelayerRpcJsonErrorV1> {
    let Some(return_data) = return_data else {
        return Ok(None);
    };
    if return_data.data.1 != "base64" {
        return Err(RelayerRpcJsonErrorV1::InvalidReturnData);
    }
    let program_id = decode_base58_fixed_v1::<32>(&return_data.program_id)
        .map_err(|_| RelayerRpcJsonErrorV1::InvalidReturnData)?;
    if program_id == [0u8; 32] {
        return Err(RelayerRpcJsonErrorV1::InvalidReturnData);
    }
    let data = decode_base64_standard_bounded_v1(
        &return_data.data.0,
        RELAYER_RPC_MAX_RETURN_DATA_BYTES_V1,
    )
    .map_err(|_| RelayerRpcJsonErrorV1::InvalidReturnData)?;
    Ok(Some(RelayerSimulationReturnDataV1 { program_id, data }))
}

fn simulation_result_digest_v1(
    context_slot: u64,
    compute_units_consumed: u64,
    loaded_accounts_data_size: Option<u64>,
    logs: &[String],
    return_data: Option<&RelayerSimulationReturnDataV1>,
) -> Result<[u8; 32], RelayerRpcJsonErrorV1> {
    let mut hasher = Sha256::new();
    hasher.update(SIMULATION_RESULT_DOMAIN_V1);
    hasher.update(context_slot.to_le_bytes());
    hasher.update(compute_units_consumed.to_le_bytes());
    match loaded_accounts_data_size {
        Some(size) => {
            hasher.update([1]);
            hasher.update(size.to_le_bytes());
        }
        None => hasher.update([0]),
    }
    hasher.update(
        u32::try_from(logs.len())
            .map_err(|_| RelayerRpcJsonErrorV1::SimulationLogsTooLarge)?
            .to_le_bytes(),
    );
    for log in logs {
        hash_bytes_v1(&mut hasher, log.as_bytes())?;
    }
    match return_data {
        Some(return_data) => {
            hasher.update([1]);
            hasher.update(return_data.program_id);
            hash_bytes_v1(&mut hasher, &return_data.data)?;
        }
        None => hasher.update([0]),
    }
    Ok(hasher.finalize().into())
}

fn validate_status_object_v1(error: &Value, status: &Value) -> Result<(), RelayerRpcJsonErrorV1> {
    let object = status
        .as_object()
        .ok_or(RelayerRpcJsonErrorV1::InvalidSignatureStatus)?;
    if object.len() != 1 {
        return Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus);
    }
    if error == &Value::Null {
        if object.get("Ok") != Some(&Value::Null) {
            return Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus);
        }
    } else if object.get("Err") != Some(error) {
        return Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus);
    }
    Ok(())
}

fn signature_status_digest_v1(
    transaction_signature: [u8; 64],
    context_slot: u64,
    status: Option<&SignatureStatusJsonV1>,
) -> Result<[u8; 32], RelayerRpcJsonErrorV1> {
    let mut hasher = Sha256::new();
    hasher.update(SIGNATURE_STATUS_DOMAIN_V1);
    hasher.update(transaction_signature);
    hasher.update(context_slot.to_le_bytes());
    match status {
        None => hasher.update([0]),
        Some(status) => {
            hasher.update([1]);
            hasher.update(status.slot.to_le_bytes());
            match status.confirmations_v1()? {
                Some(confirmations) => {
                    hasher.update([1]);
                    hasher.update(confirmations.to_le_bytes());
                }
                None => hasher.update([0]),
            }
            hash_bytes_v1(&mut hasher, status.confirmation_status.as_bytes())?;
            hash_json_value_v1(&mut hasher, &status.err, 0)?;
        }
    }
    Ok(hasher.finalize().into())
}

fn hash_json_value_v1(
    hasher: &mut Sha256,
    value: &Value,
    depth: usize,
) -> Result<(), RelayerRpcJsonErrorV1> {
    if depth > MAX_CANONICAL_JSON_DEPTH_V1 {
        return Err(RelayerRpcJsonErrorV1::UnsupportedJsonEvidence);
    }
    match value {
        Value::Null => hasher.update([0]),
        Value::Bool(value) => hasher.update([1, u8::from(*value)]),
        Value::Number(value) => {
            if let Some(value) = value.as_u64() {
                hasher.update([2]);
                hasher.update(value.to_le_bytes());
            } else if let Some(value) = value.as_i64() {
                hasher.update([3]);
                hasher.update(value.to_le_bytes());
            } else {
                return Err(RelayerRpcJsonErrorV1::UnsupportedJsonEvidence);
            }
        }
        Value::String(value) => {
            if value.len() > MAX_CANONICAL_JSON_STRING_BYTES_V1 {
                return Err(RelayerRpcJsonErrorV1::UnsupportedJsonEvidence);
            }
            hasher.update([4]);
            hash_bytes_v1(hasher, value.as_bytes())?;
        }
        Value::Array(values) => {
            if values.len() > MAX_CANONICAL_JSON_ITEMS_V1 {
                return Err(RelayerRpcJsonErrorV1::UnsupportedJsonEvidence);
            }
            hasher.update([5]);
            hasher.update(
                u32::try_from(values.len())
                    .map_err(|_| RelayerRpcJsonErrorV1::UnsupportedJsonEvidence)?
                    .to_le_bytes(),
            );
            for value in values {
                hash_json_value_v1(hasher, value, depth + 1)?;
            }
        }
        Value::Object(values) => {
            if values.len() > MAX_CANONICAL_JSON_ITEMS_V1 {
                return Err(RelayerRpcJsonErrorV1::UnsupportedJsonEvidence);
            }
            hasher.update([6]);
            hasher.update(
                u32::try_from(values.len())
                    .map_err(|_| RelayerRpcJsonErrorV1::UnsupportedJsonEvidence)?
                    .to_le_bytes(),
            );
            let mut keys: Vec<_> = values.keys().collect();
            keys.sort_unstable();
            for key in keys {
                if key.len() > MAX_CANONICAL_JSON_STRING_BYTES_V1 {
                    return Err(RelayerRpcJsonErrorV1::UnsupportedJsonEvidence);
                }
                hash_bytes_v1(hasher, key.as_bytes())?;
                hash_json_value_v1(hasher, &values[key], depth + 1)?;
            }
        }
    }
    Ok(())
}

fn hash_bytes_v1(hasher: &mut Sha256, bytes: &[u8]) -> Result<(), RelayerRpcJsonErrorV1> {
    hasher.update(
        u32::try_from(bytes.len())
            .map_err(|_| RelayerRpcJsonErrorV1::UnsupportedJsonEvidence)?
            .to_le_bytes(),
    );
    hasher.update(bytes);
    Ok(())
}

fn encode_base64_standard_v1(input: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut output = String::with_capacity(input.len().div_ceil(3) * 4);
    for chunk in input.chunks(3) {
        let a = chunk[0];
        let b = chunk.get(1).copied().unwrap_or(0);
        let c = chunk.get(2).copied().unwrap_or(0);
        output.push(ALPHABET[usize::from(a >> 2)] as char);
        output.push(ALPHABET[usize::from((a & 0x03) << 4 | b >> 4)] as char);
        if chunk.len() > 1 {
            output.push(ALPHABET[usize::from((b & 0x0f) << 2 | c >> 6)] as char);
        } else {
            output.push('=');
        }
        if chunk.len() > 2 {
            output.push(ALPHABET[usize::from(c & 0x3f)] as char);
        } else {
            output.push('=');
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use solana_address_lookup_table_interface::state::LookupTableMeta;
    use solana_keypair::Keypair;
    use solana_message::{compiled_instruction::CompiledInstruction, legacy, v0, MessageHeader};
    use solana_program::hash::Hash;
    use solana_signer::Signer;

    use super::*;

    fn key(byte: u8) -> Pubkey {
        Pubkey::new_from_array([byte; 32])
    }

    fn zero_signature_legacy_wire_v1() -> Vec<u8> {
        let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
            &[],
            Some(&key(1)),
            &Hash::new_from_array([2; 32]),
        ));
        bincode::serialize(&VersionedTransaction {
            signatures: vec![Signature::default()],
            message,
        })
        .unwrap()
    }

    fn zero_signature_v0_wire_v1(table: Pubkey) -> Vec<u8> {
        let message = VersionedMessage::V0(v0::Message {
            header: MessageHeader {
                num_required_signatures: 1,
                num_readonly_signed_accounts: 0,
                num_readonly_unsigned_accounts: 1,
            },
            account_keys: vec![key(1), key(2)],
            recent_blockhash: Hash::new_from_array([3; 32]),
            instructions: vec![CompiledInstruction {
                program_id_index: 1,
                accounts: vec![2],
                data: vec![],
            }],
            address_table_lookups: vec![v0::MessageAddressTableLookup {
                account_key: table,
                writable_indexes: vec![],
                readonly_indexes: vec![0],
            }],
        });
        bincode::serialize(&VersionedTransaction {
            signatures: vec![Signature::default()],
            message,
        })
        .unwrap()
    }

    fn signed_wire_v1() -> (Vec<u8>, [u8; 64]) {
        let payer = Keypair::new();
        let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
            &[],
            Some(&payer.pubkey()),
            &Hash::new_from_array([4; 32]),
        ));
        let transaction = VersionedTransaction::try_new(message, &[&payer]).unwrap();
        let signature = *transaction.signatures[0].as_array();
        (bincode::serialize(&transaction).unwrap(), signature)
    }

    fn lookup_table_data_v1(last_extended_slot: u64) -> Vec<u8> {
        AddressLookupTable {
            meta: LookupTableMeta {
                last_extended_slot,
                ..LookupTableMeta::default()
            },
            addresses: Cow::Owned(vec![key(9)]),
        }
        .serialize_for_tests()
        .unwrap()
    }

    fn account_json_v1(data: &[u8], owner: Pubkey) -> Value {
        serde_json::json!({
            "data": [encode_base64_standard_v1(data), "base64"],
            "executable": false,
            "lamports": 1_000_000u64,
            "owner": owner.to_string(),
            "rentEpoch": 7u64,
            "space": data.len() as u64
        })
    }

    #[test]
    fn exact_request_bytes_are_stable() {
        assert_eq!(
            FinalizedLatestBlockhashRequestV1::new(7, 99)
                .unwrap()
                .encode_json_v1(),
            br#"{"jsonrpc":"2.0","id":7,"method":"getLatestBlockhash","params":[{"commitment":"finalized","minContextSlot":99}]}"#
        );

        let table = key(8);
        let alt = FinalizedAddressLookupTablesRequestV1::new(8, 100, vec![table]).unwrap();
        assert_eq!(
            String::from_utf8(alt.encode_json_v1()).unwrap(),
            format!(
                "{{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"getMultipleAccounts\",\"params\":[[\"{table}\"],{{\"commitment\":\"finalized\",\"encoding\":\"base64\",\"minContextSlot\":100}}]}}"
            )
        );
        assert_eq!(
            FinalizedAddressLookupTablesRequestV1::new(8, 100, vec![key(9), table]),
            Err(RelayerRpcJsonErrorV1::NonCanonicalLookupTableOrder)
        );

        let wire = zero_signature_legacy_wire_v1();
        let simulation =
            ExactRelayerSimulationRequestV1::new(9, 101, 500, wire.clone(), vec![]).unwrap();
        assert_eq!(
            String::from_utf8(simulation.encode_json_v1()).unwrap(),
            format!(
                "{{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"simulateTransaction\",\"params\":[\"{}\",{{\"encoding\":\"base64\",\"commitment\":\"finalized\",\"sigVerify\":false,\"replaceRecentBlockhash\":false,\"minContextSlot\":101,\"innerInstructions\":false}}]}}",
                encode_base64_standard_v1(&wire)
            )
        );

        assert_eq!(
            FinalizedFeeForMessageRequestV1::new(10, 102, 10_000, vec![1, 2, 3])
                .unwrap()
                .encode_json_v1(),
            br#"{"jsonrpc":"2.0","id":10,"method":"getFeeForMessage","params":["AQID",{"commitment":"finalized","minContextSlot":102}]}"#
        );

        let signature = [5u8; 64];
        let status = SignatureStatusesRequestV1::new(11, signature).unwrap();
        assert_eq!(
            String::from_utf8(status.encode_json_v1()).unwrap(),
            format!(
                "{{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"getSignatureStatuses\",\"params\":[[\"{}\"],{{\"searchTransactionHistory\":true}}]}}",
                Signature::from(signature)
            )
        );

        assert_eq!(
            FinalizedBlockHeightRequestV1::new(12, 103)
                .unwrap()
                .encode_json_v1(),
            br#"{"jsonrpc":"2.0","id":12,"method":"getBlockHeight","params":[{"commitment":"finalized","minContextSlot":103}]}"#
        );
    }

    #[test]
    fn latest_blockhash_envelope_and_context_fail_closed() {
        let request = FinalizedLatestBlockhashRequestV1::new(7, 99).unwrap();
        let blockhash = Hash::new_from_array([7; 32]).to_string();
        let valid = serde_json::to_vec(&serde_json::json!({
            "jsonrpc": "2.0",
            "id": 7,
            "result": {"context": {"slot": 100}, "value": {
                "blockhash": blockhash,
                "lastValidBlockHeight": 500
            }}
        }))
        .unwrap();
        assert_eq!(
            request.decode_response_v1(&valid).unwrap().context_slot,
            100
        );

        let mut wrong_id_value: Value = serde_json::from_slice(&valid).unwrap();
        wrong_id_value["id"] = Value::from(8);
        let wrong_id_bytes = serde_json::to_vec(&wrong_id_value).unwrap();
        assert_eq!(
            request.decode_response_v1(&wrong_id_bytes),
            Err(RelayerRpcJsonErrorV1::WrongResponseId)
        );

        let mut stale_value: Value = serde_json::from_slice(&valid).unwrap();
        stale_value["result"]["context"]["slot"] = Value::from(98);
        let stale_bytes = serde_json::to_vec(&stale_value).unwrap();
        assert_eq!(
            request.decode_response_v1(&stale_bytes),
            Err(RelayerRpcJsonErrorV1::ContextTooOld)
        );

        assert_eq!(
            request.decode_response_v1(br#"{"jsonrpc":"2.0","id":7,"result":{},"error":null}"#),
            Err(RelayerRpcJsonErrorV1::RpcServerError)
        );
        assert_eq!(
            request.decode_response_v1(br#"{"jsonrpc":"2.0","id":7}"#),
            Err(RelayerRpcJsonErrorV1::MissingResult)
        );
    }

    #[test]
    fn finalized_alt_images_are_exact_and_malformed_accounts_fail_closed() {
        let address = key(8);
        let request = FinalizedAddressLookupTablesRequestV1::new(8, 100, vec![address]).unwrap();
        let data = lookup_table_data_v1(99);
        let response = |account: Value| {
            serde_json::to_vec(&serde_json::json!({
                "jsonrpc": "2.0",
                "id": 8,
                "result": {"context": {"slot": 100}, "value": [account]}
            }))
            .unwrap()
        };
        let valid = response(account_json_v1(
            &data,
            solana_sdk_ids::address_lookup_table::id(),
        ));
        let batch = request.decode_response_v1(&valid, [6; 32]).unwrap();
        assert_eq!(batch.context_slot, 100);
        assert_eq!(batch.lookup_tables[0].address(), address);
        assert_eq!(batch.lookup_tables[0].account_data(), data);

        assert_eq!(
            request.decode_response_v1(&response(Value::Null), [6; 32]),
            Err(RelayerRpcJsonErrorV1::MissingAccount)
        );
        assert_eq!(
            request.decode_response_v1(&response(account_json_v1(&data, key(7))), [6; 32]),
            Err(RelayerRpcJsonErrorV1::WrongAccountOwner)
        );
        let same_slot = lookup_table_data_v1(100);
        assert_eq!(
            request.decode_response_v1(
                &response(account_json_v1(
                    &same_slot,
                    solana_sdk_ids::address_lookup_table::id(),
                )),
                [6; 32],
            ),
            Err(RelayerRpcJsonErrorV1::SameSlotLookupTableExtension)
        );
    }

    #[test]
    fn simulation_binds_accounts_context_and_bounded_success_result() {
        let table = key(8);
        let wire = zero_signature_v0_wire_v1(table);
        let request = ExactRelayerSimulationRequestV1::new(9, 100, 500, wire, vec![table]).unwrap();
        let data = lookup_table_data_v1(99);
        let response = |slot: u64, units: u64, account: Value, err: Value| {
            serde_json::to_vec(&serde_json::json!({
                "jsonrpc": "2.0",
                "id": 9,
                "result": {"context": {"slot": slot}, "value": {
                    "err": err,
                    "logs": ["Program log: exact"],
                    "accounts": [account],
                    "unitsConsumed": units,
                    "returnData": {"programId": key(4).to_string(), "data": ["AQI=", "base64"]},
                    "innerInstructions": null,
                    "replacementBlockhash": null,
                    "loadedAccountsDataSize": 88
                }}
            }))
            .unwrap()
        };
        let account = account_json_v1(&data, solana_sdk_ids::address_lookup_table::id());
        let valid = response(100, 450, account.clone(), Value::Null);
        let decoded = request.decode_success_response_v1(&valid, [6; 32]).unwrap();
        assert_eq!(decoded.simulated_at_slot, 100);
        assert_eq!(decoded.compute_units_consumed, 450);
        assert_eq!(decoded.lookup_tables[0].account_data(), data);
        assert_ne!(decoded.simulation_result_sha256, [0u8; 32]);
        assert_eq!(decoded.return_data.unwrap().data, [1, 2]);

        assert_eq!(
            request.decode_success_response_v1(
                &response(99, 450, account.clone(), Value::Null),
                [6; 32],
            ),
            Err(RelayerRpcJsonErrorV1::ContextTooOld)
        );
        assert_eq!(
            request.decode_success_response_v1(
                &response(100, 501, account.clone(), Value::Null),
                [6; 32],
            ),
            Err(RelayerRpcJsonErrorV1::InvalidSimulationResult)
        );
        assert_eq!(
            request.decode_success_response_v1(
                &response(
                    100,
                    450,
                    account,
                    serde_json::json!({"InstructionError": [0, "Custom"]})
                ),
                [6; 32],
            ),
            Err(RelayerRpcJsonErrorV1::SimulationFailed)
        );

        let mut oversized_logs: Value = serde_json::from_slice(&valid).unwrap();
        oversized_logs["result"]["value"]["logs"] =
            serde_json::json!(["x".repeat(RELAYER_RPC_MAX_SIMULATION_LOG_BYTES_V1 + 1)]);
        assert_eq!(
            request.decode_success_response_v1(
                &serde_json::to_vec(&oversized_logs).unwrap(),
                [6; 32],
            ),
            Err(RelayerRpcJsonErrorV1::SimulationLogsTooLarge)
        );
    }

    #[test]
    fn fee_send_status_and_height_decoders_are_fail_closed() {
        let fee = FinalizedFeeForMessageRequestV1::new(10, 100, 10_000, vec![1]).unwrap();
        assert_eq!(
            fee.decode_response_v1(
                br#"{"jsonrpc":"2.0","id":10,"result":{"context":{"slot":101},"value":5000}}"#
            )
            .unwrap()
            .fee_lamports,
            5000
        );
        assert_eq!(
            fee.decode_response_v1(
                br#"{"jsonrpc":"2.0","id":10,"result":{"context":{"slot":101},"value":null}}"#
            ),
            Err(RelayerRpcJsonErrorV1::FeeUnavailable)
        );
        assert_eq!(
            fee.decode_response_v1(
                br#"{"jsonrpc":"2.0","id":10,"result":{"context":{"slot":101},"value":10001}}"#
            ),
            Err(RelayerRpcJsonErrorV1::InvalidFee)
        );

        let (wire, signature) = signed_wire_v1();
        let send = ExactSendTransactionRequestV1::new(11, 100, signature, wire).unwrap();
        assert_eq!(
            String::from_utf8(send.encode_json_v1()).unwrap(),
            format!(
                "{{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"sendTransaction\",\"params\":[\"{}\",{{\"encoding\":\"base64\",\"skipPreflight\":true,\"preflightCommitment\":\"finalized\",\"maxRetries\":0,\"minContextSlot\":100}}]}}",
                encode_base64_standard_v1(&send.signed_wire)
            )
        );
        let encoded_signature = Signature::from(signature).to_string();
        let send_response = serde_json::to_vec(&serde_json::json!({
            "jsonrpc": "2.0", "id": 11, "result": encoded_signature
        }))
        .unwrap();
        assert_eq!(send.decode_response_v1(&send_response).unwrap(), signature);
        let wrong_send = serde_json::to_vec(&serde_json::json!({
            "jsonrpc": "2.0", "id": 11, "result": Signature::from([7; 64]).to_string()
        }))
        .unwrap();
        assert_eq!(
            send.decode_response_v1(&wrong_send),
            Err(RelayerRpcJsonErrorV1::WrongSignature)
        );

        let status = SignatureStatusesRequestV1::new(12, signature).unwrap();
        let finalized = br#"{"jsonrpc":"2.0","id":12,"result":{"context":{"slot":110},"value":[{"slot":109,"confirmations":null,"err":null,"confirmationStatus":"finalized","status":{"Ok":null}}]}}"#;
        assert!(matches!(
            status.decode_response_v1(finalized).unwrap(),
            RelayerSignatureStatusRpcV1::Finalized {
                succeeded: true,
                ..
            }
        ));
        let inconsistent = br#"{"jsonrpc":"2.0","id":12,"result":{"context":{"slot":110},"value":[{"slot":109,"confirmations":null,"err":null,"confirmationStatus":"finalized","status":{"Err":"bad"}}]}}"#;
        assert_eq!(
            status.decode_response_v1(inconsistent),
            Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus)
        );
        let missing_confirmations = br#"{"jsonrpc":"2.0","id":12,"result":{"context":{"slot":110},"value":[{"slot":109,"err":null,"confirmationStatus":"finalized","status":{"Ok":null}}]}}"#;
        assert_eq!(
            status.decode_response_v1(missing_confirmations),
            Err(RelayerRpcJsonErrorV1::InvalidSignatureStatus)
        );
        let not_found =
            br#"{"jsonrpc":"2.0","id":12,"result":{"context":{"slot":110},"value":[null]}}"#;
        assert!(matches!(
            status.decode_response_v1(not_found).unwrap(),
            RelayerSignatureStatusRpcV1::NotFound { .. }
        ));

        let height = FinalizedBlockHeightRequestV1::new(13, 100).unwrap();
        assert_eq!(
            height
                .decode_response_v1(br#"{"jsonrpc":"2.0","id":13,"result":700}"#)
                .unwrap(),
            700
        );
        assert_eq!(
            height.decode_response_v1(br#"{"jsonrpc":"2.0","id":13,"result":0}"#),
            Err(RelayerRpcJsonErrorV1::InvalidBlockHeight)
        );
    }
}
