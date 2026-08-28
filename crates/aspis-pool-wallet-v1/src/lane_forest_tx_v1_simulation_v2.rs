//! Zero-signature simulation envelope for the frozen V7 one-terminal TxV1.
//!
//! This module does not own or load keys, contact RPC, sign, or submit. It
//! converts one already-reviewed `ASQ8` Pool instruction into the exact TxV1
//! wire used by `simulateTransaction` and pins the release gates that are easy
//! to lose at a client boundary: one top-level instruction, the expected Pool
//! account shape, 320 request bytes, a strict 1.3M-CU limit, and a wire strictly
//! below 4,096 bytes.

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use serde::Serialize;
use sha2::{Digest as _, Sha256};
use solana_address_v1::Address;
use solana_hash_v1::Hash as V1Hash;
use solana_message_v1::{v1, VersionedMessage as V1VersionedMessage};
use solana_program::{instruction::Instruction, pubkey::Pubkey};
use solana_signature_v1::Signature as V1Signature;
use solana_transaction_v1::versioned::VersionedTransaction as V1VersionedTransaction;

use crate::lane_forest_transaction_v1::{
    to_v1_instruction_v2, SOLANA_V1_TRANSACTION_MAX_BYTES_V2, SOLANA_V1_VERSION_PREFIX_V2,
};

pub const V7_TX_V1_TERMINAL_COMPUTE_UNIT_LIMIT_V2: u32 = 1_300_000;
pub const V7_TX_V1_TERMINAL_LOADED_ACCOUNT_BYTES_V2: u32 = 64 * 1024 * 1024;
pub const V7_TX_V1_TERMINAL_REQUEST_BYTES_V2: usize = 320;
pub const V7_TX_V1_TERMINAL_RETURN_BYTES_V2: usize = 792;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PairForestTerminalOperationV2 {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PairForestTerminalHistoryPathV2 {
    SamePage,
    Rollover,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct PairForestTxV1CaseV2 {
    pub operation: PairForestTerminalOperationV2,
    pub history_path: PairForestTerminalHistoryPathV2,
}

impl PairForestTxV1CaseV2 {
    pub const fn expected_instruction_accounts_v2(self) -> usize {
        match (self.operation, self.history_path) {
            (
                PairForestTerminalOperationV2::PrivateTransfer,
                PairForestTerminalHistoryPathV2::SamePage,
            ) => 9,
            (
                PairForestTerminalOperationV2::PrivateTransfer,
                PairForestTerminalHistoryPathV2::Rollover,
            ) => 10,
            (
                PairForestTerminalOperationV2::Withdrawal,
                PairForestTerminalHistoryPathV2::SamePage,
            ) => 14,
            (
                PairForestTerminalOperationV2::Withdrawal,
                PairForestTerminalHistoryPathV2::Rollover,
            ) => 15,
        }
    }

    pub const fn expected_wire_bytes_v2(self) -> usize {
        match (self.operation, self.history_path) {
            (
                PairForestTerminalOperationV2::PrivateTransfer,
                PairForestTerminalHistoryPathV2::SamePage,
            ) => 799,
            (
                PairForestTerminalOperationV2::PrivateTransfer,
                PairForestTerminalHistoryPathV2::Rollover,
            ) => 832,
            (
                PairForestTerminalOperationV2::Withdrawal,
                PairForestTerminalHistoryPathV2::SamePage,
            ) => 964,
            (
                PairForestTerminalOperationV2::Withdrawal,
                PairForestTerminalHistoryPathV2::Rollover,
            ) => 997,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairForestTxV1SimulationErrorV2 {
    ZeroRequestId,
    ZeroContextSlot,
    ZeroFeePayer,
    ZeroProgram,
    WrongInstructionAccountCount,
    WrongInstructionData,
    UnexpectedInstructionSigner,
    TooManyPostStateAccounts,
    CompileFailed,
    SanitizeFailed,
    SerializationFailed,
    WrongVersion,
    WrongSignatureCount,
    WrongWireSize,
    TransactionTooLarge,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PairForestTxV1SimulationSummaryV2 {
    pub schema: &'static str,
    pub case: PairForestTxV1CaseV2,
    pub pool_program: String,
    pub fee_payer: String,
    pub min_context_slot: u64,
    pub compute_unit_limit: u32,
    pub loaded_accounts_data_size_limit: u32,
    pub priority_fee_present: bool,
    pub heap_size_present: bool,
    pub required_signatures: u8,
    pub inline_addresses: usize,
    pub instruction_accounts: usize,
    pub instruction_data_bytes: usize,
    pub serialized_transaction_bytes: usize,
    pub headroom_to_4096_bytes: usize,
    pub signable_message_sha256: String,
    pub placeholder_wire_sha256: String,
    pub placeholder_signatures_are_zero: bool,
    pub simulation_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairForestTxV1SimulationPreflightV2 {
    summary: PairForestTxV1SimulationSummaryV2,
    placeholder_wire: Vec<u8>,
    simulation_request_json: Vec<u8>,
}

impl PairForestTxV1SimulationPreflightV2 {
    pub fn summary_v2(&self) -> &PairForestTxV1SimulationSummaryV2 {
        &self.summary
    }

    pub fn placeholder_wire_v2(&self) -> &[u8] {
        &self.placeholder_wire
    }

    pub fn simulation_request_json_v2(&self) -> &[u8] {
        &self.simulation_request_json
    }
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SimulationAccountsConfigV2 {
    encoding: &'static str,
    addresses: Vec<String>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SimulationConfigV2 {
    encoding: &'static str,
    commitment: &'static str,
    sig_verify: bool,
    replace_recent_blockhash: bool,
    min_context_slot: u64,
    inner_instructions: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    accounts: Option<SimulationAccountsConfigV2>,
}

#[derive(Serialize)]
struct SimulationRequestV2 {
    jsonrpc: &'static str,
    id: u64,
    method: &'static str,
    params: (String, SimulationConfigV2),
}

fn sha256_hex_v2(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[allow(clippy::too_many_arguments)]
pub fn build_pair_forest_tx_v1_simulation_preflight_v2(
    request_id: u64,
    min_context_slot: u64,
    fee_payer: Pubkey,
    recent_blockhash: [u8; 32],
    instruction: &Instruction,
    case: PairForestTxV1CaseV2,
    post_state_accounts: &[Pubkey],
) -> Result<PairForestTxV1SimulationPreflightV2, PairForestTxV1SimulationErrorV2> {
    if request_id == 0 {
        return Err(PairForestTxV1SimulationErrorV2::ZeroRequestId);
    }
    if min_context_slot == 0 {
        return Err(PairForestTxV1SimulationErrorV2::ZeroContextSlot);
    }
    if fee_payer == Pubkey::default() {
        return Err(PairForestTxV1SimulationErrorV2::ZeroFeePayer);
    }
    if instruction.program_id == Pubkey::default() {
        return Err(PairForestTxV1SimulationErrorV2::ZeroProgram);
    }
    if instruction.accounts.len() != case.expected_instruction_accounts_v2() {
        return Err(PairForestTxV1SimulationErrorV2::WrongInstructionAccountCount);
    }
    if instruction.data.len() != V7_TX_V1_TERMINAL_REQUEST_BYTES_V2
        || instruction.data.get(..4) != Some(b"ASQ8")
    {
        return Err(PairForestTxV1SimulationErrorV2::WrongInstructionData);
    }
    if instruction.accounts.iter().any(|meta| meta.is_signer) {
        return Err(PairForestTxV1SimulationErrorV2::UnexpectedInstructionSigner);
    }
    if post_state_accounts.len() > 64 {
        return Err(PairForestTxV1SimulationErrorV2::TooManyPostStateAccounts);
    }

    let config = v1::TransactionConfig::empty()
        .with_compute_unit_limit(V7_TX_V1_TERMINAL_COMPUTE_UNIT_LIMIT_V2)
        .with_loaded_accounts_data_size_limit(V7_TX_V1_TERMINAL_LOADED_ACCOUNT_BYTES_V2);
    let message = v1::Message::try_compile_with_config(
        &Address::from(fee_payer.to_bytes()),
        &[to_v1_instruction_v2(instruction)
            .map_err(|_| PairForestTxV1SimulationErrorV2::CompileFailed)?],
        V1Hash::new_from_array(recent_blockhash),
        config,
    )
    .map_err(|_| PairForestTxV1SimulationErrorV2::CompileFailed)?;
    let required_signatures = message.header.num_required_signatures;
    if required_signatures != 1 {
        return Err(PairForestTxV1SimulationErrorV2::WrongSignatureCount);
    }
    let inline_addresses = message.account_keys.len();
    let versioned_message = V1VersionedMessage::V1(message);
    versioned_message
        .sanitize()
        .map_err(|_| PairForestTxV1SimulationErrorV2::SanitizeFailed)?;
    let signable_message = versioned_message.serialize();
    let transaction = V1VersionedTransaction {
        signatures: vec![V1Signature::default()],
        message: versioned_message,
    };
    transaction
        .sanitize()
        .map_err(|_| PairForestTxV1SimulationErrorV2::SanitizeFailed)?;
    let placeholder_wire = wincode::serialize(&transaction)
        .map_err(|_| PairForestTxV1SimulationErrorV2::SerializationFailed)?;
    if placeholder_wire.first().copied() != Some(SOLANA_V1_VERSION_PREFIX_V2) {
        return Err(PairForestTxV1SimulationErrorV2::WrongVersion);
    }
    if placeholder_wire.len() >= SOLANA_V1_TRANSACTION_MAX_BYTES_V2 {
        return Err(PairForestTxV1SimulationErrorV2::TransactionTooLarge);
    }
    if placeholder_wire.len() != case.expected_wire_bytes_v2() {
        return Err(PairForestTxV1SimulationErrorV2::WrongWireSize);
    }

    let placeholder_signatures_are_zero = transaction
        .signatures
        .iter()
        .all(|signature| *signature == V1Signature::default());
    let summary = PairForestTxV1SimulationSummaryV2 {
        schema: "aspis.v7.txv1-simulation-summary.v1",
        case,
        pool_program: instruction.program_id.to_string(),
        fee_payer: fee_payer.to_string(),
        min_context_slot,
        compute_unit_limit: V7_TX_V1_TERMINAL_COMPUTE_UNIT_LIMIT_V2,
        loaded_accounts_data_size_limit: V7_TX_V1_TERMINAL_LOADED_ACCOUNT_BYTES_V2,
        priority_fee_present: false,
        heap_size_present: false,
        required_signatures,
        inline_addresses,
        instruction_accounts: instruction.accounts.len(),
        instruction_data_bytes: instruction.data.len(),
        serialized_transaction_bytes: placeholder_wire.len(),
        headroom_to_4096_bytes: SOLANA_V1_TRANSACTION_MAX_BYTES_V2 - placeholder_wire.len(),
        signable_message_sha256: sha256_hex_v2(&signable_message),
        placeholder_wire_sha256: sha256_hex_v2(&placeholder_wire),
        placeholder_signatures_are_zero,
        simulation_only: true,
    };
    let simulation_request_json = serde_json::to_vec(&SimulationRequestV2 {
        jsonrpc: "2.0",
        id: request_id,
        method: "simulateTransaction",
        params: (
            BASE64_STANDARD.encode(&placeholder_wire),
            SimulationConfigV2 {
                encoding: "base64",
                commitment: "finalized",
                sig_verify: false,
                replace_recent_blockhash: false,
                min_context_slot,
                inner_instructions: true,
                accounts: (!post_state_accounts.is_empty()).then(|| SimulationAccountsConfigV2 {
                    encoding: "base64",
                    addresses: post_state_accounts
                        .iter()
                        .map(ToString::to_string)
                        .collect(),
                }),
            },
        ),
    })
    .map_err(|_| PairForestTxV1SimulationErrorV2::SerializationFailed)?;
    Ok(PairForestTxV1SimulationPreflightV2 {
        summary,
        placeholder_wire,
        simulation_request_json,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use solana_program::instruction::AccountMeta;

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn instruction(account_count: usize) -> Instruction {
        Instruction {
            program_id: key(200),
            accounts: (0..account_count)
                .map(|index| AccountMeta::new(key(index as u8 + 1), false))
                .collect(),
            data: {
                let mut data = vec![0u8; V7_TX_V1_TERMINAL_REQUEST_BYTES_V2];
                data[..4].copy_from_slice(b"ASQ8");
                data
            },
        }
    }

    #[test]
    fn all_four_frozen_terminal_shapes_emit_strict_unsigned_simulation_requests() {
        let cases = [
            PairForestTxV1CaseV2 {
                operation: PairForestTerminalOperationV2::PrivateTransfer,
                history_path: PairForestTerminalHistoryPathV2::SamePage,
            },
            PairForestTxV1CaseV2 {
                operation: PairForestTerminalOperationV2::PrivateTransfer,
                history_path: PairForestTerminalHistoryPathV2::Rollover,
            },
            PairForestTxV1CaseV2 {
                operation: PairForestTerminalOperationV2::Withdrawal,
                history_path: PairForestTerminalHistoryPathV2::SamePage,
            },
            PairForestTxV1CaseV2 {
                operation: PairForestTerminalOperationV2::Withdrawal,
                history_path: PairForestTerminalHistoryPathV2::Rollover,
            },
        ];
        for case in cases {
            let preflight = build_pair_forest_tx_v1_simulation_preflight_v2(
                7,
                9,
                key(201),
                [202; 32],
                &instruction(case.expected_instruction_accounts_v2()),
                case,
                &[key(203)],
            )
            .unwrap();
            assert_eq!(
                preflight.summary_v2().compute_unit_limit,
                V7_TX_V1_TERMINAL_COMPUTE_UNIT_LIMIT_V2
            );
            assert_eq!(
                preflight.summary_v2().serialized_transaction_bytes,
                case.expected_wire_bytes_v2()
            );
            assert!(preflight.summary_v2().placeholder_signatures_are_zero);
            let request: serde_json::Value =
                serde_json::from_slice(preflight.simulation_request_json_v2()).unwrap();
            assert_eq!(request["method"], "simulateTransaction");
            assert_eq!(request["params"][1]["sigVerify"], false);
            assert_eq!(request["params"][1]["replaceRecentBlockhash"], false);
            assert_eq!(request["params"][1]["commitment"], "finalized");
            assert_eq!(request["params"][1]["minContextSlot"], 9);
        }
    }

    #[test]
    fn malformed_shape_never_reaches_simulation_json() {
        let case = PairForestTxV1CaseV2 {
            operation: PairForestTerminalOperationV2::PrivateTransfer,
            history_path: PairForestTerminalHistoryPathV2::SamePage,
        };
        let mut wrong_magic = instruction(case.expected_instruction_accounts_v2());
        wrong_magic.data[..4].copy_from_slice(b"ASF8");
        assert_eq!(
            build_pair_forest_tx_v1_simulation_preflight_v2(
                1,
                2,
                key(201),
                [202; 32],
                &wrong_magic,
                case,
                &[],
            ),
            Err(PairForestTxV1SimulationErrorV2::WrongInstructionData)
        );
    }
}
