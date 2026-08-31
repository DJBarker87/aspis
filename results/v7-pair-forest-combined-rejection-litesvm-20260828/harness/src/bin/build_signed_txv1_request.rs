//! Sign one reviewed V7 one-terminal TxV1 input with a disposable local-test
//! keypair and emit exact simulation and submission requests.
//!
//! This evidence-only binary performs no RPC call. The reviewed instruction is
//! preserved byte for byte except that its sole payer/signer public key is
//! replaced by the local test signer. Production wallet code and transaction
//! formats are therefore not changed by the local lifecycle test.

use std::{env, fs, str::FromStr};

use anyhow::{ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_address::Address;
use solana_hash::Hash;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::read_keypair_file;
use solana_message::{v1, VersionedMessage};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

const INPUT_SCHEMA: &str = "aspis.v7.txv1-simulation-input.v1";
const COMPUTE_UNIT_LIMIT: u32 = 1_300_000;
const LOADED_ACCOUNTS_DATA_SIZE_LIMIT: u32 = 64 * 1024 * 1024;
const TRANSACTION_BYTE_LIMIT_EXCLUSIVE: usize = 4_096;
const TERMINAL_REQUEST_BYTES: usize = 320;
const SYSTEM_PROGRAM_ID: &str = "11111111111111111111111111111111";

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct AccountMetaInput {
    pubkey: String,
    writable: bool,
    signer: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    request_id: u64,
    min_context_slot: u64,
    fee_payer: String,
    recent_blockhash: String,
    pool_program: String,
    operation: String,
    history_path: String,
    instruction_accounts: Vec<AccountMetaInput>,
    instruction_data_base64: String,
    #[serde(default)]
    post_state_accounts: Vec<String>,
}

fn parse_address(value: &str, label: &str) -> Address {
    Address::from_str(value).unwrap_or_else(|_| panic!("invalid {label} address"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn expected_shape(operation: &str, history_path: &str) -> Result<(usize, usize, usize)> {
    match (operation, history_path) {
        ("private-transfer", "same-page") => Ok((11, 5, 833)),
        ("private-transfer", "rollover") => Ok((12, 6, 866)),
        ("withdrawal", "same-page") => Ok((16, 5, 998)),
        ("withdrawal", "rollover") => Ok((17, 6, 1_031)),
        _ => anyhow::bail!("unsupported operation/historyPath combination"),
    }
}

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    let input_path = args
        .next()
        .context("usage: build_signed_txv1_request <reviewed-input.json> <local-keypair.json>")?;
    let keypair_path = args
        .next()
        .context("usage: build_signed_txv1_request <reviewed-input.json> <local-keypair.json>")?;
    ensure!(args.next().is_none(), "unexpected extra argument");

    let input: Input = serde_json::from_slice(
        &fs::read(&input_path).with_context(|| format!("read {input_path}"))?,
    )
    .with_context(|| format!("decode {input_path}"))?;
    ensure!(input.schema == INPUT_SCHEMA, "wrong input schema");
    ensure!(input.request_id != 0, "requestId must be nonzero");
    ensure!(input.min_context_slot != 0, "minContextSlot must be nonzero");
    let keypair = read_keypair_file(&keypair_path)
        .map_err(|error| anyhow::anyhow!("read local test keypair: {error}"))?;
    let signer_pubkey = Address::from(keypair.pubkey().to_bytes());
    let reviewed_fee_payer = parse_address(&input.fee_payer, "feePayer");
    let (expected_accounts, payer_index, expected_wire_bytes) =
        expected_shape(&input.operation, &input.history_path)?;
    ensure!(
        input.instruction_accounts.len() == expected_accounts,
        "wrong instruction account count"
    );
    ensure!(
        input.instruction_accounts[payer_index].signer
            && input.instruction_accounts[payer_index].writable
            && parse_address(
                &input.instruction_accounts[payer_index].pubkey,
                "reviewed payer"
            ) == reviewed_fee_payer,
        "reviewed payer position is not the sole writable signer"
    );
    ensure!(
        !input.instruction_accounts[payer_index + 1].signer
            && !input.instruction_accounts[payer_index + 1].writable
            && input.instruction_accounts[payer_index + 1].pubkey == SYSTEM_PROGRAM_ID,
        "system-program position changed"
    );
    ensure!(
        input
            .instruction_accounts
            .iter()
            .enumerate()
            .all(|(index, account)| index == payer_index || !account.signer),
        "reviewed input must have exactly one signer"
    );

    let instruction_data = BASE64_STANDARD
        .decode(&input.instruction_data_base64)
        .context("instructionDataBase64 must be valid base64")?;
    ensure!(
        BASE64_STANDARD.encode(&instruction_data) == input.instruction_data_base64,
        "instructionDataBase64 must use canonical padded encoding"
    );
    ensure!(
        instruction_data.len() == TERMINAL_REQUEST_BYTES
            && instruction_data.get(..4) == Some(b"ASQ8"),
        "reviewed input is not the canonical ASQ8 request"
    );
    let instruction = Instruction {
        program_id: parse_address(&input.pool_program, "poolProgram"),
        accounts: input
            .instruction_accounts
            .iter()
            .map(|account| AccountMeta {
                pubkey: if account.signer {
                    signer_pubkey
                } else {
                    parse_address(&account.pubkey, "instruction account")
                },
                is_signer: account.signer,
                is_writable: account.writable,
            })
            .collect(),
        data: instruction_data,
    };
    let recent_blockhash = Hash::from_str(&input.recent_blockhash)
        .context("invalid recentBlockhash")?;
    let config = v1::TransactionConfig::empty()
        .with_compute_unit_limit(COMPUTE_UNIT_LIMIT)
        .with_loaded_accounts_data_size_limit(LOADED_ACCOUNTS_DATA_SIZE_LIMIT);
    let message = v1::Message::try_compile_with_config(
        &signer_pubkey,
        &[instruction],
        recent_blockhash,
        config,
    )
    .context("compile strict TxV1")?;
    ensure!(message.header.num_required_signatures == 1, "wrong signature count");
    let inline_addresses = message.account_keys.len();
    let versioned_message = VersionedMessage::V1(message);
    versioned_message.sanitize().context("sanitize TxV1 message")?;
    let signable_message = versioned_message.serialize();
    let signed = VersionedTransaction::try_new(versioned_message, &[&keypair])
        .map_err(|error| anyhow::anyhow!("sign TxV1: {error}"))?;
    signed.sanitize().context("sanitize signed TxV1")?;
    ensure!(signed.signatures.len() == 1, "signed TxV1 must have one signature");
    ensure!(
        signed.signatures[0] != Default::default(),
        "signed TxV1 must not contain a placeholder signature"
    );
    let signed_wire = wincode::serialize(&signed)
        .map_err(|error| anyhow::anyhow!("serialize signed TxV1: {error}"))?;
    ensure!(
        signed_wire.len() == expected_wire_bytes,
        "signed TxV1 wire size changed: expected {expected_wire_bytes}, got {}",
        signed_wire.len()
    );
    ensure!(
        signed_wire.len() < TRANSACTION_BYTE_LIMIT_EXCLUSIVE,
        "signed TxV1 exceeds the 4096-byte ceiling"
    );
    let wire_base64 = BASE64_STANDARD.encode(&signed_wire);
    let simulation_request = json!({
        "jsonrpc": "2.0",
        "id": input.request_id,
        "method": "simulateTransaction",
        "params": [wire_base64, {
            "encoding": "base64",
            "commitment": "finalized",
            "sigVerify": true,
            "replaceRecentBlockhash": false,
            "minContextSlot": input.min_context_slot,
            "innerInstructions": true,
            "accounts": {"encoding": "base64", "addresses": input.post_state_accounts},
        }],
    });
    let send_request = json!({
        "jsonrpc": "2.0",
        "id": input.request_id + 100_000,
        "method": "sendTransaction",
        "params": [wire_base64, {
            "encoding": "base64",
            "skipPreflight": true,
            "preflightCommitment": "finalized",
            "maxRetries": 0,
            "minContextSlot": input.min_context_slot,
        }],
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema": "aspis.v7.txv1-signed-local-request.v1",
            "inputPath": input_path,
            "reviewedFeePayer": reviewed_fee_payer.to_string(),
            "localTestFeePayer": signer_pubkey.to_string(),
            "summary": {
                "schema": "aspis.v7.txv1-signed-local-summary.v1",
                "operation": input.operation,
                "historyPath": input.history_path,
                "poolProgram": input.pool_program,
                "feePayer": signer_pubkey.to_string(),
                "minContextSlot": input.min_context_slot,
                "computeUnitLimit": COMPUTE_UNIT_LIMIT,
                "loadedAccountsDataSizeLimit": LOADED_ACCOUNTS_DATA_SIZE_LIMIT,
                "requiredSignatures": 1,
                "inlineAddresses": inline_addresses,
                "instructionAccounts": expected_accounts,
                "instructionDataBytes": TERMINAL_REQUEST_BYTES,
                "serializedTransactionBytes": signed_wire.len(),
                "headroomTo4096Bytes": TRANSACTION_BYTE_LIMIT_EXCLUSIVE - signed_wire.len(),
                "signableMessageSha256": sha256_hex(&signable_message),
            },
            "signature": signed.signatures[0].to_string(),
            "signedWireBase64": BASE64_STANDARD.encode(&signed_wire),
            "signedWireSha256": sha256_hex(&signed_wire),
            "serializedTransactionBytes": signed_wire.len(),
            "signed": true,
            "simulationRequest": simulation_request,
            "sendRequest": send_request,
        }))?
    );
    Ok(())
}
