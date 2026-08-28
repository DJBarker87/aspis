//! Build a zero-signature TxV1 `simulateTransaction` request from a reviewed
//! one-terminal instruction manifest.
//!
//! The executable performs no RPC call and has no signing or submission path.

use std::{env, fs, str::FromStr};

use aspis_pool_wallet_v1::lane_forest_tx_v1_simulation_v2::{
    build_pair_forest_tx_v1_simulation_preflight_v2, PairForestTerminalHistoryPathV2,
    PairForestTerminalOperationV2, PairForestTxV1CaseV2,
};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use serde::Deserialize;
use solana_hash_v1::Hash;
use solana_program::{instruction::AccountMeta, instruction::Instruction, pubkey::Pubkey};

const INPUT_SCHEMA: &str = "aspis.v7.txv1-simulation-input.v1";

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

fn parse_pubkey(value: &str, label: &str) -> Pubkey {
    Pubkey::from_str(value).unwrap_or_else(|_| panic!("invalid {label} pubkey"))
}

fn main() {
    let path = env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: tx_v1_simulation_request <reviewed-input.json>");
        std::process::exit(2);
    });
    let input: Input = serde_json::from_slice(
        &fs::read(&path).unwrap_or_else(|error| panic!("read {path}: {error}")),
    )
    .unwrap_or_else(|error| panic!("decode {path}: {error}"));
    assert_eq!(input.schema, INPUT_SCHEMA, "wrong input schema");
    let case = PairForestTxV1CaseV2 {
        operation: match input.operation.as_str() {
            "private-transfer" => PairForestTerminalOperationV2::PrivateTransfer,
            "withdrawal" => PairForestTerminalOperationV2::Withdrawal,
            _ => panic!("operation must be private-transfer or withdrawal"),
        },
        history_path: match input.history_path.as_str() {
            "same-page" => PairForestTerminalHistoryPathV2::SamePage,
            "rollover" => PairForestTerminalHistoryPathV2::Rollover,
            _ => panic!("historyPath must be same-page or rollover"),
        },
    };
    let instruction_data = BASE64_STANDARD
        .decode(&input.instruction_data_base64)
        .expect("instructionDataBase64 must be valid base64");
    assert_eq!(
        BASE64_STANDARD.encode(&instruction_data),
        input.instruction_data_base64,
        "instructionDataBase64 must use canonical padded encoding"
    );
    let instruction = Instruction {
        program_id: parse_pubkey(&input.pool_program, "poolProgram"),
        accounts: input
            .instruction_accounts
            .iter()
            .map(|account| AccountMeta {
                pubkey: parse_pubkey(&account.pubkey, "instruction account"),
                is_signer: account.signer,
                is_writable: account.writable,
            })
            .collect(),
        data: instruction_data,
    };
    let recent_blockhash = Hash::from_str(&input.recent_blockhash)
        .expect("invalid recentBlockhash")
        .to_bytes();
    let post_state_accounts = input
        .post_state_accounts
        .iter()
        .map(|value| parse_pubkey(value, "post-state account"))
        .collect::<Vec<_>>();
    let preflight = build_pair_forest_tx_v1_simulation_preflight_v2(
        input.request_id,
        input.min_context_slot,
        parse_pubkey(&input.fee_payer, "feePayer"),
        recent_blockhash,
        &instruction,
        case,
        &post_state_accounts,
    )
    .expect("TxV1 preflight rejected reviewed input");
    let simulation_request: serde_json::Value =
        serde_json::from_slice(preflight.simulation_request_json_v2())
            .expect("fixed simulation request JSON");
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": "aspis.v7.txv1-simulation-preflight.v1",
            "inputPath": path,
            "summary": preflight.summary_v2(),
            "simulationRequest": simulation_request,
        }))
        .expect("fixed preflight JSON")
    );
}
