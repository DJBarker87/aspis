use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_pool_wallet_v1::lane_forest_client_v2::build_pair_forest_checkpoint_instruction_v2;
use aspis_statement::pool_v1::decode_pool_v1_pair_forest_master_v1;
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_keypair::read_keypair_file;
use solana_message::{legacy, VersionedMessage};
use solana_program::{hash::Hash, pubkey::Pubkey};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    config: String,
    payer_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
    master_account: String,
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(env::args_os().nth(1)
        .context("usage: build-live-pool-checkpoint <input.json>")?);
    ensure!(env::args_os().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    ensure!(input.schema == "aspis.v7.live-pool-checkpoint-input.v1" && input.min_context_slot > 0,
        "wrong input schema or RPC identity");
    let config: Value = serde_json::from_slice(&fs::read(&input.config)?)?;
    ensure!(config["mainnetReady"] == false && config["identitySet"]["auditOnly"] == true,
        "checkpoint is not pinned to disposable audit identities");
    let pool_id = config["identitySet"]["programs"].as_array().context("missing programs")?
        .iter().find(|program| program["name"] == "pool")
        .and_then(|program| program["id"].as_str()).context("missing Pool program")?;
    let account: Value = serde_json::from_slice(&fs::read(&input.master_account)?)?;
    let data = BASE64.decode(account["result"]["value"]["data"][0]
        .as_str().context("missing master data")?)?;
    let master = decode_pool_v1_pair_forest_master_v1(&data)
        .map_err(|error| anyhow::anyhow!("decode live master: {error:?}"))?;
    let payer = read_keypair_file(&input.payer_keypair)
        .map_err(|error| anyhow::anyhow!("read disposable payer: {error}"))?;
    let instruction = build_pair_forest_checkpoint_instruction_v2(
        Pubkey::from_str(pool_id)?, payer.pubkey(), &master,
    ).map_err(|error| anyhow::anyhow!("build checkpoint instruction: {error:?}"))?;
    let checkpoint_account = instruction.accounts[9].pubkey.to_string();
    let blockhash = Hash::from_str(&input.recent_blockhash)?;
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &[ComputeBudgetInstruction::set_compute_unit_limit(1_400_000), instruction],
        Some(&payer.pubkey()), &blockhash,
    ));
    let transaction = VersionedTransaction::try_new(message, &[&payer])
        .map_err(|error| anyhow::anyhow!("sign checkpoint: {error}"))?;
    let signature = transaction.signatures[0].to_string();
    let wire = bincode::serialize(&transaction)?;
    ensure!(wire.len() < 1_232, "checkpoint exceeds legacy envelope");
    let wire_base64 = BASE64.encode(&wire);
    println!("{}", json!({
        "schema":"aspis.v7.live-pool-signed-request.v1","operation":"checkpoint",
        "checkpointAccount":checkpoint_account,"serializedTransactionBytes":wire.len(),
        "signedWireSha256":format!("{:x}",Sha256::digest(&wire)),"signature":signature,
        "simulationRequest":{"jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction",
            "params":[wire_base64,{"encoding":"base64","commitment":"confirmed","sigVerify":true,
                "replaceRecentBlockhash":false,"minContextSlot":input.min_context_slot}]},
        "sendRequest":{"jsonrpc":"2.0","id":input.request_id+100_000,"method":"sendTransaction",
            "params":[wire_base64,{"encoding":"base64","skipPreflight":true,
                "preflightCommitment":"confirmed","minContextSlot":input.min_context_slot}]}
    }));
    Ok(())
}
