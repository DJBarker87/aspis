use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_pool::{
    deposit::DepositRequestV1, empty_roots::POOL_V1_PAIR_EMPTY_ROOTS,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_lane_root_page_address,
};
use aspis_pool_wallet_v1::lane_forest_client_v2::build_pair_forest_deposit_instruction_v2;
use aspis_statement::{
    decode_digest_canonical,
    pool_v1::{
        decode_pool_v1_pair_forest_lane_state_v1, decode_pool_v1_pair_forest_master_v1,
        pool_v1_note_commitment, pool_v1_pair_forest_deposit_lane_v1, root_history_location,
    },
};
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
    source_authority_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
    master_account: String,
    lane_accounts: Vec<String>,
    secrets_file: String,
    #[serde(default)]
    expected_next_leaf_index: Option<u64>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Secret {
    schema: String,
    input_note: Note,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Note {
    owner_key_hex: String,
    value: u32,
    asset_id: u32,
    salt_hex: String,
}

fn hex32(value: &str, label: &str) -> Result<[u8; 32]> {
    ensure!(value.len() == 64, "{label} has wrong length");
    let mut output = [0_u8; 32];
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
            .with_context(|| format!("invalid {label}"))?;
    }
    Ok(output)
}

fn rpc_account_data(path: &str) -> Result<Vec<u8>> {
    let value: Value = serde_json::from_slice(&fs::read(path)?)?;
    let encoded = value["result"]["value"]["data"][0]
        .as_str()
        .context("missing RPC account data")?;
    BASE64.decode(encoded).context("invalid account base64")
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-live-pool-deposit <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    let expected_next_leaf_index = match input.schema.as_str() {
        "aspis.v7.live-pool-deposit-input.v1" => {
            ensure!(input.expected_next_leaf_index.is_none(), "unexpected index");
            0
        }
        "aspis.v7.live-pool-staling-deposit-input.v1" => {
            ensure!(input.expected_next_leaf_index.is_none(), "unexpected index");
            1
        }
        "aspis.v7.live-pool-sequential-deposit-input.v1" => input
            .expected_next_leaf_index
            .context("missing expected sequential-deposit index")?,
        _ => anyhow::bail!("wrong input schema"),
    };
    ensure!(
        input.lane_accounts.len() == 8 && input.min_context_slot > 0,
        "invalid live input"
    );
    let config: Value = serde_json::from_slice(&fs::read(&input.config)?)?;
    ensure!(
        config["mainnetReady"] == false && config["identitySet"]["auditOnly"] == true,
        "deposit is not pinned to disposable audit identities"
    );
    let pool_id = config["identitySet"]["programs"]
        .as_array()
        .context("missing programs")?
        .iter()
        .find(|program| program["name"] == "pool")
        .and_then(|program| program["id"].as_str())
        .context("missing Pool program")?;
    let source = config["disposableLiveGenesis"]["sourceTokenAccount"]
        .as_str()
        .context("missing source token account")?;
    let master = decode_pool_v1_pair_forest_master_v1(&rpc_account_data(&input.master_account)?)
        .map_err(|error| anyhow::anyhow!("decode live master: {error:?}"))?;
    let secret: Secret = serde_json::from_slice(&fs::read(&input.secrets_file)?)?;
    ensure!(
        secret.schema == "aspis.v7.live-pool-proof-secrets.v1",
        "wrong secret schema"
    );
    ensure!(
        secret.input_note.value == 1_000 && secret.input_note.asset_id == 77,
        "unexpected deposit note value or asset"
    );
    let owner_key = decode_digest_canonical(&hex32(&secret.input_note.owner_key_hex, "owner key")?)
        .map_err(|error| anyhow::anyhow!("decode owner key: {error:?}"))?;
    let salt = decode_digest_canonical(&hex32(&secret.input_note.salt_hex, "salt")?)
        .map_err(|error| anyhow::anyhow!("decode salt: {error:?}"))?;
    let commitment = pool_v1_note_commitment(&owner_key, 1_000, master.identity.asset_id, &salt);
    let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment)
        .map_err(|error| anyhow::anyhow!("route deposit: {error:?}"))?;
    let lane = decode_pool_v1_pair_forest_lane_state_v1(
        &rpc_account_data(&input.lane_accounts[usize::from(lane_id)])?,
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(|error| anyhow::anyhow!("decode selected live lane: {error:?}"))?;
    ensure!(
        lane.lane_id == lane_id && lane.tree.next_leaf_index == expected_next_leaf_index,
        "selected deposit lane does not have the required authenticated index"
    );
    let payer = read_keypair_file(&input.payer_keypair)
        .map_err(|error| anyhow::anyhow!("read disposable payer: {error}"))?;
    let source_authority = read_keypair_file(&input.source_authority_keypair)
        .map_err(|error| anyhow::anyhow!("read disposable source authority: {error}"))?;
    ensure!(
        source_authority.pubkey() != payer.pubkey(),
        "source authority aliases payer"
    );
    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(
        lane.tree
            .next_leaf_index
            .checked_add(1)
            .context("deposit index overflow")?,
    );
    let page_mode = if lane.tree.next_leaf_index == 0 {
        "genesis"
    } else if current_location.page_number == next_location.page_number {
        "same-page"
    } else {
        "rollover"
    };
    let page_payer = (page_mode != "same-page").then_some(payer.pubkey());
    let pool_program = Pubkey::from_str(pool_id)?;
    let master_address = Pubkey::new_from_array(master.identity.pool);
    let lane_address = pool_v1_pair_forest_lane_address(&pool_program, &master_address, lane_id)
        .map_err(|error| anyhow::anyhow!("derive lane: {error:?}"))?
        .0;
    let current_page_address = pool_v1_pair_forest_lane_root_page_address(
        &pool_program,
        &master_address,
        lane_id,
        current_location.page_number,
    )
    .map_err(|error| anyhow::anyhow!("derive current page: {error:?}"))?
    .0;
    let successor_page_address = pool_v1_pair_forest_lane_root_page_address(
        &pool_program,
        &master_address,
        lane_id,
        next_location.page_number,
    )
    .map_err(|error| anyhow::anyhow!("derive successor page: {error:?}"))?
    .0;
    let instruction = build_pair_forest_deposit_instruction_v2(
        pool_program,
        &master,
        &lane,
        Pubkey::from_str(source)?,
        source_authority.pubkey(),
        page_payer,
        &DepositRequestV1 {
            owner_key,
            amount: 1_000,
            salt,
            encrypted_note_payload: &[],
        },
    )
    .map_err(|error| anyhow::anyhow!("build deposit instruction: {error:?}"))?;
    let blockhash = Hash::from_str(&input.recent_blockhash)?;
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(1_400_000),
            instruction,
        ],
        Some(&payer.pubkey()),
        &blockhash,
    ));
    let transaction = VersionedTransaction::try_new(message, &[&payer, &source_authority])
        .map_err(|error| anyhow::anyhow!("sign deposit: {error}"))?;
    let signature = transaction.signatures[0].to_string();
    let wire = bincode::serialize(&transaction)?;
    ensure!(wire.len() < 1_232, "deposit exceeds legacy envelope");
    let wire_base64 = BASE64.encode(&wire);
    println!(
        "{}",
        json!({
            "schema":"aspis.v7.live-pool-signed-request.v1","operation":"deposit",
            "selectedLane":lane_id,"sourceNextLeafIndex":lane.tree.next_leaf_index,
            "successorNextLeafIndex":lane.tree.next_leaf_index + 1,"pageMode":page_mode,
            "laneAccount":lane_address.to_string(),
            "currentPageAccount":current_page_address.to_string(),
            "successorPageAccount":successor_page_address.to_string(),
            "serializedTransactionBytes":wire.len(),
            "signedWireSha256":format!("{:x}",Sha256::digest(&wire)),"signature":signature,
            "simulationRequest":{"jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction",
                "params":[wire_base64,{"encoding":"base64","commitment":"confirmed","sigVerify":true,
                    "replaceRecentBlockhash":false,"minContextSlot":input.min_context_slot}]},
            "sendRequest":{"jsonrpc":"2.0","id":input.request_id+100_000,"method":"sendTransaction",
                "params":[wire_base64,{"encoding":"base64","skipPreflight":true,
                    "preflightCommitment":"confirmed","minContextSlot":input.min_context_slot}]}
        })
    );
    Ok(())
}
