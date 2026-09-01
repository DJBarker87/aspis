use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_pool_wallet_v1::{
    lane_forest_durable_v2::{
        encode_lane_forest_durable_state_v2, ForestFinalizedAppendEventV2,
        ForestFinalizedAppendKindV2, LaneForestDurableStateV2,
    },
    lane_forest_v2::LaneIdV2,
    scan_state::{DepositEventIdV1, FinalizedChainPointV1},
};
use aspis_statement::{
    decode_digest_canonical,
    pool_v1::{pool_v1_note_commitment, pool_v1_pair_forest_deposit_lane_v1},
};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::{json, Value};
use solana_program::pubkey::Pubkey;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    program_id: String,
    proof_account: String,
    provider_set_digest_hex: String,
    initial_master: String,
    initial_lanes: Vec<String>,
    after_deposit_lane: String,
    checkpoint_master: String,
    checkpoint_lanes: Vec<String>,
    checkpoint_account: String,
    registry_account: String,
    registry_entry_account: String,
    secrets_file: String,
    deposit_slot: u64,
    deposit_blockhash: String,
    deposit_signature: String,
    checkpoint_slot: u64,
    checkpoint_blockhash: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Secret { input_note: Note }

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Note { owner_key_hex: String, value: u32, asset_id: u32, salt_hex: String }

struct RpcAccount { address: [u8; 32], owner: [u8; 32], executable: bool, data: Vec<u8> }

fn hex<const N: usize>(value: &str, label: &str) -> Result<[u8; N]> {
    ensure!(value.len() == 2 * N, "{label} has wrong length");
    let mut output = [0_u8; N];
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
            .with_context(|| format!("invalid {label}"))?;
    }
    Ok(output)
}

fn base58<const N: usize>(value: &str, label: &str) -> Result<[u8; N]> {
    let bytes = bs58::decode(value).into_vec().with_context(|| format!("invalid {label}"))?;
    bytes.try_into().map_err(|_| anyhow::anyhow!("{label} has wrong length"))
}

fn rpc(path: &str) -> Result<RpcAccount> {
    let value: Value = serde_json::from_slice(&fs::read(path)?)?;
    let account = &value["result"]["value"];
    let address = value["requestedAddress"].as_str().context("missing requestedAddress")?;
    Ok(RpcAccount {
        address: Pubkey::from_str(address)?.to_bytes(),
        owner: Pubkey::from_str(account["owner"].as_str().context("missing owner")?)?.to_bytes(),
        executable: account["executable"].as_bool().context("missing executable")?,
        data: BASE64.decode(account["data"][0].as_str().context("missing data")?)?,
    })
}

fn account_json(account: &RpcAccount) -> Value {
    json!({"address":Pubkey::new_from_array(account.address).to_string(),
        "owner":Pubkey::new_from_array(account.owner).to_string(),"executable":account.executable,
        "dataBase64":BASE64.encode(&account.data)})
}

fn point(slot: u64, hash: &str) -> Result<FinalizedChainPointV1> {
    FinalizedChainPointV1::new(slot, base58(hash, "blockhash")?)
        .map_err(|error| anyhow::anyhow!("invalid finalized point: {error:?}"))
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(env::args_os().nth(1)
        .context("usage: materialize-live-proof-bundle <input.json> <new-output-dir>")?);
    let output = PathBuf::from(env::args_os().nth(2).context("missing output directory")?);
    ensure!(env::args_os().nth(3).is_none() && !output.exists(), "invalid or existing output");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    ensure!(input.schema == "aspis.v7.live-proof-materialization-input.v1", "wrong schema");
    ensure!(input.initial_lanes.len() == 8 && input.checkpoint_lanes.len() == 8, "wrong lane count");
    let program = Pubkey::from_str(&input.program_id)?;
    let initial_master = rpc(&input.initial_master)?;
    let initial_lanes = input.initial_lanes.iter().map(|path| rpc(path)).collect::<Result<Vec<_>>>()?;
    let initial_lane_values = initial_lanes.iter().map(|account| (account.address, account.data.clone())).collect::<Vec<_>>();
    let mut durable = LaneForestDurableStateV2::from_authenticated_accounts_v2(
        program.to_bytes(), initial_master.address, &initial_master.data, &initial_lane_values, None,
    ).map_err(|error| anyhow::anyhow!("create live durable state: {error:?}"))?;
    let secret: Secret = serde_json::from_slice(&fs::read(&input.secrets_file)?)?;
    ensure!(secret.input_note.value == 1_000 && secret.input_note.asset_id == 77, "wrong input note");
    let owner = decode_digest_canonical(&hex(&secret.input_note.owner_key_hex, "owner key")?)
        .map_err(|error| anyhow::anyhow!("decode owner: {error:?}"))?;
    let salt = decode_digest_canonical(&hex(&secret.input_note.salt_hex, "salt")?)
        .map_err(|error| anyhow::anyhow!("decode salt: {error:?}"))?;
    let commitment = pool_v1_note_commitment(&owner, 1_000, aspis_core::field::M31(77), &salt);
    let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment)
        .map_err(|error| anyhow::anyhow!("route deposit: {error:?}"))?;
    let deposit_point = point(input.deposit_slot, &input.deposit_blockhash)?;
    let event_id = DepositEventIdV1::new(deposit_point, base58(&input.deposit_signature, "signature")?, 1, 0)
        .map_err(|error| anyhow::anyhow!("create deposit event: {error:?}"))?;
    let after_lane = rpc(&input.after_deposit_lane)?;
    let after_lane_image: [u8; aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES] =
        after_lane.data.clone().try_into().map_err(|_| anyhow::anyhow!("wrong lane image size"))?;
    durable.ingest_finalized_append_preselected_v2(ForestFinalizedAppendEventV2 {
        master: initial_master.address, lane_id: LaneIdV2::new(lane_id)
            .map_err(|error| anyhow::anyhow!("invalid lane: {error:?}"))?, pair_leaf_index: 0,
        root_sequence: 1, after_lane_address: after_lane.address, after_lane_image,
        kind: ForestFinalizedAppendKindV2::Deposit { event_id,
            commitment: aspis_statement::encode_digest_canonical(&commitment), encrypted_note: None },
    }, &[event_id]).map_err(|error| anyhow::anyhow!("ingest live deposit: {error:?}"))?;
    let checkpoint_master = rpc(&input.checkpoint_master)?;
    let checkpoint_lanes = input.checkpoint_lanes.iter().map(|path| rpc(path)).collect::<Result<Vec<_>>>()?;
    let checkpoint_lane_values = checkpoint_lanes.iter().map(|account| (account.address, account.data.clone())).collect::<Vec<_>>();
    let checkpoint = rpc(&input.checkpoint_account)?;
    let checkpoint_point = point(input.checkpoint_slot, &input.checkpoint_blockhash)?;
    durable.ingest_finalized_checkpoint_v2(checkpoint_point, checkpoint_master.address,
        &checkpoint_master.data, &checkpoint_lane_values, checkpoint.address, &checkpoint.data)
        .map_err(|error| anyhow::anyhow!("ingest live checkpoint: {error:?}"))?;
    fs::create_dir(&output)?;
    let wallet_file = output.join("wallet-state.bin");
    fs::write(&wallet_file, encode_lane_forest_durable_state_v2(&durable)
        .map_err(|error| anyhow::anyhow!("encode wallet state: {error:?}"))?)?;
    let registry = rpc(&input.registry_account)?;
    let entry = rpc(&input.registry_entry_account)?;
    let bundle = json!({
        "schema":"aspis.v7.live-pool-proof-bundle.v1","programId":input.program_id,
        "proofAccount":input.proof_account,"finalizedPoint":{"slot":input.checkpoint_slot,
            "blockHashHex":hex::encode(checkpoint_point.block_hash())},
        "providerSetDigestHex":input.provider_set_digest_hex,"master":account_json(&checkpoint_master),
        "lanes":checkpoint_lanes.iter().map(account_json).collect::<Vec<_>>(),
        "checkpoint":account_json(&checkpoint),"registry":account_json(&registry),
        "registryEntry":account_json(&entry),"walletStateFile":"wallet-state.bin",
        "outputEvent":{"point":{"slot":input.deposit_slot,"blockHashHex":hex::encode(deposit_point.block_hash())},
            "transactionSignatureHex":hex::encode(event_id.transaction_signature()),
            "instructionIndex":1,"eventIndex":0},"checkpointSequence":0,
        "secretsFile":input.secrets_file,"custody":Value::Null
    });
    fs::write(output.join("live-bundle.json"), serde_json::to_vec_pretty(&bundle)?)?;
    println!("{}", json!({"schema":"aspis.v7.live-proof-materialized.v1",
        "depositLane":lane_id,"checkpointSequence":0,"walletStateBytes":fs::metadata(wallet_file)?.len(),
        "secretValuesPrinted":false}));
    Ok(())
}
