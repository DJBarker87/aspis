use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_pool::{PoolInitializationV1, LEGACY_SPL_TOKEN_PROGRAM_ID};
use aspis_pool_wallet_v1::lane_forest_client_v2::build_pair_forest_initialize_instruction_v2;
use aspis_statement::pool_v1::{
    VerifierPolicyV1, POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
    POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
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

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-live-pool-initialize <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    ensure!(
        input.schema == "aspis.v7.live-pool-initialize-input.v1",
        "wrong input schema"
    );
    ensure!(input.min_context_slot > 0 && input.request_id > 0, "invalid RPC identity");
    let config_path = input_path
        .parent()
        .unwrap_or_else(|| std::path::Path::new("."))
        .join(&input.config);
    let config: Value = serde_json::from_slice(&fs::read(config_path)?)?;
    ensure!(
        config["mainnetReady"] == false
            && config["identitySet"]["auditOnly"] == true
            && config["disposableLiveGenesis"]["enabledOnlyWithDisposableAcknowledgement"] == true,
        "initialization is not pinned to the disposable audit identity"
    );
    let pool_id = config["identitySet"]["programs"]
        .as_array()
        .context("missing programs")?
        .iter()
        .find(|program| program["name"] == "pool")
        .and_then(|program| program["id"].as_str())
        .context("missing Pool program")?;
    let registry_program = config["identitySet"]["bindingAccounts"]
        .as_array()
        .context("missing Registry account")?
        .iter()
        .find(|account| account["name"] == "registry")
        .and_then(|account| account["owner"].as_str())
        .context("missing Registry program")?;
    let mint = config["disposableLiveGenesis"]["mint"]["id"]
        .as_str()
        .context("missing mint")?;
    let payer = read_keypair_file(&input.payer_keypair)
        .map_err(|error| anyhow::anyhow!("read disposable payer: {error}"))?;
    let initialization = PoolInitializationV1 {
        asset_mint: Pubkey::from_str(mint)?.to_bytes(),
        token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
        asset_id: aspis_core::field::M31(77),
        deployment_domain: [5_u8; 32],
        verifier_policy: VerifierPolicyV1 {
            flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
                | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
            registry_program: Pubkey::from_str(registry_program)?.to_bytes(),
            registry_authority: [0_u8; 32],
            policy_binding: hex32(
                config["identitySet"]["policyBindingHex"]
                    .as_str()
                    .context("missing policy binding")?,
                "policy binding",
            )?,
        },
    };
    let instruction = build_pair_forest_initialize_instruction_v2(
        Pubkey::from_str(pool_id)?,
        payer.pubkey(),
        &initialization,
    )
    .map_err(|error| anyhow::anyhow!("build initialize instruction: {error:?}"))?;
    let blockhash = Hash::from_str(&input.recent_blockhash).context("invalid blockhash")?;
    let initialized_accounts: Vec<String> = instruction
        .accounts
        .iter()
        .filter(|account| account.is_writable && !account.is_signer)
        .map(|account| account.pubkey.to_string())
        .collect();
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &[instruction],
        Some(&payer.pubkey()),
        &blockhash,
    ));
    let transaction = VersionedTransaction::try_new(message, &[&payer])
        .map_err(|error| anyhow::anyhow!("sign initialize transaction: {error}"))?;
    let signature = transaction.signatures[0].to_string();
    let wire = bincode::serialize(&transaction)?;
    ensure!(wire.len() < 1_232, "initialize exceeds legacy transaction envelope");
    let wire_hash = format!("{:x}", Sha256::digest(&wire));
    let wire_base64 = BASE64.encode(&wire);
    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema":"aspis.v7.live-pool-signed-request.v1",
            "operation":"initialize",
            "serializedTransactionBytes":wire.len(),
            "signedWireSha256":wire_hash,
            "signature":signature,
            "initializedAccounts":initialized_accounts,
            "simulationRequest":{
                "jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction",
                "params":[wire_base64,{"encoding":"base64","commitment":"confirmed",
                    "sigVerify":true,"replaceRecentBlockhash":false,
                    "minContextSlot":input.min_context_slot}]
            },
            "sendRequest":{
                "jsonrpc":"2.0","id":input.request_id+100_000,"method":"sendTransaction",
                "params":[wire_base64,{"encoding":"base64","skipPreflight":true,
                    "preflightCommitment":"confirmed","minContextSlot":input.min_context_slot}]
            }
        }))?
    );
    Ok(())
}
