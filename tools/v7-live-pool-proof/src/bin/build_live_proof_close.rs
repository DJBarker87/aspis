use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_pool_wallet_v1::verifier_transaction_builder::V7_POOL_PROOF_CLOSE_TAG;
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_keypair::read_keypair_file;
use solana_message::{legacy, VersionedMessage};
use solana_program::{
    hash::Hash,
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    verifier_program: String,
    proof_keypair: String,
    payer_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-live-proof-close <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(input_path)?)?;
    ensure!(
        input.schema == "aspis.v7.live-proof-close-input.v1"
            && input.min_context_slot > 0
            && input.request_id > 0,
        "invalid close input"
    );
    let verifier = Pubkey::from_str(&input.verifier_program)?;
    ensure!(verifier != Pubkey::default(), "zero verifier program");
    let proof = read_keypair_file(&input.proof_keypair)
        .map_err(|error| anyhow::anyhow!("read task-owned proof keypair: {error}"))?;
    let payer = read_keypair_file(&input.payer_keypair)
        .map_err(|error| anyhow::anyhow!("read disposable payer: {error}"))?;
    ensure!(
        proof.pubkey() != payer.pubkey(),
        "proof account aliases payer"
    );
    let instruction = Instruction {
        program_id: verifier,
        accounts: vec![
            AccountMeta::new(proof.pubkey(), true),
            AccountMeta::new(payer.pubkey(), true),
        ],
        data: vec![V7_POOL_PROOF_CLOSE_TAG],
    };
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &[instruction],
        Some(&payer.pubkey()),
        &Hash::from_str(&input.recent_blockhash)?,
    ));
    let transaction = VersionedTransaction::try_new(message, &[&payer, &proof])
        .map_err(|error| anyhow::anyhow!("sign proof close: {error}"))?;
    let signature = transaction.signatures[0].to_string();
    let wire = bincode::serialize(&transaction)?;
    ensure!(wire.len() < 1_232, "proof close exceeds legacy envelope");
    let wire_base64 = BASE64.encode(&wire);
    println!(
        "{}",
        json!({
            "schema":"aspis.v7.live-proof-close-signed.v1",
            "proofAccount":proof.pubkey().to_string(),"refundAccount":payer.pubkey().to_string(),
            "signature":signature,"serializedTransactionBytes":wire.len(),
            "signedWireSha256":format!("{:x}",Sha256::digest(&wire)),
            "simulationRequest":{"jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction",
                "params":[wire_base64,{"encoding":"base64","commitment":"finalized","sigVerify":true,
                    "replaceRecentBlockhash":false,"minContextSlot":input.min_context_slot}]},
            "sendRequest":{"jsonrpc":"2.0","id":input.request_id+100_000,"method":"sendTransaction",
                "params":[wire_base64,{"encoding":"base64","skipPreflight":true,
                    "preflightCommitment":"finalized","maxRetries":0,"minContextSlot":input.min_context_slot}]}
        })
    );
    Ok(())
}
