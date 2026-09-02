use std::{env, fs, str::FromStr};

use anyhow::{ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_keypair::{read_keypair_file, Keypair};
use solana_message::{legacy, VersionedMessage};
use solana_program::{
    hash::Hash,
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    system_instruction,
};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

const SCHEMA: &str = "aspis.v7.txv1-proof-upload-input.v1";
const AUTHENTICATED_COUNTER_SCHEMA: &str =
    "aspis.v7.txv1-proof-upload-for-authenticated-counter-input.v1";
const VERIFIER_PROGRAM: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const HEADER_BYTES: u64 = 40;
const CHUNK_BYTES: usize = 960;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
    rent_lamports: u64,
    payer_keypair: String,
    proof_keypair: String,
    proof_payload: String,
    finalization_mode: Option<String>,
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn signed_request(
    name: String,
    request_id: u64,
    min_context_slot: u64,
    recent_blockhash: Hash,
    payer: &Keypair,
    instructions: Vec<Instruction>,
    signers: &[&Keypair],
) -> Result<Value> {
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &instructions,
        Some(&payer.pubkey()),
        &recent_blockhash,
    ));
    let transaction = VersionedTransaction::try_new(message, signers)
        .map_err(|error| anyhow::anyhow!("sign {name}: {error}"))?;
    let signature = transaction
        .signatures
        .first()
        .context("signed transaction omitted fee-payer signature")?
        .to_string();
    let wire = bincode::serialize(&transaction).context("serialize signed transaction")?;
    ensure!(
        wire.len() < 1_232,
        "{name} exceeds the legacy setup envelope"
    );
    let wire_base64 = BASE64_STANDARD.encode(&wire);
    Ok(json!({
        "name": name,
        "serializedTransactionBytes": wire.len(),
        "signedWireSha256": sha256_hex(&wire),
        "signature": signature,
        "simulationRequest": {
            "jsonrpc": "2.0", "id": request_id, "method": "simulateTransaction",
            "params": [wire_base64, {"encoding":"base64", "commitment":"confirmed",
                "sigVerify":true, "replaceRecentBlockhash":false,
                "minContextSlot":min_context_slot}]
        },
        "sendRequest": {
            "jsonrpc": "2.0", "id": request_id + 100_000, "method": "sendTransaction",
            "params": [wire_base64, {"encoding":"base64", "skipPreflight":true,
                "preflightCommitment":"confirmed", "minContextSlot":min_context_slot}]
        }
    }))
}

fn main() -> Result<()> {
    let input_path = env::args()
        .nth(1)
        .context("usage: build_proof_upload_requests <input.json>")?;
    ensure!(env::args().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    let authenticated_counter = match input.finalization_mode.as_deref() {
        None => {
            ensure!(input.schema == SCHEMA, "wrong input schema");
            false
        }
        Some("authenticated-counter") => {
            ensure!(
                input.schema == AUTHENTICATED_COUNTER_SCHEMA,
                "authenticated-counter upload requires its explicit schema"
            );
            true
        }
        Some(_) => anyhow::bail!("unsupported finalization mode"),
    };
    ensure!(
        input.request_id > 0 && input.min_context_slot > 0,
        "invalid RPC identity"
    );
    let blockhash = Hash::from_str(&input.recent_blockhash).context("invalid blockhash")?;
    let payer = read_keypair_file(&input.payer_keypair)
        .map_err(|error| anyhow::anyhow!("read disposable payer: {error}"))?;
    let proof = read_keypair_file(&input.proof_keypair)
        .map_err(|error| anyhow::anyhow!("read task proof keypair: {error}"))?;
    ensure!(payer.pubkey() != proof.pubkey(), "payer/proof key alias");
    let payload = fs::read(&input.proof_payload).context("read proof payload")?;
    ensure!(!payload.is_empty(), "empty proof payload");
    let payload_len = u32::try_from(payload.len()).context("proof payload too large")?;
    let verifier = Pubkey::from_str(VERIFIER_PROGRAM)?;

    let create = system_instruction::create_account(
        &payer.pubkey(),
        &proof.pubkey(),
        input.rent_lamports,
        HEADER_BYTES + u64::from(payload_len),
        &verifier,
    );
    let mut init_data = vec![0u8];
    init_data.extend_from_slice(&payload_len.to_le_bytes());
    let initialize = Instruction {
        program_id: verifier,
        accounts: vec![
            AccountMeta::new(proof.pubkey(), true),
            AccountMeta::new_readonly(payer.pubkey(), true),
        ],
        data: init_data,
    };
    let mut requests = vec![signed_request(
        "proof-create-initialize".to_string(),
        input.request_id,
        input.min_context_slot,
        blockhash,
        &payer,
        vec![create, initialize],
        &[&payer, &proof],
    )?];

    for (chunk_index, chunk) in payload.chunks(CHUNK_BYTES).enumerate() {
        let offset = u32::try_from(chunk_index * CHUNK_BYTES)?;
        let chunk_len = u32::try_from(chunk.len())?;
        let mut data = Vec::with_capacity(9 + chunk.len());
        data.push(1);
        data.extend_from_slice(&offset.to_le_bytes());
        data.extend_from_slice(&chunk_len.to_le_bytes());
        data.extend_from_slice(chunk);
        requests.push(signed_request(
            format!("proof-upload-{chunk_index:03}"),
            input.request_id + 1 + chunk_index as u64,
            input.min_context_slot,
            blockhash,
            &payer,
            vec![Instruction {
                program_id: verifier,
                accounts: vec![
                    AccountMeta::new(proof.pubkey(), false),
                    AccountMeta::new_readonly(payer.pubkey(), true),
                ],
                data,
            }],
            &[&payer],
        )?);
    }

    if !authenticated_counter {
        requests.push(signed_request(
            "proof-finalize".to_string(),
            input.request_id + 1 + requests.len() as u64,
            input.min_context_slot,
            blockhash,
            &payer,
            vec![Instruction {
                program_id: verifier,
                accounts: vec![
                    AccountMeta::new(proof.pubkey(), false),
                    AccountMeta::new_readonly(payer.pubkey(), true),
                ],
                data: vec![62],
            }],
            &[&payer],
        )?);
    }

    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema": "aspis.v7.txv1-proof-upload-signed-requests.v1",
            "proofAccount": proof.pubkey().to_string(),
            "proofPayloadBytes": payload.len(),
            "proofPayloadSha256": sha256_hex(&payload),
            "uploadChunkBytes": CHUNK_BYTES,
            "finalizationMode": if authenticated_counter { "authenticated-counter" } else { "legacy-seal" },
            "uploadedUnsealed": authenticated_counter,
            "readyForAuthenticatedCounterSeal": authenticated_counter,
            "requestCount": requests.len(),
            "requests": requests
        }))?
    );
    Ok(())
}
