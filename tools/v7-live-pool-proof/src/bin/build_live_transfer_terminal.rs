use std::{
    convert::Infallible,
    env, fs,
    path::{Path, PathBuf},
    str::FromStr,
};

use anyhow::{ensure, Context, Result};
use aspis_pool_wallet_v1::{
    derive_viewing_keypair_v1, encrypt_note_v1,
    finalized_indexer::SolanaRpcCommitmentV1,
    lane_forest_client_v2::{
        select_pair_forest_spend_profile_v2, FinalizedPairForestProfileAccountsV2,
        PairForestSpendProfileRequestV2,
    },
    lane_forest_durable_v2::{
        authenticate_forest_lane_account_v2, authenticate_forest_master_account_v2,
    },
    lane_forest_rpc_v2::FinalizedForestAccountV2,
    lane_forest_transaction_v1::{
        build_exact_pair_forest_v1_carrier_transaction_v2,
        build_pair_forest_terminal_instruction_v1_4k_v2,
        validate_signed_pair_forest_v1_carrier_transaction_v2, PairForestV1TransactionConfigV2,
    },
    tx_v1_ciphertext_carrier_v2::TxV1CiphertextCarrierV2,
    NoteContextV1, NoteOpeningV1,
};
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_pair_forest_terminal_request_v1, pool_v1_pair_forest_output_lane_v1,
        PoolV1PairForestTerminalPaymentV1, POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING, V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use hpke::rand_core::{TryCryptoRng, TryRng};
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_keypair::read_keypair_file;
use solana_program::pubkey::Pubkey;
use solana_signature_v1::Signature as V1Signature;
use solana_signer::Signer;
use solana_transaction_v1::versioned::VersionedTransaction as V1VersionedTransaction;

struct OsEntropy;
impl TryRng for OsEntropy {
    type Error = Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut b = [0; 4];
        self.try_fill_bytes(&mut b)?;
        Ok(u32::from_le_bytes(b))
    }
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut b = [0; 8];
        self.try_fill_bytes(&mut b)?;
        Ok(u64::from_le_bytes(b))
    }
    fn try_fill_bytes(&mut self, destination: &mut [u8]) -> Result<(), Self::Error> {
        getrandom::getrandom(destination).expect("operating-system entropy unavailable");
        Ok(())
    }
}
impl TryCryptoRng for OsEntropy {}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    bundle: String,
    asq8: String,
    payer_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Bundle {
    program_id: String,
    proof_account: String,
    finalized_point: Point,
    provider_set_digest_hex: String,
    master: Account,
    lanes: Vec<Account>,
    registry: Account,
    registry_entry: Account,
    secrets_file: String,
    custody: Option<Custody>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Custody {
    mint: Account,
    vault: Account,
    destination: Account,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Point {
    slot: u64,
    block_hash_hex: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Account {
    address: String,
    owner: String,
    executable: bool,
    data_base64: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Secret {
    operation: String,
    recipient_note: Option<Note>,
    change_note: Note,
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
    ensure!(value.len() == 64, "{label} length");
    let mut out = [0; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&value[i * 2..i * 2 + 2], 16)?;
    }
    Ok(out)
}
fn account(value: &Account) -> Result<FinalizedForestAccountV2> {
    Ok(FinalizedForestAccountV2 {
        address: Pubkey::from_str(&value.address)?.to_bytes(),
        owner: Pubkey::from_str(&value.owner)?.to_bytes(),
        executable: value.executable,
        data: BASE64.decode(&value.data_base64)?,
    })
}
fn note(value: Note) -> Result<NoteOpeningV1> {
    NoteOpeningV1::new(
        hex32(&value.owner_key_hex, "owner")?,
        value.value,
        value.asset_id,
        hex32(&value.salt_hex, "salt")?,
    )
    .map_err(|e| anyhow::anyhow!("invalid output note: {e:?}"))
}
fn resolve(base: &Path, value: &str) -> PathBuf {
    let path = Path::new(value);
    if path.is_absolute() {
        path.to_owned()
    } else {
        base.join(path)
    }
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-live-transfer-terminal <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    ensure!(
        (input.schema == "aspis.v7.live-transfer-terminal-input.v1"
            || input.schema == "aspis.v7.live-terminal-input.v1")
            && input.min_context_slot > 0,
        "wrong input"
    );
    let bundle_path = resolve(input_path.parent().unwrap_or(Path::new(".")), &input.bundle);
    let base = bundle_path.parent().unwrap_or(Path::new("."));
    let bundle: Bundle = serde_json::from_slice(&fs::read(&bundle_path)?)?;
    ensure!(bundle.lanes.len() == 8, "wrong lane count");
    let program = Pubkey::from_str(&bundle.program_id)?;
    let master_account = account(&bundle.master)?;
    let master = authenticate_forest_master_account_v2(
        program.to_bytes(),
        master_account.address,
        &master_account.data,
    )
    .map_err(|e| anyhow::anyhow!("authenticate master: {e:?}"))?;
    let registry = account(&bundle.registry)?;
    let entry = account(&bundle.registry_entry)?;
    let point = aspis_pool_wallet_v1::scan_state::FinalizedChainPointV1::new(
        bundle.finalized_point.slot,
        hex32(&bundle.finalized_point.block_hash_hex, "blockhash")?,
    )
    .map_err(|e| anyhow::anyhow!("point: {e:?}"))?;
    let provider = hex32(&bundle.provider_set_digest_hex, "provider")?;
    let profile = select_pair_forest_spend_profile_v2(
        Pubkey::new_from_array(registry.owner),
        &master.value,
        PairForestSpendProfileRequestV2 {
            profile_binding: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
            release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        },
        &FinalizedPairForestProfileAccountsV2 {
            point,
            context_slot: point.slot(),
            commitment: SolanaRpcCommitmentV1::Finalized,
            provider_set_digest: provider,
            registry,
            entry,
        },
    )
    .map_err(|e| anyhow::anyhow!("select profile: {e:?}"))?;
    let asq8 = fs::read(resolve(
        input_path.parent().unwrap_or(Path::new(".")),
        &input.asq8,
    ))?;
    let request = decode_pool_v1_pair_forest_terminal_request_v1(&asq8)
        .map_err(|e| anyhow::anyhow!("decode ASQ8: {e:?}"))?;
    let lane_id = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
        .map_err(|e| anyhow::anyhow!("output lane: {e:?}"))?;
    let lane_account = account(&bundle.lanes[usize::from(lane_id)])?;
    let lane = authenticate_forest_lane_account_v2(
        program.to_bytes(),
        master.address,
        aspis_pool_wallet_v1::lane_forest_v2::LaneIdV2::new(lane_id)
            .map_err(|e| anyhow::anyhow!("lane: {e:?}"))?,
        lane_account.address,
        &lane_account.data,
    )
    .map_err(|e| anyhow::anyhow!("authenticate lane: {e:?}"))?;
    let payer =
        read_keypair_file(&input.payer_keypair).map_err(|e| anyhow::anyhow!("payer: {e}"))?;
    let proof = Pubkey::from_str(&bundle.proof_account)?;
    let terminal = build_pair_forest_terminal_instruction_v1_4k_v2(
        program,
        &master.value,
        &lane.value,
        profile,
        payer.pubkey(),
        proof,
        &request,
    )
    .map_err(|e| anyhow::anyhow!("terminal instruction: {e:?}"))?;
    let terminal_accounts = terminal
        .accounts
        .iter()
        .map(|account| account.pubkey.to_string())
        .collect::<Vec<_>>();
    let marker_account = terminal.accounts[4].pubkey.to_string();
    let secrets: Secret = serde_json::from_slice(&fs::read(resolve(base, &bundle.secrets_file))?)?;
    let change = note(secrets.change_note)?;
    let pair_index = lane.value.tree.next_leaf_index;
    let mut rng = OsEntropy;
    let mut seed = [0; 32];
    let (operation, recipient_cipher, change_commitment, change_note_index) = match &request.public
    {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            ensure!(secrets.operation == "transfer", "secret operation mismatch");
            ensure!(
                bundle.custody.is_none(),
                "transfer bundle unexpectedly has custody accounts"
            );
            let recipient = note(secrets.recipient_note.context("recipient missing")?)?;
            let recipient_context = NoteContextV1::new(
                master.address,
                master.value.identity.deployment_domain,
                pair_index * 2,
                encode_digest_canonical(&public.recipient_commitment),
            )
            .map_err(|e| anyhow::anyhow!("recipient context: {e:?}"))?;
            getrandom::getrandom(&mut seed)?;
            let (_, recipient_view) = derive_viewing_keypair_v1(&seed)
                .map_err(|e| anyhow::anyhow!("recipient view: {e:?}"))?;
            let ciphertext =
                encrypt_note_v1(&mut rng, &recipient_view, &recipient_context, &recipient)
                    .map_err(|e| anyhow::anyhow!("encrypt recipient: {e:?}"))?;
            (
                "transfer",
                Some(ciphertext),
                public.change_commitment,
                pair_index * 2 + 1,
            )
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            ensure!(
                secrets.operation == "withdrawal",
                "secret operation mismatch"
            );
            ensure!(
                secrets.recipient_note.is_none(),
                "withdrawal recipient unexpectedly present"
            );
            let custody = bundle
                .custody
                .as_ref()
                .context("withdrawal custody accounts missing")?;
            ensure!(
                custody.mint.address
                    == Pubkey::new_from_array(master.value.identity.asset_mint).to_string(),
                "withdrawal mint mismatch"
            );
            ensure!(
                custody.destination.address
                    == Pubkey::new_from_array(public.destination_token_account).to_string(),
                "withdrawal destination mismatch"
            );
            ensure!(
                terminal
                    .accounts
                    .iter()
                    .any(|meta| meta.pubkey.to_string() == custody.vault.address),
                "withdrawal vault missing from terminal accounts"
            );
            ensure!(
                terminal
                    .accounts
                    .iter()
                    .any(|meta| meta.pubkey.to_string() == custody.destination.address),
                "withdrawal destination missing from terminal accounts"
            );
            ("withdrawal", None, public.change_commitment, pair_index * 2)
        }
    };
    getrandom::getrandom(&mut seed)?;
    let (_, change_view) =
        derive_viewing_keypair_v1(&seed).map_err(|e| anyhow::anyhow!("change view: {e:?}"))?;
    seed.fill(0);
    let change_context = NoteContextV1::new(
        master.address,
        master.value.identity.deployment_domain,
        change_note_index,
        encode_digest_canonical(&change_commitment),
    )
    .map_err(|e| anyhow::anyhow!("change context: {e:?}"))?;
    let change_cipher = encrypt_note_v1(&mut rng, &change_view, &change_context, &change)
        .map_err(|e| anyhow::anyhow!("encrypt change: {e:?}"))?;
    let carrier = TxV1CiphertextCarrierV2::from_terminal_v2(
        &request,
        proof.to_bytes(),
        0,
        1,
        recipient_cipher,
        change_cipher,
    )
    .map_err(|e| anyhow::anyhow!("carrier: {e:?}"))?;
    let recent = bs58::decode(&input.recent_blockhash).into_vec()?;
    let recent: [u8; 32] = recent
        .try_into()
        .map_err(|_| anyhow::anyhow!("blockhash length"))?;
    let expected = build_exact_pair_forest_v1_carrier_transaction_v2(
        &carrier,
        payer.pubkey(),
        &terminal,
        payer.pubkey(),
        recent,
        PairForestV1TransactionConfigV2 {
            priority_fee_lamports: 0,
            compute_unit_limit: 1_300_000,
            loaded_accounts_data_size_limit: 8 * 1024 * 1024,
            heap_size: 256 * 1024,
        },
        &[],
    )
    .map_err(|e| anyhow::anyhow!("build TxV1: {e:?}"))?;
    ensure!(
        expected.required_signatures_v2() == 1,
        "unexpected signatures"
    );
    let mut transaction: V1VersionedTransaction =
        wincode::deserialize(expected.placeholder_signature_wire_v2())?;
    let message = transaction.message.serialize();
    let signed = payer.sign_message(&message);
    let bytes: [u8; 64] = signed.as_ref().try_into()?;
    transaction.signatures[0] = V1Signature::from(bytes);
    let wire = wincode::serialize(&transaction)?;
    validate_signed_pair_forest_v1_carrier_transaction_v2(&expected, &wire)
        .map_err(|e| anyhow::anyhow!("validate signed TxV1: {e:?}"))?;
    ensure!(
        wire.len() < 4096 && wire.len() <= 3500,
        "TxV1 size policy failed"
    );
    let wire64 = BASE64.encode(&wire);
    let signature = transaction.signatures[0].to_string();
    println!(
        "{}",
        json!({"schema":"aspis.v7.live-terminal-signed.v1","operation":operation,"signature":signature,
        "selectedLane":lane_id,"serializedTransactionBytes":wire.len(),"signedWireSha256":format!("{:x}",Sha256::digest(&wire)),
        "instructionCount":2,"terminalInstructionCount":1,"ciphertextCarrierRealHpke":true,
        "terminalAccounts":terminal_accounts,"markerAccount":marker_account,
        "simulationRequest":{"jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction","params":[wire64,{"encoding":"base64","commitment":"finalized","sigVerify":true,"replaceRecentBlockhash":false,"minContextSlot":input.min_context_slot,"innerInstructions":true}]},
        "sendRequest":{"jsonrpc":"2.0","id":input.request_id+100000,"method":"sendTransaction","params":[wire64,{"encoding":"base64","skipPreflight":true,"preflightCommitment":"finalized","maxRetries":0,"minContextSlot":input.min_context_slot}]}})
    );
    Ok(())
}
