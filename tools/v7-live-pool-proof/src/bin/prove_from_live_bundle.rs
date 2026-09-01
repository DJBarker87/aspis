use std::{
    env, fs,
    path::{Path, PathBuf},
    str::FromStr,
    time::Instant,
};

use anyhow::{bail, ensure, Context, Result};
use aspis_pool_wallet_v1::{
    finalized_indexer::SolanaRpcCommitmentV1,
    lane_forest_client_v2::{
        select_pair_forest_spend_profile_v2, FinalizedPairForestProfileAccountsV2,
        PairForestSpendProfileRequestV2,
    },
    lane_forest_durable_v2::decode_lane_forest_durable_state_v2,
    lane_forest_rpc_v2::FinalizedForestAccountV2,
    live_pool_witness_adapter_v2::{
        authenticate_live_pair_forest_snapshot_v2, build_live_pair_forest_transfer_plan_v2,
        build_live_pair_forest_withdrawal_plan_v2, LivePairForestMembershipSourceV2,
        LiveWithdrawalCustodyAccountsV2,
    },
    scan_state::{DepositEventIdV1, FinalizedChainPointV1},
    NoteOpeningV1,
};
use aspis_statement::pool_v1::{
    encode_pool_v1_pair_verified_afterstate_v1, POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
    V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING, V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
};
use aspis_v7_live_pool_proof::{
    prove_live_pair_forest_transfer_v1, prove_live_pair_forest_withdrawal_v1,
};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

const SCHEMA: &str = "aspis.v7.live-pool-proof-bundle.v1";
const SECRET_SCHEMA: &str = "aspis.v7.live-pool-proof-secrets.v1";

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct PointInput {
    slot: u64,
    block_hash_hex: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct AccountInput {
    address: String,
    owner: String,
    executable: bool,
    data_base64: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct EventInput {
    point: PointInput,
    transaction_signature_hex: String,
    instruction_index: u16,
    event_index: u16,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct CustodyInput {
    mint: AccountInput,
    vault: AccountInput,
    destination: AccountInput,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct BundleInput {
    schema: String,
    program_id: String,
    proof_account: String,
    finalized_point: PointInput,
    provider_set_digest_hex: String,
    master: AccountInput,
    lanes: Vec<AccountInput>,
    checkpoint: AccountInput,
    registry: AccountInput,
    registry_entry: AccountInput,
    wallet_state_file: String,
    output_event: EventInput,
    checkpoint_sequence: u64,
    secrets_file: String,
    custody: Option<CustodyInput>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct NoteInput {
    owner_key_hex: String,
    value: u32,
    asset_id: u32,
    salt_hex: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SecretInput {
    schema: String,
    operation: String,
    nullifier_key_hex: String,
    input_note: NoteInput,
    recipient_note: Option<NoteInput>,
    change_note: NoteInput,
    withdrawal_amount: Option<u32>,
    withdrawal_destination: Option<String>,
}

fn hex<const N: usize>(value: &str, label: &str) -> Result<[u8; N]> {
    ensure!(value.len() == 2 * N, "{label} has wrong hex length");
    let mut output = [0u8; N];
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
            .with_context(|| format!("invalid {label} hex"))?;
    }
    Ok(output)
}

fn point(value: PointInput) -> Result<FinalizedChainPointV1> {
    FinalizedChainPointV1::new(value.slot, hex(&value.block_hash_hex, "block hash")?)
        .map_err(|error| anyhow::anyhow!("invalid finalized point: {error:?}"))
}

fn account(value: AccountInput) -> Result<FinalizedForestAccountV2> {
    Ok(FinalizedForestAccountV2 {
        address: Pubkey::from_str(&value.address)
            .context("invalid account address")?
            .to_bytes(),
        owner: Pubkey::from_str(&value.owner)
            .context("invalid account owner")?
            .to_bytes(),
        executable: value.executable,
        data: BASE64
            .decode(value.data_base64)
            .context("invalid account base64")?,
    })
}

fn note(value: NoteInput) -> Result<NoteOpeningV1> {
    NoteOpeningV1::new(
        hex(&value.owner_key_hex, "note owner key")?,
        value.value,
        value.asset_id,
        hex(&value.salt_hex, "note salt")?,
    )
    .map_err(|error| anyhow::anyhow!("invalid note opening: {error:?}"))
}

fn resolve(base: &Path, value: &str) -> PathBuf {
    let path = Path::new(value);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn main() -> Result<()> {
    let mut args = env::args_os().skip(1);
    let manifest_path = PathBuf::from(args.next().context(
        "usage: prove-from-live-bundle <bundle.json> <new-output-dir> <new-nonce-ledger-dir>",
    )?);
    let output_dir = PathBuf::from(args.next().context("missing output directory")?);
    let nonce_dir = PathBuf::from(args.next().context("missing nonce ledger directory")?);
    ensure!(args.next().is_none(), "unexpected extra argument");
    ensure!(!output_dir.exists(), "refusing to overwrite proof output");
    ensure!(
        !nonce_dir.exists(),
        "refusing to reuse nonce ledger directory"
    );
    let base = manifest_path.parent().unwrap_or_else(|| Path::new("."));
    let bundle: BundleInput = serde_json::from_slice(&fs::read(&manifest_path)?)?;
    ensure!(bundle.schema == SCHEMA, "wrong bundle schema");
    let secrets_path = resolve(base, &bundle.secrets_file);
    let secrets: SecretInput =
        serde_json::from_slice(&fs::read(&secrets_path).context("read task-owned secret file")?)?;
    ensure!(secrets.schema == SECRET_SCHEMA, "wrong secret schema");

    let program = Pubkey::from_str(&bundle.program_id).context("invalid Pool program")?;
    let proof_account = Pubkey::from_str(&bundle.proof_account)
        .context("invalid proof account")?
        .to_bytes();
    let finalized_point = point(bundle.finalized_point)?;
    let provider_set_digest = hex(&bundle.provider_set_digest_hex, "provider set digest")?;
    let master = account(bundle.master)?;
    let lanes = bundle
        .lanes
        .into_iter()
        .map(account)
        .collect::<Result<Vec<_>>>()?;
    let checkpoint = account(bundle.checkpoint)?;
    let registry = account(bundle.registry)?;
    let registry_entry = account(bundle.registry_entry)?;
    let registry_program = Pubkey::new_from_array(registry.owner);
    let master_value =
        aspis_pool_wallet_v1::lane_forest_durable_v2::authenticate_forest_master_account_v2(
            program.to_bytes(),
            master.address,
            &master.data,
        )
        .map_err(|error| {
            anyhow::anyhow!("authenticate master before Registry selection: {error:?}")
        })?;
    let selection = select_pair_forest_spend_profile_v2(
        registry_program,
        &master_value.value,
        PairForestSpendProfileRequestV2 {
            profile_binding: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
            release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        },
        &FinalizedPairForestProfileAccountsV2 {
            point: finalized_point,
            context_slot: finalized_point.slot(),
            commitment: SolanaRpcCommitmentV1::Finalized,
            provider_set_digest,
            registry,
            entry: registry_entry,
        },
    )
    .map_err(|error| anyhow::anyhow!("authenticate Registry selection: {error:?}"))?;
    let snapshot = authenticate_live_pair_forest_snapshot_v2(
        program.to_bytes(),
        finalized_point,
        provider_set_digest,
        &master,
        &lanes,
        &checkpoint,
        selection,
    )
    .map_err(|error| anyhow::anyhow!("authenticate live Pool snapshot: {error:?}"))?;

    let durable =
        decode_lane_forest_durable_state_v2(&fs::read(resolve(base, &bundle.wallet_state_file))?)
            .map_err(|error| anyhow::anyhow!("decode authenticated wallet state: {error:?}"))?;
    ensure!(
        durable.program_id() == &program.to_bytes(),
        "wallet/Pool program mismatch"
    );
    let event_point = point(bundle.output_event.point)?;
    let output_event = DepositEventIdV1::new(
        event_point,
        hex(
            &bundle.output_event.transaction_signature_hex,
            "transaction signature",
        )?,
        bundle.output_event.instruction_index,
        bundle.output_event.event_index,
    )
    .map_err(|error| anyhow::anyhow!("invalid output event identity: {error:?}"))?;
    let source = LivePairForestMembershipSourceV2::from(
        durable
            .authenticated_spend_membership_v2(output_event, bundle.checkpoint_sequence)
            .map_err(|error| anyhow::anyhow!("export retained membership: {error:?}"))?,
    );
    let nullifier_key = hex(&secrets.nullifier_key_hex, "nullifier key")?;
    let input_note = note(secrets.input_note)?;
    let change_note = note(secrets.change_note)?;
    let started = Instant::now();

    let (operation, asq8, asf8, asr8, candidate, built) = match secrets.operation.as_str() {
        "transfer" => {
            ensure!(
                bundle.custody.is_none(),
                "transfer bundle unexpectedly has custody accounts"
            );
            let recipient = note(
                secrets
                    .recipient_note
                    .context("transfer recipient note missing")?,
            )?;
            let plan = build_live_pair_forest_transfer_plan_v2(
                &snapshot,
                &source,
                &input_note,
                &nullifier_key,
                &recipient,
                &change_note,
                proof_account,
            )
            .map_err(|error| anyhow::anyhow!("build live transfer plan: {error:?}"))?;
            let candidate =
                encode_pool_v1_pair_verified_afterstate_v1(&plan.transition.candidate_afterstate)
                    .map_err(|error| anyhow::anyhow!("encode candidate afterstate: {error:?}"))?
                    .to_vec();
            let built = prove_live_pair_forest_transfer_v1(&plan, &nonce_dir)
                .map_err(|error| anyhow::anyhow!("prove live transfer: {error:?}"))?;
            (
                "transfer",
                plan.asq8.to_vec(),
                plan.asf8.to_vec(),
                plan.expected_asr8.to_vec(),
                candidate,
                built,
            )
        }
        "withdrawal" => {
            ensure!(
                secrets.recipient_note.is_none(),
                "withdrawal has recipient note"
            );
            let custody = bundle
                .custody
                .context("withdrawal custody accounts missing")?;
            let mint = account(custody.mint)?;
            let vault = account(custody.vault)?;
            let destination = account(custody.destination)?;
            let destination_address = Pubkey::from_str(
                &secrets
                    .withdrawal_destination
                    .context("withdrawal destination missing")?,
            )
            .context("invalid withdrawal destination")?
            .to_bytes();
            let plan = build_live_pair_forest_withdrawal_plan_v2(
                &snapshot,
                &source,
                &input_note,
                &nullifier_key,
                secrets
                    .withdrawal_amount
                    .context("withdrawal amount missing")?,
                destination_address,
                &change_note,
                LiveWithdrawalCustodyAccountsV2 {
                    mint: &mint,
                    vault: &vault,
                    destination: &destination,
                },
                proof_account,
            )
            .map_err(|error| anyhow::anyhow!("build live withdrawal plan: {error:?}"))?;
            let candidate =
                encode_pool_v1_pair_verified_afterstate_v1(&plan.transition.candidate_afterstate)
                    .map_err(|error| anyhow::anyhow!("encode candidate afterstate: {error:?}"))?
                    .to_vec();
            let built = prove_live_pair_forest_withdrawal_v1(&plan, &nonce_dir)
                .map_err(|error| anyhow::anyhow!("prove live withdrawal: {error:?}"))?;
            (
                "withdrawal",
                plan.asq8.to_vec(),
                plan.asf8.to_vec(),
                plan.expected_asr8.to_vec(),
                candidate,
                built,
            )
        }
        _ => bail!("operation must be transfer or withdrawal"),
    };
    ensure!(
        built.proof.pow_valid,
        "production prover returned unmined work"
    );
    fs::create_dir(&output_dir)?;
    fs::write(output_dir.join("asq8.bin"), &asq8)?;
    fs::write(output_dir.join("asf8.bin"), &asf8)?;
    fs::write(output_dir.join("expected-asr8.bin"), &asr8)?;
    fs::write(output_dir.join("candidate-afterstate.bin"), &candidate)?;
    fs::write(output_dir.join("proof-body.bin"), &built.proof.bytes)?;
    fs::write(output_dir.join("proof-payload.bin"), &built.proof_payload)?;
    let metadata = json!({
        "schema":"aspis.v7.live-pool-proof-output.v1", "operation":operation,
        "proofAccount":bundle.proof_account, "attemptId":bundle.proof_account,
        "programId":bundle.program_id, "finalizedSlot":finalized_point.slot(),
        "checkpointSequence":bundle.checkpoint_sequence,
        "sources":{
            "master":Pubkey::new_from_array(master.address).to_string(),
            "checkpoint":Pubkey::new_from_array(checkpoint.address).to_string(),
            "lanes":lanes.iter().map(|value| Pubkey::new_from_array(value.address).to_string()).collect::<Vec<_>>(),
            "walletStateSha256":sha256_hex(&fs::read(resolve(base, &bundle.wallet_state_file))?),
            "secretsFileCommitted":false
        },
        "asq8":{"bytes":asq8.len(),"sha256":sha256_hex(&asq8)},
        "asf8":{"bytes":asf8.len(),"sha256":sha256_hex(&asf8)},
        "expectedAsr8":{"bytes":asr8.len(),"sha256":sha256_hex(&asr8)},
        "proof":{"bytes":built.proof.bytes.len(),"sha256":sha256_hex(&built.proof.bytes),
            "powValid":built.proof.pow_valid,"wireFormat":"tag73-canonical-fixed-audit",
            "canonicalFixedDeltaBytes":aspis_core::v7_fixed_canonical_audit::V7_CANONICAL_FIXED_DELTA_BYTES},
        "proofPayload":{"bytes":built.proof_payload.len(),"sha256":sha256_hex(&built.proof_payload)},
        "elapsedMillis":started.elapsed().as_millis(),
        "deterministicFixtureEntropy":false,"verifierBypass":false,"trustedResultAccount":false
    });
    fs::write(
        output_dir.join("proof.json"),
        serde_json::to_vec_pretty(&metadata)?,
    )?;
    println!(
        "{}",
        serde_json::to_string(&json!({
            "operation":operation,"proofAccount":bundle.proof_account,
            "proofPayloadBytes":built.proof_payload.len(),"proofPayloadSha256":sha256_hex(&built.proof_payload)
        }))?
    );
    Ok(())
}
