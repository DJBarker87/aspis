use std::{
    env,
    fs::OpenOptions,
    io::Write,
    os::unix::fs::OpenOptionsExt,
    path::PathBuf,
};

use anyhow::{ensure, Context, Result};
use aspis_pool_wallet_v1::{wallet_transition::derive_note_nullifier_v1, NoteOpeningV1};
use aspis_statement::{
    decode_digest_canonical, derive_owner_key, encode_digest_canonical,
    pool_v1::{
        pool_v1_note_commitment, pool_v1_pair_forest_deposit_lane_v1,
        pool_v1_pair_forest_output_lane_v1,
    },
};
use serde_json::json;

fn random_digest_bytes() -> Result<[u8; 32]> {
    let mut random = [0_u8; 32];
    getrandom::getrandom(&mut random)?;
    for limb in random.chunks_exact_mut(4) {
        let value = u32::from_le_bytes(limb.try_into().unwrap()) & 0x3fff_ffff;
        limb.copy_from_slice(&value.to_le_bytes());
    }
    decode_digest_canonical(&random)
        .map_err(|error| anyhow::anyhow!("generated noncanonical digest: {error:?}"))?;
    Ok(random)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn note(owner_key: [u8; 32], value: u32, salt: [u8; 32]) -> serde_json::Value {
    json!({"ownerKeyHex":hex(&owner_key),"value":value,"assetId":77,"saltHex":hex(&salt)})
}

fn main() -> Result<()> {
    let operation = env::args().nth(1).context(
        "usage: create-live-operation-secrets <transfer|withdrawal> <new-secret-file>",
    )?;
    let output = PathBuf::from(env::args_os().nth(2).context("missing secret output")?);
    ensure!(env::args_os().nth(3).is_none(), "unexpected extra argument");
    ensure!(operation == "transfer" || operation == "withdrawal", "invalid operation");
    let (nullifier_key, owner_key, input_salt, input_commitment, lane, attempts) =
        (1_u32..=1_024)
            .find_map(|attempts| {
                let nullifier_key = random_digest_bytes().ok()?;
                let decoded_nullifier = decode_digest_canonical(&nullifier_key).ok()?;
                let owner_key = encode_digest_canonical(&derive_owner_key(&decoded_nullifier));
                let input_salt = random_digest_bytes().ok()?;
                let opening = NoteOpeningV1::new(owner_key, 1_000, 77, input_salt).ok()?;
                let input_commitment = decode_digest_canonical(
                    &aspis_pool_wallet_v1::recompute_note_commitment_v1(&opening).ok()?,
                )
                .ok()?;
                let nullifier = decode_digest_canonical(
                    &derive_note_nullifier_v1(&opening, &nullifier_key).ok()?,
                )
                .ok()?;
                let deposit_lane = pool_v1_pair_forest_deposit_lane_v1(&input_commitment).ok()?;
                let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier).ok()?;
                (deposit_lane == output_lane).then_some((
                    nullifier_key,
                    owner_key,
                    input_salt,
                    input_commitment,
                    deposit_lane,
                    attempts,
                ))
            })
            .context("failed to generate same-lane live note within bounded attempts")?;
    let input = note(owner_key, 1_000, input_salt);
    let recipient = if operation == "transfer" {
        Some(note(random_digest_bytes()?, 600, random_digest_bytes()?))
    } else {
        None
    };
    let (change_value, withdrawal_amount) = if operation == "transfer" {
        (400, None)
    } else {
        (750, Some(250))
    };
    let change = note(random_digest_bytes()?, change_value, random_digest_bytes()?);
    let withdrawal_destination = (operation == "withdrawal")
        .then_some("5jKh25biPsnrmLWXXuqKNH2Q67j69T4Q7Zew5c8wJKaV");
    let secret = json!({
        "schema":"aspis.v7.live-pool-proof-secrets.v1","operation":operation,
        "nullifierKeyHex":hex(&nullifier_key),"inputNote":input,
        "recipientNote":recipient,"changeNote":change,
        "withdrawalAmount":withdrawal_amount,"withdrawalDestination":withdrawal_destination
    });
    let mut file = OpenOptions::new().write(true).create_new(true).mode(0o600).open(&output)?;
    file.write_all(&serde_json::to_vec_pretty(&secret)?)?;
    file.write_all(b"\n")?;
    let decoded_owner = decode_digest_canonical(&owner_key)
        .map_err(|error| anyhow::anyhow!("decode generated owner key: {error:?}"))?;
    let decoded_salt = decode_digest_canonical(&input_salt)
        .map_err(|error| anyhow::anyhow!("decode generated salt: {error:?}"))?;
    ensure!(
        pool_v1_note_commitment(
            &decoded_owner,
            1_000,
            aspis_core::field::M31(77),
            &decoded_salt,
        ) == input_commitment,
        "generated commitment changed"
    );
    println!("{}", json!({
        "schema":"aspis.v7.live-operation-public.v1","operation":operation,
        "inputCommitmentHex":hex(&encode_digest_canonical(&input_commitment)),
        "depositLane":lane,"outputLane":lane,"sameLaneSelectionAttempts":attempts,
        "secretFileMode":"0600","secretValuesPrinted":false
    }));
    Ok(())
}
