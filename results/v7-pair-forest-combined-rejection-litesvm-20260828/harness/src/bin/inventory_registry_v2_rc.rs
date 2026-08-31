//! Read-only release inventory for the four honest Registry V2 fixtures.
//!
//! This does not execute SBF, sign, submit, or modify the frozen Agave bundle.
//! It reconstructs the transient ASF8 bytes from the exact ASQ8 and canonical
//! genesis accounts consumed by the signed lifecycle, then prints their hashes.

use std::{env, fs, path::Path};

use anyhow::{ensure, Context, Result};
use aspis_pool::POOL_V1_PAIR_EMPTY_ROOTS;
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
    decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_terminal_request_v1,
    decode_pool_v1_pair_verified_afterstate_v1, encode_pool_v1_pair_forest_terminal_result_v1,
    encode_pool_v1_pair_forest_terminal_statement_v1, pool_v1_pair_forest_output_lane_v1,
    reconstruct_pool_v1_pair_forest_terminal_statement_v1,
    v7_pool_pair_forest_tag73_statement_digest_v1, PoolV1PairForestTerminalCommonV1,
    PoolV1PairForestTerminalResultV1, PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotV1,
    POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES,
    POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};

const HONEST_CASES: [&str; 4] = [
    "transfer-same-page",
    "transfer-rollover",
    "withdrawal-same-page",
    "withdrawal-rollover",
];

fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update(part);
    }
    hash.finalize().into()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn account_data(bundle_root: &Path, case: &Value, address: &str) -> Result<Vec<u8>> {
    let entry = case["genesisAccounts"]
        .as_array()
        .context("case genesisAccounts is not an array")?
        .iter()
        .find(|entry| entry["address"].as_str() == Some(address))
        .with_context(|| format!("case omitted genesis account {address}"))?;
    ensure!(
        entry["loadAtGenesis"].as_bool() == Some(true),
        "required account {address} is not loaded at genesis"
    );
    let relative = entry["file"].as_str().context("account file is absent")?;
    let account: Value = serde_json::from_slice(&fs::read(bundle_root.join(relative))?)?;
    ensure!(
        account["data"][1].as_str() == Some("base64"),
        "account {address} does not use canonical base64 data"
    );
    BASE64_STANDARD
        .decode(
            account["data"][0]
                .as_str()
                .context("account data is absent")?,
        )
        .with_context(|| format!("decode account {address}"))
}

fn proof_address(bundle_root: &Path, case: &Value) -> Result<String> {
    for entry in case["genesisAccounts"]
        .as_array()
        .context("case genesisAccounts is not an array")?
    {
        if entry["loadAtGenesis"].as_bool() != Some(true) {
            continue;
        }
        let address = entry["address"]
            .as_str()
            .context("account address is absent")?;
        let data = account_data(bundle_root, case, address)?;
        if data.get(..4) == Some(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC) {
            return Ok(address.to_owned());
        }
    }
    anyhow::bail!("case omitted canonical proof account")
}

fn main() -> Result<()> {
    let args: Vec<_> = env::args_os().collect();
    ensure!(
        args.len() == 2,
        "usage: inventory_registry_v2_rc <bundle-directory>"
    );
    let bundle_root = Path::new(&args[1]);
    let bundle: Value = serde_json::from_slice(&fs::read(bundle_root.join("bundle.json"))?)?;
    let cases = bundle["cases"]
        .as_array()
        .context("bundle cases is not an array")?;
    let mut records = Vec::new();

    for name in HONEST_CASES {
        let case = cases
            .iter()
            .find(|case| case["name"].as_str() == Some(name))
            .with_context(|| format!("bundle omitted {name}"))?;
        ensure!(case["expectedOutcome"].as_str() == Some("success"));
        let input_path = case["input"].as_str().context("case input is absent")?;
        let input: Value = serde_json::from_slice(&fs::read(bundle_root.join(input_path))?)?;
        let metas = input["instructionAccounts"]
            .as_array()
            .context("instructionAccounts is not an array")?;
        ensure!(matches!(metas.len(), 11 | 12 | 16 | 17));
        let master_address = metas[0]["pubkey"]
            .as_str()
            .context("master address is absent")?;
        let checkpoint_address = metas[1]["pubkey"]
            .as_str()
            .context("checkpoint address is absent")?;
        let lane_address = metas[2]["pubkey"]
            .as_str()
            .context("lane address is absent")?;
        let proof_address = proof_address(bundle_root, case)?;
        ensure!(
            metas
                .iter()
                .any(|meta| meta["pubkey"].as_str() == Some(&proof_address)),
            "proof account is not an instruction meta"
        );

        let request_bytes = BASE64_STANDARD.decode(
            input["instructionDataBase64"]
                .as_str()
                .context("instruction data is absent")?,
        )?;
        ensure!(request_bytes.len() == POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES);
        let request = decode_pool_v1_pair_forest_terminal_request_v1(&request_bytes)
            .map_err(|error| anyhow::anyhow!("decode ASQ8 {name}: {error:?}"))?;

        let master_bytes = account_data(bundle_root, case, master_address)?;
        let checkpoint_bytes = account_data(bundle_root, case, checkpoint_address)?;
        let lane_bytes = account_data(bundle_root, case, lane_address)?;
        let proof_image = account_data(bundle_root, case, &proof_address)?;
        let master = decode_pool_v1_pair_forest_master_v1(&master_bytes)
            .map_err(|error| anyhow::anyhow!("decode master {name}: {error:?}"))?;
        let checkpoint = decode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_bytes)
            .map_err(|error| anyhow::anyhow!("decode checkpoint {name}: {error:?}"))?;
        let lane = decode_pool_v1_pair_forest_lane_state_v1(&lane_bytes, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|error| anyhow::anyhow!("decode lane {name}: {error:?}"))?;
        let master_account = master_address
            .parse::<solana_program::pubkey::Pubkey>()?
            .to_bytes();
        ensure!(master.identity.pool == master_account);
        ensure!(checkpoint.master == master_account);
        ensure!(lane.master == master_account);

        ensure!(proof_image.len() > POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES);
        ensure!(proof_image[..4] == POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
        let payload_bytes = u32::from_le_bytes(proof_image[4..8].try_into().unwrap()) as usize;
        ensure!(proof_image.len() == POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + payload_bytes);
        let payload = &proof_image[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..];
        ensure!(payload.len() > POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES);
        let (candidate_bytes, proof_body) =
            payload.split_at(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES);
        let candidate = decode_pool_v1_pair_verified_afterstate_v1(candidate_bytes)
            .map_err(|error| anyhow::anyhow!("decode candidate {name}: {error:?}"))?;

        let live_snapshot = PoolV1PairLiveSnapshotV1 {
            pool: master_account,
            deployment_domain: master.identity.deployment_domain,
            sequence: lane.tree.next_leaf_index,
            next_pair_index: lane.tree.next_leaf_index,
            current_root: lane.tree.root,
            frontier: lane.tree.frontier,
        };
        let common = PoolV1PairForestTerminalCommonV1 {
            master_account,
            checkpoint_account: checkpoint_address
                .parse::<solana_program::pubkey::Pubkey>()?
                .to_bytes(),
            selected_lane_account: lane_address
                .parse::<solana_program::pubkey::Pubkey>()?
                .to_bytes(),
            output_lane: lane.lane_id,
            checkpoint_sequence: checkpoint.checkpoint_sequence,
            historical_global_anchor: checkpoint.global_root,
            lane_transition: PoolV1PairLatePublicStatementV1 {
                live_snapshot,
                candidate_afterstate: candidate,
            },
        };
        let statement = reconstruct_pool_v1_pair_forest_terminal_statement_v1(&request, common)
            .map_err(|error| anyhow::anyhow!("reconstruct ASF8 {name}: {error:?}"))?;
        let statement_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
            .map_err(|error| anyhow::anyhow!("encode ASF8 {name}: {error:?}"))?;
        ensure!(statement_bytes.len() == POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES);
        let statement_digest =
            v7_pool_pair_forest_tag73_statement_digest_v1(&statement_bytes, sha256);

        let output_lane = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
            .map_err(|error| anyhow::anyhow!("derive output lane {name}: {error:?}"))?;
        ensure!(output_lane == lane.lane_id);
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: request.public.transition_kind(),
            master_account,
            selected_lane_account: common.selected_lane_account,
            output_lane,
            nullifier: *request.public.nullifier(),
            verified_afterstate: candidate,
        };
        let result_bytes = encode_pool_v1_pair_forest_terminal_result_v1(&result)
            .map_err(|error| anyhow::anyhow!("encode ASR8 {name}: {error:?}"))?;
        ensure!(result_bytes.len() == POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES);

        records.push(json!({
            "case": name,
            "request": {
                "bytes": request_bytes.len(),
                "sha256": hex(&sha256(&[&request_bytes])),
            },
            "statement": {
                "bytes": statement_bytes.len(),
                "sha256": hex(&sha256(&[&statement_bytes])),
                "transcriptDigestSha256": hex(&statement_digest),
            },
            "result": {
                "bytes": result_bytes.len(),
                "sha256": hex(&sha256(&[&result_bytes])),
            },
            "proofAccount": {
                "address": proof_address,
                "bytes": proof_image.len(),
                "sha256": hex(&sha256(&[&proof_image])),
            },
            "proofPayload": {
                "bytes": payload.len(),
                "sha256": hex(&sha256(&[payload])),
            },
            "candidateAfterstate": {
                "bytes": candidate_bytes.len(),
                "sha256": hex(&sha256(&[candidate_bytes])),
            },
            "tag73ProofBody": {
                "bytes": proof_body.len(),
                "sha256": hex(&sha256(&[proof_body])),
            },
        }));
    }

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema": "aspis.v7.registry-v2-rc-transient-statement-inventory.v1",
            "bundleSha256": hex(&sha256(&[&fs::read(bundle_root.join("bundle.json"))?])),
            "readOnly": true,
            "executed": false,
            "signed": false,
            "submitted": false,
            "cases": records,
        }))?
    );
    Ok(())
}
