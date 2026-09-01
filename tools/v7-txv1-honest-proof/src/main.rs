use std::{env, fs, path::PathBuf, str::FromStr, time::Instant};

use anyhow::{ensure, Context, Result};
use aspis_core::field::M31;
use aspis_pool::{
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_master_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_prover::v7_pair_forest_fixture::{
    build_v7_pair_forest_transfer_fixture_mined_v1,
    deterministic_v7_pair_forest_transfer_nullifier_v1,
};
use aspis_statement::pool_v1::{
    encode_pool_v1_pair_forest_terminal_request_v1,
    encode_pool_v1_pair_forest_terminal_statement_v1, encode_pool_v1_pair_verified_afterstate_v1,
    pool_v1_pair_forest_output_lane_v1, IncrementalMerkleTreeV1, PoolV1PairForestLaneStateV1,
    PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1, PoolV1PairLiveSnapshotV1,
    POOL_V1_PAIR_TREE_DEPTH, V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
    V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
};
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

const POOL_PROGRAM: &str = "5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx";
const VERIFIER_PROGRAM: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const CHECKPOINT_SEQUENCE: u64 = 42;
const DEPLOYMENT_DOMAIN: [u8; 32] = [5; 32];
const SELECTED_LANE_PAIRS: u32 = 13;

fn fixture_digest(seed: u32) -> aspis_statement::Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn bytes_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    let proof_account = args
        .next()
        .context("usage: aspis-v7-txv1-honest-proof <proof-account-pubkey> <new-output-dir>")?;
    let output = PathBuf::from(
        args.next()
            .context("usage: aspis-v7-txv1-honest-proof <proof-account-pubkey> <new-output-dir>")?,
    );
    ensure!(args.next().is_none(), "unexpected extra argument");
    ensure!(!output.exists(), "refusing to overwrite output directory");
    let proof_account = Pubkey::from_str(&proof_account).context("invalid proof-account pubkey")?;
    ensure!(
        proof_account != Pubkey::default(),
        "zero proof-account pubkey"
    );

    let pool_program = Pubkey::from_str(POOL_PROGRAM)?;
    let verifier_program = Pubkey::from_str(VERIFIER_PROGRAM)?;
    let mint = Pubkey::new_from_array([0x42; 32]);
    let master = pool_v1_pair_forest_master_address(&pool_program, &mint).0;
    let nullifier = deterministic_v7_pair_forest_transfer_nullifier_v1();
    let lane_id = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|error| anyhow::anyhow!("derive output lane: {error:?}"))?;
    let lane = pool_v1_pair_forest_lane_address(&pool_program, &master, lane_id)?.0;
    let checkpoint =
        pool_v1_pair_forest_checkpoint_address(&pool_program, &master, CHECKPOINT_SEQUENCE).0;

    let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
        0,
        POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(|error| anyhow::anyhow!("construct empty selected lane: {error:?}"))?;
    for pair in 0..SELECTED_LANE_PAIRS {
        tree = tree
            .append_one_with_empty_roots(
                fixture_digest(20_000 + 32 * pair),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .map_err(|error| anyhow::anyhow!("populate selected lane: {error:?}"))?
            .0;
    }
    let lane_state = PoolV1PairForestLaneStateV1 {
        master: master.to_bytes(),
        lane_id,
        tree,
    };
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: master.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN,
        sequence: lane_state.tree.next_leaf_index,
        next_pair_index: lane_state.tree.next_leaf_index,
        current_root: lane_state.tree.root,
        frontier: lane_state.tree.frontier,
    };

    let started = Instant::now();
    let built = build_v7_pair_forest_transfer_fixture_mined_v1(
        verifier_program.to_bytes(),
        proof_account.to_bytes(),
        master.to_bytes(),
        checkpoint.to_bytes(),
        lane.to_bytes(),
        CHECKPOINT_SEQUENCE,
        DEPLOYMENT_DOMAIN,
        snapshot,
    )
    .map_err(|error| anyhow::anyhow!("production pair-forest prover: {error:?}"))?;
    ensure!(
        built.proof.pow_valid,
        "production prover returned unmined work"
    );
    ensure!(
        built.transition.live_snapshot == snapshot,
        "live snapshot changed"
    );

    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        pool_program: pool_program.to_bytes(),
        public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(built.public),
    };
    let asq8 = encode_pool_v1_pair_forest_terminal_request_v1(&request)
        .map_err(|error| anyhow::anyhow!("encode ASQ8: {error:?}"))?;
    let asf8 = encode_pool_v1_pair_forest_terminal_statement_v1(&built.statement)
        .map_err(|error| anyhow::anyhow!("encode ASF8: {error:?}"))?;
    let candidate =
        encode_pool_v1_pair_verified_afterstate_v1(&built.transition.candidate_afterstate)
            .map_err(|error| anyhow::anyhow!("encode ASJA: {error:?}"))?;
    let mut payload = Vec::with_capacity(candidate.len() + built.proof.bytes.len());
    payload.extend_from_slice(&candidate);
    payload.extend_from_slice(&built.proof.bytes);

    fs::create_dir(&output).context("create output directory")?;
    fs::write(output.join("asq8.bin"), asq8)?;
    fs::write(output.join("asf8.bin"), asf8)?;
    fs::write(output.join("candidate-afterstate.bin"), candidate)?;
    fs::write(output.join("proof-body.bin"), &built.proof.bytes)?;
    fs::write(output.join("proof-payload.bin"), &payload)?;

    let metadata = serde_json::json!({
        "schema": "aspis.v7.txv1-honest-pair-forest-proof.v1",
        "operation": "private-transfer",
        "proverEntry": "build_v7_pool_pair_forest_private_transfer_onefold_proof_production",
        "deterministicFixtureEntropy": true,
        "proofAccount": proof_account.to_string(),
        "attemptId": proof_account.to_string(),
        "programs": {"pool": pool_program.to_string(), "verifier": verifier_program.to_string()},
        "accounts": {
            "master": master.to_string(), "checkpoint": checkpoint.to_string(),
            "selectedLane": lane.to_string(), "selectedLaneId": lane_id
        },
        "snapshot": {"sequence": snapshot.sequence, "nextPairIndex": snapshot.next_pair_index},
        "statementDigest": bytes_hex(&built.statement_digest),
        "asq8": {"bytes": asq8.len(), "sha256": sha256_hex(&asq8)},
        "asf8": {"bytes": asf8.len(), "sha256": sha256_hex(&asf8)},
        "candidateAfterstate": {"bytes": candidate.len(), "sha256": sha256_hex(&candidate)},
        "proof": {
            "bytes": built.proof.bytes.len(), "sha256": sha256_hex(&built.proof.bytes),
            "frontierNodes": built.proof.frontier_nodes, "workNonces": built.proof.work_nonces,
            "powValid": built.proof.pow_valid
        },
        "proofPayload": {"bytes": payload.len(), "sha256": sha256_hex(&payload)},
        "elapsedMillis": started.elapsed().as_millis(),
        "cryptographicParametersChanged": false,
        "verifierBypass": false,
        "trustedResultAccount": false
    });
    fs::write(
        output.join("proof.json"),
        serde_json::to_vec_pretty(&metadata)?,
    )?;
    println!("{}", serde_json::to_string(&metadata)?);
    Ok(())
}
