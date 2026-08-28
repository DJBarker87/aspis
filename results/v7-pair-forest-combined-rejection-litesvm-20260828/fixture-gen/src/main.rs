use std::{env, fs, path::PathBuf};

use anyhow::{bail, ensure, Context, Result};
use aspis_core::field::{M31, P};
use aspis_pool::{
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_master_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_prover::v7_pair_forest_fixture::{
    build_v7_pair_forest_transfer_fixture_mined_v1,
    deterministic_v7_pair_forest_transfer_nullifier_v1,
};
use aspis_prover::{
    state_only_entropy::StateOnlyAttemptSecrets,
    state_only_hiding::InMemoryStateOnlyMaskNonceStore,
    v6_onefold_prover::{
        build_v7_pool_pair_forest_withdrawal_onefold_proof_production, V7ProverContext,
    },
    HOST_HASH,
};
use aspis_statement::{
    derive_owner_key,
    pool_v1::{
        compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
        encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1,
        encode_pool_v1_pair_forest_terminal_statement_v1,
        encode_pool_v1_pair_verified_afterstate_v1, pair_trace::PoolV1PairInputNoteWitnessV1,
        pool_v1_note_commitment, pool_v1_pair_forest_output_lane_v1, pool_v1_tree_parent,
        IncrementalMerkleTreeV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
        PoolV1PairForestInputNoteWitnessV1, PoolV1PairForestTerminalCommonV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalResultV1, PoolV1PairForestTerminalStatementV1,
        PoolV1PairForestWithdrawalWitnessV1, PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1,
        PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1, PoolV1WithdrawalPublicV1,
        POOL_V1_PAIR_TREE_DEPTH, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING, V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

const POOL_PROGRAM_BYTES: [u8; 32] = [0x41; 32];
const VERIFIER_PROGRAM_ID: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [5; 32];
const PROOF_ACCOUNT_BYTES: [u8; 32] = [0x45; 32];
const DESTINATION_TOKEN_ACCOUNT_BYTES: [u8; 32] = [0x49; 32];

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32 + 1) % P))
}

fn strict_lane_digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32) % P))
}

fn deterministic_input_witness() -> Result<PoolV1PairForestInputNoteWitnessV1> {
    let nullifier_key = digest(10);
    let salt = digest(100);
    let asset_id = M31(77);
    let input_commitment =
        pool_v1_note_commitment(&derive_owner_key(&nullifier_key), 1_000, asset_id, &salt);
    Ok(PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key,
            salt,
            value: 1_000,
            pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
                .map_err(|error| anyhow::anyhow!("construct input pair: {error:?}"))?,
            selected_second: false,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                index: 0x5_4321,
            },
        },
        super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
        super_root_directions: [true, false, true],
    })
}

fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Result<Digest> {
    let mut current = input
        .pair
        .pair_leaf
        .leaf_digest()
        .map_err(|error| anyhow::anyhow!("hash input pair: {error:?}"))?;
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        let sibling = input.pair.membership.siblings[level];
        current = if ((input.pair.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &current)
        };
    }
    for level in 0..3 {
        let sibling = input.super_root_siblings[level];
        current = if input.super_root_directions[level] {
            pool_v1_tree_parent(&sibling, &current)
        } else {
            pool_v1_tree_parent(&current, &sibling)
        };
    }
    Ok(current)
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest: [u8; 32] = Sha256::digest(bytes).into();
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() -> Result<()> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        args.len() == 4,
        "usage: aspis-v7-pair-forest-fixture-gen <transfer|withdrawal> \
         <populated-pairs> <proof.bin> <metadata.json>"
    );
    let kind = args[0].as_str();
    ensure!(
        matches!(kind, "transfer" | "withdrawal"),
        "unknown fixture kind"
    );
    let populated_pairs = args[1].parse::<u32>().context("parse populated pairs")?;
    let proof_path = PathBuf::from(&args[2]);
    let metadata_path = PathBuf::from(&args[3]);
    if proof_path.exists() || metadata_path.exists() {
        bail!("refusing to overwrite fixture output");
    }

    let pool_program = Pubkey::new_from_array(POOL_PROGRAM_BYTES);
    let verifier_program: Pubkey = VERIFIER_PROGRAM_ID.parse()?;
    let proof_account = Pubkey::new_from_array(PROOF_ACCOUNT_BYTES);
    let mint = Pubkey::new_from_array([0x42; 32]);
    let master = pool_v1_pair_forest_master_address(&pool_program, &mint).0;
    let nullifier = deterministic_v7_pair_forest_transfer_nullifier_v1();
    let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|error| anyhow::anyhow!("derive output lane: {error:?}"))?;
    let selected_lane = pool_v1_pair_forest_lane_address(&pool_program, &master, output_lane)?.0;
    let checkpoint_sequence = 42u64;
    let checkpoint =
        pool_v1_pair_forest_checkpoint_address(&pool_program, &master, checkpoint_sequence).0;

    let mut tree = IncrementalMerkleTreeV1 {
        next_leaf_index: 0,
        root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
    };
    for leaf in 0..populated_pairs {
        tree = tree
            .append_one_with_empty_roots(
                strict_lane_digest(20_000 + 32 * leaf),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .map_err(|error| anyhow::anyhow!("populate deterministic lane: {error:?}"))?
            .0;
    }
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: master.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        sequence: tree.next_leaf_index,
        next_pair_index: tree.next_leaf_index,
        current_root: tree.root,
        frontier: tree.frontier,
    };
    let (public, statement, transition, proof) = if kind == "transfer" {
        let built = build_v7_pair_forest_transfer_fixture_mined_v1(
            verifier_program.to_bytes(),
            proof_account.to_bytes(),
            master.to_bytes(),
            checkpoint.to_bytes(),
            selected_lane.to_bytes(),
            checkpoint_sequence,
            DEPLOYMENT_DOMAIN_BYTES,
            snapshot,
        )
        .map_err(|error| anyhow::anyhow!("build honest mined transfer: {error:?}"))?;
        ensure!(
            built.public.nullifier == nullifier,
            "fixture nullifier changed"
        );
        (
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(built.public),
            built.statement,
            built.transition,
            built.proof,
        )
    } else {
        let input = deterministic_input_witness()?;
        let change = PoolV1OutputNoteWitnessV1 {
            owner_key: digest(700),
            salt: digest(800),
            value: 750,
        };
        let asset_id = M31(77);
        let anchor_root = global_anchor(&input)?;
        let withdrawal = PoolV1WithdrawalPublicV1 {
            pool: master.to_bytes(),
            deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
            anchor_sequence: checkpoint_sequence,
            anchor_root,
            nullifier,
            asset_id,
            amount: 250,
            destination_token_account: DESTINATION_TOKEN_ACCOUNT_BYTES,
            change_commitment: pool_v1_note_commitment(
                &change.owner_key,
                change.value,
                asset_id,
                &change.salt,
            ),
        };
        let witness = PoolV1PairForestWithdrawalWitnessV1 { input, change };
        let relation_context = PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: master.to_bytes(),
                deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
                anchor_sequence: checkpoint_sequence,
                anchor_root,
                asset_id,
            },
            spent_nullifiers: &[],
        };
        let compiled = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
            &withdrawal,
            &witness,
            relation_context,
            snapshot,
        )
        .map_err(|error| anyhow::anyhow!("compile withdrawal: {error:?}"))?;
        let statement = PoolV1PairForestTerminalStatementV1::Withdrawal {
            common: PoolV1PairForestTerminalCommonV1 {
                master_account: master.to_bytes(),
                checkpoint_account: checkpoint.to_bytes(),
                selected_lane_account: selected_lane.to_bytes(),
                output_lane,
                checkpoint_sequence,
                historical_global_anchor: anchor_root,
                lane_transition: compiled.public_statement,
            },
            public: withdrawal,
        };
        let statement_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
            .map_err(|error| anyhow::anyhow!("encode withdrawal ASF8: {error:?}"))?;
        let statement_digest =
            aspis_statement::pool_v1::v7_pool_pair_forest_tag73_statement_digest_v1(
                &statement_bytes,
                HOST_HASH,
            );
        let context = V7ProverContext {
            program_id: verifier_program.to_bytes(),
            release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
            attempt_id: proof_account.to_bytes(),
        };
        let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            proof_account.to_bytes(),
            [0x4b; 32],
            [0x6d; 32],
        );
        let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
        let proof = build_v7_pool_pair_forest_withdrawal_onefold_proof_production(
            &withdrawal,
            &witness,
            relation_context,
            &compiled.public_statement,
            statement_digest,
            context,
            attempt,
            &mut nonce_store,
            HOST_HASH,
        )
        .map_err(|error| anyhow::anyhow!("build honest mined withdrawal: {error:?}"))?;
        (
            PoolV1PairForestTerminalPaymentV1::Withdrawal(withdrawal),
            statement,
            compiled.public_statement,
            proof,
        )
    };

    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        pool_program: pool_program.to_bytes(),
        public,
    };
    let request_bytes = encode_pool_v1_pair_forest_terminal_request_v1(&request)
        .map_err(|error| anyhow::anyhow!("encode ASQ8: {error:?}"))?;
    let candidate_bytes =
        encode_pool_v1_pair_verified_afterstate_v1(&transition.candidate_afterstate)
            .map_err(|error| anyhow::anyhow!("encode candidate afterstate: {error:?}"))?;
    let mut payload = Vec::with_capacity(candidate_bytes.len() + proof.bytes.len());
    payload.extend_from_slice(&candidate_bytes);
    payload.extend_from_slice(&proof.bytes);
    ensure!(
        payload.len() == POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + proof.bytes.len(),
        "payload length changed"
    );
    let expected_result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: master.to_bytes(),
        selected_lane_account: selected_lane.to_bytes(),
        output_lane,
        nullifier,
        verified_afterstate: transition.candidate_afterstate,
    };
    let expected_result_bytes = encode_pool_v1_pair_forest_terminal_result_v1(&expected_result)
        .map_err(|error| anyhow::anyhow!("encode expected ASR8: {error:?}"))?;

    if let Some(parent) = proof_path.parent() {
        fs::create_dir_all(parent)?;
    }
    if let Some(parent) = metadata_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&proof_path, &proof.bytes)
        .with_context(|| format!("write {}", proof_path.display()))?;
    let metadata = serde_json::json!({
        "schema": "aspis.v7-pair-forest.strict-work-fixture.v1",
        "kind": kind,
        "security_boundary": "deterministic public KAT generated through the production prover with all work stages mined and independently checked",
        "program_id": verifier_program.to_string(),
        "attempt_id": proof_account.to_string(),
        "pool_program": pool_program.to_string(),
        "master": master.to_string(),
        "checkpoint": checkpoint.to_string(),
        "selected_lane": selected_lane.to_string(),
        "output_lane": output_lane,
        "populated_lane_pairs": tree.next_leaf_index,
        "proof_bytes": proof.bytes.len(),
        "proof_sha256": sha256_hex(&proof.bytes),
        "frontier_nodes": proof.frontier_nodes,
        "compact_counter": proof.compact_counter,
        "work_nonces": proof.work_nonces,
        "pow_valid": proof.pow_valid,
        "payload_bytes": payload.len(),
        "payload_sha256": sha256_hex(&payload),
        "request_bytes": request_bytes.len(),
        "request_sha256": sha256_hex(&request_bytes),
        "expected_asr8_bytes": expected_result_bytes.len(),
        "expected_asr8_sha256": sha256_hex(&expected_result_bytes),
        "statement_digest": sha256_hex(&aspis_statement::pool_v1::v7_pool_pair_forest_tag73_statement_digest_v1(
            &encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
                .map_err(|error| anyhow::anyhow!("re-encode statement: {error:?}"))?,
            HOST_HASH,
        )),
    });
    fs::write(&metadata_path, serde_json::to_vec_pretty(&metadata)?)
        .with_context(|| format!("write {}", metadata_path.display()))?;
    println!(
        "generated strict forest fixture: kind={} pairs={} proof={} payload={} frontier={}",
        kind,
        populated_pairs,
        proof.bytes.len(),
        payload.len(),
        proof.frontier_nodes
    );
    Ok(())
}
