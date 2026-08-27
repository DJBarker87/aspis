use std::{env, fs, path::PathBuf};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::{field::M31, v7_staged_pair::V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS};
use aspis_pool::{
    pool_v1_nullifier_marker_address, pool_v1_pair_forest_checkpoint_address,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_lane_root_page_address,
    pool_v1_pair_forest_master_address, pool_v1_verifier_entry_address,
    pool_v1_verifier_registry_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, decode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_verified_afterstate_v1, encode_verifier_registry_entry_v1,
        encode_verifier_registry_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, VerifierEntryStatusV1,
        VerifierPolicyV1, VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
    },
    Digest,
};
use aspis_verifier::v7_staged_pair_profile::{
    V7_STAGED_PAIR_PROFILE_BINDING, V7_STAGED_PAIR_RELEASE_BINDING,
};
use litesvm::{types::TransactionMetadata, LiteSVM};
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_program::pubkey::Pubkey;
use solana_signer::Signer;
use solana_transaction::Transaction;

const CU_LIMIT: u32 = 1_400_000;
const SLOT: u64 = 150;
const POOL_BYTES: [u8; 32] = [0xa5; 32];
const VERIFIER_BYTES: [u8; 32] = [0xb6; 32];
const REGISTRY_BYTES: [u8; 32] = [0xc7; 32];
const AUTHORITY_BYTES: [u8; 32] = [0xd8; 32];
const POLICY_BYTES: [u8; 32] = [0x19; 32];
const DOMAIN_BYTES: [u8; 32] = [0x4c; 32];

fn legacy(bytes: [u8; 32]) -> Pubkey {
    Pubkey::new_from_array(bytes)
}

fn address(key: &Pubkey) -> Address {
    Address::from(key.to_bytes())
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 101 * index as u32))
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn checked<T, E: core::fmt::Debug>(result: core::result::Result<T, E>, context: &str) -> Result<T> {
    result.map_err(|error| anyhow!("{context}: {error:?}"))
}

fn put_account(svm: &mut LiteSVM, key: Pubkey, owner: Pubkey, data: Vec<u8>) -> Result<()> {
    svm.set_account(
        address(&key),
        Account {
            lamports: svm.minimum_balance_for_rent_exemption(data.len()).max(1),
            data,
            owner: address(&owner),
            executable: false,
            rent_epoch: u64::MAX,
        },
    )
    .map_err(|error| anyhow!("set account {key}: {error}"))?;
    Ok(())
}

fn meta(key: Pubkey, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(address(&key), false)
    } else {
        AccountMeta::new_readonly(address(&key), false)
    }
}

fn tx(svm: &LiteSVM, payer: &Keypair, instruction: Instruction) -> Transaction {
    Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
            instruction,
        ],
        Some(&payer.pubkey()),
        &[payer],
        svm.latest_blockhash(),
    )
}

fn execute(
    svm: &mut LiteSVM,
    payer: &Keypair,
    instruction: Instruction,
) -> Result<TransactionMetadata> {
    let transaction = tx(svm, payer, instruction);
    let simulation = svm
        .simulate_transaction(transaction.clone())
        .map_err(|failed| {
            anyhow!(
                "simulation failed: {:?}\n{}",
                failed.err,
                failed.meta.pretty_logs()
            )
        })?;
    let landed = svm.send_transaction(transaction).map_err(|failed| {
        anyhow!(
            "execution failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    ensure!(simulation.meta == landed, "simulation/execution mismatch");
    Ok(landed)
}

fn phase_ledger(logs: &[String]) -> Vec<serde_json::Value> {
    let mut pending: Option<String> = None;
    let mut previous: Option<u64> = None;
    let mut result = Vec::new();
    for log in logs {
        if let Some((_, label)) = log.split_once("aspis-") {
            if label.starts_with("forest-pool-profile:")
                || label.starts_with("asq8-profile:")
                || label.starts_with("asq8-component:")
            {
                pending = Some(format!("aspis-{label}"));
            }
            continue;
        }
        let Some(label) = pending.take() else {
            continue;
        };
        let Some((_, tail)) = log.split_once("Program consumption:") else {
            pending = Some(label);
            continue;
        };
        let Some(remaining) = tail
            .split_whitespace()
            .find_map(|token| token.parse::<u64>().ok())
        else {
            continue;
        };
        let delta = previous.map(|value| value.saturating_sub(remaining));
        previous = Some(remaining);
        result.push(serde_json::json!({
            "label": label,
            "remaining": remaining,
            "delta_from_previous_marker": delta,
        }));
    }
    result
}

fn main() -> Result<()> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        args.len() == 3 || args.len() == 4,
        "usage: harness <aspis_pool.so> <aspis_verifier.so> <evidence.json> [expected-return-bytes]"
    );
    let pool_path = PathBuf::from(&args[0]);
    let verifier_path = PathBuf::from(&args[1]);
    let evidence_path = PathBuf::from(&args[2]);
    let expected_return_bytes = args
        .get(3)
        .map(|value| value.parse::<usize>())
        .transpose()
        .context("invalid expected return byte count")?
        .unwrap_or(792);
    ensure!(!evidence_path.exists(), "refusing to overwrite evidence");
    let pool_elf = fs::read(&pool_path)?;
    let verifier_elf = fs::read(&verifier_path)?;

    let pool_program = legacy(POOL_BYTES);
    let verifier_program = legacy(VERIFIER_BYTES);
    let registry_program = legacy(REGISTRY_BYTES);
    let mint = legacy([0x51; 32]);
    let master_key = pool_v1_pair_forest_master_address(&pool_program, &mint).0;
    let policy = VerifierPolicyV1 {
        flags: 0,
        registry_program: REGISTRY_BYTES,
        registry_authority: AUTHORITY_BYTES,
        policy_binding: POLICY_BYTES,
    };
    let master = PoolV1PairForestMasterV1 {
        identity: PoolIdentityV1 {
            pool: master_key.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(73),
            deployment_domain: DOMAIN_BYTES,
        },
        verifier_policy: policy,
        initialized_lane_mask: 0xff,
        has_checkpoint: true,
        next_checkpoint_sequence: 1,
        last_checkpoint_lane_sequences: [0; 8],
    };
    let mut nullifier = digest(30_000);
    nullifier[0] = M31(3);
    let lane_id = checked(
        aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(&nullifier),
        "select output lane",
    )?;
    let lane_key = pool_v1_pair_forest_lane_address(&pool_program, &master_key, lane_id)?.0;
    let lane = PoolV1PairForestLaneStateV1 {
        master: master_key.to_bytes(),
        lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        },
    };
    let (next_tree, _) = checked(
        lane.tree
            .append_one_with_empty_roots(digest(40_000), &POOL_V1_PAIR_EMPTY_ROOTS),
        "construct candidate lane",
    )?;
    let candidate = PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: next_tree.next_leaf_index,
        next_root: next_tree.root,
        next_frontier: next_tree.frontier,
    };
    let checkpoint = PoolV1PairForestCheckpointV1 {
        master: master_key.to_bytes(),
        deployment_domain: DOMAIN_BYTES,
        checkpoint_sequence: 0,
        global_root: digest(50_000),
        lane_sequences: [0; 8],
    };
    let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&pool_program, &master_key, 0).0;
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: V7_STAGED_PAIR_PROFILE_BINDING,
        verifier_release: V7_STAGED_PAIR_RELEASE_BINDING,
        pool_program: pool_program.to_bytes(),
        public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(PoolV1PrivateTransferPublicV1 {
            pool: master_key.to_bytes(),
            deployment_domain: DOMAIN_BYTES,
            anchor_sequence: 0,
            anchor_root: checkpoint.global_root,
            nullifier,
            asset_id: M31(73),
            recipient_commitment: digest(60_000),
            change_commitment: digest(70_000),
        }),
    };
    let instruction_data = checked(
        encode_pool_v1_pair_forest_terminal_request_v1(&request),
        "encode ASQ8",
    )?;

    let frontier_nodes = aspis_statement::pool_v1::V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES;
    let proof_bytes = V7_STAGED_PAIR_BODY_WITHOUT_FRONTIERS + 2 * 26 * frontier_nodes;
    let payload_bytes = 688 + proof_bytes;
    let proof_key = legacy([0x71; 32]);
    let mut proof_image = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + payload_bytes];
    proof_image[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
    proof_image[4..8].copy_from_slice(&(payload_bytes as u32).to_le_bytes());
    let candidate_bytes = checked(
        encode_pool_v1_pair_verified_afterstate_v1(&candidate),
        "encode candidate afterstate",
    )?;
    proof_image[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
        ..POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + 688]
        .copy_from_slice(&candidate_bytes);

    let registry = pool_v1_verifier_registry_address(&registry_program, &master_key).0;
    let entry = pool_v1_verifier_entry_address(
        &registry_program,
        &master_key,
        &V7_STAGED_PAIR_PROFILE_BINDING,
        &V7_STAGED_PAIR_RELEASE_BINDING,
    )
    .0;
    let registry_image = checked(
        encode_verifier_registry_v1(&VerifierRegistryV1 {
            flags: 0,
            pool: master_key.to_bytes(),
            authority: AUTHORITY_BYTES,
            policy_binding: POLICY_BYTES,
            generation: 1,
            minimum_activation_delay_slots: 1,
        }),
        "encode registry",
    )?;
    let entry_image = checked(
        encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Active,
            statement_version: 1,
            pool: master_key.to_bytes(),
            verifier_program: verifier_program.to_bytes(),
            profile_binding: V7_STAGED_PAIR_PROFILE_BINDING,
            release_binding: V7_STAGED_PAIR_RELEASE_BINDING,
            activation_slot: 90,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
            policy_binding: POLICY_BYTES,
        }),
        "encode registry entry",
    )?;
    let page =
        pool_v1_pair_forest_lane_root_page_address(&pool_program, &master_key, lane_id, 0)?.0;
    let marker = pool_v1_nullifier_marker_address(
        &pool_program,
        &master_key,
        &encode_digest_canonical(&nullifier),
    )?
    .0;

    let payer = Keypair::new_from_array([1u8; 32]);
    let mut svm = LiteSVM::new();
    svm.add_program(address(&pool_program), &pool_elf)?;
    svm.add_program(address(&verifier_program), &verifier_elf)?;
    svm.warp_to_slot(SLOT);
    svm.airdrop(&payer.pubkey(), 10_000_000_000)
        .map_err(|failed| anyhow!("airdrop: {:?}", failed.err))?;
    put_account(
        &mut svm,
        master_key,
        pool_program,
        checked(
            encode_pool_v1_pair_forest_master_v1(&master),
            "encode master",
        )?
        .to_vec(),
    )?;
    put_account(
        &mut svm,
        checkpoint_key,
        pool_program,
        checked(
            encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint),
            "encode checkpoint",
        )?
        .to_vec(),
    )?;
    put_account(
        &mut svm,
        lane_key,
        pool_program,
        checked(
            encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS),
            "encode lane",
        )?
        .to_vec(),
    )?;
    put_account(
        &mut svm,
        page,
        pool_program,
        vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    )?;
    put_account(
        &mut svm,
        marker,
        pool_program,
        vec![0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
    )?;
    put_account(
        &mut svm,
        registry,
        registry_program,
        registry_image.to_vec(),
    )?;
    put_account(&mut svm, entry, registry_program, entry_image.to_vec())?;
    put_account(&mut svm, proof_key, verifier_program, proof_image)?;

    let instruction = Instruction {
        program_id: address(&pool_program),
        accounts: vec![
            meta(master_key, false),
            meta(checkpoint_key, false),
            meta(lane_key, true),
            meta(page, true),
            meta(marker, true),
            meta(registry, false),
            meta(entry, false),
            meta(verifier_program, false),
            meta(proof_key, false),
        ],
        data: instruction_data.to_vec(),
    };
    let wire_bytes = wincode::serialize(&tx(&svm, &payer, instruction.clone()))?.len();
    ensure!(wire_bytes <= 1_232, "transaction exceeds legacy wire limit");
    let executed = execute(&mut svm, &payer, instruction)?;
    let phase_ledger = phase_ledger(&executed.logs);
    ensure!(!phase_ledger.is_empty(), "profile markers missing");
    ensure!(
        executed.return_data.data.len() == 792,
        "unexpected final Pool return-data length"
    );

    let lane_after = svm
        .get_account(&address(&lane_key))
        .context("lane missing")?;
    let decoded_lane = checked(
        decode_pool_v1_pair_forest_lane_state_v1(&lane_after.data, &POOL_V1_PAIR_EMPTY_ROOTS),
        "decode lane after",
    )?;
    ensure!(decoded_lane.tree == next_tree, "lane afterstate mismatch");
    let page_after = svm.get_account(&address(&page)).context("page missing")?;
    ensure!(
        checked(
            aspis_statement::pool_v1::root_history::read_root_history_page_root_v1(
                &page_after.data,
                1,
            ),
            "read history root",
        )? == next_tree.root,
        "history root mismatch"
    );
    let marker_after = svm
        .get_account(&address(&marker))
        .context("marker missing")?;
    ensure!(
        checked(
            decode_pool_v1_nullifier_marker(&marker_after.data),
            "decode marker",
        )?
        .nullifier
            == nullifier,
        "marker mismatch"
    );

    let evidence = serde_json::json!({
        "schema": "aspis.v7.pair-forest-byte-cu-profile.v1",
        "baseline_revision": "041780f4ef0be98c5b1675df87917046b62b4c2f",
        "execution_kind": "measurement-only unverified ASQ8/ASF8/ASR8 transport plus byte-only Pool mutation",
        "cryptographic_tag73_executed": false,
        "compute_unit_limit": CU_LIMIT,
        "compute_units": executed.compute_units_consumed,
        "transaction_wire_bytes": wire_bytes,
        "instruction_bytes": instruction_data.len(),
        "proof_grammar_max_bytes": aspis_core::v7_staged_pair::V7_STAGED_PAIR_MAX_BODY_BYTES,
        "fixture_frontier_nodes_per_tree": frontier_nodes,
        "proof_body_bytes": proof_bytes,
        "upload_payload_bytes": payload_bytes,
        "verifier_cpi_return_bytes": expected_return_bytes,
        "final_pool_return_bytes": executed.return_data.data.len(),
        "pool_elf_sha256": sha256_hex(&pool_elf),
        "verifier_profile_elf_sha256": sha256_hex(&verifier_elf),
        "phase_ledger": phase_ledger,
        "boundaries": [
            "the verifier profile constructs ASR8 after byte/account/ASF8 validation without executing Tag-73 cryptography",
            "the Pool profile writes the verifier-authenticated afterstate bytes without its strict 20-Poseidon reconstruction",
            "profile log syscalls are metered and inflate the total"
        ]
    });
    fs::write(&evidence_path, serde_json::to_vec_pretty(&evidence)?)?;
    println!(
        "pair-forest byte profile PASS: {} CU, {} tx bytes",
        executed.compute_units_consumed, wire_bytes
    );
    Ok(())
}
