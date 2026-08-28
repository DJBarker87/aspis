use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{anyhow, bail, ensure, Context, Result};
use aspis_core::field::{M31, P};
use aspis_pool::{
    pool_v1_nullifier_marker_address, pool_v1_pair_forest_checkpoint_address,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_master_address,
    pool_v1_root_page_address, pool_v1_vault_authority_address,
    pool_v1_vault_token_account_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_statement::pool_v1::root_history::{
    append_root_history_page_bytes_v1, initialize_root_history_page_bytes_v1, root_history_location,
};
use aspis_statement::{
    derive_owner_key, encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, decode_pool_v1_pair_forest_lane_state_v1,
        decode_pool_v1_pair_verified_afterstate_v1, encode_pool_v1_nullifier_marker,
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1,
        encode_pool_v1_pair_forest_terminal_statement_v1,
        encode_pool_v1_pair_verified_afterstate_v1, encode_verifier_registry_entry_v1,
        encode_verifier_registry_v1, pool_v1_note_commitment, pool_v1_nullifier,
        pool_v1_pair_forest_output_lane_v1, pool_v1_tree_parent, IncrementalMerkleTreeV1,
        PoolIdentityV1, PoolV1NullifierMarkerV1, PoolV1PairForestCheckpointV1,
        PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1, PoolV1PairForestTerminalCommonV1,
        PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalResultV1, PoolV1PairForestTerminalStatementV1,
        PoolV1PairLatePublicStatementV1, PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
        VerifierEntryStatusV1, VerifierPolicyV1, VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
        POOL_V1_PAIR_TREE_DEPTH, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        POOL_V1_ROOT_HISTORY_CAPACITY, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT, POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC, V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};
use litesvm::LiteSVM;
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::{
    compute_budget::ComputeBudget, compute_budget_limits::MAX_LOADED_ACCOUNTS_DATA_SIZE_BYTES,
};
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::{v1, v1::TransactionConfig, VersionedMessage};
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
const PROFILE_SLOT: u64 = 150;
const TXV1_TARGET_BYTES: usize = 4_096;

const POOL_PROGRAM_BYTES: [u8; 32] = [0x41; 32];
const VERIFIER_PROGRAM_ID: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0x44; 32];
const REGISTRY_AUTHORITY_BYTES: [u8; 32] = [0; 32];
const POLICY_BINDING_BYTES: [u8; 32] = [7; 32];
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [5; 32];
const PROOF_ACCOUNT_BYTES: [u8; 32] = [0x45; 32];
const DESTINATION_TOKEN_ACCOUNT_BYTES: [u8; 32] = [0x49; 32];
const DESTINATION_TOKEN_OWNER_BYTES: [u8; 32] = [0x4a; 32];
const LEGACY_SPL_TOKEN_PROGRAM_ID: &str = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA";
const LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES: usize = 82;
const LEGACY_SPL_TOKEN_ACCOUNT_BYTES: usize = 165;
const WITHDRAWAL_AMOUNT: u64 = 250;
const VAULT_BALANCE_BEFORE: u64 = 10_000;
const DESTINATION_BALANCE_BEFORE: u64 = 17;

struct Args {
    pool_program: PathBuf,
    verifier_program: PathBuf,
    evidence: PathBuf,
    proof_fixture: PathBuf,
    expect_success: bool,
    runtime_compute_limit: u64,
    transport: Transport,
    populated_pairs: u32,
    operation: Operation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Transport {
    Asq8,
    Asf8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operation {
    Transfer,
    Withdrawal,
}

fn parse_args() -> Result<Args> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        (5..=9).contains(&args.len()),
        "usage: aspis-v7-pair-forest-combined <aspis_pool.so> <aspis_verifier.so> \
         <evidence.json> <proof-body-or-payload.bin> <success|failure> \
         [runtime-compute-limit] [asq8|asf8] [populated-pairs] [transfer|withdrawal]"
    );
    let expect_success = match args[4].as_str() {
        "success" => true,
        "failure" => false,
        _ => bail!("expected outcome must be success or failure"),
    };
    let runtime_compute_limit = args
        .get(5)
        .map(|value| value.parse::<u64>())
        .transpose()
        .context("parse runtime compute limit")?
        .unwrap_or(u64::from(COMPUTE_UNIT_LIMIT));
    let transport = match args.get(6).map(String::as_str).unwrap_or("asq8") {
        "asq8" => Transport::Asq8,
        "asf8" => Transport::Asf8,
        _ => bail!("transport must be asq8 or asf8"),
    };
    let populated_pairs = args
        .get(7)
        .map(|value| value.parse::<u32>())
        .transpose()
        .context("parse populated pairs")?
        .unwrap_or(13);
    let operation = match args.get(8).map(String::as_str).unwrap_or("transfer") {
        "transfer" => Operation::Transfer,
        "withdrawal" => Operation::Withdrawal,
        _ => bail!("operation must be transfer or withdrawal"),
    };
    Ok(Args {
        pool_program: PathBuf::from(&args[0]),
        verifier_program: PathBuf::from(&args[1]),
        evidence: PathBuf::from(&args[2]),
        proof_fixture: PathBuf::from(&args[3]),
        expect_success,
        runtime_compute_limit,
        transport,
        populated_pairs,
        operation,
    })
}

fn legacy(bytes: [u8; 32]) -> LegacyPubkey {
    LegacyPubkey::new_from_array(bytes)
}

fn address(key: &LegacyPubkey) -> Address {
    Address::from(key.to_bytes())
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32 + 1) % P))
}

fn strict_lane_digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32) % P))
}

fn deterministic_anchor_and_nullifier() -> Result<(Digest, Digest)> {
    let nullifier_key = digest(10);
    let salt = digest(100);
    let asset_id = M31(77);
    let input_commitment =
        pool_v1_note_commitment(&derive_owner_key(&nullifier_key), 1_000, asset_id, &salt);
    let mut anchor = PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
        .map_err(|error| anyhow!("construct deterministic input pair: {error:?}"))?
        .leaf_digest()
        .map_err(|error| anyhow!("hash deterministic input pair: {error:?}"))?;
    let membership_index = 0x5_4321u64;
    for level in 0..20 {
        let sibling = digest(2_000 + 20 * level as u32);
        anchor = if ((membership_index >> level) & 1) == 0 {
            pool_v1_tree_parent(&anchor, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &anchor)
        };
    }
    for (sibling, direction) in [digest(3_000), digest(3_100), digest(3_200)]
        .into_iter()
        .zip([true, false, true])
    {
        anchor = if direction {
            pool_v1_tree_parent(&sibling, &anchor)
        } else {
            pool_v1_tree_parent(&anchor, &sibling)
        };
    }
    Ok((anchor, pool_v1_nullifier(&nullifier_key, &salt)))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest: [u8; 32] = Sha256::digest(bytes).into();
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn initialized_mint_data(supply: u64, decimals: u8) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
    data[36..44].copy_from_slice(&supply.to_le_bytes());
    data[44] = decimals;
    data[45] = 1;
    data
}

fn initialized_token_data(mint: LegacyPubkey, owner: LegacyPubkey, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
    data[..32].copy_from_slice(&mint.to_bytes());
    data[32..64].copy_from_slice(&owner.to_bytes());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1;
    data
}

fn token_amount(account: &Account) -> Result<u64> {
    ensure!(
        account.data.len() == LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
        "wrong legacy token account length"
    );
    Ok(u64::from_le_bytes(account.data[64..72].try_into()?))
}

fn put_account(
    svm: &mut LiteSVM,
    key: LegacyPubkey,
    owner: LegacyPubkey,
    data: Vec<u8>,
) -> Result<()> {
    let lamports = svm.minimum_balance_for_rent_exemption(data.len()).max(1);
    svm.set_account(
        address(&key),
        Account {
            lamports,
            data,
            owner: address(&owner),
            executable: false,
            rent_epoch: u64::MAX,
        },
    )
    .map_err(|error| anyhow!("set account {key}: {error}"))?;
    Ok(())
}

fn meta(key: LegacyPubkey, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(address(&key), false)
    } else {
        AccountMeta::new_readonly(address(&key), false)
    }
}

fn transaction_v1(
    svm: &LiteSVM,
    payer: &Keypair,
    instruction: Instruction,
) -> Result<VersionedTransaction> {
    let config = TransactionConfig::empty()
        .with_compute_unit_limit(COMPUTE_UNIT_LIMIT)
        .with_loaded_accounts_data_size_limit(MAX_LOADED_ACCOUNTS_DATA_SIZE_BYTES.get());
    let message = v1::Message::try_compile_with_config(
        &payer.pubkey(),
        &[instruction],
        svm.latest_blockhash(),
        config,
    )?;
    Ok(VersionedTransaction::try_new(
        VersionedMessage::V1(message),
        &[payer],
    )?)
}

fn snapshot(svm: &LiteSVM, keys: &[LegacyPubkey]) -> Result<Vec<Account>> {
    keys.iter()
        .map(|key| {
            svm.get_account(&address(key))
                .with_context(|| format!("snapshot account {key}"))
        })
        .collect()
}

fn load_payload(
    path: &PathBuf,
    expected_afterstate: &[u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES],
) -> Result<(Vec<u8>, &'static str)> {
    let fixture = fs::read(path).with_context(|| format!("read {}", path.display()))?;
    let (payload, kind) = if fixture.len() >= POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        && fixture[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] == expected_afterstate[..]
    {
        (fixture, "complete-proof-account-payload")
    } else {
        let mut payload =
            Vec::with_capacity(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + fixture.len());
        payload.extend_from_slice(expected_afterstate);
        payload.extend_from_slice(&fixture);
        (payload, "compact-proof-body")
    };
    ensure!(
        payload.len() > POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        "proof payload is shorter than the 688-byte candidate afterstate plus proof"
    );
    ensure!(
        payload[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] == expected_afterstate[..],
        "fixture candidate afterstate does not match this deterministic lane transition"
    );
    decode_pool_v1_pair_verified_afterstate_v1(&payload[..POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES])
        .map_err(|error| anyhow!("decode fixture candidate afterstate: {error:?}"))?;
    Ok((payload, kind))
}

fn main() -> Result<()> {
    let args = parse_args()?;
    ensure!(
        !args.evidence.exists(),
        "refusing to overwrite {}",
        args.evidence.display()
    );
    let pool_artifact = fs::read(&args.pool_program)
        .with_context(|| format!("read {}", args.pool_program.display()))?;
    let verifier_artifact = fs::read(&args.verifier_program)
        .with_context(|| format!("read {}", args.verifier_program.display()))?;

    let pool_program = legacy(POOL_PROGRAM_BYTES);
    let verifier_program = LegacyPubkey::from_str(VERIFIER_PROGRAM_ID)?;
    let registry_program = legacy(REGISTRY_PROGRAM_BYTES);
    let mint = legacy([0x42; 32]);
    let master_key = pool_v1_pair_forest_master_address(&pool_program, &mint).0;
    let (historical_global_anchor, nullifier) = deterministic_anchor_and_nullifier()?;

    let policy = VerifierPolicyV1 {
        flags: 1,
        registry_program: REGISTRY_PROGRAM_BYTES,
        registry_authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
    };
    let master = PoolV1PairForestMasterV1 {
        identity: PoolIdentityV1 {
            pool: master_key.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: LegacyPubkey::from_str(LEGACY_SPL_TOKEN_PROGRAM_ID)?.to_bytes(),
            asset_id: M31(77),
            deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        },
        verifier_policy: policy,
        initialized_lane_mask: 0xff,
        has_checkpoint: true,
        next_checkpoint_sequence: 43,
        last_checkpoint_lane_sequences: [0; 8],
    };

    let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|error| anyhow!("derive output lane: {error:?}"))?;
    let lane_key = pool_v1_pair_forest_lane_address(&pool_program, &master_key, output_lane)?.0;
    let mut tree = IncrementalMerkleTreeV1 {
        next_leaf_index: 0,
        root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
    };
    let mut all_lane_roots = vec![tree.root];
    for leaf in 0..args.populated_pairs {
        tree = tree
            .append_one_with_empty_roots(
                strict_lane_digest(20_000 + 32 * leaf),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .map_err(|error| anyhow!("populate deterministic output lane: {error:?}"))?
            .0;
        all_lane_roots.push(tree.root);
    }
    let lane = PoolV1PairForestLaneStateV1 {
        master: master_key.to_bytes(),
        lane_id: output_lane,
        tree,
    };

    let checkpoint_sequence = 42u64;
    let checkpoint_key =
        pool_v1_pair_forest_checkpoint_address(&pool_program, &master_key, checkpoint_sequence).0;
    let checkpoint = PoolV1PairForestCheckpointV1 {
        master: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        checkpoint_sequence,
        global_root: historical_global_anchor,
        lane_sequences: [0; 8],
    };

    let asset_id = M31(77);
    let recipient = pool_v1_note_commitment(&digest(300), 600, asset_id, &digest(400));
    let change = pool_v1_note_commitment(&digest(500), 400, asset_id, &digest(600));
    let transfer_public = PoolV1PrivateTransferPublicV1 {
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: checkpoint_sequence,
        anchor_root: checkpoint.global_root,
        nullifier,
        asset_id,
        recipient_commitment: recipient,
        change_commitment: change,
    };
    let withdrawal_change = pool_v1_note_commitment(&digest(700), 750, asset_id, &digest(800));
    let withdrawal_public = PoolV1WithdrawalPublicV1 {
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: checkpoint_sequence,
        anchor_root: checkpoint.global_root,
        nullifier,
        asset_id,
        amount: WITHDRAWAL_AMOUNT as u32,
        destination_token_account: DESTINATION_TOKEN_ACCOUNT_BYTES,
        change_commitment: withdrawal_change,
    };
    let payment = match args.operation {
        Operation::Transfer => PoolV1PairForestTerminalPaymentV1::PrivateTransfer(transfer_public),
        Operation::Withdrawal => PoolV1PairForestTerminalPaymentV1::Withdrawal(withdrawal_public),
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        pool_program: pool_program.to_bytes(),
        public: payment,
    };

    // The candidate afterstate is validly encoded and exactly matches the
    // selected lane's one-pair transition.
    let output_pair = match args.operation {
        Operation::Transfer => PoolV1PairLeafWitnessV1::two_outputs(recipient, change),
        Operation::Withdrawal => PoolV1PairLeafWitnessV1::single_output(withdrawal_change),
    }
    .map_err(|error| anyhow!("construct deterministic output pair: {error:?}"))?;
    let output_pair_leaf = output_pair
        .leaf_digest()
        .map_err(|error| anyhow!("hash deterministic output pair: {error:?}"))?;
    let next_tree = lane
        .tree
        .append_one_with_empty_roots(output_pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .map_err(|error| anyhow!("construct deterministic afterstate: {error:?}"))?
        .0;
    let candidate_afterstate = PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: next_tree.next_leaf_index,
        next_root: next_tree.root,
        next_frontier: next_tree.frontier,
    };
    let instruction_data = match args.transport {
        Transport::Asq8 => {
            let bytes = encode_pool_v1_pair_forest_terminal_request_v1(&request)
                .map_err(|error| anyhow!("encode ASQ8: {error:?}"))?;
            ensure!(
                bytes.len() == POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
                "ASQ8 length changed"
            );
            bytes.to_vec()
        }
        Transport::Asf8 => {
            let common = PoolV1PairForestTerminalCommonV1 {
                master_account: master_key.to_bytes(),
                checkpoint_account: checkpoint_key.to_bytes(),
                selected_lane_account: lane_key.to_bytes(),
                output_lane,
                checkpoint_sequence,
                historical_global_anchor,
                lane_transition: PoolV1PairLatePublicStatementV1 {
                    live_snapshot: PoolV1PairLiveSnapshotV1 {
                        pool: master_key.to_bytes(),
                        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
                        sequence: lane.tree.next_leaf_index,
                        next_pair_index: lane.tree.next_leaf_index,
                        current_root: lane.tree.root,
                        frontier: lane.tree.frontier,
                    },
                    candidate_afterstate,
                },
            };
            let statement = match args.operation {
                Operation::Transfer => PoolV1PairForestTerminalStatementV1::PrivateTransfer {
                    common,
                    public: transfer_public,
                },
                Operation::Withdrawal => PoolV1PairForestTerminalStatementV1::Withdrawal {
                    common,
                    public: withdrawal_public,
                },
            };
            encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
                .map_err(|error| anyhow!("encode ASF8: {error:?}"))?
                .to_vec()
        }
    };
    let expected_afterstate = encode_pool_v1_pair_verified_afterstate_v1(&candidate_afterstate)
        .map_err(|error| anyhow!("encode deterministic afterstate: {error:?}"))?;
    let (payload, fixture_kind) = load_payload(&args.proof_fixture, &expected_afterstate)?;
    ensure!(
        payload.len() <= u32::MAX as usize,
        "proof payload too large"
    );
    let mut proof_image = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + payload.len()];
    proof_image[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
    proof_image[4..8].copy_from_slice(&(payload.len() as u32).to_le_bytes());
    proof_image[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..].copy_from_slice(&payload);
    let proof_key = legacy(PROOF_ACCOUNT_BYTES);

    let current_history_location = root_history_location(lane.tree.next_leaf_index);
    let next_history_location = root_history_location(lane.tree.next_leaf_index + 1);
    let rollover = current_history_location.page_number != next_history_location.page_number;
    let page_key = pool_v1_root_page_address(
        &pool_program,
        &lane_key,
        current_history_location.page_number,
    )
    .0;
    let next_page_key = rollover.then(|| {
        pool_v1_root_page_address(&pool_program, &lane_key, next_history_location.page_number).0
    });
    let marker_key = pool_v1_nullifier_marker_address(
        &pool_program,
        &master_key,
        &encode_digest_canonical(&nullifier),
    )?
    .0;
    let registry_key =
        aspis_pool::pool_v1_verifier_registry_address(&registry_program, &master_key).0;
    let entry_key = aspis_pool::pool_v1_verifier_entry_address(
        &registry_program,
        &master_key,
        &V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        &V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    )
    .0;
    let registry_image = encode_verifier_registry_v1(&VerifierRegistryV1 {
        flags: 2,
        pool: master_key.to_bytes(),
        authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
        generation: 1,
        minimum_activation_delay_slots: 1,
    })
    .map_err(|error| anyhow!("encode registry: {error:?}"))?;
    let entry_image = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Active,
        statement_version: 1,
        pool: master_key.to_bytes(),
        verifier_program: verifier_program.to_bytes(),
        profile_binding: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        activation_slot: 90,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: POLICY_BINDING_BYTES,
    })
    .map_err(|error| anyhow!("encode registry entry: {error:?}"))?;

    let payer = Keypair::new_from_array([1u8; 32]);
    let mut svm = LiteSVM::new();
    if args.runtime_compute_limit != u64::from(COMPUTE_UNIT_LIMIT) {
        let mut diagnostic_budget = ComputeBudget::new_with_defaults(false);
        diagnostic_budget.compute_unit_limit = args.runtime_compute_limit;
        svm = svm.with_compute_budget(diagnostic_budget);
    }
    svm.add_program(address(&pool_program), &pool_artifact)?;
    svm.add_program(address(&verifier_program), &verifier_artifact)?;
    svm.warp_to_slot(PROFILE_SLOT);
    svm.airdrop(&payer.pubkey(), 10_000_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    let current_page_first =
        current_history_location.page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64;
    let current_roots = &all_lane_roots[current_page_first as usize..];
    let mut history_image = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
    initialize_root_history_page_bytes_v1(
        &mut history_image,
        lane_key.to_bytes(),
        current_history_location.page_number,
        current_roots,
    )
    .map_err(|error| anyhow!("initialize populated lane history: {error:?}"))?;
    ensure!(
        all_lane_roots.len() == lane.tree.next_leaf_index as usize + 1,
        "deterministic history/root sequence mismatch"
    );
    let mut history_probe = history_image.clone();
    let mut next_history_probe = None;
    if rollover {
        let mut next = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(
            &mut next,
            lane_key.to_bytes(),
            next_history_location.page_number,
            &[candidate_afterstate.next_root],
        )
        .map_err(|error| anyhow!("initialize expected rollover page: {error:?}"))?;
        next_history_probe = Some(next);
    } else {
        append_root_history_page_bytes_v1(
            &mut history_probe,
            candidate_afterstate.next_pair_index,
            candidate_afterstate.next_root,
        )
        .map_err(|error| anyhow!("candidate does not extend current history page: {error:?}"))?;
    }
    put_account(
        &mut svm,
        master_key,
        pool_program,
        encode_pool_v1_pair_forest_master_v1(&master)
            .map_err(|error| anyhow!("encode master: {error:?}"))?
            .to_vec(),
    )?;
    put_account(
        &mut svm,
        checkpoint_key,
        pool_program,
        encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
            .map_err(|error| anyhow!("encode checkpoint: {error:?}"))?
            .to_vec(),
    )?;
    put_account(
        &mut svm,
        lane_key,
        pool_program,
        encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|error| anyhow!("encode lane: {error:?}"))?
            .to_vec(),
    )?;
    put_account(&mut svm, page_key, pool_program, history_image)?;
    if let Some(next_page_key) = next_page_key {
        put_account(
            &mut svm,
            next_page_key,
            pool_program,
            vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
        )?;
    }
    put_account(
        &mut svm,
        marker_key,
        pool_program,
        vec![0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
    )?;
    put_account(
        &mut svm,
        registry_key,
        registry_program,
        registry_image.to_vec(),
    )?;
    put_account(&mut svm, entry_key, registry_program, entry_image.to_vec())?;
    put_account(&mut svm, proof_key, verifier_program, proof_image)?;

    let token_program = LegacyPubkey::from_str(LEGACY_SPL_TOKEN_PROGRAM_ID)?;
    let vault_authority = pool_v1_vault_authority_address(&pool_program, &master_key).0;
    let vault_key = pool_v1_vault_token_account_address(&pool_program, &master_key).0;
    let destination_key = legacy(DESTINATION_TOKEN_ACCOUNT_BYTES);
    if args.operation == Operation::Withdrawal {
        put_account(
            &mut svm,
            mint,
            token_program,
            initialized_mint_data(1_000_000, 6),
        )?;
        put_account(
            &mut svm,
            vault_key,
            token_program,
            initialized_token_data(mint, vault_authority, VAULT_BALANCE_BEFORE),
        )?;
        put_account(
            &mut svm,
            destination_key,
            token_program,
            initialized_token_data(
                mint,
                legacy(DESTINATION_TOKEN_OWNER_BYTES),
                DESTINATION_BALANCE_BEFORE,
            ),
        )?;
        put_account(
            &mut svm,
            vault_authority,
            LegacyPubkey::default(),
            Vec::new(),
        )?;
    }

    let mut protected_keys = vec![master_key, checkpoint_key, lane_key, page_key];
    if let Some(next_page_key) = next_page_key {
        protected_keys.push(next_page_key);
    }
    let marker_snapshot_index = protected_keys.len();
    protected_keys.extend([marker_key, registry_key, entry_key, proof_key]);
    let registry_snapshot_index = marker_snapshot_index + 1;
    let entry_snapshot_index = marker_snapshot_index + 2;
    let proof_snapshot_index = marker_snapshot_index + 3;
    let token_snapshot_index = protected_keys.len();
    if args.operation == Operation::Withdrawal {
        protected_keys.extend([mint, vault_key, destination_key, vault_authority]);
    }
    let before = snapshot(&svm, &protected_keys)?;
    let mut instruction_accounts = vec![
        meta(master_key, false),
        meta(checkpoint_key, false),
        meta(lane_key, true),
        meta(page_key, !rollover),
    ];
    if let Some(next_page_key) = next_page_key {
        instruction_accounts.push(meta(next_page_key, true));
    }
    instruction_accounts.extend([
        meta(marker_key, true),
        meta(registry_key, false),
        meta(entry_key, false),
        meta(verifier_program, false),
        meta(proof_key, false),
    ]);
    if args.operation == Operation::Withdrawal {
        instruction_accounts.extend([
            meta(mint, false),
            meta(vault_key, true),
            meta(destination_key, true),
            meta(vault_authority, false),
            meta(token_program, false),
        ]);
    }
    let instruction = Instruction {
        program_id: address(&pool_program),
        accounts: instruction_accounts,
        data: instruction_data.to_vec(),
    };
    let tx = transaction_v1(&svm, &payer, instruction)?;
    let tx_bytes = wincode::serialize(&tx)?.len();
    ensure!(
        tx_bytes < TXV1_TARGET_BYTES,
        "transaction exceeds TxV1 target"
    );

    let expected_lane_image = encode_pool_v1_pair_forest_lane_state_v1(
        &PoolV1PairForestLaneStateV1 {
            master: lane.master,
            lane_id: lane.lane_id,
            tree: next_tree,
        },
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(|error| anyhow!("encode expected next lane: {error:?}"))?;
    let marker_payload = PoolV1NullifierMarkerV1 {
        transition_kind: request.public.transition_kind(),
        pool: master_key.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        nullifier,
        retained_anchor_sequence: checkpoint_sequence,
        retained_anchor_root: historical_global_anchor,
        verifier_profile: V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    };
    let expected_marker_image = encode_pool_v1_nullifier_marker(&marker_payload)
        .map_err(|error| anyhow!("encode expected marker: {error:?}"))?;
    let expected_result = PoolV1PairForestTerminalResultV1 {
        transition_kind: request.public.transition_kind(),
        master_account: master_key.to_bytes(),
        selected_lane_account: lane_key.to_bytes(),
        output_lane,
        nullifier,
        verified_afterstate: candidate_afterstate,
    };
    let expected_result_bytes = encode_pool_v1_pair_forest_terminal_result_v1(&expected_result)
        .map_err(|error| anyhow!("encode expected ASR8: {error:?}"))?;

    let (compute_units, logs, return_program, return_data, execution_error) = if args.expect_success
    {
        let simulated = svm.simulate_transaction(tx.clone()).map_err(|failed| {
            anyhow!(
                "expected-success simulation failed: {:?}\n{}",
                failed.err,
                failed.meta.pretty_logs()
            )
        })?;
        let executed = svm.send_transaction(tx).map_err(|failed| {
            anyhow!(
                "expected-success execution failed: {:?}\n{}",
                failed.err,
                failed.meta.pretty_logs()
            )
        })?;
        ensure!(
            simulated.meta == executed,
            "successful simulation and execution metadata differ"
        );
        ensure!(
            executed.return_data.program_id == address(&pool_program)
                && executed.return_data.data == expected_result_bytes,
            "successful transaction returned the wrong Pool ASR8"
        );
        (
            executed.compute_units_consumed,
            executed.logs,
            executed.return_data.program_id,
            executed.return_data.data,
            None,
        )
    } else {
        let simulated = svm
            .simulate_transaction(tx.clone())
            .expect_err("expected-failure simulation unexpectedly succeeded");
        let executed = svm
            .send_transaction(tx)
            .expect_err("expected-failure execution unexpectedly succeeded");
        ensure!(
            simulated.err == executed.err && simulated.meta == executed.meta,
            "failed simulation and execution metadata differ"
        );
        ensure!(
            executed.meta.return_data.data.is_empty(),
            "failed transaction leaked verifier or Pool return data"
        );
        (
            executed.meta.compute_units_consumed,
            executed.meta.logs,
            executed.meta.return_data.program_id,
            executed.meta.return_data.data,
            Some(format!("{:?}", executed.err)),
        )
    };
    let after = snapshot(&svm, &protected_keys)?;
    if args.expect_success {
        ensure!(
            before[0] == after[0]
                && before[1] == after[1]
                && before[registry_snapshot_index] == after[registry_snapshot_index]
                && before[entry_snapshot_index] == after[entry_snapshot_index]
                && before[proof_snapshot_index] == after[proof_snapshot_index],
            "successful terminal mutated a read-only authenticated account"
        );
        if args.operation == Operation::Withdrawal {
            ensure!(
                before[token_snapshot_index] == after[token_snapshot_index]
                    && before[token_snapshot_index + 3] == after[token_snapshot_index + 3],
                "successful withdrawal mutated mint or vault authority"
            );
            ensure!(
                token_amount(&before[token_snapshot_index + 1])? == VAULT_BALANCE_BEFORE
                    && token_amount(&after[token_snapshot_index + 1])?
                        == VAULT_BALANCE_BEFORE - WITHDRAWAL_AMOUNT,
                "withdrawal vault delta was not exact"
            );
            ensure!(
                token_amount(&before[token_snapshot_index + 2])? == DESTINATION_BALANCE_BEFORE
                    && token_amount(&after[token_snapshot_index + 2])?
                        == DESTINATION_BALANCE_BEFORE + WITHDRAWAL_AMOUNT,
                "withdrawal destination delta was not exact"
            );
        }
        ensure!(
            after[2].data == expected_lane_image,
            "wrong next lane image"
        );
        ensure!(
            after[3].data == history_probe,
            "wrong current history image"
        );
        if let Some(expected) = &next_history_probe {
            ensure!(after[4].data == *expected, "wrong rollover history image");
        }
        ensure!(
            after[marker_snapshot_index].data == expected_marker_image,
            "wrong nullifier marker image"
        );
        ensure!(
            decode_pool_v1_pair_forest_lane_state_v1(&after[2].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .map_err(|error| anyhow!("decode settled lane: {error:?}"))?
                .tree
                == next_tree,
            "settled lane did not decode to the exact candidate tree"
        );
        ensure!(
            decode_pool_v1_nullifier_marker(&after[marker_snapshot_index].data)
                .map_err(|error| anyhow!("decode settled marker: {error:?}"))?
                == marker_payload,
            "settled marker did not decode to the exact nullifier payload"
        );
    } else {
        ensure!(before == after, "failed CPI mutated protected Pool state");
    }

    let verifier_address = address(&verifier_program).to_string();
    let invoked_verifier = logs
        .iter()
        .any(|line| line.contains(&verifier_address) && line.contains("invoke"));
    ensure!(
        invoked_verifier,
        "logs do not show the selected verifier CPI:\n{}",
        logs.join("\n")
    );

    let proof_bytes = payload.len() - POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let evidence = serde_json::json!({
        "schema": "aspis.v7-pair-forest.combined-litesvm.v2",
        "classification": if args.expect_success {
            "REAL COMBINED STRICT-WORK ACCEPTANCE CU"
        } else {
            "REAL COMBINED STRICT-WORK REJECTION CU"
        },
        "fixture": {
            "kind": fixture_kind,
            "external_path": args.proof_fixture,
            "payload_bytes": payload.len(),
            "candidate_afterstate_bytes": POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
            "proof_bytes": proof_bytes,
            "payload_sha256": sha256_hex(&payload),
            "proof_sha256": sha256_hex(&payload[POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES..]),
            "strict_work_expected": true
        },
        "execution": {
            "runtime": "LiteSVM 0.16.0",
            "network": "none",
            "transaction_format": "true Solana TxV1 / VersionedMessage::V1",
            "terminal_transport": match args.transport {
                Transport::Asq8 => "ASQ8 / 320-byte compact request",
                Transport::Asf8 => "ASF8 / 1,880-byte full statement",
            },
            "serialized_transaction_bytes": tx_bytes,
            "txv1_4096_target_headroom_bytes": TXV1_TARGET_BYTES - tx_bytes,
            "instruction_bytes": instruction_data.len(),
            "account_metas_excluding_payer": 9 + usize::from(rollover) + if args.operation == Operation::Withdrawal { 5 } else { 0 },
            "txv1_declared_compute_unit_limit": COMPUTE_UNIT_LIMIT,
            "runtime_compute_limit": args.runtime_compute_limit,
            "runtime_limit_is_diagnostic_override": args.runtime_compute_limit != u64::from(COMPUTE_UNIT_LIMIT),
            "compute_units": compute_units,
            "outcome": if args.expect_success { "accepted" } else { "rejected" },
            "operation": match args.operation { Operation::Transfer => "private-transfer", Operation::Withdrawal => "withdrawal" },
            "simulation_equals_execution": true,
            "error": execution_error,
            "selected_verifier_cpi_observed_in_logs": invoked_verifier,
            "return_program": return_program.to_string(),
            "return_data_bytes": return_data.len(),
            "return_data_sha256": sha256_hex(&return_data),
            "logs": logs,
        },
        "authenticated_path": {
            "pool_program": pool_program.to_string(),
            "verifier_program": verifier_program.to_string(),
            "registry_program": registry_program.to_string(),
            "master": master_key.to_string(),
            "checkpoint": checkpoint_key.to_string(),
            "selected_output_lane": output_lane,
            "selected_lane": lane_key.to_string(),
            "history_page": page_key.to_string(),
            "rollover_history_page": next_page_key.map(|key| key.to_string()),
            "history_mode": if rollover { "rollover" } else { "same-page" },
            "nullifier_marker": marker_key.to_string(),
            "proof_account": proof_key.to_string(),
            "registry_profile_and_release_exact": true,
            "registry_entry_active_at_slot": PROFILE_SLOT,
            "proof_owner_is_selected_verifier": true,
            "candidate_afterstate_matches_deterministic_lane_transition": true,
            "populated_lane_pairs_before": lane.tree.next_leaf_index,
            "history_roots_before": current_roots.len()
        },
        "atomicity": {
            "master_unchanged": before[0] == after[0],
            "checkpoint_unchanged": before[1] == after[1],
            "lane_changed_exactly_on_success": (before[2] != after[2]) == args.expect_success,
            "history_changed_exactly_on_success": (before[3] != after[3]) == args.expect_success,
            "rollover_page_changed_exactly_on_success": next_page_key.map(|_| (before[4] != after[4]) == args.expect_success),
            "nullifier_marker_changed_exactly_on_success": (before[marker_snapshot_index] != after[marker_snapshot_index]) == args.expect_success,
            "registry_unchanged": before[registry_snapshot_index] == after[registry_snapshot_index],
            "entry_unchanged": before[entry_snapshot_index] == after[entry_snapshot_index],
            "proof_unchanged": before[proof_snapshot_index] == after[proof_snapshot_index],
            "withdrawal_mint_unchanged": if args.operation == Operation::Withdrawal {
                Some(before[token_snapshot_index] == after[token_snapshot_index])
            } else {
                None
            },
            "withdrawal_vault_amount_before": (args.operation == Operation::Withdrawal).then(|| token_amount(&before[token_snapshot_index + 1])).transpose()?,
            "withdrawal_vault_amount_after": (args.operation == Operation::Withdrawal).then(|| token_amount(&after[token_snapshot_index + 1])).transpose()?,
            "withdrawal_destination_amount_before": (args.operation == Operation::Withdrawal).then(|| token_amount(&before[token_snapshot_index + 2])).transpose()?,
            "withdrawal_destination_amount_after": (args.operation == Operation::Withdrawal).then(|| token_amount(&after[token_snapshot_index + 2])).transpose()?,
            "settled_lane_equals_candidate": after[2].data == expected_lane_image,
            "settled_history_equals_expected": after[3].data == history_probe,
            "settled_rollover_page_equals_expected": next_history_probe.as_ref().map(|expected| after[4].data == *expected),
            "settled_marker_equals_expected": after[marker_snapshot_index].data == expected_marker_image,
            "failure_all_accounts_byte_exact": !args.expect_success && before == after
        },
        "artifacts": {
            "pool": {
                "path": args.pool_program,
                "bytes": pool_artifact.len(),
                "sha256": sha256_hex(&pool_artifact)
            },
            "verifier": {
                "path": args.verifier_program,
                "bytes": verifier_artifact.len(),
                "sha256": sha256_hex(&verifier_artifact)
            }
        },
        "honest_fixture_contract": {
            "argument": "fourth argument is either compact proof body or complete payload, excluding the 40-byte ASPU header",
            "payload_layout": "688-byte encoded candidate afterstate followed by compact Tag-73 proof",
            "fixed_proof_account": proof_key.to_string(),
            "fixed_verifier_program": verifier_program.to_string(),
            "fixed_pool_master": master_key.to_string(),
            "requirement": "the fixture must be generated for the deterministic public statement and identities recorded above"
        },
        "boundaries": [
            "This is deterministic local LiteSVM evidence. No devnet, mainnet, signing service, or RPC is used.",
            "The transaction is a real TxV1 message with its 1.4M compute limit in TransactionConfig.",
            "A runtime limit above 1.4M is an explicit local diagnostic override and is not deployable evidence.",
            "The strict frozen proof executes all 35/31/34-bit work checks; there is no threshold bypass."
        ]
    });
    if let Some(parent) = args.evidence.parent() {
        fs::create_dir_all(parent)?;
    }
    if args.evidence.exists() {
        bail!("refusing to overwrite {}", args.evidence.display());
    }
    fs::write(&args.evidence, serde_json::to_vec_pretty(&evidence)?)?;
    println!(
        "pair-forest combined {} PASS: {} CU, {} TxV1 bytes",
        if args.expect_success {
            "acceptance"
        } else {
            "rejection"
        },
        compute_units,
        tx_bytes
    );
    println!("evidence={}", args.evidence.display());
    Ok(())
}
