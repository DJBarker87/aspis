use std::{env, fs, path::PathBuf};

use anyhow::{anyhow, bail, ensure, Context, Result};
use aspis_core::field::M31;
use aspis_pool::{
    encode_prepare_settlement_instruction_v1, encode_private_transfer_instruction_v1,
    encode_settle_prepared_instruction_v1, pool_v1_nullifier_marker_address,
    pool_v1_prepared_settlement_plan_address, pool_v1_prepared_settlement_rollover_address,
    pool_v1_root_page_address, pool_v1_state_address, PoolInitializationV1, PoolStateV1,
    PrivateTransferStatementV1, POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES,
    POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES,
};
use aspis_statement::pool_v1::root_history::read_root_history_page_root_v1;
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, encode_pool_v1_private_transfer_public_v1,
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1,
        finalize_pool_v1_authorization_receipt_account_v1, historical_anchor_envelope_digest_v1,
        initialize_pool_v1_authorization_receipt_account_v1,
        pool_v1_authorization_receipt_pda_inputs_for_binding_v1,
        verifier_statement_payload_digest_v1, HistoricalAnchorEnvelopeV1,
        PoolV1AuthorizationReceiptV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
        RootHistoryPageV1, VerifierDispatchBindingV1, VerifierDispatchRequestV1,
        VerifierEntryStatusV1, VerifierPolicyV1, VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES, POOL_V1_AUTHORIZATION_RECEIPT_SEED,
        POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES, POOL_V1_PAYMENT_STATEMENT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
    },
    poseidon2::Digest,
};
use litesvm::{types::TransactionMetadata, LiteSVM};
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_sdk_ids::system_program;
use solana_signer::Signer;
use solana_transaction::Transaction;

const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
const PROFILE_SLOT: u64 = 150;
const SOURCE_SEQUENCE_TARGET: u64 = 254;
const POOL_PROGRAM_BYTES: [u8; 32] = [0xA5; 32];
const VERIFIER_PROGRAM_BYTES: [u8; 32] = [0xB6; 32];
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0xC7; 32];
const REGISTRY_AUTHORITY_BYTES: [u8; 32] = [0xD8; 32];
const POLICY_BINDING_BYTES: [u8; 32] = [0x19; 32];
const PROFILE_BINDING_BYTES: [u8; 32] = [0x2A; 32];
const RELEASE_BINDING_BYTES: [u8; 32] = [0x3B; 32];
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [0x4C; 32];

fn legacy(bytes: [u8; 32]) -> LegacyPubkey {
    LegacyPubkey::new_from_array(bytes)
}

fn address(key: &LegacyPubkey) -> Address {
    Address::from(key.to_bytes())
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 101 * index as u32))
}

fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
    let mut state = Sha256::new();
    for input in inputs {
        state.update(input);
    }
    state.finalize().into()
}

fn sha256_hex(bytes: &[u8]) -> String {
    sha256(&[bytes])
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
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

fn meta(key: LegacyPubkey, signer: bool, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(address(&key), signer)
    } else {
        AccountMeta::new_readonly(address(&key), signer)
    }
}

fn transaction(svm: &LiteSVM, payer: &Keypair, instruction: Instruction) -> Transaction {
    Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(COMPUTE_UNIT_LIMIT),
            instruction,
        ],
        Some(&payer.pubkey()),
        &[payer],
        svm.latest_blockhash(),
    )
}

fn run_success(
    svm: &mut LiteSVM,
    payer: &Keypair,
    name: &str,
    instruction: Instruction,
    expected_return: Option<(&[u8; 4], usize)>,
) -> Result<TransactionMetadata> {
    let tx = transaction(svm, payer, instruction);
    let simulation = svm.simulate_transaction(tx.clone()).map_err(|failed| {
        anyhow!(
            "{name} simulation failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    let executed = svm.send_transaction(tx).map_err(|failed| {
        anyhow!(
            "{name} execution failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    ensure!(
        simulation.meta == executed,
        "{name}: simulation/execution mismatch"
    );
    match expected_return {
        Some((magic, bytes)) => ensure!(
            executed.return_data.program_id == Address::from(POOL_PROGRAM_BYTES)
                && executed.return_data.data.len() == bytes
                && executed.return_data.data[..4] == magic[..],
            "{name}: wrong return data"
        ),
        None => ensure!(
            executed.return_data.data.is_empty(),
            "{name}: unexpected return data"
        ),
    }
    Ok(executed)
}

fn run_rejection(
    svm: &mut LiteSVM,
    payer: &Keypair,
    name: &str,
    instruction: Instruction,
) -> Result<(u64, String)> {
    let tx = transaction(svm, payer, instruction);
    let simulation = svm
        .simulate_transaction(tx.clone())
        .expect_err("rejection simulation unexpectedly accepted");
    let executed = svm
        .send_transaction(tx)
        .expect_err("rejection execution unexpectedly accepted");
    ensure!(
        simulation.err == executed.err,
        "{name}: rejection error mismatch"
    );
    ensure!(
        simulation.meta == executed.meta,
        "{name}: rejection metadata mismatch"
    );
    ensure!(
        executed.meta.return_data.data.is_empty(),
        "{name}: rejection exposed return data"
    );
    Ok((
        executed.meta.compute_units_consumed,
        format!("{:?}", executed.err),
    ))
}

fn parse_args() -> Result<(PathBuf, PathBuf)> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        args.len() == 2,
        "usage: harness <aspis_pool.so> <evidence.json>"
    );
    Ok((PathBuf::from(&args[0]), PathBuf::from(&args[1])))
}

fn main() -> Result<()> {
    let (artifact_path, output_path) = parse_args()?;
    ensure!(
        !output_path.exists(),
        "refusing to overwrite {}",
        output_path.display()
    );
    let artifact =
        fs::read(&artifact_path).with_context(|| format!("read {}", artifact_path.display()))?;
    let artifact_sha = sha256_hex(&artifact);
    let pool_program = legacy(POOL_PROGRAM_BYTES);
    let verifier_program = legacy(VERIFIER_PROGRAM_BYTES);
    let registry_program = legacy(REGISTRY_PROGRAM_BYTES);
    let mint = legacy([0x51; 32]);
    let pool = pool_v1_state_address(&pool_program, &mint).0;
    let page = pool_v1_root_page_address(&pool_program, &pool, 0).0;
    let next_page = pool_v1_root_page_address(&pool_program, &pool, 1).0;
    let policy = VerifierPolicyV1 {
        flags: 0,
        registry_program: REGISTRY_PROGRAM_BYTES,
        registry_authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
    };
    let initialization = PoolInitializationV1 {
        asset_mint: mint.to_bytes(),
        token_program: aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
        asset_id: M31(73),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        verifier_policy: policy,
    };
    let mut state = PoolStateV1::genesis(&pool, initialization)?;
    let mut page_model = RootHistoryPageV1::genesis(pool.to_bytes(), state.tree.root);
    for index in 0..SOURCE_SEQUENCE_TARGET {
        let (next_tree, receipt) = state
            .tree
            .append_one(digest(10_000 + index as u32))
            .map_err(|error| anyhow!("seed populated tree at {index}: {error:?}"))?;
        page_model
            .push(receipt.root_sequence, receipt.root)
            .map_err(|error| anyhow!("retain seeded root at {index}: {error:?}"))?;
        state.tree = next_tree;
    }
    let source_sequence = state.current_root_sequence();
    let page_image = page_model
        .encode()
        .map_err(|error| anyhow!("encode genesis root history: {error:?}"))?;

    let nullifier = digest(30_000);
    let recipient = digest(31_000);
    let change = digest(32_000);
    let public_statement = PoolV1PrivateTransferPublicV1 {
        pool: pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: source_sequence,
        anchor_root: state.tree.root,
        nullifier,
        asset_id: M31(73),
        recipient_commitment: recipient,
        change_commitment: change,
    };
    let statement_payload = encode_pool_v1_private_transfer_public_v1(&public_statement)
        .map_err(|error| anyhow!("encode private-transfer statement: {error:?}"))?;
    ensure!(statement_payload.len() == POOL_V1_PAYMENT_STATEMENT_BYTES);
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: source_sequence,
        anchor_root: state.tree.root,
        nullifier,
        verifier_profile: PROFILE_BINDING_BYTES,
        verifier_release: RELEASE_BINDING_BYTES,
    };
    let statement_digest = verifier_statement_payload_digest_v1(
        1,
        &PROFILE_BINDING_BYTES,
        &RELEASE_BINDING_BYTES,
        &statement_payload,
        sha256,
    )
    .map_err(|error| anyhow!("derive statement digest: {error:?}"))?;
    let proof_account = legacy([0x71; 32]);
    let binding = VerifierDispatchBindingV1 {
        statement_version: 1,
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        verifier_program: VERIFIER_PROGRAM_BYTES,
        profile_binding: PROFILE_BINDING_BYTES,
        release_binding: RELEASE_BINDING_BYTES,
        pool: pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: source_sequence,
        anchor_root: state.tree.root,
        nullifier,
        statement_digest,
        envelope_digest: historical_anchor_envelope_digest_v1(&envelope, sha256)
            .map_err(|error| anyhow!("derive envelope digest: {error:?}"))?,
        proof_account: proof_account.to_bytes(),
        proof_body_digest: [0x72; 32],
        proof_body_length: 30_504,
        statement_payload_length: statement_payload.len() as u32,
    };
    let request = VerifierDispatchRequestV1 {
        binding,
        statement_payload: &statement_payload,
    };
    let inputs = pool_v1_authorization_receipt_pda_inputs_for_binding_v1(&binding, 0, sha256)
        .map_err(|error| anyhow!("derive receipt PDA inputs: {error:?}"))?;
    let (receipt_address, receipt_bump) = LegacyPubkey::find_program_address(
        &[
            POOL_V1_AUTHORIZATION_RECEIPT_SEED,
            &inputs.proof_account,
            &inputs.statement_digest,
            &inputs.binding_digest,
        ],
        &verifier_program,
    );
    let pending = initialize_pool_v1_authorization_receipt_account_v1(
        &request,
        binding.proof_account,
        [0x46; 32],
        Some([0x46; 32]),
        [0x47; 32],
        receipt_bump,
        sha256,
    )
    .map_err(|error| anyhow!("initialize receipt image: {error:?}"))?;
    let receipt_image = finalize_pool_v1_authorization_receipt_account_v1(
        &pending,
        &request,
        &PoolV1AuthorizationReceiptV1 {
            pda_bump: receipt_bump,
            verified_slot: 100,
            binding,
        },
        sha256,
    )
    .map_err(|error| anyhow!("finalize receipt image: {error:?}"))?;
    ensure!(receipt_image.len() == POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES);

    let registry = aspis_pool::pool_v1_verifier_registry_address(&registry_program, &pool).0;
    let entry = aspis_pool::pool_v1_verifier_entry_address(
        &registry_program,
        &pool,
        &PROFILE_BINDING_BYTES,
        &RELEASE_BINDING_BYTES,
    )
    .0;
    let registry_image = encode_verifier_registry_v1(&VerifierRegistryV1 {
        flags: 0,
        pool: pool.to_bytes(),
        authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
        generation: 1,
        minimum_activation_delay_slots: 1,
    })
    .map_err(|error| anyhow!("encode registry: {error:?}"))?;
    let entry_image = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Active,
        statement_version: 1,
        pool: pool.to_bytes(),
        verifier_program: VERIFIER_PROGRAM_BYTES,
        profile_binding: PROFILE_BINDING_BYTES,
        release_binding: RELEASE_BINDING_BYTES,
        activation_slot: 90,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: POLICY_BINDING_BYTES,
    })
    .map_err(|error| anyhow!("encode registry entry: {error:?}"))?;

    let payer = Keypair::new_from_array([1u8; 32]);
    let payer_legacy = legacy(payer.pubkey().to_bytes());
    let plan = pool_v1_prepared_settlement_plan_address(
        &pool_program,
        &pool,
        &statement_digest,
        source_sequence,
        &payer_legacy,
    )
    .0;
    let rollover_plan = pool_v1_prepared_settlement_rollover_address(&pool_program, &plan).0;
    let marker = pool_v1_nullifier_marker_address(
        &pool_program,
        &pool,
        &encode_digest_canonical(&nullifier),
    )?
    .0;
    let spend = encode_private_transfer_instruction_v1(
        &envelope,
        &PrivateTransferStatementV1 {
            pool: public_statement.pool,
            deployment_domain: public_statement.deployment_domain,
            anchor_sequence: public_statement.anchor_sequence,
            anchor_root: public_statement.anchor_root,
            nullifier: public_statement.nullifier,
            asset_id: public_statement.asset_id,
            recipient_commitment: public_statement.recipient_commitment,
            change_commitment: public_statement.change_commitment,
        },
    )
    .map_err(|error| anyhow!("encode nested private transfer: {error:?}"))?;
    let prepare_data = encode_prepare_settlement_instruction_v1(
        PoolV1TransitionKind::PrivateTransfer,
        110,
        200,
        &spend,
    )
    .map_err(|error| anyhow!("encode prepare instruction: {error:?}"))?;
    let settle_data = encode_settle_prepared_instruction_v1(
        PoolV1TransitionKind::PrivateTransfer,
        &statement_payload,
    )
    .map_err(|error| anyhow!("encode settle instruction: {error:?}"))?;

    let mut svm = LiteSVM::new();
    svm.add_program(address(&pool_program), &artifact)?;
    svm.warp_to_slot(PROFILE_SLOT);
    svm.airdrop(&payer.pubkey(), 10_000_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    put_account(&mut svm, pool, pool_program, state.encode()?.to_vec())?;
    put_account(&mut svm, page, pool_program, page_image.to_vec())?;
    put_account(
        &mut svm,
        receipt_address,
        verifier_program,
        receipt_image.to_vec(),
    )?;
    put_account(
        &mut svm,
        registry,
        registry_program,
        registry_image.to_vec(),
    )?;
    put_account(&mut svm, entry, registry_program, entry_image.to_vec())?;
    // Profile the plan-construction kernel independently of System account
    // creation.  The public processor accepts an exact rent-exempt, all-zero,
    // Pool-owned PDA and rechecks it before persisting the authenticated image.
    put_account(
        &mut svm,
        plan,
        pool_program,
        vec![0u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES],
    )?;
    put_account(
        &mut svm,
        next_page,
        pool_program,
        vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    )?;
    put_account(
        &mut svm,
        rollover_plan,
        pool_program,
        vec![0u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES],
    )?;

    let pool_before_prepare = svm.get_account(&address(&pool)).context("pool missing")?;
    let page_before_prepare = svm.get_account(&address(&page)).context("page missing")?;
    let next_page_before_prepare = svm
        .get_account(&address(&next_page))
        .context("next page missing")?;
    let prepare_instruction = Instruction {
        program_id: address(&pool_program),
        accounts: vec![
            meta(payer_legacy, true, true),
            meta(pool, false, true),
            meta(page, false, false),
            meta(next_page, false, true),
            meta(receipt_address, false, false),
            meta(registry, false, false),
            meta(entry, false, false),
            meta(plan, false, true),
            meta(rollover_plan, false, true),
            meta(legacy(system_program::id().to_bytes()), false, false),
        ],
        data: prepare_data.to_vec(),
    };
    let prepare_tx_bytes =
        wincode::serialize(&transaction(&svm, &payer, prepare_instruction.clone()))?.len();
    let prepare_meta = run_success(
        &mut svm,
        &payer,
        "prepare_private_transfer",
        prepare_instruction,
        None,
    )?;
    ensure!(
        svm.get_account(&address(&pool)).as_ref() == Some(&pool_before_prepare)
            && svm.get_account(&address(&page)).as_ref() == Some(&page_before_prepare)
            && svm.get_account(&address(&next_page)).as_ref() == Some(&next_page_before_prepare),
        "preparation mutated live Pool state"
    );
    let plan_after_prepare = svm
        .get_account(&address(&plan))
        .context("prepared core PDA missing")?;
    ensure!(
        plan_after_prepare.owner == address(&pool_program)
            && plan_after_prepare.data.len() == POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES,
        "prepared core PDA has wrong owner/size"
    );
    let rollover_after_prepare = svm
        .get_account(&address(&rollover_plan))
        .context("prepared rollover PDA missing")?;
    ensure!(
        rollover_after_prepare.owner == address(&pool_program)
            && rollover_after_prepare.data.len()
                == POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES,
        "prepared rollover PDA has wrong owner/size"
    );

    svm.expire_blockhash();
    let settle_instruction = Instruction {
        program_id: address(&pool_program),
        accounts: vec![
            meta(payer_legacy, true, true),
            meta(pool, false, true),
            meta(page, false, true),
            meta(next_page, false, true),
            meta(marker, false, true),
            meta(receipt_address, false, false),
            meta(registry, false, false),
            meta(entry, false, false),
            meta(plan, false, true),
            meta(rollover_plan, false, true),
            meta(legacy(system_program::id().to_bytes()), false, false),
        ],
        data: settle_data.to_vec(),
    };
    let settle_tx_bytes =
        wincode::serialize(&transaction(&svm, &payer, settle_instruction.clone()))?.len();
    let settle_meta = run_success(
        &mut svm,
        &payer,
        "settle_private_transfer",
        settle_instruction.clone(),
        Some((b"ASTR", 200)),
    )?;
    let state_after = PoolStateV1::decode(
        &svm.get_account(&address(&pool))
            .context("pool missing after settle")?
            .data,
        &pool,
    )?;
    ensure!(state_after.current_root_sequence() == source_sequence + 2);
    let current_page_after = svm
        .get_account(&address(&page))
        .context("current history page missing after settle")?;
    let next_page_after = svm
        .get_account(&address(&next_page))
        .context("rollover history page missing after settle")?;
    let penultimate_root =
        read_root_history_page_root_v1(&current_page_after.data, source_sequence + 1)
            .map_err(|error| anyhow!("read penultimate retained root: {error:?}"))?;
    let final_root = read_root_history_page_root_v1(&next_page_after.data, source_sequence + 2)
        .map_err(|error| anyhow!("read final retained root: {error:?}"))?;
    ensure!(
        final_root == state_after.tree.root && penultimate_root != final_root,
        "rollover history roots do not match the final Pool state"
    );
    let marker_account = svm
        .get_account(&address(&marker))
        .context("nullifier marker missing")?;
    ensure!(
        marker_account.owner == address(&pool_program)
            && marker_account.data.len() == POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES
    );
    let decoded_marker = decode_pool_v1_nullifier_marker(&marker_account.data)
        .map_err(|error| anyhow!("decode nullifier marker: {error:?}"))?;
    ensure!(decoded_marker.nullifier == nullifier && decoded_marker.pool == pool.to_bytes());
    let plan_closed = svm
        .get_account(&address(&plan))
        .map(|account| account.lamports == 0)
        .unwrap_or(true);
    ensure!(plan_closed, "prepared core PDA was not closed/refunded");
    let rollover_plan_closed = svm
        .get_account(&address(&rollover_plan))
        .map(|account| account.lamports == 0)
        .unwrap_or(true);
    ensure!(
        rollover_plan_closed,
        "prepared rollover PDA was not closed/refunded"
    );

    let pool_before_replay = svm.get_account(&address(&pool));
    let page_before_replay = svm.get_account(&address(&page));
    let next_page_before_replay = svm.get_account(&address(&next_page));
    let marker_before_replay = svm.get_account(&address(&marker));
    svm.expire_blockhash();
    let (replay_cu, replay_error) =
        run_rejection(&mut svm, &payer, "replay_consumed_plan", settle_instruction)?;
    ensure!(
        svm.get_account(&address(&pool)) == pool_before_replay
            && svm.get_account(&address(&page)) == page_before_replay
            && svm.get_account(&address(&next_page)) == next_page_before_replay
            && svm.get_account(&address(&marker)) == marker_before_replay,
        "rejected replay mutated Pool state"
    );

    ensure!(prepare_meta.compute_units_consumed < COMPUTE_UNIT_LIMIT as u64);
    ensure!(settle_meta.compute_units_consumed < COMPUTE_UNIT_LIMIT as u64);
    ensure!(prepare_tx_bytes <= 1_232 && settle_tx_bytes <= 1_232);
    let evidence = serde_json::json!({
        "schema": "aspis.pool-v1.prepared-runtime-evidence.v1",
        "profile_slot": PROFILE_SLOT,
        "compute_unit_limit": COMPUTE_UNIT_LIMIT,
        "artifact": {
            "path": artifact_path,
            "bytes": artifact.len(),
            "sha256": artifact_sha,
            "source_note": "focused current-worktree profile; reproducible clean-source release build remains a later gate"
        },
        "prepare": {
            "compute_units": prepare_meta.compute_units_consumed,
            "transaction_bytes": prepare_tx_bytes,
            "live_pool_and_history_unchanged": true,
            "core_plan_bytes": POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES,
            "rollover_plan_bytes": POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES,
            "core_plan_owner_exact": true,
            "profile_plan_account_preallocated": true,
            "profile_rollover_accounts_preallocated": true,
            "profile_next_history_page_preallocated": true
        },
        "settle": {
            "compute_units": settle_meta.compute_units_consumed,
            "transaction_bytes": settle_tx_bytes,
            "return_magic": "ASTR",
            "return_bytes": 200,
            "sequence_before": source_sequence,
            "sequence_after": state_after.current_root_sequence(),
            "two_ordered_outputs": true,
            "nullifier_marker_exact": true,
            "plan_closed_and_refunded": true,
            "rollover_plan_closed_and_refunded": true,
            "rollover_history_page_applied": true
        },
        "replay": {
            "outcome": "rejected",
            "compute_units": replay_cu,
            "error": replay_error,
            "pool_history_marker_byte_exact": true
        },
        "assertions": {
            "simulation_equals_execution_for_successes_and_replay": true,
            "prepare_under_1400000_cu": true,
            "settle_under_1400000_cu": true,
            "both_transactions_fit_1232_bytes": true,
            "preparation_is_not_a_state_transition": true,
            "settlement_is_atomic_and_one_shot": true,
            "private_transfer_crosses_root_page_254_to_256": true,
            "no_network_send_or_deploy": true
        },
        "boundaries": [
            "The finalized authorization receipt is injected as a canonical verifier-owned account image; this profile isolates Pool preparation and settlement rather than re-running Tag-73 verification.",
            "The core plan PDA, rollover-plan PDA and next history-page PDA are preallocated as exact rent-exempt all-zero Pool accounts to measure authenticated construction separately from System account creation.",
            "This is deterministic LiteSVM execution, not finalized devnet evidence.",
            "The profiled SBF was built from the current worktree; clean-source reproducibility is a separate release gate."
        ]
    });
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)?;
    }
    if output_path.exists() {
        bail!("refusing to overwrite {}", output_path.display());
    }
    fs::write(&output_path, serde_json::to_vec_pretty(&evidence)?)?;
    println!(
        "prepared Pool path PASS: prepare={} CU settle={} CU replay={} CU",
        prepare_meta.compute_units_consumed, settle_meta.compute_units_consumed, replay_cu
    );
    println!("evidence={}", output_path.display());
    Ok(())
}
