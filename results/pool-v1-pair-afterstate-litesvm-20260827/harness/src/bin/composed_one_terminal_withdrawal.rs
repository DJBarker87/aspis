use std::{env, fs, path::PathBuf};

use anyhow::{anyhow, bail, ensure, Context, Result};
use aspis_core::field::M31;
use aspis_pool::{
    encode_pair_withdrawal_instruction_v1, pool_v1_nullifier_marker_address,
    pool_v1_pair_state_address, pool_v1_root_page_address, pool_v1_vault_authority_address,
    pool_v1_vault_token_account_address, PairPoolStateV1, PoolInitializationV1,
    WithdrawalStatementV1, LEGACY_SPL_TOKEN_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES,
    POOL_V1_EMPTY_ROOTS, POOL_V1_PAIR_STATE_ACCOUNT_BYTES,
};
use aspis_statement::{
    derive_owner_key, encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, encode_pool_v1_pair_verified_afterstate_v1,
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1, pool_v1_membership_root_v1,
        pool_v1_note_commitment, pool_v1_nullifier, root_history_location,
        HistoricalAnchorEnvelopeV1, PoolV1MembershipWitnessV1, PoolV1PairLeafWitnessV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1TransitionKind, RootHistoryPageV1,
        VerifierEntryStatusV1, VerifierPolicyV1, VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
        V7_POOL_NATIVE_TAG73_PROFILE_BINDING, V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
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
use solana_signer::Signer;
use solana_transaction::Transaction;

const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
const PROFILE_SLOT: u64 = 150;
const MEMBERSHIP_ANCHOR_SEQUENCE: u64 = 1;
const POOL_PROGRAM_BYTES: [u8; 32] = [0xA5; 32];
const VERIFIER_PROGRAM_BYTES: [u8; 32] = [0xB6; 32];
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0xC7; 32];
const REGISTRY_AUTHORITY_BYTES: [u8; 32] = [0xD8; 32];
const POLICY_BINDING_BYTES: [u8; 32] = [0x19; 32];
const PROFILE_BINDING_BYTES: [u8; 32] = V7_POOL_NATIVE_TAG73_PROFILE_BINDING;
const RELEASE_BINDING_BYTES: [u8; 32] = V7_POOL_NATIVE_TAG73_RELEASE_BINDING;
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [0x4C; 32];
const WITHDRAWAL_AMOUNT: u32 = 25_000;
const VAULT_BALANCE_BEFORE: u64 = 1_000_000;
const DESTINATION_BALANCE_BEFORE: u64 = 7_000;
const TOKEN_DECIMALS: u8 = 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    SamePage,
    Rollover,
    WithdrawalSamePage,
}

#[derive(Debug)]
struct CuMarker {
    label: String,
    remaining: u64,
    delta_from_previous: Option<i64>,
}

fn parse_cu_markers(logs: &[String]) -> Vec<CuMarker> {
    let mut pending = None;
    let mut previous = None;
    let mut markers = Vec::new();
    for log in logs {
        if let Some((_, suffix)) = log.split_once("aspis-pair-cu:") {
            pending = Some(format!("pool:{}", suffix.trim()));
            continue;
        }
        if let Some((_, suffix)) = log.split_once("aspis-v7-profile:") {
            pending = Some(format!("verifier:{}", suffix.trim()));
            continue;
        }
        let Some((_, rest)) = log.split_once("Program consumption:") else {
            continue;
        };
        let Some(label) = pending.take() else {
            continue;
        };
        let Some(remaining) = rest
            .split_whitespace()
            .find_map(|token| token.parse::<u64>().ok())
        else {
            continue;
        };
        let delta_from_previous = previous.map(|prior| prior as i64 - remaining as i64);
        previous = Some(remaining);
        markers.push(CuMarker {
            label,
            remaining,
            delta_from_previous,
        });
    }
    markers
}

impl Mode {
    fn parse(value: &str) -> Result<Self> {
        match value {
            "same-page" => Ok(Self::SamePage),
            "rollover" => Ok(Self::Rollover),
            "withdrawal-same-page" => Ok(Self::WithdrawalSamePage),
            _ => bail!("mode must be same-page, rollover or withdrawal-same-page"),
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::SamePage => "same-page",
            Self::Rollover => "rollover",
            Self::WithdrawalSamePage => "withdrawal-same-page",
        }
    }

    fn source_sequence(self) -> u64 {
        match self {
            Self::SamePage => 100,
            Self::Rollover => 255,
            Self::WithdrawalSamePage => 100,
        }
    }

    fn is_rollover(self) -> bool {
        self == Self::Rollover
    }
}

fn legacy(bytes: [u8; 32]) -> LegacyPubkey {
    LegacyPubkey::new_from_array(bytes)
}

fn address(key: &LegacyPubkey) -> Address {
    Address::from(key.to_bytes())
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 101 * index as u32))
}

fn native_digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 29 * index as u32))
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn sha256_hex(bytes: &[u8]) -> String {
    sha256(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn legacy_mint_image(supply: u64) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
    data[36..44].copy_from_slice(&supply.to_le_bytes());
    data[44] = TOKEN_DECIMALS;
    data[45] = 1;
    data
}

fn legacy_token_image(mint: LegacyPubkey, authority: LegacyPubkey, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
    data[..32].copy_from_slice(mint.as_ref());
    data[32..64].copy_from_slice(authority.as_ref());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1;
    data
}

fn token_amount(data: &[u8]) -> Result<u64> {
    ensure!(data.len() == LEGACY_SPL_TOKEN_ACCOUNT_BYTES);
    Ok(u64::from_le_bytes(data[64..72].try_into()?))
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
    ensure!(simulation.meta == executed, "simulation/execution mismatch");
    ensure!(
        executed.return_data.program_id == Address::from(POOL_PROGRAM_BYTES)
            && executed.return_data.data.len() == 200
            && executed.return_data.data[..4] == *b"ASTR",
        "wrong Pool transition receipt"
    );
    Ok(executed)
}

fn parse_args() -> Result<(PathBuf, PathBuf, PathBuf, PathBuf)> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        args.len() == 4,
        "usage: composed_one_terminal <aspis_pool.so> <verifier.so> <proof.bin> <evidence.json>"
    );
    Ok((
        PathBuf::from(&args[0]),
        PathBuf::from(&args[1]),
        PathBuf::from(&args[2]),
        PathBuf::from(&args[3]),
    ))
}

fn main() -> Result<()> {
    let (pool_artifact_path, verifier_artifact_path, proof_path, output_path) = parse_args()?;
    let mode = Mode::WithdrawalSamePage;
    ensure!(
        !output_path.exists(),
        "refusing to overwrite {}",
        output_path.display()
    );
    let pool_artifact = fs::read(&pool_artifact_path)
        .with_context(|| format!("read {}", pool_artifact_path.display()))?;
    let verifier_artifact = fs::read(&verifier_artifact_path)
        .with_context(|| format!("read {}", verifier_artifact_path.display()))?;
    let proof_body =
        fs::read(&proof_path).with_context(|| format!("read {}", proof_path.display()))?;
    ensure!(proof_body.len() == 30_192, "preserved proof length changed");
    ensure!(
        sha256_hex(&proof_body)
            == "656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c",
        "preserved proof digest changed"
    );

    let pool_program = legacy(POOL_PROGRAM_BYTES);
    let verifier_program = legacy(VERIFIER_PROGRAM_BYTES);
    let registry_program = legacy(REGISTRY_PROGRAM_BYTES);
    let mint = legacy([0x51; 32]);
    let pool = pool_v1_pair_state_address(&pool_program, &mint).0;
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
    let mut state = PairPoolStateV1::genesis(&pool, initialization)?;
    let mut page = RootHistoryPageV1::genesis(pool.to_bytes(), state.tree.root);
    for index in 0..mode.source_sequence() {
        let (next, receipt) =
            state.append_verified_pair_from_program_invariant(digest(10_000 + index as u32))?;
        page.push(receipt.root_sequence, receipt.root)
            .map_err(|error| anyhow!("seed root page: {error:?}"))?;
        state = next;
    }
    ensure!(state.current_root_sequence() == mode.source_sequence());
    let input_note = pool_v1_note_commitment(
        &derive_owner_key(&native_digest(10)),
        1_000,
        M31(73),
        &native_digest(700),
    );
    let membership_anchor_root = pool_v1_membership_root_v1(
        input_note,
        &PoolV1MembershipWitnessV1 {
            siblings: core::array::from_fn(|level| POOL_V1_EMPTY_ROOTS[level]),
            index: 0,
        },
    )
    .map_err(|error| anyhow!("derive preserved anchor: {error:?}"))?;
    let page_zero = pool_v1_root_page_address(&pool_program, &pool, 0).0;
    let page_one = pool_v1_root_page_address(&pool_program, &pool, 1).0;
    let mut page_zero_image = page
        .encode()
        .map_err(|error| anyhow!("encode root page: {error:?}"))?;
    let anchor_offset = 64 + MEMBERSHIP_ANCHOR_SEQUENCE as usize * 32;
    page_zero_image[anchor_offset..anchor_offset + 32]
        .copy_from_slice(&encode_digest_canonical(&membership_anchor_root));

    let nullifier = pool_v1_nullifier(&native_digest(10), &native_digest(700));
    let _recipient =
        pool_v1_note_commitment(&native_digest(2_300), 600, M31(73), &native_digest(2_400));
    let change =
        pool_v1_note_commitment(&native_digest(2_500), 400, M31(73), &native_digest(2_600));
    let pair_leaf = PoolV1PairLeafWitnessV1::single_output(change)
        .and_then(|witness| witness.leaf_digest())
        .map_err(|error| anyhow!("single-output pair leaf: {error:?}"))?;
    let (expected_state, expected_append) =
        state.append_verified_pair_from_program_invariant(pair_leaf)?;
    let afterstate = encode_pool_v1_pair_verified_afterstate_v1(&PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: expected_state.tree.next_leaf_index,
        next_root: expected_state.tree.root,
        next_frontier: expected_state.tree.frontier,
    })
    .map_err(|error| anyhow!("encode ASJA: {error:?}"))?;
    ensure!(afterstate.len() == POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES);
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::Withdrawal,
        pool: pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: MEMBERSHIP_ANCHOR_SEQUENCE,
        anchor_root: membership_anchor_root,
        nullifier,
        verifier_profile: PROFILE_BINDING_BYTES,
        verifier_release: RELEASE_BINDING_BYTES,
    };
    let destination = legacy([0x62; 32]);
    let spend = encode_pair_withdrawal_instruction_v1(
        &envelope,
        &WithdrawalStatementV1 {
            pool: pool.to_bytes(),
            deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
            anchor_sequence: MEMBERSHIP_ANCHOR_SEQUENCE,
            anchor_root: membership_anchor_root,
            nullifier,
            asset_id: M31(73),
            amount: WITHDRAWAL_AMOUNT,
            destination_token_account: destination.to_bytes(),
            change_commitment: change,
        },
    )
    .map_err(|error| anyhow!("encode pair withdrawal: {error:?}"))?;

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

    let proof = legacy([0x71; 32]);
    let body_bytes = proof_body.len() + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let mut proof_image = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + body_bytes];
    proof_image[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
    proof_image[4..8].copy_from_slice(&(body_bytes as u32).to_le_bytes());
    let proof_end = POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + proof_body.len();
    proof_image[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..proof_end]
        .copy_from_slice(&proof_body);
    proof_image[proof_end..].copy_from_slice(&afterstate);
    let marker = pool_v1_nullifier_marker_address(
        &pool_program,
        &pool,
        &encode_digest_canonical(&nullifier),
    )?
    .0;
    let token_program = aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID;
    let vault = pool_v1_vault_token_account_address(&pool_program, &pool).0;
    let vault_authority = pool_v1_vault_authority_address(&pool_program, &pool).0;

    let payer = Keypair::new_from_array([1u8; 32]);
    let mut svm = LiteSVM::new();
    svm.add_program(address(&pool_program), &pool_artifact)?;
    svm.add_program(address(&verifier_program), &verifier_artifact)?;
    svm.warp_to_slot(PROFILE_SLOT);
    svm.airdrop(&payer.pubkey(), 10_000_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    put_account(&mut svm, pool, pool_program, state.encode()?.to_vec())?;
    put_account(&mut svm, page_zero, pool_program, page_zero_image.to_vec())?;
    if mode == Mode::Rollover {
        put_account(
            &mut svm,
            page_one,
            pool_program,
            vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
        )?;
    }
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
    put_account(&mut svm, proof, verifier_program, proof_image)?;
    put_account(
        &mut svm,
        mint,
        token_program,
        legacy_mint_image(VAULT_BALANCE_BEFORE + DESTINATION_BALANCE_BEFORE),
    )?;
    put_account(
        &mut svm,
        vault,
        token_program,
        legacy_token_image(mint, vault_authority, VAULT_BALANCE_BEFORE),
    )?;
    put_account(
        &mut svm,
        destination,
        token_program,
        legacy_token_image(mint, legacy([0x63; 32]), DESTINATION_BALANCE_BEFORE),
    )?;
    put_account(
        &mut svm,
        vault_authority,
        LegacyPubkey::default(),
        Vec::new(),
    )?;

    let page_zero_before = svm
        .get_account(&address(&page_zero))
        .context("page zero missing")?;
    let mut accounts = vec![meta(pool, true), meta(page_zero, !mode.is_rollover())];
    if mode.is_rollover() {
        accounts.push(meta(page_one, true));
    }
    accounts.extend_from_slice(&[
        meta(marker, true),
        meta(registry, false),
        meta(entry, false),
        meta(verifier_program, false),
        meta(proof, false),
        meta(mint, false),
        meta(vault, true),
        meta(destination, true),
        meta(vault_authority, false),
        meta(token_program, false),
    ]);
    let instruction = Instruction {
        program_id: address(&pool_program),
        accounts,
        data: spend.to_vec(),
    };
    let tx_bytes = wincode::serialize(&transaction(&svm, &payer, instruction.clone()))?.len();
    ensure!(tx_bytes <= 1_232, "transaction exceeds Solana wire limit");
    let executed = run_success(
        &mut svm,
        &payer,
        &format!("pair_afterstate_{}", mode.label()),
        instruction,
    )?;
    ensure!(executed.compute_units_consumed < COMPUTE_UNIT_LIMIT as u64);
    let cu_markers = parse_cu_markers(&executed.logs);
    for required in [
        "pool:handler_entry",
        "pool:verifier_cpi_start",
        "verifier:entry",
        "verifier:proof-accepted",
        "verifier:asja-return-set",
        "pool:verifier_cpi_complete",
        "pool:custody_cpi_start",
        "pool:custody_cpi_complete",
        "pool:custody_delta_validated",
        "pool:history_written",
        "pool:receipt_returned",
    ] {
        ensure!(
            cu_markers.iter().any(|marker| marker.label == required),
            "missing profile marker {required}: {:?}",
            cu_markers
        );
    }

    let pool_after_account = svm
        .get_account(&address(&pool))
        .context("pool missing after")?;
    ensure!(pool_after_account.data.len() == POOL_V1_PAIR_STATE_ACCOUNT_BYTES);
    ensure!(
        pool_after_account.data == expected_state.encode()?.to_vec(),
        "Pool afterstate mismatch"
    );
    let marker_after = svm
        .get_account(&address(&marker))
        .context("marker missing after")?;
    let marker_decoded = decode_pool_v1_nullifier_marker(&marker_after.data)
        .map_err(|error| anyhow!("decode marker: {error:?}"))?;
    ensure!(marker_decoded.nullifier == nullifier);
    ensure!(marker_decoded.retained_anchor_sequence == MEMBERSHIP_ANCHOR_SEQUENCE);
    ensure!(marker_decoded.retained_anchor_root == membership_anchor_root);

    let target_page = if mode.is_rollover() {
        page_one
    } else {
        page_zero
    };
    let target_after = svm
        .get_account(&address(&target_page))
        .context("target history page missing after")?;
    let target_location = root_history_location(expected_append.root_sequence);
    let retained = aspis_statement::pool_v1::root_history::read_root_history_page_root_v1(
        &target_after.data,
        expected_append.root_sequence,
    )
    .map_err(|error| anyhow!("read appended root: {error:?}"))?;
    ensure!(retained == expected_append.root);
    let page_zero_after = svm
        .get_account(&address(&page_zero))
        .context("page zero missing after")?;
    let anchor_after = aspis_statement::pool_v1::root_history::read_root_history_page_root_v1(
        &page_zero_after.data,
        MEMBERSHIP_ANCHOR_SEQUENCE,
    )
    .map_err(|error| anyhow!("read membership anchor after: {error:?}"))?;
    ensure!(anchor_after == membership_anchor_root);
    if mode.is_rollover() {
        ensure!(
            page_zero_after == page_zero_before,
            "rollover mutated full prior page"
        );
    }
    let vault_account = svm
        .get_account(&address(&vault))
        .context("vault missing after")?;
    let destination_account = svm
        .get_account(&address(&destination))
        .context("destination missing after")?;
    let vault_after = token_amount(&vault_account.data)?;
    let destination_after = token_amount(&destination_account.data)?;
    ensure!(
        vault_after == VAULT_BALANCE_BEFORE - u64::from(WITHDRAWAL_AMOUNT),
        "wrong exact vault debit"
    );
    ensure!(
        destination_after == DESTINATION_BALANCE_BEFORE + u64::from(WITHDRAWAL_AMOUNT),
        "wrong exact destination credit"
    );

    let cu_marker_json = cu_markers
        .iter()
        .map(|marker| {
            serde_json::json!({
                "label": marker.label,
                "remaining": marker.remaining,
                "delta_from_previous": marker.delta_from_previous,
            })
        })
        .collect::<Vec<_>>();
    let first_marker_consumed = cu_markers
        .first()
        .map(|marker| u64::from(COMPUTE_UNIT_LIMIT) - marker.remaining);
    let last_marker_to_transaction_end = cu_markers.last().map(|marker| {
        executed
            .compute_units_consumed
            .saturating_sub(u64::from(COMPUTE_UNIT_LIMIT) - marker.remaining)
    });
    let evidence = serde_json::json!({
        "schema": "aspis.pool-v1.composed-native-tag73-withdrawal-cu-diagnostic.v1",
        "mode": mode.label(),
        "profile_slot": PROFILE_SLOT,
        "compute_unit_limit": COMPUTE_UNIT_LIMIT,
        "execution": {
            "compute_units": executed.compute_units_consumed,
            "transaction_bytes": tx_bytes,
            "instruction_bytes": spend.len(),
            "account_metas_excluding_compute_budget_and_payer": 12,
            "simulation_equals_execution": true,
            "return_magic": "ASTR",
            "return_bytes": 200,
            "direct_verifier_baseline_cu": 1254737,
            "transport_double_suffix_baseline_cu": 93818,
            "incremental_over_direct_verifier_cu": executed.compute_units_consumed.saturating_sub(1254737),
            "delta_from_naive_sum_cu": executed.compute_units_consumed as i64 - 1254737 - 93818,
            "headroom_cu": u64::from(COMPUTE_UNIT_LIMIT) - executed.compute_units_consumed
        },
        "profiling": {
            "enabled": !cu_markers.is_empty(),
            "marker_calls_are_metered_and_inflate_the_profiled_total": !cu_markers.is_empty(),
            "before_first_marker_including_transaction_dispatch": first_marker_consumed,
            "after_last_marker_to_transaction_end": last_marker_to_transaction_end,
            "markers": cu_marker_json
        },
        "state_transition": {
            "membership_anchor_sequence": MEMBERSHIP_ANCHOR_SEQUENCE,
            "source_sequence": mode.source_sequence(),
            "next_sequence": expected_append.root_sequence,
            "history_target_page": target_location.page_number,
            "history_target_slot": target_location.slot,
            "historical_anchor_value_preserved": true,
            "full_prior_page_byte_exact_on_rollover": false,
            "pool_matches_verifier_afterstate": true,
            "nullifier_marker_created_once": true,
            "pool_side_poseidon_calls": 0
        },
        "custody": {
            "real_legacy_spl_token_cpi_executed": true,
            "transfer_checked": true,
            "pda_authority_signed": true,
            "amount": WITHDRAWAL_AMOUNT,
            "vault_before": VAULT_BALANCE_BEFORE,
            "vault_after": vault_after,
            "destination_before": DESTINATION_BALANCE_BEFORE,
            "destination_after": destination_after,
            "exact_pre_post_balance_delta_checked_by_pool": true
        },
        "transport": {
            "kind": "measurement-only real native Tag-73 verifier followed by fixed withdrawal ASJA transport and custody CPI",
            "request_is_registry_and_proof_account_bound": true,
            "proof_account_body_bytes": proof_body.len() + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
            "native_proof_bytes": proof_body.len(),
            "native_proof_sha256": sha256_hex(&proof_body),
            "returned_asja_bytes": POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
            "immediate_return_program_checked": true,
            "real_tag73_proof_executed": true,
            "proof_binds_returned_asja": false,
            "proof_binds_withdrawal_amount_or_destination": false,
            "outer_pair_pool_substituted_for_preserved_native_statement_pool": true,
            "outer_withdrawal_reinterpreted_as_preserved_native_private_transfer": true
        },
        "artifacts": {
            "pool": {
                "path": pool_artifact_path,
                "bytes": pool_artifact.len(),
                "sha256": sha256_hex(&pool_artifact)
            },
            "verifier_diagnostic": {
                "path": verifier_artifact_path,
                "bytes": verifier_artifact.len(),
                "sha256": sha256_hex(&verifier_artifact)
            },
            "proof": {
                "path": proof_path,
                "bytes": proof_body.len(),
                "sha256": sha256_hex(&proof_body)
            }
        },
        "toolchain": {
            "cargo_build_sbf": "solana-cargo-build-sbf 2.3.0",
            "platform_tools": "v1.48",
            "sbf_rustc": "1.84.1",
            "host_rustc": "1.93.0 (254b59607 2026-01-19)",
            "host_cargo": "1.93.0 (083ac5135 2025-12-15)",
            "litesvm": "0.16.0",
            "host": "macOS 26.5 (25F71), Darwin 25.5.0 arm64"
        },
        "boundaries": [
            "This transaction executes the preserved honest 30,192-byte native Tag-73 proof before returning ASJA, but that proof does not bind the appended 688 ASJA bytes.",
            "The preserved proof binds the legacy Pool PDA; the measurement adapter substitutes that one pool field while the outer pair Pool uses its distinct PDA. This is not a sound authorization bridge.",
            "The preserved proof is a private-transfer proof, not a withdrawal proof. The diagnostic reconstructs its fixed recipient while the outer instruction independently supplies withdrawal amount and destination; neither is authenticated by this proof.",
            "The proof and fixed ASJA are adjacent in the verifier-owned proof account only for this CU transport diagnostic.",
            "The pair entrypoint is compiled only with the measurement-only pair-afterstate-evidence feature; the default production entrypoint remains disabled.",
            "The nullifier marker is an exact pre-created Pool-owned zeroed account; System creation cost is excluded. Custody uses a real legacy SPL Token TransferChecked CPI with pre-created accounts.",
            "Pool source has no state write before verifier success, and Solana transaction atomicity rolls back the Pool/history/marker if the verifier CPI fails; the prior real-verifier red gate separately captured that exact runtime rollback.",
            "This is deterministic LiteSVM execution with no network, deploy, or transaction submission."
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
        "pair ASJA {} PASS: {} CU, {} tx bytes",
        mode.label(),
        executed.compute_units_consumed,
        tx_bytes
    );
    println!("evidence={}", output_path.display());
    Ok(())
}
