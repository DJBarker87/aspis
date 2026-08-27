use std::{env, fs, path::PathBuf};

use anyhow::{anyhow, bail, ensure, Context, Result};
use aspis_core::field::M31;
use aspis_pool::{
    encode_pair_private_transfer_instruction_v1, pool_v1_nullifier_marker_address,
    pool_v1_pair_state_address, pool_v1_root_page_address, PairPoolStateV1,
    PoolInitializationV1, PrivateTransferStatementV1, POOL_V1_PAIR_STATE_ACCOUNT_BYTES,
};
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, encode_pool_v1_pair_verified_afterstate_v1,
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1, root_history_location,
        HistoricalAnchorEnvelopeV1, PoolV1PairVerifiedAfterstateV1, PoolV1TransitionKind,
        RootHistoryPageV1, VerifierEntryStatusV1, VerifierPolicyV1,
        VerifierRegistryEntryV1, VerifierRegistryV1, POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
        POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT, POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
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
const MEMBERSHIP_ANCHOR_SEQUENCE: u64 = 50;
const POOL_PROGRAM_BYTES: [u8; 32] = [0xA5; 32];
const VERIFIER_PROGRAM_BYTES: [u8; 32] = [0xB6; 32];
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0xC7; 32];
const REGISTRY_AUTHORITY_BYTES: [u8; 32] = [0xD8; 32];
const POLICY_BINDING_BYTES: [u8; 32] = [0x19; 32];
const PROFILE_BINDING_BYTES: [u8; 32] = [0x2A; 32];
const RELEASE_BINDING_BYTES: [u8; 32] = [0x3B; 32];
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [0x4C; 32];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    SamePage,
    Rollover,
}

impl Mode {
    fn parse(value: &str) -> Result<Self> {
        match value {
            "same-page" => Ok(Self::SamePage),
            "rollover" => Ok(Self::Rollover),
            _ => bail!("mode must be same-page or rollover"),
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::SamePage => "same-page",
            Self::Rollover => "rollover",
        }
    }

    fn source_sequence(self) -> u64 {
        match self {
            Self::SamePage => 100,
            Self::Rollover => 255,
        }
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

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn sha256_hex(bytes: &[u8]) -> String {
    sha256(bytes)
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

fn parse_args() -> Result<(PathBuf, PathBuf, Mode, PathBuf)> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    ensure!(
        args.len() == 4,
        "usage: harness <aspis_pool.so> <verifier_double.so> <same-page|rollover> <evidence.json>"
    );
    Ok((
        PathBuf::from(&args[0]),
        PathBuf::from(&args[1]),
        Mode::parse(&args[2])?,
        PathBuf::from(&args[3]),
    ))
}

fn main() -> Result<()> {
    let (pool_artifact_path, verifier_artifact_path, mode, output_path) = parse_args()?;
    ensure!(
        !output_path.exists(),
        "refusing to overwrite {}",
        output_path.display()
    );
    let pool_artifact = fs::read(&pool_artifact_path)
        .with_context(|| format!("read {}", pool_artifact_path.display()))?;
    let verifier_artifact = fs::read(&verifier_artifact_path)
        .with_context(|| format!("read {}", verifier_artifact_path.display()))?;

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
    let mut membership_anchor_root = None;
    for index in 0..mode.source_sequence() {
        let (next, receipt) = state
            .append_verified_pair_from_program_invariant(digest(10_000 + index as u32))?;
        page.push(receipt.root_sequence, receipt.root)
            .map_err(|error| anyhow!("seed root page: {error:?}"))?;
        if receipt.root_sequence == MEMBERSHIP_ANCHOR_SEQUENCE {
            membership_anchor_root = Some(receipt.root);
        }
        state = next;
    }
    ensure!(state.current_root_sequence() == mode.source_sequence());
    let membership_anchor_root = membership_anchor_root.context("membership anchor missing")?;
    let page_zero = pool_v1_root_page_address(&pool_program, &pool, 0).0;
    let page_one = pool_v1_root_page_address(&pool_program, &pool, 1).0;
    let page_zero_image = page
        .encode()
        .map_err(|error| anyhow!("encode root page: {error:?}"))?;

    let nullifier = digest(30_000 + mode.source_sequence() as u32);
    let recipient = digest(31_000 + mode.source_sequence() as u32);
    let change = digest(32_000 + mode.source_sequence() as u32);
    let (expected_state, expected_append) = state
        .append_occupied_pair_from_program_invariant(recipient, change)?;
    let afterstate = encode_pool_v1_pair_verified_afterstate_v1(
        &PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: expected_state.tree.next_leaf_index,
            next_root: expected_state.tree.root,
            next_frontier: expected_state.tree.frontier,
        },
    )
    .map_err(|error| anyhow!("encode ASJA: {error:?}"))?;
    ensure!(afterstate.len() == POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES);
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: MEMBERSHIP_ANCHOR_SEQUENCE,
        anchor_root: membership_anchor_root,
        nullifier,
        verifier_profile: PROFILE_BINDING_BYTES,
        verifier_release: RELEASE_BINDING_BYTES,
    };
    let spend = encode_pair_private_transfer_instruction_v1(
        &envelope,
        &PrivateTransferStatementV1 {
            pool: pool.to_bytes(),
            deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
            anchor_sequence: MEMBERSHIP_ANCHOR_SEQUENCE,
            anchor_root: membership_anchor_root,
            nullifier,
            asset_id: M31(73),
            recipient_commitment: recipient,
            change_commitment: change,
        },
    )
    .map_err(|error| anyhow!("encode pair spend: {error:?}"))?;

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
    let mut proof_image = vec![
        0u8;
        POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
            + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    ];
    proof_image[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
    proof_image[4..8]
        .copy_from_slice(&(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES as u32).to_le_bytes());
    proof_image[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..].copy_from_slice(&afterstate);
    let marker = pool_v1_nullifier_marker_address(
        &pool_program,
        &pool,
        &encode_digest_canonical(&nullifier),
    )?
    .0;

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
    put_account(&mut svm, registry, registry_program, registry_image.to_vec())?;
    put_account(&mut svm, entry, registry_program, entry_image.to_vec())?;
    put_account(&mut svm, proof, verifier_program, proof_image)?;

    let page_zero_before = svm
        .get_account(&address(&page_zero))
        .context("page zero missing")?;
    let mut accounts = vec![meta(pool, true), meta(page_zero, mode == Mode::SamePage)];
    if mode == Mode::Rollover {
        accounts.push(meta(page_one, true));
    }
    accounts.extend_from_slice(&[
        meta(marker, true),
        meta(registry, false),
        meta(entry, false),
        meta(verifier_program, false),
        meta(proof, false),
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

    let pool_after_account = svm.get_account(&address(&pool)).context("pool missing after")?;
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

    let target_page = if mode == Mode::SamePage { page_zero } else { page_one };
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
    if mode == Mode::Rollover {
        ensure!(page_zero_after == page_zero_before, "rollover mutated full prior page");
    }

    let evidence = serde_json::json!({
        "schema": "aspis.pool-v1.pair-afterstate-runtime-evidence.v1",
        "mode": mode.label(),
        "profile_slot": PROFILE_SLOT,
        "compute_unit_limit": COMPUTE_UNIT_LIMIT,
        "execution": {
            "compute_units": executed.compute_units_consumed,
            "transaction_bytes": tx_bytes,
            "instruction_bytes": spend.len(),
            "account_metas_excluding_compute_budget_and_payer": if mode == Mode::SamePage { 7 } else { 8 },
            "simulation_equals_execution": true,
            "return_magic": "ASTR",
            "return_bytes": 200
        },
        "state_transition": {
            "membership_anchor_sequence": MEMBERSHIP_ANCHOR_SEQUENCE,
            "source_sequence": mode.source_sequence(),
            "next_sequence": expected_append.root_sequence,
            "history_target_page": target_location.page_number,
            "history_target_slot": target_location.slot,
            "historical_anchor_value_preserved": true,
            "full_prior_page_byte_exact_on_rollover": mode == Mode::Rollover,
            "pool_matches_verifier_afterstate": true,
            "nullifier_marker_created_once": true,
            "pool_side_poseidon_calls": 0
        },
        "transport": {
            "kind": "authenticated selected-verifier CPI transport double",
            "request_is_registry_and_proof_account_bound": true,
            "proof_account_body_bytes": POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
            "returned_asja_bytes": POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
            "immediate_return_program_checked": true,
            "real_tag73_proof_executed": false
        },
        "artifacts": {
            "pool": {
                "path": pool_artifact_path,
                "bytes": pool_artifact.len(),
                "sha256": sha256_hex(&pool_artifact)
            },
            "verifier_transport_double": {
                "path": verifier_artifact_path,
                "bytes": verifier_artifact.len(),
                "sha256": sha256_hex(&verifier_artifact)
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
            "The selected verifier is a transport double: it performs no cryptographic proof verification and returns the framed ASJA bytes from its verifier-owned proof account.",
            "This number is the executable Pool suffix plus selected-verifier CPI/688-byte return transport; it must not be added to a verifier reference as if it were a measured combined real-proof execution.",
            "The pair entrypoint is compiled only with the measurement-only pair-afterstate-evidence feature; the default production entrypoint remains disabled.",
            "Marker and rollover history accounts are exact pre-created Pool-owned zeroed accounts; System creation cost is excluded.",
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
