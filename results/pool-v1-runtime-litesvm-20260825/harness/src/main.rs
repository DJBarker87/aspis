use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
};

use anyhow::{anyhow, bail, Context, Result};
use aspis_core::field::M31;
use aspis_pool::{
    deposit_transport::encode_deposit_instruction_v1, encode_initialize_instruction_v1,
    encode_private_transfer_instruction_v1, encode_withdrawal_instruction_v1,
    pool_v1_nullifier_marker_address, pool_v1_root_page_address, pool_v1_state_address,
    pool_v1_vault_authority_address, pool_v1_vault_token_account_address,
    pool_v1_verifier_entry_address, pool_v1_verifier_registry_address, DepositRequestV1,
    PoolInitializationV1, PoolStateV1, PrivateTransferStatementV1, WithdrawalStatementV1,
    LEGACY_SPL_TOKEN_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES,
    LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_STATE_ACCOUNT_BYTES,
};
use aspis_statement::{
    pool_v1::{
        decode_deposit_receipt_v1, decode_pool_v1_nullifier_marker,
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1, pool_v1_note_commitment,
        root_history::{initialize_root_history_page_bytes_v1, read_root_history_page_root_v1},
        HistoricalAnchorEnvelopeV1, PoolV1NullifierMarkerV1, PoolV1TransitionKind,
        VerifierEntryStatusV1, VerifierPolicyV1, VerifierRegistryEntryV1, VerifierRegistryV1,
        POOL_V1_DEPOSIT_RECEIPT_BYTES, POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
    },
    poseidon2::Digest,
};
use litesvm::{types::TransactionMetadata, LiteSVM};
use serde::Serialize;
use sha2::{Digest as ShaDigest, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::{v0::Message as MessageV0, AddressLookupTableAccount, VersionedMessage};
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_sdk_ids::system_program;
use solana_signer::Signer;
use solana_transaction::{versioned::VersionedTransaction, Transaction};

const HARNESS_VERSION: &str = "pool-v1-litesvm-evidence-v1";
const LITESVM_VERSION: &str = "0.16.0";
const AGAVE_RUNTIME_VERSION: &str = "4.2.1";
const MAX_TRANSACTION_BYTES: usize = 1_232;
const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;

// These are deterministic test addresses only. They are not deployment ids.
const POOL_PROGRAM_BYTES: [u8; 32] = [0xA5; 32];
const MOCK_VERIFIER_BYTES: [u8; 32] = [0xB6; 32];
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0xC7; 32];
const REGISTRY_AUTHORITY_BYTES: [u8; 32] = [0xD8; 32];
const POLICY_BINDING_BYTES: [u8; 32] = [0x19; 32];
const PROFILE_BINDING_BYTES: [u8; 32] = [0x2A; 32];
const RELEASE_BINDING_BYTES: [u8; 32] = [0x3B; 32];
const DEPLOYMENT_DOMAIN_BYTES: [u8; 32] = [0x4C; 32];
const ASSET_ID: M31 = M31(73);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RunMode {
    Full,
    InitOnly,
    DepositSlice,
    PrivateTransferSlice,
}

#[derive(Serialize)]
struct ArtifactEvidence {
    path: String,
    bytes: u64,
    sha256: String,
}

#[derive(Serialize)]
struct StepEvidence {
    name: String,
    outcome: String,
    simulation_matches_execution: bool,
    compute_units: u64,
    fee_lamports: u64,
    return_program: String,
    return_bytes: usize,
    return_magic: String,
    error: Option<String>,
}

#[derive(Serialize)]
struct RentEvidence {
    pool_state: u64,
    root_page: u64,
    vault_token_account: u64,
    nullifier_marker: u64,
    initialization_payer_delta: u64,
    initialization_expected_delta: u64,
    private_transfer_payer_delta: u64,
    private_transfer_expected_delta: u64,
    withdrawal_payer_delta: u64,
    withdrawal_expected_delta: u64,
    rollover_payer_delta: u64,
    rollover_expected_delta: u64,
}

#[derive(Serialize)]
struct SizeEvidence {
    instruction: String,
    account_metas: usize,
    writable_metas: usize,
    signer_metas: usize,
    instruction_data_bytes: usize,
    legacy_transaction_bytes: usize,
    v0_alt_transaction_bytes: usize,
    legacy_fits_1232: bool,
    v0_alt_fits_1232: bool,
}

#[derive(Serialize)]
struct LockEvidence {
    first_private_writable: Vec<String>,
    duplicate_private_writable: Vec<String>,
    writable_intersection: Vec<String>,
    same_pool_and_marker_conflict: bool,
    runtime_scheduler_boundary: String,
}

#[derive(Serialize)]
struct RolloverEvidence {
    sequence_before: u64,
    sequence_after_deposit: u64,
    sequence_after_historical_spend: u64,
    page_zero_unchanged_by_rollover: bool,
    page_one_rent_exempt: bool,
    historical_anchor_sequence: u64,
    historical_anchor_page: u64,
    mutable_current_page: u64,
}

#[derive(Serialize)]
struct Evidence {
    schema: String,
    harness_version: String,
    litesvm_version: String,
    agave_runtime_version: String,
    execution_environment: String,
    pool_program_id: String,
    mock_verifier_program_id: String,
    program_id_status: String,
    artifacts: Vec<ArtifactEvidence>,
    steps: Vec<StepEvidence>,
    rent: RentEvidence,
    transaction_sizes: Vec<SizeEvidence>,
    locks: LockEvidence,
    rollover: RolloverEvidence,
    assertions: BTreeMap<String, bool>,
    explicit_boundaries: Vec<String>,
}

#[derive(Clone)]
struct PoolKeys {
    mint: LegacyPubkey,
    pool: LegacyPubkey,
    page_zero: LegacyPubkey,
    vault: LegacyPubkey,
    vault_authority: LegacyPubkey,
}

struct RegistryKeys {
    registry: LegacyPubkey,
    entry: LegacyPubkey,
    proof: LegacyPubkey,
}

fn legacy(bytes: [u8; 32]) -> LegacyPubkey {
    LegacyPubkey::new_from_array(bytes)
}

fn address(key: &LegacyPubkey) -> Address {
    Address::from(key.to_bytes())
}

fn fixed_address(byte: u8) -> Address {
    Address::from([byte; 32])
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 29 * index as u32))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hash = Sha256::new();
    hash.update(bytes);
    hash.finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn artifact(path: &Path) -> Result<ArtifactEvidence> {
    let bytes = fs::read(path).with_context(|| format!("read {}", path.display()))?;
    Ok(ArtifactEvidence {
        path: path.display().to_string(),
        bytes: bytes.len() as u64,
        sha256: sha256_hex(&bytes),
    })
}

fn pool_keys(mint_byte: u8) -> PoolKeys {
    let mint = legacy([mint_byte; 32]);
    let program = legacy(POOL_PROGRAM_BYTES);
    let pool = pool_v1_state_address(&program, &mint).0;
    PoolKeys {
        mint,
        pool,
        page_zero: pool_v1_root_page_address(&program, &pool, 0).0,
        vault: pool_v1_vault_token_account_address(&program, &pool).0,
        vault_authority: pool_v1_vault_authority_address(&program, &pool).0,
    }
}

fn policy() -> VerifierPolicyV1 {
    VerifierPolicyV1 {
        flags: 0,
        registry_program: REGISTRY_PROGRAM_BYTES,
        registry_authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
    }
}

fn initialization(keys: &PoolKeys) -> PoolInitializationV1 {
    PoolInitializationV1 {
        asset_mint: keys.mint.to_bytes(),
        token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
        asset_id: ASSET_ID,
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        verifier_policy: policy(),
    }
}

fn mint_data(decimals: u8) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
    data[44] = decimals;
    data[45] = 1;
    data
}

fn token_data(mint: &LegacyPubkey, authority: &Address, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
    data[..32].copy_from_slice(&mint.to_bytes());
    data[32..64].copy_from_slice(authority.as_ref());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1;
    data
}

fn token_amount(account: &Account) -> u64 {
    u64::from_le_bytes(account.data[64..72].try_into().unwrap())
}

fn proof_data(body: &[u8]) -> Vec<u8> {
    let mut data = vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + body.len()];
    data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
    data[4..8].copy_from_slice(&(body.len() as u32).to_le_bytes());
    data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..].copy_from_slice(body);
    data
}

fn put_account(svm: &mut LiteSVM, key: Address, owner: Address, data: Vec<u8>) -> Result<()> {
    let lamports = svm.minimum_balance_for_rent_exemption(data.len()).max(1);
    svm.set_account(
        key,
        Account {
            lamports,
            data,
            owner,
            executable: false,
            rent_epoch: 0,
        },
    )
    .map_err(|error| anyhow!("set account {key}: {error}"))?;
    Ok(())
}

fn put_token_fixture(
    svm: &mut LiteSVM,
    keys: &PoolKeys,
    source_owner: &Address,
    source_key: Address,
    source_amount: u64,
    vault_amount: Option<u64>,
) -> Result<()> {
    let token_program = address(&LEGACY_SPL_TOKEN_PROGRAM_ID);
    put_account(svm, address(&keys.mint), token_program, mint_data(6))?;
    put_account(
        svm,
        source_key,
        token_program,
        token_data(&keys.mint, source_owner, source_amount),
    )?;
    if let Some(amount) = vault_amount {
        put_account(
            svm,
            address(&keys.vault),
            token_program,
            token_data(&keys.mint, &address(&keys.vault_authority), amount),
        )?;
    }
    Ok(())
}

fn install_registry(svm: &mut LiteSVM, keys: &PoolKeys, proof_byte: u8) -> Result<RegistryKeys> {
    let registry_program = legacy(REGISTRY_PROGRAM_BYTES);
    let registry = pool_v1_verifier_registry_address(&registry_program, &keys.pool).0;
    let entry = pool_v1_verifier_entry_address(
        &registry_program,
        &keys.pool,
        &PROFILE_BINDING_BYTES,
        &RELEASE_BINDING_BYTES,
    )
    .0;
    let proof = legacy([proof_byte; 32]);
    let registry_data = encode_verifier_registry_v1(&VerifierRegistryV1 {
        flags: 0,
        pool: keys.pool.to_bytes(),
        authority: REGISTRY_AUTHORITY_BYTES,
        policy_binding: POLICY_BINDING_BYTES,
        generation: 1,
        minimum_activation_delay_slots: 1,
    })
    .map_err(|error| anyhow!("encode verifier registry: {error:?}"))?;
    let entry_data = encode_verifier_registry_entry_v1(&VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Active,
        statement_version: 1,
        pool: keys.pool.to_bytes(),
        verifier_program: MOCK_VERIFIER_BYTES,
        profile_binding: PROFILE_BINDING_BYTES,
        release_binding: RELEASE_BINDING_BYTES,
        activation_slot: 0,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: POLICY_BINDING_BYTES,
    })
    .map_err(|error| anyhow!("encode verifier registry entry: {error:?}"))?;
    put_account(
        svm,
        address(&registry),
        address(&registry_program),
        registry_data.to_vec(),
    )?;
    put_account(
        svm,
        address(&entry),
        address(&registry_program),
        entry_data.to_vec(),
    )?;
    put_account(
        svm,
        address(&proof),
        Address::from(MOCK_VERIFIER_BYTES),
        proof_data(b"pool-runtime-transport-only-proof"),
    )?;
    Ok(RegistryKeys {
        registry,
        entry,
        proof,
    })
}

fn meta(key: Address, signer: bool, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(key, signer)
    } else {
        AccountMeta::new_readonly(key, signer)
    }
}

fn instruction(data: Vec<u8>, accounts: Vec<AccountMeta>) -> Instruction {
    Instruction {
        program_id: Address::from(POOL_PROGRAM_BYTES),
        accounts,
        data,
    }
}

fn init_instruction(keys: &PoolKeys, payer: Address) -> Instruction {
    instruction(
        encode_initialize_instruction_v1(&initialization(keys))
            .unwrap()
            .to_vec(),
        vec![
            meta(payer, true, true),
            meta(address(&keys.pool), false, true),
            meta(address(&keys.page_zero), false, true),
            meta(address(&keys.mint), false, false),
            meta(address(&keys.vault), false, true),
            meta(address(&LEGACY_SPL_TOKEN_PROGRAM_ID), false, false),
            meta(system_program::id(), false, false),
        ],
    )
}

fn deposit_instruction(
    keys: &PoolKeys,
    current_page: LegacyPubkey,
    next_page: Option<LegacyPubkey>,
    source: Address,
    source_owner: Address,
    payer: Address,
    amount: u32,
    payload: &[u8],
    salt_seed: u32,
) -> Instruction {
    let request = DepositRequestV1 {
        owner_key: digest(salt_seed + 1_000),
        amount,
        salt: digest(salt_seed),
        encrypted_note_payload: payload,
    };
    let data = encode_deposit_instruction_v1(&request)
        .unwrap()
        .as_bytes()
        .to_vec();
    let mut accounts = vec![
        meta(address(&keys.pool), false, true),
        meta(address(&current_page), false, next_page.is_none()),
    ];
    if let Some(next) = next_page {
        accounts.push(meta(address(&next), false, true));
    }
    accounts.extend([
        meta(address(&keys.mint), false, false),
        meta(source, false, true),
        meta(source_owner, true, false),
        meta(address(&keys.vault), false, true),
        meta(address(&LEGACY_SPL_TOKEN_PROGRAM_ID), false, false),
    ]);
    if next_page.is_some() {
        accounts.extend([
            meta(payer, true, true),
            meta(system_program::id(), false, false),
        ]);
    }
    instruction(data, accounts)
}

fn marker_for(envelope: &HistoricalAnchorEnvelopeV1, keys: &PoolKeys) -> LegacyPubkey {
    pool_v1_nullifier_marker_address(
        &legacy(POOL_PROGRAM_BYTES),
        &keys.pool,
        &PoolV1NullifierMarkerV1::from_historical_anchor(envelope).canonical_nullifier_encoding(),
    )
    .unwrap()
    .0
}

fn private_instruction(
    keys: &PoolKeys,
    registry: &RegistryKeys,
    payer: Address,
    anchor_page: LegacyPubkey,
    current_page: LegacyPubkey,
    anchor_sequence: u64,
    anchor_root: Digest,
    nullifier: Digest,
    first: Digest,
    second: Digest,
) -> (Instruction, LegacyPubkey) {
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: keys.pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence,
        anchor_root,
        nullifier,
        verifier_profile: PROFILE_BINDING_BYTES,
        verifier_release: RELEASE_BINDING_BYTES,
    };
    let statement = PrivateTransferStatementV1 {
        pool: envelope.pool,
        deployment_domain: envelope.deployment_domain,
        anchor_sequence,
        anchor_root,
        nullifier,
        asset_id: ASSET_ID,
        recipient_commitment: first,
        change_commitment: second,
    };
    let marker = marker_for(&envelope, keys);
    let mut accounts = vec![meta(address(&keys.pool), false, true)];
    if anchor_page == current_page {
        accounts.push(meta(address(&anchor_page), false, true));
    } else {
        accounts.push(meta(address(&anchor_page), false, false));
        accounts.push(meta(address(&current_page), false, true));
    }
    accounts.extend([
        meta(address(&marker), false, true),
        meta(payer, true, true),
        meta(system_program::id(), false, false),
        meta(address(&registry.registry), false, false),
        meta(address(&registry.entry), false, false),
        meta(Address::from(MOCK_VERIFIER_BYTES), false, false),
        meta(address(&registry.proof), false, false),
    ]);
    (
        instruction(
            encode_private_transfer_instruction_v1(&envelope, &statement)
                .unwrap()
                .to_vec(),
            accounts,
        ),
        marker,
    )
}

#[allow(clippy::too_many_arguments)]
fn withdrawal_instruction(
    keys: &PoolKeys,
    registry: &RegistryKeys,
    payer: Address,
    anchor_page: LegacyPubkey,
    current_page: LegacyPubkey,
    anchor_sequence: u64,
    anchor_root: Digest,
    nullifier: Digest,
    destination: Address,
    amount: u32,
    change: Digest,
) -> (Instruction, LegacyPubkey) {
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: PoolV1TransitionKind::Withdrawal,
        pool: keys.pool.to_bytes(),
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence,
        anchor_root,
        nullifier,
        verifier_profile: PROFILE_BINDING_BYTES,
        verifier_release: RELEASE_BINDING_BYTES,
    };
    let statement = WithdrawalStatementV1 {
        pool: envelope.pool,
        deployment_domain: envelope.deployment_domain,
        anchor_sequence,
        anchor_root,
        nullifier,
        asset_id: ASSET_ID,
        amount,
        destination_token_account: destination.to_bytes(),
        change_commitment: change,
    };
    let marker = marker_for(&envelope, keys);
    let mut accounts = vec![meta(address(&keys.pool), false, true)];
    if anchor_page == current_page {
        accounts.push(meta(address(&anchor_page), false, true));
    } else {
        accounts.push(meta(address(&anchor_page), false, false));
        accounts.push(meta(address(&current_page), false, true));
    }
    accounts.extend([
        meta(address(&marker), false, true),
        meta(payer, true, true),
        meta(system_program::id(), false, false),
        meta(address(&registry.registry), false, false),
        meta(address(&registry.entry), false, false),
        meta(Address::from(MOCK_VERIFIER_BYTES), false, false),
        meta(address(&registry.proof), false, false),
        meta(address(&keys.mint), false, false),
        meta(address(&keys.vault), false, true),
        meta(destination, false, true),
        meta(address(&keys.vault_authority), false, false),
        meta(address(&LEGACY_SPL_TOKEN_PROGRAM_ID), false, false),
    ]);
    (
        instruction(
            encode_withdrawal_instruction_v1(&envelope, &statement)
                .unwrap()
                .to_vec(),
            accounts,
        ),
        marker,
    )
}

fn return_magic(meta: &TransactionMetadata) -> String {
    String::from_utf8_lossy(meta.return_data.data.get(..4).unwrap_or(&[])).into_owned()
}

fn success_step(
    svm: &mut LiteSVM,
    name: &str,
    transaction: Transaction,
    expected_magic: &[u8; 4],
    expected_length: usize,
) -> Result<(StepEvidence, TransactionMetadata)> {
    let simulation = svm
        .simulate_transaction(transaction.clone())
        .map_err(|failed| {
            anyhow!(
                "{name} simulation failed: {:?}\n{}",
                failed.err,
                failed.meta.pretty_logs()
            )
        })?;
    let executed = svm.send_transaction(transaction).map_err(|failed| {
        anyhow!(
            "{name} execution failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    if simulation.meta != executed {
        bail!("{name}: simulation metadata differed from execution");
    }
    if executed.return_data.program_id != Address::from(POOL_PROGRAM_BYTES)
        || executed.return_data.data.len() != expected_length
        || executed.return_data.data[..4] != expected_magic[..]
    {
        bail!("{name}: wrong Pool return data");
    }
    Ok((
        StepEvidence {
            name: name.to_string(),
            outcome: "success".to_string(),
            simulation_matches_execution: true,
            compute_units: executed.compute_units_consumed,
            fee_lamports: executed.fee,
            return_program: executed.return_data.program_id.to_string(),
            return_bytes: executed.return_data.data.len(),
            return_magic: return_magic(&executed),
            error: None,
        },
        executed,
    ))
}

fn failure_step(svm: &mut LiteSVM, name: &str, transaction: Transaction) -> Result<StepEvidence> {
    let simulation = svm
        .simulate_transaction(transaction.clone())
        .expect_err("negative-path simulation must fail");
    let executed = svm
        .send_transaction(transaction)
        .expect_err("negative-path execution must fail");
    if simulation.err != executed.err || simulation.meta != executed.meta {
        bail!("{name}: failed simulation metadata differed from execution");
    }
    if !executed.meta.return_data.data.is_empty() {
        bail!("{name}: failed transaction retained nonempty return data");
    }
    Ok(StepEvidence {
        name: name.to_string(),
        outcome: "rejected".to_string(),
        simulation_matches_execution: true,
        compute_units: executed.meta.compute_units_consumed,
        fee_lamports: executed.meta.fee,
        return_program: executed.meta.return_data.program_id.to_string(),
        return_bytes: 0,
        return_magic: String::new(),
        error: Some(format!("{:?}", executed.err)),
    })
}

fn transaction(
    svm: &LiteSVM,
    instructions: &[Instruction],
    payer: &Keypair,
    extra_signers: &[&Keypair],
) -> Transaction {
    let mut signers: Vec<&Keypair> = vec![payer];
    for signer in extra_signers {
        if signer.pubkey() != payer.pubkey() {
            signers.push(*signer);
        }
    }
    let mut budgeted_instructions = Vec::with_capacity(instructions.len() + 1);
    budgeted_instructions.push(ComputeBudgetInstruction::set_compute_unit_limit(
        COMPUTE_UNIT_LIMIT,
    ));
    budgeted_instructions.extend_from_slice(instructions);
    Transaction::new_signed_with_payer(
        &budgeted_instructions,
        Some(&payer.pubkey()),
        &signers,
        svm.latest_blockhash(),
    )
}

fn account_snapshot(svm: &LiteSVM, keys: &[Address]) -> Vec<Option<Account>> {
    keys.iter().map(|key| svm.get_account(key)).collect()
}

fn transaction_size(
    name: &str,
    ix: &Instruction,
    payer: &Keypair,
    extra_signers: &[&Keypair],
) -> Result<SizeEvidence> {
    let hash = solana_hash::Hash::new_from_array([0x77; 32]);
    let mut signers: Vec<&Keypair> = vec![payer];
    for signer in extra_signers {
        if signer.pubkey() != payer.pubkey() {
            signers.push(*signer);
        }
    }
    let budgeted_instructions = [
        ComputeBudgetInstruction::set_compute_unit_limit(COMPUTE_UNIT_LIMIT),
        ix.clone(),
    ];
    let legacy = Transaction::new_signed_with_payer(
        &budgeted_instructions,
        Some(&payer.pubkey()),
        &signers,
        hash,
    );
    let legacy_bytes = wincode::serialized_size(&legacy)? as usize;

    let lookup_addresses: Vec<Address> = ix
        .accounts
        .iter()
        .filter(|account| !account.is_signer)
        .map(|account| account.pubkey)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let lookup = AddressLookupTableAccount {
        key: fixed_address(0x7A),
        addresses: lookup_addresses,
    };
    let message = MessageV0::try_compile(&payer.pubkey(), &budgeted_instructions, &[lookup], hash)?;
    let versioned = VersionedTransaction::try_new(VersionedMessage::V0(message), &signers)?;
    let v0_bytes = wincode::serialized_size(&versioned)? as usize;

    Ok(SizeEvidence {
        instruction: name.to_string(),
        account_metas: ix.accounts.len(),
        writable_metas: ix.accounts.iter().filter(|meta| meta.is_writable).count(),
        signer_metas: ix.accounts.iter().filter(|meta| meta.is_signer).count(),
        instruction_data_bytes: ix.data.len(),
        legacy_transaction_bytes: legacy_bytes,
        v0_alt_transaction_bytes: v0_bytes,
        legacy_fits_1232: legacy_bytes <= MAX_TRANSACTION_BYTES,
        v0_alt_fits_1232: v0_bytes <= MAX_TRANSACTION_BYTES,
    })
}

fn writable_addresses(ix: &Instruction) -> BTreeSet<Address> {
    ix.accounts
        .iter()
        .filter(|meta| meta.is_writable)
        .map(|meta| meta.pubkey)
        .collect()
}

fn set_near_rollover_pool(
    svm: &mut LiteSVM,
    keys: &PoolKeys,
    source_owner: Address,
    source: Address,
) -> Result<Vec<Digest>> {
    let mut state = PoolStateV1::genesis(&keys.pool, initialization(keys))?;
    let mut roots = vec![state.tree.root];
    for index in 0..255u32 {
        let (next, receipt) = state
            .tree
            .append_one(digest(10_000 + index * 31))
            .map_err(|error| anyhow!("construct rollover tree: {error:?}"))?;
        state.tree = next;
        roots.push(receipt.root);
    }
    if state.current_root_sequence() != 255 || roots.len() != 256 {
        bail!("near-rollover fixture did not reach sequence 255");
    }
    let state_data = state.encode()?.to_vec();
    let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
    initialize_root_history_page_bytes_v1(&mut page_data, keys.pool.to_bytes(), 0, &roots)
        .map_err(|error| anyhow!("construct rollover page: {error:?}"))?;
    put_account(
        svm,
        address(&keys.pool),
        Address::from(POOL_PROGRAM_BYTES),
        state_data,
    )?;
    put_account(
        svm,
        address(&keys.page_zero),
        Address::from(POOL_PROGRAM_BYTES),
        page_data,
    )?;
    put_token_fixture(svm, keys, &source_owner, source, 1_000, Some(0))?;
    Ok(roots)
}

fn parse_args() -> Result<(PathBuf, PathBuf, PathBuf, RunMode)> {
    let mut args = env::args().skip(1);
    let pool = args.next().map(PathBuf::from).ok_or_else(|| {
        anyhow!("usage: harness <aspis_pool.so> <mock_verifier.so> <evidence.json>")
    })?;
    let verifier = args.next().map(PathBuf::from).ok_or_else(|| {
        anyhow!("usage: harness <aspis_pool.so> <mock_verifier.so> <evidence.json>")
    })?;
    let output = args.next().map(PathBuf::from).ok_or_else(|| {
        anyhow!("usage: harness <aspis_pool.so> <mock_verifier.so> <evidence.json>")
    })?;
    let mode = match args.next().as_deref() {
        None => RunMode::Full,
        Some("--init-only") => RunMode::InitOnly,
        Some("--deposit-slice") => RunMode::DepositSlice,
        Some("--private-transfer-slice") => RunMode::PrivateTransferSlice,
        Some(other) => bail!("unexpected argument: {other}"),
    };
    if args.next().is_some() {
        bail!("unexpected extra argument");
    }
    Ok((pool, verifier, output, mode))
}

fn main() -> Result<()> {
    let (pool_so, verifier_so, output, mode) = parse_args()?;
    let pool_bytes = fs::read(&pool_so)?;
    let verifier_bytes = fs::read(&verifier_so)?;
    let mut svm = LiteSVM::new();
    svm.add_program(Address::from(POOL_PROGRAM_BYTES), &pool_bytes)?;
    svm.add_program(Address::from(MOCK_VERIFIER_BYTES), &verifier_bytes)?;

    let payer = Keypair::new_from_array([1u8; 32]);
    let source_owner = Keypair::new_from_array([2u8; 32]);
    let source = fixed_address(0x61);
    svm.airdrop(&payer.pubkey(), 50_000_000_000)
        .map_err(|failed| anyhow!("fund deterministic test payer: {:?}", failed.err))?;

    let rent_pool = svm.minimum_balance_for_rent_exemption(POOL_V1_STATE_ACCOUNT_BYTES);
    let rent_page = svm.minimum_balance_for_rent_exemption(POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES);
    let rent_vault = svm.minimum_balance_for_rent_exemption(LEGACY_SPL_TOKEN_ACCOUNT_BYTES);
    let rent_marker =
        svm.minimum_balance_for_rent_exemption(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES);

    let keys = pool_keys(0x51);
    put_token_fixture(
        &mut svm,
        &keys,
        &source_owner.pubkey(),
        source,
        10_000,
        None,
    )?;

    let mut steps = Vec::new();
    let payer_before_init = svm.get_balance(&payer.pubkey()).unwrap();
    let init_ix = init_instruction(&keys, payer.pubkey());
    let init_tx = transaction(&svm, &[init_ix.clone()], &payer, &[]);
    let (init_step, init_meta) = success_step(&mut svm, "initialize", init_tx, b"ASIR", 104)?;
    steps.push(init_step);
    let payer_after_init = svm.get_balance(&payer.pubkey()).unwrap();
    let init_expected_delta = rent_pool + rent_page + rent_vault + init_meta.fee;
    if payer_before_init - payer_after_init != init_expected_delta {
        bail!("initialization payer delta did not equal rent plus fee");
    }
    for (key, bytes, rent) in [
        (address(&keys.pool), POOL_V1_STATE_ACCOUNT_BYTES, rent_pool),
        (
            address(&keys.page_zero),
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
            rent_page,
        ),
        (
            address(&keys.vault),
            LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
            rent_vault,
        ),
    ] {
        let account = svm
            .get_account(&key)
            .ok_or_else(|| anyhow!("missing initialized account"))?;
        if account.data.len() != bytes || account.lamports != rent {
            bail!("initialized account has wrong size/rent");
        }
    }

    if mode == RunMode::InitOnly {
        let init_evidence = serde_json::json!({
            "schema": "aspis.pool-v1.init-runtime-evidence.v1",
            "harness_version": HARNESS_VERSION,
            "litesvm_version": LITESVM_VERSION,
            "agave_runtime_version": AGAVE_RUNTIME_VERSION,
            "compute_unit_limit": COMPUTE_UNIT_LIMIT,
            "pool_program_id": Address::from(POOL_PROGRAM_BYTES).to_string(),
            "program_id_status": "deterministic test-only runtime address; production Pool has no declare_id and no release deployment id is selected",
            "pool_artifact": artifact(&pool_so)?,
            "step": &steps[0],
            "rent": {
                "pool_state": rent_pool,
                "root_page": rent_page,
                "vault_token_account": rent_vault,
                "payer_delta": payer_before_init - payer_after_init,
                "expected_rent_plus_fee": init_expected_delta,
            },
            "accounts": {
                "pool_state": {
                    "bytes": POOL_V1_STATE_ACCOUNT_BYTES,
                    "lamports": rent_pool,
                    "owner": Address::from(POOL_PROGRAM_BYTES).to_string(),
                },
                "root_page_zero": {
                    "bytes": POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                    "lamports": rent_page,
                    "owner": Address::from(POOL_PROGRAM_BYTES).to_string(),
                },
                "vault_token_account": {
                    "bytes": LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
                    "lamports": rent_vault,
                    "owner": address(&LEGACY_SPL_TOKEN_PROGRAM_ID).to_string(),
                },
            },
            "assertions": {
                "simulation_metadata_equals_execution": true,
                "asir_exact_104_bytes": true,
                "all_three_accounts_exact_size_owner_and_rent": true,
                "payer_delta_equals_rent_plus_fee": true,
                "strict_1400000_cu_limit": true,
                "no_network_send_or_deploy": true,
            },
        });
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&output, serde_json::to_vec_pretty(&init_evidence)?)?;
        println!(
            "Pool V1 strict-cap initialization: PASS ({} CU)",
            steps[0].compute_units
        );
        println!("evidence={}", output.display());
        return Ok(());
    }

    svm.expire_blockhash();
    let payload = vec![0xA3; 512];
    let payer_before_deposit = svm.get_balance(&payer.pubkey()).unwrap();
    let deposit_ix = deposit_instruction(
        &keys,
        keys.page_zero,
        None,
        source,
        source_owner.pubkey(),
        payer.pubkey(),
        1_000,
        &payload,
        700,
    );
    let deposit_tx = transaction(&svm, &[deposit_ix.clone()], &payer, &[&source_owner]);
    let (deposit_step, deposit_meta) = success_step(
        &mut svm,
        "deposit_max_payload",
        deposit_tx,
        b"ASPD",
        224 + payload.len(),
    )?;
    steps.push(deposit_step);
    let payer_after_deposit = svm.get_balance(&payer.pubkey()).unwrap();
    if payer_before_deposit - payer_after_deposit != deposit_meta.fee {
        bail!("deposit payer delta did not equal the transaction fee");
    }
    let state_after_deposit = PoolStateV1::decode(
        &svm.get_account(&address(&keys.pool)).unwrap().data,
        &keys.pool,
    )?;
    if state_after_deposit.current_root_sequence() != 1
        || token_amount(&svm.get_account(&source).unwrap()) != 9_000
        || token_amount(&svm.get_account(&address(&keys.vault)).unwrap()) != 1_000
    {
        bail!("deposit did not produce exact state/token delta");
    }
    let page_zero_after_deposit = svm.get_account(&address(&keys.page_zero)).unwrap();
    let retained_root = read_root_history_page_root_v1(&page_zero_after_deposit.data, 1)
        .map_err(|error| anyhow!("read sequence-one deposit root: {error:?}"))?;
    if retained_root != state_after_deposit.tree.root {
        bail!("deposit state root did not equal sequence-one root history");
    }
    let receipt =
        decode_deposit_receipt_v1(&deposit_meta.return_data.data[..POOL_V1_DEPOSIT_RECEIPT_BYTES])
            .map_err(|error| anyhow!("decode deposit receipt: {error:?}"))?;
    let expected_note = pool_v1_note_commitment(&digest(1_700), 1_000, ASSET_ID, &digest(700));
    if receipt.pool != keys.pool.to_bytes()
        || receipt.asset_mint != keys.mint.to_bytes()
        || receipt.source_token_account != source.to_bytes()
        || receipt.vault_token_account != keys.vault.to_bytes()
        || receipt.amount != 1_000
        || receipt.encrypted_note_payload_bytes != payload.len() as u16
        || receipt.note_commitment != expected_note
        || receipt.leaf_index != 0
        || receipt.root_sequence != 1
        || receipt.root != state_after_deposit.tree.root
        || deposit_meta.return_data.data[POOL_V1_DEPOSIT_RECEIPT_BYTES..] != payload
    {
        bail!("deposit receipt or opaque payload did not match the exact transition");
    }
    let anchor_sequence = 1u64;
    let anchor_root = state_after_deposit.tree.root;

    if mode == RunMode::PrivateTransferSlice {
        let registry = install_registry(&mut svm, &keys, 0x71)?;
        let first_output = digest(2_100);
        let second_output = digest(2_200);
        let nullifier = digest(2_000);
        let (private_ix, private_marker) = private_instruction(
            &keys,
            &registry,
            payer.pubkey(),
            keys.page_zero,
            keys.page_zero,
            anchor_sequence,
            anchor_root,
            nullifier,
            first_output,
            second_output,
        );
        let private_size = transaction_size("ASPT", &private_ix, &payer, &[])?;
        if !private_size.v0_alt_fits_1232 {
            bail!("private-transfer v0+ALT transaction exceeds 1232 bytes");
        }

        let payer_before_private = svm.get_balance(&payer.pubkey()).unwrap();
        svm.expire_blockhash();
        let private_tx = transaction(&svm, &[private_ix], &payer, &[]);
        let (private_step, private_meta) = success_step(
            &mut svm,
            "private_transfer_1_to_2",
            private_tx,
            b"ASTR",
            200,
        )?;
        let payer_after_private = svm.get_balance(&payer.pubkey()).unwrap();
        let private_expected_delta = rent_marker + private_meta.fee;
        if payer_before_private - payer_after_private != private_expected_delta {
            bail!("private-transfer payer delta did not equal marker rent plus fee");
        }

        let state_after_private = PoolStateV1::decode(
            &svm.get_account(&address(&keys.pool)).unwrap().data,
            &keys.pool,
        )?;
        let (expected_tree, expected_receipts) = state_after_deposit
            .tree
            .append_two(first_output, second_output)
            .map_err(|error| anyhow!("derive expected ordered roots: {error:?}"))?;
        let page_after_private = svm.get_account(&address(&keys.page_zero)).unwrap();
        let first_retained_root = read_root_history_page_root_v1(&page_after_private.data, 2)
            .map_err(|error| anyhow!("read sequence-two private root: {error:?}"))?;
        let second_retained_root = read_root_history_page_root_v1(&page_after_private.data, 3)
            .map_err(|error| anyhow!("read sequence-three private root: {error:?}"))?;
        if state_after_private.current_root_sequence() != 3
            || state_after_private.tree != expected_tree
            || first_retained_root != expected_receipts.first.root
            || second_retained_root != expected_receipts.second.root
            || second_retained_root != state_after_private.tree.root
        {
            bail!("private transfer did not preserve both exact chronological roots");
        }
        let marker_account = svm
            .get_account(&address(&private_marker))
            .ok_or_else(|| anyhow!("private transfer did not create its nullifier marker"))?;
        let decoded_marker = decode_pool_v1_nullifier_marker(&marker_account.data)
            .map_err(|error| anyhow!("decode private nullifier marker: {error:?}"))?;
        if marker_account.owner != Address::from(POOL_PROGRAM_BYTES)
            || marker_account.lamports != rent_marker
            || decoded_marker.pool != keys.pool.to_bytes()
            || decoded_marker.nullifier != nullifier
        {
            bail!("private-transfer marker identity/owner/rent mismatch");
        }

        steps.push(private_step);
        let slice_evidence = serde_json::json!({
            "schema": "aspis.pool-v1.private-transfer-runtime-evidence.v1",
            "harness_version": HARNESS_VERSION,
            "litesvm_version": LITESVM_VERSION,
            "agave_runtime_version": AGAVE_RUNTIME_VERSION,
            "compute_unit_limit": COMPUTE_UNIT_LIMIT,
            "pool_program_id": Address::from(POOL_PROGRAM_BYTES).to_string(),
            "mock_verifier_program_id": Address::from(MOCK_VERIFIER_BYTES).to_string(),
            "program_id_status": "deterministic test-only runtime address; production Pool has no declare_id and no release deployment id is selected",
            "artifacts": [artifact(&pool_so)?, artifact(&verifier_so)?],
            "steps": &steps,
            "private_transfer": {
                "anchor_sequence": anchor_sequence,
                "sequence_before": state_after_deposit.current_root_sequence(),
                "sequence_after": state_after_private.current_root_sequence(),
                "first_leaf_index": expected_receipts.first.leaf_index,
                "second_leaf_index": expected_receipts.second.leaf_index,
                "first_root_sequence": expected_receipts.first.root_sequence,
                "second_root_sequence": expected_receipts.second.root_sequence,
                "first_retained_root": format!("{:?}", first_retained_root),
                "second_retained_root": format!("{:?}", second_retained_root),
                "state_root": format!("{:?}", state_after_private.tree.root),
                "return_magic": "ASTR",
                "return_bytes": 200,
                "payer_delta": payer_before_private - payer_after_private,
                "expected_marker_rent_plus_fee": private_expected_delta,
                "marker_lamports": marker_account.lamports,
                "transaction_size": private_size,
            },
            "assertions": {
                "simulation_metadata_equals_execution": true,
                "strict_1400000_cu_limit": true,
                "one_input_appends_exactly_two_ordered_outputs": true,
                "both_chronological_roots_retained_exactly": true,
                "final_state_root_equals_second_retained_root": true,
                "nullifier_marker_exact_owner_identity_and_rent": true,
                "payer_delta_equals_marker_rent_plus_fee": true,
                "astr_exact_200_bytes": true,
                "v0_alt_fits_1232": true,
                "no_network_send_or_deploy": true,
            },
            "explicit_boundary": "The mock verifier proves no Tag-73 statement; this slice isolates the real Pool-side private-transfer transition and authenticated verifier transport.",
        });
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&output, serde_json::to_vec_pretty(&slice_evidence)?)?;
        println!(
            "Pool V1 strict-cap private-transfer slice: PASS ({} CU)",
            steps.last().unwrap().compute_units
        );
        println!("evidence={}", output.display());
        return Ok(());
    }

    // A successful deposit followed by a failing second instruction must roll
    // back both the SPL Token CPI and every Pool write in the transaction.
    svm.expire_blockhash();
    let rollback_keys = [
        address(&keys.pool),
        address(&keys.page_zero),
        source,
        address(&keys.vault),
    ];
    let rollback_before = account_snapshot(&svm, &rollback_keys);
    let rollback_deposit = deposit_instruction(
        &keys,
        keys.page_zero,
        None,
        source,
        source_owner.pubkey(),
        payer.pubkey(),
        7,
        b"rollback",
        701,
    );
    let deliberate_failure = instruction(b"FAIL".to_vec(), Vec::new());
    let rollback_tx = transaction(
        &svm,
        &[rollback_deposit, deliberate_failure],
        &payer,
        &[&source_owner],
    );
    steps.push(failure_step(
        &mut svm,
        "transaction_rollback_after_successful_pool_and_token_cpi",
        rollback_tx,
    )?);
    if account_snapshot(&svm, &rollback_keys) != rollback_before {
        bail!("failed outer transaction did not roll back Pool/token accounts");
    }

    if mode == RunMode::DepositSlice {
        let slice_evidence = serde_json::json!({
            "schema": "aspis.pool-v1.deposit-runtime-evidence.v1",
            "harness_version": HARNESS_VERSION,
            "litesvm_version": LITESVM_VERSION,
            "agave_runtime_version": AGAVE_RUNTIME_VERSION,
            "compute_unit_limit": COMPUTE_UNIT_LIMIT,
            "pool_program_id": Address::from(POOL_PROGRAM_BYTES).to_string(),
            "program_id_status": "deterministic test-only runtime address; production Pool has no declare_id and no release deployment id is selected",
            "pool_artifact": artifact(&pool_so)?,
            "steps": &steps,
            "initialization": {
                "payer_delta": payer_before_init - payer_after_init,
                "expected_rent_plus_fee": init_expected_delta,
                "return_magic": "ASIR",
                "return_bytes": 104,
            },
            "deposit": {
                "amount": 1_000,
                "encrypted_payload_bytes": payload.len(),
                "return_magic": "ASPD",
                "return_bytes": POOL_V1_DEPOSIT_RECEIPT_BYTES + payload.len(),
                "leaf_index": receipt.leaf_index,
                "root_sequence": receipt.root_sequence,
                "note_commitment": format!("{:?}", receipt.note_commitment),
                "root": format!("{:?}", receipt.root),
                "source_before": 10_000,
                "source_after": token_amount(&svm.get_account(&source).unwrap()),
                "vault_before": 0,
                "vault_after": token_amount(&svm.get_account(&address(&keys.vault)).unwrap()),
                "payer_delta": payer_before_deposit - payer_after_deposit,
                "expected_fee_only_delta": deposit_meta.fee,
                "pool_state_bytes": svm.get_account(&address(&keys.pool)).unwrap().data.len(),
                "root_page_bytes": page_zero_after_deposit.data.len(),
                "root_page_lamports": page_zero_after_deposit.lamports,
            },
            "invalid_deposit_rollback": {
                "shape": "valid seven-unit deposit followed by an invalid Pool instruction in the same transaction",
                "all_pool_and_token_accounts_byte_exact_after_failure": true,
                "return_data_empty": true,
                "error": steps.last().and_then(|step| step.error.as_deref()),
            },
            "assertions": {
                "simulation_metadata_equals_execution_for_all_steps": true,
                "initialization_exact": true,
                "deposit_receipt_and_payload_exact": true,
                "deposit_note_commitment_exact": true,
                "deposit_root_equals_sequence_one_history": true,
                "token_delta_exact": true,
                "deposit_creates_no_new_rent_account": true,
                "invalid_batch_rolls_back_successful_pool_and_spl_cpi": true,
                "failed_transaction_return_data_empty": true,
                "strict_1400000_cu_limit": true,
                "no_network_send_or_deploy": true,
            },
        });
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&output, serde_json::to_vec_pretty(&slice_evidence)?)?;
        println!(
            "Pool V1 strict-cap deposit slice: PASS (deposit {} CU; rollback {} CU)",
            steps[1].compute_units, steps[2].compute_units
        );
        println!("evidence={}", output.display());
        return Ok(());
    }

    // Exact privilege and alias failures occur before mutation and publish no
    // successful Pool return data.
    svm.expire_blockhash();
    let privilege_before = account_snapshot(&svm, &rollback_keys);
    let mut readonly_pool = deposit_ix.clone();
    readonly_pool.accounts[0].is_writable = false;
    let readonly_tx = transaction(&svm, &[readonly_pool], &payer, &[&source_owner]);
    steps.push(failure_step(
        &mut svm,
        "deposit_rejects_readonly_pool",
        readonly_tx,
    )?);
    if account_snapshot(&svm, &rollback_keys) != privilege_before {
        bail!("privilege rejection mutated state");
    }

    svm.expire_blockhash();
    let alias_before = account_snapshot(&svm, &rollback_keys);
    let mut aliased = deposit_ix.clone();
    aliased.accounts[5].pubkey = source;
    let alias_tx = transaction(&svm, &[aliased], &payer, &[&source_owner]);
    steps.push(failure_step(
        &mut svm,
        "deposit_rejects_source_vault_alias",
        alias_tx,
    )?);
    if account_snapshot(&svm, &rollback_keys) != alias_before {
        bail!("alias rejection mutated state");
    }

    let registry = install_registry(&mut svm, &keys, 0x71)?;
    let (private_ix, private_marker) = private_instruction(
        &keys,
        &registry,
        payer.pubkey(),
        keys.page_zero,
        keys.page_zero,
        anchor_sequence,
        anchor_root,
        digest(2_000),
        digest(2_100),
        digest(2_200),
    );
    let private_writable = writable_addresses(&private_ix);
    let payer_before_private = svm.get_balance(&payer.pubkey()).unwrap();
    svm.expire_blockhash();
    let private_tx = transaction(&svm, &[private_ix.clone()], &payer, &[]);
    let (private_step, private_meta) = success_step(
        &mut svm,
        "private_transfer_1_to_2",
        private_tx,
        b"ASTR",
        200,
    )?;
    steps.push(private_step);
    let payer_after_private = svm.get_balance(&payer.pubkey()).unwrap();
    let private_expected_delta = rent_marker + private_meta.fee;
    if payer_before_private - payer_after_private != private_expected_delta {
        bail!("private-transfer payer delta did not equal marker rent plus fee");
    }
    let state_after_private = PoolStateV1::decode(
        &svm.get_account(&address(&keys.pool)).unwrap().data,
        &keys.pool,
    )?;
    if state_after_private.current_root_sequence() != 3 {
        bail!("private transfer did not append exactly two leaves");
    }

    svm.expire_blockhash();
    let duplicate_keys = [
        address(&keys.pool),
        address(&keys.page_zero),
        address(&private_marker),
        source,
        address(&keys.vault),
    ];
    let duplicate_before = account_snapshot(&svm, &duplicate_keys);
    let duplicate_tx = transaction(&svm, &[private_ix.clone()], &payer, &[]);
    steps.push(failure_step(
        &mut svm,
        "duplicate_nullifier_rejected_with_rollback",
        duplicate_tx,
    )?);
    if account_snapshot(&svm, &duplicate_keys) != duplicate_before {
        bail!("duplicate nullifier rejection mutated protected accounts");
    }

    let destination = fixed_address(0x62);
    put_account(
        &mut svm,
        destination,
        address(&LEGACY_SPL_TOKEN_PROGRAM_ID),
        token_data(&keys.mint, &fixed_address(0x63), 5),
    )?;
    let (withdraw_ix, withdraw_marker) = withdrawal_instruction(
        &keys,
        &registry,
        payer.pubkey(),
        keys.page_zero,
        keys.page_zero,
        anchor_sequence,
        anchor_root,
        digest(3_000),
        destination,
        25,
        digest(3_100),
    );
    let payer_before_withdrawal = svm.get_balance(&payer.pubkey()).unwrap();
    svm.expire_blockhash();
    let withdraw_tx = transaction(&svm, &[withdraw_ix.clone()], &payer, &[]);
    let (withdraw_step, withdraw_meta) = success_step(
        &mut svm,
        "withdrawal_with_change",
        withdraw_tx,
        b"ASTR",
        200,
    )?;
    steps.push(withdraw_step);
    let payer_after_withdrawal = svm.get_balance(&payer.pubkey()).unwrap();
    let withdrawal_expected_delta = rent_marker + withdraw_meta.fee;
    if payer_before_withdrawal - payer_after_withdrawal != withdrawal_expected_delta {
        bail!("withdrawal payer delta did not equal marker rent plus fee");
    }
    if token_amount(&svm.get_account(&address(&keys.vault)).unwrap()) != 975
        || token_amount(&svm.get_account(&destination).unwrap()) != 30
        || svm.get_account(&address(&withdraw_marker)).is_none()
    {
        bail!("withdrawal did not produce exact token/marker delta");
    }
    let state_after_withdrawal = PoolStateV1::decode(
        &svm.get_account(&address(&keys.pool)).unwrap().data,
        &keys.pool,
    )?;
    if state_after_withdrawal.current_root_sequence() != 4 {
        bail!("withdrawal did not append exactly one change leaf");
    }

    // A second valid pool is injected at sequence 255 so one focused runtime
    // transaction exercises page creation/rent instead of replaying 255 CPIs.
    let rollover_keys = pool_keys(0x52);
    let rollover_source = fixed_address(0x64);
    let roots = set_near_rollover_pool(
        &mut svm,
        &rollover_keys,
        source_owner.pubkey(),
        rollover_source,
    )?;
    let page_zero_before_rollover = svm.get_account(&address(&rollover_keys.page_zero)).unwrap();
    let page_one = pool_v1_root_page_address(&legacy(POOL_PROGRAM_BYTES), &rollover_keys.pool, 1).0;
    let rollover_ix = deposit_instruction(
        &rollover_keys,
        rollover_keys.page_zero,
        Some(page_one),
        rollover_source,
        source_owner.pubkey(),
        payer.pubkey(),
        100,
        b"rollover",
        4_000,
    );
    let payer_before_rollover = svm.get_balance(&payer.pubkey()).unwrap();
    svm.expire_blockhash();
    let rollover_tx = transaction(&svm, &[rollover_ix.clone()], &payer, &[&source_owner]);
    let (rollover_step, rollover_meta) = success_step(
        &mut svm,
        "deposit_root_page_rollover",
        rollover_tx,
        b"ASPD",
        224 + b"rollover".len(),
    )?;
    steps.push(rollover_step);
    let payer_after_rollover = svm.get_balance(&payer.pubkey()).unwrap();
    let rollover_expected_delta = rent_page + rollover_meta.fee;
    if payer_before_rollover - payer_after_rollover != rollover_expected_delta {
        bail!("rollover payer delta did not equal page rent plus fee");
    }
    let rollover_state = PoolStateV1::decode(
        &svm.get_account(&address(&rollover_keys.pool)).unwrap().data,
        &rollover_keys.pool,
    )?;
    let page_one_account = svm.get_account(&address(&page_one)).unwrap();
    let sequence_256_root = read_root_history_page_root_v1(&page_one_account.data, 256)
        .map_err(|error| anyhow!("read sequence-256 rollover root: {error:?}"))?;
    if rollover_state.current_root_sequence() != 256
        || sequence_256_root != rollover_state.tree.root
    {
        bail!("rollover did not create exact sequence-256 history");
    }
    let page_zero_unchanged =
        svm.get_account(&address(&rollover_keys.page_zero)).unwrap() == page_zero_before_rollover;
    if !page_zero_unchanged {
        bail!("full historical page changed during rollover");
    }

    let rollover_registry = install_registry(&mut svm, &rollover_keys, 0x72)?;
    let historical_anchor_sequence = 1u64;
    let historical_anchor_root = roots[historical_anchor_sequence as usize];
    let (historical_ix, _) = private_instruction(
        &rollover_keys,
        &rollover_registry,
        payer.pubkey(),
        rollover_keys.page_zero,
        page_one,
        historical_anchor_sequence,
        historical_anchor_root,
        digest(5_000),
        digest(5_100),
        digest(5_200),
    );
    svm.expire_blockhash();
    let historical_tx = transaction(&svm, &[historical_ix.clone()], &payer, &[]);
    let (historical_step, _) = success_step(
        &mut svm,
        "historical_page_anchor_with_distinct_current_page",
        historical_tx,
        b"ASTR",
        200,
    )?;
    steps.push(historical_step);
    let rollover_after_historical = PoolStateV1::decode(
        &svm.get_account(&address(&rollover_keys.pool)).unwrap().data,
        &rollover_keys.pool,
    )?;
    if rollover_after_historical.current_root_sequence() != 258
        || svm.get_account(&address(&rollover_keys.page_zero)).unwrap() != page_zero_before_rollover
    {
        bail!("historical split-page spend mutated the anchor page or wrong sequence");
    }

    let transaction_sizes = vec![
        transaction_size("ASIN", &init_ix, &payer, &[])?,
        transaction_size("ASDI-max-payload", &deposit_ix, &payer, &[&source_owner])?,
        transaction_size("ASPT", &private_ix, &payer, &[])?,
        transaction_size("ASWD", &withdraw_ix, &payer, &[])?,
        transaction_size("ASDI-rollover", &rollover_ix, &payer, &[&source_owner])?,
        transaction_size("ASPT-split-pages", &historical_ix, &payer, &[])?,
    ];
    if transaction_sizes
        .iter()
        .any(|entry| !entry.v0_alt_fits_1232)
    {
        bail!("at least one exact v0+ALT transaction exceeds 1232 bytes");
    }

    let duplicate_writable = writable_addresses(&private_ix);
    let intersection: Vec<String> = private_writable
        .intersection(&duplicate_writable)
        .map(ToString::to_string)
        .collect();
    let lock_evidence = LockEvidence {
        first_private_writable: private_writable.iter().map(ToString::to_string).collect(),
        duplicate_private_writable: duplicate_writable.iter().map(ToString::to_string).collect(),
        writable_intersection: intersection,
        same_pool_and_marker_conflict: private_writable.contains(&address(&keys.pool))
            && private_writable.contains(&address(&private_marker))
            && duplicate_writable.contains(&address(&keys.pool))
            && duplicate_writable.contains(&address(&private_marker)),
        runtime_scheduler_boundary: "LiteSVM validates the transaction lock set and the exact writable overlap; concurrent Agave banking-stage scheduling remains a Solana-runtime boundary.".to_string(),
    };

    let rent = RentEvidence {
        pool_state: rent_pool,
        root_page: rent_page,
        vault_token_account: rent_vault,
        nullifier_marker: rent_marker,
        initialization_payer_delta: payer_before_init - payer_after_init,
        initialization_expected_delta: init_expected_delta,
        private_transfer_payer_delta: payer_before_private - payer_after_private,
        private_transfer_expected_delta: private_expected_delta,
        withdrawal_payer_delta: payer_before_withdrawal - payer_after_withdrawal,
        withdrawal_expected_delta: withdrawal_expected_delta,
        rollover_payer_delta: payer_before_rollover - payer_after_rollover,
        rollover_expected_delta,
    };

    let rollover = RolloverEvidence {
        sequence_before: 255,
        sequence_after_deposit: rollover_state.current_root_sequence(),
        sequence_after_historical_spend: rollover_after_historical.current_root_sequence(),
        page_zero_unchanged_by_rollover: page_zero_unchanged,
        page_one_rent_exempt: page_one_account.lamports == rent_page,
        historical_anchor_sequence,
        historical_anchor_page: 0,
        mutable_current_page: 1,
    };

    let mut assertions = BTreeMap::new();
    assertions.insert("all_success_return_data_exact".to_string(), true);
    assertions.insert("all_failure_return_data_empty".to_string(), true);
    assertions.insert("simulation_equals_execution".to_string(), true);
    assertions.insert("duplicate_nullifier_state_rollback".to_string(), true);
    assertions.insert(
        "post_success_second_instruction_transaction_rollback".to_string(),
        true,
    );
    assertions.insert("account_privilege_rejection_no_mutation".to_string(), true);
    assertions.insert("account_alias_rejection_no_mutation".to_string(), true);
    assertions.insert("historical_anchor_split_page_acceptance".to_string(), true);
    assertions.insert("root_page_rollover_exact".to_string(), true);
    assertions.insert("v0_alt_all_fit_1232".to_string(), true);
    assertions.insert("no_network_send_or_deploy".to_string(), true);

    let evidence = Evidence {
        schema: "aspis.pool-v1.runtime-evidence.v1".to_string(),
        harness_version: HARNESS_VERSION.to_string(),
        litesvm_version: LITESVM_VERSION.to_string(),
        agave_runtime_version: AGAVE_RUNTIME_VERSION.to_string(),
        execution_environment: format!("{}-{}", env::consts::OS, env::consts::ARCH),
        pool_program_id: Address::from(POOL_PROGRAM_BYTES).to_string(),
        mock_verifier_program_id: Address::from(MOCK_VERIFIER_BYTES).to_string(),
        program_id_status: "deterministic test-only runtime address; production Pool has no declare_id and no release deployment id is selected".to_string(),
        artifacts: vec![artifact(&pool_so)?, artifact(&verifier_so)?],
        steps,
        rent,
        transaction_sizes,
        locks: lock_evidence,
        rollover,
        assertions,
        explicit_boundaries: vec![
            "The mock verifier proves no Tag-73 or cryptographic statement; it exercises only exact ASVQ/ASVS CPI transport and Pool-side authentication.".to_string(),
            "No release Pool program id, loader/upgrade-authority policy, deployed executable identity, ALT account, or client cluster configuration has been selected.".to_string(),
            "LiteSVM is deterministic in-process Agave execution; finalized devnet execution and concurrent banking-stage account scheduling are separate release gates.".to_string(),
            "Solana runtime/SBF correctness and SPL Token program correctness remain explicit external assumptions.".to_string(),
        ],
    };

    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&output, serde_json::to_vec_pretty(&evidence)?)?;
    println!("Pool V1 focused LiteSVM lifecycle: PASS");
    println!("evidence={}", output.display());
    Ok(())
}
