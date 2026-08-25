use std::{collections::BTreeMap, env, fs, path::PathBuf};

use anyhow::{anyhow, bail, Context, Result};
use aspis_registry::{
    encode_initialize_registry_v1, encode_schedule_profile_v1, encode_simple_mutation_v1,
    pool_v1_verifier_entry_address, pool_v1_verifier_registry_address, RegistryMutationOpcodeV1,
    RegistryProgramErrorV1,
};
use aspis_statement::pool_v1::{
    decode_verifier_registry_entry_v1, decode_verifier_registry_v1, VerifierEntryStatusV1,
    POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
    POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
};
use litesvm::{types::TransactionMetadata, LiteSVM};
use serde::Serialize;
use sha2::{Digest, Sha256};
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_instruction_error::InstructionError;
use solana_keypair::Keypair;
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_sdk_ids::system_program;
use solana_signer::Signer;
use solana_transaction::Transaction;
use solana_transaction_error::TransactionError;

const HARNESS_VERSION: &str = "aspis-registry-litesvm-evidence-v1";
const LITESVM_VERSION: &str = "0.16.0";
const AGAVE_RUNTIME_VERSION: &str = "4.2.1";
const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
const EXPECTED_ARTIFACT_BYTES: usize = 102_648;
const EXPECTED_ARTIFACT_SHA256: &str =
    "1066ffc4bf8a12a0ea56b64474b70e172162fc7852b66293c0c8c5f1380f0ff6";

// Deterministic local-runtime identities only; none is a deployment address.
const REGISTRY_PROGRAM_BYTES: [u8; 32] = [0xC7; 32];
const POOL_BYTES: [u8; 32] = [0x51; 32];
const POLICY_BINDING: [u8; 32] = [0x19; 32];
const PROFILE_BINDING: [u8; 32] = [0x2A; 32];
const ROLLBACK_PROFILE_BINDING: [u8; 32] = [0x2B; 32];
const RELEASE_A: [u8; 32] = [0x3B; 32];
const RELEASE_B: [u8; 32] = [0x4B; 32];
const ROLLBACK_RELEASE: [u8; 32] = [0x5B; 32];
const VERIFIER_A: [u8; 32] = [0x6B; 32];
const VERIFIER_B: [u8; 32] = [0x7B; 32];
const WRONG_ENTRY_ADDRESS: [u8; 32] = [0xEE; 32];
const MINIMUM_DELAY: u64 = 10;
const SCHEDULE_SLOT: u64 = 100;
const FIRST_ACTIVATION_SLOT: u64 = 110;
const SECOND_ACTIVATION_SLOT: u64 = 120;
const RETIREMENT_SLOT: u64 = 121;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct AccountSnapshot {
    exists: bool,
    lamports: Option<u64>,
    owner: Option<String>,
    executable: Option<bool>,
    rent_epoch: Option<u64>,
    data_bytes: Option<usize>,
    data_sha256: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct RollbackAccountEvidence {
    label: String,
    address: String,
    before: AccountSnapshot,
    after: AccountSnapshot,
    exact_match: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ReturnEvidence {
    program_id: String,
    data_bytes: usize,
    data_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
struct StepEvidence {
    name: String,
    slot: u64,
    outcome: String,
    expected_error: Option<String>,
    actual_error: Option<String>,
    simulation_matches_execution: bool,
    compute_units: u64,
    compute_unit_limit: u32,
    fee_lamports: u64,
    rent_debit_lamports: u64,
    payer_before_lamports: u64,
    payer_after_lamports: u64,
    payer_delta_lamports: u64,
    expected_payer_delta_lamports: u64,
    return_data: ReturnEvidence,
    logs: Vec<String>,
    system_program_invoke_observed: bool,
    system_program_success_observed: bool,
    rollback_accounts: Vec<RollbackAccountEvidence>,
}

#[derive(Clone, Debug, Serialize)]
struct ArtifactEvidence {
    path: String,
    bytes: usize,
    sha256: String,
    expected_bytes: usize,
    expected_sha256: String,
    exact_match: bool,
}

#[derive(Clone, Debug, Serialize)]
struct RentEvidence {
    registry_account_bytes: usize,
    registry_rent_lamports: u64,
    entry_account_bytes: usize,
    entry_rent_lamports: u64,
    initialize_payer_delta_lamports: u64,
    initialize_expected_rent_plus_fee: u64,
    schedule_a_payer_delta_lamports: u64,
    schedule_a_expected_rent_plus_fee: u64,
    schedule_b_payer_delta_lamports: u64,
    schedule_b_expected_rent_plus_fee: u64,
    rolled_back_schedule_payer_delta_lamports: u64,
    rolled_back_schedule_expected_fee_only: u64,
}

#[derive(Clone, Debug, Serialize)]
struct FinalStateEvidence {
    registry: AccountSnapshot,
    entry_a: AccountSnapshot,
    entry_b: AccountSnapshot,
    generation: u64,
    registry_flags: u8,
    immutable: bool,
    authority_zeroed: bool,
    entry_a_status: String,
    entry_a_activation_slot: u64,
    entry_a_retirement_slot: u64,
    entry_b_status: String,
    entry_b_activation_slot: u64,
    entry_b_retirement_slot: u64,
    entries_exactly_compatible: bool,
}

#[derive(Debug, Serialize)]
struct Evidence {
    schema: String,
    harness_version: String,
    litesvm_version: String,
    agave_runtime_version: String,
    execution_environment: String,
    compute_unit_limit: u32,
    registry_program_id: String,
    program_id_status: String,
    artifact: ArtifactEvidence,
    addresses: BTreeMap<String, String>,
    steps: Vec<StepEvidence>,
    rent: RentEvidence,
    final_state: FinalStateEvidence,
    assertions: BTreeMap<String, bool>,
    explicit_boundaries: Vec<String>,
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn address(key: &LegacyPubkey) -> Address {
    Address::from(key.to_bytes())
}

fn legacy(bytes: [u8; 32]) -> LegacyPubkey {
    LegacyPubkey::new_from_array(bytes)
}

fn registry_program() -> LegacyPubkey {
    legacy(REGISTRY_PROGRAM_BYTES)
}

fn pool() -> LegacyPubkey {
    legacy(POOL_BYTES)
}

fn registry_address() -> Address {
    address(&pool_v1_verifier_registry_address(&registry_program(), &pool()).0)
}

fn entry_address(profile: &[u8; 32], release: &[u8; 32]) -> Address {
    address(&pool_v1_verifier_entry_address(&registry_program(), &pool(), profile, release).0)
}

fn account_meta(key: Address, signer: bool, writable: bool) -> AccountMeta {
    if writable {
        AccountMeta::new(key, signer)
    } else {
        AccountMeta::new_readonly(key, signer)
    }
}

fn registry_instruction(data: Vec<u8>, accounts: Vec<AccountMeta>) -> Instruction {
    Instruction {
        program_id: Address::from(REGISTRY_PROGRAM_BYTES),
        accounts,
        data,
    }
}

fn initialize_instruction(authority: Address, payer: Address) -> Instruction {
    registry_instruction(
        encode_initialize_registry_v1(POOL_BYTES, POLICY_BINDING, MINIMUM_DELAY).to_vec(),
        vec![
            account_meta(registry_address(), false, true),
            account_meta(authority, true, false),
            account_meta(payer, true, true),
            account_meta(system_program::id(), false, false),
        ],
    )
}

#[allow(clippy::too_many_arguments)]
fn schedule_instruction(
    entry: Address,
    authority: Address,
    payer: Address,
    expected_generation: u64,
    verifier: [u8; 32],
    profile: [u8; 32],
    release: [u8; 32],
    activation_slot: u64,
) -> Instruction {
    registry_instruction(
        encode_schedule_profile_v1(
            expected_generation,
            verifier,
            profile,
            release,
            1,
            activation_slot,
        )
        .to_vec(),
        vec![
            account_meta(registry_address(), false, true),
            account_meta(entry, false, true),
            account_meta(authority, true, false),
            account_meta(payer, true, true),
            account_meta(system_program::id(), false, false),
        ],
    )
}

fn simple_instruction(
    opcode: RegistryMutationOpcodeV1,
    expected_generation: u64,
    authority: Address,
    authority_is_signer: bool,
    additional_entries: &[(Address, bool)],
) -> Result<Instruction> {
    let mut accounts = vec![account_meta(registry_address(), false, true)];
    accounts.extend(
        additional_entries
            .iter()
            .map(|(key, writable)| account_meta(*key, false, *writable)),
    );
    accounts.push(account_meta(authority, authority_is_signer, false));
    Ok(registry_instruction(
        encode_simple_mutation_v1(opcode, expected_generation)
            .map_err(|error| anyhow!("encode simple mutation: {error:?}"))?
            .to_vec(),
        accounts,
    ))
}

fn transaction(
    svm: &mut LiteSVM,
    instructions: &[Instruction],
    payer: &Keypair,
    extra_signers: &[&Keypair],
) -> Transaction {
    svm.expire_blockhash();
    let mut signers = vec![payer];
    for signer in extra_signers {
        if signer.pubkey() != payer.pubkey() {
            signers.push(*signer);
        }
    }
    let mut budgeted = Vec::with_capacity(instructions.len() + 1);
    budgeted.push(ComputeBudgetInstruction::set_compute_unit_limit(
        COMPUTE_UNIT_LIMIT,
    ));
    budgeted.extend_from_slice(instructions);
    Transaction::new_signed_with_payer(
        &budgeted,
        Some(&payer.pubkey()),
        &signers,
        svm.latest_blockhash(),
    )
}

fn snapshot(svm: &LiteSVM, key: &Address) -> AccountSnapshot {
    match svm.get_account(key) {
        None => AccountSnapshot {
            exists: false,
            lamports: None,
            owner: None,
            executable: None,
            rent_epoch: None,
            data_bytes: None,
            data_sha256: None,
        },
        Some(account) => AccountSnapshot {
            exists: true,
            lamports: Some(account.lamports),
            owner: Some(account.owner.to_string()),
            executable: Some(account.executable),
            rent_epoch: Some(account.rent_epoch),
            data_bytes: Some(account.data.len()),
            data_sha256: Some(sha256_hex(&account.data)),
        },
    }
}

fn return_evidence(meta: &TransactionMetadata) -> ReturnEvidence {
    ReturnEvidence {
        program_id: meta.return_data.program_id.to_string(),
        data_bytes: meta.return_data.data.len(),
        data_sha256: sha256_hex(&meta.return_data.data),
    }
}

fn system_program_log_flags(logs: &[String]) -> (bool, bool) {
    let prefix = format!("Program {}", system_program::id());
    (
        logs.iter()
            .any(|line| line.starts_with(&prefix) && line.contains(" invoke [")),
        logs.iter().any(|line| line == &format!("{prefix} success")),
    )
}

fn success_step(
    svm: &mut LiteSVM,
    payer: &Keypair,
    name: &str,
    slot: u64,
    transaction: Transaction,
    expected_rent_debit: u64,
) -> Result<StepEvidence> {
    let payer_before = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer before transaction"))?;
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
    if executed.compute_units_consumed > u64::from(COMPUTE_UNIT_LIMIT) {
        bail!("{name}: compute use exceeded the strict cap");
    }
    if !executed.return_data.data.is_empty() {
        bail!("{name}: registry unexpectedly returned data");
    }
    let payer_after = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer after transaction"))?;
    let payer_delta = payer_before
        .checked_sub(payer_after)
        .ok_or_else(|| anyhow!("{name}: payer balance increased unexpectedly"))?;
    let expected_delta = expected_rent_debit
        .checked_add(executed.fee)
        .ok_or_else(|| anyhow!("{name}: payer delta overflow"))?;
    if payer_delta != expected_delta {
        bail!("{name}: payer delta {payer_delta} != rent plus fee {expected_delta}");
    }
    let (system_invoke, system_success) = system_program_log_flags(&executed.logs);
    Ok(StepEvidence {
        name: name.to_string(),
        slot,
        outcome: "success".to_string(),
        expected_error: None,
        actual_error: None,
        simulation_matches_execution: true,
        compute_units: executed.compute_units_consumed,
        compute_unit_limit: COMPUTE_UNIT_LIMIT,
        fee_lamports: executed.fee,
        rent_debit_lamports: expected_rent_debit,
        payer_before_lamports: payer_before,
        payer_after_lamports: payer_after,
        payer_delta_lamports: payer_delta,
        expected_payer_delta_lamports: expected_delta,
        return_data: return_evidence(&executed),
        logs: executed.logs,
        system_program_invoke_observed: system_invoke,
        system_program_success_observed: system_success,
        rollback_accounts: Vec::new(),
    })
}

#[allow(clippy::too_many_arguments)]
fn failure_step(
    svm: &mut LiteSVM,
    payer: &Keypair,
    name: &str,
    slot: u64,
    transaction: Transaction,
    expected_error: TransactionError,
    rollback_accounts: &[(&str, Address)],
    require_system_cpi: bool,
) -> Result<StepEvidence> {
    let before: Vec<_> = rollback_accounts
        .iter()
        .map(|(label, key)| ((*label).to_string(), *key, snapshot(svm, key)))
        .collect();
    let payer_before = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer before rejected transaction"))?;
    let simulation = svm
        .simulate_transaction(transaction.clone())
        .expect_err("negative-path simulation must reject");
    let executed = svm
        .send_transaction(transaction)
        .expect_err("negative-path execution must reject");
    if simulation.err != executed.err || simulation.meta != executed.meta {
        bail!("{name}: failed simulation metadata differed from execution");
    }
    if executed.err != expected_error {
        bail!(
            "{name}: wrong rejection: actual {:?}, expected {:?}",
            executed.err,
            expected_error
        );
    }
    if executed.meta.compute_units_consumed > u64::from(COMPUTE_UNIT_LIMIT) {
        bail!("{name}: rejected transaction exceeded the strict compute cap");
    }
    if !executed.meta.return_data.data.is_empty() {
        bail!("{name}: rejected transaction retained return data");
    }
    let payer_after = svm
        .get_balance(&payer.pubkey())
        .ok_or_else(|| anyhow!("{name}: missing payer after rejected transaction"))?;
    let payer_delta = payer_before
        .checked_sub(payer_after)
        .ok_or_else(|| anyhow!("{name}: rejected transaction increased payer balance"))?;
    if payer_delta != executed.meta.fee {
        bail!("{name}: rejected payer delta did not equal fee only");
    }
    let rollback: Vec<_> = before
        .into_iter()
        .map(|(label, key, before)| {
            let after = snapshot(svm, &key);
            RollbackAccountEvidence {
                label,
                address: key.to_string(),
                exact_match: before == after,
                before,
                after,
            }
        })
        .collect();
    if rollback.iter().any(|account| !account.exact_match) {
        bail!("{name}: an account changed despite rejection");
    }
    let (system_invoke, system_success) = system_program_log_flags(&executed.meta.logs);
    if require_system_cpi && !(system_invoke && system_success) {
        bail!("{name}: successful System Program CPI was not observed before rollback");
    }
    Ok(StepEvidence {
        name: name.to_string(),
        slot,
        outcome: "rejected".to_string(),
        expected_error: Some(format!("{expected_error:?}")),
        actual_error: Some(format!("{:?}", executed.err)),
        simulation_matches_execution: true,
        compute_units: executed.meta.compute_units_consumed,
        compute_unit_limit: COMPUTE_UNIT_LIMIT,
        fee_lamports: executed.meta.fee,
        rent_debit_lamports: 0,
        payer_before_lamports: payer_before,
        payer_after_lamports: payer_after,
        payer_delta_lamports: payer_delta,
        expected_payer_delta_lamports: executed.meta.fee,
        return_data: return_evidence(&executed.meta),
        logs: executed.meta.logs,
        system_program_invoke_observed: system_invoke,
        system_program_success_observed: system_success,
        rollback_accounts: rollback,
    })
}

fn custom_error(index: u8, error: RegistryProgramErrorV1) -> TransactionError {
    TransactionError::InstructionError(index, InstructionError::Custom(error as u32))
}

fn decode_registry(svm: &LiteSVM) -> Result<aspis_statement::pool_v1::VerifierRegistryV1> {
    let account = svm
        .get_account(&registry_address())
        .ok_or_else(|| anyhow!("registry account is absent"))?;
    decode_verifier_registry_v1(&account.data)
        .map_err(|error| anyhow!("decode registry: {error:?}"))
}

fn decode_entry(
    svm: &LiteSVM,
    profile: &[u8; 32],
    release: &[u8; 32],
) -> Result<aspis_statement::pool_v1::VerifierRegistryEntryV1> {
    let key = entry_address(profile, release);
    let account = svm
        .get_account(&key)
        .ok_or_else(|| anyhow!("entry account {key} is absent"))?;
    decode_verifier_registry_entry_v1(&account.data)
        .map_err(|error| anyhow!("decode entry {key}: {error:?}"))
}

fn assert_registry_generation(svm: &LiteSVM, generation: u64) -> Result<()> {
    let actual = decode_registry(svm)?.generation;
    if actual != generation {
        bail!("registry generation {actual} != expected {generation}");
    }
    Ok(())
}

fn parse_args() -> Result<(PathBuf, PathBuf)> {
    let mut args = env::args().skip(1);
    let artifact = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: harness <aspis_registry.so> <evidence.json>"))?;
    let output = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: harness <aspis_registry.so> <evidence.json>"))?;
    if args.next().is_some() {
        bail!("unexpected extra argument");
    }
    Ok((artifact, output))
}

fn main() -> Result<()> {
    let (artifact_path, output_path) = parse_args()?;
    let artifact_bytes = fs::read(&artifact_path)
        .with_context(|| format!("read artifact {}", artifact_path.display()))?;
    let artifact_sha = sha256_hex(&artifact_bytes);
    let artifact_matches =
        artifact_bytes.len() == EXPECTED_ARTIFACT_BYTES && artifact_sha == EXPECTED_ARTIFACT_SHA256;
    if !artifact_matches {
        bail!(
            "artifact mismatch: {} bytes, sha256 {}",
            artifact_bytes.len(),
            artifact_sha
        );
    }

    let mut svm = LiteSVM::new();
    svm.add_program(Address::from(REGISTRY_PROGRAM_BYTES), &artifact_bytes)?;
    svm.warp_to_slot(SCHEDULE_SLOT);

    let payer = Keypair::new_from_array([1u8; 32]);
    let authority = Keypair::new_from_array([2u8; 32]);
    let wrong_authority = Keypair::new_from_array([3u8; 32]);
    svm.airdrop(&payer.pubkey(), 50_000_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    svm.airdrop(&authority.pubkey(), 1_000_000)
        .map_err(|failed| anyhow!("fund authority: {:?}", failed.err))?;
    svm.airdrop(&wrong_authority.pubkey(), 1_000_000)
        .map_err(|failed| anyhow!("fund wrong authority: {:?}", failed.err))?;

    let registry = registry_address();
    let entry_a = entry_address(&PROFILE_BINDING, &RELEASE_A);
    let entry_b = entry_address(&PROFILE_BINDING, &RELEASE_B);
    let rollback_entry = entry_address(&ROLLBACK_PROFILE_BINDING, &ROLLBACK_RELEASE);
    let wrong_entry = Address::from(WRONG_ENTRY_ADDRESS);
    let registry_rent = svm.minimum_balance_for_rent_exemption(POOL_V1_VERIFIER_REGISTRY_BYTES);
    let entry_rent = svm.minimum_balance_for_rent_exemption(POOL_V1_VERIFIER_ENTRY_BYTES);

    let mut steps = Vec::new();

    let init_tx = transaction(
        &mut svm,
        &[initialize_instruction(authority.pubkey(), payer.pubkey())],
        &payer,
        &[&authority],
    );
    steps.push(success_step(
        &mut svm,
        &payer,
        "initialize_registry_pda",
        SCHEDULE_SLOT,
        init_tx,
        registry_rent,
    )?);
    assert_registry_generation(&svm, 0)?;
    let initialized = svm
        .get_account(&registry)
        .ok_or_else(|| anyhow!("initialized registry absent"))?;
    if initialized.owner != Address::from(REGISTRY_PROGRAM_BYTES)
        || initialized.data.len() != POOL_V1_VERIFIER_REGISTRY_BYTES
        || initialized.lamports != registry_rent
    {
        bail!("initialized registry has wrong owner, size, or rent");
    }

    let wrong_signer_ix = simple_instruction(
        RegistryMutationOpcodeV1::Pause,
        0,
        wrong_authority.pubkey(),
        true,
        &[],
    )?;
    let wrong_signer_tx = transaction(&mut svm, &[wrong_signer_ix], &payer, &[&wrong_authority]);
    steps.push(failure_step(
        &mut svm,
        &payer,
        "wrong_authority_signer_rejected",
        SCHEDULE_SLOT,
        wrong_signer_tx,
        custom_error(1, RegistryProgramErrorV1::InvalidAuthority),
        &[("registry", registry)],
        false,
    )?);

    let missing_signer_ix = simple_instruction(
        RegistryMutationOpcodeV1::Pause,
        0,
        authority.pubkey(),
        false,
        &[],
    )?;
    let missing_signer_tx = transaction(&mut svm, &[missing_signer_ix], &payer, &[]);
    steps.push(failure_step(
        &mut svm,
        &payer,
        "stored_authority_without_signature_rejected",
        SCHEDULE_SLOT,
        missing_signer_tx,
        custom_error(1, RegistryProgramErrorV1::InvalidAuthority),
        &[("registry", registry)],
        false,
    )?);

    let wrong_pda_ix = schedule_instruction(
        wrong_entry,
        authority.pubkey(),
        payer.pubkey(),
        0,
        VERIFIER_A,
        PROFILE_BINDING,
        RELEASE_A,
        FIRST_ACTIVATION_SLOT,
    );
    let wrong_pda_tx = transaction(&mut svm, &[wrong_pda_ix], &payer, &[&authority]);
    steps.push(failure_step(
        &mut svm,
        &payer,
        "wrong_entry_pda_rejected",
        SCHEDULE_SLOT,
        wrong_pda_tx,
        custom_error(1, RegistryProgramErrorV1::InvalidFreshAccount),
        &[("registry", registry), ("wrong_entry", wrong_entry)],
        false,
    )?);

    let wrong_generation_ix = simple_instruction(
        RegistryMutationOpcodeV1::Pause,
        1,
        authority.pubkey(),
        true,
        &[],
    )?;
    let wrong_generation_tx = transaction(&mut svm, &[wrong_generation_ix], &payer, &[&authority]);
    steps.push(failure_step(
        &mut svm,
        &payer,
        "stale_generation_rejected",
        SCHEDULE_SLOT,
        wrong_generation_tx,
        custom_error(1, RegistryProgramErrorV1::GenerationMismatch),
        &[("registry", registry)],
        false,
    )?);

    let rollback_schedule_ix = schedule_instruction(
        rollback_entry,
        authority.pubkey(),
        payer.pubkey(),
        0,
        VERIFIER_A,
        ROLLBACK_PROFILE_BINDING,
        ROLLBACK_RELEASE,
        FIRST_ACTIVATION_SLOT,
    );
    let rollback_failure_ix = simple_instruction(
        RegistryMutationOpcodeV1::Pause,
        99,
        authority.pubkey(),
        true,
        &[],
    )?;
    let rollback_tx = transaction(
        &mut svm,
        &[rollback_schedule_ix, rollback_failure_ix],
        &payer,
        &[&authority],
    );
    steps.push(failure_step(
        &mut svm,
        &payer,
        "system_cpi_schedule_then_later_failure_rolls_back",
        SCHEDULE_SLOT,
        rollback_tx,
        custom_error(2, RegistryProgramErrorV1::GenerationMismatch),
        &[("registry", registry), ("new_entry_pda", rollback_entry)],
        true,
    )?);
    assert_registry_generation(&svm, 0)?;

    let schedule_a_ix = schedule_instruction(
        entry_a,
        authority.pubkey(),
        payer.pubkey(),
        0,
        VERIFIER_A,
        PROFILE_BINDING,
        RELEASE_A,
        FIRST_ACTIVATION_SLOT,
    );
    let schedule_a_tx = transaction(&mut svm, &[schedule_a_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "schedule_profile_a_at_exact_delay",
        SCHEDULE_SLOT,
        schedule_a_tx,
        entry_rent,
    )?);
    assert_registry_generation(&svm, 1)?;

    svm.warp_to_slot(FIRST_ACTIVATION_SLOT - 1);
    let early_activate_ix = simple_instruction(
        RegistryMutationOpcodeV1::Activate,
        1,
        authority.pubkey(),
        true,
        &[(entry_a, true)],
    )?;
    let early_activate_tx = transaction(&mut svm, &[early_activate_ix], &payer, &[&authority]);
    steps.push(failure_step(
        &mut svm,
        &payer,
        "early_activation_rejected",
        FIRST_ACTIVATION_SLOT - 1,
        early_activate_tx,
        custom_error(1, RegistryProgramErrorV1::ActivationDelayNotElapsed),
        &[("registry", registry), ("entry_a", entry_a)],
        false,
    )?);
    assert_registry_generation(&svm, 1)?;

    svm.warp_to_slot(FIRST_ACTIVATION_SLOT);
    let activate_a_ix = simple_instruction(
        RegistryMutationOpcodeV1::Activate,
        1,
        authority.pubkey(),
        true,
        &[(entry_a, true)],
    )?;
    let activate_a_tx = transaction(&mut svm, &[activate_a_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "activate_profile_a",
        FIRST_ACTIVATION_SLOT,
        activate_a_tx,
        0,
    )?);
    assert_registry_generation(&svm, 2)?;

    let pause_ix = simple_instruction(
        RegistryMutationOpcodeV1::Pause,
        2,
        authority.pubkey(),
        true,
        &[],
    )?;
    let pause_tx = transaction(&mut svm, &[pause_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "pause_registry",
        FIRST_ACTIVATION_SLOT,
        pause_tx,
        0,
    )?);
    let paused = decode_registry(&svm)?;
    if !paused.is_paused() || paused.generation != 3 {
        bail!("pause did not set the flag and generation exactly once");
    }

    let unpause_ix = simple_instruction(
        RegistryMutationOpcodeV1::Unpause,
        3,
        authority.pubkey(),
        true,
        &[],
    )?;
    let unpause_tx = transaction(&mut svm, &[unpause_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "unpause_registry",
        FIRST_ACTIVATION_SLOT,
        unpause_tx,
        0,
    )?);
    let unpaused = decode_registry(&svm)?;
    if unpaused.is_paused() || unpaused.generation != 4 {
        bail!("unpause did not clear the flag and increment exactly once");
    }

    let schedule_b_ix = schedule_instruction(
        entry_b,
        authority.pubkey(),
        payer.pubkey(),
        4,
        VERIFIER_B,
        PROFILE_BINDING,
        RELEASE_B,
        SECOND_ACTIVATION_SLOT,
    );
    let schedule_b_tx = transaction(&mut svm, &[schedule_b_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "schedule_compatible_replacement_b",
        FIRST_ACTIVATION_SLOT,
        schedule_b_tx,
        entry_rent,
    )?);
    assert_registry_generation(&svm, 5)?;

    svm.warp_to_slot(SECOND_ACTIVATION_SLOT);
    let activate_b_ix = simple_instruction(
        RegistryMutationOpcodeV1::Activate,
        5,
        authority.pubkey(),
        true,
        &[(entry_b, true)],
    )?;
    let activate_b_tx = transaction(&mut svm, &[activate_b_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "activate_replacement_b",
        SECOND_ACTIVATION_SLOT,
        activate_b_tx,
        0,
    )?);
    assert_registry_generation(&svm, 6)?;

    svm.warp_to_slot(RETIREMENT_SLOT);
    let retire_a_ix = simple_instruction(
        RegistryMutationOpcodeV1::Retire,
        6,
        authority.pubkey(),
        true,
        &[(entry_a, true), (entry_b, false)],
    )?;
    let retire_a_tx = transaction(&mut svm, &[retire_a_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "retire_a_with_distinct_active_compatible_b",
        RETIREMENT_SLOT,
        retire_a_tx,
        0,
    )?);
    assert_registry_generation(&svm, 7)?;

    let freeze_ix = simple_instruction(
        RegistryMutationOpcodeV1::Freeze,
        7,
        authority.pubkey(),
        true,
        &[],
    )?;
    let freeze_tx = transaction(&mut svm, &[freeze_ix], &payer, &[&authority]);
    steps.push(success_step(
        &mut svm,
        &payer,
        "freeze_registry_immutably",
        RETIREMENT_SLOT,
        freeze_tx,
        0,
    )?);
    assert_registry_generation(&svm, 8)?;

    let post_freeze_ix = simple_instruction(
        RegistryMutationOpcodeV1::Pause,
        8,
        authority.pubkey(),
        true,
        &[],
    )?;
    let post_freeze_tx = transaction(&mut svm, &[post_freeze_ix], &payer, &[&authority]);
    steps.push(failure_step(
        &mut svm,
        &payer,
        "post_freeze_mutation_rejected",
        RETIREMENT_SLOT,
        post_freeze_tx,
        custom_error(1, RegistryProgramErrorV1::RegistryFrozen),
        &[
            ("registry", registry),
            ("entry_a", entry_a),
            ("entry_b", entry_b),
        ],
        false,
    )?);

    let final_registry = decode_registry(&svm)?;
    let final_a = decode_entry(&svm, &PROFILE_BINDING, &RELEASE_A)?;
    let final_b = decode_entry(&svm, &PROFILE_BINDING, &RELEASE_B)?;
    let exactly_compatible = final_b.is_exact_compatible_replacement_for(&final_a, RETIREMENT_SLOT);
    if final_registry.generation != 8
        || final_registry.flags != POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE
        || !final_registry.is_immutable()
        || final_registry.authority != [0u8; 32]
        || final_a.status != VerifierEntryStatusV1::Retired
        || final_a.activation_slot != FIRST_ACTIVATION_SLOT
        || final_a.retirement_slot != RETIREMENT_SLOT
        || final_b.status != VerifierEntryStatusV1::Active
        || final_b.activation_slot != SECOND_ACTIVATION_SLOT
        || final_b.retirement_slot != POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
        || !exactly_compatible
    {
        bail!("final registry or entry state violated the lifecycle assertions");
    }

    for (label, key, bytes, rent) in [
        (
            "registry",
            registry,
            POOL_V1_VERIFIER_REGISTRY_BYTES,
            registry_rent,
        ),
        ("entry_a", entry_a, POOL_V1_VERIFIER_ENTRY_BYTES, entry_rent),
        ("entry_b", entry_b, POOL_V1_VERIFIER_ENTRY_BYTES, entry_rent),
    ] {
        let account = svm
            .get_account(&key)
            .ok_or_else(|| anyhow!("{label}: final account absent"))?;
        if account.owner != Address::from(REGISTRY_PROGRAM_BYTES)
            || account.data.len() != bytes
            || account.lamports != rent
        {
            bail!("{label}: final owner, bytes, or rent mismatch");
        }
    }
    if svm.get_account(&rollback_entry).is_some() {
        bail!("rolled-back System CPI left its entry PDA behind");
    }

    let all_steps_under_cap = steps
        .iter()
        .all(|step| step.compute_units <= u64::from(COMPUTE_UNIT_LIMIT));
    let all_returns_empty = steps.iter().all(|step| step.return_data.data_bytes == 0);
    let all_simulations_match = steps.iter().all(|step| step.simulation_matches_execution);
    let all_rejections_rollback_exact = steps
        .iter()
        .filter(|step| step.outcome == "rejected")
        .flat_map(|step| &step.rollback_accounts)
        .all(|account| account.exact_match);
    let system_rollback = steps
        .iter()
        .find(|step| step.name == "system_cpi_schedule_then_later_failure_rolls_back")
        .ok_or_else(|| anyhow!("missing System CPI rollback evidence"))?;
    let system_cpi_rollback_exact = system_rollback.system_program_invoke_observed
        && system_rollback.system_program_success_observed
        && system_rollback
            .rollback_accounts
            .iter()
            .all(|account| account.exact_match)
        && !snapshot(&svm, &rollback_entry).exists;

    let mut addresses = BTreeMap::new();
    addresses.insert("authority".to_string(), authority.pubkey().to_string());
    addresses.insert("entry_a".to_string(), entry_a.to_string());
    addresses.insert("entry_b".to_string(), entry_b.to_string());
    addresses.insert("payer".to_string(), payer.pubkey().to_string());
    addresses.insert("pool".to_string(), address(&pool()).to_string());
    addresses.insert("registry".to_string(), registry.to_string());
    addresses.insert("rollback_entry".to_string(), rollback_entry.to_string());
    addresses.insert(
        "wrong_authority".to_string(),
        wrong_authority.pubkey().to_string(),
    );

    let init = &steps[0];
    let rolled_back = &steps[5];
    let schedule_a = &steps[6];
    let schedule_b = &steps[11];
    let rent = RentEvidence {
        registry_account_bytes: POOL_V1_VERIFIER_REGISTRY_BYTES,
        registry_rent_lamports: registry_rent,
        entry_account_bytes: POOL_V1_VERIFIER_ENTRY_BYTES,
        entry_rent_lamports: entry_rent,
        initialize_payer_delta_lamports: init.payer_delta_lamports,
        initialize_expected_rent_plus_fee: registry_rent + init.fee_lamports,
        schedule_a_payer_delta_lamports: schedule_a.payer_delta_lamports,
        schedule_a_expected_rent_plus_fee: entry_rent + schedule_a.fee_lamports,
        schedule_b_payer_delta_lamports: schedule_b.payer_delta_lamports,
        schedule_b_expected_rent_plus_fee: entry_rent + schedule_b.fee_lamports,
        rolled_back_schedule_payer_delta_lamports: rolled_back.payer_delta_lamports,
        rolled_back_schedule_expected_fee_only: rolled_back.fee_lamports,
    };

    let final_state = FinalStateEvidence {
        registry: snapshot(&svm, &registry),
        entry_a: snapshot(&svm, &entry_a),
        entry_b: snapshot(&svm, &entry_b),
        generation: final_registry.generation,
        registry_flags: final_registry.flags,
        immutable: final_registry.is_immutable(),
        authority_zeroed: final_registry.authority == [0u8; 32],
        entry_a_status: format!("{:?}", final_a.status),
        entry_a_activation_slot: final_a.activation_slot,
        entry_a_retirement_slot: final_a.retirement_slot,
        entry_b_status: format!("{:?}", final_b.status),
        entry_b_activation_slot: final_b.activation_slot,
        entry_b_retirement_slot: final_b.retirement_slot,
        entries_exactly_compatible: exactly_compatible,
    };

    let assertions = BTreeMap::from([
        ("artifact_hash_and_size_exact".to_string(), artifact_matches),
        (
            "all_compute_units_at_or_below_1400000".to_string(),
            all_steps_under_cap,
        ),
        ("all_return_data_empty".to_string(), all_returns_empty),
        (
            "all_simulations_match_execution".to_string(),
            all_simulations_match,
        ),
        (
            "all_rejections_rollback_exact".to_string(),
            all_rejections_rollback_exact,
        ),
        (
            "system_cpi_rollback_exact".to_string(),
            system_cpi_rollback_exact,
        ),
        (
            "final_generation_exactly_8".to_string(),
            final_registry.generation == 8,
        ),
        (
            "freeze_zeroed_authority".to_string(),
            final_registry.authority == [0u8; 32],
        ),
        ("registry_and_entries_exact_rent".to_string(), true),
        (
            "distinct_active_compatible_replacement_used".to_string(),
            exactly_compatible,
        ),
        ("no_network_deploy_or_send".to_string(), true),
    ]);
    if assertions.values().any(|value| !value) {
        bail!("one or more final evidence assertions failed");
    }

    let evidence = Evidence {
        schema: "aspis.registry-v1.runtime-evidence.v1".to_string(),
        harness_version: HARNESS_VERSION.to_string(),
        litesvm_version: LITESVM_VERSION.to_string(),
        agave_runtime_version: AGAVE_RUNTIME_VERSION.to_string(),
        execution_environment: "in-process LiteSVM; deterministic local identities; no RPC or network transaction".to_string(),
        compute_unit_limit: COMPUTE_UNIT_LIMIT,
        registry_program_id: Address::from(REGISTRY_PROGRAM_BYTES).to_string(),
        program_id_status: "deterministic test-only runtime address; no deployment id selected".to_string(),
        artifact: ArtifactEvidence {
            path: artifact_path.display().to_string(),
            bytes: artifact_bytes.len(),
            sha256: artifact_sha,
            expected_bytes: EXPECTED_ARTIFACT_BYTES,
            expected_sha256: EXPECTED_ARTIFACT_SHA256.to_string(),
            exact_match: artifact_matches,
        },
        addresses,
        steps,
        rent,
        final_state,
        assertions,
        explicit_boundaries: vec![
            "LiteSVM executes the SBF artifact locally; this is not validator, devnet, or deployment evidence.".to_string(),
            "The deterministic authority is a keypair, not an exercised multisig-program PDA CPI signer; the registry only enforces the stored key and runtime signer bit.".to_string(),
            "Program upgrade-authority governance remains outside this registry-account mutation lifecycle.".to_string(),
            "Policy/profile manifest authenticity and the approved SHA-256 collision boundary remain external.".to_string(),
        ],
    };

    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&output_path, serde_json::to_vec_pretty(&evidence)?)?;
    println!(
        "Aspis Registry V1 LiteSVM lifecycle: PASS ({} steps, max {} CU)",
        evidence.steps.len(),
        evidence
            .steps
            .iter()
            .map(|step| step.compute_units)
            .max()
            .unwrap_or(0)
    );
    println!("evidence={}", output_path.display());
    Ok(())
}
