extern crate alloc;

#[cfg(not(feature = "no-entrypoint"))]
#[allow(unused_imports)]
use alloc::format;
use aspis_statement::pool_v1::{
    decode_verifier_registry_entry_v1, decode_verifier_registry_v1,
    encode_verifier_registry_entry_v1, encode_verifier_registry_v1, VerifierEntryStatusV1,
    VerifierRegistryEntryV1, VerifierRegistryV1, POOL_V1_VERIFIER_ENTRY_BYTES,
    POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT, POOL_V1_VERIFIER_REGISTRY_BYTES,
    POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE, POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED,
};
#[allow(deprecated)]
use solana_program::system_instruction;
use solana_program::{
    account_info::AccountInfo, clock::Clock, entrypoint::ProgramResult, instruction::Instruction,
    program, program_error::ProgramError, pubkey::Pubkey, rent::Rent, sysvar::Sysvar,
};
use solana_sdk_ids::{native_loader, system_program};

use crate::{
    error::RegistryProgramErrorV1,
    instruction::{decode_registry_instruction_v1, RegistryInstructionV1},
};

pub const POOL_V1_VERIFIER_REGISTRY_SEED: &[u8] = b"aspis-verifier-registry-v1";
pub const POOL_V1_VERIFIER_ENTRY_SEED: &[u8] = b"aspis-verifier-entry-v1";

pub fn pool_v1_verifier_registry_address(registry_program: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VERIFIER_REGISTRY_SEED, pool.as_ref()],
        registry_program,
    )
}

pub fn pool_v1_verifier_entry_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
    profile_binding: &[u8; 32],
    release_binding: &[u8; 32],
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_VERIFIER_ENTRY_SEED,
            pool.as_ref(),
            profile_binding,
            release_binding,
        ],
        registry_program,
    )
}

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_instruction);

trait RegistryCpiRuntimeV1 {
    fn invoke<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
    ) -> ProgramResult;

    fn invoke_signed<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
        signer_seeds: &[&[&[u8]]],
    ) -> ProgramResult;
}

struct SolanaRegistryCpiRuntimeV1;

impl RegistryCpiRuntimeV1 for SolanaRegistryCpiRuntimeV1 {
    fn invoke<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
    ) -> ProgramResult {
        program::invoke(instruction, account_infos)
    }

    fn invoke_signed<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
        signer_seeds: &[&[&[u8]]],
    ) -> ProgramResult {
        program::invoke_signed(instruction, account_infos, signer_seeds)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FreshPdaPreparationV1 {
    CreateOrAllocateSystemOwned,
    ProgramOwnedZeroed,
}

fn exact_accounts<'a, 'info, const N: usize>(
    accounts: &'a [AccountInfo<'info>],
) -> Result<&'a [AccountInfo<'info>; N], ProgramError> {
    accounts
        .try_into()
        .map_err(|_| RegistryProgramErrorV1::InvalidAccountCount.into())
}

fn require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
    for left in 0..accounts.len() {
        for right in left + 1..accounts.len() {
            if accounts[left].key == accounts[right].key {
                return Err(RegistryProgramErrorV1::DuplicateAccount.into());
            }
        }
    }
    Ok(())
}

fn require_authority(registry: &VerifierRegistryV1, authority: &AccountInfo<'_>) -> ProgramResult {
    if registry.is_immutable() {
        return Err(RegistryProgramErrorV1::RegistryFrozen.into());
    }
    if authority.key.to_bytes() != registry.authority
        || !authority.is_signer
        || authority.is_writable
        || authority.executable
    {
        return Err(RegistryProgramErrorV1::InvalidAuthority.into());
    }
    Ok(())
}

fn require_initial_authority(authority: &AccountInfo<'_>) -> ProgramResult {
    if authority.key == &Pubkey::default()
        || !authority.is_signer
        || authority.is_writable
        || authority.executable
    {
        return Err(RegistryProgramErrorV1::InvalidAuthority.into());
    }
    Ok(())
}

fn require_payer_and_system_program(
    payer: &AccountInfo<'_>,
    system_program_account: &AccountInfo<'_>,
) -> ProgramResult {
    if !payer.is_signer
        || !payer.is_writable
        || payer.executable
        || payer.owner != &system_program::id()
    {
        return Err(RegistryProgramErrorV1::InvalidPayer.into());
    }
    if system_program_account.key != &system_program::id()
        || system_program_account.owner != &native_loader::id()
        || !system_program_account.executable
        || system_program_account.is_signer
        || system_program_account.is_writable
    {
        return Err(RegistryProgramErrorV1::InvalidSystemProgram.into());
    }
    Ok(())
}

fn plan_fresh_program_pda(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    expected_address: &Pubkey,
    exact_bytes: usize,
) -> Result<FreshPdaPreparationV1, ProgramError> {
    if account.key != expected_address
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(RegistryProgramErrorV1::InvalidFreshAccount.into());
    }
    if account.owner == program_id {
        let data = account.try_borrow_data()?;
        if data.len() != exact_bytes || data.iter().any(|byte| *byte != 0) {
            return Err(RegistryProgramErrorV1::InvalidFreshAccount.into());
        }
        Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
    } else if account.owner == &system_program::id() && account.data_is_empty() {
        Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned)
    } else {
        Err(RegistryProgramErrorV1::InvalidFreshAccount.into())
    }
}

fn create_or_allocate_pda<'info, R: RegistryCpiRuntimeV1>(
    runtime: &mut R,
    payer: &AccountInfo<'info>,
    account: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    exact_bytes: usize,
    owner: &Pubkey,
    signer_seeds: &[&[u8]],
) -> ProgramResult {
    if account.owner != &system_program::id() || !account.data_is_empty() {
        return Err(RegistryProgramErrorV1::InvalidFreshAccount.into());
    }
    let required_lamports = Rent::get()?.minimum_balance(exact_bytes).max(1);
    let infos = [
        payer.clone(),
        account.clone(),
        system_program_account.clone(),
    ];
    let signer_seed_sets = [signer_seeds];
    if account.lamports() == 0 {
        runtime.invoke_signed(
            &system_instruction::create_account(
                payer.key,
                account.key,
                required_lamports,
                exact_bytes as u64,
                owner,
            ),
            &infos,
            &signer_seed_sets,
        )?;
    } else {
        let deficit = required_lamports.saturating_sub(account.lamports());
        if deficit != 0 {
            runtime.invoke(
                &system_instruction::transfer(payer.key, account.key, deficit),
                &infos,
            )?;
        }
        runtime.invoke_signed(
            &system_instruction::allocate(account.key, exact_bytes as u64),
            &infos,
            &signer_seed_sets,
        )?;
        runtime.invoke_signed(
            &system_instruction::assign(account.key, owner),
            &infos,
            &signer_seed_sets,
        )?;
    }
    Ok(())
}

fn require_zero_program_account(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    exact_bytes: usize,
) -> ProgramResult {
    if account.owner != program_id
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(RegistryProgramErrorV1::InvalidFreshAccount.into());
    }
    let data = account.try_borrow_data()?;
    if data.len() != exact_bytes || data.iter().any(|byte| *byte != 0) {
        return Err(RegistryProgramErrorV1::InvalidFreshAccount.into());
    }
    Ok(())
}

fn load_registry(
    program_id: &Pubkey,
    account: &AccountInfo<'_>,
) -> Result<VerifierRegistryV1, ProgramError> {
    if account.owner != program_id
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(RegistryProgramErrorV1::InvalidRegistryAccount.into());
    }
    let registry = {
        let data = account.try_borrow_data()?;
        decode_verifier_registry_v1(&data)
            .map_err(|_| RegistryProgramErrorV1::InvalidRegistryAccount)?
    };
    let pool = Pubkey::new_from_array(registry.pool);
    if account.key != &pool_v1_verifier_registry_address(program_id, &pool).0 {
        return Err(RegistryProgramErrorV1::InvalidRegistryAddress.into());
    }
    Ok(registry)
}

fn load_entry(
    program_id: &Pubkey,
    account: &AccountInfo<'_>,
    writable: bool,
) -> Result<VerifierRegistryEntryV1, ProgramError> {
    if account.owner != program_id
        || account.executable
        || account.is_signer
        || account.is_writable != writable
    {
        return Err(RegistryProgramErrorV1::InvalidEntryAccount.into());
    }
    let entry = {
        let data = account.try_borrow_data()?;
        decode_verifier_registry_entry_v1(&data)
            .map_err(|_| RegistryProgramErrorV1::InvalidEntryAccount)?
    };
    let pool = Pubkey::new_from_array(entry.pool);
    if account.key
        != &pool_v1_verifier_entry_address(
            program_id,
            &pool,
            &entry.profile_binding,
            &entry.release_binding,
        )
        .0
    {
        return Err(RegistryProgramErrorV1::InvalidEntryAddress.into());
    }
    Ok(entry)
}

fn require_entry_registry_match(
    registry: &VerifierRegistryV1,
    entry: &VerifierRegistryEntryV1,
) -> ProgramResult {
    if entry.pool != registry.pool || entry.policy_binding != registry.policy_binding {
        return Err(RegistryProgramErrorV1::InvalidEntryAccount.into());
    }
    Ok(())
}

fn require_generation(registry: &VerifierRegistryV1, expected: u64) -> ProgramResult {
    if registry.generation != expected {
        return Err(RegistryProgramErrorV1::GenerationMismatch.into());
    }
    Ok(())
}

fn incremented_registry(registry: VerifierRegistryV1) -> Result<VerifierRegistryV1, ProgramError> {
    let generation = registry
        .generation
        .checked_add(1)
        .ok_or(RegistryProgramErrorV1::GenerationOverflow)?;
    Ok(VerifierRegistryV1 {
        generation,
        ..registry
    })
}

fn registry_image(
    registry: &VerifierRegistryV1,
) -> Result<[u8; POOL_V1_VERIFIER_REGISTRY_BYTES], ProgramError> {
    encode_verifier_registry_v1(registry)
        .map_err(|_| RegistryProgramErrorV1::InvalidRegistryAccount.into())
}

fn entry_image(
    entry: &VerifierRegistryEntryV1,
) -> Result<[u8; POOL_V1_VERIFIER_ENTRY_BYTES], ProgramError> {
    encode_verifier_registry_entry_v1(entry)
        .map_err(|_| RegistryProgramErrorV1::InvalidEntryAccount.into())
}

fn commit_registry(
    registry_account: &AccountInfo<'_>,
    image: &[u8; POOL_V1_VERIFIER_REGISTRY_BYTES],
) -> ProgramResult {
    let mut data = registry_account.try_borrow_mut_data()?;
    if data.len() != image.len() {
        return Err(RegistryProgramErrorV1::InvalidRegistryAccount.into());
    }
    data.copy_from_slice(image);
    Ok(())
}

fn commit_registry_and_entry(
    registry_account: &AccountInfo<'_>,
    registry: &[u8; POOL_V1_VERIFIER_REGISTRY_BYTES],
    entry_account: &AccountInfo<'_>,
    entry: &[u8; POOL_V1_VERIFIER_ENTRY_BYTES],
) -> ProgramResult {
    // Acquire both mutable borrows before either byte image is changed. Every
    // semantic validation and encoding step has already succeeded.
    let mut registry_data = registry_account.try_borrow_mut_data()?;
    let mut entry_data = entry_account.try_borrow_mut_data()?;
    if registry_data.len() != registry.len() || entry_data.len() != entry.len() {
        return Err(RegistryProgramErrorV1::InvalidAccountCount.into());
    }
    registry_data.copy_from_slice(registry);
    entry_data.copy_from_slice(entry);
    Ok(())
}

fn process_initialize<R: RegistryCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    pool: [u8; 32],
    policy_binding: [u8; 32],
    minimum_activation_delay_slots: u64,
    runtime: &mut R,
) -> ProgramResult {
    let [registry_account, authority, payer, system_program_account] = exact_accounts(accounts)?;
    require_unique_accounts(accounts)?;
    require_initial_authority(authority)?;
    require_payer_and_system_program(payer, system_program_account)?;

    let registry = VerifierRegistryV1 {
        flags: 0,
        pool,
        authority: authority.key.to_bytes(),
        policy_binding,
        generation: 0,
        minimum_activation_delay_slots,
    };
    let image =
        registry_image(&registry).map_err(|_| RegistryProgramErrorV1::InvalidInstruction)?;
    let pool_key = Pubkey::new_from_array(pool);
    let (expected_address, bump) = pool_v1_verifier_registry_address(program_id, &pool_key);
    let preparation = plan_fresh_program_pda(
        registry_account,
        program_id,
        &expected_address,
        POOL_V1_VERIFIER_REGISTRY_BYTES,
    )?;

    if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        let bump_seed = [bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_VERIFIER_REGISTRY_SEED,
            pool_key.as_ref(),
            &bump_seed,
        ];
        create_or_allocate_pda(
            runtime,
            payer,
            registry_account,
            system_program_account,
            POOL_V1_VERIFIER_REGISTRY_BYTES,
            program_id,
            seeds,
        )?;
        require_zero_program_account(
            registry_account,
            program_id,
            POOL_V1_VERIFIER_REGISTRY_BYTES,
        )?;
    }

    commit_registry(registry_account, &image)
}

#[allow(clippy::too_many_arguments)]
fn process_schedule<R: RegistryCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    expected_generation: u64,
    verifier_program: [u8; 32],
    profile_binding: [u8; 32],
    release_binding: [u8; 32],
    statement_version: u8,
    activation_slot: u64,
    current_slot: u64,
    runtime: &mut R,
) -> ProgramResult {
    let [registry_account, entry_account, authority, payer, system_program_account] =
        exact_accounts(accounts)?;
    require_unique_accounts(accounts)?;
    let registry = load_registry(program_id, registry_account)?;
    require_authority(&registry, authority)?;
    require_generation(&registry, expected_generation)?;
    require_payer_and_system_program(payer, system_program_account)?;

    let earliest = current_slot
        .checked_add(registry.minimum_activation_delay_slots)
        .ok_or(RegistryProgramErrorV1::ActivationDelayOverflow)?;
    if activation_slot < earliest {
        return Err(RegistryProgramErrorV1::ActivationDelayNotElapsed.into());
    }
    let entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Pending,
        statement_version,
        pool: registry.pool,
        verifier_program,
        profile_binding,
        release_binding,
        activation_slot,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: registry.policy_binding,
    };
    let encoded_entry =
        entry_image(&entry).map_err(|_| RegistryProgramErrorV1::InvalidInstruction)?;
    let next_registry = incremented_registry(registry)?;
    let encoded_registry = registry_image(&next_registry)?;
    let pool = Pubkey::new_from_array(registry.pool);
    let (expected_address, bump) =
        pool_v1_verifier_entry_address(program_id, &pool, &profile_binding, &release_binding);
    let preparation = plan_fresh_program_pda(
        entry_account,
        program_id,
        &expected_address,
        POOL_V1_VERIFIER_ENTRY_BYTES,
    )?;

    if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        let bump_seed = [bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_VERIFIER_ENTRY_SEED,
            pool.as_ref(),
            &profile_binding,
            &release_binding,
            &bump_seed,
        ];
        create_or_allocate_pda(
            runtime,
            payer,
            entry_account,
            system_program_account,
            POOL_V1_VERIFIER_ENTRY_BYTES,
            program_id,
            seeds,
        )?;
        require_zero_program_account(entry_account, program_id, POOL_V1_VERIFIER_ENTRY_BYTES)?;
    }

    commit_registry_and_entry(
        registry_account,
        &encoded_registry,
        entry_account,
        &encoded_entry,
    )
}

fn process_pause_change(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    expected_generation: u64,
    paused: bool,
) -> ProgramResult {
    let [registry_account, authority] = exact_accounts(accounts)?;
    require_unique_accounts(accounts)?;
    let registry = load_registry(program_id, registry_account)?;
    require_authority(&registry, authority)?;
    require_generation(&registry, expected_generation)?;
    if registry.is_paused() == paused {
        return Err(if paused {
            RegistryProgramErrorV1::RegistryAlreadyPaused.into()
        } else {
            RegistryProgramErrorV1::RegistryNotPaused.into()
        });
    }
    let mut next = incremented_registry(registry)?;
    if paused {
        next.flags |= POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED;
    } else {
        next.flags &= !POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED;
    }
    commit_registry(registry_account, &registry_image(&next)?)
}

fn process_activate(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    expected_generation: u64,
    current_slot: u64,
) -> ProgramResult {
    let [registry_account, entry_account, authority] = exact_accounts(accounts)?;
    require_unique_accounts(accounts)?;
    let registry = load_registry(program_id, registry_account)?;
    require_authority(&registry, authority)?;
    require_generation(&registry, expected_generation)?;
    let entry = load_entry(program_id, entry_account, true)?;
    require_entry_registry_match(&registry, &entry)?;
    if entry.status != VerifierEntryStatusV1::Pending {
        return Err(RegistryProgramErrorV1::EntryNotPending.into());
    }
    if !entry.has_no_retirement_slot() {
        return Err(RegistryProgramErrorV1::InvalidEntryState.into());
    }
    if current_slot < entry.activation_slot {
        return Err(RegistryProgramErrorV1::ActivationDelayNotElapsed.into());
    }
    let next_entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Active,
        ..entry
    };
    let next_registry = incremented_registry(registry)?;
    commit_registry_and_entry(
        registry_account,
        &registry_image(&next_registry)?,
        entry_account,
        &entry_image(&next_entry)?,
    )
}

fn process_retire(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    expected_generation: u64,
    current_slot: u64,
) -> ProgramResult {
    let [registry_account, retiring_account, replacement_account, authority] =
        exact_accounts(accounts)?;
    require_unique_accounts(accounts)?;
    let registry = load_registry(program_id, registry_account)?;
    require_authority(&registry, authority)?;
    require_generation(&registry, expected_generation)?;
    let retiring = load_entry(program_id, retiring_account, true)?;
    let replacement = load_entry(program_id, replacement_account, false)?;
    require_entry_registry_match(&registry, &retiring)?;
    require_entry_registry_match(&registry, &replacement)?;
    if !retiring.is_active_at(current_slot) {
        return Err(RegistryProgramErrorV1::EntryNotActive.into());
    }
    if !retiring.has_no_retirement_slot() {
        return Err(RegistryProgramErrorV1::InvalidEntryState.into());
    }
    if !replacement.is_active_at(current_slot) {
        return Err(RegistryProgramErrorV1::ReplacementNotActive.into());
    }
    if !replacement.is_exact_compatible_replacement_for(&retiring, current_slot) {
        return Err(RegistryProgramErrorV1::IncompatibleReplacement.into());
    }
    if current_slot <= retiring.activation_slot {
        return Err(RegistryProgramErrorV1::InvalidRetirementSlot.into());
    }
    let next_entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Retired,
        retirement_slot: current_slot,
        ..retiring
    };
    let next_registry = incremented_registry(registry)?;
    commit_registry_and_entry(
        registry_account,
        &registry_image(&next_registry)?,
        retiring_account,
        &entry_image(&next_entry)?,
    )
}

fn process_freeze(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    expected_generation: u64,
) -> ProgramResult {
    let [registry_account, authority] = exact_accounts(accounts)?;
    require_unique_accounts(accounts)?;
    let registry = load_registry(program_id, registry_account)?;
    require_authority(&registry, authority)?;
    require_generation(&registry, expected_generation)?;
    let mut next = incremented_registry(registry)?;
    next.flags |= POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE;
    next.authority = [0u8; 32];
    commit_registry(registry_account, &registry_image(&next)?)
}

fn process_decoded_instruction<R: RegistryCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction: RegistryInstructionV1,
    current_slot: u64,
    runtime: &mut R,
) -> ProgramResult {
    match instruction {
        RegistryInstructionV1::Initialize {
            pool,
            policy_binding,
            minimum_activation_delay_slots,
        } => process_initialize(
            program_id,
            accounts,
            pool,
            policy_binding,
            minimum_activation_delay_slots,
            runtime,
        ),
        RegistryInstructionV1::ScheduleProfile {
            expected_generation,
            verifier_program,
            profile_binding,
            release_binding,
            statement_version,
            activation_slot,
        } => process_schedule(
            program_id,
            accounts,
            expected_generation,
            verifier_program,
            profile_binding,
            release_binding,
            statement_version,
            activation_slot,
            current_slot,
            runtime,
        ),
        RegistryInstructionV1::Pause {
            expected_generation,
        } => process_pause_change(program_id, accounts, expected_generation, true),
        RegistryInstructionV1::Unpause {
            expected_generation,
        } => process_pause_change(program_id, accounts, expected_generation, false),
        RegistryInstructionV1::Activate {
            expected_generation,
        } => process_activate(program_id, accounts, expected_generation, current_slot),
        RegistryInstructionV1::Retire {
            expected_generation,
        } => process_retire(program_id, accounts, expected_generation, current_slot),
        RegistryInstructionV1::Freeze {
            expected_generation,
        } => process_freeze(program_id, accounts, expected_generation),
    }
}

#[cfg(test)]
fn process_instruction_with_runtime<R: RegistryCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    current_slot: u64,
    runtime: &mut R,
) -> ProgramResult {
    let instruction = decode_registry_instruction_v1(instruction_data)
        .map_err(|_| RegistryProgramErrorV1::InvalidInstruction)?;
    process_decoded_instruction(program_id, accounts, instruction, current_slot, runtime)
}

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    let instruction = decode_registry_instruction_v1(instruction_data)
        .map_err(|_| RegistryProgramErrorV1::InvalidInstruction)?;
    let current_slot = if instruction.requires_clock() {
        Clock::get()?.slot
    } else {
        0
    };
    let mut runtime = SolanaRegistryCpiRuntimeV1;
    process_decoded_instruction(
        program_id,
        accounts,
        instruction,
        current_slot,
        &mut runtime,
    )
}

#[cfg(test)]
#[path = "processor_tests.rs"]
mod tests;
