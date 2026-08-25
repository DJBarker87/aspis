//! Native Solana entrypoint and exact Pool V1 account composition.
//!
//! The entrypoint deliberately has no `declare_id!`: the runtime-supplied
//! `program_id` is the sole PDA domain.  A release must pin that id outside
//! this crate before any client or deployment is considered compatible.

extern crate alloc;

#[cfg(target_os = "solana")]
use alloc::format;
use alloc::{vec, vec::Vec};
use aspis_core::transcript::HashFn;
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        encode_historical_anchor_envelope_v1, root_history_location, PoolV1NullifierMarkerV1,
        PoolV1TransitionKind, POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
        POOL_V1_NULLIFIER_MARKER_SEED, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_SEED,
    },
};
#[allow(deprecated)]
use solana_program::system_instruction;
use solana_program::{
    account_info::AccountInfo,
    clock::Clock,
    entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction},
    program,
    program_error::ProgramError,
    pubkey::Pubkey,
    rent::Rent,
    sysvar::Sysvar,
};
use solana_sdk_ids::{
    bpf_loader, bpf_loader_upgradeable, loader_v4, native_loader, system_program,
};

use crate::{
    anchor::{
        authenticate_historical_anchor_after_prevalidated_state_v1,
        authenticate_historical_anchor_v1, HistoricalAnchorAuthorizationV1,
    },
    deposit_transport::{
        process_prevalidated_vault_backed_deposit_v1, POOL_V1_DEPOSIT_INSTRUCTION_MAGIC,
    },
    error::PoolV1ProgramError,
    history::{require_program_account, validate_new_page_account},
    instruction::{
        decode_deposit_top_level_v1, decode_initialize_instruction_v1,
        decode_private_transfer_instruction_v1, decode_withdrawal_instruction_v1,
        encode_initialization_receipt_v1, encode_transition_receipt_v1, TransitionReceiptV1,
        POOL_V1_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC,
        POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC,
    },
    nullifier::{
        plan_nullifier_marker_consumption_v1, NullifierMarkerPreparationV1,
        PlannedNullifierMarkerV1,
    },
    state::{
        pool_v1_state_address, CanonicalPoolStateV1, PoolStateV1, POOL_V1_STATE_ACCOUNT_BYTES,
        POOL_V1_STATE_SEED,
    },
    transition::{
        apply_authorized_append_after_prevalidated_history_v1, apply_authorized_append_after_v1,
        initialize_pool_accounts_v1, validate_current_history,
        validate_current_history_after_prevalidated_anchor_v1, AuthorizedAppendV1,
    },
    vault::{
        exact_withdrawal_transfer_account_infos_v1, parse_legacy_mint_v1,
        parse_legacy_token_account_v1, plan_legacy_deposit_transfer_v1,
        plan_legacy_withdrawal_transfer_v1, pool_v1_vault_authority_address,
        pool_v1_vault_token_account_address, validate_exact_withdrawal_delta_v1,
        LEGACY_SPL_TOKEN_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_VAULT_AUTHORITY_SEED,
        POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,
    },
    verifier_dispatch::{
        derive_verifier_dispatch_claim_v1, dispatch_authenticated_verifier_readonly_v1,
        VerifierDispatchClaimV1,
    },
};

const SPL_TOKEN_INITIALIZE_ACCOUNT3_DISCRIMINANT: u8 = 18;

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_instruction);

trait PoolCpiRuntimeV1 {
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

struct SolanaPoolCpiRuntimeV1;

impl PoolCpiRuntimeV1 for SolanaPoolCpiRuntimeV1 {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VaultPreparationV1 {
    CreateAndInitialize,
    InitializedEmpty,
}

fn solana_sha256(inputs: &[&[u8]]) -> [u8; 32] {
    solana_program::hash::hashv(inputs).to_bytes()
}

fn supported_program_loader(owner: &Pubkey) -> bool {
    owner == &bpf_loader::id()
        || owner == &bpf_loader_upgradeable::id()
        || owner == &loader_v4::id()
}

fn require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
    for left in 0..accounts.len() {
        for right in left + 1..accounts.len() {
            if accounts[left].key == accounts[right].key {
                return Err(ProgramError::InvalidArgument);
            }
        }
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
        return Err(PoolV1ProgramError::InvalidPayer.into());
    }
    if system_program_account.key != &system_program::id()
        || system_program_account.owner != &native_loader::id()
        || !system_program_account.executable
        || system_program_account.is_signer
        || system_program_account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidSystemProgram.into());
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
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    if account.owner == program_id {
        let data = account.try_borrow_data()?;
        if data.len() != exact_bytes || data.iter().any(|byte| *byte != 0) {
            return Err(PoolV1ProgramError::InvalidFreshAccount.into());
        }
        Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
    } else if account.owner == &system_program::id() && account.data_is_empty() {
        Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned)
    } else {
        Err(PoolV1ProgramError::InvalidFreshAccount.into())
    }
}

fn create_or_allocate_pda<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    payer: &AccountInfo<'info>,
    account: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    exact_bytes: usize,
    owner: &Pubkey,
    signer_seeds: &[&[u8]],
) -> ProgramResult {
    require_payer_and_system_program(payer, system_program_account)?;
    if account.owner != &system_program::id() || !account.data_is_empty() {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
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

fn require_token_program_account(account: &AccountInfo<'_>) -> ProgramResult {
    if account.key != &LEGACY_SPL_TOKEN_PROGRAM_ID
        || !account.executable
        || account.is_signer
        || account.is_writable
        || !supported_program_loader(account.owner)
    {
        return Err(PoolV1ProgramError::InvalidTokenProgram.into());
    }
    Ok(())
}

fn require_initialized_empty_vault(
    program_id: &Pubkey,
    pool: &Pubkey,
    mint: &Pubkey,
    vault: &AccountInfo<'_>,
) -> ProgramResult {
    if vault.key != &pool_v1_vault_token_account_address(program_id, pool).0
        || vault.owner != &LEGACY_SPL_TOKEN_PROGRAM_ID
        || vault.executable
        || vault.is_signer
        || !vault.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    let parsed = parse_legacy_token_account_v1(&vault.try_borrow_data()?)?;
    if parsed.mint != *mint
        || parsed.authority != pool_v1_vault_authority_address(program_id, pool).0
        || parsed.amount != 0
        || parsed.has_delegate
        || parsed.is_native
        || parsed.delegated_amount != 0
        || parsed.has_close_authority
    {
        return Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into());
    }
    Ok(())
}

fn plan_vault_initialization(
    program_id: &Pubkey,
    pool: &Pubkey,
    mint: &Pubkey,
    vault: &AccountInfo<'_>,
) -> Result<VaultPreparationV1, ProgramError> {
    if vault.key != &pool_v1_vault_token_account_address(program_id, pool).0
        || vault.executable
        || vault.is_signer
        || !vault.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    if vault.owner == &system_program::id() && vault.data_is_empty() {
        Ok(VaultPreparationV1::CreateAndInitialize)
    } else {
        require_initialized_empty_vault(program_id, pool, mint, vault)?;
        Ok(VaultPreparationV1::InitializedEmpty)
    }
}

#[allow(clippy::too_many_arguments)]
fn initialize_vault_account<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    program_id: &Pubkey,
    pool: &Pubkey,
    mint: &AccountInfo<'info>,
    vault: &AccountInfo<'info>,
    token_program: &AccountInfo<'info>,
    payer: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    preparation: VaultPreparationV1,
) -> ProgramResult {
    if preparation == VaultPreparationV1::InitializedEmpty {
        return Ok(());
    }
    let (_, bump) = pool_v1_vault_token_account_address(program_id, pool);
    let bump_seed = [bump];
    let seeds: &[&[u8]] = &[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED, pool.as_ref(), &bump_seed];
    create_or_allocate_pda(
        runtime,
        payer,
        vault,
        system_program_account,
        LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
        &LEGACY_SPL_TOKEN_PROGRAM_ID,
        seeds,
    )?;

    let authority = pool_v1_vault_authority_address(program_id, pool).0;
    let mut data = Vec::with_capacity(33);
    data.push(SPL_TOKEN_INITIALIZE_ACCOUNT3_DISCRIMINANT);
    data.extend_from_slice(authority.as_ref());
    let instruction = Instruction {
        program_id: LEGACY_SPL_TOKEN_PROGRAM_ID,
        accounts: vec![
            AccountMeta::new(*vault.key, false),
            AccountMeta::new_readonly(*mint.key, false),
        ],
        data,
    };
    runtime.invoke(
        &instruction,
        &[vault.clone(), mint.clone(), token_program.clone()],
    )?;
    require_initialized_empty_vault(program_id, pool, mint.key, vault)
}

fn load_canonical_pool_state(
    program_id: &Pubkey,
    pool_account: &AccountInfo<'_>,
) -> Result<CanonicalPoolStateV1, ProgramError> {
    CanonicalPoolStateV1::decode_account(program_id, pool_account)
}

#[allow(clippy::too_many_arguments)]
fn create_program_pda_if_needed<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    program_id: &Pubkey,
    payer: &AccountInfo<'info>,
    account: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    exact_bytes: usize,
    preparation: FreshPdaPreparationV1,
    signer_seeds: &[&[u8]],
) -> ProgramResult {
    if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        create_or_allocate_pda(
            runtime,
            payer,
            account,
            system_program_account,
            exact_bytes,
            program_id,
            signer_seeds,
        )?;
    }
    Ok(())
}

#[inline(never)]
fn process_initialize_with_runtime_v1<'info, R: PoolCpiRuntimeV1, S: FnOnce(&[u8])>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    runtime: &mut R,
    set_return_data: S,
) -> ProgramResult {
    let initialization = decode_initialize_instruction_v1(instruction_data)?;
    let [payer, pool, page_zero, mint, vault, token_program, system_program_account] = accounts
    else {
        return Err(if accounts.len() < 7 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    require_unique_accounts(accounts)?;
    require_payer_and_system_program(payer, system_program_account)?;
    require_token_program_account(token_program)?;

    let mint_key = Pubkey::new_from_array(initialization.asset_mint);
    if mint.key != &mint_key
        || mint.owner != &LEGACY_SPL_TOKEN_PROGRAM_ID
        || mint.executable
        || mint.is_signer
        || mint.is_writable
    {
        return Err(PoolV1ProgramError::InvalidMint.into());
    }
    parse_legacy_mint_v1(&mint.try_borrow_data()?)?;

    let (expected_pool, pool_bump) = pool_v1_state_address(program_id, &mint_key);
    let pool_preparation = plan_fresh_program_pda(
        pool,
        program_id,
        &expected_pool,
        POOL_V1_STATE_ACCOUNT_BYTES,
    )?;
    let (expected_page, page_bump) = crate::pool_v1_root_page_address(program_id, pool.key, 0);
    let page_preparation = plan_fresh_program_pda(
        page_zero,
        program_id,
        &expected_page,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    )?;
    let vault_preparation = plan_vault_initialization(program_id, pool.key, &mint_key, vault)?;

    // Construct and encode the full state before the first CPI. This catches
    // every policy/identity/tree format error while all accounts are unchanged.
    PoolStateV1::genesis_boxed(pool.key, initialization)?.validate_encoding()?;

    let pool_bump_seed = [pool_bump];
    let pool_seeds: &[&[u8]] = &[POOL_V1_STATE_SEED, mint_key.as_ref(), &pool_bump_seed];
    create_program_pda_if_needed(
        runtime,
        program_id,
        payer,
        pool,
        system_program_account,
        POOL_V1_STATE_ACCOUNT_BYTES,
        pool_preparation,
        pool_seeds,
    )?;
    let page_number = 0u64.to_le_bytes();
    let page_bump_seed = [page_bump];
    let page_seeds: &[&[u8]] = &[
        POOL_V1_ROOT_HISTORY_PAGE_SEED,
        pool.key.as_ref(),
        &page_number,
        &page_bump_seed,
    ];
    create_program_pda_if_needed(
        runtime,
        program_id,
        payer,
        page_zero,
        system_program_account,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        page_preparation,
        page_seeds,
    )?;
    initialize_vault_account(
        runtime,
        program_id,
        pool.key,
        mint,
        vault,
        token_program,
        payer,
        system_program_account,
        vault_preparation,
    )?;

    initialize_pool_accounts_v1(
        program_id,
        &[pool.clone(), page_zero.clone()],
        initialization,
    )?;
    let receipt = encode_initialization_receipt_v1(pool.key, page_zero.key, vault.key);
    set_return_data(&receipt);
    Ok(())
}

fn deposit_rolls_to_next_page(state: &PoolStateV1) -> Result<bool, ProgramError> {
    let current_sequence = state.current_root_sequence();
    let next_sequence = current_sequence
        .checked_add(1)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    Ok(root_history_location(next_sequence).page_number
        != root_history_location(current_sequence).page_number)
}

#[inline(never)]
fn process_deposit_with_runtime_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    runtime: &mut R,
) -> ProgramResult {
    let request = decode_deposit_top_level_v1(instruction_data)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = load_canonical_pool_state(program_id, pool)?;
    let rollover = deposit_rolls_to_next_page(&state)?;
    if !rollover {
        let [pool, current_page, mint, source, source_authority, vault, token_program] = accounts
        else {
            return Err(if accounts.len() < 7 {
                ProgramError::NotEnoughAccountKeys
            } else {
                ProgramError::InvalidArgument
            });
        };
        require_unique_accounts(accounts)?;
        require_token_program_account(token_program)?;
        return process_prevalidated_vault_backed_deposit_v1(
            program_id,
            &[pool.clone(), current_page.clone()],
            &[
                mint.clone(),
                source.clone(),
                source_authority.clone(),
                vault.clone(),
                token_program.clone(),
            ],
            &state,
            request,
        );
    }

    let [pool, current_page, next_page, mint, source, source_authority, vault, token_program, payer, system_program_account] =
        accounts
    else {
        return Err(if accounts.len() < 10 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    require_unique_accounts(accounts)?;
    require_payer_and_system_program(payer, system_program_account)?;
    require_token_program_account(token_program)?;
    if current_page.is_signer || current_page.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    validate_current_history(program_id, pool, current_page, &state)?;
    let token_accounts = [
        mint.clone(),
        source.clone(),
        source_authority.clone(),
        vault.clone(),
        token_program.clone(),
    ];
    // Validate the entire economic transfer before creating the rollover page.
    plan_legacy_deposit_transfer_v1(
        program_id,
        pool.key,
        &state,
        &token_accounts,
        request.amount,
    )?;

    let next_page_number = root_history_location(state.current_root_sequence() + 1).page_number;
    let (expected_next, next_bump) =
        crate::pool_v1_root_page_address(program_id, pool.key, next_page_number);
    let preparation = plan_fresh_program_pda(
        next_page,
        program_id,
        &expected_next,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    )?;
    let page_number_bytes = next_page_number.to_le_bytes();
    let bump_seed = [next_bump];
    let seeds: &[&[u8]] = &[
        POOL_V1_ROOT_HISTORY_PAGE_SEED,
        pool.key.as_ref(),
        &page_number_bytes,
        &bump_seed,
    ];
    create_program_pda_if_needed(
        runtime,
        program_id,
        payer,
        next_page,
        system_program_account,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        preparation,
        seeds,
    )?;
    validate_new_page_account(program_id, pool.key, next_page_number, next_page)?;
    process_prevalidated_vault_backed_deposit_v1(
        program_id,
        &[pool.clone(), current_page.clone(), next_page.clone()],
        &token_accounts,
        &state,
        request,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SpendPageLayoutV1 {
    anchor_index: usize,
    current_index: usize,
    next_index: Option<usize>,
    suffix_start: usize,
    next_page_number: Option<u64>,
    next_page_bump: Option<u8>,
}

fn require_spend_capacity(state: &PoolStateV1, append_count: u64) -> ProgramResult {
    let next = state
        .current_root_sequence()
        .checked_add(append_count)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    if state.current_root_sequence() >= aspis_statement::pool_v1::POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    if next > aspis_statement::pool_v1::POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1ProgramError::InsufficientTreeCapacity.into());
    }
    Ok(())
}

fn plan_spend_page_layout_v1(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    state: &PoolStateV1,
    anchor_sequence: u64,
    append_count: u64,
) -> Result<SpendPageLayoutV1, ProgramError> {
    require_spend_capacity(state, append_count)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let anchor_number = root_history_location(anchor_sequence).page_number;
    let current_number = root_history_location(state.current_root_sequence()).page_number;
    let first_number = root_history_location(state.current_root_sequence() + 1).page_number;
    let last_number =
        root_history_location(state.current_root_sequence() + append_count).page_number;
    if anchor_number > current_number
        || first_number < current_number
        || last_number > current_number.saturating_add(1)
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }

    let anchor_key = crate::pool_v1_root_page_address(program_id, pool.key, anchor_number).0;
    let current_key = crate::pool_v1_root_page_address(program_id, pool.key, current_number).0;
    let anchor_index = 1;
    let anchor_account = accounts
        .get(anchor_index)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    if anchor_account.key != &anchor_key {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    let mut cursor = 2;
    let current_index = if anchor_key == current_key {
        anchor_index
    } else {
        let index = cursor;
        cursor += 1;
        let current = accounts
            .get(index)
            .ok_or(ProgramError::NotEnoughAccountKeys)?;
        if current.key != &current_key {
            return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
        }
        index
    };
    let current_writable = first_number == current_number;
    require_program_account(&accounts[current_index], program_id, current_writable)?;
    if accounts[current_index].is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    if current_index != anchor_index {
        require_program_account(anchor_account, program_id, false)?;
        if anchor_account.is_signer {
            return Err(ProgramError::InvalidAccountData);
        }
    }

    let (next_index, next_page_number, next_page_bump) = if last_number > current_number {
        let index = cursor;
        cursor += 1;
        let next = accounts
            .get(index)
            .ok_or(ProgramError::NotEnoughAccountKeys)?;
        let (expected, bump) = crate::pool_v1_root_page_address(program_id, pool.key, last_number);
        if next.key != &expected {
            return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
        }
        (Some(index), Some(last_number), Some(bump))
    } else {
        (None, None, None)
    };
    Ok(SpendPageLayoutV1 {
        anchor_index,
        current_index,
        next_index,
        suffix_start: cursor,
        next_page_number,
        next_page_bump,
    })
}

fn validate_spend_binding_v1(
    pool: &AccountInfo<'_>,
    state: &PoolStateV1,
    transition_kind: PoolV1TransitionKind,
    envelope_kind: PoolV1TransitionKind,
    statement_pool: &[u8; 32],
    statement_domain: &[u8; 32],
    statement_asset_id: aspis_core::field::M31,
) -> ProgramResult {
    if envelope_kind != transition_kind
        || statement_pool != &pool.key.to_bytes()
        || statement_domain != &state.identity.deployment_domain
        || statement_asset_id != state.identity.asset_id
    {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    Ok(())
}

fn plan_marker_from_envelope_v1(
    program_id: &Pubkey,
    marker_account: &AccountInfo<'_>,
    envelope: &aspis_statement::pool_v1::HistoricalAnchorEnvelopeV1,
) -> Result<PlannedNullifierMarkerV1, ProgramError> {
    plan_nullifier_marker_consumption_v1(
        program_id,
        marker_account,
        PoolV1NullifierMarkerV1::from_historical_anchor(envelope),
    )
}

fn create_next_root_page_if_needed<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    layout: SpendPageLayoutV1,
    payer: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
) -> ProgramResult {
    let Some(next_index) = layout.next_index else {
        return Ok(());
    };
    let next_page = &accounts[next_index];
    let page_number = layout
        .next_page_number
        .ok_or(PoolV1ProgramError::StateHistoryMismatch)?;
    let bump = layout
        .next_page_bump
        .ok_or(PoolV1ProgramError::StateHistoryMismatch)?;
    let expected = crate::pool_v1_root_page_address(program_id, accounts[0].key, page_number).0;
    let preparation = plan_fresh_program_pda(
        next_page,
        program_id,
        &expected,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    )?;
    let page_number_bytes = page_number.to_le_bytes();
    let bump_seed = [bump];
    let seeds: &[&[u8]] = &[
        POOL_V1_ROOT_HISTORY_PAGE_SEED,
        accounts[0].key.as_ref(),
        &page_number_bytes,
        &bump_seed,
    ];
    create_program_pda_if_needed(
        runtime,
        program_id,
        payer,
        next_page,
        system_program_account,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        preparation,
        seeds,
    )?;
    validate_new_page_account(program_id, accounts[0].key, page_number, next_page)
}

fn state_accounts_for_append_v1<'info>(
    accounts: &[AccountInfo<'info>],
    layout: SpendPageLayoutV1,
) -> Vec<AccountInfo<'info>> {
    let mut state_accounts = Vec::with_capacity(if layout.next_index.is_some() { 3 } else { 2 });
    state_accounts.push(accounts[0].clone());
    state_accounts.push(accounts[layout.current_index].clone());
    if let Some(next_index) = layout.next_index {
        state_accounts.push(accounts[next_index].clone());
    }
    state_accounts
}

fn create_and_write_marker_v1<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    program_id: &Pubkey,
    pool: &Pubkey,
    marker_account: &AccountInfo<'info>,
    payer: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    planned: PlannedNullifierMarkerV1,
) -> ProgramResult {
    if planned.preparation == NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned {
        let nullifier_bytes = planned.marker.canonical_nullifier_encoding();
        let bump_seed = [planned.address_bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_NULLIFIER_MARKER_SEED,
            pool.as_ref(),
            &nullifier_bytes,
            &bump_seed,
        ];
        create_or_allocate_pda(
            runtime,
            payer,
            marker_account,
            system_program_account,
            POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
            program_id,
            seeds,
        )?;
    }
    let ready = plan_nullifier_marker_consumption_v1(program_id, marker_account, planned.marker)?;
    if ready.preparation != NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed
        || ready.encoded_marker != planned.encoded_marker
    {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }
    let mut data = marker_account.try_borrow_mut_data()?;
    data.copy_from_slice(&planned.encoded_marker);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn process_private_transfer_with_runtime_v1<'info, R, V, S>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    hash: HashFn,
    runtime: &mut R,
    verify: V,
    set_return_data: S,
) -> ProgramResult
where
    R: PoolCpiRuntimeV1,
    V: FnOnce(
        &Pubkey,
        &[u8],
        &[u8],
        &PoolStateV1,
        &[AccountInfo<'info>],
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        VerifierDispatchClaimV1,
        u64,
    ) -> ProgramResult,
    S: FnOnce(&[u8]),
{
    let decoded = decode_private_transfer_instruction_v1(instruction_data)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = load_canonical_pool_state(program_id, pool)?;
    validate_spend_binding_v1(
        pool,
        &state,
        PoolV1TransitionKind::PrivateTransfer,
        decoded.envelope.transition_kind,
        &decoded.statement.pool,
        &decoded.statement.deployment_domain,
        decoded.statement.asset_id,
    )?;
    let layout = plan_spend_page_layout_v1(
        program_id,
        accounts,
        &state,
        decoded.envelope.anchor_sequence,
        2,
    )?;
    let expected_accounts = layout.suffix_start + 7;
    if accounts.len() != expected_accounts {
        return Err(if accounts.len() < expected_accounts {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    require_unique_accounts(accounts)?;
    let marker = &accounts[layout.suffix_start];
    let payer = &accounts[layout.suffix_start + 1];
    let system_program_account = &accounts[layout.suffix_start + 2];
    let registry_accounts = &accounts[layout.suffix_start + 3..layout.suffix_start + 5];
    let verifier_program = &accounts[layout.suffix_start + 5];
    let proof = &accounts[layout.suffix_start + 6];
    require_payer_and_system_program(payer, system_program_account)?;

    let encoded_envelope = encode_historical_anchor_envelope_v1(&decoded.envelope)
        .map_err(|_| PoolV1ProgramError::InvalidHistoricalAnchorEnvelope)?;
    let authenticated_anchor = authenticate_historical_anchor_after_prevalidated_state_v1(
        program_id,
        pool,
        &accounts[layout.anchor_index],
        &encoded_envelope,
        HistoricalAnchorAuthorizationV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            verifier_profile: decoded.envelope.verifier_profile,
            verifier_release: decoded.envelope.verifier_release,
        },
        &state,
    )?;
    let current_history = validate_current_history_after_prevalidated_anchor_v1(
        program_id,
        pool,
        &accounts[layout.current_index],
        &state,
        authenticated_anchor,
    )?;
    let planned_marker = plan_marker_from_envelope_v1(program_id, marker, &decoded.envelope)?;
    if let Some(next_index) = layout.next_index {
        let page_number = layout
            .next_page_number
            .ok_or(PoolV1ProgramError::StateHistoryMismatch)?;
        let expected = crate::pool_v1_root_page_address(program_id, pool.key, page_number).0;
        plan_fresh_program_pda(
            &accounts[next_index],
            program_id,
            &expected,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        )?;
    }
    let claim = derive_verifier_dispatch_claim_v1(verifier_program, proof, hash)?;
    verify(
        pool.key,
        &encoded_envelope,
        decoded.statement_payload,
        &state,
        registry_accounts,
        verifier_program,
        proof,
        claim,
        current_slot,
    )?;

    create_next_root_page_if_needed(
        runtime,
        program_id,
        accounts,
        layout,
        payer,
        system_program_account,
    )?;
    let state_accounts = state_accounts_for_append_v1(accounts, layout);
    // `state` is the sealed result of the complete fail-closed decode above.
    // No intervening CPI receives the Pool account, so reuse it here rather
    // than repeating the depth-20 source reconstruction and the standalone
    // append path's source/post-state reconstructions.
    let append = apply_authorized_append_after_prevalidated_history_v1(
        program_id,
        &state_accounts,
        &state,
        current_history,
        AuthorizedAppendV1::Two(
            decoded.statement.recipient_commitment,
            decoded.statement.change_commitment,
        ),
        || {
            let replanned = plan_marker_from_envelope_v1(program_id, marker, &decoded.envelope)?;
            if replanned != planned_marker {
                return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
            }
            create_and_write_marker_v1(
                runtime,
                program_id,
                pool.key,
                marker,
                payer,
                system_program_account,
                replanned,
            )
        },
    )?;
    let second = append.second.ok_or(ProgramError::InvalidAccountData)?;
    let receipt = encode_transition_receipt_v1(&TransitionReceiptV1 {
        transition_kind: PoolV1TransitionKind::PrivateTransfer,
        pool: pool.key.to_bytes(),
        nullifier: decoded.statement.nullifier,
        first_output: decoded.statement.recipient_commitment,
        second_output_or_destination: encode_digest_canonical(&decoded.statement.change_commitment),
        withdrawal_amount: 0,
        first_leaf_index: append.first.leaf_index,
        second_leaf_index: second.leaf_index,
        root_sequence: second.leaf_index + 1,
        root: second.root,
    })?;
    set_return_data(&receipt);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn process_withdrawal_with_runtime_v1<'info, R, V, S>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    hash: HashFn,
    runtime: &mut R,
    verify: V,
    set_return_data: S,
) -> ProgramResult
where
    R: PoolCpiRuntimeV1,
    V: FnOnce(
        &Pubkey,
        &[u8],
        &[u8],
        &PoolStateV1,
        &[AccountInfo<'info>],
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        VerifierDispatchClaimV1,
        u64,
    ) -> ProgramResult,
    S: FnOnce(&[u8]),
{
    let decoded = decode_withdrawal_instruction_v1(instruction_data)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = load_canonical_pool_state(program_id, pool)?;
    validate_spend_binding_v1(
        pool,
        &state,
        PoolV1TransitionKind::Withdrawal,
        decoded.envelope.transition_kind,
        &decoded.statement.pool,
        &decoded.statement.deployment_domain,
        decoded.statement.asset_id,
    )?;
    let layout = plan_spend_page_layout_v1(
        program_id,
        accounts,
        &state,
        decoded.envelope.anchor_sequence,
        1,
    )?;
    let expected_accounts = layout.suffix_start + 7 + 5;
    if accounts.len() != expected_accounts {
        return Err(if accounts.len() < expected_accounts {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    require_unique_accounts(accounts)?;
    let marker = &accounts[layout.suffix_start];
    let payer = &accounts[layout.suffix_start + 1];
    let system_program_account = &accounts[layout.suffix_start + 2];
    let registry_accounts = &accounts[layout.suffix_start + 3..layout.suffix_start + 5];
    let verifier_program = &accounts[layout.suffix_start + 5];
    let proof = &accounts[layout.suffix_start + 6];
    let token_accounts = &accounts[layout.suffix_start + 7..layout.suffix_start + 12];
    require_payer_and_system_program(payer, system_program_account)?;
    require_token_program_account(&token_accounts[4])?;

    let encoded_envelope = encode_historical_anchor_envelope_v1(&decoded.envelope)
        .map_err(|_| PoolV1ProgramError::InvalidHistoricalAnchorEnvelope)?;
    authenticate_historical_anchor_v1(
        program_id,
        pool,
        &accounts[layout.anchor_index],
        &encoded_envelope,
        HistoricalAnchorAuthorizationV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            verifier_profile: decoded.envelope.verifier_profile,
            verifier_release: decoded.envelope.verifier_release,
        },
    )?;
    validate_current_history(program_id, pool, &accounts[layout.current_index], &state)?;
    let planned_marker = plan_marker_from_envelope_v1(program_id, marker, &decoded.envelope)?;
    if let Some(next_index) = layout.next_index {
        let page_number = layout
            .next_page_number
            .ok_or(PoolV1ProgramError::StateHistoryMismatch)?;
        let expected = crate::pool_v1_root_page_address(program_id, pool.key, page_number).0;
        plan_fresh_program_pda(
            &accounts[next_index],
            program_id,
            &expected,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        )?;
    }
    let destination = Pubkey::new_from_array(decoded.statement.destination_token_account);
    let withdrawal_plan = plan_legacy_withdrawal_transfer_v1(
        program_id,
        pool.key,
        &state,
        token_accounts,
        &destination,
        decoded.statement.amount,
    )?;
    let transfer_infos = exact_withdrawal_transfer_account_infos_v1(token_accounts)?;
    let claim = derive_verifier_dispatch_claim_v1(verifier_program, proof, hash)?;
    verify(
        pool.key,
        &encoded_envelope,
        decoded.statement_payload,
        &state,
        registry_accounts,
        verifier_program,
        proof,
        claim,
        current_slot,
    )?;

    create_next_root_page_if_needed(
        runtime,
        program_id,
        accounts,
        layout,
        payer,
        system_program_account,
    )?;
    let state_accounts = state_accounts_for_append_v1(accounts, layout);
    let append = apply_authorized_append_after_v1(
        program_id,
        &state_accounts,
        AuthorizedAppendV1::One(decoded.statement.change_commitment),
        || {
            let replanned = plan_marker_from_envelope_v1(program_id, marker, &decoded.envelope)?;
            if replanned != planned_marker {
                return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
            }
            if replanned.preparation == NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned {
                let nullifier_bytes = replanned.marker.canonical_nullifier_encoding();
                let bump_seed = [replanned.address_bump];
                let seeds: &[&[u8]] = &[
                    POOL_V1_NULLIFIER_MARKER_SEED,
                    pool.key.as_ref(),
                    &nullifier_bytes,
                    &bump_seed,
                ];
                create_or_allocate_pda(
                    runtime,
                    payer,
                    marker,
                    system_program_account,
                    POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
                    program_id,
                    seeds,
                )?;
            }

            let bump_seed = [withdrawal_plan.authority_bump];
            let authority_seeds: &[&[u8]] =
                &[POOL_V1_VAULT_AUTHORITY_SEED, pool.key.as_ref(), &bump_seed];
            runtime.invoke_signed(
                &withdrawal_plan.instruction,
                &transfer_infos,
                &[authority_seeds],
            )?;
            validate_exact_withdrawal_delta_v1(token_accounts, &withdrawal_plan)?;

            let ready = plan_marker_from_envelope_v1(program_id, marker, &decoded.envelope)?;
            if ready.preparation != NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed
                || ready.encoded_marker != replanned.encoded_marker
            {
                return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
            }
            marker
                .try_borrow_mut_data()?
                .copy_from_slice(&ready.encoded_marker);
            Ok(())
        },
    )?;
    let receipt = encode_transition_receipt_v1(&TransitionReceiptV1 {
        transition_kind: PoolV1TransitionKind::Withdrawal,
        pool: pool.key.to_bytes(),
        nullifier: decoded.statement.nullifier,
        first_output: decoded.statement.change_commitment,
        second_output_or_destination: decoded.statement.destination_token_account,
        withdrawal_amount: decoded.statement.amount,
        first_leaf_index: append.first.leaf_index,
        second_leaf_index: 0,
        root_sequence: append.first.leaf_index + 1,
        root: append.first.root,
    })?;
    set_return_data(&receipt);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn dispatch_selected_verifier_v1<'info>(
    pool: &Pubkey,
    encoded_envelope: &[u8],
    statement_payload: &[u8],
    state: &PoolStateV1,
    registry_accounts: &[AccountInfo<'info>],
    verifier_program: &AccountInfo<'info>,
    proof: &AccountInfo<'info>,
    claim: VerifierDispatchClaimV1,
    current_slot: u64,
) -> ProgramResult {
    dispatch_authenticated_verifier_readonly_v1(
        pool,
        &state.identity.deployment_domain,
        &state.verifier_policy,
        registry_accounts,
        verifier_program,
        proof,
        encoded_envelope,
        statement_payload,
        claim,
        current_slot,
        solana_sha256,
    )?;
    Ok(())
}

/// Exact native Pool dispatcher. Return data is cleared at entry and again on
/// every error, so an accepted verifier's intermediate `ASVS` cannot escape a
/// later failed marker/tree/vault transition.
#[inline(never)]
pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    program::set_return_data(&[]);
    let magic = instruction_data
        .get(..4)
        .ok_or(ProgramError::InvalidInstructionData)?;
    let mut runtime = SolanaPoolCpiRuntimeV1;
    let result = if magic == POOL_V1_INITIALIZE_INSTRUCTION_MAGIC {
        process_initialize_with_runtime_v1(
            program_id,
            accounts,
            instruction_data,
            &mut runtime,
            program::set_return_data,
        )
    } else if magic == POOL_V1_DEPOSIT_INSTRUCTION_MAGIC {
        process_deposit_with_runtime_v1(program_id, accounts, instruction_data, &mut runtime)
    } else if magic == POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC {
        let slot = Clock::get()?.slot;
        process_private_transfer_with_runtime_v1(
            program_id,
            accounts,
            instruction_data,
            slot,
            solana_sha256,
            &mut runtime,
            dispatch_selected_verifier_v1,
            program::set_return_data,
        )
    } else if magic == POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC {
        let slot = Clock::get()?.slot;
        process_withdrawal_with_runtime_v1(
            program_id,
            accounts,
            instruction_data,
            slot,
            solana_sha256,
            &mut runtime,
            dispatch_selected_verifier_v1,
            program::set_return_data,
        )
    } else {
        Err(ProgramError::InvalidInstructionData)
    };
    if result.is_err() {
        program::set_return_data(&[]);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{
        pool_v1::{decode_pool_v1_nullifier_marker, HistoricalAnchorEnvelopeV1, VerifierPolicyV1},
        poseidon2::Digest,
    };
    use solana_program::clock::Epoch;
    use std::{cell::RefCell, vec};

    use crate::instruction::{
        encode_initialize_instruction_v1, encode_private_transfer_instruction_v1,
        encode_withdrawal_instruction_v1, PrivateTransferStatementV1, WithdrawalStatementV1,
    };
    use crate::state::PoolInitializationV1;

    struct NoCpi;

    impl PoolCpiRuntimeV1 for NoCpi {
        fn invoke<'info>(&mut self, _: &Instruction, _: &[AccountInfo<'info>]) -> ProgramResult {
            panic!("unexpected CPI")
        }

        fn invoke_signed<'info>(
            &mut self,
            _: &Instruction,
            _: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            panic!("unexpected signed CPI")
        }
    }

    struct WithdrawalCpi {
        called: bool,
        expected_amount: u64,
    }

    impl PoolCpiRuntimeV1 for WithdrawalCpi {
        fn invoke<'info>(&mut self, _: &Instruction, _: &[AccountInfo<'info>]) -> ProgramResult {
            panic!("unexpected unsigned CPI")
        }

        fn invoke_signed<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
            signer_seeds: &[&[&[u8]]],
        ) -> ProgramResult {
            assert_eq!(instruction.program_id, LEGACY_SPL_TOKEN_PROGRAM_ID);
            assert_eq!(instruction.data[0], 12);
            assert_eq!(
                u64::from_le_bytes(instruction.data[1..9].try_into().unwrap()),
                self.expected_amount
            );
            assert_eq!(infos.len(), 5);
            assert_eq!(signer_seeds.len(), 1);
            let vault_before = {
                let data = infos[0].try_borrow_data()?;
                u64::from_le_bytes(data[64..72].try_into().unwrap())
            };
            let destination_before = {
                let data = infos[2].try_borrow_data()?;
                u64::from_le_bytes(data[64..72].try_into().unwrap())
            };
            let vault_after = vault_before
                .checked_sub(self.expected_amount)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            let destination_after = destination_before
                .checked_add(self.expected_amount)
                .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
            infos[0].try_borrow_mut_data()?[64..72].copy_from_slice(&vault_after.to_le_bytes());
            infos[2].try_borrow_mut_data()?[64..72]
                .copy_from_slice(&destination_after.to_le_bytes());
            self.called = true;
            Ok(())
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 23 * index as u32))
    }

    fn policy() -> VerifierPolicyV1 {
        VerifierPolicyV1 {
            flags: 0,
            registry_program: [6u8; 32],
            registry_authority: [7u8; 32],
            policy_binding: [8u8; 32],
        }
    }

    fn initialization(mint: &Pubkey) -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(9),
            deployment_domain: [10u8; 32],
            verifier_policy: policy(),
        }
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    fn mint_data(decimals: u8) -> [u8; crate::LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES] {
        let mut data = [0u8; crate::LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
        data[44] = decimals;
        data[45] = 1;
        data
    }

    fn token_data(
        mint: &Pubkey,
        authority: &Pubkey,
        amount: u64,
    ) -> [u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES] {
        let mut data = [0u8; LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
        data[..32].copy_from_slice(mint.as_ref());
        data[32..64].copy_from_slice(authority.as_ref());
        data[64..72].copy_from_slice(&amount.to_le_bytes());
        data[108] = 1;
        data
    }

    fn proof_data(body: &[u8]) -> Vec<u8> {
        let mut data = vec![0u8; 40 + body.len()];
        data[..4].copy_from_slice(b"ASPU");
        data[4..8].copy_from_slice(&(body.len() as u32).to_le_bytes());
        data[40..].copy_from_slice(body);
        data
    }

    #[test]
    fn public_dispatch_rejects_short_and_unknown_instruction_headers() {
        let program_id = Pubkey::new_unique();
        assert_eq!(
            process_instruction(&program_id, &[], b"ASP"),
            Err(ProgramError::InvalidInstructionData)
        );
        assert_eq!(
            process_instruction(&program_id, &[], b"NOPE"),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn precreated_initialization_reaches_dispatch_without_cpi_and_emits_only_after_success() {
        let program_id = Pubkey::new_unique();
        let mint_key = Pubkey::new_unique();
        let pool_key = pool_v1_state_address(&program_id, &mint_key).0;
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let vault_key = pool_v1_vault_token_account_address(&program_id, &pool_key).0;
        let vault_authority = pool_v1_vault_authority_address(&program_id, &pool_key).0;
        let payer_key = Pubkey::new_unique();
        let token_program_key = LEGACY_SPL_TOKEN_PROGRAM_ID;
        let system_program_key = system_program::id();
        let native_loader_key = native_loader::id();
        let bpf_loader_key = bpf_loader::id();

        let mut payer_lamports = 10;
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        let mut mint_lamports = 1;
        let mut vault_lamports = 1;
        let mut token_program_lamports = 1;
        let mut system_program_lamports = 1;
        let mut payer_data = [];
        let mut pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut mint_data = mint_data(6);
        let mut vault_data = token_data(&mint_key, &vault_authority, 0);
        let mut token_program_data = [];
        let mut system_program_data = [];
        let instruction = encode_initialize_instruction_v1(&initialization(&mint_key)).unwrap();
        let returned = RefCell::new(Vec::new());
        {
            let accounts = [
                account(
                    &payer_key,
                    &system_program_key,
                    &mut payer_lamports,
                    &mut payer_data,
                    true,
                    true,
                    false,
                ),
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &page_key,
                    &program_id,
                    &mut page_lamports,
                    &mut page_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &mint_key,
                    &token_program_key,
                    &mut mint_lamports,
                    &mut mint_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &vault_key,
                    &token_program_key,
                    &mut vault_lamports,
                    &mut vault_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &token_program_key,
                    &bpf_loader_key,
                    &mut token_program_lamports,
                    &mut token_program_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &system_program_key,
                    &native_loader_key,
                    &mut system_program_lamports,
                    &mut system_program_data,
                    false,
                    false,
                    true,
                ),
            ];
            process_initialize_with_runtime_v1(
                &program_id,
                &accounts,
                &instruction,
                &mut NoCpi,
                |data| returned.borrow_mut().extend_from_slice(data),
            )
            .unwrap();
        }
        assert_eq!(returned.borrow().len(), 104);
        assert_eq!(&returned.borrow()[..4], b"ASIR");
        assert_eq!(
            PoolStateV1::decode(&pool_data, &pool_key)
                .unwrap()
                .current_root_sequence(),
            0
        );
        assert_ne!(&page_data[..4], &[0u8; 4]);
    }

    #[test]
    fn private_transfer_failure_alias_rejection_then_success_is_exactly_one_to_two() {
        let program_id = Pubkey::new_unique();
        let mint_key = Pubkey::new_unique();
        let pool_key = pool_v1_state_address(&program_id, &mint_key).0;
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let mut pool_data = PoolStateV1::genesis(&pool_key, initialization(&mint_key))
            .unwrap()
            .encode()
            .unwrap();
        let state = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        crate::history::write_new_page_unchecked(
            &mut page_data,
            &pool_key,
            0,
            0,
            &[state.tree.root],
        );
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: pool_key.to_bytes(),
            deployment_domain: state.identity.deployment_domain,
            anchor_sequence: 0,
            anchor_root: state.tree.root,
            nullifier: digest(100),
            verifier_profile: [11u8; 32],
            verifier_release: [12u8; 32],
        };
        let statement = PrivateTransferStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: 0,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: state.identity.asset_id,
            recipient_commitment: digest(200),
            change_commitment: digest(300),
        };
        let instruction = encode_private_transfer_instruction_v1(&envelope, &statement).unwrap();
        let marker_key = crate::pool_v1_nullifier_marker_address(
            &program_id,
            &pool_key,
            &PoolV1NullifierMarkerV1::from_historical_anchor(&envelope)
                .canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let payer_key = Pubkey::new_unique();
        let registry_key = Pubkey::new_unique();
        let entry_key = Pubkey::new_unique();
        let verifier_key = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let system_key = system_program::id();
        let native_loader_key = native_loader::id();
        let bpf_loader_key = bpf_loader::id();
        let registry_owner = Pubkey::new_unique();

        let mut marker_data = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let mut payer_data = [];
        let mut system_data = [];
        let mut registry_data = [];
        let mut entry_data = [];
        let mut verifier_data = [];
        let mut proof_data = proof_data(b"proof");
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        let mut marker_lamports = 1;
        let mut payer_lamports = 10;
        let mut system_lamports = 1;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let mut verifier_lamports = 1;
        let mut proof_lamports = 1;
        let before_pool = pool_data;
        let before_page = page_data.clone();
        let before_marker = marker_data;
        let returned = RefCell::new(Vec::new());
        {
            let accounts = [
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &page_key,
                    &program_id,
                    &mut page_lamports,
                    &mut page_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &marker_key,
                    &program_id,
                    &mut marker_lamports,
                    &mut marker_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &payer_key,
                    &system_key,
                    &mut payer_lamports,
                    &mut payer_data,
                    true,
                    true,
                    false,
                ),
                account(
                    &system_key,
                    &native_loader_key,
                    &mut system_lamports,
                    &mut system_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &registry_key,
                    &registry_owner,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &entry_key,
                    &registry_owner,
                    &mut entry_lamports,
                    &mut entry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &bpf_loader_key,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                    false,
                ),
            ];
            assert_eq!(
                process_private_transfer_with_runtime_v1(
                    &program_id,
                    &accounts,
                    &instruction,
                    50,
                    solana_sha256,
                    &mut NoCpi,
                    |_, _, _, _, _, _, _, _, _| Err(ProgramError::Custom(0xDEAD)),
                    |data| returned.borrow_mut().extend_from_slice(data),
                ),
                Err(ProgramError::Custom(0xDEAD))
            );
        }
        assert_eq!(pool_data, before_pool);
        assert_eq!(page_data, before_page);
        assert_eq!(marker_data, before_marker);
        assert!(returned.borrow().is_empty());

        // Duplicate role keys fail before the verifier closure is reached.
        let mut alias_entry_data = [];
        let mut alias_entry_lamports = 1;
        let verifier_called = RefCell::new(false);
        {
            let accounts = [
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &page_key,
                    &program_id,
                    &mut page_lamports,
                    &mut page_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &marker_key,
                    &program_id,
                    &mut marker_lamports,
                    &mut marker_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &payer_key,
                    &system_key,
                    &mut payer_lamports,
                    &mut payer_data,
                    true,
                    true,
                    false,
                ),
                account(
                    &system_key,
                    &native_loader_key,
                    &mut system_lamports,
                    &mut system_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &registry_key,
                    &registry_owner,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &registry_key,
                    &registry_owner,
                    &mut alias_entry_lamports,
                    &mut alias_entry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &bpf_loader_key,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                    false,
                ),
            ];
            assert_eq!(
                process_private_transfer_with_runtime_v1(
                    &program_id,
                    &accounts,
                    &instruction,
                    50,
                    solana_sha256,
                    &mut NoCpi,
                    |_, _, _, _, _, _, _, _, _| {
                        *verifier_called.borrow_mut() = true;
                        Ok(())
                    },
                    |_| {},
                ),
                Err(ProgramError::InvalidArgument)
            );
        }
        assert!(!*verifier_called.borrow());
        assert_eq!(pool_data, before_pool);
        assert_eq!(page_data, before_page);
        assert_eq!(marker_data, before_marker);

        // The same exact account layout succeeds only after verifier
        // acceptance, consumes the marker, appends two ordered commitments,
        // and emits the outer Pool receipt rather than verifier return data.
        let success_returned = RefCell::new(Vec::new());
        {
            let accounts = [
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &page_key,
                    &program_id,
                    &mut page_lamports,
                    &mut page_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &marker_key,
                    &program_id,
                    &mut marker_lamports,
                    &mut marker_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &payer_key,
                    &system_key,
                    &mut payer_lamports,
                    &mut payer_data,
                    true,
                    true,
                    false,
                ),
                account(
                    &system_key,
                    &native_loader_key,
                    &mut system_lamports,
                    &mut system_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &registry_key,
                    &registry_owner,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &entry_key,
                    &registry_owner,
                    &mut entry_lamports,
                    &mut entry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &bpf_loader_key,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                    false,
                ),
            ];
            process_private_transfer_with_runtime_v1(
                &program_id,
                &accounts,
                &instruction,
                50,
                solana_sha256,
                &mut NoCpi,
                |_, encoded_envelope, payload, _, _, _, _, _, _| {
                    assert_eq!(encoded_envelope.len(), 208);
                    assert_eq!(payload.len(), 216);
                    Ok(())
                },
                |data| success_returned.borrow_mut().extend_from_slice(data),
            )
            .unwrap();
        }
        assert_eq!(
            PoolStateV1::decode(&pool_data, &pool_key)
                .unwrap()
                .current_root_sequence(),
            2
        );
        assert_eq!(
            decode_pool_v1_nullifier_marker(&marker_data)
                .unwrap()
                .nullifier,
            envelope.nullifier
        );
        assert_eq!(success_returned.borrow().len(), 200);
        assert_eq!(&success_returned.borrow()[..4], b"ASTR");
    }

    #[test]
    fn accepted_withdrawal_updates_exact_balances_marker_tree_and_success_receipt() {
        let program_id = Pubkey::new_unique();
        let mint_key = Pubkey::new_unique();
        let pool_key = pool_v1_state_address(&program_id, &mint_key).0;
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let vault_key = pool_v1_vault_token_account_address(&program_id, &pool_key).0;
        let vault_authority_key = pool_v1_vault_authority_address(&program_id, &pool_key).0;
        let destination_key = Pubkey::new_unique();
        let mut pool_data = PoolStateV1::genesis(&pool_key, initialization(&mint_key))
            .unwrap()
            .encode()
            .unwrap();
        let state = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        crate::history::write_new_page_unchecked(
            &mut page_data,
            &pool_key,
            0,
            0,
            &[state.tree.root],
        );
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: pool_key.to_bytes(),
            deployment_domain: state.identity.deployment_domain,
            anchor_sequence: 0,
            anchor_root: state.tree.root,
            nullifier: digest(400),
            verifier_profile: [13u8; 32],
            verifier_release: [14u8; 32],
        };
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: 0,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: state.identity.asset_id,
            amount: 25,
            destination_token_account: destination_key.to_bytes(),
            change_commitment: digest(500),
        };
        let instruction = encode_withdrawal_instruction_v1(&envelope, &statement).unwrap();
        let marker_key = crate::pool_v1_nullifier_marker_address(
            &program_id,
            &pool_key,
            &PoolV1NullifierMarkerV1::from_historical_anchor(&envelope)
                .canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let payer_key = Pubkey::new_unique();
        let registry_key = Pubkey::new_unique();
        let entry_key = Pubkey::new_unique();
        let verifier_key = Pubkey::new_unique();
        let proof_key = Pubkey::new_unique();
        let system_key = system_program::id();
        let native_loader_key = native_loader::id();
        let bpf_loader_key = bpf_loader::id();
        let registry_owner = Pubkey::new_unique();
        let token_key = LEGACY_SPL_TOKEN_PROGRAM_ID;

        let mut marker_data = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let mut payer_data = [];
        let mut system_data = [];
        let mut registry_data = [];
        let mut entry_data = [];
        let mut verifier_data = [];
        let mut proof_data = proof_data(b"withdraw-proof");
        let mut mint_data = mint_data(6);
        let mut vault_data = token_data(&mint_key, &vault_authority_key, 100);
        let destination_authority = Pubkey::new_unique();
        let mut destination_data = token_data(&mint_key, &destination_authority, 10);
        let mut vault_authority_data = [];
        let mut token_program_data = [];
        let [mut pool_lamports, mut page_lamports, mut marker_lamports, mut payer_lamports, mut system_lamports, mut registry_lamports, mut entry_lamports, mut verifier_lamports, mut proof_lamports, mut mint_lamports, mut vault_lamports, mut destination_lamports, mut vault_authority_lamports, mut token_program_lamports] =
            [1, 1, 1, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
        macro_rules! withdrawal_accounts {
            () => {
                [
                    account(
                        &pool_key,
                        &program_id,
                        &mut pool_lamports,
                        &mut pool_data,
                        false,
                        true,
                        false,
                    ),
                    account(
                        &page_key,
                        &program_id,
                        &mut page_lamports,
                        &mut page_data,
                        false,
                        true,
                        false,
                    ),
                    account(
                        &marker_key,
                        &program_id,
                        &mut marker_lamports,
                        &mut marker_data,
                        false,
                        true,
                        false,
                    ),
                    account(
                        &payer_key,
                        &system_key,
                        &mut payer_lamports,
                        &mut payer_data,
                        true,
                        true,
                        false,
                    ),
                    account(
                        &system_key,
                        &native_loader_key,
                        &mut system_lamports,
                        &mut system_data,
                        false,
                        false,
                        true,
                    ),
                    account(
                        &registry_key,
                        &registry_owner,
                        &mut registry_lamports,
                        &mut registry_data,
                        false,
                        false,
                        false,
                    ),
                    account(
                        &entry_key,
                        &registry_owner,
                        &mut entry_lamports,
                        &mut entry_data,
                        false,
                        false,
                        false,
                    ),
                    account(
                        &verifier_key,
                        &bpf_loader_key,
                        &mut verifier_lamports,
                        &mut verifier_data,
                        false,
                        false,
                        true,
                    ),
                    account(
                        &proof_key,
                        &verifier_key,
                        &mut proof_lamports,
                        &mut proof_data,
                        false,
                        false,
                        false,
                    ),
                    account(
                        &mint_key,
                        &token_key,
                        &mut mint_lamports,
                        &mut mint_data,
                        false,
                        false,
                        false,
                    ),
                    account(
                        &vault_key,
                        &token_key,
                        &mut vault_lamports,
                        &mut vault_data,
                        false,
                        true,
                        false,
                    ),
                    account(
                        &destination_key,
                        &token_key,
                        &mut destination_lamports,
                        &mut destination_data,
                        false,
                        true,
                        false,
                    ),
                    account(
                        &vault_authority_key,
                        &system_key,
                        &mut vault_authority_lamports,
                        &mut vault_authority_data,
                        false,
                        false,
                        false,
                    ),
                    account(
                        &token_key,
                        &bpf_loader_key,
                        &mut token_program_lamports,
                        &mut token_program_data,
                        false,
                        false,
                        true,
                    ),
                ]
            };
        }

        let before_pool = pool_data;
        let before_page = page_data.clone();
        let before_marker = marker_data;
        let before_vault = vault_data;
        let before_destination = destination_data;
        let failed_return = RefCell::new(Vec::new());
        {
            let accounts = withdrawal_accounts!();
            assert_eq!(
                process_withdrawal_with_runtime_v1(
                    &program_id,
                    &accounts,
                    &instruction,
                    50,
                    solana_sha256,
                    &mut NoCpi,
                    |_, _, _, _, _, _, _, _, _| Err(ProgramError::Custom(0xBEEF)),
                    |data| failed_return.borrow_mut().extend_from_slice(data),
                ),
                Err(ProgramError::Custom(0xBEEF))
            );
        }
        assert_eq!(pool_data, before_pool);
        assert_eq!(page_data, before_page);
        assert_eq!(marker_data, before_marker);
        assert_eq!(vault_data, before_vault);
        assert_eq!(destination_data, before_destination);
        assert!(failed_return.borrow().is_empty());

        let returned = RefCell::new(Vec::new());
        let verifier_called = RefCell::new(false);
        let mut runtime = WithdrawalCpi {
            called: false,
            expected_amount: 25,
        };
        {
            let accounts = [
                account(
                    &pool_key,
                    &program_id,
                    &mut pool_lamports,
                    &mut pool_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &page_key,
                    &program_id,
                    &mut page_lamports,
                    &mut page_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &marker_key,
                    &program_id,
                    &mut marker_lamports,
                    &mut marker_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &payer_key,
                    &system_key,
                    &mut payer_lamports,
                    &mut payer_data,
                    true,
                    true,
                    false,
                ),
                account(
                    &system_key,
                    &native_loader_key,
                    &mut system_lamports,
                    &mut system_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &registry_key,
                    &registry_owner,
                    &mut registry_lamports,
                    &mut registry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &entry_key,
                    &registry_owner,
                    &mut entry_lamports,
                    &mut entry_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &verifier_key,
                    &bpf_loader_key,
                    &mut verifier_lamports,
                    &mut verifier_data,
                    false,
                    false,
                    true,
                ),
                account(
                    &proof_key,
                    &verifier_key,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &mint_key,
                    &token_key,
                    &mut mint_lamports,
                    &mut mint_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &vault_key,
                    &token_key,
                    &mut vault_lamports,
                    &mut vault_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &destination_key,
                    &token_key,
                    &mut destination_lamports,
                    &mut destination_data,
                    false,
                    true,
                    false,
                ),
                account(
                    &vault_authority_key,
                    &system_key,
                    &mut vault_authority_lamports,
                    &mut vault_authority_data,
                    false,
                    false,
                    false,
                ),
                account(
                    &token_key,
                    &bpf_loader_key,
                    &mut token_program_lamports,
                    &mut token_program_data,
                    false,
                    false,
                    true,
                ),
            ];
            process_withdrawal_with_runtime_v1(
                &program_id,
                &accounts,
                &instruction,
                50,
                solana_sha256,
                &mut runtime,
                |_, encoded_envelope, payload, _, _, _, _, _, _| {
                    *verifier_called.borrow_mut() = true;
                    assert_eq!(encoded_envelope.len(), 208);
                    assert_eq!(payload.len(), 216);
                    Ok(())
                },
                |data| returned.borrow_mut().extend_from_slice(data),
            )
            .unwrap();
        }
        assert!(runtime.called);
        assert!(*verifier_called.borrow());
        assert_eq!(
            u64::from_le_bytes(vault_data[64..72].try_into().unwrap()),
            75
        );
        assert_eq!(
            u64::from_le_bytes(destination_data[64..72].try_into().unwrap()),
            35
        );
        assert_eq!(
            PoolStateV1::decode(&pool_data, &pool_key)
                .unwrap()
                .current_root_sequence(),
            1
        );
        assert_eq!(
            decode_pool_v1_nullifier_marker(&marker_data)
                .unwrap()
                .nullifier,
            envelope.nullifier
        );
        assert_eq!(returned.borrow().len(), 200);
        assert_eq!(&returned.borrow()[..4], b"ASTR");
    }
}
