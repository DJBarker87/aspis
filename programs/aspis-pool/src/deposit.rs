//! Vault-backed Pool V1 deposit kernel.
//!
//! The native entrypoint reaches this crate-private kernel only through the
//! exact `ASDI` decoder. It validates one exact legacy SPL Token transfer,
//! computes the frozen note commitment from public fields, then appends exactly
//! one leaf/root. The encrypted payload is bounded opaque delivery data and is
//! never an input to the commitment.

extern crate alloc;

use alloc::boxed::Box;

use aspis_core::field::P;
use aspis_statement::{
    pool_v1::{
        pool_v1_note_commitment, DepositEventV1, DepositReceiptV1,
        POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES,
    },
    poseidon2::Digest,
    VALUE_LIMIT,
};
use solana_program::{
    account_info::AccountInfo, instruction::Instruction, program, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::{
    error::PoolV1ProgramError,
    history::require_program_account,
    state::{pool_v1_state_address, CanonicalPoolStateV1, PoolStateV1},
    transition::{
        apply_authorized_append_after_prevalidated_v1, apply_authorized_append_after_v1,
        AuthorizedAppendReceiptV1, AuthorizedAppendV1,
    },
    vault::{
        exact_transfer_account_infos_v1, plan_legacy_deposit_transfer_v1,
        validate_exact_deposit_delta_v1, LegacyDepositTransferPlanV1,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositRequestV1<'a> {
    pub owner_key: Digest,
    pub amount: u32,
    pub salt: Digest,
    pub encrypted_note_payload: &'a [u8],
}

fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

fn validate_request(request: &DepositRequestV1<'_>) -> Result<(), ProgramError> {
    // The public instruction field is exactly u32, while the frozen spend
    // relation additionally requires the 30-bit VALUE_LIMIT range.
    if request.amount == 0 || request.amount >= VALUE_LIMIT {
        return Err(PoolV1ProgramError::InvalidDepositAmount.into());
    }
    if request.encrypted_note_payload.len() > POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES {
        return Err(PoolV1ProgramError::InvalidEncryptedNotePayload.into());
    }
    if !digest_is_canonical(&request.owner_key) || !digest_is_canonical(&request.salt) {
        return Err(PoolV1ProgramError::NonCanonicalLeaf.into());
    }
    Ok(())
}

fn load_pool_state_for_deposit(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo],
) -> Result<Box<PoolStateV1>, ProgramError> {
    let pool_account = state_accounts
        .first()
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    require_program_account(pool_account, program_id, true)?;
    let state = {
        let data = pool_account.try_borrow_data()?;
        PoolStateV1::decode_boxed(&data, pool_account.key)?
    };
    let asset_mint = Pubkey::new_from_array(state.identity.asset_mint);
    if pool_account.key != &pool_v1_state_address(program_id, &asset_mint).0 {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    Ok(state)
}

fn require_disjoint_account_groups(
    state_accounts: &[AccountInfo],
    token_accounts: &[AccountInfo],
) -> Result<(), ProgramError> {
    for state_account in state_accounts {
        for token_account in token_accounts {
            if state_account.key == token_account.key {
                return Err(ProgramError::InvalidArgument);
            }
        }
    }
    Ok(())
}

struct PreparedDepositV1<'info> {
    transfer_plan: LegacyDepositTransferPlanV1,
    transfer_infos: [AccountInfo<'info>; 5],
    note_commitment: Digest,
}

fn prepare_deposit_after_state_validation_v1<'info>(
    program_id: &Pubkey,
    state: &PoolStateV1,
    token_accounts: &[AccountInfo<'info>],
    request: &DepositRequestV1<'_>,
) -> Result<PreparedDepositV1<'info>, ProgramError> {
    let pool = Pubkey::new_from_array(state.identity.pool);
    let transfer_plan =
        plan_legacy_deposit_transfer_v1(program_id, &pool, state, token_accounts, request.amount)?;
    let note_commitment = pool_v1_note_commitment(
        &request.owner_key,
        request.amount,
        state.identity.asset_id,
        &request.salt,
    );
    let transfer_infos = exact_transfer_account_infos_v1(token_accounts)?;
    Ok(PreparedDepositV1 {
        transfer_plan,
        transfer_infos,
        note_commitment,
    })
}

fn finish_deposit_event_v1<'payload>(
    state: &PoolStateV1,
    request: DepositRequestV1<'payload>,
    prepared: &PreparedDepositV1<'_>,
    append: AuthorizedAppendReceiptV1,
) -> DepositEventV1<'payload> {
    let receipt = DepositReceiptV1 {
        pool: state.identity.pool,
        asset_mint: state.identity.asset_mint,
        source_token_account: prepared.transfer_plan.source.to_bytes(),
        vault_token_account: prepared.transfer_plan.vault.to_bytes(),
        amount: request.amount,
        encrypted_note_payload_bytes: request.encrypted_note_payload.len() as u16,
        note_commitment: prepared.note_commitment,
        leaf_index: append.first.leaf_index,
        root_sequence: append.first.leaf_index + 1,
        root: append.first.root,
    };
    DepositEventV1 {
        receipt,
        encrypted_note_payload: request.encrypted_note_payload,
    }
}

#[inline(never)]
fn apply_vault_backed_deposit_with_transfer_v1<'payload, 'info, F>(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo<'info>],
    token_accounts: &[AccountInfo<'info>],
    request: DepositRequestV1<'payload>,
    transfer: F,
) -> Result<DepositEventV1<'payload>, ProgramError>
where
    F: FnOnce(&Instruction, &[AccountInfo<'info>]) -> Result<(), ProgramError>,
{
    validate_request(&request)?;
    require_disjoint_account_groups(state_accounts, token_accounts)?;
    let state = load_pool_state_for_deposit(program_id, state_accounts)?;
    let prepared =
        prepare_deposit_after_state_validation_v1(program_id, &state, token_accounts, &request)?;

    // The transition kernel completes all tree/history validation, planning
    // and mutable Pool borrow acquisition before calling this closure. The
    // exact transfer and post-CPI delta check therefore precede the first Pool
    // state write. Returning Err relies on Solana transaction rollback for any
    // successful CPI effects; CPI/runtime atomicity remains an external gate.
    let append = apply_authorized_append_after_v1(
        program_id,
        state_accounts,
        AuthorizedAppendV1::One(prepared.note_commitment),
        || {
            transfer(
                &prepared.transfer_plan.instruction,
                &prepared.transfer_infos,
            )?;
            validate_exact_deposit_delta_v1(token_accounts, &prepared.transfer_plan)
        },
    )?;
    Ok(finish_deposit_event_v1(&state, request, &prepared, append))
}

#[inline(never)]
fn apply_prevalidated_vault_backed_deposit_with_transfer_v1<'payload, 'info, F>(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo<'info>],
    token_accounts: &[AccountInfo<'info>],
    state: &CanonicalPoolStateV1,
    request: DepositRequestV1<'payload>,
    transfer: F,
) -> Result<DepositEventV1<'payload>, ProgramError>
where
    F: FnOnce(&Instruction, &[AccountInfo<'info>]) -> Result<(), ProgramError>,
{
    validate_request(&request)?;
    require_disjoint_account_groups(state_accounts, token_accounts)?;
    let pool_account = state_accounts
        .first()
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    state.require_same_writable_account(program_id, pool_account)?;
    let prepared = prepare_deposit_after_state_validation_v1(
        program_id,
        state.as_state(),
        token_accounts,
        &request,
    )?;
    let append = apply_authorized_append_after_prevalidated_v1(
        program_id,
        state_accounts,
        state,
        AuthorizedAppendV1::One(prepared.note_commitment),
        || {
            transfer(
                &prepared.transfer_plan.instruction,
                &prepared.transfer_infos,
            )?;
            validate_exact_deposit_delta_v1(token_accounts, &prepared.transfer_plan)
        },
    )?;
    Ok(finish_deposit_event_v1(
        state.as_state(),
        request,
        &prepared,
        append,
    ))
}

/// Apply one vault-backed deposit through the legacy SPL Token program.
///
/// Exact account groups are:
///
/// - state: `[pool_state, current_root_page]`, plus the zeroed next page only
///   when the one-leaf append rolls over;
/// - token: `[mint, source, source_authority, vault, token_program]`.
///
/// There is intentionally no public raw-append function or instruction.
#[inline(never)]
pub fn apply_vault_backed_deposit_v1<'payload, 'info>(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo<'info>],
    token_accounts: &[AccountInfo<'info>],
    request: DepositRequestV1<'payload>,
) -> Result<DepositEventV1<'payload>, ProgramError> {
    apply_vault_backed_deposit_with_transfer_v1(
        program_id,
        state_accounts,
        token_accounts,
        request,
        program::invoke,
    )
}

/// Processor-only path carrying the one canonical decoded Pool state through
/// deposit authorization and persistence. Standalone callers keep using
/// `apply_vault_backed_deposit_v1`, which performs its own canonical decode.
#[inline(never)]
pub(crate) fn apply_prevalidated_vault_backed_deposit_v1<'payload, 'info>(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo<'info>],
    token_accounts: &[AccountInfo<'info>],
    state: &CanonicalPoolStateV1,
    request: DepositRequestV1<'payload>,
) -> Result<DepositEventV1<'payload>, ProgramError> {
    apply_prevalidated_vault_backed_deposit_with_transfer_v1(
        program_id,
        state_accounts,
        token_accounts,
        state,
        request,
        program::invoke,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        decode_deposit_receipt_v1, encode_deposit_receipt_v1, pool_v1_note_commitment,
        validate_deposit_event_v1, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    };
    use solana_program::{clock::Epoch, instruction::AccountMeta};
    use std::{cell::Cell, vec};

    use crate::{
        history::{read_retained_root, validate_root_page_bytes},
        state::{PoolInitializationV1, POOL_V1_STATE_ACCOUNT_BYTES},
        transition::initialize_pool_accounts_v1,
        vault::{
            pool_v1_vault_authority_address, pool_v1_vault_token_account_address,
            write_token_amount_for_test, LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
            LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_PROGRAM_ID,
        },
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 31 * index as u32))
    }

    fn policy() -> aspis_statement::pool_v1::VerifierPolicyV1 {
        aspis_statement::pool_v1::VerifierPolicyV1 {
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
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
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

    fn mint_data(decimals: u8) -> [u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES] {
        let mut data = [0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
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

    #[test]
    fn backed_deposit_transfers_exact_u32_then_appends_one_note_and_root() {
        let program_id = Pubkey::new_unique();
        let mint_key = Pubkey::new_unique();
        let pool_key = pool_v1_state_address(&program_id, &mint_key).0;
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let vault_key = pool_v1_vault_token_account_address(&program_id, &pool_key).0;
        let vault_authority = pool_v1_vault_authority_address(&program_id, &pool_key).0;
        let source_key = Pubkey::new_unique();
        let source_authority_key = Pubkey::new_unique();
        let token_program_key = LEGACY_SPL_TOKEN_PROGRAM_ID;
        let loader_owner = Pubkey::new_unique();

        let mut pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        {
            let pool = account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
                false,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut page_lamports,
                &mut page_data,
                false,
                true,
                false,
            );
            initialize_pool_accounts_v1(&program_id, &[pool, page], initialization(&mint_key))
                .unwrap();
        }
        let pool_before = pool_data;
        let page_before = page_data.clone();

        let mut mint_data = mint_data(6);
        let mut source_data = token_data(&mint_key, &source_authority_key, 1_000);
        let mut vault_data = token_data(&mint_key, &vault_authority, 40);
        let mut authority_data = [];
        let mut token_program_data = [];
        let mut mint_lamports = 1;
        let mut source_lamports = 1;
        let mut authority_lamports = 1;
        let mut vault_lamports = 1;
        let mut token_program_lamports = 1;
        let payload = [0xA5u8; 37];
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(100),
            encrypted_note_payload: &payload,
        };
        let transfer_called = Cell::new(false);
        let event = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
                false,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut page_lamports,
                &mut page_data,
                false,
                true,
                false,
            );
            let mint = account(
                &mint_key,
                &token_program_key,
                &mut mint_lamports,
                &mut mint_data,
                false,
                false,
                false,
            );
            let source = account(
                &source_key,
                &token_program_key,
                &mut source_lamports,
                &mut source_data,
                false,
                true,
                false,
            );
            let authority = account(
                &source_authority_key,
                &loader_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
                false,
            );
            let vault = account(
                &vault_key,
                &token_program_key,
                &mut vault_lamports,
                &mut vault_data,
                false,
                true,
                false,
            );
            let token_program = account(
                &token_program_key,
                &loader_owner,
                &mut token_program_lamports,
                &mut token_program_data,
                false,
                false,
                true,
            );
            apply_vault_backed_deposit_with_transfer_v1(
                &program_id,
                &[pool.clone(), page.clone()],
                &[
                    mint,
                    source.clone(),
                    authority,
                    vault.clone(),
                    token_program,
                ],
                request,
                |instruction, infos| {
                    transfer_called.set(true);
                    assert!(pool.try_borrow_data().is_err());
                    assert!(page.try_borrow_data().is_err());
                    assert_eq!(instruction.program_id, LEGACY_SPL_TOKEN_PROGRAM_ID);
                    assert_eq!(
                        instruction.accounts,
                        vec![
                            AccountMeta::new(source_key, false),
                            AccountMeta::new_readonly(mint_key, false),
                            AccountMeta::new(vault_key, false),
                            AccountMeta::new_readonly(source_authority_key, true),
                        ]
                    );
                    let mut expected_data = vec![12];
                    expected_data.extend_from_slice(&77u64.to_le_bytes());
                    expected_data.push(6);
                    assert_eq!(instruction.data, expected_data);
                    assert_eq!(infos.len(), 5);
                    assert_eq!(infos[0].key, &source_key);
                    assert_eq!(infos[2].key, &vault_key);
                    write_token_amount_for_test(&infos[0], 923)?;
                    write_token_amount_for_test(&infos[2], 117)?;
                    Ok(())
                },
            )
            .unwrap()
        };

        assert!(transfer_called.get());
        assert_ne!(pool_data, pool_before);
        assert_ne!(page_data, page_before);
        assert_eq!(
            u64::from_le_bytes(source_data[64..72].try_into().unwrap()),
            923
        );
        assert_eq!(
            u64::from_le_bytes(vault_data[64..72].try_into().unwrap()),
            117
        );
        assert_eq!(event.encrypted_note_payload, payload);
        assert_eq!(event.receipt.amount, 77);
        assert_eq!(event.receipt.leaf_index, 0);
        assert_eq!(event.receipt.root_sequence, 1);
        assert_eq!(
            event.receipt.note_commitment,
            pool_v1_note_commitment(&request.owner_key, 77, M31(4), &request.salt)
        );
        assert_eq!(validate_deposit_event_v1(&event), Ok(()));
        let receipt_bytes = encode_deposit_receipt_v1(&event.receipt).unwrap();
        assert_eq!(decode_deposit_receipt_v1(&receipt_bytes), Ok(event.receipt));

        let state = PoolStateV1::decode(&pool_data, &pool_key).unwrap();
        assert_eq!(state.tree.next_leaf_index, 1);
        assert_eq!(state.tree.root, event.receipt.root);
        let header = validate_root_page_bytes(&page_data, &pool_key, 0).unwrap();
        assert_eq!(header.filled, 2);
        assert_eq!(
            read_retained_root(&page_data, header, 1).unwrap(),
            event.receipt.root
        );
    }

    #[test]
    fn prevalidated_deposit_is_byte_exact_to_standalone_kernel() {
        let program_id = Pubkey::new_unique();
        let mint_key = Pubkey::new_unique();
        let pool_key = pool_v1_state_address(&program_id, &mint_key).0;
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let vault_key = pool_v1_vault_token_account_address(&program_id, &pool_key).0;
        let vault_authority = pool_v1_vault_authority_address(&program_id, &pool_key).0;
        let source_key = Pubkey::new_unique();
        let source_authority_key = Pubkey::new_unique();
        let loader_owner = Pubkey::new_unique();

        let mut initial_pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut initial_page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut initial_pool_lamports = 1;
        let mut initial_page_lamports = 1;
        {
            let pool = account(
                &pool_key,
                &program_id,
                &mut initial_pool_lamports,
                &mut initial_pool_data,
                false,
                true,
                false,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut initial_page_lamports,
                &mut initial_page_data,
                false,
                true,
                false,
            );
            initialize_pool_accounts_v1(&program_id, &[pool, page], initialization(&mint_key))
                .unwrap();
        }
        let initial_mint_data = mint_data(6);
        let initial_source_data = token_data(&mint_key, &source_authority_key, 1_000);
        let initial_vault_data = token_data(&mint_key, &vault_authority, 40);
        let payload = [0x5Au8; 19];
        let request = DepositRequestV1 {
            owner_key: digest(700),
            amount: 77,
            salt: digest(800),
            encrypted_note_payload: &payload,
        };

        let mut standalone_pool_data = initial_pool_data;
        let mut standalone_page_data = initial_page_data.clone();
        let mut standalone_mint_data = initial_mint_data;
        let mut standalone_source_data = initial_source_data;
        let mut standalone_vault_data = initial_vault_data;
        let mut standalone_authority_data = [];
        let mut standalone_token_program_data = [];
        let mut standalone_pool_lamports = 1;
        let mut standalone_page_lamports = 1;
        let mut standalone_mint_lamports = 1;
        let mut standalone_source_lamports = 1;
        let mut standalone_authority_lamports = 1;
        let mut standalone_vault_lamports = 1;
        let mut standalone_token_program_lamports = 1;
        let standalone_event = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut standalone_pool_lamports,
                &mut standalone_pool_data,
                false,
                true,
                false,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut standalone_page_lamports,
                &mut standalone_page_data,
                false,
                true,
                false,
            );
            let mint = account(
                &mint_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut standalone_mint_lamports,
                &mut standalone_mint_data,
                false,
                false,
                false,
            );
            let source = account(
                &source_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut standalone_source_lamports,
                &mut standalone_source_data,
                false,
                true,
                false,
            );
            let authority = account(
                &source_authority_key,
                &loader_owner,
                &mut standalone_authority_lamports,
                &mut standalone_authority_data,
                true,
                false,
                false,
            );
            let vault = account(
                &vault_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut standalone_vault_lamports,
                &mut standalone_vault_data,
                false,
                true,
                false,
            );
            let token_program = account(
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &loader_owner,
                &mut standalone_token_program_lamports,
                &mut standalone_token_program_data,
                false,
                false,
                true,
            );
            apply_vault_backed_deposit_with_transfer_v1(
                &program_id,
                &[pool, page],
                &[mint, source, authority, vault, token_program],
                request,
                |_, infos| {
                    write_token_amount_for_test(&infos[0], 923)?;
                    write_token_amount_for_test(&infos[2], 117)?;
                    Ok(())
                },
            )
            .unwrap()
        };

        let mut prevalidated_pool_data = initial_pool_data;
        let mut prevalidated_page_data = initial_page_data;
        let mut prevalidated_mint_data = initial_mint_data;
        let mut prevalidated_source_data = initial_source_data;
        let mut prevalidated_vault_data = initial_vault_data;
        let mut prevalidated_authority_data = [];
        let mut prevalidated_token_program_data = [];
        let mut prevalidated_pool_lamports = 1;
        let mut prevalidated_page_lamports = 1;
        let mut prevalidated_mint_lamports = 1;
        let mut prevalidated_source_lamports = 1;
        let mut prevalidated_authority_lamports = 1;
        let mut prevalidated_vault_lamports = 1;
        let mut prevalidated_token_program_lamports = 1;
        let canonical = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut prevalidated_pool_lamports,
                &mut prevalidated_pool_data,
                false,
                true,
                false,
            );
            CanonicalPoolStateV1::decode_account(&program_id, &pool).unwrap()
        };
        let prevalidated_event = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut prevalidated_pool_lamports,
                &mut prevalidated_pool_data,
                false,
                true,
                false,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut prevalidated_page_lamports,
                &mut prevalidated_page_data,
                false,
                true,
                false,
            );
            let mint = account(
                &mint_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut prevalidated_mint_lamports,
                &mut prevalidated_mint_data,
                false,
                false,
                false,
            );
            let source = account(
                &source_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut prevalidated_source_lamports,
                &mut prevalidated_source_data,
                false,
                true,
                false,
            );
            let authority = account(
                &source_authority_key,
                &loader_owner,
                &mut prevalidated_authority_lamports,
                &mut prevalidated_authority_data,
                true,
                false,
                false,
            );
            let vault = account(
                &vault_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut prevalidated_vault_lamports,
                &mut prevalidated_vault_data,
                false,
                true,
                false,
            );
            let token_program = account(
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &loader_owner,
                &mut prevalidated_token_program_lamports,
                &mut prevalidated_token_program_data,
                false,
                false,
                true,
            );
            apply_prevalidated_vault_backed_deposit_with_transfer_v1(
                &program_id,
                &[pool, page],
                &[mint, source, authority, vault, token_program],
                &canonical,
                request,
                |_, infos| {
                    write_token_amount_for_test(&infos[0], 923)?;
                    write_token_amount_for_test(&infos[2], 117)?;
                    Ok(())
                },
            )
            .unwrap()
        };

        assert_eq!(prevalidated_event, standalone_event);
        assert_eq!(prevalidated_pool_data, standalone_pool_data);
        assert_eq!(prevalidated_page_data, standalone_page_data);
        assert_eq!(prevalidated_mint_data, standalone_mint_data);
        assert_eq!(prevalidated_source_data, standalone_source_data);
        assert_eq!(prevalidated_vault_data, standalone_vault_data);
    }

    #[test]
    fn failed_transfer_leaves_pool_and_history_byte_exact() {
        let program_id = Pubkey::new_unique();
        let mint_key = Pubkey::new_unique();
        let pool_key = pool_v1_state_address(&program_id, &mint_key).0;
        let page_key = crate::pool_v1_root_page_address(&program_id, &pool_key, 0).0;
        let vault_key = pool_v1_vault_token_account_address(&program_id, &pool_key).0;
        let vault_authority = pool_v1_vault_authority_address(&program_id, &pool_key).0;
        let source_key = Pubkey::new_unique();
        let source_authority_key = Pubkey::new_unique();
        let loader_owner = Pubkey::new_unique();
        let mut pool_data = [0u8; POOL_V1_STATE_ACCOUNT_BYTES];
        let mut page_data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        let mut pool_lamports = 1;
        let mut page_lamports = 1;
        {
            let pool = account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
                false,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut page_lamports,
                &mut page_data,
                false,
                true,
                false,
            );
            initialize_pool_accounts_v1(&program_id, &[pool, page], initialization(&mint_key))
                .unwrap();
        }
        let pool_before = pool_data;
        let page_before = page_data.clone();
        let mut mint_data = mint_data(6);
        let mut source_data = token_data(&mint_key, &source_authority_key, 100);
        let mut vault_data = token_data(&mint_key, &vault_authority, 0);
        let mut authority_data = [];
        let mut token_program_data = [];
        let mut mint_lamports = 1;
        let mut source_lamports = 1;
        let mut authority_lamports = 1;
        let mut vault_lamports = 1;
        let mut token_program_lamports = 1;
        let called = Cell::new(false);
        let result = {
            let pool = account(
                &pool_key,
                &program_id,
                &mut pool_lamports,
                &mut pool_data,
                false,
                true,
                false,
            );
            let page = account(
                &page_key,
                &program_id,
                &mut page_lamports,
                &mut page_data,
                false,
                true,
                false,
            );
            let mint = account(
                &mint_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut mint_lamports,
                &mut mint_data,
                false,
                false,
                false,
            );
            let source = account(
                &source_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut source_lamports,
                &mut source_data,
                false,
                true,
                false,
            );
            let authority = account(
                &source_authority_key,
                &loader_owner,
                &mut authority_lamports,
                &mut authority_data,
                true,
                false,
                false,
            );
            let vault = account(
                &vault_key,
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &mut vault_lamports,
                &mut vault_data,
                false,
                true,
                false,
            );
            let token_program = account(
                &LEGACY_SPL_TOKEN_PROGRAM_ID,
                &loader_owner,
                &mut token_program_lamports,
                &mut token_program_data,
                false,
                false,
                true,
            );
            apply_vault_backed_deposit_with_transfer_v1(
                &program_id,
                &[pool, page],
                &[mint, source, authority, vault, token_program],
                DepositRequestV1 {
                    owner_key: digest(10),
                    amount: 50,
                    salt: digest(100),
                    encrypted_note_payload: &[],
                },
                |_, _| {
                    called.set(true);
                    Err(ProgramError::Custom(0xDEAD))
                },
            )
        };
        assert!(called.get());
        assert_eq!(result, Err(ProgramError::Custom(0xDEAD)));
        assert_eq!(pool_data, pool_before);
        assert_eq!(page_data, page_before);
        assert_eq!(
            u64::from_le_bytes(source_data[64..72].try_into().unwrap()),
            100
        );
        assert_eq!(
            u64::from_le_bytes(vault_data[64..72].try_into().unwrap()),
            0
        );
    }

    #[test]
    fn invalid_amount_payload_and_token2022_shape_fail_before_transfer() {
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 0,
            salt: digest(100),
            encrypted_note_payload: &[],
        };
        assert_eq!(
            validate_request(&request),
            Err(PoolV1ProgramError::InvalidDepositAmount.into())
        );
        assert_eq!(
            validate_request(&DepositRequestV1 {
                amount: VALUE_LIMIT,
                ..request
            }),
            Err(PoolV1ProgramError::InvalidDepositAmount.into())
        );
        let oversized = [0u8; POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES + 1];
        assert_eq!(
            validate_request(&DepositRequestV1 {
                amount: 1,
                encrypted_note_payload: &oversized,
                ..request
            }),
            Err(PoolV1ProgramError::InvalidEncryptedNotePayload.into())
        );

        let mut token2022_mint = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES + 1];
        token2022_mint[45] = 1;
        assert_eq!(
            crate::vault::parse_legacy_mint_v1(&token2022_mint),
            Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into())
        );
        let mut frozen = token_data(&Pubkey::new_unique(), &Pubkey::new_unique(), 1);
        frozen[108] = 2;
        assert_eq!(
            crate::vault::parse_legacy_token_account_v1(&frozen),
            Err(PoolV1ProgramError::InvalidTokenAccount.into())
        );
    }
}
