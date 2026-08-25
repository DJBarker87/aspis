//! Exact, unsigned Pool V1 Solana instruction builders.
//!
//! These builders reuse the program crate's frozen encoders and derive every
//! Pool-owned address from the caller-pinned deployment id. They never sign,
//! submit, simulate, or choose a program id. Account order and privileges are
//! part of the returned ABI and duplicate semantic roles fail closed.

use std::collections::BTreeSet;

use aspis_pool::{
    decode_initialize_instruction_v1, decode_private_transfer_instruction_v1,
    decode_withdrawal_instruction_v1,
    deposit::DepositRequestV1,
    deposit_transport::{
        decode_deposit_instruction_v1, encode_deposit_instruction_v1,
        DepositInstructionFormatErrorV1, POOL_V1_DEPOSIT_INSTRUCTION_MAGIC,
    },
    encode_initialize_instruction_v1, encode_private_transfer_instruction_v1,
    encode_withdrawal_instruction_v1, pool_v1_nullifier_marker_address, pool_v1_root_page_address,
    pool_v1_state_address, pool_v1_vault_authority_address, pool_v1_vault_token_account_address,
    pool_v1_verifier_entry_address, pool_v1_verifier_registry_address, PoolInitializationV1,
    PoolInstructionFormatErrorV1, PrivateTransferStatementV1, WithdrawalStatementV1,
    LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_INITIALIZE_INSTRUCTION_MAGIC,
    POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC, POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC,
};
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{root_history_location, HistoricalAnchorEnvelopeV1, POOL_V1_LEAF_CAPACITY},
};
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
};
use solana_sdk_ids::system_program;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolTransactionBuilderErrorV1 {
    UnpinnedProgramId,
    ArithmeticOverflow,
    TreeCapacityExceeded,
    AnchorAfterCurrentRoot,
    MissingRolloverPayer,
    UnexpectedRolloverPayer,
    AccountAlias,
    WrongProgramId,
    WrongAccountLayout,
    DepositFormat(DepositInstructionFormatErrorV1),
    PoolFormat(PoolInstructionFormatErrorV1),
}

impl From<DepositInstructionFormatErrorV1> for PoolTransactionBuilderErrorV1 {
    fn from(error: DepositInstructionFormatErrorV1) -> Self {
        Self::DepositFormat(error)
    }
}

impl From<PoolInstructionFormatErrorV1> for PoolTransactionBuilderErrorV1 {
    fn from(error: PoolInstructionFormatErrorV1) -> Self {
        Self::PoolFormat(error)
    }
}

/// Public account addresses needed by both proof-authorized transitions.
/// The program authenticates the selected verifier and proof account at
/// runtime; this builder derives the registry addresses and freezes ordering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierRouteAccountsV1 {
    pub payer: Pubkey,
    pub registry_program: Pubkey,
    pub verifier_program: Pubkey,
    pub sealed_proof_account: Pubkey,
}

fn require_pinned_program(program_id: &Pubkey) -> Result<(), PoolTransactionBuilderErrorV1> {
    if *program_id == Pubkey::default() {
        Err(PoolTransactionBuilderErrorV1::UnpinnedProgramId)
    } else {
        Ok(())
    }
}

fn require_unique_accounts(accounts: &[AccountMeta]) -> Result<(), PoolTransactionBuilderErrorV1> {
    let mut keys = BTreeSet::new();
    if accounts
        .iter()
        .all(|meta| keys.insert(meta.pubkey.to_bytes()))
    {
        Ok(())
    } else {
        Err(PoolTransactionBuilderErrorV1::AccountAlias)
    }
}

/// Build exact `ASIN` initialization accounts and bytes.
pub fn build_initialize_instruction_v1(
    program_id: Pubkey,
    payer: Pubkey,
    initialization: &PoolInitializationV1,
) -> Result<Instruction, PoolTransactionBuilderErrorV1> {
    require_pinned_program(&program_id)?;
    let mint = Pubkey::new_from_array(initialization.asset_mint);
    let pool = pool_v1_state_address(&program_id, &mint).0;
    let page_zero = pool_v1_root_page_address(&program_id, &pool, 0).0;
    let vault = pool_v1_vault_token_account_address(&program_id, &pool).0;
    let accounts = vec![
        AccountMeta::new(payer, true),
        AccountMeta::new(pool, false),
        AccountMeta::new(page_zero, false),
        AccountMeta::new_readonly(mint, false),
        AccountMeta::new(vault, false),
        AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
        AccountMeta::new_readonly(system_program::id(), false),
    ];
    require_unique_accounts(&accounts)?;
    Ok(Instruction {
        program_id,
        accounts,
        data: encode_initialize_instruction_v1(initialization)?.to_vec(),
    })
}

/// Build exact `ASDI` deposit accounts and bytes for one authenticated Pool
/// state snapshot. `current_root_sequence` is the state sequence used to
/// choose the current/root-rollover account layout.
#[allow(clippy::too_many_arguments)]
pub fn build_deposit_instruction_v1(
    program_id: Pubkey,
    pool: Pubkey,
    asset_mint: Pubkey,
    current_root_sequence: u64,
    source_token_account: Pubkey,
    source_authority: Pubkey,
    rollover_payer: Option<Pubkey>,
    request: &DepositRequestV1<'_>,
) -> Result<Instruction, PoolTransactionBuilderErrorV1> {
    require_pinned_program(&program_id)?;
    if pool_v1_state_address(&program_id, &asset_mint).0 != pool {
        return Err(PoolTransactionBuilderErrorV1::WrongAccountLayout);
    }
    let next_sequence = current_root_sequence
        .checked_add(1)
        .ok_or(PoolTransactionBuilderErrorV1::ArithmeticOverflow)?;
    if next_sequence > POOL_V1_LEAF_CAPACITY {
        return Err(PoolTransactionBuilderErrorV1::TreeCapacityExceeded);
    }
    let current_page_number = root_history_location(current_root_sequence).page_number;
    let next_page_number = root_history_location(next_sequence).page_number;
    let current_page = pool_v1_root_page_address(&program_id, &pool, current_page_number).0;
    let vault = pool_v1_vault_token_account_address(&program_id, &pool).0;
    let mut accounts = vec![AccountMeta::new(pool, false)];
    if current_page_number == next_page_number {
        if rollover_payer.is_some() {
            return Err(PoolTransactionBuilderErrorV1::UnexpectedRolloverPayer);
        }
        accounts.extend([
            AccountMeta::new(current_page, false),
            AccountMeta::new_readonly(asset_mint, false),
            AccountMeta::new(source_token_account, false),
            AccountMeta::new_readonly(source_authority, true),
            AccountMeta::new(vault, false),
            AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
        ]);
    } else {
        let payer = rollover_payer.ok_or(PoolTransactionBuilderErrorV1::MissingRolloverPayer)?;
        let next_page = pool_v1_root_page_address(&program_id, &pool, next_page_number).0;
        accounts.extend([
            AccountMeta::new_readonly(current_page, false),
            AccountMeta::new(next_page, false),
            AccountMeta::new_readonly(asset_mint, false),
            AccountMeta::new(source_token_account, false),
            AccountMeta::new_readonly(source_authority, true),
            AccountMeta::new(vault, false),
            AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ]);
    }
    require_unique_accounts(&accounts)?;
    Ok(Instruction {
        program_id,
        accounts,
        data: encode_deposit_instruction_v1(request)?.as_bytes().to_vec(),
    })
}

fn spend_page_accounts_v1(
    program_id: &Pubkey,
    pool: &Pubkey,
    anchor_sequence: u64,
    current_root_sequence: u64,
    append_count: u64,
) -> Result<Vec<AccountMeta>, PoolTransactionBuilderErrorV1> {
    if anchor_sequence > current_root_sequence {
        return Err(PoolTransactionBuilderErrorV1::AnchorAfterCurrentRoot);
    }
    let final_sequence = current_root_sequence
        .checked_add(append_count)
        .ok_or(PoolTransactionBuilderErrorV1::ArithmeticOverflow)?;
    if current_root_sequence >= POOL_V1_LEAF_CAPACITY || final_sequence > POOL_V1_LEAF_CAPACITY {
        return Err(PoolTransactionBuilderErrorV1::TreeCapacityExceeded);
    }
    let first_sequence = current_root_sequence
        .checked_add(1)
        .ok_or(PoolTransactionBuilderErrorV1::ArithmeticOverflow)?;
    let anchor_page_number = root_history_location(anchor_sequence).page_number;
    let current_page_number = root_history_location(current_root_sequence).page_number;
    let first_page_number = root_history_location(first_sequence).page_number;
    let last_page_number = root_history_location(final_sequence).page_number;
    if anchor_page_number > current_page_number
        || first_page_number < current_page_number
        || last_page_number > current_page_number.saturating_add(1)
    {
        return Err(PoolTransactionBuilderErrorV1::WrongAccountLayout);
    }

    let anchor_page = pool_v1_root_page_address(program_id, pool, anchor_page_number).0;
    let current_page = pool_v1_root_page_address(program_id, pool, current_page_number).0;
    let current_writable = first_page_number == current_page_number;
    let mut accounts = vec![AccountMeta::new(*pool, false)];
    if anchor_page == current_page {
        accounts.push(if current_writable {
            AccountMeta::new(anchor_page, false)
        } else {
            AccountMeta::new_readonly(anchor_page, false)
        });
    } else {
        accounts.push(AccountMeta::new_readonly(anchor_page, false));
        accounts.push(if current_writable {
            AccountMeta::new(current_page, false)
        } else {
            AccountMeta::new_readonly(current_page, false)
        });
    }
    if last_page_number > current_page_number {
        accounts.push(AccountMeta::new(
            pool_v1_root_page_address(program_id, pool, last_page_number).0,
            false,
        ));
    }
    Ok(accounts)
}

fn append_verifier_suffix_v1(
    program_id: &Pubkey,
    pool: &Pubkey,
    envelope: &HistoricalAnchorEnvelopeV1,
    route: VerifierRouteAccountsV1,
    accounts: &mut Vec<AccountMeta>,
) -> Result<(), PoolTransactionBuilderErrorV1> {
    let nullifier = encode_digest_canonical(&envelope.nullifier);
    let marker = pool_v1_nullifier_marker_address(program_id, pool, &nullifier)
        .map_err(|_| PoolTransactionBuilderErrorV1::WrongAccountLayout)?
        .0;
    let registry = pool_v1_verifier_registry_address(&route.registry_program, pool).0;
    let entry = pool_v1_verifier_entry_address(
        &route.registry_program,
        pool,
        &envelope.verifier_profile,
        &envelope.verifier_release,
    )
    .0;
    accounts.extend([
        AccountMeta::new(marker, false),
        AccountMeta::new(route.payer, true),
        AccountMeta::new_readonly(system_program::id(), false),
        AccountMeta::new_readonly(registry, false),
        AccountMeta::new_readonly(entry, false),
        AccountMeta::new_readonly(route.verifier_program, false),
        AccountMeta::new_readonly(route.sealed_proof_account, false),
    ]);
    Ok(())
}

pub fn build_private_transfer_instruction_v1(
    program_id: Pubkey,
    current_root_sequence: u64,
    envelope: &HistoricalAnchorEnvelopeV1,
    statement: &PrivateTransferStatementV1,
    route: VerifierRouteAccountsV1,
) -> Result<Instruction, PoolTransactionBuilderErrorV1> {
    require_pinned_program(&program_id)?;
    let pool = Pubkey::new_from_array(statement.pool);
    let mut accounts = spend_page_accounts_v1(
        &program_id,
        &pool,
        statement.anchor_sequence,
        current_root_sequence,
        2,
    )?;
    append_verifier_suffix_v1(&program_id, &pool, envelope, route, &mut accounts)?;
    require_unique_accounts(&accounts)?;
    Ok(Instruction {
        program_id,
        accounts,
        data: encode_private_transfer_instruction_v1(envelope, statement)?.to_vec(),
    })
}

#[allow(clippy::too_many_arguments)]
pub fn build_withdrawal_instruction_v1(
    program_id: Pubkey,
    current_root_sequence: u64,
    asset_mint: Pubkey,
    envelope: &HistoricalAnchorEnvelopeV1,
    statement: &WithdrawalStatementV1,
    route: VerifierRouteAccountsV1,
) -> Result<Instruction, PoolTransactionBuilderErrorV1> {
    require_pinned_program(&program_id)?;
    let pool = Pubkey::new_from_array(statement.pool);
    if pool_v1_state_address(&program_id, &asset_mint).0 != pool {
        return Err(PoolTransactionBuilderErrorV1::WrongAccountLayout);
    }
    let destination = Pubkey::new_from_array(statement.destination_token_account);
    let mut accounts = spend_page_accounts_v1(
        &program_id,
        &pool,
        statement.anchor_sequence,
        current_root_sequence,
        1,
    )?;
    append_verifier_suffix_v1(&program_id, &pool, envelope, route, &mut accounts)?;
    accounts.extend([
        AccountMeta::new_readonly(asset_mint, false),
        AccountMeta::new(
            pool_v1_vault_token_account_address(&program_id, &pool).0,
            false,
        ),
        AccountMeta::new(destination, false),
        AccountMeta::new_readonly(pool_v1_vault_authority_address(&program_id, &pool).0, false),
        AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
    ]);
    require_unique_accounts(&accounts)?;
    Ok(Instruction {
        program_id,
        accounts,
        data: encode_withdrawal_instruction_v1(envelope, statement)?.to_vec(),
    })
}

/// Rebuild and compare an untrusted unsigned instruction against the exact
/// account ABI at one Pool state snapshot. This is used by the relayer before
/// it exposes an instruction to an external signer.
pub fn validate_pool_instruction_v1(
    pinned_program_id: Pubkey,
    current_root_sequence: u64,
    registry_program: Pubkey,
    instruction: &Instruction,
) -> Result<(), PoolTransactionBuilderErrorV1> {
    require_pinned_program(&pinned_program_id)?;
    if instruction.program_id != pinned_program_id {
        return Err(PoolTransactionBuilderErrorV1::WrongProgramId);
    }
    require_unique_accounts(&instruction.accounts)?;
    let magic = instruction
        .data
        .get(..4)
        .ok_or(PoolTransactionBuilderErrorV1::WrongAccountLayout)?;
    let rebuilt = if magic == POOL_V1_INITIALIZE_INSTRUCTION_MAGIC {
        let decoded = decode_initialize_instruction_v1(&instruction.data)?;
        let payer = instruction
            .accounts
            .first()
            .ok_or(PoolTransactionBuilderErrorV1::WrongAccountLayout)?
            .pubkey;
        build_initialize_instruction_v1(pinned_program_id, payer, &decoded)?
    } else if magic == POOL_V1_DEPOSIT_INSTRUCTION_MAGIC {
        let decoded = decode_deposit_instruction_v1(&instruction.data)?;
        let rollover = root_history_location(current_root_sequence).page_number
            != root_history_location(
                current_root_sequence
                    .checked_add(1)
                    .ok_or(PoolTransactionBuilderErrorV1::ArithmeticOverflow)?,
            )
            .page_number;
        let (mint_index, source_index, authority_index, payer) = if rollover {
            (3, 4, 5, Some(8))
        } else {
            (2, 3, 4, None)
        };
        let account = |index: usize| {
            instruction
                .accounts
                .get(index)
                .map(|meta| meta.pubkey)
                .ok_or(PoolTransactionBuilderErrorV1::WrongAccountLayout)
        };
        build_deposit_instruction_v1(
            pinned_program_id,
            account(0)?,
            account(mint_index)?,
            current_root_sequence,
            account(source_index)?,
            account(authority_index)?,
            payer.map(account).transpose()?,
            &decoded,
        )?
    } else if magic == POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC {
        let decoded = decode_private_transfer_instruction_v1(&instruction.data)?;
        let prefix = spend_page_accounts_v1(
            &pinned_program_id,
            &Pubkey::new_from_array(decoded.statement.pool),
            decoded.statement.anchor_sequence,
            current_root_sequence,
            2,
        )?;
        let offset = prefix.len();
        let account = |index: usize| {
            instruction
                .accounts
                .get(index)
                .map(|meta| meta.pubkey)
                .ok_or(PoolTransactionBuilderErrorV1::WrongAccountLayout)
        };
        build_private_transfer_instruction_v1(
            pinned_program_id,
            current_root_sequence,
            &decoded.envelope,
            &decoded.statement,
            VerifierRouteAccountsV1 {
                payer: account(offset + 1)?,
                registry_program,
                verifier_program: account(offset + 5)?,
                sealed_proof_account: account(offset + 6)?,
            },
        )?
    } else if magic == POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC {
        let decoded = decode_withdrawal_instruction_v1(&instruction.data)?;
        let prefix = spend_page_accounts_v1(
            &pinned_program_id,
            &Pubkey::new_from_array(decoded.statement.pool),
            decoded.statement.anchor_sequence,
            current_root_sequence,
            1,
        )?;
        let offset = prefix.len();
        let account = |index: usize| {
            instruction
                .accounts
                .get(index)
                .map(|meta| meta.pubkey)
                .ok_or(PoolTransactionBuilderErrorV1::WrongAccountLayout)
        };
        build_withdrawal_instruction_v1(
            pinned_program_id,
            current_root_sequence,
            account(offset + 7)?,
            &decoded.envelope,
            &decoded.statement,
            VerifierRouteAccountsV1 {
                payer: account(offset + 1)?,
                registry_program,
                verifier_program: account(offset + 5)?,
                sealed_proof_account: account(offset + 6)?,
            },
        )?
    } else {
        return Err(PoolTransactionBuilderErrorV1::WrongAccountLayout);
    };
    if rebuilt == *instruction {
        Ok(())
    } else {
        Err(PoolTransactionBuilderErrorV1::WrongAccountLayout)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{
        pool_v1::{
            HistoricalAnchorEnvelopeV1, PoolV1TransitionKind, VerifierPolicyV1,
            POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
        },
        poseidon2::Digest,
    };

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn route() -> VerifierRouteAccountsV1 {
        VerifierRouteAccountsV1 {
            payer: key(7),
            registry_program: key(8),
            verifier_program: key(9),
            sealed_proof_account: key(10),
        }
    }

    fn envelope(kind: PoolV1TransitionKind, pool: Pubkey) -> HistoricalAnchorEnvelopeV1 {
        HistoricalAnchorEnvelopeV1 {
            transition_kind: kind,
            pool: pool.to_bytes(),
            deployment_domain: [0x31; 32],
            anchor_sequence: 7,
            anchor_root: digest(100),
            nullifier: digest(200),
            verifier_profile: [0x41; 32],
            verifier_release: [0x42; 32],
        }
    }

    #[test]
    fn builders_round_trip_all_frozen_program_decoders_and_account_abis() {
        let program_id = key(1);
        let payer = key(2);
        let mint = key(3);
        let initialization = PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(9),
            deployment_domain: [0x31; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
                registry_program: route().registry_program.to_bytes(),
                registry_authority: [0; 32],
                policy_binding: [0x33; 32],
            },
        };
        let init = build_initialize_instruction_v1(program_id, payer, &initialization).unwrap();
        assert_eq!(
            decode_initialize_instruction_v1(&init.data).unwrap(),
            initialization
        );
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let page = pool_v1_root_page_address(&program_id, &pool, 0).0;
        let vault = pool_v1_vault_token_account_address(&program_id, &pool).0;
        assert_eq!(
            init.accounts,
            vec![
                AccountMeta::new(payer, true),
                AccountMeta::new(pool, false),
                AccountMeta::new(page, false),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(vault, false),
                AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
                AccountMeta::new_readonly(system_program::id(), false),
            ]
        );
        validate_pool_instruction_v1(program_id, 0, route().registry_program, &init).unwrap();

        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(20),
            encrypted_note_payload: &[0xaa, 0xbb],
        };
        let deposit =
            build_deposit_instruction_v1(program_id, pool, mint, 7, key(4), key(5), None, &request)
                .unwrap();
        let decoded_deposit = decode_deposit_instruction_v1(&deposit.data).unwrap();
        assert_eq!(decoded_deposit, request);
        assert_eq!(
            deposit.accounts,
            vec![
                AccountMeta::new(pool, false),
                AccountMeta::new(page, false),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(key(4), false),
                AccountMeta::new_readonly(key(5), true),
                AccountMeta::new(vault, false),
                AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
            ]
        );
        validate_pool_instruction_v1(program_id, 7, route().registry_program, &deposit).unwrap();

        let private_envelope = envelope(PoolV1TransitionKind::PrivateTransfer, pool);
        let private_statement = PrivateTransferStatementV1 {
            pool: pool.to_bytes(),
            deployment_domain: private_envelope.deployment_domain,
            anchor_sequence: private_envelope.anchor_sequence,
            anchor_root: private_envelope.anchor_root,
            nullifier: private_envelope.nullifier,
            asset_id: M31(9),
            recipient_commitment: digest(300),
            change_commitment: digest(400),
        };
        let private = build_private_transfer_instruction_v1(
            program_id,
            7,
            &private_envelope,
            &private_statement,
            route(),
        )
        .unwrap();
        let decoded_private = decode_private_transfer_instruction_v1(&private.data).unwrap();
        assert_eq!(decoded_private.statement, private_statement);
        let verifier_registry =
            pool_v1_verifier_registry_address(&route().registry_program, &pool).0;
        let verifier_entry = pool_v1_verifier_entry_address(
            &route().registry_program,
            &pool,
            &private_envelope.verifier_profile,
            &private_envelope.verifier_release,
        )
        .0;
        let private_marker = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &encode_digest_canonical(&private_envelope.nullifier),
        )
        .unwrap()
        .0;
        assert_eq!(
            private.accounts,
            vec![
                AccountMeta::new(pool, false),
                AccountMeta::new(page, false),
                AccountMeta::new(private_marker, false),
                AccountMeta::new(route().payer, true),
                AccountMeta::new_readonly(system_program::id(), false),
                AccountMeta::new_readonly(verifier_registry, false),
                AccountMeta::new_readonly(verifier_entry, false),
                AccountMeta::new_readonly(route().verifier_program, false),
                AccountMeta::new_readonly(route().sealed_proof_account, false),
            ]
        );
        validate_pool_instruction_v1(program_id, 7, route().registry_program, &private).unwrap();

        let withdrawal_envelope = envelope(PoolV1TransitionKind::Withdrawal, pool);
        let withdrawal_statement = WithdrawalStatementV1 {
            pool: pool.to_bytes(),
            deployment_domain: withdrawal_envelope.deployment_domain,
            anchor_sequence: withdrawal_envelope.anchor_sequence,
            anchor_root: withdrawal_envelope.anchor_root,
            nullifier: withdrawal_envelope.nullifier,
            asset_id: M31(9),
            amount: 5,
            destination_token_account: key(11).to_bytes(),
            change_commitment: digest(500),
        };
        let withdrawal = build_withdrawal_instruction_v1(
            program_id,
            7,
            mint,
            &withdrawal_envelope,
            &withdrawal_statement,
            route(),
        )
        .unwrap();
        let decoded_withdrawal = decode_withdrawal_instruction_v1(&withdrawal.data).unwrap();
        assert_eq!(decoded_withdrawal.statement, withdrawal_statement);
        let withdrawal_marker = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &encode_digest_canonical(&withdrawal_envelope.nullifier),
        )
        .unwrap()
        .0;
        let withdrawal_entry = pool_v1_verifier_entry_address(
            &route().registry_program,
            &pool,
            &withdrawal_envelope.verifier_profile,
            &withdrawal_envelope.verifier_release,
        )
        .0;
        assert_eq!(
            withdrawal.accounts,
            vec![
                AccountMeta::new(pool, false),
                AccountMeta::new(page, false),
                AccountMeta::new(withdrawal_marker, false),
                AccountMeta::new(route().payer, true),
                AccountMeta::new_readonly(system_program::id(), false),
                AccountMeta::new_readonly(verifier_registry, false),
                AccountMeta::new_readonly(withdrawal_entry, false),
                AccountMeta::new_readonly(route().verifier_program, false),
                AccountMeta::new_readonly(route().sealed_proof_account, false),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(vault, false),
                AccountMeta::new(key(11), false),
                AccountMeta::new_readonly(
                    pool_v1_vault_authority_address(&program_id, &pool).0,
                    false,
                ),
                AccountMeta::new_readonly(LEGACY_SPL_TOKEN_PROGRAM_ID, false),
            ]
        );
        validate_pool_instruction_v1(program_id, 7, route().registry_program, &withdrawal).unwrap();
    }

    #[test]
    fn rollover_is_exact_and_account_aliases_fail_before_exposure() {
        let program_id = key(1);
        let mint = key(3);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 1,
            salt: digest(20),
            encrypted_note_payload: &[],
        };
        let current = aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_CAPACITY as u64 - 1;
        let rollover = build_deposit_instruction_v1(
            program_id,
            pool,
            mint,
            current,
            key(4),
            key(5),
            Some(key(6)),
            &request,
        )
        .unwrap();
        assert_eq!(rollover.accounts.len(), 10);
        assert!(!rollover.accounts[1].is_writable);
        assert!(rollover.accounts[2].is_writable);
        validate_pool_instruction_v1(program_id, current, route().registry_program, &rollover)
            .unwrap();

        let private_envelope = envelope(PoolV1TransitionKind::PrivateTransfer, pool);
        let private_statement = PrivateTransferStatementV1 {
            pool: pool.to_bytes(),
            deployment_domain: private_envelope.deployment_domain,
            anchor_sequence: private_envelope.anchor_sequence,
            anchor_root: private_envelope.anchor_root,
            nullifier: private_envelope.nullifier,
            asset_id: M31(9),
            recipient_commitment: digest(300),
            change_commitment: digest(400),
        };
        let private_rollover = build_private_transfer_instruction_v1(
            program_id,
            current,
            &private_envelope,
            &private_statement,
            route(),
        )
        .unwrap();
        assert_eq!(private_rollover.accounts.len(), 10);
        assert!(!private_rollover.accounts[1].is_writable);
        assert!(private_rollover.accounts[2].is_writable);
        validate_pool_instruction_v1(
            program_id,
            current,
            route().registry_program,
            &private_rollover,
        )
        .unwrap();

        assert_eq!(
            build_deposit_instruction_v1(
                program_id,
                pool,
                mint,
                7,
                key(4),
                key(4),
                None,
                &request,
            )
            .err(),
            Some(PoolTransactionBuilderErrorV1::AccountAlias)
        );

        let mut forged = rollover;
        forged.accounts[2].pubkey = forged.accounts[1].pubkey;
        assert_eq!(
            validate_pool_instruction_v1(program_id, current, route().registry_program, &forged),
            Err(PoolTransactionBuilderErrorV1::AccountAlias)
        );
    }
}
