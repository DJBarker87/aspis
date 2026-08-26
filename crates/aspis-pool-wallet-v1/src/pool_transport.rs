//! Exact successful Pool V1 top-level instruction/return-data authentication.
//!
//! Solana return data is transaction-global, so a wallet accepts it only for
//! one unique, final top-level invocation of the deployment-pinned Pool. This
//! module extends the original deposit adapter to initialization, preparation,
//! and the two proof-authorized transitions without accepting inner-instruction
//! guesses.

use std::collections::BTreeSet;

use aspis_core::field::M31;
use aspis_pool::{
    decode_initialize_instruction_v1, decode_prepare_settlement_instruction_v1,
    decode_private_transfer_instruction_v1, decode_withdrawal_instruction_v1,
    instruction::encode_transition_receipt_v1, pool_v1_prepared_settlement_plan_address,
    pool_v1_prepared_settlement_rollover_address, pool_v1_root_page_address, pool_v1_state_address,
    pool_v1_vault_token_account_address, PrepareSettlementInstructionFormatErrorV1,
    TransitionReceiptV1, POOL_V1_INITIALIZATION_RECEIPT_BYTES,
    POOL_V1_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC,
    POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC, POOL_V1_TRANSITION_RECEIPT_BYTES,
    POOL_V1_TRANSITION_RECEIPT_MAGIC, POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC,
};
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        root_history_location, verifier_statement_payload_digest_v1, PoolV1TransitionKind,
        POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_HISTORICAL_ANCHOR_VERSION, POOL_V1_LEAF_CAPACITY,
    },
};
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;
use solana_sdk_ids::system_program;

use crate::{
    rpc_adapter::{
        authenticate_finalized_rpc_deposit_v1, DepositRpcAdapterErrorV1, DepositRpcBindingV1,
        FinalizedRpcTransactionV1, ResolvedRpcInstructionV1,
    },
    scan_state::{DepositEventIdV1, DepositScanIdentityV1, FinalizedDepositRecordV1},
};

pub const POOL_V1_INITIALIZATION_RECEIPT_MAGIC: [u8; 4] = *b"ASIR";
pub const POOL_V1_TRANSITION_RECEIPT_VERSION: u8 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InitializationReceiptV1 {
    pub pool: [u8; 32],
    pub root_page_zero: [u8; 32],
    pub vault_token_account: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransitionOutputRoleV1 {
    Recipient,
    Change,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedTransitionOutputV1 {
    pub id: DepositEventIdV1,
    pub transition_kind: PoolV1TransitionKind,
    pub role: TransitionOutputRoleV1,
    pub leaf_index: u64,
    pub root_sequence: u64,
    pub commitment: [u8; 32],
    /// Present for the last output, whose root is carried by `ASTR`. Earlier
    /// output roots are authenticated from the append-only history page.
    pub expected_root: Option<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedTransitionV1 {
    pub receipt: TransitionReceiptV1,
    pub outputs: Vec<AuthenticatedTransitionOutputV1>,
    /// Exact `instruction || ASTR` bytes. Scan-state fingerprints domain-bind
    /// these bytes together with each output's event index.
    pub authenticated_transport: Vec<u8>,
}

/// Finalized, successful preparation of a state-bound Pool plan. Preparation
/// is non-appending: this metadata is public reconciliation evidence only and
/// does not advance the wallet leaf/nullifier cursor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedPreparedSettlementV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub source_root_sequence: u64,
    pub not_before_slot: u64,
    pub expires_at_slot: u64,
    pub plan_authority: [u8; 32],
    pub authorization_receipt: [u8; 32],
    pub verifier_registry: [u8; 32],
    pub verifier_entry: [u8; 32],
    pub core_plan: [u8; 32],
    pub rollover_page: Option<[u8; 32]>,
    pub rollover_shard: Option<[u8; 32]>,
}

pub enum AuthenticatedPoolInvocationV1<'a> {
    Initialization(InitializationReceiptV1),
    PreparedSettlement(AuthenticatedPreparedSettlementV1),
    Deposit(FinalizedDepositRecordV1<'a>),
    Transition(AuthenticatedTransitionV1),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolRpcAdapterErrorV1 {
    TransactionFailed,
    PoolInstructionMissing,
    MultiplePoolInstructions,
    PoolInstructionNotFinal,
    MissingReturnData,
    UnexpectedReturnData,
    WrongReturnDataProgram,
    UnsupportedPoolInstruction,
    WrongReceiptLength,
    WrongReceiptMagic,
    WrongReceiptVersion,
    WrongTransitionKind,
    WrongOutputCount,
    WrongDigestEncoding,
    NonZeroReserved,
    NonCanonicalDigest,
    IdentityMismatch,
    ReceiptInstructionMismatch,
    EventIdentity,
    MissingInstructionAccounts,
    InstructionAccountAlias,
    WrongInstructionAccounts,
    Deposit(DepositRpcAdapterErrorV1),
    PoolInstruction(aspis_pool::PoolInstructionFormatErrorV1),
    PreparedSettlementInstruction(PrepareSettlementInstructionFormatErrorV1),
}

pub fn decode_initialization_receipt_v1(
    bytes: &[u8],
) -> Result<InitializationReceiptV1, PoolRpcAdapterErrorV1> {
    if bytes.len() != POOL_V1_INITIALIZATION_RECEIPT_BYTES {
        return Err(PoolRpcAdapterErrorV1::WrongReceiptLength);
    }
    if bytes[..4] != POOL_V1_INITIALIZATION_RECEIPT_MAGIC {
        return Err(PoolRpcAdapterErrorV1::WrongReceiptMagic);
    }
    if bytes[4] != 1 {
        return Err(PoolRpcAdapterErrorV1::WrongReceiptVersion);
    }
    if bytes[5..8] != [0u8; 3] {
        return Err(PoolRpcAdapterErrorV1::NonZeroReserved);
    }
    Ok(InitializationReceiptV1 {
        pool: bytes[8..40].try_into().unwrap(),
        root_page_zero: bytes[40..72].try_into().unwrap(),
        vault_token_account: bytes[72..104].try_into().unwrap(),
    })
}

pub fn decode_transition_receipt_v1(
    bytes: &[u8],
) -> Result<TransitionReceiptV1, PoolRpcAdapterErrorV1> {
    if bytes.len() != POOL_V1_TRANSITION_RECEIPT_BYTES {
        return Err(PoolRpcAdapterErrorV1::WrongReceiptLength);
    }
    if bytes[..4] != POOL_V1_TRANSITION_RECEIPT_MAGIC {
        return Err(PoolRpcAdapterErrorV1::WrongReceiptMagic);
    }
    if bytes[4] != POOL_V1_TRANSITION_RECEIPT_VERSION {
        return Err(PoolRpcAdapterErrorV1::WrongReceiptVersion);
    }
    let transition_kind = if bytes[5] == PoolV1TransitionKind::PrivateTransfer as u8 {
        PoolV1TransitionKind::PrivateTransfer
    } else if bytes[5] == PoolV1TransitionKind::Withdrawal as u8 {
        PoolV1TransitionKind::Withdrawal
    } else {
        return Err(PoolRpcAdapterErrorV1::WrongTransitionKind);
    };
    let expected_outputs = match transition_kind {
        PoolV1TransitionKind::PrivateTransfer => 2,
        PoolV1TransitionKind::Withdrawal => 1,
    };
    if bytes[6] != expected_outputs {
        return Err(PoolRpcAdapterErrorV1::WrongOutputCount);
    }
    if bytes[7] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolRpcAdapterErrorV1::WrongDigestEncoding);
    }
    if bytes[140..144] != [0u8; 4] {
        return Err(PoolRpcAdapterErrorV1::NonZeroReserved);
    }
    let nullifier = decode_digest_canonical(bytes[40..72].try_into().unwrap())
        .map_err(|_| PoolRpcAdapterErrorV1::NonCanonicalDigest)?;
    let first_output = decode_digest_canonical(bytes[72..104].try_into().unwrap())
        .map_err(|_| PoolRpcAdapterErrorV1::NonCanonicalDigest)?;
    let root = decode_digest_canonical(bytes[168..200].try_into().unwrap())
        .map_err(|_| PoolRpcAdapterErrorV1::NonCanonicalDigest)?;
    let receipt = TransitionReceiptV1 {
        transition_kind,
        pool: bytes[8..40].try_into().unwrap(),
        nullifier,
        first_output,
        second_output_or_destination: bytes[104..136].try_into().unwrap(),
        withdrawal_amount: u32::from_le_bytes(bytes[136..140].try_into().unwrap()),
        first_leaf_index: u64::from_le_bytes(bytes[144..152].try_into().unwrap()),
        second_leaf_index: u64::from_le_bytes(bytes[152..160].try_into().unwrap()),
        root_sequence: u64::from_le_bytes(bytes[160..168].try_into().unwrap()),
        root,
    };
    let canonical =
        encode_transition_receipt_v1(&receipt).map_err(PoolRpcAdapterErrorV1::PoolInstruction)?;
    if canonical.as_slice() != bytes {
        return Err(PoolRpcAdapterErrorV1::ReceiptInstructionMismatch);
    }
    Ok(receipt)
}

fn exact_final_pool_instruction_index_v1(
    binding: &DepositRpcBindingV1,
    transaction: &FinalizedRpcTransactionV1<'_>,
) -> Result<usize, PoolRpcAdapterErrorV1> {
    if !transaction.succeeded {
        return Err(PoolRpcAdapterErrorV1::TransactionFailed);
    }
    let mut indices = transaction
        .top_level_instructions
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| {
            (instruction.program_id == *binding.program_id()).then_some(index)
        });
    let index = indices
        .next()
        .ok_or(PoolRpcAdapterErrorV1::PoolInstructionMissing)?;
    if indices.next().is_some() {
        return Err(PoolRpcAdapterErrorV1::MultiplePoolInstructions);
    }
    if index + 1 != transaction.top_level_instructions.len() {
        return Err(PoolRpcAdapterErrorV1::PoolInstructionNotFinal);
    }
    Ok(index)
}

fn require_identity(
    identity: &DepositScanIdentityV1,
    pool: &[u8; 32],
    deployment_domain: &[u8; 32],
    asset_id: M31,
) -> Result<(), PoolRpcAdapterErrorV1> {
    if pool != identity.pool()
        || deployment_domain != identity.deployment_domain()
        || asset_id.0 != identity.asset_id()
    {
        Err(PoolRpcAdapterErrorV1::IdentityMismatch)
    } else {
        Ok(())
    }
}

fn sha256_parts_v1(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

fn authenticate_prepared_settlement_v1(
    program_id: &Pubkey,
    identity: &DepositScanIdentityV1,
    current_root_sequence: u64,
    instruction: &ResolvedRpcInstructionV1<'_>,
) -> Result<AuthenticatedPreparedSettlementV1, PoolRpcAdapterErrorV1> {
    let prepared = decode_prepare_settlement_instruction_v1(instruction.data)
        .map_err(PoolRpcAdapterErrorV1::PreparedSettlementInstruction)?;
    let (envelope, statement_payload, append_count) = match prepared.transition_kind {
        PoolV1TransitionKind::PrivateTransfer => {
            let spend = decode_private_transfer_instruction_v1(prepared.spend_instruction)
                .map_err(PoolRpcAdapterErrorV1::PoolInstruction)?;
            require_identity(
                identity,
                &spend.statement.pool,
                &spend.statement.deployment_domain,
                spend.statement.asset_id,
            )?;
            (spend.envelope, spend.statement_payload, 2u64)
        }
        PoolV1TransitionKind::Withdrawal => {
            let spend = decode_withdrawal_instruction_v1(prepared.spend_instruction)
                .map_err(PoolRpcAdapterErrorV1::PoolInstruction)?;
            require_identity(
                identity,
                &spend.statement.pool,
                &spend.statement.deployment_domain,
                spend.statement.asset_id,
            )?;
            (spend.envelope, spend.statement_payload, 1u64)
        }
    };
    if instruction.account_keys.is_empty() {
        return Err(PoolRpcAdapterErrorV1::MissingInstructionAccounts);
    }
    let mut unique = BTreeSet::new();
    if !instruction
        .account_keys
        .iter()
        .all(|account| unique.insert(*account))
    {
        return Err(PoolRpcAdapterErrorV1::InstructionAccountAlias);
    }
    let final_sequence = current_root_sequence
        .checked_add(append_count)
        .ok_or(PoolRpcAdapterErrorV1::WrongInstructionAccounts)?;
    if envelope.anchor_sequence > current_root_sequence
        || current_root_sequence >= POOL_V1_LEAF_CAPACITY
        || final_sequence > POOL_V1_LEAF_CAPACITY
    {
        return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
    }
    let pool = Pubkey::new_from_array(*identity.pool());
    let anchor_page_number = root_history_location(envelope.anchor_sequence).page_number;
    let current_page_number = root_history_location(current_root_sequence).page_number;
    let final_page_number = root_history_location(final_sequence).page_number;
    if anchor_page_number > current_page_number
        || final_page_number > current_page_number.saturating_add(1)
    {
        return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
    }
    let account = |index: usize| {
        instruction
            .account_keys
            .get(index)
            .copied()
            .ok_or(PoolRpcAdapterErrorV1::WrongInstructionAccounts)
    };
    if account(0)? == [0u8; 32] || account(1)? != *identity.pool() {
        return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
    }
    let plan_authority = account(0)?;
    let anchor_page = pool_v1_root_page_address(program_id, &pool, anchor_page_number)
        .0
        .to_bytes();
    let current_page = pool_v1_root_page_address(program_id, &pool, current_page_number)
        .0
        .to_bytes();
    let mut cursor = 2usize;
    if account(cursor)? != anchor_page {
        return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
    }
    cursor += 1;
    if current_page != anchor_page {
        if account(cursor)? != current_page {
            return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
        }
        cursor += 1;
    }
    let has_rollover = final_page_number > current_page_number;
    let rollover_page = if has_rollover {
        let expected = pool_v1_root_page_address(program_id, &pool, final_page_number)
            .0
            .to_bytes();
        if account(cursor)? != expected {
            return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
        }
        cursor += 1;
        Some(expected)
    } else {
        None
    };
    let expected_accounts = cursor + if has_rollover { 6 } else { 5 };
    if instruction.account_keys.len() != expected_accounts {
        return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
    }
    let authorization_receipt = account(cursor)?;
    let verifier_registry = account(cursor + 1)?;
    let verifier_entry = account(cursor + 2)?;
    if authorization_receipt == [0u8; 32]
        || verifier_registry == [0u8; 32]
        || verifier_entry == [0u8; 32]
    {
        return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
    }
    let statement_digest = verifier_statement_payload_digest_v1(
        POOL_V1_HISTORICAL_ANCHOR_VERSION,
        &envelope.verifier_profile,
        &envelope.verifier_release,
        statement_payload,
        sha256_parts_v1,
    )
    .map_err(|_| PoolRpcAdapterErrorV1::WrongInstructionAccounts)?;
    let core_plan = pool_v1_prepared_settlement_plan_address(
        program_id,
        &pool,
        &statement_digest,
        current_root_sequence,
        &Pubkey::new_from_array(plan_authority),
    )
    .0;
    if account(cursor + 3)? != core_plan.to_bytes() {
        return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
    }
    let rollover_shard = if has_rollover {
        let expected = pool_v1_prepared_settlement_rollover_address(program_id, &core_plan)
            .0
            .to_bytes();
        if account(cursor + 4)? != expected
            || account(cursor + 5)? != system_program::id().to_bytes()
        {
            return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
        }
        Some(expected)
    } else {
        if account(cursor + 4)? != system_program::id().to_bytes() {
            return Err(PoolRpcAdapterErrorV1::WrongInstructionAccounts);
        }
        None
    };
    Ok(AuthenticatedPreparedSettlementV1 {
        transition_kind: prepared.transition_kind,
        source_root_sequence: current_root_sequence,
        not_before_slot: prepared.not_before_slot,
        expires_at_slot: prepared.expires_at_slot,
        plan_authority,
        authorization_receipt,
        verifier_registry,
        verifier_entry,
        core_plan: core_plan.to_bytes(),
        rollover_page,
        rollover_shard,
    })
}

/// Authenticate exactly one successful final top-level Pool invocation.
pub fn authenticate_finalized_rpc_pool_v1<'a>(
    binding: &DepositRpcBindingV1,
    identity: &DepositScanIdentityV1,
    current_root_sequence: u64,
    transaction: &'a FinalizedRpcTransactionV1<'a>,
) -> Result<AuthenticatedPoolInvocationV1<'a>, PoolRpcAdapterErrorV1> {
    let program_id = Pubkey::new_from_array(*binding.program_id());
    let mint = Pubkey::new_from_array(*identity.asset_mint());
    let expected_pool = pool_v1_state_address(&program_id, &mint).0;
    let expected_vault = pool_v1_vault_token_account_address(&program_id, &expected_pool).0;
    if expected_pool.to_bytes() != *identity.pool()
        || expected_vault.to_bytes() != *identity.vault_token_account()
    {
        return Err(PoolRpcAdapterErrorV1::IdentityMismatch);
    }
    let instruction_index = exact_final_pool_instruction_index_v1(binding, transaction)?;
    let instruction = &transaction.top_level_instructions[instruction_index];
    let magic = instruction
        .data
        .get(..4)
        .ok_or(PoolRpcAdapterErrorV1::UnsupportedPoolInstruction)?;

    if magic == crate::rpc_adapter::POOL_V1_DEPOSIT_INSTRUCTION_MAGIC {
        return authenticate_finalized_rpc_deposit_v1(binding, identity, transaction)
            .map(AuthenticatedPoolInvocationV1::Deposit)
            .map_err(PoolRpcAdapterErrorV1::Deposit);
    }

    if magic == POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC {
        let authenticated = authenticate_prepared_settlement_v1(
            &program_id,
            identity,
            current_root_sequence,
            instruction,
        )?;
        match transaction.return_data {
            None => {}
            Some(return_data) if return_data.program_id != *binding.program_id() => {
                return Err(PoolRpcAdapterErrorV1::WrongReturnDataProgram);
            }
            Some(return_data) if !return_data.data.is_empty() => {
                return Err(PoolRpcAdapterErrorV1::UnexpectedReturnData);
            }
            Some(_) => {}
        }
        return Ok(AuthenticatedPoolInvocationV1::PreparedSettlement(
            authenticated,
        ));
    }

    let return_data = transaction
        .return_data
        .ok_or(PoolRpcAdapterErrorV1::MissingReturnData)?;
    if return_data.program_id != *binding.program_id() {
        return Err(PoolRpcAdapterErrorV1::WrongReturnDataProgram);
    }

    if magic == POOL_V1_INITIALIZE_INSTRUCTION_MAGIC {
        let initialization = decode_initialize_instruction_v1(instruction.data)
            .map_err(PoolRpcAdapterErrorV1::PoolInstruction)?;
        if initialization.asset_mint != *identity.asset_mint()
            || initialization.deployment_domain != *identity.deployment_domain()
            || initialization.asset_id.0 != identity.asset_id()
        {
            return Err(PoolRpcAdapterErrorV1::IdentityMismatch);
        }
        let receipt = decode_initialization_receipt_v1(return_data.data)?;
        let mint = Pubkey::new_from_array(initialization.asset_mint);
        let expected_pool = pool_v1_state_address(&program_id, &mint).0;
        let expected_page = pool_v1_root_page_address(&program_id, &expected_pool, 0)
            .0
            .to_bytes();
        let expected_vault = pool_v1_vault_token_account_address(&program_id, &expected_pool)
            .0
            .to_bytes();
        if expected_pool.to_bytes() != *identity.pool()
            || expected_vault != *identity.vault_token_account()
            || receipt.pool != *identity.pool()
            || receipt.root_page_zero != expected_page
            || receipt.vault_token_account != *identity.vault_token_account()
        {
            return Err(PoolRpcAdapterErrorV1::ReceiptInstructionMismatch);
        }
        return Ok(AuthenticatedPoolInvocationV1::Initialization(receipt));
    }

    let receipt = decode_transition_receipt_v1(return_data.data)?;
    let instruction_index =
        u16::try_from(instruction_index).map_err(|_| PoolRpcAdapterErrorV1::EventIdentity)?;
    let mut authenticated_transport =
        Vec::with_capacity(instruction.data.len() + return_data.data.len());
    authenticated_transport.extend_from_slice(instruction.data);
    authenticated_transport.extend_from_slice(return_data.data);

    let (first_commitment, second_commitment) = if magic
        == POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC
    {
        let decoded = decode_private_transfer_instruction_v1(instruction.data)
            .map_err(PoolRpcAdapterErrorV1::PoolInstruction)?;
        require_identity(
            identity,
            &decoded.statement.pool,
            &decoded.statement.deployment_domain,
            decoded.statement.asset_id,
        )?;
        if receipt.transition_kind != PoolV1TransitionKind::PrivateTransfer
            || receipt.pool != decoded.statement.pool
            || receipt.nullifier != decoded.statement.nullifier
            || receipt.first_output != decoded.statement.recipient_commitment
            || receipt.second_output_or_destination
                != encode_digest_canonical(&decoded.statement.change_commitment)
            || receipt.withdrawal_amount != 0
            || receipt.second_leaf_index != receipt.first_leaf_index.saturating_add(1)
            || receipt.root_sequence != receipt.second_leaf_index.saturating_add(1)
        {
            return Err(PoolRpcAdapterErrorV1::ReceiptInstructionMismatch);
        }
        (
            encode_digest_canonical(&decoded.statement.recipient_commitment),
            Some(encode_digest_canonical(
                &decoded.statement.change_commitment,
            )),
        )
    } else if magic == POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC {
        let decoded = decode_withdrawal_instruction_v1(instruction.data)
            .map_err(PoolRpcAdapterErrorV1::PoolInstruction)?;
        require_identity(
            identity,
            &decoded.statement.pool,
            &decoded.statement.deployment_domain,
            decoded.statement.asset_id,
        )?;
        if receipt.transition_kind != PoolV1TransitionKind::Withdrawal
            || receipt.pool != decoded.statement.pool
            || receipt.nullifier != decoded.statement.nullifier
            || receipt.first_output != decoded.statement.change_commitment
            || receipt.second_output_or_destination != decoded.statement.destination_token_account
            || receipt.withdrawal_amount != decoded.statement.amount
            || receipt.second_leaf_index != 0
            || receipt.root_sequence != receipt.first_leaf_index.saturating_add(1)
        {
            return Err(PoolRpcAdapterErrorV1::ReceiptInstructionMismatch);
        }
        (
            encode_digest_canonical(&decoded.statement.change_commitment),
            None,
        )
    } else {
        return Err(PoolRpcAdapterErrorV1::UnsupportedPoolInstruction);
    };

    let first_id = DepositEventIdV1::new(
        transaction.point,
        transaction.transaction_signature,
        instruction_index,
        0,
    )
    .map_err(|_| PoolRpcAdapterErrorV1::EventIdentity)?;
    let mut outputs = vec![AuthenticatedTransitionOutputV1 {
        id: first_id,
        transition_kind: receipt.transition_kind,
        role: if receipt.transition_kind == PoolV1TransitionKind::PrivateTransfer {
            TransitionOutputRoleV1::Recipient
        } else {
            TransitionOutputRoleV1::Change
        },
        leaf_index: receipt.first_leaf_index,
        root_sequence: receipt.first_leaf_index.saturating_add(1),
        commitment: first_commitment,
        expected_root: (second_commitment.is_none())
            .then_some(encode_digest_canonical(&receipt.root)),
    }];
    if let Some(commitment) = second_commitment {
        outputs.push(AuthenticatedTransitionOutputV1 {
            id: DepositEventIdV1::new(
                transaction.point,
                transaction.transaction_signature,
                instruction_index,
                1,
            )
            .map_err(|_| PoolRpcAdapterErrorV1::EventIdentity)?,
            transition_kind: receipt.transition_kind,
            role: TransitionOutputRoleV1::Change,
            leaf_index: receipt.second_leaf_index,
            root_sequence: receipt.second_leaf_index.saturating_add(1),
            commitment,
            expected_root: Some(encode_digest_canonical(&receipt.root)),
        });
    }
    Ok(AuthenticatedPoolInvocationV1::Transition(
        AuthenticatedTransitionV1 {
            receipt,
            outputs,
            authenticated_transport,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rpc_adapter::{ResolvedRpcInstructionV1, ResolvedRpcReturnDataV1};
    use aspis_pool::{
        encode_withdrawal_instruction_v1, instruction::encode_transition_receipt_v1,
        WithdrawalStatementV1,
    };
    use aspis_statement::{pool_v1::HistoricalAnchorEnvelopeV1, poseidon2::Digest};

    use crate::transaction_builder::{
        build_prepare_withdrawal_instruction_v1, PreparedSettlementRouteAccountsV1,
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    #[test]
    fn transition_receipt_decoder_rejects_trailing_reserved_and_noncanonical_bytes() {
        let receipt = TransitionReceiptV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: [1; 32],
            nullifier: digest(10),
            first_output: digest(20),
            second_output_or_destination: encode_digest_canonical(&digest(30)),
            withdrawal_amount: 0,
            first_leaf_index: 7,
            second_leaf_index: 8,
            root_sequence: 9,
            root: digest(40),
        };
        let canonical = encode_transition_receipt_v1(&receipt).unwrap();
        assert_eq!(decode_transition_receipt_v1(&canonical), Ok(receipt));
        let mut trailing = canonical.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_transition_receipt_v1(&trailing),
            Err(PoolRpcAdapterErrorV1::WrongReceiptLength)
        );
        let mut reserved = canonical;
        reserved[140] = 1;
        assert_eq!(
            decode_transition_receipt_v1(&reserved),
            Err(PoolRpcAdapterErrorV1::NonZeroReserved)
        );
        let mut noncanonical = canonical;
        noncanonical[40..44].copy_from_slice(&aspis_core::field::P.to_le_bytes());
        assert_eq!(
            decode_transition_receipt_v1(&noncanonical),
            Err(PoolRpcAdapterErrorV1::NonCanonicalDigest)
        );
    }

    #[test]
    fn withdrawal_transport_requires_exact_instruction_receipt_and_identity() {
        let program_id = [0x91; 32];
        let program_key = Pubkey::new_from_array(program_id);
        let mint = Pubkey::new_from_array([3; 32]);
        let pool = pool_v1_state_address(&program_key, &mint).0;
        let vault = pool_v1_vault_token_account_address(&program_key, &pool).0;
        let identity = DepositScanIdentityV1::new(
            pool.to_bytes(),
            [2; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap();
        let binding = DepositRpcBindingV1::new(program_id).unwrap();
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: *identity.pool(),
            deployment_domain: *identity.deployment_domain(),
            anchor_sequence: 7,
            anchor_root: digest(50),
            nullifier: digest(60),
            verifier_profile: [5; 32],
            verifier_release: [6; 32],
        };
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(identity.asset_id()),
            amount: 25,
            destination_token_account: [7; 32],
            change_commitment: digest(70),
        };
        let instruction_wire = encode_withdrawal_instruction_v1(&envelope, &statement).unwrap();
        let receipt = TransitionReceiptV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: statement.pool,
            nullifier: statement.nullifier,
            first_output: statement.change_commitment,
            second_output_or_destination: statement.destination_token_account,
            withdrawal_amount: statement.amount,
            first_leaf_index: 11,
            second_leaf_index: 0,
            root_sequence: 12,
            root: digest(80),
        };
        let return_wire = encode_transition_receipt_v1(&receipt).unwrap();
        let instructions = [ResolvedRpcInstructionV1 {
            program_id,
            account_keys: &[],
            data: &instruction_wire,
        }];
        let transaction = FinalizedRpcTransactionV1 {
            point: crate::scan_state::FinalizedChainPointV1::new(42, [8; 32]).unwrap(),
            transaction_signature: [9; 64],
            succeeded: true,
            top_level_instructions: &instructions,
            return_data: Some(crate::rpc_adapter::ResolvedRpcReturnDataV1 {
                program_id,
                data: &return_wire,
            }),
        };

        let authenticated =
            authenticate_finalized_rpc_pool_v1(&binding, &identity, 11, &transaction).unwrap();
        let AuthenticatedPoolInvocationV1::Transition(authenticated) = authenticated else {
            panic!("withdrawal must authenticate as a transition");
        };
        assert_eq!(authenticated.receipt, receipt);
        assert_eq!(authenticated.outputs.len(), 1);
        assert_eq!(
            authenticated.outputs[0].role,
            TransitionOutputRoleV1::Change
        );
        assert_eq!(authenticated.outputs[0].leaf_index, 11);
        assert_eq!(authenticated.outputs[0].root_sequence, 12);
        assert_eq!(
            authenticated.outputs[0].expected_root,
            Some(encode_digest_canonical(&receipt.root))
        );

        let mut mismatched_wire = return_wire;
        mismatched_wire[136..140].copy_from_slice(&(statement.amount + 1).to_le_bytes());
        let mismatched_transaction = FinalizedRpcTransactionV1 {
            return_data: Some(crate::rpc_adapter::ResolvedRpcReturnDataV1 {
                program_id,
                data: &mismatched_wire,
            }),
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_pool_v1(&binding, &identity, 11, &mismatched_transaction,)
                .err(),
            Some(PoolRpcAdapterErrorV1::ReceiptInstructionMismatch)
        );
    }

    #[test]
    fn prepared_settlement_transport_exposes_exact_plan_and_rejects_alias_or_return_data() {
        let program_id = [0x91; 32];
        let program_key = Pubkey::new_from_array(program_id);
        let mint = Pubkey::new_from_array([3; 32]);
        let pool = pool_v1_state_address(&program_key, &mint).0;
        let vault = pool_v1_vault_token_account_address(&program_key, &pool).0;
        let identity = DepositScanIdentityV1::new(
            pool.to_bytes(),
            [2; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap();
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: *identity.pool(),
            deployment_domain: *identity.deployment_domain(),
            anchor_sequence: 7,
            anchor_root: digest(50),
            nullifier: digest(60),
            verifier_profile: [5; 32],
            verifier_release: [6; 32],
        };
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(identity.asset_id()),
            amount: 25,
            destination_token_account: [7; 32],
            change_commitment: digest(70),
        };
        let instruction = build_prepare_withdrawal_instruction_v1(
            program_key,
            7,
            &envelope,
            &statement,
            100,
            120,
            PreparedSettlementRouteAccountsV1 {
                plan_authority: Pubkey::new_from_array([8; 32]),
                registry_program: Pubkey::new_from_array([9; 32]),
                authorization_receipt: Pubkey::new_from_array([10; 32]),
            },
        )
        .unwrap();
        let account_keys: Vec<_> = instruction
            .accounts
            .iter()
            .map(|account| account.pubkey.to_bytes())
            .collect();
        let instructions = [ResolvedRpcInstructionV1 {
            program_id,
            account_keys: &account_keys,
            data: &instruction.data,
        }];
        let transaction = FinalizedRpcTransactionV1 {
            point: crate::scan_state::FinalizedChainPointV1::new(42, [8; 32]).unwrap(),
            transaction_signature: [9; 64],
            succeeded: true,
            top_level_instructions: &instructions,
            return_data: None,
        };
        let binding = DepositRpcBindingV1::new(program_id).unwrap();
        let authenticated =
            authenticate_finalized_rpc_pool_v1(&binding, &identity, 7, &transaction).unwrap();
        let AuthenticatedPoolInvocationV1::PreparedSettlement(prepared) = authenticated else {
            panic!("ASPP must authenticate as a prepared settlement");
        };
        assert_eq!(prepared.transition_kind, PoolV1TransitionKind::Withdrawal);
        assert_eq!(prepared.source_root_sequence, 7);
        assert_eq!(prepared.core_plan, account_keys[6]);
        assert_eq!(prepared.rollover_page, None);
        assert_eq!(prepared.rollover_shard, None);

        let rollover_sequence = aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_CAPACITY as u64 - 1;
        let rollover_envelope = HistoricalAnchorEnvelopeV1 {
            anchor_sequence: rollover_sequence,
            ..envelope
        };
        let rollover_statement = WithdrawalStatementV1 {
            anchor_sequence: rollover_sequence,
            ..statement
        };
        let rollover_instruction = build_prepare_withdrawal_instruction_v1(
            program_key,
            rollover_sequence,
            &rollover_envelope,
            &rollover_statement,
            100,
            120,
            PreparedSettlementRouteAccountsV1 {
                plan_authority: Pubkey::new_from_array([8; 32]),
                registry_program: Pubkey::new_from_array([9; 32]),
                authorization_receipt: Pubkey::new_from_array([10; 32]),
            },
        )
        .unwrap();
        let rollover_keys: Vec<_> = rollover_instruction
            .accounts
            .iter()
            .map(|account| account.pubkey.to_bytes())
            .collect();
        let rollover_instructions = [ResolvedRpcInstructionV1 {
            program_id,
            account_keys: &rollover_keys,
            data: &rollover_instruction.data,
        }];
        let rollover_transaction = FinalizedRpcTransactionV1 {
            point: crate::scan_state::FinalizedChainPointV1::new(43, [11; 32]).unwrap(),
            transaction_signature: [12; 64],
            succeeded: true,
            top_level_instructions: &rollover_instructions,
            return_data: None,
        };
        let AuthenticatedPoolInvocationV1::PreparedSettlement(rollover) =
            authenticate_finalized_rpc_pool_v1(
                &binding,
                &identity,
                rollover_sequence,
                &rollover_transaction,
            )
            .unwrap()
        else {
            panic!("rollover ASPP must authenticate as a prepared settlement");
        };
        assert_eq!(rollover.rollover_page, Some(rollover_keys[3]));
        assert_eq!(rollover.core_plan, rollover_keys[7]);
        assert_eq!(rollover.rollover_shard, Some(rollover_keys[8]));

        let nonempty = [1u8];
        let unexpected_return = FinalizedRpcTransactionV1 {
            return_data: Some(ResolvedRpcReturnDataV1 {
                program_id,
                data: &nonempty,
            }),
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_pool_v1(&binding, &identity, 7, &unexpected_return).err(),
            Some(PoolRpcAdapterErrorV1::UnexpectedReturnData)
        );

        let mut aliased_keys = account_keys.clone();
        aliased_keys[3] = aliased_keys[2];
        let aliased_instruction = [ResolvedRpcInstructionV1 {
            program_id,
            account_keys: &aliased_keys,
            data: &instruction.data,
        }];
        let aliased = FinalizedRpcTransactionV1 {
            top_level_instructions: &aliased_instruction,
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_pool_v1(&binding, &identity, 7, &aliased).err(),
            Some(PoolRpcAdapterErrorV1::InstructionAccountAlias)
        );

        let failed = FinalizedRpcTransactionV1 {
            succeeded: false,
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_pool_v1(&binding, &identity, 7, &failed).err(),
            Some(PoolRpcAdapterErrorV1::TransactionFailed)
        );
    }
}
