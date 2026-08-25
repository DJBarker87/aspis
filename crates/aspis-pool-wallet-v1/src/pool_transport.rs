//! Exact successful Pool V1 top-level instruction/return-data authentication.
//!
//! Solana return data is transaction-global, so a wallet accepts it only for
//! one unique, final top-level invocation of the deployment-pinned Pool. This
//! module extends the original deposit adapter to initialization and the two
//! proof-authorized transitions without accepting inner-instruction guesses.

use aspis_core::field::M31;
use aspis_pool::{
    decode_initialize_instruction_v1, decode_private_transfer_instruction_v1,
    decode_withdrawal_instruction_v1, instruction::encode_transition_receipt_v1,
    pool_v1_root_page_address, pool_v1_state_address, pool_v1_vault_token_account_address,
    TransitionReceiptV1, POOL_V1_INITIALIZATION_RECEIPT_BYTES,
    POOL_V1_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC,
    POOL_V1_TRANSITION_RECEIPT_BYTES, POOL_V1_TRANSITION_RECEIPT_MAGIC,
    POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC,
};
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{PoolV1TransitionKind, POOL_V1_DIGEST_ENCODING_VERSION},
};
use solana_program::pubkey::Pubkey;

use crate::{
    rpc_adapter::{
        authenticate_finalized_rpc_deposit_v1, DepositRpcAdapterErrorV1, DepositRpcBindingV1,
        FinalizedRpcTransactionV1,
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

pub enum AuthenticatedPoolInvocationV1<'a> {
    Initialization(InitializationReceiptV1),
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
    Deposit(DepositRpcAdapterErrorV1),
    PoolInstruction(aspis_pool::PoolInstructionFormatErrorV1),
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

/// Authenticate exactly one successful final top-level Pool invocation.
pub fn authenticate_finalized_rpc_pool_v1<'a>(
    binding: &DepositRpcBindingV1,
    identity: &DepositScanIdentityV1,
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
    use crate::rpc_adapter::ResolvedRpcInstructionV1;
    use aspis_pool::{
        encode_withdrawal_instruction_v1, instruction::encode_transition_receipt_v1,
        WithdrawalStatementV1,
    };
    use aspis_statement::{pool_v1::HistoricalAnchorEnvelopeV1, poseidon2::Digest};

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
            authenticate_finalized_rpc_pool_v1(&binding, &identity, &transaction).unwrap();
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
            authenticate_finalized_rpc_pool_v1(&binding, &identity, &mismatched_transaction,).err(),
            Some(PoolRpcAdapterErrorV1::ReceiptInstructionMismatch)
        );
    }
}
