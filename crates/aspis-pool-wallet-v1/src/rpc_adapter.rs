//! Strict adapter from resolved Solana RPC transaction data to the Pool V1
//! scanner.
//!
//! Solana return data is one transaction-global value owned by its most recent
//! setter. This adapter therefore accepts a deposit only when the pinned Pool
//! program occurs exactly once as a top-level instruction, that instruction is
//! last, its complete V1 wire is canonical, the transaction succeeded, and
//! the return-data owner is the same pinned program. RPC base58/base64 decoding,
//! account-key resolution and finalized commitment are explicit caller
//! boundaries; this module consumes their exact decoded bytes.

use aspis_pool::{pool_v1_state_address, pool_v1_vault_token_account_address};
use aspis_statement::{
    decode_digest_canonical,
    pool_v1::{pool_v1_note_commitment, DepositEventV1, POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES},
    poseidon2::Digest,
    VALUE_LIMIT,
};
use solana_program::pubkey::Pubkey;

use crate::{
    scan_state::{
        decode_deposit_event_record_v1, DepositEventIdV1, DepositEventRecordErrorV1,
        DepositScanIdentityV1, DepositScanOutcomeV1, FinalizedChainPointV1,
        FinalizedDepositRecordV1, LocalOwnerKeyStoreV1, ScanStateErrorV1, ScanStateV1,
    },
    ViewingSecretKeyV1,
};

pub const POOL_V1_DEPOSIT_INSTRUCTION_MAGIC: [u8; 4] = *b"ASDI";
pub const POOL_V1_DEPOSIT_INSTRUCTION_VERSION: u8 = 1;
pub const POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES: usize = 80;
pub const POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES: usize =
    match POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
        .checked_add(POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES)
    {
        Some(length) => length,
        None => panic!("Pool V1 deposit instruction size overflow"),
    };

const INSTRUCTION_OWNER_KEY_OFFSET: usize = 8;
const INSTRUCTION_AMOUNT_OFFSET: usize = 40;
const INSTRUCTION_SALT_OFFSET: usize = 48;
const INSTRUCTION_PAYLOAD_OFFSET: usize = POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DepositInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    InvalidAmount,
    InvalidPayloadLength,
    NonCanonicalDigest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecodedDepositInstructionV1<'a> {
    pub owner_key: Digest,
    pub amount: u32,
    pub salt: Digest,
    pub encrypted_note_payload: &'a [u8],
}

/// Decode the exact instruction wire accepted by the Pool deposit transport.
/// The declared payload length must consume the complete byte slice.
pub fn decode_deposit_instruction_v1(
    bytes: &[u8],
) -> Result<DecodedDepositInstructionV1<'_>, DepositInstructionFormatErrorV1> {
    if bytes.len() < POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
        || bytes.len() > POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES
    {
        return Err(DepositInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_DEPOSIT_INSTRUCTION_MAGIC {
        return Err(DepositInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_DEPOSIT_INSTRUCTION_VERSION {
        return Err(DepositInstructionFormatErrorV1::WrongVersion);
    }
    if bytes[5] != 0 || bytes[44..48] != [0u8; 4] {
        return Err(DepositInstructionFormatErrorV1::NonZeroReserved);
    }

    let declared_payload_length = usize::from(u16::from_le_bytes(
        bytes[6..8]
            .try_into()
            .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?,
    ));
    if declared_payload_length > POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES {
        return Err(DepositInstructionFormatErrorV1::InvalidPayloadLength);
    }
    let expected_length = INSTRUCTION_PAYLOAD_OFFSET
        .checked_add(declared_payload_length)
        .ok_or(DepositInstructionFormatErrorV1::WrongLength)?;
    if bytes.len() != expected_length {
        return Err(DepositInstructionFormatErrorV1::WrongLength);
    }

    let owner_key_bytes: &[u8; 32] = bytes[INSTRUCTION_OWNER_KEY_OFFSET..INSTRUCTION_AMOUNT_OFFSET]
        .try_into()
        .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?;
    let salt_bytes: &[u8; 32] = bytes[INSTRUCTION_SALT_OFFSET..INSTRUCTION_PAYLOAD_OFFSET]
        .try_into()
        .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?;
    let owner_key = decode_digest_canonical(owner_key_bytes)
        .map_err(|_| DepositInstructionFormatErrorV1::NonCanonicalDigest)?;
    let salt = decode_digest_canonical(salt_bytes)
        .map_err(|_| DepositInstructionFormatErrorV1::NonCanonicalDigest)?;
    let amount = u32::from_le_bytes(
        bytes[INSTRUCTION_AMOUNT_OFFSET..44]
            .try_into()
            .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?,
    );
    if amount == 0 || amount >= VALUE_LIMIT {
        return Err(DepositInstructionFormatErrorV1::InvalidAmount);
    }

    Ok(DecodedDepositInstructionV1 {
        owner_key,
        amount,
        salt,
        encrypted_note_payload: &bytes[INSTRUCTION_PAYLOAD_OFFSET..],
    })
}

/// Deployment-specific trust root. There is deliberately no default program
/// id: the caller must pin the deployed Pool executable explicitly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositRpcBindingV1 {
    program_id: [u8; 32],
}

impl DepositRpcBindingV1 {
    pub fn new(program_id: [u8; 32]) -> Result<Self, DepositRpcAdapterErrorV1> {
        if program_id == [0u8; 32] {
            return Err(DepositRpcAdapterErrorV1::InvalidProgramBinding);
        }
        Ok(Self { program_id })
    }

    pub fn program_id(&self) -> &[u8; 32] {
        &self.program_id
    }
}

/// One top-level compiled instruction after every RPC account-key index has
/// been resolved. Retaining the ordered account keys lets non-returning Pool
/// instructions authenticate deterministic plan PDAs instead of trusting only
/// their instruction bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedRpcInstructionV1<'a> {
    pub program_id: [u8; 32],
    pub account_keys: &'a [[u8; 32]],
    pub data: &'a [u8],
}

/// Solana transaction `meta.returnData` after base64 decoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedRpcReturnDataV1<'a> {
    pub program_id: [u8; 32],
    pub data: &'a [u8],
}

/// Minimal finalized transaction view required by the adapter. `succeeded`
/// must be derived from `meta.err == null`; a failed transaction is rejected
/// before any scan-state mutation even when RPC also reports return data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedRpcTransactionV1<'a> {
    pub point: FinalizedChainPointV1,
    pub transaction_signature: [u8; 64],
    pub succeeded: bool,
    pub top_level_instructions: &'a [ResolvedRpcInstructionV1<'a>],
    pub return_data: Option<ResolvedRpcReturnDataV1<'a>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DepositRpcAdapterErrorV1 {
    InvalidProgramBinding,
    TransactionFailed,
    MissingTopLevelInstruction,
    DepositInstructionNotFinal,
    AdditionalPoolInstruction,
    WrongInstructionProgram,
    InstructionIndexOverflow,
    DepositInstruction(DepositInstructionFormatErrorV1),
    MissingReturnData,
    WrongReturnDataProgram,
    DepositRecord(DepositEventRecordErrorV1),
    ReceiptIdentityMismatch,
    InstructionEventMismatch,
    EventIdentity(ScanStateErrorV1),
    ScanState(ScanStateErrorV1),
}

fn event_matches_instruction_and_identity_v1(
    instruction: &DecodedDepositInstructionV1<'_>,
    event: &DepositEventV1<'_>,
    identity: &DepositScanIdentityV1,
) -> bool {
    if event.receipt.pool != *identity.pool()
        || event.receipt.asset_mint != *identity.asset_mint()
        || event.receipt.vault_token_account != *identity.vault_token_account()
    {
        return false;
    }
    let expected_commitment = pool_v1_note_commitment(
        &instruction.owner_key,
        instruction.amount,
        aspis_core::field::M31(identity.asset_id()),
        &instruction.salt,
    );
    event.receipt.amount == instruction.amount
        && event.receipt.note_commitment == expected_commitment
        && event.encrypted_note_payload == instruction.encrypted_note_payload
}

/// Authenticate a resolved, externally-finalized RPC transaction and return
/// the exact record/id accepted by [`ScanStateV1`]. This function is read-only.
pub fn authenticate_finalized_rpc_deposit_v1<'a>(
    binding: &DepositRpcBindingV1,
    identity: &DepositScanIdentityV1,
    transaction: &'a FinalizedRpcTransactionV1<'a>,
) -> Result<FinalizedDepositRecordV1<'a>, DepositRpcAdapterErrorV1> {
    if !transaction.succeeded {
        return Err(DepositRpcAdapterErrorV1::TransactionFailed);
    }
    let program_id = Pubkey::new_from_array(*binding.program_id());
    let mint = Pubkey::new_from_array(*identity.asset_mint());
    let expected_pool = pool_v1_state_address(&program_id, &mint).0;
    let expected_vault = pool_v1_vault_token_account_address(&program_id, &expected_pool).0;
    if expected_pool.to_bytes() != *identity.pool()
        || expected_vault.to_bytes() != *identity.vault_token_account()
    {
        return Err(DepositRpcAdapterErrorV1::ReceiptIdentityMismatch);
    }
    let final_index = transaction
        .top_level_instructions
        .len()
        .checked_sub(1)
        .ok_or(DepositRpcAdapterErrorV1::MissingTopLevelInstruction)?;
    let final_instruction = &transaction.top_level_instructions[final_index];
    if final_instruction.program_id != binding.program_id {
        return Err(
            if transaction
                .top_level_instructions
                .iter()
                .any(|instruction| instruction.program_id == binding.program_id)
            {
                DepositRpcAdapterErrorV1::DepositInstructionNotFinal
            } else {
                DepositRpcAdapterErrorV1::WrongInstructionProgram
            },
        );
    }
    if transaction.top_level_instructions[..final_index]
        .iter()
        .any(|instruction| instruction.program_id == binding.program_id)
    {
        return Err(DepositRpcAdapterErrorV1::AdditionalPoolInstruction);
    }
    let instruction_index = u16::try_from(final_index)
        .map_err(|_| DepositRpcAdapterErrorV1::InstructionIndexOverflow)?;
    let decoded_instruction = decode_deposit_instruction_v1(final_instruction.data)
        .map_err(DepositRpcAdapterErrorV1::DepositInstruction)?;

    let return_data = transaction
        .return_data
        .ok_or(DepositRpcAdapterErrorV1::MissingReturnData)?;
    if return_data.program_id != binding.program_id {
        return Err(DepositRpcAdapterErrorV1::WrongReturnDataProgram);
    }
    let event = decode_deposit_event_record_v1(return_data.data)
        .map_err(DepositRpcAdapterErrorV1::DepositRecord)?;
    if event.receipt.pool != *identity.pool()
        || event.receipt.asset_mint != *identity.asset_mint()
        || event.receipt.vault_token_account != *identity.vault_token_account()
    {
        return Err(DepositRpcAdapterErrorV1::ReceiptIdentityMismatch);
    }
    if !event_matches_instruction_and_identity_v1(&decoded_instruction, &event, identity) {
        return Err(DepositRpcAdapterErrorV1::InstructionEventMismatch);
    }

    let id = DepositEventIdV1::new(
        transaction.point,
        transaction.transaction_signature,
        instruction_index,
        0,
    )
    .map_err(DepositRpcAdapterErrorV1::EventIdentity)?;
    Ok(FinalizedDepositRecordV1::new(id, return_data.data))
}

/// Authenticate and ingest exactly one successful finalized RPC deposit. All
/// transport failures occur before the mutable scan-state ingestion call.
pub fn ingest_finalized_rpc_deposit_v1(
    state: &mut ScanStateV1,
    binding: &DepositRpcBindingV1,
    transaction: &FinalizedRpcTransactionV1<'_>,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> Result<DepositScanOutcomeV1, DepositRpcAdapterErrorV1> {
    let observation =
        authenticate_finalized_rpc_deposit_v1(binding, state.identity(), transaction)?;
    state
        .ingest_finalized_deposit_v1(observation, viewing_secret, local_keys)
        .map_err(DepositRpcAdapterErrorV1::ScanState)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{
        encode_digest_canonical,
        pool_v1::{DepositEventV1, DepositReceiptV1},
        poseidon2::Digest,
    };

    use crate::{
        derive_viewing_keypair_v1,
        scan_state::{
            encode_deposit_event_record_v1, DepositScanIdentityV1, FinalizedBlockV1,
            LocalOwnerKeyStoreV1, ScanStateV1,
        },
    };

    const PROGRAM_ID: [u8; 32] = [0x99; 32];

    struct EmptyKeyStore;

    impl LocalOwnerKeyStoreV1 for EmptyKeyStore {
        fn contains_owner_key_v1(&self, _: &[u8; 32]) -> bool {
            false
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn digest_bytes(seed: u32) -> [u8; 32] {
        encode_digest_canonical(&digest(seed))
    }

    fn identity() -> DepositScanIdentityV1 {
        let program_id = Pubkey::new_from_array(PROGRAM_ID);
        let mint = Pubkey::new_from_array([0x33; 32]);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let vault = pool_v1_vault_token_account_address(&program_id, &pool).0;
        DepositScanIdentityV1::new(
            pool.to_bytes(),
            [0x22; 32],
            mint.to_bytes(),
            vault.to_bytes(),
            9,
        )
        .unwrap()
    }

    fn point(slot: u64, byte: u8) -> FinalizedChainPointV1 {
        FinalizedChainPointV1::new(slot, [byte; 32]).unwrap()
    }

    fn instruction_bytes(payload: &[u8]) -> Vec<u8> {
        let owner_key = digest(10);
        let salt = digest(100);
        let mut bytes = vec![0u8; POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES + payload.len()];
        bytes[..4].copy_from_slice(&POOL_V1_DEPOSIT_INSTRUCTION_MAGIC);
        bytes[4] = POOL_V1_DEPOSIT_INSTRUCTION_VERSION;
        bytes[6..8].copy_from_slice(&(payload.len() as u16).to_le_bytes());
        bytes[8..40].copy_from_slice(&encode_digest_canonical(&owner_key));
        bytes[40..44].copy_from_slice(&77u32.to_le_bytes());
        bytes[48..80].copy_from_slice(&encode_digest_canonical(&salt));
        bytes[80..].copy_from_slice(payload);
        bytes
    }

    fn return_record(payload: &[u8]) -> Vec<u8> {
        let receipt = DepositReceiptV1 {
            pool: *identity().pool(),
            asset_mint: *identity().asset_mint(),
            source_token_account: [0x55; 32],
            vault_token_account: *identity().vault_token_account(),
            amount: 77,
            encrypted_note_payload_bytes: payload.len() as u16,
            note_commitment: pool_v1_note_commitment(&digest(10), 77, M31(9), &digest(100)),
            leaf_index: 7,
            root_sequence: 8,
            root: digest(700),
        };
        encode_deposit_event_record_v1(&DepositEventV1 {
            receipt,
            encrypted_note_payload: payload,
        })
        .unwrap()
    }

    fn anchored_state() -> ScanStateV1 {
        ScanStateV1::new(identity(), point(100, 0xa0), 7, digest_bytes(600)).unwrap()
    }

    #[test]
    fn strict_rpc_binding_rejects_wrong_program_instruction_and_trailing_data() {
        let binding = DepositRpcBindingV1::new(PROGRAM_ID).unwrap();
        let payload = [0xaa, 0xbb, 0xcc];
        let instruction_data = instruction_bytes(&payload);
        let record = return_record(&payload);
        let block_point = point(101, 0xa1);

        let wrong_program = [ResolvedRpcInstructionV1 {
            program_id: [0x98; 32],
            account_keys: &[],
            data: &instruction_data,
        }];
        let transaction = FinalizedRpcTransactionV1 {
            point: block_point,
            transaction_signature: [0x77; 64],
            succeeded: true,
            top_level_instructions: &wrong_program,
            return_data: Some(ResolvedRpcReturnDataV1 {
                program_id: PROGRAM_ID,
                data: &record,
            }),
        };
        assert_eq!(
            authenticate_finalized_rpc_deposit_v1(&binding, &identity(), &transaction),
            Err(DepositRpcAdapterErrorV1::WrongInstructionProgram)
        );

        let mut wrong_version_data = instruction_data.clone();
        wrong_version_data[4] = 2;
        let wrong_version = [ResolvedRpcInstructionV1 {
            program_id: PROGRAM_ID,
            account_keys: &[],
            data: &wrong_version_data,
        }];
        let transaction = FinalizedRpcTransactionV1 {
            top_level_instructions: &wrong_version,
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_deposit_v1(&binding, &identity(), &transaction),
            Err(DepositRpcAdapterErrorV1::DepositInstruction(
                DepositInstructionFormatErrorV1::WrongVersion
            ))
        );

        let mut trailing_instruction_data = instruction_data.clone();
        trailing_instruction_data.push(0);
        let trailing_instruction = [ResolvedRpcInstructionV1 {
            program_id: PROGRAM_ID,
            account_keys: &[],
            data: &trailing_instruction_data,
        }];
        let transaction = FinalizedRpcTransactionV1 {
            top_level_instructions: &trailing_instruction,
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_deposit_v1(&binding, &identity(), &transaction),
            Err(DepositRpcAdapterErrorV1::DepositInstruction(
                DepositInstructionFormatErrorV1::WrongLength
            ))
        );

        let canonical_instruction = [ResolvedRpcInstructionV1 {
            program_id: PROGRAM_ID,
            account_keys: &[],
            data: &instruction_data,
        }];
        let transaction = FinalizedRpcTransactionV1 {
            top_level_instructions: &canonical_instruction,
            return_data: Some(ResolvedRpcReturnDataV1 {
                program_id: [0x98; 32],
                data: &record,
            }),
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_deposit_v1(&binding, &identity(), &transaction),
            Err(DepositRpcAdapterErrorV1::WrongReturnDataProgram)
        );

        let mut trailing_record = record.clone();
        trailing_record.push(0);
        let transaction = FinalizedRpcTransactionV1 {
            top_level_instructions: &canonical_instruction,
            return_data: Some(ResolvedRpcReturnDataV1 {
                program_id: PROGRAM_ID,
                data: &trailing_record,
            }),
            ..transaction
        };
        assert!(matches!(
            authenticate_finalized_rpc_deposit_v1(&binding, &identity(), &transaction),
            Err(DepositRpcAdapterErrorV1::DepositRecord(_))
        ));
    }

    #[test]
    fn pool_deposit_must_be_the_only_pool_instruction_and_final() {
        let binding = DepositRpcBindingV1::new(PROGRAM_ID).unwrap();
        let payload = [0xaa];
        let instruction_data = instruction_bytes(&payload);
        let record = return_record(&payload);
        let other_instruction_data = [7u8];
        let non_final = [
            ResolvedRpcInstructionV1 {
                program_id: PROGRAM_ID,
                account_keys: &[],
                data: &instruction_data,
            },
            ResolvedRpcInstructionV1 {
                program_id: [0x88; 32],
                account_keys: &[],
                data: &other_instruction_data,
            },
        ];
        let transaction = FinalizedRpcTransactionV1 {
            point: point(101, 0xa1),
            transaction_signature: [0x77; 64],
            succeeded: true,
            top_level_instructions: &non_final,
            return_data: Some(ResolvedRpcReturnDataV1 {
                program_id: PROGRAM_ID,
                data: &record,
            }),
        };
        assert_eq!(
            authenticate_finalized_rpc_deposit_v1(&binding, &identity(), &transaction),
            Err(DepositRpcAdapterErrorV1::DepositInstructionNotFinal)
        );

        let repeated_pool = [
            ResolvedRpcInstructionV1 {
                program_id: PROGRAM_ID,
                account_keys: &[],
                data: &instruction_data,
            },
            ResolvedRpcInstructionV1 {
                program_id: PROGRAM_ID,
                account_keys: &[],
                data: &instruction_data,
            },
        ];
        let transaction = FinalizedRpcTransactionV1 {
            top_level_instructions: &repeated_pool,
            ..transaction
        };
        assert_eq!(
            authenticate_finalized_rpc_deposit_v1(&binding, &identity(), &transaction),
            Err(DepositRpcAdapterErrorV1::AdditionalPoolInstruction)
        );
    }

    #[test]
    fn failed_transaction_never_ingests_and_success_can_be_rolled_back_exactly() {
        let binding = DepositRpcBindingV1::new(PROGRAM_ID).unwrap();
        let payload = [0xaa, 0xbb, 0xcc];
        let instruction_data = instruction_bytes(&payload);
        let record = return_record(&payload);
        let instructions = [ResolvedRpcInstructionV1 {
            program_id: PROGRAM_ID,
            account_keys: &[],
            data: &instruction_data,
        }];
        let anchor_state = anchored_state();
        let anchor = anchor_state.anchor();
        let child = FinalizedBlockV1::new(point(101, 0xa1), anchor).unwrap();
        let mut state = anchor_state.clone();
        state.advance_finalized_block_v1(child).unwrap();
        let before_failed_transaction = state.clone();
        let (viewing_secret, _) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let keys = EmptyKeyStore;
        let failed_transaction = FinalizedRpcTransactionV1 {
            point: child.point(),
            transaction_signature: [0x77; 64],
            succeeded: false,
            top_level_instructions: &instructions,
            return_data: Some(ResolvedRpcReturnDataV1 {
                program_id: PROGRAM_ID,
                data: &record,
            }),
        };

        assert_eq!(
            ingest_finalized_rpc_deposit_v1(
                &mut state,
                &binding,
                &failed_transaction,
                &viewing_secret,
                &keys,
            )
            .unwrap_err(),
            DepositRpcAdapterErrorV1::TransactionFailed
        );
        assert_eq!(state, before_failed_transaction);

        let successful_transaction = FinalizedRpcTransactionV1 {
            succeeded: true,
            ..failed_transaction
        };
        let outcome = ingest_finalized_rpc_deposit_v1(
            &mut state,
            &binding,
            &successful_transaction,
            &viewing_secret,
            &keys,
        )
        .unwrap();
        assert!(matches!(
            outcome,
            DepositScanOutcomeV1::InvalidEncryptedPayload(_)
        ));
        assert_eq!(state.next_leaf_index(), 8);
        assert_eq!(state.retained_event_count(), 1);

        let rollback = state.rollback_to_v1(anchor).unwrap();
        assert_eq!(rollback.removed_events.len(), 1);
        assert_eq!(rollback.removed_events[0].instruction_index(), 0);
        assert_eq!(rollback.removed_events[0].event_index(), 0);
        assert_eq!(state, anchor_state);
    }
}
