//! Canonical Pool V1 deposit instruction and return-data transport.
//!
//! The native Pool entrypoint passes its runtime `program_id` and exact
//! state/token account groups here. The successful path sets one Pool-owned
//! Solana return-data value containing exactly
//! `DepositReceiptV1 || encrypted_note_payload`.
//! Return data is never set when instruction decoding, the deposit kernel, or
//! event encoding fails.

use aspis_core::field::P;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        encode_deposit_receipt_v1, validate_deposit_event_v1, DepositEventV1,
        PoolV1DepositFormatError, POOL_V1_DEPOSIT_RECEIPT_BYTES, POOL_V1_DEPOSIT_RETURN_MAX_BYTES,
        POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES,
    },
    VALUE_LIMIT,
};
use solana_program::{
    account_info::AccountInfo, program, program_error::ProgramError, pubkey::Pubkey,
};

use crate::{
    apply_vault_backed_deposit_v1, deposit::apply_prevalidated_vault_backed_deposit_v1,
    state::CanonicalPoolStateV1, DepositRequestV1,
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

/// Fixed-capacity canonical instruction image. Only [`Self::as_bytes`] is part
/// of the wire; unused capacity is never serialized.
pub struct DepositInstructionDataV1 {
    bytes: [u8; POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES],
    length: usize,
}

impl DepositInstructionDataV1 {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.length]
    }
}

/// Fixed-capacity canonical Solana return-data image. Its exact serialized
/// length is the receipt-declared payload boundary, never the full capacity.
pub struct DepositEventReturnDataV1 {
    bytes: [u8; POOL_V1_DEPOSIT_RETURN_MAX_BYTES],
    length: usize,
}

impl DepositEventReturnDataV1 {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.length]
    }
}

fn digest_is_canonical(digest: &aspis_statement::Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

/// Encode the only accepted V1 deposit instruction image.
///
/// ```text
/// 0..4    magic ASDI
/// 4       version 1
/// 5       flags 0
/// 6..8    encrypted payload length u16 LE
/// 8..40   owner-key digest (canonical LE M31 limbs)
/// 40..44  amount u32 LE
/// 44..48  zero reserved
/// 48..80  salt digest (canonical LE M31 limbs)
/// 80..N   exact opaque encrypted-note payload
/// ```
pub fn encode_deposit_instruction_v1(
    request: &DepositRequestV1<'_>,
) -> Result<DepositInstructionDataV1, DepositInstructionFormatErrorV1> {
    if request.amount == 0 || request.amount >= VALUE_LIMIT {
        return Err(DepositInstructionFormatErrorV1::InvalidAmount);
    }
    if request.encrypted_note_payload.len() > POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES {
        return Err(DepositInstructionFormatErrorV1::InvalidPayloadLength);
    }
    if !digest_is_canonical(&request.owner_key) || !digest_is_canonical(&request.salt) {
        return Err(DepositInstructionFormatErrorV1::NonCanonicalDigest);
    }

    let length = INSTRUCTION_PAYLOAD_OFFSET
        .checked_add(request.encrypted_note_payload.len())
        .ok_or(DepositInstructionFormatErrorV1::WrongLength)?;
    let payload_length = u16::try_from(request.encrypted_note_payload.len())
        .map_err(|_| DepositInstructionFormatErrorV1::InvalidPayloadLength)?;
    let mut bytes = [0u8; POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_DEPOSIT_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_DEPOSIT_INSTRUCTION_VERSION;
    bytes[6..8].copy_from_slice(&payload_length.to_le_bytes());
    bytes[INSTRUCTION_OWNER_KEY_OFFSET..INSTRUCTION_AMOUNT_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&request.owner_key));
    bytes[INSTRUCTION_AMOUNT_OFFSET..44].copy_from_slice(&request.amount.to_le_bytes());
    bytes[INSTRUCTION_SALT_OFFSET..INSTRUCTION_PAYLOAD_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&request.salt));
    bytes[INSTRUCTION_PAYLOAD_OFFSET..length].copy_from_slice(request.encrypted_note_payload);
    Ok(DepositInstructionDataV1 { bytes, length })
}

/// Strictly decode one V1 deposit instruction. Truncation, trailing data,
/// unknown versions/flags and non-canonical field elements fail closed.
pub fn decode_deposit_instruction_v1(
    bytes: &[u8],
) -> Result<DepositRequestV1<'_>, DepositInstructionFormatErrorV1> {
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

    Ok(DepositRequestV1 {
        owner_key,
        amount,
        salt,
        encrypted_note_payload: &bytes[INSTRUCTION_PAYLOAD_OFFSET..],
    })
}

/// Encode the exact successful deposit return-data record.
pub fn encode_deposit_event_return_data_v1(
    event: &DepositEventV1<'_>,
) -> Result<DepositEventReturnDataV1, PoolV1DepositFormatError> {
    validate_deposit_event_v1(event)?;
    let receipt = encode_deposit_receipt_v1(&event.receipt)?;
    let length = POOL_V1_DEPOSIT_RECEIPT_BYTES
        .checked_add(event.encrypted_note_payload.len())
        .ok_or(PoolV1DepositFormatError::InvalidPayloadLength)?;
    let mut bytes = [0u8; POOL_V1_DEPOSIT_RETURN_MAX_BYTES];
    bytes[..POOL_V1_DEPOSIT_RECEIPT_BYTES].copy_from_slice(&receipt);
    bytes[POOL_V1_DEPOSIT_RECEIPT_BYTES..length].copy_from_slice(event.encrypted_note_payload);
    Ok(DepositEventReturnDataV1 { bytes, length })
}

fn execute_and_emit_deposit_v1<'payload, E, S>(
    execute: E,
    set_return_data: S,
) -> Result<(), ProgramError>
where
    E: FnOnce() -> Result<DepositEventV1<'payload>, ProgramError>,
    S: FnOnce(&[u8]),
{
    let event = execute()?;
    let return_data = encode_deposit_event_return_data_v1(&event)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    set_return_data(return_data.as_bytes());
    Ok(())
}

fn process_vault_backed_deposit_instruction_with_runtime_v1<'info, S>(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo<'info>],
    token_accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    set_return_data: S,
) -> Result<(), ProgramError>
where
    S: FnOnce(&[u8]),
{
    let request = decode_deposit_instruction_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    execute_and_emit_deposit_v1(
        || apply_vault_backed_deposit_v1(program_id, state_accounts, token_accounts, request),
        set_return_data,
    )
}

/// Decode, apply and expose one deposit event through Solana return data.
///
/// The native entrypoint supplies the reviewed account split and remains
/// responsible for deployment/client program-id pinning. The return-data call
/// is sequenced strictly after the full deposit kernel returns success.
pub fn process_vault_backed_deposit_instruction_v1<'info>(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo<'info>],
    token_accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
) -> Result<(), ProgramError> {
    process_vault_backed_deposit_instruction_with_runtime_v1(
        program_id,
        state_accounts,
        token_accounts,
        instruction_data,
        program::set_return_data,
    )
}

/// Emit the identical deposit result from the processor's already-decoded
/// instruction request and canonical Pool-state token.
pub(crate) fn process_prevalidated_vault_backed_deposit_v1<'payload, 'info>(
    program_id: &Pubkey,
    state_accounts: &[AccountInfo<'info>],
    token_accounts: &[AccountInfo<'info>],
    state: &CanonicalPoolStateV1,
    request: DepositRequestV1<'payload>,
) -> Result<(), ProgramError> {
    execute_and_emit_deposit_v1(
        || {
            apply_prevalidated_vault_backed_deposit_v1(
                program_id,
                state_accounts,
                token_accounts,
                state,
                request,
            )
        },
        program::set_return_data,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{pool_v1::DepositReceiptV1, poseidon2::Digest};
    use std::{cell::RefCell, vec::Vec};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn request<'a>(payload: &'a [u8]) -> DepositRequestV1<'a> {
        DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(100),
            encrypted_note_payload: payload,
        }
    }

    fn event<'a>(payload: &'a [u8]) -> DepositEventV1<'a> {
        DepositEventV1 {
            receipt: DepositReceiptV1 {
                pool: [1u8; 32],
                asset_mint: [2u8; 32],
                source_token_account: [3u8; 32],
                vault_token_account: [4u8; 32],
                amount: 77,
                encrypted_note_payload_bytes: payload.len() as u16,
                note_commitment: digest(200),
                leaf_index: 7,
                root_sequence: 8,
                root: digest(300),
            },
            encrypted_note_payload: payload,
        }
    }

    #[test]
    fn canonical_instruction_round_trip_rejects_wrong_version_reserved_and_trailing() {
        let payload = [0xaa, 0xbb, 0xcc];
        let request = request(&payload);
        let encoded = encode_deposit_instruction_v1(&request).unwrap();
        assert_eq!(&encoded.as_bytes()[..8], b"ASDI\x01\x00\x03\x00");
        assert_eq!(
            decode_deposit_instruction_v1(encoded.as_bytes()),
            Ok(request)
        );

        let mut wrong_version = encoded.as_bytes().to_vec();
        wrong_version[4] = 2;
        assert_eq!(
            decode_deposit_instruction_v1(&wrong_version),
            Err(DepositInstructionFormatErrorV1::WrongVersion)
        );
        let mut reserved = encoded.as_bytes().to_vec();
        reserved[44] = 1;
        assert_eq!(
            decode_deposit_instruction_v1(&reserved),
            Err(DepositInstructionFormatErrorV1::NonZeroReserved)
        );
        let mut trailing = encoded.as_bytes().to_vec();
        trailing.push(0);
        assert_eq!(
            decode_deposit_instruction_v1(&trailing),
            Err(DepositInstructionFormatErrorV1::WrongLength)
        );
    }

    #[test]
    fn successful_kernel_result_sets_exact_receipt_payload_once() {
        let payload = [0xaa, 0xbb, 0xcc];
        let event = event(&payload);
        let expected = encode_deposit_event_return_data_v1(&event).unwrap();
        let emitted = RefCell::new(Vec::new());

        execute_and_emit_deposit_v1(
            || Ok(event),
            |bytes| emitted.borrow_mut().push(bytes.to_vec()),
        )
        .unwrap();

        let emitted = emitted.into_inner();
        assert_eq!(emitted.len(), 1);
        assert_eq!(emitted[0], expected.as_bytes());
        assert_eq!(&emitted[0][..4], b"ASPD");
        assert_eq!(&emitted[0][POOL_V1_DEPOSIT_RECEIPT_BYTES..], payload);
    }

    #[test]
    fn failed_kernel_result_never_sets_return_data() {
        let emitted = RefCell::new(Vec::<Vec<u8>>::new());
        let result = execute_and_emit_deposit_v1(
            || -> Result<DepositEventV1<'static>, ProgramError> {
                Err(ProgramError::Custom(0xdead))
            },
            |bytes| emitted.borrow_mut().push(bytes.to_vec()),
        );

        assert_eq!(result, Err(ProgramError::Custom(0xdead)));
        assert!(emitted.into_inner().is_empty());
    }
}
