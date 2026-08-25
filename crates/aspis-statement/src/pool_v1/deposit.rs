//! Exact Pool V1 deposit receipt and opaque delivery-payload boundary.
//!
//! The note commitment is computed from the public deposit fields elsewhere;
//! the encrypted payload is delivery data only.  Its bytes are never decoded
//! or trusted when deriving the commitment.

use aspis_core::field::P;

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest, VALUE_LIMIT};

pub const POOL_V1_DEPOSIT_RECEIPT_MAGIC: [u8; 4] = *b"ASPD";
pub const POOL_V1_DEPOSIT_RECEIPT_VERSION: u8 = 1;
pub const POOL_V1_DEPOSIT_RECEIPT_BYTES: usize = 224;
/// Keeps the fixed receipt plus opaque payload below Solana's 1,024-byte
/// return-data ceiling.  A future event transport may use the same bound.
pub const POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES: usize = 512;
pub const POOL_V1_DEPOSIT_RETURN_MAX_BYTES: usize =
    POOL_V1_DEPOSIT_RECEIPT_BYTES + POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES;

const RECEIPT_POOL_OFFSET: usize = 8;
const RECEIPT_ASSET_MINT_OFFSET: usize = 40;
const RECEIPT_SOURCE_TOKEN_OFFSET: usize = 72;
const RECEIPT_VAULT_TOKEN_OFFSET: usize = 104;
const RECEIPT_AMOUNT_OFFSET: usize = 136;
const RECEIPT_PAYLOAD_LENGTH_OFFSET: usize = 140;
const RECEIPT_NOTE_OFFSET: usize = 144;
const RECEIPT_LEAF_INDEX_OFFSET: usize = 176;
const RECEIPT_ROOT_SEQUENCE_OFFSET: usize = 184;
const RECEIPT_ROOT_OFFSET: usize = 192;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1DepositFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    InvalidIdentity,
    InvalidAmount,
    InvalidPayloadLength,
    NonCanonicalDigest,
    InvalidSequence,
}

/// Fixed receipt paired with one opaque encrypted-note payload.
///
/// `root_sequence == leaf_index + 1`.  The payload length is committed by the
/// fixed receipt framing, but the payload contents do not influence
/// `note_commitment`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositReceiptV1 {
    pub pool: [u8; 32],
    pub asset_mint: [u8; 32],
    pub source_token_account: [u8; 32],
    pub vault_token_account: [u8; 32],
    pub amount: u32,
    pub encrypted_note_payload_bytes: u16,
    pub note_commitment: Digest,
    pub leaf_index: u64,
    pub root_sequence: u64,
    pub root: Digest,
}

/// Borrowed delivery result.  The program layer may encode/log this pair,
/// but must never parse the payload to decide the note commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositEventV1<'a> {
    pub receipt: DepositReceiptV1,
    pub encrypted_note_payload: &'a [u8],
}

fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

pub fn validate_deposit_receipt_v1(
    receipt: &DepositReceiptV1,
) -> Result<(), PoolV1DepositFormatError> {
    if receipt.pool == [0u8; 32]
        || receipt.asset_mint == [0u8; 32]
        || receipt.source_token_account == [0u8; 32]
        || receipt.vault_token_account == [0u8; 32]
        || receipt.source_token_account == receipt.vault_token_account
    {
        return Err(PoolV1DepositFormatError::InvalidIdentity);
    }
    // SpendV0 proves a 30-bit value.  Merely fitting in u32 is insufficient
    // because a larger deposit would create an unspendable Pool V1 note.
    if receipt.amount == 0 || receipt.amount >= VALUE_LIMIT {
        return Err(PoolV1DepositFormatError::InvalidAmount);
    }
    if usize::from(receipt.encrypted_note_payload_bytes) > POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES
    {
        return Err(PoolV1DepositFormatError::InvalidPayloadLength);
    }
    if !digest_is_canonical(&receipt.note_commitment) || !digest_is_canonical(&receipt.root) {
        return Err(PoolV1DepositFormatError::NonCanonicalDigest);
    }
    if receipt.leaf_index.checked_add(1) != Some(receipt.root_sequence) {
        return Err(PoolV1DepositFormatError::InvalidSequence);
    }
    Ok(())
}

pub fn validate_deposit_event_v1(
    event: &DepositEventV1<'_>,
) -> Result<(), PoolV1DepositFormatError> {
    validate_deposit_receipt_v1(&event.receipt)?;
    if event.encrypted_note_payload.len() != usize::from(event.receipt.encrypted_note_payload_bytes)
    {
        return Err(PoolV1DepositFormatError::InvalidPayloadLength);
    }
    Ok(())
}

pub fn encode_deposit_receipt_v1(
    receipt: &DepositReceiptV1,
) -> Result<[u8; POOL_V1_DEPOSIT_RECEIPT_BYTES], PoolV1DepositFormatError> {
    validate_deposit_receipt_v1(receipt)?;
    let mut output = [0u8; POOL_V1_DEPOSIT_RECEIPT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_DEPOSIT_RECEIPT_MAGIC);
    output[4] = POOL_V1_DEPOSIT_RECEIPT_VERSION;
    output[RECEIPT_POOL_OFFSET..RECEIPT_ASSET_MINT_OFFSET].copy_from_slice(&receipt.pool);
    output[RECEIPT_ASSET_MINT_OFFSET..RECEIPT_SOURCE_TOKEN_OFFSET]
        .copy_from_slice(&receipt.asset_mint);
    output[RECEIPT_SOURCE_TOKEN_OFFSET..RECEIPT_VAULT_TOKEN_OFFSET]
        .copy_from_slice(&receipt.source_token_account);
    output[RECEIPT_VAULT_TOKEN_OFFSET..RECEIPT_AMOUNT_OFFSET]
        .copy_from_slice(&receipt.vault_token_account);
    output[RECEIPT_AMOUNT_OFFSET..RECEIPT_PAYLOAD_LENGTH_OFFSET]
        .copy_from_slice(&receipt.amount.to_le_bytes());
    output[RECEIPT_PAYLOAD_LENGTH_OFFSET..142]
        .copy_from_slice(&receipt.encrypted_note_payload_bytes.to_le_bytes());
    output[RECEIPT_NOTE_OFFSET..RECEIPT_LEAF_INDEX_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&receipt.note_commitment));
    output[RECEIPT_LEAF_INDEX_OFFSET..RECEIPT_ROOT_SEQUENCE_OFFSET]
        .copy_from_slice(&receipt.leaf_index.to_le_bytes());
    output[RECEIPT_ROOT_SEQUENCE_OFFSET..RECEIPT_ROOT_OFFSET]
        .copy_from_slice(&receipt.root_sequence.to_le_bytes());
    output[RECEIPT_ROOT_OFFSET..].copy_from_slice(&encode_digest_canonical(&receipt.root));
    Ok(output)
}

pub fn decode_deposit_receipt_v1(
    bytes: &[u8],
) -> Result<DepositReceiptV1, PoolV1DepositFormatError> {
    if bytes.len() != POOL_V1_DEPOSIT_RECEIPT_BYTES {
        return Err(PoolV1DepositFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_DEPOSIT_RECEIPT_MAGIC {
        return Err(PoolV1DepositFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_DEPOSIT_RECEIPT_VERSION {
        return Err(PoolV1DepositFormatError::WrongVersion);
    }
    if bytes[5..8] != [0u8; 3] || bytes[142..144] != [0u8; 2] {
        return Err(PoolV1DepositFormatError::NonZeroReserved);
    }
    let note_commitment = decode_digest_canonical(
        bytes[RECEIPT_NOTE_OFFSET..RECEIPT_LEAF_INDEX_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1DepositFormatError::NonCanonicalDigest)?;
    let root = decode_digest_canonical(bytes[RECEIPT_ROOT_OFFSET..].try_into().unwrap())
        .map_err(|_| PoolV1DepositFormatError::NonCanonicalDigest)?;
    let receipt = DepositReceiptV1 {
        pool: bytes[RECEIPT_POOL_OFFSET..RECEIPT_ASSET_MINT_OFFSET]
            .try_into()
            .unwrap(),
        asset_mint: bytes[RECEIPT_ASSET_MINT_OFFSET..RECEIPT_SOURCE_TOKEN_OFFSET]
            .try_into()
            .unwrap(),
        source_token_account: bytes[RECEIPT_SOURCE_TOKEN_OFFSET..RECEIPT_VAULT_TOKEN_OFFSET]
            .try_into()
            .unwrap(),
        vault_token_account: bytes[RECEIPT_VAULT_TOKEN_OFFSET..RECEIPT_AMOUNT_OFFSET]
            .try_into()
            .unwrap(),
        amount: u32::from_le_bytes(
            bytes[RECEIPT_AMOUNT_OFFSET..RECEIPT_PAYLOAD_LENGTH_OFFSET]
                .try_into()
                .unwrap(),
        ),
        encrypted_note_payload_bytes: u16::from_le_bytes(
            bytes[RECEIPT_PAYLOAD_LENGTH_OFFSET..142]
                .try_into()
                .unwrap(),
        ),
        note_commitment,
        leaf_index: u64::from_le_bytes(
            bytes[RECEIPT_LEAF_INDEX_OFFSET..RECEIPT_ROOT_SEQUENCE_OFFSET]
                .try_into()
                .unwrap(),
        ),
        root_sequence: u64::from_le_bytes(
            bytes[RECEIPT_ROOT_SEQUENCE_OFFSET..RECEIPT_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        root,
    };
    validate_deposit_receipt_v1(&receipt)?;
    Ok(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn receipt() -> DepositReceiptV1 {
        DepositReceiptV1 {
            pool: [1u8; 32],
            asset_mint: [2u8; 32],
            source_token_account: [3u8; 32],
            vault_token_account: [4u8; 32],
            amount: 77,
            encrypted_note_payload_bytes: 5,
            note_commitment: digest(10),
            leaf_index: 11,
            root_sequence: 12,
            root: digest(20),
        }
    }

    #[test]
    fn exact_receipt_image_roundtrips_and_event_payload_is_opaque() {
        let receipt = receipt();
        let encoded = encode_deposit_receipt_v1(&receipt).unwrap();
        assert_eq!(encoded.len(), 224);
        assert_eq!(&encoded[..5], &[b'A', b'S', b'P', b'D', 1]);
        assert_eq!(decode_deposit_receipt_v1(&encoded), Ok(receipt));

        let first_payload = [1u8, 2, 3, 4, 5];
        let second_payload = [9u8, 8, 7, 6, 5];
        assert_eq!(
            validate_deposit_event_v1(&DepositEventV1 {
                receipt,
                encrypted_note_payload: &first_payload,
            }),
            Ok(())
        );
        // Equal-length payload content has no effect on the fixed receipt or
        // note commitment.
        assert_eq!(
            encode_deposit_receipt_v1(
                &DepositEventV1 {
                    receipt,
                    encrypted_note_payload: &second_payload,
                }
                .receipt
            )
            .unwrap(),
            encoded
        );
    }

    #[test]
    fn receipt_rejects_unspendable_amount_bad_framing_and_bad_sequence() {
        let baseline = encode_deposit_receipt_v1(&receipt()).unwrap();

        for amount in [0, VALUE_LIMIT] {
            assert_eq!(
                encode_deposit_receipt_v1(&DepositReceiptV1 {
                    amount,
                    ..receipt()
                }),
                Err(PoolV1DepositFormatError::InvalidAmount)
            );
        }
        assert_eq!(
            encode_deposit_receipt_v1(&DepositReceiptV1 {
                root_sequence: 13,
                ..receipt()
            }),
            Err(PoolV1DepositFormatError::InvalidSequence)
        );
        assert_eq!(
            validate_deposit_event_v1(&DepositEventV1 {
                receipt: receipt(),
                encrypted_note_payload: &[1, 2, 3, 4],
            }),
            Err(PoolV1DepositFormatError::InvalidPayloadLength)
        );

        let mut reserved = baseline;
        reserved[142] = 1;
        assert_eq!(
            decode_deposit_receipt_v1(&reserved),
            Err(PoolV1DepositFormatError::NonZeroReserved)
        );
    }
}
