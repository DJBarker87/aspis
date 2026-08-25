//! Canonical byte format for a state-bound Pool V1 prepared settlement.
//!
//! The account is deliberately large: it carries the exact precomputed Pool
//! and root-history images that the final atomic settlement will copy.  Its
//! SHA-256 authenticator covers every preceding byte, while provenance comes
//! from the requirement that the account is the Pool-owned PDA derived from
//! the Pool and canonical statement digest.

extern crate alloc;

use alloc::{boxed::Box, vec};

use aspis_core::transcript::HashFn;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{root_history_location, AppendOneV1, PoolV1TransitionKind},
    poseidon2::Digest,
};
use solana_program::{program_error::ProgramError, pubkey::Pubkey};

use crate::state::POOL_V1_STATE_ACCOUNT_BYTES;

pub const POOL_V1_PREPARED_SETTLEMENT_MAGIC: [u8; 4] = *b"ASPS";
pub const POOL_V1_PREPARED_SETTLEMENT_VERSION: u8 = 1;
pub const POOL_V1_PREPARED_SETTLEMENT_HASH_SHA256: u8 = 1;
pub const POOL_V1_PREPARED_SETTLEMENT_SEED: &[u8] = b"aspis-settle-plan-v1";
pub const POOL_V1_PREPARED_SETTLEMENT_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/prepared-settlement/v1";
pub const POOL_V1_PREPARED_SETTLEMENT_HEADER_BYTES: usize = 16;
pub const POOL_V1_PREPARED_SETTLEMENT_RECEIPT_BYTES: usize = 64;
pub const POOL_V1_PREPARED_SETTLEMENT_DIGEST_BYTES: usize = 32;

const PROGRAM_OFFSET: usize = POOL_V1_PREPARED_SETTLEMENT_HEADER_BYTES;
const POOL_OFFSET: usize = PROGRAM_OFFSET + 32;
const PLAN_AUTHORITY_OFFSET: usize = POOL_OFFSET + 32;
const SOURCE_SEQUENCE_OFFSET: usize = PLAN_AUTHORITY_OFFSET + 32;
const SOURCE_ROOT_OFFSET: usize = SOURCE_SEQUENCE_OFFSET + 8;
const SOURCE_POOL_DIGEST_OFFSET: usize = SOURCE_ROOT_OFFSET + 32;
const CURRENT_PAGE_ADDRESS_OFFSET: usize = SOURCE_POOL_DIGEST_OFFSET + 32;
const CURRENT_PAGE_DIGEST_OFFSET: usize = CURRENT_PAGE_ADDRESS_OFFSET + 32;
const NEXT_PAGE_ADDRESS_OFFSET: usize = CURRENT_PAGE_DIGEST_OFFSET + 32;
const NEXT_PAGE_DIGEST_OFFSET: usize = NEXT_PAGE_ADDRESS_OFFSET + 32;
const STATEMENT_DIGEST_OFFSET: usize = NEXT_PAGE_DIGEST_OFFSET + 32;
const NULLIFIER_OFFSET: usize = STATEMENT_DIGEST_OFFSET + 32;
const AUTHORIZATION_RECEIPT_ADDRESS_OFFSET: usize = NULLIFIER_OFFSET + 32;
const AUTHORIZATION_RECEIPT_DIGEST_OFFSET: usize = AUTHORIZATION_RECEIPT_ADDRESS_OFFSET + 32;
const NOT_BEFORE_SLOT_OFFSET: usize = AUTHORIZATION_RECEIPT_DIGEST_OFFSET + 32;
const EXPIRES_AT_SLOT_OFFSET: usize = NOT_BEFORE_SLOT_OFFSET + 8;
const FIRST_COMMITMENT_OFFSET: usize = EXPIRES_AT_SLOT_OFFSET + 8;
const SECOND_COMMITMENT_OFFSET: usize = FIRST_COMMITMENT_OFFSET + 32;
const FIRST_RECEIPT_OFFSET: usize = SECOND_COMMITMENT_OFFSET + 32;
const SECOND_RECEIPT_OFFSET: usize =
    FIRST_RECEIPT_OFFSET + POOL_V1_PREPARED_SETTLEMENT_RECEIPT_BYTES;
const NEXT_POOL_IMAGE_OFFSET: usize =
    SECOND_RECEIPT_OFFSET + POOL_V1_PREPARED_SETTLEMENT_RECEIPT_BYTES;
const NEXT_CURRENT_PAGE_IMAGE_OFFSET: usize = NEXT_POOL_IMAGE_OFFSET + POOL_V1_STATE_ACCOUNT_BYTES;
const NEXT_ROLLOVER_PAGE_IMAGE_OFFSET: usize = NEXT_CURRENT_PAGE_IMAGE_OFFSET
    + aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES;
const PLAN_DIGEST_OFFSET: usize = NEXT_ROLLOVER_PAGE_IMAGE_OFFSET
    + aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES;

pub const POOL_V1_PREPARED_SETTLEMENT_ACCOUNT_BYTES: usize =
    PLAN_DIGEST_OFFSET + POOL_V1_PREPARED_SETTLEMENT_DIGEST_BYTES;

const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_SEED.len() <= 32);
const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_ACCOUNT_BYTES == 18_192);

#[cfg(test)]
pub(crate) const TEST_SOURCE_ROOT_OFFSET: usize = SOURCE_ROOT_OFFSET;
#[cfg(test)]
pub(crate) const TEST_FIRST_COMMITMENT_OFFSET: usize = FIRST_COMMITMENT_OFFSET;
#[cfg(test)]
pub(crate) const TEST_SECOND_COMMITMENT_OFFSET: usize = SECOND_COMMITMENT_OFFSET;
#[cfg(test)]
pub(crate) const TEST_FIRST_RECEIPT_ROOT_OFFSET: usize = FIRST_RECEIPT_OFFSET + 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreparedSettlementFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongHashAlgorithm,
    WrongTransitionKind,
    WrongOutputCount,
    WrongPageCount,
    ZeroPlanAuthority,
    NonZeroReserved,
    NonCanonicalDigest,
    InvalidReceipt,
    InvalidTimeRange,
    DigestMismatch,
}

impl From<PreparedSettlementFormatErrorV1> for ProgramError {
    fn from(_: PreparedSettlementFormatErrorV1) -> Self {
        ProgramError::InvalidAccountData
    }
}

#[derive(Clone, Copy)]
pub(crate) struct PreparedSettlementPlanFieldsV1<'a> {
    pub pda_bump: u8,
    pub transition_kind: PoolV1TransitionKind,
    pub program_id: [u8; 32],
    pub pool: [u8; 32],
    pub plan_authority: [u8; 32],
    pub source_sequence: u64,
    pub source_root: Digest,
    pub source_pool_image_digest: [u8; 32],
    pub current_page_address: [u8; 32],
    pub source_current_page_image_digest: [u8; 32],
    pub next_page_address: Option<[u8; 32]>,
    pub source_next_page_image_digest: Option<[u8; 32]>,
    pub statement_digest: [u8; 32],
    pub nullifier: Digest,
    pub authorization_receipt_address: [u8; 32],
    pub authorization_receipt_image_digest: [u8; 32],
    pub not_before_slot: u64,
    pub expires_at_slot: u64,
    pub first_commitment: Digest,
    pub second_commitment: Option<Digest>,
    pub first_receipt: AppendOneV1,
    pub second_receipt: Option<AppendOneV1>,
    pub next_pool_image: &'a [u8; POOL_V1_STATE_ACCOUNT_BYTES],
    pub next_current_page_image:
        &'a [u8; aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    pub next_rollover_page_image:
        Option<&'a [u8; aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PreparedSettlementPlanViewV1<'a> {
    pub pda_bump: u8,
    pub transition_kind: PoolV1TransitionKind,
    pub program_id: [u8; 32],
    pub pool: [u8; 32],
    pub plan_authority: [u8; 32],
    pub source_sequence: u64,
    pub source_root: Digest,
    pub source_pool_image_digest: [u8; 32],
    pub current_page_address: [u8; 32],
    pub source_current_page_image_digest: [u8; 32],
    pub next_page_address: Option<[u8; 32]>,
    pub source_next_page_image_digest: Option<[u8; 32]>,
    pub statement_digest: [u8; 32],
    pub nullifier: Digest,
    pub authorization_receipt_address: [u8; 32],
    pub authorization_receipt_image_digest: [u8; 32],
    pub not_before_slot: u64,
    pub expires_at_slot: u64,
    pub first_commitment: Digest,
    pub second_commitment: Option<Digest>,
    pub first_receipt: AppendOneV1,
    pub second_receipt: Option<AppendOneV1>,
    pub next_pool_image: &'a [u8; POOL_V1_STATE_ACCOUNT_BYTES],
    pub next_current_page_image:
        &'a [u8; aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    pub next_rollover_page_image:
        Option<&'a [u8; aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES]>,
}

pub fn pool_v1_prepared_settlement_plan_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    statement_digest: &[u8; 32],
    source_sequence: u64,
    plan_authority: &Pubkey,
) -> (Pubkey, u8) {
    let source_sequence = source_sequence.to_le_bytes();
    Pubkey::find_program_address(
        &[
            POOL_V1_PREPARED_SETTLEMENT_SEED,
            pool.as_ref(),
            statement_digest,
            &source_sequence,
            plan_authority.as_ref(),
        ],
        program_id,
    )
}

pub(crate) fn exact_image_digest_v1(bytes: &[u8], hash: HashFn) -> [u8; 32] {
    hash(&[bytes])
}

fn transition_kind_from_byte(
    value: u8,
) -> Result<PoolV1TransitionKind, PreparedSettlementFormatErrorV1> {
    match value {
        1 => Ok(PoolV1TransitionKind::PrivateTransfer),
        2 => Ok(PoolV1TransitionKind::Withdrawal),
        _ => Err(PreparedSettlementFormatErrorV1::WrongTransitionKind),
    }
}

fn receipt_is_exact(receipt: &AppendOneV1) -> bool {
    receipt.root_sequence == receipt.leaf_index.checked_add(1).unwrap_or(u64::MAX)
        && receipt.history == root_history_location(receipt.root_sequence)
}

fn encode_receipt(output: &mut [u8], receipt: &AppendOneV1) {
    output.fill(0);
    output[..8].copy_from_slice(&receipt.leaf_index.to_le_bytes());
    output[8..16].copy_from_slice(&receipt.root_sequence.to_le_bytes());
    output[16..48].copy_from_slice(&encode_digest_canonical(&receipt.root));
    output[48..56].copy_from_slice(&receipt.history.page_number.to_le_bytes());
    output[56..58].copy_from_slice(&receipt.history.slot.to_le_bytes());
}

fn decode_receipt(bytes: &[u8]) -> Result<AppendOneV1, PreparedSettlementFormatErrorV1> {
    if bytes.len() != POOL_V1_PREPARED_SETTLEMENT_RECEIPT_BYTES || bytes[58..64] != [0u8; 6] {
        return Err(PreparedSettlementFormatErrorV1::InvalidReceipt);
    }
    let receipt = AppendOneV1 {
        leaf_index: u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        root_sequence: u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
        root: decode_digest_canonical(bytes[16..48].try_into().unwrap())
            .map_err(|_| PreparedSettlementFormatErrorV1::NonCanonicalDigest)?,
        history: aspis_statement::pool_v1::RootHistoryLocationV1 {
            page_number: u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
            slot: u16::from_le_bytes(bytes[56..58].try_into().unwrap()),
        },
    };
    if !receipt_is_exact(&receipt) {
        return Err(PreparedSettlementFormatErrorV1::InvalidReceipt);
    }
    Ok(receipt)
}

fn digest32(bytes: &[u8]) -> Result<Digest, PreparedSettlementFormatErrorV1> {
    decode_digest_canonical(
        bytes
            .try_into()
            .map_err(|_| PreparedSettlementFormatErrorV1::WrongLength)?,
    )
    .map_err(|_| PreparedSettlementFormatErrorV1::NonCanonicalDigest)
}

fn exact32(bytes: &[u8]) -> [u8; 32] {
    bytes.try_into().unwrap()
}

pub(crate) fn encode_prepared_settlement_plan_v1(
    fields: PreparedSettlementPlanFieldsV1<'_>,
    hash: HashFn,
) -> Result<Box<[u8; POOL_V1_PREPARED_SETTLEMENT_ACCOUNT_BYTES]>, PreparedSettlementFormatErrorV1> {
    let (output_count, second_commitment, second_receipt) = match (
        fields.transition_kind,
        fields.second_commitment,
        fields.second_receipt,
    ) {
        (PoolV1TransitionKind::PrivateTransfer, Some(commitment), Some(receipt)) => {
            (2u8, Some(commitment), Some(receipt))
        }
        (PoolV1TransitionKind::Withdrawal, None, None) => (1u8, None, None),
        _ => return Err(PreparedSettlementFormatErrorV1::WrongOutputCount),
    };
    let (page_count, next_page_address, next_page_digest, next_page_image) = match (
        fields.next_page_address,
        fields.source_next_page_image_digest,
        fields.next_rollover_page_image,
    ) {
        (None, None, None) => (1u8, [0u8; 32], [0u8; 32], None),
        (Some(address), Some(digest), Some(image)) => (2u8, address, digest, Some(image)),
        _ => return Err(PreparedSettlementFormatErrorV1::WrongPageCount),
    };
    if fields.plan_authority == [0u8; 32] {
        return Err(PreparedSettlementFormatErrorV1::ZeroPlanAuthority);
    }
    if fields.not_before_slot > fields.expires_at_slot {
        return Err(PreparedSettlementFormatErrorV1::InvalidTimeRange);
    }
    if !receipt_is_exact(&fields.first_receipt)
        || second_receipt
            .as_ref()
            .is_some_and(|receipt| !receipt_is_exact(receipt))
    {
        return Err(PreparedSettlementFormatErrorV1::InvalidReceipt);
    }

    let raw: Box<[u8]> = vec![0u8; POOL_V1_PREPARED_SETTLEMENT_ACCOUNT_BYTES].into_boxed_slice();
    let mut output: Box<[u8; POOL_V1_PREPARED_SETTLEMENT_ACCOUNT_BYTES]> = raw
        .try_into()
        .map_err(|_| PreparedSettlementFormatErrorV1::WrongLength)?;
    output[..4].copy_from_slice(&POOL_V1_PREPARED_SETTLEMENT_MAGIC);
    output[4] = POOL_V1_PREPARED_SETTLEMENT_VERSION;
    output[5] = POOL_V1_PREPARED_SETTLEMENT_HASH_SHA256;
    output[6] = fields.transition_kind as u8;
    output[7] = output_count;
    output[8] = page_count;
    output[9] = fields.pda_bump;
    output[PROGRAM_OFFSET..POOL_OFFSET].copy_from_slice(&fields.program_id);
    output[POOL_OFFSET..PLAN_AUTHORITY_OFFSET].copy_from_slice(&fields.pool);
    output[PLAN_AUTHORITY_OFFSET..SOURCE_SEQUENCE_OFFSET].copy_from_slice(&fields.plan_authority);
    output[SOURCE_SEQUENCE_OFFSET..SOURCE_ROOT_OFFSET]
        .copy_from_slice(&fields.source_sequence.to_le_bytes());
    output[SOURCE_ROOT_OFFSET..SOURCE_POOL_DIGEST_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&fields.source_root));
    output[SOURCE_POOL_DIGEST_OFFSET..CURRENT_PAGE_ADDRESS_OFFSET]
        .copy_from_slice(&fields.source_pool_image_digest);
    output[CURRENT_PAGE_ADDRESS_OFFSET..CURRENT_PAGE_DIGEST_OFFSET]
        .copy_from_slice(&fields.current_page_address);
    output[CURRENT_PAGE_DIGEST_OFFSET..NEXT_PAGE_ADDRESS_OFFSET]
        .copy_from_slice(&fields.source_current_page_image_digest);
    output[NEXT_PAGE_ADDRESS_OFFSET..NEXT_PAGE_DIGEST_OFFSET].copy_from_slice(&next_page_address);
    output[NEXT_PAGE_DIGEST_OFFSET..STATEMENT_DIGEST_OFFSET].copy_from_slice(&next_page_digest);
    output[STATEMENT_DIGEST_OFFSET..NULLIFIER_OFFSET].copy_from_slice(&fields.statement_digest);
    output[NULLIFIER_OFFSET..AUTHORIZATION_RECEIPT_ADDRESS_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&fields.nullifier));
    output[AUTHORIZATION_RECEIPT_ADDRESS_OFFSET..AUTHORIZATION_RECEIPT_DIGEST_OFFSET]
        .copy_from_slice(&fields.authorization_receipt_address);
    output[AUTHORIZATION_RECEIPT_DIGEST_OFFSET..NOT_BEFORE_SLOT_OFFSET]
        .copy_from_slice(&fields.authorization_receipt_image_digest);
    output[NOT_BEFORE_SLOT_OFFSET..EXPIRES_AT_SLOT_OFFSET]
        .copy_from_slice(&fields.not_before_slot.to_le_bytes());
    output[EXPIRES_AT_SLOT_OFFSET..FIRST_COMMITMENT_OFFSET]
        .copy_from_slice(&fields.expires_at_slot.to_le_bytes());
    output[FIRST_COMMITMENT_OFFSET..SECOND_COMMITMENT_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&fields.first_commitment));
    if let Some(commitment) = second_commitment {
        output[SECOND_COMMITMENT_OFFSET..FIRST_RECEIPT_OFFSET]
            .copy_from_slice(&encode_digest_canonical(&commitment));
    }
    encode_receipt(
        &mut output[FIRST_RECEIPT_OFFSET..SECOND_RECEIPT_OFFSET],
        &fields.first_receipt,
    );
    if let Some(receipt) = second_receipt {
        encode_receipt(
            &mut output[SECOND_RECEIPT_OFFSET..NEXT_POOL_IMAGE_OFFSET],
            &receipt,
        );
    }
    output[NEXT_POOL_IMAGE_OFFSET..NEXT_CURRENT_PAGE_IMAGE_OFFSET]
        .copy_from_slice(fields.next_pool_image);
    output[NEXT_CURRENT_PAGE_IMAGE_OFFSET..NEXT_ROLLOVER_PAGE_IMAGE_OFFSET]
        .copy_from_slice(fields.next_current_page_image);
    if let Some(image) = next_page_image {
        output[NEXT_ROLLOVER_PAGE_IMAGE_OFFSET..PLAN_DIGEST_OFFSET].copy_from_slice(image);
    }
    let digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_DIGEST_DOMAIN,
        &output[..PLAN_DIGEST_OFFSET],
    ]);
    output[PLAN_DIGEST_OFFSET..].copy_from_slice(&digest);
    Ok(output)
}

pub(crate) fn decode_prepared_settlement_plan_v1(
    bytes: &[u8],
    hash: HashFn,
) -> Result<PreparedSettlementPlanViewV1<'_>, PreparedSettlementFormatErrorV1> {
    let bytes: &[u8; POOL_V1_PREPARED_SETTLEMENT_ACCOUNT_BYTES] = bytes
        .try_into()
        .map_err(|_| PreparedSettlementFormatErrorV1::WrongLength)?;
    if bytes[..4] != POOL_V1_PREPARED_SETTLEMENT_MAGIC {
        return Err(PreparedSettlementFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PREPARED_SETTLEMENT_VERSION {
        return Err(PreparedSettlementFormatErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PREPARED_SETTLEMENT_HASH_SHA256 {
        return Err(PreparedSettlementFormatErrorV1::WrongHashAlgorithm);
    }
    if bytes[10..16] != [0u8; 6] {
        return Err(PreparedSettlementFormatErrorV1::NonZeroReserved);
    }
    let expected_digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_DIGEST_DOMAIN,
        &bytes[..PLAN_DIGEST_OFFSET],
    ]);
    if bytes[PLAN_DIGEST_OFFSET..] != expected_digest {
        return Err(PreparedSettlementFormatErrorV1::DigestMismatch);
    }
    let transition_kind = transition_kind_from_byte(bytes[6])?;
    let second_commitment = match (transition_kind, bytes[7]) {
        (PoolV1TransitionKind::PrivateTransfer, 2) => Some(digest32(
            &bytes[SECOND_COMMITMENT_OFFSET..FIRST_RECEIPT_OFFSET],
        )?),
        (PoolV1TransitionKind::Withdrawal, 1)
            if bytes[SECOND_COMMITMENT_OFFSET..FIRST_RECEIPT_OFFSET] == [0u8; 32] =>
        {
            None
        }
        _ => return Err(PreparedSettlementFormatErrorV1::WrongOutputCount),
    };
    let first_receipt = decode_receipt(&bytes[FIRST_RECEIPT_OFFSET..SECOND_RECEIPT_OFFSET])?;
    let second_receipt = match transition_kind {
        PoolV1TransitionKind::PrivateTransfer => Some(decode_receipt(
            &bytes[SECOND_RECEIPT_OFFSET..NEXT_POOL_IMAGE_OFFSET],
        )?),
        PoolV1TransitionKind::Withdrawal
            if bytes[SECOND_RECEIPT_OFFSET..NEXT_POOL_IMAGE_OFFSET]
                == [0u8; POOL_V1_PREPARED_SETTLEMENT_RECEIPT_BYTES] =>
        {
            None
        }
        PoolV1TransitionKind::Withdrawal => {
            return Err(PreparedSettlementFormatErrorV1::InvalidReceipt)
        }
    };
    let (next_page_address, source_next_page_image_digest, next_rollover_page_image) =
        match bytes[8] {
            1 if bytes[NEXT_PAGE_ADDRESS_OFFSET..STATEMENT_DIGEST_OFFSET] == [0u8; 64]
                && bytes[NEXT_ROLLOVER_PAGE_IMAGE_OFFSET..PLAN_DIGEST_OFFSET]
                    .iter()
                    .all(|byte| *byte == 0) =>
            {
                (None, None, None)
            }
            2 => (
                Some(exact32(
                    &bytes[NEXT_PAGE_ADDRESS_OFFSET..NEXT_PAGE_DIGEST_OFFSET],
                )),
                Some(exact32(
                    &bytes[NEXT_PAGE_DIGEST_OFFSET..STATEMENT_DIGEST_OFFSET],
                )),
                Some(
                    (&bytes[NEXT_ROLLOVER_PAGE_IMAGE_OFFSET..PLAN_DIGEST_OFFSET])
                        .try_into()
                        .unwrap(),
                ),
            ),
            _ => return Err(PreparedSettlementFormatErrorV1::WrongPageCount),
        };
    let not_before_slot = u64::from_le_bytes(
        bytes[NOT_BEFORE_SLOT_OFFSET..EXPIRES_AT_SLOT_OFFSET]
            .try_into()
            .unwrap(),
    );
    let expires_at_slot = u64::from_le_bytes(
        bytes[EXPIRES_AT_SLOT_OFFSET..FIRST_COMMITMENT_OFFSET]
            .try_into()
            .unwrap(),
    );
    if not_before_slot > expires_at_slot {
        return Err(PreparedSettlementFormatErrorV1::InvalidTimeRange);
    }
    Ok(PreparedSettlementPlanViewV1 {
        pda_bump: bytes[9],
        transition_kind,
        program_id: exact32(&bytes[PROGRAM_OFFSET..POOL_OFFSET]),
        pool: exact32(&bytes[POOL_OFFSET..PLAN_AUTHORITY_OFFSET]),
        plan_authority: {
            let authority = exact32(&bytes[PLAN_AUTHORITY_OFFSET..SOURCE_SEQUENCE_OFFSET]);
            if authority == [0u8; 32] {
                return Err(PreparedSettlementFormatErrorV1::ZeroPlanAuthority);
            }
            authority
        },
        source_sequence: u64::from_le_bytes(
            bytes[SOURCE_SEQUENCE_OFFSET..SOURCE_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        source_root: digest32(&bytes[SOURCE_ROOT_OFFSET..SOURCE_POOL_DIGEST_OFFSET])?,
        source_pool_image_digest: exact32(
            &bytes[SOURCE_POOL_DIGEST_OFFSET..CURRENT_PAGE_ADDRESS_OFFSET],
        ),
        current_page_address: exact32(
            &bytes[CURRENT_PAGE_ADDRESS_OFFSET..CURRENT_PAGE_DIGEST_OFFSET],
        ),
        source_current_page_image_digest: exact32(
            &bytes[CURRENT_PAGE_DIGEST_OFFSET..NEXT_PAGE_ADDRESS_OFFSET],
        ),
        next_page_address,
        source_next_page_image_digest,
        statement_digest: exact32(&bytes[STATEMENT_DIGEST_OFFSET..NULLIFIER_OFFSET]),
        nullifier: digest32(&bytes[NULLIFIER_OFFSET..AUTHORIZATION_RECEIPT_ADDRESS_OFFSET])?,
        authorization_receipt_address: exact32(
            &bytes[AUTHORIZATION_RECEIPT_ADDRESS_OFFSET..AUTHORIZATION_RECEIPT_DIGEST_OFFSET],
        ),
        authorization_receipt_image_digest: exact32(
            &bytes[AUTHORIZATION_RECEIPT_DIGEST_OFFSET..NOT_BEFORE_SLOT_OFFSET],
        ),
        not_before_slot,
        expires_at_slot,
        first_commitment: digest32(&bytes[FIRST_COMMITMENT_OFFSET..SECOND_COMMITMENT_OFFSET])?,
        second_commitment,
        first_receipt,
        second_receipt,
        next_pool_image: (&bytes[NEXT_POOL_IMAGE_OFFSET..NEXT_CURRENT_PAGE_IMAGE_OFFSET])
            .try_into()
            .unwrap(),
        next_current_page_image: (&bytes
            [NEXT_CURRENT_PAGE_IMAGE_OFFSET..NEXT_ROLLOVER_PAGE_IMAGE_OFFSET])
            .try_into()
            .unwrap(),
        next_rollover_page_image,
    })
}

#[cfg(test)]
pub(crate) fn reauthenticate_prepared_settlement_plan_for_test(
    bytes: &mut [u8; POOL_V1_PREPARED_SETTLEMENT_ACCOUNT_BYTES],
    hash: HashFn,
) {
    let digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_DIGEST_DOMAIN,
        &bytes[..PLAN_DIGEST_OFFSET],
    ]);
    bytes[PLAN_DIGEST_OFFSET..].copy_from_slice(&digest);
}
