//! Canonical byte formats for a state-bound Pool V1 prepared settlement.
//!
//! The exact precomputed Pool and current-history images live in a 10,000-byte
//! core PDA. A rollover uses a second, exact 8,504-byte PDA for the next-page
//! image. The core authenticates the shard address and digest; the shard
//! authenticates the core address and every transition identity field needed
//! to prevent cross-plan substitution.

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
pub const POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_MAGIC: [u8; 4] = *b"ASRS";
pub const POOL_V1_PREPARED_SETTLEMENT_VERSION: u8 = 1;
pub const POOL_V1_PREPARED_SETTLEMENT_HASH_SHA256: u8 = 1;
pub const POOL_V1_PREPARED_SETTLEMENT_SEED: &[u8] = b"aspis-settle-plan-v1";
pub const POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED: &[u8] = b"aspis-settle-roll-v1";
pub const POOL_V1_PREPARED_SETTLEMENT_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/prepared-settlement/core/v1";
pub const POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/prepared-settlement/rollover/v1";
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
const ROLLOVER_SHARD_ADDRESS_OFFSET: usize = NEXT_ROLLOVER_PAGE_IMAGE_OFFSET;
const ROLLOVER_SHARD_DIGEST_OFFSET: usize = ROLLOVER_SHARD_ADDRESS_OFFSET + 32;
const CORE_DIGEST_OFFSET: usize = ROLLOVER_SHARD_DIGEST_OFFSET + 32;

pub const POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES: usize =
    CORE_DIGEST_OFFSET + POOL_V1_PREPARED_SETTLEMENT_DIGEST_BYTES;

const SHARD_CORE_ADDRESS_OFFSET: usize = POOL_V1_PREPARED_SETTLEMENT_HEADER_BYTES;
const SHARD_PROGRAM_OFFSET: usize = SHARD_CORE_ADDRESS_OFFSET + 32;
const SHARD_POOL_OFFSET: usize = SHARD_PROGRAM_OFFSET + 32;
const SHARD_STATEMENT_DIGEST_OFFSET: usize = SHARD_POOL_OFFSET + 32;
const SHARD_SOURCE_SEQUENCE_OFFSET: usize = SHARD_STATEMENT_DIGEST_OFFSET + 32;
const SHARD_PLAN_AUTHORITY_OFFSET: usize = SHARD_SOURCE_SEQUENCE_OFFSET + 8;
const SHARD_NEXT_PAGE_ADDRESS_OFFSET: usize = SHARD_PLAN_AUTHORITY_OFFSET + 32;
const SHARD_NEXT_PAGE_IMAGE_OFFSET: usize = SHARD_NEXT_PAGE_ADDRESS_OFFSET + 32;
const SHARD_DIGEST_OFFSET: usize = SHARD_NEXT_PAGE_IMAGE_OFFSET
    + aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES;

pub const POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES: usize =
    SHARD_DIGEST_OFFSET + POOL_V1_PREPARED_SETTLEMENT_DIGEST_BYTES;

const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_SEED.len() <= 32);
const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED.len() <= 32);
const _: () = assert!(NEXT_ROLLOVER_PAGE_IMAGE_OFFSET == 9_904);
const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES == 10_000);
const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES == 8_504);
const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES <= 10_240);
const _: () = assert!(POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES <= 10_240);

/// Exact heap occupied simultaneously by the prepared next-state image and
/// the two encoded plan images on the rollover path. History-page images are
/// written directly into these outputs rather than staged in additional
/// 8,256-byte allocations.
pub(crate) const PREPARED_SETTLEMENT_MAX_LIVE_OUTPUT_IMAGE_BYTES: usize =
    POOL_V1_STATE_ACCOUNT_BYTES
        + POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES
        + POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES;
const _: () = assert!(PREPARED_SETTLEMENT_MAX_LIVE_OUTPUT_IMAGE_BYTES < 32 * 1_024);

#[cfg(test)]
pub(crate) const TEST_SOURCE_ROOT_OFFSET: usize = SOURCE_ROOT_OFFSET;
#[cfg(test)]
pub(crate) const TEST_FIRST_COMMITMENT_OFFSET: usize = FIRST_COMMITMENT_OFFSET;
#[cfg(test)]
pub(crate) const TEST_SECOND_COMMITMENT_OFFSET: usize = SECOND_COMMITMENT_OFFSET;
#[cfg(test)]
pub(crate) const TEST_FIRST_RECEIPT_ROOT_OFFSET: usize = FIRST_RECEIPT_OFFSET + 16;
#[cfg(test)]
pub(crate) const TEST_ROLLOVER_SHARD_IMAGE_OFFSET: usize = SHARD_NEXT_PAGE_IMAGE_OFFSET;
#[cfg(test)]
pub(crate) const TEST_ROLLOVER_SHARD_CORE_ADDRESS_OFFSET: usize = SHARD_CORE_ADDRESS_OFFSET;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreparedSettlementFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongHashAlgorithm,
    WrongTransitionKind,
    WrongOutputCount,
    WrongPageCount,
    WrongShard,
    InvalidPda,
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PreparedSettlementRolloverShardImageV1 {
    pub address: Pubkey,
    pub pda_bump: u8,
    pub image: Box<[u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PreparedSettlementPlanImagesV1 {
    pub core_address: Pubkey,
    pub core_pda_bump: u8,
    pub source_sequence: u64,
    pub statement_digest: [u8; 32],
    pub core_image: Box<[u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES]>,
    pub rollover_shard: Option<PreparedSettlementRolloverShardImageV1>,
}

#[derive(Clone, Copy)]
pub(crate) struct PreparedSettlementRolloverShardAccountV1<'a> {
    pub address: &'a Pubkey,
    pub owner: &'a Pubkey,
    pub image: &'a [u8],
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
    pub rollover_shard_address: Option<[u8; 32]>,
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

pub fn pool_v1_prepared_settlement_rollover_address(
    program_id: &Pubkey,
    core_plan_address: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,
            core_plan_address.as_ref(),
        ],
        program_id,
    )
}

pub(crate) fn exact_image_digest_v1(bytes: &[u8], hash: HashFn) -> [u8; 32] {
    hash(&[bytes])
}

fn exact_array<const N: usize>(bytes: &[u8]) -> Result<[u8; N], PreparedSettlementFormatErrorV1> {
    bytes
        .try_into()
        .map_err(|_| PreparedSettlementFormatErrorV1::WrongLength)
}

fn exact_ref<const N: usize>(bytes: &[u8]) -> Result<&[u8; N], PreparedSettlementFormatErrorV1> {
    bytes
        .try_into()
        .map_err(|_| PreparedSettlementFormatErrorV1::WrongLength)
}

fn zeroed_box<const N: usize>() -> Result<Box<[u8; N]>, PreparedSettlementFormatErrorV1> {
    let raw: Box<[u8]> = vec![0u8; N].into_boxed_slice();
    raw.try_into()
        .map_err(|_| PreparedSettlementFormatErrorV1::WrongLength)
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
        leaf_index: u64::from_le_bytes(exact_array(&bytes[..8])?),
        root_sequence: u64::from_le_bytes(exact_array(&bytes[8..16])?),
        root: decode_digest_canonical(&exact_array(&bytes[16..48])?)
            .map_err(|_| PreparedSettlementFormatErrorV1::NonCanonicalDigest)?,
        history: aspis_statement::pool_v1::RootHistoryLocationV1 {
            page_number: u64::from_le_bytes(exact_array(&bytes[48..56])?),
            slot: u16::from_le_bytes(exact_array(&bytes[56..58])?),
        },
    };
    if !receipt_is_exact(&receipt) {
        return Err(PreparedSettlementFormatErrorV1::InvalidReceipt);
    }
    Ok(receipt)
}

fn digest32(bytes: &[u8]) -> Result<Digest, PreparedSettlementFormatErrorV1> {
    decode_digest_canonical(&exact_array(bytes)?)
        .map_err(|_| PreparedSettlementFormatErrorV1::NonCanonicalDigest)
}

fn encode_rollover_shard_v1<WriteRolloverPage>(
    fields: PreparedSettlementPlanFieldsV1<'_>,
    core_address: &Pubkey,
    next_page_address: [u8; 32],
    write_rollover_page: WriteRolloverPage,
    hash: HashFn,
) -> Result<PreparedSettlementRolloverShardImageV1, PreparedSettlementFormatErrorV1>
where
    WriteRolloverPage: FnOnce(&mut [u8]),
{
    let program_id = Pubkey::new_from_array(fields.program_id);
    let (address, pda_bump) =
        pool_v1_prepared_settlement_rollover_address(&program_id, core_address);
    let mut output = zeroed_box::<POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES>()?;
    output[..4].copy_from_slice(&POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_MAGIC);
    output[4] = POOL_V1_PREPARED_SETTLEMENT_VERSION;
    output[5] = POOL_V1_PREPARED_SETTLEMENT_HASH_SHA256;
    output[6] = pda_bump;
    output[SHARD_CORE_ADDRESS_OFFSET..SHARD_PROGRAM_OFFSET].copy_from_slice(core_address.as_ref());
    output[SHARD_PROGRAM_OFFSET..SHARD_POOL_OFFSET].copy_from_slice(&fields.program_id);
    output[SHARD_POOL_OFFSET..SHARD_STATEMENT_DIGEST_OFFSET].copy_from_slice(&fields.pool);
    output[SHARD_STATEMENT_DIGEST_OFFSET..SHARD_SOURCE_SEQUENCE_OFFSET]
        .copy_from_slice(&fields.statement_digest);
    output[SHARD_SOURCE_SEQUENCE_OFFSET..SHARD_PLAN_AUTHORITY_OFFSET]
        .copy_from_slice(&fields.source_sequence.to_le_bytes());
    output[SHARD_PLAN_AUTHORITY_OFFSET..SHARD_NEXT_PAGE_ADDRESS_OFFSET]
        .copy_from_slice(&fields.plan_authority);
    output[SHARD_NEXT_PAGE_ADDRESS_OFFSET..SHARD_NEXT_PAGE_IMAGE_OFFSET]
        .copy_from_slice(&next_page_address);
    write_rollover_page(&mut output[SHARD_NEXT_PAGE_IMAGE_OFFSET..SHARD_DIGEST_OFFSET]);
    let digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_DIGEST_DOMAIN,
        &output[..SHARD_DIGEST_OFFSET],
    ]);
    output[SHARD_DIGEST_OFFSET..].copy_from_slice(&digest);
    Ok(PreparedSettlementRolloverShardImageV1 {
        address,
        pda_bump,
        image: output,
    })
}

pub(crate) fn encode_prepared_settlement_plan_v1<WriteCurrentPage, WriteRolloverPage>(
    fields: PreparedSettlementPlanFieldsV1<'_>,
    write_current_page: WriteCurrentPage,
    write_rollover_page: WriteRolloverPage,
    hash: HashFn,
) -> Result<PreparedSettlementPlanImagesV1, PreparedSettlementFormatErrorV1>
where
    WriteCurrentPage: FnOnce(&mut [u8]),
    WriteRolloverPage: FnOnce(&mut [u8]),
{
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
    let (page_count, next_page_address, next_page_digest) = match (
        fields.next_page_address,
        fields.source_next_page_image_digest,
    ) {
        (None, None) => (1u8, [0u8; 32], [0u8; 32]),
        (Some(address), Some(digest)) => (2u8, address, digest),
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

    let program_id = Pubkey::new_from_array(fields.program_id);
    let pool = Pubkey::new_from_array(fields.pool);
    let plan_authority = Pubkey::new_from_array(fields.plan_authority);
    let (core_address, core_bump) = pool_v1_prepared_settlement_plan_address(
        &program_id,
        &pool,
        &fields.statement_digest,
        fields.source_sequence,
        &plan_authority,
    );
    if fields.pda_bump != core_bump {
        return Err(PreparedSettlementFormatErrorV1::InvalidPda);
    }
    // Allocate the core first and write the current history page directly into
    // its final slice. This deliberately avoids a separate 8,256-byte staging
    // image on Solana's default 32 KiB heap.
    let mut output = zeroed_box::<POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES>()?;
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
    write_current_page(
        &mut output[NEXT_CURRENT_PAGE_IMAGE_OFFSET..NEXT_ROLLOVER_PAGE_IMAGE_OFFSET],
    );
    // The optional rollover page is likewise written directly into the final
    // shard allocation. At no point are two standalone history-page images
    // live alongside the 10,000-byte core and 8,504-byte shard.
    let rollover_shard = if page_count == 2 {
        Some(encode_rollover_shard_v1(
            fields,
            &core_address,
            next_page_address,
            write_rollover_page,
            hash,
        )?)
    } else {
        None
    };
    if let Some(shard) = &rollover_shard {
        output[ROLLOVER_SHARD_ADDRESS_OFFSET..ROLLOVER_SHARD_DIGEST_OFFSET]
            .copy_from_slice(shard.address.as_ref());
        output[ROLLOVER_SHARD_DIGEST_OFFSET..CORE_DIGEST_OFFSET]
            .copy_from_slice(&shard.image[SHARD_DIGEST_OFFSET..]);
    }
    let digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_DIGEST_DOMAIN,
        &output[..CORE_DIGEST_OFFSET],
    ]);
    output[CORE_DIGEST_OFFSET..].copy_from_slice(&digest);
    Ok(PreparedSettlementPlanImagesV1 {
        core_address,
        core_pda_bump: core_bump,
        source_sequence: fields.source_sequence,
        statement_digest: fields.statement_digest,
        core_image: output,
        rollover_shard,
    })
}

#[allow(clippy::too_many_arguments)]
fn decode_rollover_shard_v1<'a>(
    core_address: &Pubkey,
    expected_program: [u8; 32],
    expected_pool: [u8; 32],
    expected_statement_digest: [u8; 32],
    expected_source_sequence: u64,
    expected_plan_authority: [u8; 32],
    expected_next_page_address: [u8; 32],
    expected_shard_address: [u8; 32],
    expected_shard_digest: [u8; 32],
    account: PreparedSettlementRolloverShardAccountV1<'a>,
    hash: HashFn,
) -> Result<
    &'a [u8; aspis_statement::pool_v1::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
    PreparedSettlementFormatErrorV1,
> {
    let bytes: &[u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES] =
        exact_ref(account.image)?;
    if bytes[..4] != POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_MAGIC {
        return Err(PreparedSettlementFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PREPARED_SETTLEMENT_VERSION {
        return Err(PreparedSettlementFormatErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PREPARED_SETTLEMENT_HASH_SHA256 {
        return Err(PreparedSettlementFormatErrorV1::WrongHashAlgorithm);
    }
    if bytes[7..POOL_V1_PREPARED_SETTLEMENT_HEADER_BYTES] != [0u8; 9] {
        return Err(PreparedSettlementFormatErrorV1::NonZeroReserved);
    }
    let digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_DIGEST_DOMAIN,
        &bytes[..SHARD_DIGEST_OFFSET],
    ]);
    if bytes[SHARD_DIGEST_OFFSET..] != digest || digest != expected_shard_digest {
        return Err(PreparedSettlementFormatErrorV1::DigestMismatch);
    }
    let program_id = Pubkey::new_from_array(expected_program);
    let (expected_address, expected_bump) =
        pool_v1_prepared_settlement_rollover_address(&program_id, core_address);
    if account.owner != &program_id
        || account.address != &expected_address
        || account.address.to_bytes() != expected_shard_address
        || bytes[6] != expected_bump
        || bytes[SHARD_CORE_ADDRESS_OFFSET..SHARD_PROGRAM_OFFSET] != core_address.to_bytes()
        || bytes[SHARD_PROGRAM_OFFSET..SHARD_POOL_OFFSET] != expected_program
        || bytes[SHARD_POOL_OFFSET..SHARD_STATEMENT_DIGEST_OFFSET] != expected_pool
        || bytes[SHARD_STATEMENT_DIGEST_OFFSET..SHARD_SOURCE_SEQUENCE_OFFSET]
            != expected_statement_digest
        || bytes[SHARD_SOURCE_SEQUENCE_OFFSET..SHARD_PLAN_AUTHORITY_OFFSET]
            != expected_source_sequence.to_le_bytes()
        || bytes[SHARD_PLAN_AUTHORITY_OFFSET..SHARD_NEXT_PAGE_ADDRESS_OFFSET]
            != expected_plan_authority
        || bytes[SHARD_NEXT_PAGE_ADDRESS_OFFSET..SHARD_NEXT_PAGE_IMAGE_OFFSET]
            != expected_next_page_address
    {
        return Err(PreparedSettlementFormatErrorV1::WrongShard);
    }
    exact_ref(&bytes[SHARD_NEXT_PAGE_IMAGE_OFFSET..SHARD_DIGEST_OFFSET])
}

pub(crate) fn decode_prepared_settlement_plan_v1<'a>(
    core_address: &Pubkey,
    core_bytes: &'a [u8],
    rollover_shard: Option<PreparedSettlementRolloverShardAccountV1<'a>>,
    hash: HashFn,
) -> Result<PreparedSettlementPlanViewV1<'a>, PreparedSettlementFormatErrorV1> {
    let bytes: &[u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES] = exact_ref(core_bytes)?;
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
        &bytes[..CORE_DIGEST_OFFSET],
    ]);
    if bytes[CORE_DIGEST_OFFSET..] != expected_digest {
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
    let program_id = exact_array(&bytes[PROGRAM_OFFSET..POOL_OFFSET])?;
    let pool = exact_array(&bytes[POOL_OFFSET..PLAN_AUTHORITY_OFFSET])?;
    let plan_authority = exact_array(&bytes[PLAN_AUTHORITY_OFFSET..SOURCE_SEQUENCE_OFFSET])?;
    if plan_authority == [0u8; 32] {
        return Err(PreparedSettlementFormatErrorV1::ZeroPlanAuthority);
    }
    let source_sequence = u64::from_le_bytes(exact_array(
        &bytes[SOURCE_SEQUENCE_OFFSET..SOURCE_ROOT_OFFSET],
    )?);
    let statement_digest = exact_array(&bytes[STATEMENT_DIGEST_OFFSET..NULLIFIER_OFFSET])?;
    let (expected_core_address, expected_core_bump) = pool_v1_prepared_settlement_plan_address(
        &Pubkey::new_from_array(program_id),
        &Pubkey::new_from_array(pool),
        &statement_digest,
        source_sequence,
        &Pubkey::new_from_array(plan_authority),
    );
    if *core_address != expected_core_address || bytes[9] != expected_core_bump {
        return Err(PreparedSettlementFormatErrorV1::InvalidPda);
    }
    let next_page_raw = exact_array(&bytes[NEXT_PAGE_ADDRESS_OFFSET..NEXT_PAGE_DIGEST_OFFSET])?;
    let next_page_digest_raw =
        exact_array(&bytes[NEXT_PAGE_DIGEST_OFFSET..STATEMENT_DIGEST_OFFSET])?;
    let shard_address_raw =
        exact_array(&bytes[ROLLOVER_SHARD_ADDRESS_OFFSET..ROLLOVER_SHARD_DIGEST_OFFSET])?;
    let shard_digest_raw = exact_array(&bytes[ROLLOVER_SHARD_DIGEST_OFFSET..CORE_DIGEST_OFFSET])?;
    let (next_page_address, source_next_page_image_digest, rollover_shard_address, next_image) =
        match bytes[8] {
            1 if next_page_raw == [0u8; 32]
                && next_page_digest_raw == [0u8; 32]
                && shard_address_raw == [0u8; 32]
                && shard_digest_raw == [0u8; 32]
                && rollover_shard.is_none() =>
            {
                (None, None, None, None)
            }
            2 if next_page_raw != [0u8; 32]
                && next_page_digest_raw != [0u8; 32]
                && shard_address_raw != [0u8; 32]
                && shard_digest_raw != [0u8; 32] =>
            {
                let shard = rollover_shard.ok_or(PreparedSettlementFormatErrorV1::WrongShard)?;
                let image = decode_rollover_shard_v1(
                    core_address,
                    program_id,
                    pool,
                    statement_digest,
                    source_sequence,
                    plan_authority,
                    next_page_raw,
                    shard_address_raw,
                    shard_digest_raw,
                    shard,
                    hash,
                )?;
                (
                    Some(next_page_raw),
                    Some(next_page_digest_raw),
                    Some(shard_address_raw),
                    Some(image),
                )
            }
            _ => return Err(PreparedSettlementFormatErrorV1::WrongPageCount),
        };
    let not_before_slot = u64::from_le_bytes(exact_array(
        &bytes[NOT_BEFORE_SLOT_OFFSET..EXPIRES_AT_SLOT_OFFSET],
    )?);
    let expires_at_slot = u64::from_le_bytes(exact_array(
        &bytes[EXPIRES_AT_SLOT_OFFSET..FIRST_COMMITMENT_OFFSET],
    )?);
    if not_before_slot > expires_at_slot {
        return Err(PreparedSettlementFormatErrorV1::InvalidTimeRange);
    }
    Ok(PreparedSettlementPlanViewV1 {
        pda_bump: bytes[9],
        transition_kind,
        program_id,
        pool,
        plan_authority,
        source_sequence,
        source_root: digest32(&bytes[SOURCE_ROOT_OFFSET..SOURCE_POOL_DIGEST_OFFSET])?,
        source_pool_image_digest: exact_array(
            &bytes[SOURCE_POOL_DIGEST_OFFSET..CURRENT_PAGE_ADDRESS_OFFSET],
        )?,
        current_page_address: exact_array(
            &bytes[CURRENT_PAGE_ADDRESS_OFFSET..CURRENT_PAGE_DIGEST_OFFSET],
        )?,
        source_current_page_image_digest: exact_array(
            &bytes[CURRENT_PAGE_DIGEST_OFFSET..NEXT_PAGE_ADDRESS_OFFSET],
        )?,
        next_page_address,
        source_next_page_image_digest,
        rollover_shard_address,
        statement_digest,
        nullifier: digest32(&bytes[NULLIFIER_OFFSET..AUTHORIZATION_RECEIPT_ADDRESS_OFFSET])?,
        authorization_receipt_address: exact_array(
            &bytes[AUTHORIZATION_RECEIPT_ADDRESS_OFFSET..AUTHORIZATION_RECEIPT_DIGEST_OFFSET],
        )?,
        authorization_receipt_image_digest: exact_array(
            &bytes[AUTHORIZATION_RECEIPT_DIGEST_OFFSET..NOT_BEFORE_SLOT_OFFSET],
        )?,
        not_before_slot,
        expires_at_slot,
        first_commitment: digest32(&bytes[FIRST_COMMITMENT_OFFSET..SECOND_COMMITMENT_OFFSET])?,
        second_commitment,
        first_receipt,
        second_receipt,
        next_pool_image: exact_ref(&bytes[NEXT_POOL_IMAGE_OFFSET..NEXT_CURRENT_PAGE_IMAGE_OFFSET])?,
        next_current_page_image: exact_ref(
            &bytes[NEXT_CURRENT_PAGE_IMAGE_OFFSET..NEXT_ROLLOVER_PAGE_IMAGE_OFFSET],
        )?,
        next_rollover_page_image: next_image,
    })
}

#[cfg(test)]
pub(crate) fn reauthenticate_prepared_settlement_plan_for_test(
    bytes: &mut [u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES],
    hash: HashFn,
) {
    let digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_DIGEST_DOMAIN,
        &bytes[..CORE_DIGEST_OFFSET],
    ]);
    bytes[CORE_DIGEST_OFFSET..].copy_from_slice(&digest);
}

#[cfg(test)]
pub(crate) fn reauthenticate_prepared_settlement_rollover_for_test(
    bytes: &mut [u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES],
    hash: HashFn,
) {
    let digest = hash(&[
        POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_DIGEST_DOMAIN,
        &bytes[..SHARD_DIGEST_OFFSET],
    ]);
    bytes[SHARD_DIGEST_OFFSET..].copy_from_slice(&digest);
}

#[cfg(test)]
pub(crate) fn bind_prepared_settlement_rollover_for_test(
    core: &mut [u8; POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES],
    shard: &[u8; POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES],
    hash: HashFn,
) {
    core[ROLLOVER_SHARD_DIGEST_OFFSET..CORE_DIGEST_OFFSET]
        .copy_from_slice(&shard[SHARD_DIGEST_OFFSET..]);
    reauthenticate_prepared_settlement_plan_for_test(core, hash);
}
