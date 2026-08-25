//! Zero-copy validation and mutation helpers for Pool V1 root pages.

use aspis_core::field::P;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        root_history_location, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_ROOT_HISTORY_CAPACITY,
        POOL_V1_ROOT_HISTORY_CAPACITY_LOG2, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_MAGIC, POOL_V1_ROOT_HISTORY_PAGE_SEED,
        POOL_V1_ROOT_HISTORY_PAGE_VERSION,
    },
    poseidon2::Digest,
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::error::PoolV1ProgramError;

const PAGE_POOL_OFFSET: usize = 8;
const PAGE_NUMBER_OFFSET: usize = 40;
const PAGE_FIRST_SEQUENCE_OFFSET: usize = 48;
const PAGE_FILLED_OFFSET: usize = 56;
const PAGE_ROOTS_OFFSET: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootPageHeaderV1 {
    pub pool: Pubkey,
    pub page_number: u64,
    pub first_sequence: u64,
    pub filled: u16,
}

pub fn pool_v1_root_page_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
) -> (Pubkey, u8) {
    let page_number_bytes = page_number.to_le_bytes();
    Pubkey::find_program_address(
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            pool.as_ref(),
            &page_number_bytes,
        ],
        program_id,
    )
}

pub(crate) fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

pub(crate) fn require_program_account(
    account: &AccountInfo,
    program_id: &Pubkey,
    writable: bool,
) -> Result<(), ProgramError> {
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if account.executable || account.is_writable != writable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

pub(crate) fn require_program_owned(
    account: &AccountInfo,
    program_id: &Pubkey,
) -> Result<(), ProgramError> {
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

pub(crate) fn require_root_page_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    let expected = pool_v1_root_page_address(program_id, pool, page_number).0;
    if account.key != &expected {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    Ok(())
}

pub(crate) fn validate_root_page_bytes(
    data: &[u8],
    expected_pool: &Pubkey,
    expected_page_number: u64,
) -> Result<RootPageHeaderV1, ProgramError> {
    if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
        || data[..4] != POOL_V1_ROOT_HISTORY_PAGE_MAGIC
        || data[4] != POOL_V1_ROOT_HISTORY_PAGE_VERSION
        || data[5] != POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
        || data[6] != POOL_V1_DIGEST_ENCODING_VERSION
        || data[7] != 0
        || data[58..64] != [0u8; 6]
    {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    let pool = Pubkey::new_from_array(
        data[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET]
            .try_into()
            .unwrap(),
    );
    let page_number = u64::from_le_bytes(
        data[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
            .try_into()
            .unwrap(),
    );
    let first_sequence = u64::from_le_bytes(
        data[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
            .try_into()
            .unwrap(),
    );
    let filled = u16::from_le_bytes(data[PAGE_FILLED_OFFSET..58].try_into().unwrap());
    let expected_first = page_number
        .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    if pool != *expected_pool
        || page_number != expected_page_number
        || first_sequence != expected_first
        || usize::from(filled) > POOL_V1_ROOT_HISTORY_CAPACITY
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    for slot in 0..usize::from(filled) {
        let start = PAGE_ROOTS_OFFSET + slot * 32;
        decode_digest_canonical(data[start..start + 32].try_into().unwrap())
            .map_err(|_| ProgramError::InvalidAccountData)?;
    }
    let unused_start = PAGE_ROOTS_OFFSET + usize::from(filled) * 32;
    if data[unused_start..].iter().any(|byte| *byte != 0) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(RootPageHeaderV1 {
        pool,
        page_number,
        first_sequence,
        filled,
    })
}

pub(crate) fn read_retained_root(
    data: &[u8],
    header: RootPageHeaderV1,
    sequence: u64,
) -> Result<Digest, ProgramError> {
    let location = root_history_location(sequence);
    if location.page_number != header.page_number || location.slot >= header.filled {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let start = PAGE_ROOTS_OFFSET + usize::from(location.slot) * 32;
    decode_digest_canonical(data[start..start + 32].try_into().unwrap())
        .map_err(|_| ProgramError::InvalidAccountData)
}

pub(crate) fn write_new_page_unchecked(
    data: &mut [u8],
    pool: &Pubkey,
    page_number: u64,
    first_sequence: u64,
    roots: &[Digest],
) {
    debug_assert_eq!(data.len(), POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES);
    debug_assert!(roots.len() <= POOL_V1_ROOT_HISTORY_CAPACITY);
    data.fill(0);
    data[..4].copy_from_slice(&POOL_V1_ROOT_HISTORY_PAGE_MAGIC);
    data[4] = POOL_V1_ROOT_HISTORY_PAGE_VERSION;
    data[5] = POOL_V1_ROOT_HISTORY_CAPACITY_LOG2;
    data[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    data[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET].copy_from_slice(pool.as_ref());
    data[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
        .copy_from_slice(&page_number.to_le_bytes());
    data[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
        .copy_from_slice(&first_sequence.to_le_bytes());
    data[PAGE_FILLED_OFFSET..58].copy_from_slice(&(roots.len() as u16).to_le_bytes());
    for (slot, root) in roots.iter().enumerate() {
        let start = PAGE_ROOTS_OFFSET + slot * 32;
        data[start..start + 32].copy_from_slice(&encode_digest_canonical(root));
    }
}

pub(crate) fn append_roots_unchecked(data: &mut [u8], header: RootPageHeaderV1, roots: &[Digest]) {
    debug_assert!(usize::from(header.filled) + roots.len() <= POOL_V1_ROOT_HISTORY_CAPACITY);
    for (offset, root) in roots.iter().enumerate() {
        let slot = usize::from(header.filled) + offset;
        let start = PAGE_ROOTS_OFFSET + slot * 32;
        data[start..start + 32].copy_from_slice(&encode_digest_canonical(root));
    }
    let filled = header.filled + roots.len() as u16;
    data[PAGE_FILLED_OFFSET..58].copy_from_slice(&filled.to_le_bytes());
}

pub(crate) fn validate_new_page_account(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    require_program_account(account, program_id, true)?;
    require_root_page_address(program_id, pool, page_number, account)?;
    let data = account.try_borrow_data()?;
    if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES || data.iter().any(|byte| *byte != 0) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
