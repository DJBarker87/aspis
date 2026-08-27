#![no_std]
#![allow(unexpected_cfgs)]

extern crate alloc;

use alloc::format;
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program, program_error::ProgramError,
    pubkey::Pubkey,
};

const PROOF_MAGIC: [u8; 4] = *b"ASPU";
const PROOF_HEADER_BYTES: usize = 40;
const ASJA_BYTES: usize = 688;

solana_program::entrypoint!(process_instruction);

/// Measurement-only selected-verifier transport double.  It exercises a real
/// CPI and immediate return-data authentication, but performs no proof work:
/// the exact ASJA image is carried in the framed verifier-owned proof body.
pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    _instruction_data: &[u8],
) -> ProgramResult {
    let [proof] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    if proof.is_writable || proof.is_signer || proof.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    let data = proof.try_borrow_data()?;
    if data.len() != PROOF_HEADER_BYTES + ASJA_BYTES
        || data[..4] != PROOF_MAGIC
        || u32::from_le_bytes(data[4..8].try_into().unwrap()) != ASJA_BYTES as u32
        || data[8..PROOF_HEADER_BYTES].iter().any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    program::set_return_data(&data[PROOF_HEADER_BYTES..]);
    Ok(())
}
