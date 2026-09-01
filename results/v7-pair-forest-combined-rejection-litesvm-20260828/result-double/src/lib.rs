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

solana_program::entrypoint!(process_instruction);

/// Test-only immutable selected-verifier double. The Pool still authenticates
/// this program through the full Registry V2 ProgramData/hash certificate;
/// the double returns the exact proof-account body so the outer Pool can be
/// exercised against wrong-length and canonical-but-wrong ASR8 results.
pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    _instruction_data: &[u8],
) -> ProgramResult {
    let proof = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if proof.is_writable || proof.is_signer || proof.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    let data = proof.try_borrow_data()?;
    if data.len() < PROOF_HEADER_BYTES
        || data[..4] != PROOF_MAGIC
        || data[8..PROOF_HEADER_BYTES].iter().any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let body_len = u32::from_le_bytes(
        data[4..8]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ) as usize;
    if body_len != data.len() - PROOF_HEADER_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    program::set_return_data(&data[PROOF_HEADER_BYTES..]);
    Ok(())
}
