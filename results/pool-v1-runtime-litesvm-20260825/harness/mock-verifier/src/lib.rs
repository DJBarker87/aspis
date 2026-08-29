//! Test-only verifier transport double for the Pool runtime harness.
//!
//! This program deliberately proves no cryptographic statement. It accepts
//! only the frozen ASVQ framing, echoes the 384-byte authenticated binding as
//! ASVS, replaces the verify code with the frozen success code, and publishes
//! that byte string as Solana return data. The Pool still authenticates the
//! selected program, registry entry, proof-account owner/body digest and every
//! echoed binding byte. Consequently this double exercises real cross-program
//! invocation and return-data plumbing without being evidence for Tag-73.

#![no_std]
#![allow(unexpected_cfgs)]

extern crate alloc;

#[cfg(target_os = "solana")]
use alloc::format;
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program, program_error::ProgramError,
    pubkey::Pubkey,
};

const ASVQ_MAGIC: [u8; 4] = *b"ASVQ";
const ASVS_MAGIC: [u8; 4] = *b"ASVS";
const VERSION: u8 = 1;
const BINDING_BYTES: usize = 384;
const SUCCESS_CODE: u32 = 0x4153_0001;

solana_program::entrypoint!(process_instruction);

fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    let [proof] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    if proof.owner != program_id
        || proof.is_signer
        || proof.is_writable
        || proof.executable
        || instruction_data.len() <= BINDING_BYTES
        || instruction_data[..4] != ASVQ_MAGIC
        || instruction_data[4] != VERSION
        || instruction_data[8..12] != 1u32.to_le_bytes()
        || u32::from_le_bytes(instruction_data[380..384].try_into().unwrap()) as usize
            != instruction_data.len() - BINDING_BYTES
    {
        return Err(ProgramError::InvalidInstructionData);
    }

    let mut result = [0u8; BINDING_BYTES];
    result.copy_from_slice(&instruction_data[..BINDING_BYTES]);
    result[..4].copy_from_slice(&ASVS_MAGIC);
    result[8..12].copy_from_slice(&SUCCESS_CODE.to_le_bytes());
    program::set_return_data(&result);
    Ok(())
}
