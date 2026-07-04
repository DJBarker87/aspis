//! Aspis on-chain verifier (Stage 0 slice).
//!
//! The program is the crate seam the design cares about: it parses and
//! verifies proof envelopes against a statement digest and knows nothing
//! about spends. Staged upload follows the Yano pattern: a proof account is
//! populated chunk by chunk, then `Verify` runs `aspis_core::verify` over it
//! with the SHA-256 syscall as the hash backend.
//!
//! Proof account layout: [0..4] proof_len u32 LE, [4..4+proof_len] bytes.

use borsh::{BorshDeserialize, BorshSerialize};
#[cfg(not(feature = "no-entrypoint"))]
use solana_program::entrypoint;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    declare_id,
    entrypoint::ProgramResult,
    hash::hashv,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

declare_id!("2Ao6ThT7qABozK7zD7UwSsAC64zyZY34TfSB8TAYPxTD");

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize)]
pub enum AspisInstruction {
    /// Set the proof length header. Account must be pre-created with owner =
    /// this program and space >= 4 + total_len.
    InitProof { total_len: u32 },
    /// Copy `chunk` into the proof body at `offset`.
    UploadChunk { offset: u32, chunk: Vec<u8> },
    /// Verify the uploaded proof against `statement_digest`.
    Verify { statement_digest: [u8; 32] },
}

/// hashv-shaped backend over the Solana SHA-256 syscall.
fn sbf_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    hashv(inputs).to_bytes()
}

#[cfg(not(feature = "no-entrypoint"))]
entrypoint!(process_instruction);

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let instruction = AspisInstruction::try_from_slice(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let account_iter = &mut accounts.iter();
    let proof_account = next_account_info(account_iter)?;
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }

    match instruction {
        AspisInstruction::InitProof { total_len } => {
            let mut data = proof_account.try_borrow_mut_data()?;
            if data.len() < 4 + total_len as usize {
                return Err(ProgramError::AccountDataTooSmall);
            }
            data[0..4].copy_from_slice(&total_len.to_le_bytes());
            Ok(())
        }
        AspisInstruction::UploadChunk { offset, chunk } => {
            let mut data = proof_account.try_borrow_mut_data()?;
            let total_len = u32::from_le_bytes(data[0..4].try_into().unwrap()) as usize;
            let start = 4 + offset as usize;
            let end = start
                .checked_add(chunk.len())
                .ok_or(ProgramError::InvalidInstructionData)?;
            if offset as usize + chunk.len() > total_len || end > data.len() {
                return Err(ProgramError::InvalidInstructionData);
            }
            data[start..end].copy_from_slice(&chunk);
            Ok(())
        }
        AspisInstruction::Verify { statement_digest } => {
            let data = proof_account.try_borrow_data()?;
            let total_len = u32::from_le_bytes(data[0..4].try_into().unwrap()) as usize;
            if 4 + total_len > data.len() {
                return Err(ProgramError::InvalidAccountData);
            }
            let proof = &data[4..4 + total_len];
            match aspis_core::verify(proof, &statement_digest, sbf_hashv) {
                Ok(()) => {
                    msg!("aspis: proof accepted");
                    Ok(())
                }
                Err(err) => {
                    msg!("aspis: proof rejected");
                    Err(ProgramError::Custom(err.code()))
                }
            }
        }
    }
}
