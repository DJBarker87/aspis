#[cfg(not(feature = "no-entrypoint"))]
use solana_program::entrypoint;
use solana_program::{
    account_info::AccountInfo, declare_id, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};

use circle_p3_core::{mirror_verify_scenario_bytes, parse_instruction_data};

declare_id!("CiRcLeP3Vrfy9oN4v5v7yLFV7hWgZB9D8vM1g8K3p3S");

#[cfg(not(feature = "no-entrypoint"))]
entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    _accounts: &[AccountInfo],
    input: &[u8],
) -> ProgramResult {
    let (kind, proof_bytes) =
        parse_instruction_data(input).map_err(|_| ProgramError::InvalidInstructionData)?;
    mirror_verify_scenario_bytes(kind, proof_bytes)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(())
}
