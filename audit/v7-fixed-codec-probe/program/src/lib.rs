#![allow(unexpected_cfgs)]

use aspis_core::v7_fixed_codec_experiment::{
    experimental_fixed_section_checksum, selected_packed_fixed_section_checksum,
    V7FixedCodecVariant,
};
use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult, log::sol_log_compute_units,
    program::set_return_data, program_error::ProgramError, pubkey::Pubkey,
};

entrypoint!(process_instruction);

fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let [proof_account] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    let [mode] = instruction_data else {
        return Err(ProgramError::InvalidInstructionData);
    };
    if proof_account.is_writable || proof_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    let data = proof_account.try_borrow_data()?;
    sol_log_compute_units();
    let checksum = match mode {
        0 => selected_packed_fixed_section_checksum(&data),
        1 => experimental_fixed_section_checksum(&data, V7FixedCodecVariant::CanonicalPreFinal),
        2 => experimental_fixed_section_checksum(&data, V7FixedCodecVariant::CanonicalFinal256),
        3 => experimental_fixed_section_checksum(&data, V7FixedCodecVariant::CanonicalBoth),
        _ => return Err(ProgramError::InvalidInstructionData),
    }
    .map_err(|_| ProgramError::InvalidAccountData)?;
    sol_log_compute_units();
    let mut encoded = [0u8; 16];
    checksum.write_le_bytes(&mut encoded);
    set_return_data(&encoded);
    Ok(())
}
