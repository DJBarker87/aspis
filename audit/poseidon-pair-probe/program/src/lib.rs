#![allow(unexpected_cfgs)]

use aspis_core::field::M31;
use aspis_statement::pool_v1::pool_v1_tree_parent;
use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult, program::set_return_data,
    program_error::ProgramError, pubkey::Pubkey,
};

entrypoint!(process_instruction);

fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if !accounts.is_empty() || instruction_data.len() != 2 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let count = u16::from_le_bytes(instruction_data.try_into().unwrap());
    let right = core::array::from_fn(|lane| M31(200 + lane as u32));
    let mut node = core::array::from_fn(|lane| M31(100 + lane as u32));
    for _ in 0..count {
        node = pool_v1_tree_parent(&node, &right);
    }
    let mut encoded = [0u8; 32];
    for (lane, value) in node.iter().enumerate() {
        encoded[4 * lane..4 * lane + 4].copy_from_slice(&value.0.to_le_bytes());
    }
    set_return_data(&encoded);
    Ok(())
}
