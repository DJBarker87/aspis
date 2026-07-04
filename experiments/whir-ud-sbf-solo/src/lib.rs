#[cfg(not(feature = "no-entrypoint"))]
use solana_program::entrypoint;
use solana_program::{
    account_info::AccountInfo, declare_id, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};
use whir_ud_host::{mirror_verify_scenario_bytes, ScenarioConfig, VectorPattern};

declare_id!("11111111111111111111111111111111");

#[cfg(not(feature = "no-entrypoint"))]
entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    _accounts: &[AccountInfo],
    input: &[u8],
) -> ProgramResult {
    let config = ScenarioConfig {
        name: "whir-ud-goldilocks2".to_string(),
        security_level: 100,
        pow_bits: 20,
        num_variables: 4,
        evaluations: 1,
        linear_constraints: 0,
        rate_bits: 1,
        initial_folding_factor: 4,
        folding_factor: 4,
        unique_decoding: true,
        vector_pattern: VectorPattern::Ascending,
    };
    mirror_verify_scenario_bytes(&config, input)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(())
}
