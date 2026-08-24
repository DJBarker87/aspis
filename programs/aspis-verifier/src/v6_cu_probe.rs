//! Isolated local-validator probe for the V6 packed parser and final evaluator.
//!
//! This module is never part of a production feature set. It measures the
//! exact no-allocation parser, compact-frontier counter, and all sixteen
//! packed final-256 evaluations against a sealed proof account.

use aspis_core::field::QM31;
use aspis_core::v6_onefold::{
    binary_frontier_nodes, evaluate_packed_final256_at_queries, V6OneFoldWire, V6_QUERY_COUNT,
};
use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    hash::hashv,
    log::{sol_log_compute_units, sol_log_data},
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

pub const V6_CU_PROBE_TAG: u8 = 68;
pub const V6_CU_PROBE_WIRE_BYTES: usize = 1 + 2 + 2 + V6_QUERY_COUNT * 4;

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_v6_cu_probe_instruction);

fn read_u16(input: &mut &[u8]) -> Result<u16, ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<2>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(u16::from_le_bytes(*head))
}

fn read_u32(input: &mut &[u8]) -> Result<u32, ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<4>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(u32::from_le_bytes(*head))
}

fn qm31_bytes(value: QM31) -> [u8; 16] {
    let mut bytes = [0u8; 16];
    value.write_le_bytes(&mut bytes);
    bytes
}

pub fn process_v6_cu_probe_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() != V6_CU_PROBE_WIRE_BYTES
        || instruction_data.first().copied() != Some(V6_CU_PROBE_TAG)
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if proof_account.owner != program_id || proof_account.is_writable {
        return Err(ProgramError::IncorrectProgramId);
    }

    let mut input = &instruction_data[1..];
    let c1_frontier_nodes = usize::from(read_u16(&mut input)?);
    let c2_frontier_nodes = usize::from(read_u16(&mut input)?);
    let mut queries = [0u32; V6_QUERY_COUNT];
    for query in &mut queries {
        *query = read_u32(&mut input)?;
    }
    if !input.is_empty() {
        return Err(ProgramError::InvalidInstructionData);
    }

    let account_data = proof_account.try_borrow_data()?;
    if !crate::lifecycle::proof_account_finalized(&account_data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = crate::lifecycle::uploaded_proof_bounds(&account_data)?;
    let proof = &account_data[proof_start..proof_end];

    msg!("aspis-v6-cu:entry");
    sol_log_compute_units();
    let parsed =
        V6OneFoldWire::parse_deferred_canonicality(proof, c1_frontier_nodes, c2_frontier_nodes)
            .map_err(|_| ProgramError::InvalidAccountData)?;
    msg!("aspis-v6-cu:parsed");
    sol_log_compute_units();

    let frontier =
        binary_frontier_nodes(queries, 18).map_err(|_| ProgramError::InvalidInstructionData)?;
    if frontier != c1_frontier_nodes || frontier != c2_frontier_nodes {
        return Err(ProgramError::InvalidInstructionData);
    }
    msg!("aspis-v6-cu:frontier");
    sol_log_compute_units();

    let evaluated = evaluate_packed_final256_at_queries(parsed.fixed_fields_packed, queries)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let outputs = evaluated.map(qm31_bytes);
    msg!("aspis-v6-cu:final-evaluations");
    sol_log_compute_units();

    let slices: [&[u8]; V6_QUERY_COUNT] = core::array::from_fn(|index| outputs[index].as_slice());
    let sink = hashv(&slices);
    sol_log_data(&[b"aspis-v6-final256-probe-v1", sink.as_ref()]);
    msg!("aspis-v6-cu:sink");
    sol_log_compute_units();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lifecycle::PROOF_ACCOUNT_HEADER_LEN;
    use crate::test_support::make_account;
    use aspis_core::v6_onefold::{V6_BODY_WITHOUT_FRONTIERS, V6_FRONTIER_CAP_PER_TREE};

    fn clustered_queries() -> [u32; V6_QUERY_COUNT] {
        core::array::from_fn(|index| index as u32)
    }

    fn wire(frontier: usize, queries: [u32; V6_QUERY_COUNT]) -> Vec<u8> {
        let mut wire = Vec::with_capacity(V6_CU_PROBE_WIRE_BYTES);
        wire.push(V6_CU_PROBE_TAG);
        wire.extend_from_slice(&(frontier as u16).to_le_bytes());
        wire.extend_from_slice(&(frontier as u16).to_le_bytes());
        for query in queries {
            wire.extend_from_slice(&query.to_le_bytes());
        }
        wire
    }

    #[test]
    fn exact_sealed_probe_accepts_and_mismatched_frontier_rejects() {
        let program_id = crate::id();
        let proof_key = Pubkey::new_unique();
        let queries = clustered_queries();
        let frontier = binary_frontier_nodes(queries, 18).unwrap();
        assert!(frontier <= V6_FRONTIER_CAP_PER_TREE);
        let body_len = V6_BODY_WITHOUT_FRONTIERS + 2 * frontier * 32;
        let mut data = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + body_len];
        data[0..4].copy_from_slice(b"ASPU");
        data[4..8].copy_from_slice(&(body_len as u32).to_le_bytes());
        let mut lamports = 1;
        let proof = make_account(
            &proof_key,
            &program_id,
            &mut lamports,
            &mut data,
            false,
            false,
        );
        assert_eq!(
            process_v6_cu_probe_instruction(
                &program_id,
                &[proof.clone()],
                &wire(frontier, queries)
            ),
            Ok(())
        );
        assert_eq!(
            process_v6_cu_probe_instruction(&program_id, &[proof], &wire(frontier + 1, queries)),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn probe_feature_cannot_change_the_production_dispatch() {
        assert_eq!(
            crate::dispatch::process_spend_production_instruction(
                &crate::id(),
                &[],
                &[V6_CU_PROBE_TAG]
            ),
            Err(ProgramError::InvalidInstructionData)
        );
    }
}
