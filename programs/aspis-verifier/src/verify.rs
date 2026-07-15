//! Production proof verification (wire tags 59, 60, and 65).
//!
//! Every path decodes the public statement from the wire, requires a sealed
//! proof account, and runs the complete production verifier over the
//! uploaded proof bytes with the SHA-256 syscall backend. There is no
//! diagnostic or unmined bypass in this module: the dispatcher rejects the
//! wire's diagnostic selector before verification is reached.

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, hash::hashv, log::sol_log_compute_units,
    msg, program_error::ProgramError,
};

use crate::lifecycle::{proof_account_finalized, uploaded_proof_bounds};

pub(crate) fn sbf_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    hashv(inputs).to_bytes()
}

#[cfg_attr(not(feature = "spend-dynamic-rate512"), allow(dead_code))]
#[inline(always)]
fn m31_inverse_cluster_portable(value: aspis_core::field::M31) -> aspis_core::field::M31 {
    value.inv()
}

pub(crate) fn decode_spend_public(
    public_input: &[u8; 104],
) -> Result<aspis_statement::SpendPublic, ProgramError> {
    let mut public_values = [aspis_core::field::M31::ZERO; 25];
    for (index, output) in public_values.iter_mut().enumerate() {
        *output = aspis_core::field::M31::from_le_bytes(
            public_input[index * 4..index * 4 + 4].try_into().unwrap(),
        )
        .ok_or(ProgramError::InvalidInstructionData)?;
    }
    Ok(aspis_statement::SpendPublic {
        anchor: public_values[0..8].try_into().unwrap(),
        nullifier: public_values[8..16].try_into().unwrap(),
        output_commitment: public_values[16..24].try_into().unwrap(),
        asset_id: public_values[24],
        fee: u32::from_le_bytes(public_input[100..104].try_into().unwrap()),
    })
}

fn trace_atomic_spend_acceptance_phase(event: aspis_statement::state_only_spend::SpendTraceEvent) {
    use aspis_statement::state_only_spend::SpendTraceEvent;
    match event {
        SpendTraceEvent::Parsed => msg!("aspis-cu:atomic59_parsed"),
        SpendTraceEvent::Transcript => msg!("aspis-cu:atomic59_transcript"),
        SpendTraceEvent::Terminal => msg!("aspis-cu:atomic59_terminal"),
        SpendTraceEvent::Relation => msg!("aspis-cu:atomic59_relation"),
        SpendTraceEvent::Openings => msg!("aspis-cu:atomic59_openings"),
        SpendTraceEvent::Layer0Queries => msg!("aspis-cu:atomic59_layer0_queries"),
        SpendTraceEvent::LaterQueries => msg!("aspis-cu:atomic59_later_queries"),
        SpendTraceEvent::Complete => msg!("aspis-cu:atomic59_core_complete"),
    }
    sol_log_compute_units();
}

#[inline(never)]
fn verify_atomic_spend_proof_bytes_v3(
    proof: &[u8],
    statement: &aspis_statement::AtomicPaymentStatementV3,
    trace: Option<aspis_statement::state_only_spend::SpendTrace>,
) -> ProgramResult {
    #[cfg(feature = "spend-dynamic-rate512")]
    aspis_statement::state_only_spend::verify_atomic_state_only_spend_v3_with_inverse(
        proof,
        statement,
        sbf_hashv,
        trace,
        m31_inverse_cluster_portable,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    #[cfg(not(feature = "spend-dynamic-rate512"))]
    aspis_statement::state_only_spend::verify_atomic_state_only_spend_v3(
        proof, statement, sbf_hashv, trace,
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(())
}

/// Wire tag 59: read-only production verification of the uploaded proof
/// against the wire-supplied public statement.
#[inline(never)]
pub(crate) fn verify_uploaded_atomic_spend_acceptance_v3(
    proof_account: &AccountInfo,
    pool: [u8; 32],
    sequence: u64,
    public_input: &[u8; 104],
    output_anchor: [u8; 32],
) -> ProgramResult {
    msg!("aspis-cu:atomic59_instruction_start");
    sol_log_compute_units();
    let public = decode_spend_public(public_input)?;
    let output_anchor = aspis_statement::decode_digest_canonical(&output_anchor)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let statement = aspis_statement::AtomicPaymentStatementV3 {
        pool,
        sequence,
        spend: public,
        output_anchor,
    };
    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    msg!("aspis-cu:atomic59_proof_loaded");
    sol_log_compute_units();
    verify_atomic_spend_proof_bytes_v3(
        &data[proof_start..proof_end],
        &statement,
        Some(trace_atomic_spend_acceptance_phase),
    )?;
    msg!("aspis-cu:atomic59_done");
    sol_log_compute_units();
    Ok(())
}

/// Wire tags 60/65: production verification inside the atomic
/// state-transition wrapper.
#[inline(never)]
pub(crate) fn verify_uploaded_atomic_spend_production_statement_v3(
    proof_account: &AccountInfo,
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> ProgramResult {
    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    verify_atomic_spend_proof_bytes_v3(&data[proof_start..proof_end], statement, None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id;
    use crate::lifecycle::{AUTHORITY_OFFSET, PROOF_ACCOUNT_HEADER_LEN, PROOF_ACCOUNT_MAGIC};
    use crate::test_support::make_account;
    use solana_program::pubkey::Pubkey;

    #[test]
    fn production_spend_read_and_mutation_paths_require_finalized_proofs() {
        let program_id = id();
        let proof_key = Pubkey::new_unique();
        let authority_key = Pubkey::new_unique();
        let mut proof_lamports = 0;
        let mut proof_data = [0u8; PROOF_ACCOUNT_HEADER_LEN + 1];
        proof_data[0..4].copy_from_slice(&PROOF_ACCOUNT_MAGIC);
        proof_data[4..8].copy_from_slice(&1u32.to_le_bytes());
        proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].copy_from_slice(authority_key.as_ref());

        let public_input = [0u8; 104];
        let statement = aspis_statement::AtomicPaymentStatementV3 {
            pool: [0u8; 32],
            sequence: 0,
            spend: aspis_statement::SpendPublic {
                anchor: [aspis_core::field::M31::ZERO; 8],
                nullifier: [aspis_core::field::M31::ZERO; 8],
                output_commitment: [aspis_core::field::M31::ZERO; 8],
                asset_id: aspis_core::field::M31::ZERO,
                fee: 0,
            },
            output_anchor: [aspis_core::field::M31::ZERO; 8],
        };

        for finalized in [false, true] {
            if finalized {
                proof_data[AUTHORITY_OFFSET..AUTHORITY_OFFSET + 32].fill(0);
            }
            let expected = if finalized {
                Err(ProgramError::InvalidInstructionData)
            } else {
                Err(ProgramError::InvalidAccountData)
            };
            {
                let proof = make_account(
                    &proof_key,
                    &program_id,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                );
                assert_eq!(
                    verify_uploaded_atomic_spend_acceptance_v3(
                        &proof,
                        [0u8; 32],
                        0,
                        &public_input,
                        [0u8; 32],
                    ),
                    expected
                );
            }
            {
                let proof = make_account(
                    &proof_key,
                    &program_id,
                    &mut proof_lamports,
                    &mut proof_data,
                    false,
                    false,
                );
                assert_eq!(
                    verify_uploaded_atomic_spend_production_statement_v3(&proof, &statement),
                    expected
                );
            }
        }
    }
}
