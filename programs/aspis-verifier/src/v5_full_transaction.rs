//! Isolated local-validator transaction wrapper for the provisional v5 Spend.
//!
//! This deliberately reuses the production atomic state-transition machinery
//! while keeping the provisional proof verifier behind the `v5-cu-probe`
//! feature.  The proof account is retained and read-only, matching production
//! tag 60.  Nothing in this module is reachable from the frozen production
//! dispatcher.

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::atomic_payment::{self, AtomicPaymentPublicInputs};

/// Local-validator-only discriminator for an end-to-end provisional v5 Spend.
pub const V5_FULL_CU_TRANSACTION_TAG: u8 = 67;

const PUBLIC_WIRE_BYTES: usize = 4 * 32 + 2 * 4 + 32;
pub const V5_FULL_CU_TRANSACTION_WIRE_BYTES: usize = 1 + PUBLIC_WIRE_BYTES;

fn take<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<N>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(*head)
}

/// Decode exactly the production atomic public-input tuple from tag 67.
pub fn parse_v5_full_cu_public_inputs(
    instruction_data: &[u8],
) -> Result<AtomicPaymentPublicInputs, ProgramError> {
    let (&tag, mut wire) = instruction_data
        .split_first()
        .ok_or(ProgramError::InvalidInstructionData)?;
    if tag != V5_FULL_CU_TRANSACTION_TAG
        || instruction_data.len() != V5_FULL_CU_TRANSACTION_WIRE_BYTES
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let public = AtomicPaymentPublicInputs {
        current_anchor: take::<32>(&mut wire)?,
        nullifier: take::<32>(&mut wire)?,
        output_commitment: take::<32>(&mut wire)?,
        output_anchor: take::<32>(&mut wire)?,
        asset_id: u32::from_le_bytes(take::<4>(&mut wire)?),
        fee: u32::from_le_bytes(take::<4>(&mut wire)?),
        deployment_domain: take::<32>(&mut wire)?,
    };
    if !wire.is_empty() {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(public)
}

/// Run one real atomic state transition around a provisional v5 verifier.
///
/// The callback shape is intentionally identical to the production verifier
/// callback.  This lets the v5 verifier consume the statement constructed from
/// the live pool account instead of trusting a proof-carried duplicate.
pub fn process_v5_full_cu_transaction_with_verifier<'a, F>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'a>],
    instruction_data: &[u8],
    verify_complete_proof: F,
) -> ProgramResult
where
    F: FnOnce(
        &AccountInfo<'a>,
        &aspis_statement::AtomicPaymentStatementV4,
        &[u8; 32],
    ) -> ProgramResult,
{
    let public = parse_v5_full_cu_public_inputs(instruction_data)?;
    atomic_payment::verify_and_apply_atomic_payment_state(
        program_id,
        accounts,
        &public,
        verify_complete_proof,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn wire() -> Vec<u8> {
        let mut output = Vec::with_capacity(V5_FULL_CU_TRANSACTION_WIRE_BYTES);
        output.push(V5_FULL_CU_TRANSACTION_TAG);
        output.extend_from_slice(&[1u8; 32]);
        output.extend_from_slice(&[2u8; 32]);
        output.extend_from_slice(&[3u8; 32]);
        output.extend_from_slice(&[4u8; 32]);
        output.extend_from_slice(&17u32.to_le_bytes());
        output.extend_from_slice(&1u32.to_le_bytes());
        output.extend_from_slice(&[5u8; 32]);
        output
    }

    #[test]
    fn exact_wire_matches_the_atomic_transition_tuple() {
        let bytes = wire();
        let public = parse_v5_full_cu_public_inputs(&bytes).unwrap();
        assert_eq!(bytes.len(), 169);
        assert_eq!(public.current_anchor, [1u8; 32]);
        assert_eq!(public.nullifier, [2u8; 32]);
        assert_eq!(public.output_commitment, [3u8; 32]);
        assert_eq!(public.output_anchor, [4u8; 32]);
        assert_eq!(public.asset_id, 17);
        assert_eq!(public.fee, 1);
        assert_eq!(public.deployment_domain, [5u8; 32]);
    }

    #[test]
    fn wrong_tag_and_trailing_bytes_fail_before_account_access() {
        let mut bytes = wire();
        bytes[0] = 66;
        assert_eq!(
            parse_v5_full_cu_public_inputs(&bytes),
            Err(ProgramError::InvalidInstructionData)
        );
        bytes[0] = V5_FULL_CU_TRANSACTION_TAG;
        bytes.push(0);
        assert_eq!(
            process_v5_full_cu_transaction_with_verifier(
                &Pubkey::new_unique(),
                &[],
                &bytes,
                |_, _, _| Ok(())
            ),
            Err(ProgramError::InvalidInstructionData)
        );
    }

    #[test]
    fn isolated_probe_entrypoint_routes_tag67_into_the_atomic_wrapper() {
        assert_eq!(
            crate::v5_cu_probe::process_v5_cu_probe_instruction(
                &Pubkey::new_unique(),
                &[],
                &wire(),
            ),
            Err(ProgramError::NotEnoughAccountKeys)
        );
    }
}
