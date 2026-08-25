//! Production transaction wrapper for the V6 26+3 one-fold verifier.
//!
//! This module contains no diagnostic hash substitution and no acceptance
//! shortcut. Tag 72 checks all three work witnesses, exact terminal equality,
//! both authenticated binary openings, the one-fold query equalities, and the
//! complete relation tail before the shared atomic wrapper mutates any state.

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::atomic_payment::{self, AtomicPaymentPublicInputs};

pub const V6_PRODUCTION_TAG: u8 = 72;
const V6_ATOMIC_PUBLIC_WIRE_BYTES: usize = 4 * 32 + 2 * 4 + 32;
pub const V6_ATOMIC_WIRE_BYTES: usize = 1 + 2 + 2 + 1 + V6_ATOMIC_PUBLIC_WIRE_BYTES;

/// SHA-256("aspis:v6:onefold:26c1-3c2:b10:q16:frontier209:work34-31-34:release-v1").
///
/// This compiled value separates V6 proofs from probes and from every future
/// release even when the program id and public statement are otherwise equal.
pub const V6_RELEASE_BINDING: [u8; 32] = [
    0x36, 0xd1, 0xd6, 0xa7, 0x1b, 0x6a, 0x6e, 0x66, 0x99, 0x82, 0xca, 0x9e, 0xa6, 0x7b, 0xc1, 0x9f,
    0xd1, 0x33, 0x1a, 0x2c, 0x21, 0x2c, 0xa8, 0x03, 0xa1, 0xb6, 0xc5, 0xda, 0x17, 0x6e, 0x5e, 0x18,
];

fn take<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], ProgramError> {
    let (head, tail) = input
        .split_first_chunk::<N>()
        .ok_or(ProgramError::InvalidInstructionData)?;
    *input = tail;
    Ok(*head)
}

fn u16_le(input: &mut &[u8]) -> Result<u16, ProgramError> {
    Ok(u16::from_le_bytes(take::<2>(input)?))
}

fn u32_le(input: &mut &[u8]) -> Result<u32, ProgramError> {
    Ok(u32::from_le_bytes(take::<4>(input)?))
}

/// Parse and execute the exact production V6 atomic wire.
pub fn process_v6_atomic_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() != V6_ATOMIC_WIRE_BYTES
        || instruction_data.first().copied() != Some(V6_PRODUCTION_TAG)
    {
        return Err(ProgramError::InvalidInstructionData);
    }

    let mut input = &instruction_data[1..];
    let c1_frontier_nodes = usize::from(u16_le(&mut input)?);
    let c2_frontier_nodes = usize::from(u16_le(&mut input)?);
    let selector = take::<1>(&mut input)?[0];
    let public = AtomicPaymentPublicInputs {
        current_anchor: take(&mut input)?,
        nullifier: take(&mut input)?,
        output_commitment: take(&mut input)?,
        output_anchor: take(&mut input)?,
        asset_id: u32_le(&mut input)?,
        fee: u32_le(&mut input)?,
        deployment_domain: take(&mut input)?,
    };
    if !input.is_empty() {
        return Err(ProgramError::InvalidInstructionData);
    }

    atomic_payment::verify_and_apply_atomic_payment_state(
        program_id,
        accounts,
        &public,
        |proof_account, statement, statement_digest| {
            let account_data = proof_account.try_borrow_data()?;
            if !crate::lifecycle::proof_account_finalized(&account_data) {
                return Err(ProgramError::InvalidAccountData);
            }
            let (proof_start, proof_end) = crate::lifecycle::uploaded_proof_bounds(&account_data)?;
            let proof = &account_data[proof_start..proof_end];
            crate::v6_verifier::verify_v6_read_only_with_statement_digest(
                crate::verify::sbf_hashv,
                proof,
                c1_frontier_nodes,
                c2_frontier_nodes,
                selector,
                program_id,
                V6_RELEASE_BINDING,
                proof_account.key,
                statement,
                *statement_digest,
                true,
            )
            .map_err(|_| ProgramError::InvalidAccountData)?;
            Ok(())
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn release_binding_matches_documented_preimage() {
        assert_eq!(
            solana_program::hash::hash(
                b"aspis:v6:onefold:26c1-3c2:b10:q16:frontier209:work34-31-34:release-v1"
            )
            .to_bytes(),
            V6_RELEASE_BINDING
        );
    }

    #[test]
    fn production_wire_is_exact_and_rejects_trailing_bytes() {
        let wire = vec![0u8; V6_ATOMIC_WIRE_BYTES];
        assert_eq!(
            process_v6_atomic_instruction(&crate::id(), &[], &wire),
            Err(ProgramError::InvalidInstructionData)
        );

        let mut exact = wire;
        exact[0] = V6_PRODUCTION_TAG;
        assert_eq!(
            process_v6_atomic_instruction(&crate::id(), &[], &exact),
            Err(ProgramError::NotEnoughAccountKeys)
        );
        exact.push(0);
        assert_eq!(
            process_v6_atomic_instruction(&crate::id(), &[], &exact),
            Err(ProgramError::InvalidInstructionData)
        );
    }
}
