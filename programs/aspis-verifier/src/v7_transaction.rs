//! Production transaction wrapper for the compact V7 one-fold verifier.
//!
//! Tag 73 checks all three work witnesses, exact terminal equality, both
//! authenticated 208-bit binary opening, every
//! one-fold query equality, and the complete relation tail before the shared
//! atomic wrapper mutates state.

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::atomic_payment::{self, AtomicPaymentPublicInputs};

pub const V7_PRODUCTION_TAG: u8 = 73;
const V7_ATOMIC_PUBLIC_WIRE_BYTES: usize = 4 * 32 + 2 * 4 + 32;
pub const V7_ATOMIC_WIRE_BYTES: usize = 1 + 2 + V7_ATOMIC_PUBLIC_WIRE_BYTES;

/// SHA-256("aspis:v7:onefold:26c1-3c2:b10:q16:digest208:frontier203:first64:full-c2:work35-31-34:release-v1").
///
/// This compiled value separates compact V7 proofs from probes and from V6,
/// even when the program id and public statement are otherwise equal.
pub const V7_RELEASE_BINDING: [u8; 32] = [
    0x7a, 0xc8, 0xfe, 0x92, 0xc3, 0xf4, 0x91, 0x99, 0x72, 0xd6, 0x5d, 0x0b, 0x59, 0xa7, 0x89, 0x8e,
    0xd1, 0x00, 0x5c, 0xb4, 0x01, 0x6f, 0xdb, 0x1f, 0x3d, 0xaf, 0xf0, 0xae, 0xbb, 0x49, 0xa0, 0xf9,
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

/// Parse and execute the exact production V7 atomic wire.
pub fn process_v7_atomic_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() != V7_ATOMIC_WIRE_BYTES
        || instruction_data.first().copied() != Some(V7_PRODUCTION_TAG)
    {
        return Err(ProgramError::InvalidInstructionData);
    }

    let mut input = &instruction_data[1..];
    let frontier_nodes = usize::from(u16_le(&mut input)?);
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
            crate::v7_verifier::verify_v7_read_only_with_statement_digest(
                crate::verify::sbf_hashv,
                proof,
                frontier_nodes,
                program_id,
                V7_RELEASE_BINDING,
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
                b"aspis:v7:onefold:26c1-3c2:b10:q16:digest208:frontier203:first64:full-c2:work35-31-34:release-v1"
            )
            .to_bytes(),
            V7_RELEASE_BINDING
        );
    }

    #[test]
    fn production_wire_is_exact_and_rejects_trailing_bytes() {
        let wire = vec![0u8; V7_ATOMIC_WIRE_BYTES];
        assert_eq!(
            process_v7_atomic_instruction(&crate::id(), &[], &wire),
            Err(ProgramError::InvalidInstructionData)
        );

        let mut exact = wire;
        exact[0] = V7_PRODUCTION_TAG;
        assert_eq!(
            process_v7_atomic_instruction(&crate::id(), &[], &exact),
            Err(ProgramError::NotEnoughAccountKeys)
        );
        exact.push(0);
        assert_eq!(
            process_v7_atomic_instruction(&crate::id(), &[], &exact),
            Err(ProgramError::InvalidInstructionData)
        );
    }
}
