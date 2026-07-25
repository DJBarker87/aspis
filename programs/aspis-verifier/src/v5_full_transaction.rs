//! Tag-67 transaction wrapper for the v5 Spend.
//!
//! Both the production dispatcher and the isolated local-validator probe use
//! this wrapper. It parses the fixed public wire and then enters the shared
//! atomic state transition. The production dispatcher supplies the v5
//! verifier; the probe supplies the same verifier through its diagnostic
//! entrypoint.

use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::atomic_payment::{self, AtomicPaymentPublicInputs};

/// Discriminator for an end-to-end v5 Spend.
pub const V5_FULL_CU_TRANSACTION_TAG: u8 = 67;

/// Tag 67 accepts only a nullifier whose canonical PDA is found on Solana's
/// first address attempt.
pub const V5_NULLIFIER_PDA_BUMP: u8 = u8::MAX;

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

/// Run one real atomic state transition around the supplied v5 verifier.
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
    atomic_payment::verify_and_apply_atomic_payment_state_with_required_nullifier_bump(
        program_id,
        accounts,
        &public,
        V5_NULLIFIER_PDA_BUMP,
        verify_complete_proof,
    )
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;

    use aspis_core::field::M31;
    use solana_program::{account_info::AccountInfo, clock::Epoch, system_program};

    use super::*;

    fn nullifier_with_bump(program_id: &Pubkey, required_bump: u8) -> [u8; 32] {
        for seed in 0..10_000u32 {
            let digest = core::array::from_fn(|index| M31(seed + index as u32 * 17));
            let nullifier = aspis_statement::encode_digest_canonical(&digest);
            let (_, bump) = atomic_payment::atomic_nullifier_address(program_id, &nullifier);
            if bump == required_bump {
                return nullifier;
            }
        }
        panic!("no test nullifier found for bump {required_bump}");
    }

    fn wire(nullifier: [u8; 32]) -> Vec<u8> {
        let mut output = Vec::with_capacity(V5_FULL_CU_TRANSACTION_WIRE_BYTES);
        output.push(V5_FULL_CU_TRANSACTION_TAG);
        output.extend_from_slice(&[1u8; 32]);
        output.extend_from_slice(&nullifier);
        output.extend_from_slice(&[3u8; 32]);
        output.extend_from_slice(&[4u8; 32]);
        output.extend_from_slice(&17u32.to_le_bytes());
        output.extend_from_slice(&1u32.to_le_bytes());
        output.extend_from_slice(&[5u8; 32]);
        output
    }

    struct TransitionResult {
        result: ProgramResult,
        verifier_called: bool,
        pool_before: [u8; atomic_payment::ATOMIC_POOL_STATE_LEN],
        pool_after: [u8; atomic_payment::ATOMIC_POOL_STATE_LEN],
        marker_before: [u8; atomic_payment::ATOMIC_NULLIFIER_MARKER_LEN],
        marker_after: [u8; atomic_payment::ATOMIC_NULLIFIER_MARKER_LEN],
        lamports_before: [u64; 5],
        lamports_after: [u64; 5],
    }

    fn run_transition(required_bump: u8) -> TransitionResult {
        let program_id = crate::id();
        let nullifier = nullifier_with_bump(&program_id, required_bump);
        let bytes = wire(nullifier);
        let public = parse_v5_full_cu_public_inputs(&bytes).unwrap();
        let proof_key = Pubkey::new_unique();
        let pool_key = Pubkey::new_unique();
        let (nullifier_key, actual_bump) =
            atomic_payment::atomic_nullifier_address(&program_id, &public.nullifier);
        assert_eq!(actual_bump, required_bump);
        let payer_key = Pubkey::new_unique();
        let system_key = system_program::id();
        let system_owner = Pubkey::new_unique();

        let mut proof_lamports = 11;
        let mut pool_lamports = 12;
        let mut nullifier_lamports = 13;
        let mut payer_lamports = 14;
        let mut system_lamports = 15;
        let lamports_before = [
            proof_lamports,
            pool_lamports,
            nullifier_lamports,
            payer_lamports,
            system_lamports,
        ];
        let mut proof_data = [0x55; 8];
        let mut pool_data = [0u8; atomic_payment::ATOMIC_POOL_STATE_LEN];
        atomic_payment::AtomicPoolStateV2 {
            sequence: 0,
            anchor: public.current_anchor,
            deployment_domain: public.deployment_domain,
        }
        .encode(&mut pool_data)
        .unwrap();
        let pool_before = pool_data;
        let mut nullifier_data = [0u8; atomic_payment::ATOMIC_NULLIFIER_MARKER_LEN];
        let marker_before = nullifier_data;
        let mut payer_data = [];
        let mut system_data = [];
        let verifier_called = Cell::new(false);

        let accounts = vec![
            AccountInfo::new(
                &proof_key,
                false,
                false,
                &mut proof_lamports,
                &mut proof_data,
                &program_id,
                false,
                Epoch::default(),
            ),
            AccountInfo::new(
                &pool_key,
                false,
                true,
                &mut pool_lamports,
                &mut pool_data,
                &program_id,
                false,
                Epoch::default(),
            ),
            AccountInfo::new(
                &nullifier_key,
                false,
                true,
                &mut nullifier_lamports,
                &mut nullifier_data,
                &program_id,
                false,
                Epoch::default(),
            ),
            AccountInfo::new(
                &payer_key,
                true,
                true,
                &mut payer_lamports,
                &mut payer_data,
                &system_key,
                false,
                Epoch::default(),
            ),
            AccountInfo::new(
                &system_key,
                false,
                false,
                &mut system_lamports,
                &mut system_data,
                &system_owner,
                true,
                Epoch::default(),
            ),
        ];
        let result = process_v5_full_cu_transaction_with_verifier(
            &program_id,
            &accounts,
            &bytes,
            |_, _, _| {
                verifier_called.set(true);
                Ok(())
            },
        );
        drop(accounts);

        TransitionResult {
            result,
            verifier_called: verifier_called.get(),
            pool_before,
            pool_after: pool_data,
            marker_before,
            marker_after: nullifier_data,
            lamports_before,
            lamports_after: [
                proof_lamports,
                pool_lamports,
                nullifier_lamports,
                payer_lamports,
                system_lamports,
            ],
        }
    }

    #[test]
    fn exact_wire_matches_the_atomic_transition_tuple() {
        let bytes = wire([2u8; 32]);
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
        let mut bytes = wire([2u8; 32]);
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
    fn tag67_rejects_bump_below_255_without_verification_or_state_change() {
        let transition = run_transition(V5_NULLIFIER_PDA_BUMP - 1);
        assert_eq!(transition.result, Err(ProgramError::InvalidSeeds));
        assert!(!transition.verifier_called);
        assert_eq!(transition.pool_after, transition.pool_before);
        assert_eq!(transition.marker_after, transition.marker_before);
        assert_eq!(transition.lamports_after, transition.lamports_before);
    }

    #[test]
    fn tag67_accepts_bump_255_and_applies_the_state_change() {
        let transition = run_transition(V5_NULLIFIER_PDA_BUMP);
        assert_eq!(transition.result, Ok(()));
        assert!(transition.verifier_called);
        assert_ne!(transition.pool_after, transition.pool_before);
        assert_ne!(transition.marker_after, transition.marker_before);
        assert_eq!(transition.lamports_after, transition.lamports_before);
        assert_eq!(
            atomic_payment::AtomicPoolStateV2::decode(&transition.pool_after)
                .unwrap()
                .sequence,
            1
        );
    }

    #[test]
    fn isolated_probe_entrypoint_routes_tag67_into_the_atomic_wrapper() {
        let program_id = Pubkey::new_unique();
        let nullifier = nullifier_with_bump(&program_id, V5_NULLIFIER_PDA_BUMP);
        assert_eq!(
            crate::v5_cu_probe::process_v5_cu_probe_instruction(&program_id, &[], &wire(nullifier),),
            Err(ProgramError::NotEnoughAccountKeys)
        );
    }
}
