//! Canonical Pool V1 nullifier-marker planning.
//!
//! This module validates the exact writable marker PDA and distinguishes the
//! two admissible fresh account forms from an occupied marker. It performs no
//! System CPI or account write. The entrypoint's atomic spend composition
//! rechecks the plan after proof verification, creates/allocates if required,
//! acquires every Pool/history mutable borrow, and only then copies the
//! prevalidated fixed marker image.

use aspis_statement::{
    decode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, encode_pool_v1_nullifier_marker, PoolV1NullifierMarkerV1,
        POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES, POOL_V1_NULLIFIER_MARKER_SEED,
    },
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};
use solana_sdk_ids::system_program;

use crate::error::PoolV1ProgramError;

/// Exact third seed validation is part of this address API: arbitrary 32 bytes
/// that do not decode as eight canonical M31 limbs are rejected before PDA
/// derivation.
pub fn pool_v1_nullifier_marker_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    canonical_nullifier_encoding: &[u8; 32],
) -> Result<(Pubkey, u8), ProgramError> {
    decode_digest_canonical(canonical_nullifier_encoding)
        .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAccount)?;
    Ok(Pubkey::find_program_address(
        &[
            POOL_V1_NULLIFIER_MARKER_SEED,
            pool.as_ref(),
            canonical_nullifier_encoding,
        ],
        program_id,
    ))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NullifierMarkerPreparationV1 {
    /// A data-empty System-owned PDA. Future composition must perform the
    /// reviewed create/allocate/assign sequence with `invoke_signed`.
    CreateOrAllocateSystemOwned,
    /// An exact-size, program-owned, all-zero account ready for the final copy.
    PopulateProgramOwnedZeroed,
}

/// Fully validated but unapplied marker plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlannedNullifierMarkerV1 {
    preparation: NullifierMarkerPreparationV1,
    address_bump: u8,
    marker: PoolV1NullifierMarkerV1,
    encoded_marker: [u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
}

impl PlannedNullifierMarkerV1 {
    pub(crate) fn preparation(self) -> NullifierMarkerPreparationV1 {
        self.preparation
    }

    pub(crate) fn address_bump(self) -> u8 {
        self.address_bump
    }

    pub(crate) fn marker(self) -> PoolV1NullifierMarkerV1 {
        self.marker
    }

    pub(crate) fn encoded_marker(self) -> [u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES] {
        self.encoded_marker
    }
}

/// Plan consumption of one exact canonical nullifier marker without writing.
///
/// A valid occupied marker always returns `NullifierAlreadyConsumed`, even if
/// its recorded context differs. This prevents a hypothetical PDA collision
/// or pre-existing valid marker from being overwritten. Nonzero bytes that do
/// not decode as the exact Pool V1 marker format are malformed and fail
/// separately.
pub fn plan_nullifier_marker_consumption_v1(
    program_id: &Pubkey,
    marker_account: &AccountInfo,
    marker: PoolV1NullifierMarkerV1,
) -> Result<PlannedNullifierMarkerV1, ProgramError> {
    let encoded_marker = encode_pool_v1_nullifier_marker(&marker)
        .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAccount)?;
    let pool = Pubkey::new_from_array(marker.pool);
    let canonical_nullifier = marker.canonical_nullifier_encoding();
    let (expected_address, address_bump) =
        pool_v1_nullifier_marker_address(program_id, &pool, &canonical_nullifier)?;
    if marker_account.key != &expected_address || marker_account.key == &pool {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into());
    }
    if marker_account.executable || marker_account.is_signer || !marker_account.is_writable {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }

    let preparation = if marker_account.owner == program_id {
        let data = marker_account.try_borrow_data()?;
        if data.len() != POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES {
            return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
        }
        if data.iter().all(|byte| *byte == 0) {
            NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed
        } else if decode_pool_v1_nullifier_marker(&data).is_ok() {
            return Err(PoolV1ProgramError::NullifierAlreadyConsumed.into());
        } else {
            return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
        }
    } else if marker_account.owner == &system_program::id() && marker_account.data_is_empty() {
        NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned
    } else {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    };

    Ok(PlannedNullifierMarkerV1 {
        preparation,
        address_bump,
        marker,
        encoded_marker,
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::{M31, P};
    use aspis_statement::{
        pool_v1::{PoolV1TransitionKind, POOL_V1_NULLIFIER_MARKER_MAGIC},
        poseidon2::Digest,
    };
    use solana_program::clock::Epoch;

    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 19 * index as u32))
    }

    fn marker(pool: Pubkey) -> PoolV1NullifierMarkerV1 {
        PoolV1NullifierMarkerV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: pool.to_bytes(),
            deployment_domain: [2u8; 32],
            nullifier: digest(10),
            retained_anchor_sequence: 44,
            retained_anchor_root: digest(100),
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        }
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    #[test]
    fn exact_seed_schedule_uses_pool_and_canonical_nullifier_bytes() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let nullifier = marker.canonical_nullifier_encoding();
        let derived = pool_v1_nullifier_marker_address(&program_id, &pool, &nullifier).unwrap();
        assert_eq!(
            derived,
            Pubkey::find_program_address(
                &[POOL_V1_NULLIFIER_MARKER_SEED, pool.as_ref(), &nullifier],
                &program_id
            )
        );

        let mut noncanonical = nullifier;
        noncanonical[..4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            pool_v1_nullifier_marker_address(&program_id, &pool, &noncanonical),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );
    }

    #[test]
    fn system_empty_and_program_zeroed_accounts_produce_distinct_unapplied_plans() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &marker.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;

        let mut system_lamports = 7;
        let mut empty_data = [];
        let system_owner = system_program::id();
        let system_account = account(
            &marker_key,
            &system_owner,
            &mut system_lamports,
            &mut empty_data,
            false,
            true,
            false,
        );
        let system_plan =
            plan_nullifier_marker_consumption_v1(&program_id, &system_account, marker).unwrap();
        assert_eq!(
            system_plan.preparation,
            NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned
        );
        assert_eq!(
            &system_plan.encoded_marker[..4],
            &POOL_V1_NULLIFIER_MARKER_MAGIC
        );

        let mut program_lamports = 1;
        let mut zeroed = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let program_account = account(
            &marker_key,
            &program_id,
            &mut program_lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        let program_plan =
            plan_nullifier_marker_consumption_v1(&program_id, &program_account, marker).unwrap();
        assert_eq!(
            program_plan.preparation,
            NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed
        );
        assert_eq!(system_plan.encoded_marker, program_plan.encoded_marker);
        assert!(zeroed.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn fresh_program_marker_can_be_consumed_once_and_second_plan_rejects() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &marker.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let mut lamports = 1;
        let mut data = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let plan = {
            let account = account(
                &marker_key,
                &program_id,
                &mut lamports,
                &mut data,
                false,
                true,
                false,
            );
            plan_nullifier_marker_consumption_v1(&program_id, &account, marker).unwrap()
        };
        // This direct copy models only the later infallible persistence step;
        // no public writer is exposed by the production module.
        data.copy_from_slice(&plan.encoded_marker);
        let account = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut data,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &account, marker),
            Err(PoolV1ProgramError::NullifierAlreadyConsumed.into())
        );
    }

    #[test]
    fn occupied_valid_marker_for_other_context_is_never_overwritten() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let requested = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &requested.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let occupied = PoolV1NullifierMarkerV1 {
            deployment_domain: [99u8; 32],
            ..requested
        };
        let mut data = encode_pool_v1_nullifier_marker(&occupied).unwrap();
        let before = data;
        let mut lamports = 1;
        let account = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut data,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &account, requested),
            Err(PoolV1ProgramError::NullifierAlreadyConsumed.into())
        );
        assert_eq!(data, before);
    }

    #[test]
    fn wrong_address_owner_privileges_length_or_malformed_image_fail_closed() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &marker.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;

        let wrong_key = Pubkey::new_unique();
        let mut lamports = 1;
        let mut zeroed = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let wrong_address = account(
            &wrong_key,
            &program_id,
            &mut lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &wrong_address, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into())
        );

        let foreign_owner = Pubkey::new_unique();
        let foreign = account(
            &marker_key,
            &foreign_owner,
            &mut lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &foreign, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );

        let readonly = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut zeroed,
            false,
            false,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &readonly, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );

        let mut wrong_length = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES - 1];
        let wrong_length_account = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut wrong_length,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &wrong_length_account, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );

        zeroed[0] = 0xff;
        let before = zeroed;
        let malformed = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &malformed, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );
        assert_eq!(zeroed, before);
    }
}
