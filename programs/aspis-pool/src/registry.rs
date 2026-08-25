//! Read-only verifier-registry authentication for Pool V1.
//!
//! This module authorizes only an exact verifier/profile/release selection.
//! It does not invoke a verifier, accept a proof, reserve a nullifier, append a
//! note, or expose an instruction. Future spend code must bind the same fields
//! into the proof statement and authenticate verifier success before it may
//! call the crate-private state transition kernel.

use aspis_statement::pool_v1::{
    decode_verifier_registry_entry_v1, decode_verifier_registry_v1, validate_verifier_policy_v1,
    VerifierEntryStatusV1, VerifierPolicyV1, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
    POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::error::PoolV1ProgramError;

pub const POOL_V1_VERIFIER_REGISTRY_SEED: &[u8] = b"aspis-verifier-registry-v1";
pub const POOL_V1_VERIFIER_ENTRY_SEED: &[u8] = b"aspis-verifier-entry-v1";

pub fn pool_v1_verifier_registry_address(registry_program: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VERIFIER_REGISTRY_SEED, pool.as_ref()],
        registry_program,
    )
}

pub fn pool_v1_verifier_entry_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
    profile_binding: &[u8; 32],
    release_binding: &[u8; 32],
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_VERIFIER_ENTRY_SEED,
            pool.as_ref(),
            profile_binding,
            release_binding,
        ],
        registry_program,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct VerifierSelectionV1 {
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub statement_version: u8,
}

/// Evidence returned only after the Pool policy, canonical registry and exact
/// active entry all agree at `current_slot`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AuthenticatedVerifierSelectionV1 {
    policy: VerifierPolicyV1,
    pool: [u8; 32],
    verifier_program: [u8; 32],
    profile_binding: [u8; 32],
    release_binding: [u8; 32],
    statement_version: u8,
    registry_generation: u64,
    /// Exact slot at which the registry/entry pair was authenticated.  Hot
    /// settlement paths must require this to equal their settlement slot so a
    /// capability obtained before a pause or retirement cannot be replayed.
    authenticated_at_slot: u64,
}

impl AuthenticatedVerifierSelectionV1 {
    pub(crate) fn matches_policy(self, policy: &VerifierPolicyV1) -> bool {
        self.policy == *policy
    }

    pub(crate) fn matches(
        self,
        pool: [u8; 32],
        verifier_program: [u8; 32],
        profile_binding: [u8; 32],
        release_binding: [u8; 32],
        statement_version: u8,
    ) -> bool {
        self.pool == pool
            && self.verifier_program == verifier_program
            && self.profile_binding == profile_binding
            && self.release_binding == release_binding
            && self.statement_version == statement_version
    }

    pub(crate) fn registry_generation(self) -> u64 {
        self.registry_generation
    }

    pub(crate) fn authenticated_at_slot(self) -> u64 {
        self.authenticated_at_slot
    }
}

fn require_readonly_registry_account(
    account: &AccountInfo,
    registry_program: &Pubkey,
    invalid: PoolV1ProgramError,
) -> Result<(), ProgramError> {
    if account.owner != registry_program
        || account.executable
        || account.is_writable
        || account.is_signer
    {
        return Err(invalid.into());
    }
    Ok(())
}

/// Authenticate exactly `[registry, entry]` without mutating either account.
///
/// This is deliberately an internal precondition checker, not verifier
/// dispatch. The caller must additionally prove that the accepted proof
/// statement binds the returned Pool and verifier selection, then authenticate
/// the exact verifier result before any Pool write.
pub(crate) fn authenticate_verifier_selection_v1(
    pool: &Pubkey,
    policy: &VerifierPolicyV1,
    accounts: &[AccountInfo],
    selection: VerifierSelectionV1,
    current_slot: u64,
) -> Result<AuthenticatedVerifierSelectionV1, ProgramError> {
    let [registry_account, entry_account] = accounts else {
        return Err(if accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    validate_verifier_policy_v1(policy).map_err(|_| PoolV1ProgramError::InvalidVerifierRegistry)?;
    let registry_program = Pubkey::new_from_array(policy.registry_program);

    require_readonly_registry_account(
        registry_account,
        &registry_program,
        PoolV1ProgramError::InvalidVerifierRegistry,
    )?;
    if registry_account.key != &pool_v1_verifier_registry_address(&registry_program, pool).0 {
        return Err(PoolV1ProgramError::InvalidVerifierRegistryAddress.into());
    }
    let registry = {
        let data = registry_account.try_borrow_data()?;
        decode_verifier_registry_v1(&data)
            .map_err(|_| PoolV1ProgramError::InvalidVerifierRegistry)?
    };
    let policy_requires_immutable =
        policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY != 0;
    if registry.pool != pool.to_bytes()
        || registry.authority != policy.registry_authority
        || registry.policy_binding != policy.policy_binding
        || registry.is_immutable() != policy_requires_immutable
    {
        return Err(PoolV1ProgramError::InvalidVerifierRegistry.into());
    }
    if registry.is_paused() {
        return Err(PoolV1ProgramError::VerifierRegistryPaused.into());
    }

    require_readonly_registry_account(
        entry_account,
        &registry_program,
        PoolV1ProgramError::InvalidVerifierEntry,
    )?;
    let expected_entry = pool_v1_verifier_entry_address(
        &registry_program,
        pool,
        &selection.profile_binding,
        &selection.release_binding,
    )
    .0;
    if entry_account.key != &expected_entry {
        return Err(PoolV1ProgramError::InvalidVerifierEntryAddress.into());
    }
    let entry = {
        let data = entry_account.try_borrow_data()?;
        decode_verifier_registry_entry_v1(&data)
            .map_err(|_| PoolV1ProgramError::InvalidVerifierEntry)?
    };
    if entry.pool != pool.to_bytes()
        || entry.policy_binding != policy.policy_binding
        || entry.verifier_program != selection.verifier_program
        || entry.profile_binding != selection.profile_binding
        || entry.release_binding != selection.release_binding
        || entry.statement_version != selection.statement_version
    {
        return Err(PoolV1ProgramError::VerifierSelectionMismatch.into());
    }
    if entry.status != VerifierEntryStatusV1::Active {
        return Err(PoolV1ProgramError::VerifierEntryInactive.into());
    }
    if current_slot < entry.activation_slot {
        return Err(PoolV1ProgramError::VerifierEntryNotActiveYet.into());
    }
    if entry.retirement_slot != POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
        && current_slot >= entry.retirement_slot
    {
        return Err(PoolV1ProgramError::VerifierEntryRetired.into());
    }

    Ok(AuthenticatedVerifierSelectionV1 {
        policy: *policy,
        pool: entry.pool,
        verifier_program: entry.verifier_program,
        profile_binding: entry.profile_binding,
        release_binding: entry.release_binding,
        statement_version: entry.statement_version,
        registry_generation: registry.generation,
        authenticated_at_slot: current_slot,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::pool_v1::{
        encode_verifier_registry_entry_v1, encode_verifier_registry_v1, VerifierRegistryEntryV1,
        VerifierRegistryV1, POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE, POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED,
    };
    use solana_program::clock::Epoch;

    fn policy(registry_program: Pubkey) -> VerifierPolicyV1 {
        VerifierPolicyV1 {
            flags: 0,
            registry_program: registry_program.to_bytes(),
            registry_authority: [7u8; 32],
            policy_binding: [8u8; 32],
        }
    }

    fn selection() -> VerifierSelectionV1 {
        VerifierSelectionV1 {
            verifier_program: [9u8; 32],
            profile_binding: [10u8; 32],
            release_binding: [11u8; 32],
            statement_version: 1,
        }
    }

    fn registry(pool: Pubkey, flags: u8) -> VerifierRegistryV1 {
        VerifierRegistryV1 {
            flags,
            pool: pool.to_bytes(),
            authority: [7u8; 32],
            policy_binding: [8u8; 32],
            generation: 3,
            minimum_activation_delay_slots: 32,
        }
    }

    fn entry(pool: Pubkey) -> VerifierRegistryEntryV1 {
        let selection = selection();
        VerifierRegistryEntryV1 {
            status: VerifierEntryStatusV1::Active,
            statement_version: selection.statement_version,
            pool: pool.to_bytes(),
            verifier_program: selection.verifier_program,
            profile_binding: selection.profile_binding,
            release_binding: selection.release_binding,
            activation_slot: 100,
            retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
            policy_binding: [8u8; 32],
        }
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            false,
            false,
            lamports,
            data,
            owner,
            false,
            Epoch::default(),
        )
    }

    #[test]
    fn canonical_active_entry_authorizes_exact_selection_without_writes() {
        let registry_program = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let policy = policy(registry_program);
        let selection = selection();
        let registry_key = pool_v1_verifier_registry_address(&registry_program, &pool).0;
        let entry_key = pool_v1_verifier_entry_address(
            &registry_program,
            &pool,
            &selection.profile_binding,
            &selection.release_binding,
        )
        .0;
        let mut registry_data = encode_verifier_registry_v1(&registry(pool, 0)).unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&entry(pool)).unwrap();
        let registry_before = registry_data;
        let entry_before = entry_data;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let registry_account = account(
            &registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
        );
        let entry_account = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
        );

        let authenticated = authenticate_verifier_selection_v1(
            &pool,
            &policy,
            &[registry_account, entry_account],
            selection,
            100,
        )
        .unwrap();
        assert!(authenticated.matches(
            pool.to_bytes(),
            selection.verifier_program,
            selection.profile_binding,
            selection.release_binding,
            selection.statement_version,
        ));
        assert_eq!(authenticated.registry_generation(), 3);
        assert_eq!(authenticated.authenticated_at_slot(), 100);
        assert_eq!(registry_data, registry_before);
        assert_eq!(entry_data, entry_before);
    }

    #[test]
    fn wrong_entry_pda_and_mismatched_selection_fail_closed() {
        let registry_program = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let policy = policy(registry_program);
        let selection = selection();
        let registry_key = pool_v1_verifier_registry_address(&registry_program, &pool).0;
        let wrong_entry_key = Pubkey::new_unique();
        let mut registry_data = encode_verifier_registry_v1(&registry(pool, 0)).unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&entry(pool)).unwrap();
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let registry_account = account(
            &registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
        );
        let entry_account = account(
            &wrong_entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
        );
        assert_eq!(
            authenticate_verifier_selection_v1(
                &pool,
                &policy,
                &[registry_account, entry_account],
                selection,
                100,
            ),
            Err(PoolV1ProgramError::InvalidVerifierEntryAddress.into())
        );

        let entry_key = pool_v1_verifier_entry_address(
            &registry_program,
            &pool,
            &selection.profile_binding,
            &selection.release_binding,
        )
        .0;
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let registry_account = account(
            &registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
        );
        let entry_account = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
        );
        assert_eq!(
            authenticate_verifier_selection_v1(
                &pool,
                &policy,
                &[registry_account, entry_account],
                VerifierSelectionV1 {
                    verifier_program: [12u8; 32],
                    ..selection
                },
                100,
            ),
            Err(PoolV1ProgramError::VerifierSelectionMismatch.into())
        );
    }

    #[test]
    fn wrong_registry_pda_or_owner_is_rejected_before_entry_acceptance() {
        let registry_program = Pubkey::new_unique();
        let wrong_owner = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let policy = policy(registry_program);
        let selection = selection();
        let registry_key = pool_v1_verifier_registry_address(&registry_program, &pool).0;
        let wrong_registry_key = Pubkey::new_unique();
        let entry_key = pool_v1_verifier_entry_address(
            &registry_program,
            &pool,
            &selection.profile_binding,
            &selection.release_binding,
        )
        .0;
        let mut registry_data = encode_verifier_registry_v1(&registry(pool, 0)).unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&entry(pool)).unwrap();

        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let registry_account = account(
            &wrong_registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
        );
        let entry_account = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
        );
        assert_eq!(
            authenticate_verifier_selection_v1(
                &pool,
                &policy,
                &[registry_account, entry_account],
                selection,
                100,
            ),
            Err(PoolV1ProgramError::InvalidVerifierRegistryAddress.into())
        );

        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let registry_account = account(
            &registry_key,
            &wrong_owner,
            &mut registry_lamports,
            &mut registry_data,
        );
        let entry_account = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
        );
        assert_eq!(
            authenticate_verifier_selection_v1(
                &pool,
                &policy,
                &[registry_account, entry_account],
                selection,
                100,
            ),
            Err(PoolV1ProgramError::InvalidVerifierRegistry.into())
        );
    }

    #[test]
    fn paused_preactivation_and_retired_entries_are_rejected() {
        let registry_program = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let policy = policy(registry_program);
        let selection = selection();
        let registry_key = pool_v1_verifier_registry_address(&registry_program, &pool).0;
        let entry_key = pool_v1_verifier_entry_address(
            &registry_program,
            &pool,
            &selection.profile_binding,
            &selection.release_binding,
        )
        .0;

        let run = |registry_value: VerifierRegistryV1,
                   entry_value: VerifierRegistryEntryV1,
                   slot: u64| {
            let mut registry_data = encode_verifier_registry_v1(&registry_value).unwrap();
            let mut entry_data = encode_verifier_registry_entry_v1(&entry_value).unwrap();
            let mut registry_lamports = 1;
            let mut entry_lamports = 1;
            let registry_account = account(
                &registry_key,
                &registry_program,
                &mut registry_lamports,
                &mut registry_data,
            );
            let entry_account = account(
                &entry_key,
                &registry_program,
                &mut entry_lamports,
                &mut entry_data,
            );
            authenticate_verifier_selection_v1(
                &pool,
                &policy,
                &[registry_account, entry_account],
                selection,
                slot,
            )
        };

        assert_eq!(
            run(
                registry(pool, POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED),
                entry(pool),
                100,
            ),
            Err(PoolV1ProgramError::VerifierRegistryPaused.into())
        );
        assert_eq!(
            run(registry(pool, 0), entry(pool), 99),
            Err(PoolV1ProgramError::VerifierEntryNotActiveYet.into())
        );
        assert_eq!(
            run(
                registry(pool, 0),
                VerifierRegistryEntryV1 {
                    retirement_slot: 120,
                    ..entry(pool)
                },
                120,
            ),
            Err(PoolV1ProgramError::VerifierEntryRetired.into())
        );
    }

    #[test]
    fn immutable_policy_accepts_matching_zero_authority_registry() {
        let registry_program = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let policy = VerifierPolicyV1 {
            flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
            registry_program: registry_program.to_bytes(),
            registry_authority: [0u8; 32],
            policy_binding: [8u8; 32],
        };
        let selection = selection();
        let registry_key = pool_v1_verifier_registry_address(&registry_program, &pool).0;
        let entry_key = pool_v1_verifier_entry_address(
            &registry_program,
            &pool,
            &selection.profile_binding,
            &selection.release_binding,
        )
        .0;
        let immutable_registry = VerifierRegistryV1 {
            flags: POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
            authority: [0u8; 32],
            ..registry(pool, 0)
        };
        let mut registry_data = encode_verifier_registry_v1(&immutable_registry).unwrap();
        let mut entry_data = encode_verifier_registry_entry_v1(&entry(pool)).unwrap();
        let mut registry_lamports = 1;
        let mut entry_lamports = 1;
        let registry_account = account(
            &registry_key,
            &registry_program,
            &mut registry_lamports,
            &mut registry_data,
        );
        let entry_account = account(
            &entry_key,
            &registry_program,
            &mut entry_lamports,
            &mut entry_data,
        );
        assert!(authenticate_verifier_selection_v1(
            &pool,
            &policy,
            &[registry_account, entry_account],
            selection,
            100,
        )
        .is_ok());
    }
}
