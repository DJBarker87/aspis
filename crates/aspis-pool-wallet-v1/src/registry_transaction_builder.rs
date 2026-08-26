//! Exact unsigned governance instructions for the Pool V1 verifier registry.
//!
//! All registry/entry PDAs, fixed-width mutation bytes, account ordering and
//! privilege bits are derived here.  This module has no signer, multisig, RPC,
//! simulation or submission capability.

use std::collections::BTreeSet;

use aspis_registry::{
    encode_initialize_registry_v1, encode_schedule_profile_v1, encode_simple_mutation_v1,
    pool_v1_verifier_entry_address, pool_v1_verifier_registry_address, RegistryMutationOpcodeV1,
};
use aspis_statement::pool_v1::{
    POOL_V1_HISTORICAL_ANCHOR_VERSION, V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
    V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
};
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
};
use solana_sdk_ids::system_program;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegistryTransactionBuilderErrorV1 {
    UnpinnedProgramId,
    ZeroAccount,
    ZeroBinding,
    ZeroActivationDelay,
    InvalidStatementVersion,
    InvalidActivationSlot,
    AccountAlias,
    SameRelease,
    IncompatibleProfile,
    InvalidMutation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryGovernanceRouteV1 {
    /// Exact stored registry authority, normally a threshold-multisig PDA.
    pub authority: Pubkey,
    /// Separate System-owned hot payer used only for fresh PDA rent.
    pub payer: Pubkey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryEntryKeyV1 {
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
}

impl RegistryEntryKeyV1 {
    pub const fn native_tag73_v1() -> Self {
        Self {
            profile_binding: V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
            release_binding: V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
        }
    }
}

fn require_nonzero_distinct(
    program_id: Pubkey,
    accounts: &[Pubkey],
) -> Result<(), RegistryTransactionBuilderErrorV1> {
    if program_id == Pubkey::default() || program_id == system_program::id() {
        return Err(RegistryTransactionBuilderErrorV1::UnpinnedProgramId);
    }
    if accounts.iter().any(|key| *key == Pubkey::default()) {
        return Err(RegistryTransactionBuilderErrorV1::ZeroAccount);
    }
    if accounts
        .iter()
        .any(|key| *key == program_id || *key == system_program::id())
    {
        return Err(RegistryTransactionBuilderErrorV1::AccountAlias);
    }
    let mut unique = BTreeSet::new();
    if !accounts.iter().all(|key| unique.insert(key.to_bytes())) {
        return Err(RegistryTransactionBuilderErrorV1::AccountAlias);
    }
    Ok(())
}

fn require_entry_key(key: RegistryEntryKeyV1) -> Result<(), RegistryTransactionBuilderErrorV1> {
    if key.profile_binding == [0u8; 32] || key.release_binding == [0u8; 32] {
        Err(RegistryTransactionBuilderErrorV1::ZeroBinding)
    } else {
        Ok(())
    }
}

/// Initialize the canonical registry PDA for one Pool and policy manifest.
pub fn build_initialize_registry_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    policy_binding: [u8; 32],
    minimum_activation_delay_slots: u64,
    route: RegistryGovernanceRouteV1,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    let registry = pool_v1_verifier_registry_address(&registry_program, &pool).0;
    require_nonzero_distinct(
        registry_program,
        &[registry, pool, route.authority, route.payer],
    )?;
    if policy_binding == [0u8; 32] {
        return Err(RegistryTransactionBuilderErrorV1::ZeroBinding);
    }
    if minimum_activation_delay_slots == 0 {
        return Err(RegistryTransactionBuilderErrorV1::ZeroActivationDelay);
    }
    Ok(Instruction {
        program_id: registry_program,
        accounts: vec![
            AccountMeta::new(registry, false),
            AccountMeta::new_readonly(route.authority, true),
            AccountMeta::new(route.payer, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: encode_initialize_registry_v1(
            pool.to_bytes(),
            policy_binding,
            minimum_activation_delay_slots,
        )
        .to_vec(),
    })
}

/// Schedule one exact profile/release entry at a caller-selected activation
/// slot.  The program independently enforces the stored minimum delay.
#[allow(clippy::too_many_arguments)]
pub fn build_schedule_registry_profile_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    verifier_program: Pubkey,
    entry_key: RegistryEntryKeyV1,
    statement_version: u8,
    activation_slot: u64,
    route: RegistryGovernanceRouteV1,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    require_entry_key(entry_key)?;
    if statement_version == 0 {
        return Err(RegistryTransactionBuilderErrorV1::InvalidStatementVersion);
    }
    if activation_slot == 0 {
        return Err(RegistryTransactionBuilderErrorV1::InvalidActivationSlot);
    }
    let registry = pool_v1_verifier_registry_address(&registry_program, &pool).0;
    let entry = pool_v1_verifier_entry_address(
        &registry_program,
        &pool,
        &entry_key.profile_binding,
        &entry_key.release_binding,
    )
    .0;
    require_nonzero_distinct(
        registry_program,
        &[
            pool,
            verifier_program,
            registry,
            entry,
            route.authority,
            route.payer,
        ],
    )?;
    Ok(Instruction {
        program_id: registry_program,
        accounts: vec![
            AccountMeta::new(registry, false),
            AccountMeta::new(entry, false),
            AccountMeta::new_readonly(route.authority, true),
            AccountMeta::new(route.payer, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: encode_schedule_profile_v1(
            expected_generation,
            verifier_program.to_bytes(),
            entry_key.profile_binding,
            entry_key.release_binding,
            statement_version,
            activation_slot,
        )
        .to_vec(),
    })
}

/// Schedule the one frozen native Pool V1 Tag-73 payment profile without
/// allowing callers to substitute its profile, release or statement version.
pub fn build_schedule_native_tag73_profile_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    verifier_program: Pubkey,
    activation_slot: u64,
    route: RegistryGovernanceRouteV1,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    build_schedule_registry_profile_instruction_v1(
        registry_program,
        pool,
        expected_generation,
        verifier_program,
        RegistryEntryKeyV1::native_tag73_v1(),
        POOL_V1_HISTORICAL_ANCHOR_VERSION,
        activation_slot,
        route,
    )
}

fn build_simple_registry_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    authority: Pubkey,
    opcode: RegistryMutationOpcodeV1,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    let registry = pool_v1_verifier_registry_address(&registry_program, &pool).0;
    require_nonzero_distinct(registry_program, &[pool, registry, authority])?;
    let data = encode_simple_mutation_v1(opcode, expected_generation)
        .map_err(|_| RegistryTransactionBuilderErrorV1::InvalidMutation)?;
    Ok(Instruction {
        program_id: registry_program,
        accounts: vec![
            AccountMeta::new(registry, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: data.to_vec(),
    })
}

pub fn build_pause_registry_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    authority: Pubkey,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    build_simple_registry_instruction_v1(
        registry_program,
        pool,
        expected_generation,
        authority,
        RegistryMutationOpcodeV1::Pause,
    )
}

pub fn build_unpause_registry_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    authority: Pubkey,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    build_simple_registry_instruction_v1(
        registry_program,
        pool,
        expected_generation,
        authority,
        RegistryMutationOpcodeV1::Unpause,
    )
}

pub fn build_freeze_registry_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    authority: Pubkey,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    build_simple_registry_instruction_v1(
        registry_program,
        pool,
        expected_generation,
        authority,
        RegistryMutationOpcodeV1::Freeze,
    )
}

/// Activate one scheduled entry after its on-chain activation slot.
pub fn build_activate_registry_entry_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    entry_key: RegistryEntryKeyV1,
    authority: Pubkey,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    require_entry_key(entry_key)?;
    let registry = pool_v1_verifier_registry_address(&registry_program, &pool).0;
    let entry = pool_v1_verifier_entry_address(
        &registry_program,
        &pool,
        &entry_key.profile_binding,
        &entry_key.release_binding,
    )
    .0;
    require_nonzero_distinct(registry_program, &[pool, registry, entry, authority])?;
    let data = encode_simple_mutation_v1(RegistryMutationOpcodeV1::Activate, expected_generation)
        .map_err(|_| RegistryTransactionBuilderErrorV1::InvalidMutation)?;
    Ok(Instruction {
        program_id: registry_program,
        accounts: vec![
            AccountMeta::new(registry, false),
            AccountMeta::new(entry, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: data.to_vec(),
    })
}

/// Retire one active release only in favor of a distinct entry.  The program
/// authenticates same-profile compatibility and replacement activity.
pub fn build_retire_registry_entry_instruction_v1(
    registry_program: Pubkey,
    pool: Pubkey,
    expected_generation: u64,
    retiring: RegistryEntryKeyV1,
    replacement: RegistryEntryKeyV1,
    authority: Pubkey,
) -> Result<Instruction, RegistryTransactionBuilderErrorV1> {
    require_entry_key(retiring)?;
    require_entry_key(replacement)?;
    if retiring.release_binding == replacement.release_binding {
        return Err(RegistryTransactionBuilderErrorV1::SameRelease);
    }
    if retiring.profile_binding != replacement.profile_binding {
        return Err(RegistryTransactionBuilderErrorV1::IncompatibleProfile);
    }
    let registry = pool_v1_verifier_registry_address(&registry_program, &pool).0;
    let retiring_entry = pool_v1_verifier_entry_address(
        &registry_program,
        &pool,
        &retiring.profile_binding,
        &retiring.release_binding,
    )
    .0;
    let replacement_entry = pool_v1_verifier_entry_address(
        &registry_program,
        &pool,
        &replacement.profile_binding,
        &replacement.release_binding,
    )
    .0;
    require_nonzero_distinct(
        registry_program,
        &[pool, registry, retiring_entry, replacement_entry, authority],
    )?;
    let data = encode_simple_mutation_v1(RegistryMutationOpcodeV1::Retire, expected_generation)
        .map_err(|_| RegistryTransactionBuilderErrorV1::InvalidMutation)?;
    Ok(Instruction {
        program_id: registry_program,
        accounts: vec![
            AccountMeta::new(registry, false),
            AccountMeta::new(retiring_entry, false),
            AccountMeta::new_readonly(replacement_entry, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: data.to_vec(),
    })
}

#[cfg(test)]
mod tests {
    use aspis_registry::{decode_registry_instruction_v1, RegistryInstructionV1};

    use super::*;

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn route() -> RegistryGovernanceRouteV1 {
        RegistryGovernanceRouteV1 {
            authority: key(3),
            payer: key(4),
        }
    }

    #[test]
    fn native_registry_lifecycle_builders_freeze_exact_wires_pdas_and_privileges() {
        let registry_program = key(1);
        let pool = key(2);
        let verifier_program = key(5);
        let registry = pool_v1_verifier_registry_address(&registry_program, &pool).0;
        let native = RegistryEntryKeyV1::native_tag73_v1();
        let entry = pool_v1_verifier_entry_address(
            &registry_program,
            &pool,
            &native.profile_binding,
            &native.release_binding,
        )
        .0;

        let initialize = build_initialize_registry_instruction_v1(
            registry_program,
            pool,
            [9u8; 32],
            64,
            route(),
        )
        .unwrap();
        assert_eq!(
            decode_registry_instruction_v1(&initialize.data).unwrap(),
            RegistryInstructionV1::Initialize {
                pool: pool.to_bytes(),
                policy_binding: [9u8; 32],
                minimum_activation_delay_slots: 64,
            }
        );
        assert_eq!(initialize.accounts[0], AccountMeta::new(registry, false));
        assert_eq!(
            initialize.accounts[1],
            AccountMeta::new_readonly(route().authority, true)
        );
        assert_eq!(
            initialize.accounts[2],
            AccountMeta::new(route().payer, true)
        );

        let schedule = build_schedule_native_tag73_profile_instruction_v1(
            registry_program,
            pool,
            0,
            verifier_program,
            1_000,
            route(),
        )
        .unwrap();
        assert_eq!(
            decode_registry_instruction_v1(&schedule.data).unwrap(),
            RegistryInstructionV1::ScheduleProfile {
                expected_generation: 0,
                verifier_program: verifier_program.to_bytes(),
                profile_binding: V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
                release_binding: V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
                statement_version: POOL_V1_HISTORICAL_ANCHOR_VERSION,
                activation_slot: 1_000,
            }
        );
        assert_eq!(schedule.accounts[0], AccountMeta::new(registry, false));
        assert_eq!(schedule.accounts[1], AccountMeta::new(entry, false));

        let activate = build_activate_registry_entry_instruction_v1(
            registry_program,
            pool,
            1,
            native,
            route().authority,
        )
        .unwrap();
        assert_eq!(activate.accounts[1], AccountMeta::new(entry, false));
        assert_eq!(
            decode_registry_instruction_v1(&activate.data).unwrap(),
            RegistryInstructionV1::Activate {
                expected_generation: 1
            }
        );
        for (instruction, expected) in [
            (
                build_pause_registry_instruction_v1(registry_program, pool, 2, route().authority)
                    .unwrap(),
                RegistryInstructionV1::Pause {
                    expected_generation: 2,
                },
            ),
            (
                build_unpause_registry_instruction_v1(registry_program, pool, 3, route().authority)
                    .unwrap(),
                RegistryInstructionV1::Unpause {
                    expected_generation: 3,
                },
            ),
            (
                build_freeze_registry_instruction_v1(registry_program, pool, 4, route().authority)
                    .unwrap(),
                RegistryInstructionV1::Freeze {
                    expected_generation: 4,
                },
            ),
        ] {
            assert_eq!(
                decode_registry_instruction_v1(&instruction.data).unwrap(),
                expected
            );
            assert_eq!(instruction.accounts.len(), 2);
        }
    }

    #[test]
    fn release_rotation_and_invalid_governance_shapes_fail_closed() {
        let registry_program = key(1);
        let pool = key(2);
        let native = RegistryEntryKeyV1::native_tag73_v1();
        let replacement = RegistryEntryKeyV1 {
            profile_binding: native.profile_binding,
            release_binding: [0xaa; 32],
        };
        let retire = build_retire_registry_entry_instruction_v1(
            registry_program,
            pool,
            9,
            native,
            replacement,
            route().authority,
        )
        .unwrap();
        assert_eq!(
            decode_registry_instruction_v1(&retire.data).unwrap(),
            RegistryInstructionV1::Retire {
                expected_generation: 9
            }
        );
        assert!(retire.accounts[1].is_writable);
        assert!(!retire.accounts[2].is_writable);
        assert_eq!(
            build_retire_registry_entry_instruction_v1(
                registry_program,
                pool,
                9,
                native,
                native,
                route().authority,
            )
            .unwrap_err(),
            RegistryTransactionBuilderErrorV1::SameRelease
        );
        assert_eq!(
            build_initialize_registry_instruction_v1(
                registry_program,
                pool,
                [0u8; 32],
                64,
                route(),
            )
            .unwrap_err(),
            RegistryTransactionBuilderErrorV1::ZeroBinding
        );
        assert_eq!(
            build_initialize_registry_instruction_v1(
                registry_program,
                pool,
                [9u8; 32],
                0,
                route(),
            )
            .unwrap_err(),
            RegistryTransactionBuilderErrorV1::ZeroActivationDelay
        );
        let mut system_authority = route();
        system_authority.authority = system_program::id();
        assert_eq!(
            build_initialize_registry_instruction_v1(
                registry_program,
                pool,
                [9u8; 32],
                64,
                system_authority,
            )
            .unwrap_err(),
            RegistryTransactionBuilderErrorV1::ZeroAccount
        );
        assert_eq!(
            build_schedule_registry_profile_instruction_v1(
                registry_program,
                pool,
                0,
                key(5),
                native,
                0,
                1_000,
                route(),
            )
            .unwrap_err(),
            RegistryTransactionBuilderErrorV1::InvalidStatementVersion
        );
        assert_eq!(
            build_retire_registry_entry_instruction_v1(
                registry_program,
                pool,
                9,
                native,
                RegistryEntryKeyV1 {
                    profile_binding: [0xbb; 32],
                    release_binding: [0xaa; 32],
                },
                route().authority,
            )
            .unwrap_err(),
            RegistryTransactionBuilderErrorV1::IncompatibleProfile
        );
    }
}
