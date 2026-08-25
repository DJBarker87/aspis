use super::*;
use crate::instruction::{
    encode_initialize_registry_v1, encode_schedule_profile_v1, encode_simple_mutation_v1,
    RegistryMutationOpcodeV1,
};
use solana_program::clock::Epoch;
use std::{vec, vec::Vec};

const POLICY_BINDING: [u8; 32] = [8u8; 32];
const PROFILE_BINDING: [u8; 32] = [10u8; 32];
const RELEASE_A: [u8; 32] = [11u8; 32];
const RELEASE_B: [u8; 32] = [12u8; 32];
const VERIFIER_A: [u8; 32] = [13u8; 32];
const VERIFIER_B: [u8; 32] = [14u8; 32];

struct TestAccount {
    key: Pubkey,
    owner: Pubkey,
    lamports: u64,
    data: Vec<u8>,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
}

impl TestAccount {
    fn info(&mut self) -> AccountInfo<'_> {
        AccountInfo::new(
            &self.key,
            self.is_signer,
            self.is_writable,
            &mut self.lamports,
            self.data.as_mut_slice(),
            &self.owner,
            self.executable,
            Epoch::default(),
        )
    }

    fn snapshot(&self) -> (u64, Vec<u8>) {
        (self.lamports, self.data.clone())
    }

    fn assert_unchanged(&self, before: &(u64, Vec<u8>)) {
        assert_eq!((self.lamports, &self.data), (before.0, &before.1));
    }
}

struct NoCpi;

impl RegistryCpiRuntimeV1 for NoCpi {
    fn invoke<'info>(
        &mut self,
        _instruction: &Instruction,
        _account_infos: &[AccountInfo<'info>],
    ) -> ProgramResult {
        panic!("unexpected CPI in a program-owned preparation test")
    }

    fn invoke_signed<'info>(
        &mut self,
        _instruction: &Instruction,
        _account_infos: &[AccountInfo<'info>],
        _signer_seeds: &[&[&[u8]]],
    ) -> ProgramResult {
        panic!("unexpected CPI in a program-owned preparation test")
    }
}

fn custom(error: RegistryProgramErrorV1) -> ProgramError {
    error.into()
}

fn authority_account(key: Pubkey, signer: bool) -> TestAccount {
    TestAccount {
        key,
        owner: Pubkey::new_unique(),
        lamports: 1,
        data: Vec::new(),
        is_signer: signer,
        is_writable: false,
        executable: false,
    }
}

fn payer_account() -> TestAccount {
    TestAccount {
        key: Pubkey::new_unique(),
        owner: system_program::id(),
        lamports: 1_000_000,
        data: Vec::new(),
        is_signer: true,
        is_writable: true,
        executable: false,
    }
}

fn system_program_account() -> TestAccount {
    TestAccount {
        key: system_program::id(),
        owner: native_loader::id(),
        lamports: 1,
        data: Vec::new(),
        is_signer: false,
        is_writable: false,
        executable: true,
    }
}

fn zeroed_registry_account(program_id: Pubkey, pool: Pubkey) -> TestAccount {
    TestAccount {
        key: pool_v1_verifier_registry_address(&program_id, &pool).0,
        owner: program_id,
        lamports: 1,
        data: vec![0u8; POOL_V1_VERIFIER_REGISTRY_BYTES],
        is_signer: false,
        is_writable: true,
        executable: false,
    }
}

fn registry_state(
    pool: Pubkey,
    authority: Pubkey,
    generation: u64,
    flags: u8,
) -> VerifierRegistryV1 {
    VerifierRegistryV1 {
        flags,
        pool: pool.to_bytes(),
        authority: if flags & POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE != 0 {
            [0u8; 32]
        } else {
            authority.to_bytes()
        },
        policy_binding: POLICY_BINDING,
        generation,
        minimum_activation_delay_slots: 10,
    }
}

fn registry_account(
    program_id: Pubkey,
    pool: Pubkey,
    authority: Pubkey,
    generation: u64,
    flags: u8,
) -> TestAccount {
    TestAccount {
        key: pool_v1_verifier_registry_address(&program_id, &pool).0,
        owner: program_id,
        lamports: 1,
        data: encode_verifier_registry_v1(&registry_state(pool, authority, generation, flags))
            .unwrap()
            .to_vec(),
        is_signer: false,
        is_writable: true,
        executable: false,
    }
}

fn entry_state(
    pool: Pubkey,
    profile_binding: [u8; 32],
    release_binding: [u8; 32],
    verifier_program: [u8; 32],
    status: VerifierEntryStatusV1,
    activation_slot: u64,
) -> VerifierRegistryEntryV1 {
    VerifierRegistryEntryV1 {
        status,
        statement_version: 1,
        pool: pool.to_bytes(),
        verifier_program,
        profile_binding,
        release_binding,
        activation_slot,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: POLICY_BINDING,
    }
}

fn zeroed_entry_account(
    program_id: Pubkey,
    pool: Pubkey,
    profile_binding: [u8; 32],
    release_binding: [u8; 32],
) -> TestAccount {
    TestAccount {
        key: pool_v1_verifier_entry_address(&program_id, &pool, &profile_binding, &release_binding)
            .0,
        owner: program_id,
        lamports: 1,
        data: vec![0u8; POOL_V1_VERIFIER_ENTRY_BYTES],
        is_signer: false,
        is_writable: true,
        executable: false,
    }
}

fn entry_account(
    program_id: Pubkey,
    entry: VerifierRegistryEntryV1,
    writable: bool,
) -> TestAccount {
    let pool = Pubkey::new_from_array(entry.pool);
    TestAccount {
        key: pool_v1_verifier_entry_address(
            &program_id,
            &pool,
            &entry.profile_binding,
            &entry.release_binding,
        )
        .0,
        owner: program_id,
        lamports: 1,
        data: encode_verifier_registry_entry_v1(&entry).unwrap().to_vec(),
        is_signer: false,
        is_writable: writable,
        executable: false,
    }
}

fn invoke_initialize(
    program_id: &Pubkey,
    registry: &mut TestAccount,
    authority: &mut TestAccount,
    payer: &mut TestAccount,
    system: &mut TestAccount,
    instruction: &[u8],
) -> ProgramResult {
    let accounts = [
        registry.info(),
        authority.info(),
        payer.info(),
        system.info(),
    ];
    process_instruction_with_runtime(program_id, &accounts, instruction, 0, &mut NoCpi)
}

#[allow(clippy::too_many_arguments)]
fn invoke_schedule(
    program_id: &Pubkey,
    registry: &mut TestAccount,
    entry: &mut TestAccount,
    authority: &mut TestAccount,
    payer: &mut TestAccount,
    system: &mut TestAccount,
    instruction: &[u8],
    slot: u64,
) -> ProgramResult {
    let accounts = [
        registry.info(),
        entry.info(),
        authority.info(),
        payer.info(),
        system.info(),
    ];
    process_instruction_with_runtime(program_id, &accounts, instruction, slot, &mut NoCpi)
}

fn invoke_simple(
    program_id: &Pubkey,
    registry: &mut TestAccount,
    authority: &mut TestAccount,
    opcode: RegistryMutationOpcodeV1,
    expected_generation: u64,
) -> ProgramResult {
    let accounts = [registry.info(), authority.info()];
    process_instruction_with_runtime(
        program_id,
        &accounts,
        &encode_simple_mutation_v1(opcode, expected_generation).unwrap(),
        0,
        &mut NoCpi,
    )
}

fn invoke_activate(
    program_id: &Pubkey,
    registry: &mut TestAccount,
    entry: &mut TestAccount,
    authority: &mut TestAccount,
    expected_generation: u64,
    slot: u64,
) -> ProgramResult {
    let accounts = [registry.info(), entry.info(), authority.info()];
    process_instruction_with_runtime(
        program_id,
        &accounts,
        &encode_simple_mutation_v1(RegistryMutationOpcodeV1::Activate, expected_generation)
            .unwrap(),
        slot,
        &mut NoCpi,
    )
}

fn invoke_retire(
    program_id: &Pubkey,
    registry: &mut TestAccount,
    retiring: &mut TestAccount,
    replacement: &mut TestAccount,
    authority: &mut TestAccount,
    expected_generation: u64,
    slot: u64,
) -> ProgramResult {
    let accounts = [
        registry.info(),
        retiring.info(),
        replacement.info(),
        authority.info(),
    ];
    process_instruction_with_runtime(
        program_id,
        &accounts,
        &encode_simple_mutation_v1(RegistryMutationOpcodeV1::Retire, expected_generation).unwrap(),
        slot,
        &mut NoCpi,
    )
}

fn assert_all_unchanged(accounts: &[(&TestAccount, (u64, Vec<u8>))]) {
    for (account, snapshot) in accounts {
        account.assert_unchanged(snapshot);
    }
}

#[test]
fn initialize_requires_strict_authority_and_nonzero_delay_and_cannot_reinitialize() {
    let program_id = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    let authority_key = Pubkey::new_unique();
    let instruction = encode_initialize_registry_v1(pool.to_bytes(), POLICY_BINDING, 10);
    let mut registry = zeroed_registry_account(program_id, pool);
    let mut authority = authority_account(authority_key, true);
    let mut payer = payer_account();
    let mut system = system_program_account();

    assert_eq!(
        invoke_initialize(
            &program_id,
            &mut registry,
            &mut authority,
            &mut payer,
            &mut system,
            &instruction,
        ),
        Ok(())
    );
    let decoded = decode_verifier_registry_v1(&registry.data).unwrap();
    assert_eq!(decoded.pool, pool.to_bytes());
    assert_eq!(decoded.authority, authority_key.to_bytes());
    assert_eq!(decoded.generation, 0);
    assert_eq!(decoded.minimum_activation_delay_slots, 10);

    let before = registry.snapshot();
    assert_eq!(
        invoke_initialize(
            &program_id,
            &mut registry,
            &mut authority,
            &mut payer,
            &mut system,
            &instruction,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidFreshAccount))
    );
    registry.assert_unchanged(&before);

    let actual_unsigned_pool = Pubkey::new_unique();
    let mut unsigned_registry = zeroed_registry_account(program_id, actual_unsigned_pool);
    let unsigned_instruction =
        encode_initialize_registry_v1(actual_unsigned_pool.to_bytes(), POLICY_BINDING, 10);
    let mut unsigned = authority_account(authority_key, false);
    let before = unsigned_registry.snapshot();
    assert_eq!(
        invoke_initialize(
            &program_id,
            &mut unsigned_registry,
            &mut unsigned,
            &mut payer,
            &mut system,
            &unsigned_instruction,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidAuthority))
    );
    unsigned_registry.assert_unchanged(&before);
    let zero_delay_pool = Pubkey::new_unique();
    let mut zero_delay_registry = zeroed_registry_account(program_id, zero_delay_pool);
    let before = zero_delay_registry.snapshot();
    assert_eq!(
        invoke_initialize(
            &program_id,
            &mut zero_delay_registry,
            &mut authority,
            &mut payer,
            &mut system,
            &encode_initialize_registry_v1(zero_delay_pool.to_bytes(), POLICY_BINDING, 0),
        ),
        Err(custom(RegistryProgramErrorV1::InvalidInstruction))
    );
    zero_delay_registry.assert_unchanged(&before);
}

#[test]
fn schedule_enforces_authority_generation_and_full_nonzero_delay_before_any_write() {
    let program_id = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    let authority_key = Pubkey::new_unique();
    let mut registry = registry_account(program_id, pool, authority_key, 0, 0);
    let mut entry = zeroed_entry_account(program_id, pool, PROFILE_BINDING, RELEASE_A);
    let mut authority = authority_account(authority_key, true);
    let mut payer = payer_account();
    let mut system = system_program_account();

    let too_early = encode_schedule_profile_v1(0, VERIFIER_A, PROFILE_BINDING, RELEASE_A, 1, 109);
    let registry_before = registry.snapshot();
    let entry_before = entry.snapshot();
    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            &mut payer,
            &mut system,
            &too_early,
            100,
        ),
        Err(custom(RegistryProgramErrorV1::ActivationDelayNotElapsed))
    );
    assert_all_unchanged(&[
        (&registry, registry_before.clone()),
        (&entry, entry_before.clone()),
    ]);

    authority.is_signer = false;
    let scheduled = encode_schedule_profile_v1(0, VERIFIER_A, PROFILE_BINDING, RELEASE_A, 1, 110);
    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            &mut payer,
            &mut system,
            &scheduled,
            100,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidAuthority))
    );
    assert_all_unchanged(&[
        (&registry, registry_before.clone()),
        (&entry, entry_before.clone()),
    ]);

    authority.is_signer = true;
    let stale = encode_schedule_profile_v1(1, VERIFIER_A, PROFILE_BINDING, RELEASE_A, 1, 110);
    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            &mut payer,
            &mut system,
            &stale,
            100,
        ),
        Err(custom(RegistryProgramErrorV1::GenerationMismatch))
    );
    assert_all_unchanged(&[(&registry, registry_before), (&entry, entry_before)]);

    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            &mut payer,
            &mut system,
            &scheduled,
            100,
        ),
        Ok(())
    );
    assert_eq!(
        decode_verifier_registry_v1(&registry.data)
            .unwrap()
            .generation,
        1
    );
    let decoded_entry = decode_verifier_registry_entry_v1(&entry.data).unwrap();
    assert_eq!(decoded_entry.status, VerifierEntryStatusV1::Pending);
    assert_eq!(decoded_entry.activation_slot, 110);

    let registry_before = registry.snapshot();
    let entry_before = entry.snapshot();
    let replay = encode_schedule_profile_v1(1, VERIFIER_A, PROFILE_BINDING, RELEASE_A, 1, 120);
    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            &mut payer,
            &mut system,
            &replay,
            110,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidFreshAccount))
    );
    assert_all_unchanged(&[(&registry, registry_before), (&entry, entry_before)]);
}

#[test]
fn pause_and_unpause_increment_once_while_noops_stale_generation_and_overflow_roll_back() {
    let program_id = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    let authority_key = Pubkey::new_unique();
    let mut registry = registry_account(program_id, pool, authority_key, 3, 0);
    let mut authority = authority_account(authority_key, true);

    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut authority,
            RegistryMutationOpcodeV1::Pause,
            3,
        ),
        Ok(())
    );
    let paused = decode_verifier_registry_v1(&registry.data).unwrap();
    assert!(paused.is_paused());
    assert_eq!(paused.generation, 4);

    let before = registry.snapshot();
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut authority,
            RegistryMutationOpcodeV1::Pause,
            4,
        ),
        Err(custom(RegistryProgramErrorV1::RegistryAlreadyPaused))
    );
    registry.assert_unchanged(&before);
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut authority,
            RegistryMutationOpcodeV1::Unpause,
            3,
        ),
        Err(custom(RegistryProgramErrorV1::GenerationMismatch))
    );
    registry.assert_unchanged(&before);

    authority.is_signer = false;
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut authority,
            RegistryMutationOpcodeV1::Unpause,
            4,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidAuthority))
    );
    registry.assert_unchanged(&before);
    authority.is_signer = true;

    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut authority,
            RegistryMutationOpcodeV1::Unpause,
            4,
        ),
        Ok(())
    );
    let unpaused = decode_verifier_registry_v1(&registry.data).unwrap();
    assert!(!unpaused.is_paused());
    assert_eq!(unpaused.generation, 5);

    let mut overflow_registry = registry_account(program_id, pool, authority_key, u64::MAX, 0);
    let before = overflow_registry.snapshot();
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut overflow_registry,
            &mut authority,
            RegistryMutationOpcodeV1::Pause,
            u64::MAX,
        ),
        Err(custom(RegistryProgramErrorV1::GenerationOverflow))
    );
    overflow_registry.assert_unchanged(&before);
}

#[test]
fn activation_waits_for_the_scheduled_slot_and_is_status_only() {
    let program_id = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    let authority_key = Pubkey::new_unique();
    let mut registry = registry_account(program_id, pool, authority_key, 0, 0);
    let pending = entry_state(
        pool,
        PROFILE_BINDING,
        RELEASE_A,
        VERIFIER_A,
        VerifierEntryStatusV1::Pending,
        110,
    );
    let mut entry = entry_account(program_id, pending, true);
    let mut authority = authority_account(authority_key, true);
    let registry_before = registry.snapshot();
    let entry_before = entry.snapshot();

    assert_eq!(
        invoke_activate(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            0,
            109,
        ),
        Err(custom(RegistryProgramErrorV1::ActivationDelayNotElapsed))
    );
    assert_all_unchanged(&[
        (&registry, registry_before.clone()),
        (&entry, entry_before.clone()),
    ]);

    assert_eq!(
        invoke_activate(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            0,
            110,
        ),
        Ok(())
    );
    let active = decode_verifier_registry_entry_v1(&entry.data).unwrap();
    assert_eq!(active.status, VerifierEntryStatusV1::Active);
    assert_eq!(active.activation_slot, pending.activation_slot);
    assert_eq!(
        decode_verifier_registry_v1(&registry.data)
            .unwrap()
            .generation,
        1
    );

    let registry_before = registry.snapshot();
    let entry_before = entry.snapshot();
    assert_eq!(
        invoke_activate(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            1,
            111,
        ),
        Err(custom(RegistryProgramErrorV1::EntryNotPending))
    );
    assert_all_unchanged(&[(&registry, registry_before), (&entry, entry_before)]);
}

struct RetireFixture {
    program_id: Pubkey,
    registry: TestAccount,
    retiring: TestAccount,
    replacement: TestAccount,
    authority: TestAccount,
}

impl RetireFixture {
    fn new(retiring: VerifierRegistryEntryV1, replacement: VerifierRegistryEntryV1) -> Self {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_from_array(retiring.pool);
        let authority_key = Pubkey::new_unique();
        Self {
            program_id,
            registry: registry_account(program_id, pool, authority_key, 5, 0),
            retiring: entry_account(program_id, retiring, true),
            replacement: entry_account(program_id, replacement, false),
            authority: authority_account(authority_key, true),
        }
    }

    fn invoke(&mut self, slot: u64) -> ProgramResult {
        invoke_retire(
            &self.program_id,
            &mut self.registry,
            &mut self.retiring,
            &mut self.replacement,
            &mut self.authority,
            5,
            slot,
        )
    }

    fn snapshots(&self) -> [(u64, Vec<u8>); 3] {
        [
            self.registry.snapshot(),
            self.retiring.snapshot(),
            self.replacement.snapshot(),
        ]
    }

    fn assert_unchanged(&self, before: &[(u64, Vec<u8>); 3]) {
        self.registry.assert_unchanged(&before[0]);
        self.retiring.assert_unchanged(&before[1]);
        self.replacement.assert_unchanged(&before[2]);
    }
}

fn retirement_pair(pool: Pubkey) -> (VerifierRegistryEntryV1, VerifierRegistryEntryV1) {
    (
        entry_state(
            pool,
            PROFILE_BINDING,
            RELEASE_A,
            VERIFIER_A,
            VerifierEntryStatusV1::Active,
            100,
        ),
        entry_state(
            pool,
            PROFILE_BINDING,
            RELEASE_B,
            VERIFIER_B,
            VerifierEntryStatusV1::Active,
            90,
        ),
    )
}

#[test]
fn retirement_requires_distinct_active_exact_profile_continuity() {
    let pool = Pubkey::new_unique();
    let (retiring, replacement) = retirement_pair(pool);
    let replacement_before = encode_verifier_registry_entry_v1(&replacement).unwrap();
    let mut fixture = RetireFixture::new(retiring, replacement);

    assert_eq!(fixture.invoke(110), Ok(()));
    let registry = decode_verifier_registry_v1(&fixture.registry.data).unwrap();
    let retired = decode_verifier_registry_entry_v1(&fixture.retiring.data).unwrap();
    assert_eq!(registry.generation, 6);
    assert_eq!(retired.status, VerifierEntryStatusV1::Retired);
    assert_eq!(retired.retirement_slot, 110);
    assert_eq!(fixture.replacement.data, replacement_before);

    let (retiring, mut replacement) = retirement_pair(pool);
    replacement.status = VerifierEntryStatusV1::Pending;
    let mut fixture = RetireFixture::new(retiring, replacement);
    let before = fixture.snapshots();
    assert_eq!(
        fixture.invoke(110),
        Err(custom(RegistryProgramErrorV1::ReplacementNotActive))
    );
    fixture.assert_unchanged(&before);

    let (retiring, mut replacement) = retirement_pair(pool);
    replacement.profile_binding = [77u8; 32];
    let mut fixture = RetireFixture::new(retiring, replacement);
    let before = fixture.snapshots();
    assert_eq!(
        fixture.invoke(110),
        Err(custom(RegistryProgramErrorV1::IncompatibleReplacement))
    );
    fixture.assert_unchanged(&before);

    let (mut retiring, replacement) = retirement_pair(pool);
    retiring.status = VerifierEntryStatusV1::Pending;
    let mut fixture = RetireFixture::new(retiring, replacement);
    let before = fixture.snapshots();
    assert_eq!(
        fixture.invoke(110),
        Err(custom(RegistryProgramErrorV1::EntryNotActive))
    );
    fixture.assert_unchanged(&before);

    let (retiring, replacement) = retirement_pair(pool);
    let mut fixture = RetireFixture::new(retiring, replacement);
    let before = fixture.snapshots();
    assert_eq!(
        fixture.invoke(100),
        Err(custom(RegistryProgramErrorV1::InvalidRetirementSlot))
    );
    fixture.assert_unchanged(&before);
}

#[test]
fn freeze_is_irreversible_and_every_mutation_rejects_without_changes() {
    let program_id = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    let authority_key = Pubkey::new_unique();
    let mut registry = registry_account(
        program_id,
        pool,
        authority_key,
        8,
        POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED,
    );
    let mut authority = authority_account(authority_key, true);
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut authority,
            RegistryMutationOpcodeV1::Freeze,
            8,
        ),
        Ok(())
    );
    let frozen = decode_verifier_registry_v1(&registry.data).unwrap();
    assert!(frozen.is_immutable());
    assert!(frozen.is_paused());
    assert_eq!(frozen.authority, [0u8; 32]);
    assert_eq!(frozen.generation, 9);

    for opcode in [
        RegistryMutationOpcodeV1::Pause,
        RegistryMutationOpcodeV1::Unpause,
        RegistryMutationOpcodeV1::Freeze,
    ] {
        let before = registry.snapshot();
        assert_eq!(
            invoke_simple(&program_id, &mut registry, &mut authority, opcode, 9,),
            Err(custom(RegistryProgramErrorV1::RegistryFrozen))
        );
        registry.assert_unchanged(&before);
    }

    let (retiring, replacement) = retirement_pair(pool);
    let mut retiring = entry_account(program_id, retiring, true);
    let mut replacement = entry_account(program_id, replacement, false);
    let before = registry.snapshot();
    let retiring_before = retiring.snapshot();
    let replacement_before = replacement.snapshot();
    assert_eq!(
        invoke_retire(
            &program_id,
            &mut registry,
            &mut retiring,
            &mut replacement,
            &mut authority,
            9,
            110,
        ),
        Err(custom(RegistryProgramErrorV1::RegistryFrozen))
    );
    assert_all_unchanged(&[
        (&registry, before),
        (&retiring, retiring_before),
        (&replacement, replacement_before),
    ]);

    let pending = entry_state(
        pool,
        PROFILE_BINDING,
        [33u8; 32],
        VERIFIER_A,
        VerifierEntryStatusV1::Pending,
        120,
    );
    let mut pending = entry_account(program_id, pending, true);
    let registry_before = registry.snapshot();
    let entry_before = pending.snapshot();
    assert_eq!(
        invoke_activate(
            &program_id,
            &mut registry,
            &mut pending,
            &mut authority,
            9,
            120,
        ),
        Err(custom(RegistryProgramErrorV1::RegistryFrozen))
    );
    assert_all_unchanged(&[(&registry, registry_before), (&pending, entry_before)]);

    let mut fresh = zeroed_entry_account(program_id, pool, [44u8; 32], [45u8; 32]);
    let mut payer = payer_account();
    let mut system = system_program_account();
    let registry_before = registry.snapshot();
    let fresh_before = fresh.snapshot();
    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut registry,
            &mut fresh,
            &mut authority,
            &mut payer,
            &mut system,
            &encode_schedule_profile_v1(9, VERIFIER_A, [44u8; 32], [45u8; 32], 1, 130),
            120,
        ),
        Err(custom(RegistryProgramErrorV1::RegistryFrozen))
    );
    assert_all_unchanged(&[(&registry, registry_before), (&fresh, fresh_before)]);
}

#[test]
fn account_version_pda_privilege_and_instruction_validation_fail_closed() {
    let program_id = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    let authority_key = Pubkey::new_unique();
    let mut authority = authority_account(authority_key, true);

    let mut corrupt = registry_account(program_id, pool, authority_key, 0, 0);
    corrupt.data[4] = 2;
    let before = corrupt.snapshot();
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut corrupt,
            &mut authority,
            RegistryMutationOpcodeV1::Pause,
            0,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidRegistryAccount))
    );
    corrupt.assert_unchanged(&before);

    let mut wrong_pda = registry_account(program_id, pool, authority_key, 0, 0);
    wrong_pda.key = Pubkey::new_unique();
    let before = wrong_pda.snapshot();
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut wrong_pda,
            &mut authority,
            RegistryMutationOpcodeV1::Pause,
            0,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidRegistryAddress))
    );
    wrong_pda.assert_unchanged(&before);

    let mut wrong_owner = registry_account(program_id, pool, authority_key, 0, 0);
    wrong_owner.owner = Pubkey::new_unique();
    let before = wrong_owner.snapshot();
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut wrong_owner,
            &mut authority,
            RegistryMutationOpcodeV1::Pause,
            0,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidRegistryAccount))
    );
    wrong_owner.assert_unchanged(&before);

    let mut registry = registry_account(program_id, pool, authority_key, 0, 0);
    authority.is_writable = true;
    let before = registry.snapshot();
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut authority,
            RegistryMutationOpcodeV1::Pause,
            0,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidAuthority))
    );
    registry.assert_unchanged(&before);
    authority.is_writable = false;

    let pending = entry_state(
        pool,
        PROFILE_BINDING,
        RELEASE_A,
        VERIFIER_A,
        VerifierEntryStatusV1::Pending,
        10,
    );
    let mut entry = entry_account(program_id, pending, true);
    entry.key = Pubkey::new_unique();
    let registry_before = registry.snapshot();
    let entry_before = entry.snapshot();
    assert_eq!(
        invoke_activate(
            &program_id,
            &mut registry,
            &mut entry,
            &mut authority,
            0,
            10,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidEntryAddress))
    );
    assert_all_unchanged(&[(&registry, registry_before), (&entry, entry_before)]);

    let mut trailing = encode_simple_mutation_v1(RegistryMutationOpcodeV1::Pause, 0)
        .unwrap()
        .to_vec();
    trailing.push(0);
    let before = registry.snapshot();
    let accounts = [registry.info(), authority.info()];
    assert_eq!(
        process_instruction_with_runtime(&program_id, &accounts, &trailing, 0, &mut NoCpi),
        Err(custom(RegistryProgramErrorV1::InvalidInstruction))
    );
    drop(accounts);
    registry.assert_unchanged(&before);

    let before = registry.snapshot();
    let mut duplicate_authority = authority_account(registry.key, true);
    assert_eq!(
        invoke_simple(
            &program_id,
            &mut registry,
            &mut duplicate_authority,
            RegistryMutationOpcodeV1::Pause,
            0,
        ),
        Err(custom(RegistryProgramErrorV1::DuplicateAccount))
    );
    registry.assert_unchanged(&before);
}

#[test]
fn invalid_initialization_and_schedule_fields_or_pdas_never_mutate_accounts() {
    let program_id = Pubkey::new_unique();
    let authority_key = Pubkey::new_unique();
    let mut authority = authority_account(authority_key, true);
    let mut payer = payer_account();
    let mut system = system_program_account();

    let pool = Pubkey::new_unique();
    let mut wrong_registry = zeroed_registry_account(program_id, pool);
    wrong_registry.key = Pubkey::new_unique();
    let before = wrong_registry.snapshot();
    assert_eq!(
        invoke_initialize(
            &program_id,
            &mut wrong_registry,
            &mut authority,
            &mut payer,
            &mut system,
            &encode_initialize_registry_v1(pool.to_bytes(), POLICY_BINDING, 10),
        ),
        Err(custom(RegistryProgramErrorV1::InvalidFreshAccount))
    );
    wrong_registry.assert_unchanged(&before);

    let mut zero_policy_registry = zeroed_registry_account(program_id, pool);
    let before = zero_policy_registry.snapshot();
    assert_eq!(
        invoke_initialize(
            &program_id,
            &mut zero_policy_registry,
            &mut authority,
            &mut payer,
            &mut system,
            &encode_initialize_registry_v1(pool.to_bytes(), [0u8; 32], 10),
        ),
        Err(custom(RegistryProgramErrorV1::InvalidInstruction))
    );
    zero_policy_registry.assert_unchanged(&before);

    let mut registry = registry_account(program_id, pool, authority_key, 0, 0);
    let mut entry = zeroed_entry_account(program_id, pool, PROFILE_BINDING, RELEASE_A);
    for (verifier, profile, release, statement) in [
        ([0u8; 32], PROFILE_BINDING, RELEASE_A, 1),
        (VERIFIER_A, [0u8; 32], RELEASE_A, 1),
        (VERIFIER_A, PROFILE_BINDING, [0u8; 32], 1),
        (VERIFIER_A, PROFILE_BINDING, RELEASE_A, 0),
    ] {
        let registry_before = registry.snapshot();
        let entry_before = entry.snapshot();
        assert_eq!(
            invoke_schedule(
                &program_id,
                &mut registry,
                &mut entry,
                &mut authority,
                &mut payer,
                &mut system,
                &encode_schedule_profile_v1(0, verifier, profile, release, statement, 110),
                100,
            ),
            Err(custom(RegistryProgramErrorV1::InvalidInstruction))
        );
        assert_all_unchanged(&[(&registry, registry_before), (&entry, entry_before)]);
    }

    let mut overflow_registry = registry_account(program_id, pool, authority_key, 0, 0);
    let mut overflow_entry = zeroed_entry_account(program_id, pool, PROFILE_BINDING, RELEASE_A);
    let registry_before = overflow_registry.snapshot();
    let entry_before = overflow_entry.snapshot();
    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut overflow_registry,
            &mut overflow_entry,
            &mut authority,
            &mut payer,
            &mut system,
            &encode_schedule_profile_v1(0, VERIFIER_A, PROFILE_BINDING, RELEASE_A, 1, u64::MAX,),
            u64::MAX - 5,
        ),
        Err(custom(RegistryProgramErrorV1::ActivationDelayOverflow))
    );
    assert_all_unchanged(&[
        (&overflow_registry, registry_before),
        (&overflow_entry, entry_before),
    ]);

    let mut wrong_entry_pda = zeroed_entry_account(program_id, pool, PROFILE_BINDING, RELEASE_A);
    wrong_entry_pda.key = Pubkey::new_unique();
    let registry_before = registry.snapshot();
    let entry_before = wrong_entry_pda.snapshot();
    assert_eq!(
        invoke_schedule(
            &program_id,
            &mut registry,
            &mut wrong_entry_pda,
            &mut authority,
            &mut payer,
            &mut system,
            &encode_schedule_profile_v1(0, VERIFIER_A, PROFILE_BINDING, RELEASE_A, 1, 110,),
            100,
        ),
        Err(custom(RegistryProgramErrorV1::InvalidFreshAccount))
    );
    assert_all_unchanged(&[
        (&registry, registry_before),
        (&wrong_entry_pda, entry_before),
    ]);
}

#[test]
fn canonical_seed_schedules_bind_pool_profile_and_release() {
    let program_id = Pubkey::new_unique();
    let pool = Pubkey::new_unique();
    let (registry, registry_bump) = pool_v1_verifier_registry_address(&program_id, &pool);
    assert_eq!(
        registry,
        Pubkey::create_program_address(
            &[
                POOL_V1_VERIFIER_REGISTRY_SEED,
                pool.as_ref(),
                &[registry_bump],
            ],
            &program_id,
        )
        .unwrap()
    );

    let (entry, entry_bump) =
        pool_v1_verifier_entry_address(&program_id, &pool, &PROFILE_BINDING, &RELEASE_A);
    assert_eq!(
        entry,
        Pubkey::create_program_address(
            &[
                POOL_V1_VERIFIER_ENTRY_SEED,
                pool.as_ref(),
                &PROFILE_BINDING,
                &RELEASE_A,
                &[entry_bump],
            ],
            &program_id,
        )
        .unwrap()
    );
    assert_ne!(
        entry,
        pool_v1_verifier_entry_address(&program_id, &pool, &PROFILE_BINDING, &RELEASE_B,).0
    );
}
