#![no_std]

pub const NO_RETIREMENT_SLOT: u64 = u64::MAX;
pub const ASR8_BYTES: u16 = 792;
pub const STATEMENT_VERSION: u8 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegistryError {
    AlreadyInitialized,
    NotInitialized,
    DuplicateAccount,
    InvalidRegistryAccount,
    InvalidEntryAccount,
    InvalidAuthority,
    InvalidPayer,
    InvalidSystemProgram,
    InvalidFreshAccount,
    InvalidBinding,
    GenerationMismatch,
    GenerationOverflow,
    ActivationDelayOverflow,
    ActivationDelayNotElapsed,
    RegistryAlreadyPaused,
    RegistryNotPaused,
    EntryNotPending,
    EntryNotActive,
    InvalidEntryState,
    ReplacementNotActive,
    IncompatibleReplacement,
    InvalidRetirementSlot,
    RegistryFrozen,
    ReservationFailed,
    CommitBorrowFailed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelectionError {
    InvalidPolicy,
    InvalidRegistry,
    RegistryPaused,
    InvalidEntry,
    EntryInactive,
    EntryNotActiveYet,
    EntryRetired,
    SelectionMismatch,
    InvalidVerifierProgram,
    InvalidProof,
    VerifierCpi,
    MissingReturn,
    WrongReturnProgram,
    WrongReturnLength,
    InvalidReturn,
    ResultBinding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryStatus {
    Pending,
    Active,
    Paused,
    Retired,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryTarget {
    Primary,
    Replacement,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SupportedLoader {
    LegacyBpf,
    UpgradeableBpf,
    LoaderV4,
    Unsupported,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Registry {
    pub paused: bool,
    pub immutable: bool,
    pub pool: u64,
    pub authority: u64,
    pub policy: u64,
    pub generation: u64,
    pub minimum_activation_delay_slots: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Entry {
    pub status: EntryStatus,
    pub statement_version: u8,
    pub pool: u64,
    pub verifier_program: u64,
    pub profile: u64,
    pub release: u64,
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistrySystem {
    pub registry: Option<Registry>,
    pub primary: Option<Entry>,
    pub replacement: Option<Entry>,
    /// Frozen stand-in for Pool lane/history/vault state not owned by the
    /// registry program. Operator calls must preserve it exactly.
    pub unrelated_pool_state: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthorityGate {
    pub all_accounts_unique: bool,
    pub registry_account_exact: bool,
    pub registry_program_owned: bool,
    pub registry_writable: bool,
    pub registry_nonsigner: bool,
    pub authority_key: u64,
    pub authority_signer: bool,
    pub authority_readonly: bool,
    pub authority_nonexecutable: bool,
    pub commit_borrows_succeed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CreationGate {
    pub payer_signer: bool,
    pub payer_writable: bool,
    pub payer_system_owned: bool,
    pub payer_nonexecutable: bool,
    pub system_key_exact: bool,
    pub system_native_loader_owned: bool,
    pub system_executable: bool,
    pub system_readonly: bool,
    pub system_nonsigner: bool,
    pub fresh_pda_exact: bool,
    pub fresh_writable: bool,
    pub fresh_nonsigner: bool,
    pub fresh_nonexecutable: bool,
    pub fresh_system_empty_or_program_zeroed: bool,
    pub reservation_succeeds: bool,
    pub post_reservation_program_owned_zeroed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InitializeInput {
    pub pool: u64,
    pub policy: u64,
    pub authority: u64,
    pub minimum_activation_delay_slots: u64,
    pub all_accounts_unique: bool,
    pub authority_signer: bool,
    pub authority_readonly: bool,
    pub authority_nonexecutable: bool,
    pub registry_pda_exact: bool,
    pub creation: CreationGate,
    pub commit_borrow_succeeds: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScheduleInput {
    pub gate: AuthorityGate,
    pub creation: CreationGate,
    pub expected_generation: u64,
    pub target: EntryTarget,
    pub verifier_program: u64,
    pub profile: u64,
    pub release: u64,
    pub statement_version: u8,
    pub activation_slot: u64,
    pub current_slot: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SimpleMutationInput {
    pub gate: AuthorityGate,
    pub expected_generation: u64,
    pub target: EntryTarget,
    pub current_slot: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegistryOperation {
    Initialize(InitializeInput),
    Schedule(ScheduleInput),
    Pause(SimpleMutationInput),
    Unpause(SimpleMutationInput),
    Activate(SimpleMutationInput),
    Retire(SimpleMutationInput),
    Freeze(SimpleMutationInput),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryOutcome {
    pub committed: bool,
    pub state: RegistrySystem,
    pub error: Option<RegistryError>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SelectionInput {
    pub pool: u64,
    pub policy_registry_program: u64,
    pub policy_authority: u64,
    pub policy_binding: u64,
    pub policy_requires_immutable: bool,
    pub registry_account_program_owned: bool,
    pub registry_account_readonly: bool,
    pub registry_pda_exact: bool,
    pub entry_account_program_owned: bool,
    pub entry_account_readonly: bool,
    pub entry_pda_exact: bool,
    pub registry: Registry,
    pub entry: Entry,
    pub selected_verifier_program: u64,
    pub selected_profile: u64,
    pub selected_release: u64,
    pub statement_version: u8,
    pub current_slot: u64,
    pub verifier_key: u64,
    pub verifier_loader: SupportedLoader,
    pub verifier_executable: bool,
    pub verifier_readonly: bool,
    pub verifier_nonsigner: bool,
    pub proof_owner: u64,
    pub proof_readonly: bool,
    pub proof_nonsigner: bool,
    pub verifier_cpi_succeeds: bool,
    pub return_present: bool,
    pub returned_program: u64,
    pub returned_length: u16,
    pub returned_canonical: bool,
    pub returned_semantics_exact: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedSelection {
    pub pool: u64,
    pub registry_program: u64,
    pub registry_generation: u64,
    pub verifier_program: u64,
    pub profile: u64,
    pub release: u64,
    pub statement_version: u8,
    pub authenticated_at_slot: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceRoots {
    pub operator: RegistryOutcome,
    pub selected: Result<AuthenticatedSelection, SelectionError>,
}

fn valid_creation(gate: CreationGate) -> Result<(), RegistryError> {
    if !gate.payer_signer
        || !gate.payer_writable
        || !gate.payer_system_owned
        || !gate.payer_nonexecutable
    {
        return Err(RegistryError::InvalidPayer);
    }
    if !gate.system_key_exact
        || !gate.system_native_loader_owned
        || !gate.system_executable
        || !gate.system_readonly
        || !gate.system_nonsigner
    {
        return Err(RegistryError::InvalidSystemProgram);
    }
    if !gate.fresh_pda_exact
        || !gate.fresh_writable
        || !gate.fresh_nonsigner
        || !gate.fresh_nonexecutable
        || !gate.fresh_system_empty_or_program_zeroed
    {
        return Err(RegistryError::InvalidFreshAccount);
    }
    if !gate.reservation_succeeds {
        return Err(RegistryError::ReservationFailed);
    }
    if !gate.post_reservation_program_owned_zeroed {
        return Err(RegistryError::InvalidFreshAccount);
    }
    Ok(())
}

fn require_authority(
    registry: Registry,
    gate: AuthorityGate,
    expected_generation: u64,
) -> Result<(), RegistryError> {
    if !gate.all_accounts_unique {
        return Err(RegistryError::DuplicateAccount);
    }
    if !gate.registry_account_exact
        || !gate.registry_program_owned
        || !gate.registry_writable
        || !gate.registry_nonsigner
    {
        return Err(RegistryError::InvalidRegistryAccount);
    }
    if registry.immutable || registry.authority == 0 {
        return Err(RegistryError::RegistryFrozen);
    }
    if gate.authority_key != registry.authority
        || !gate.authority_signer
        || !gate.authority_readonly
        || !gate.authority_nonexecutable
    {
        return Err(RegistryError::InvalidAuthority);
    }
    if registry.generation != expected_generation {
        return Err(RegistryError::GenerationMismatch);
    }
    Ok(())
}

fn next_generation(registry: Registry) -> Result<Registry, RegistryError> {
    let generation = match registry.generation.checked_add(1) {
        Some(value) => value,
        None => return Err(RegistryError::GenerationOverflow),
    };
    Ok(Registry {
        generation,
        ..registry
    })
}

fn require_registry(system: RegistrySystem) -> Result<Registry, RegistryError> {
    match system.registry {
        Some(registry) => Ok(registry),
        None => Err(RegistryError::NotInitialized),
    }
}

fn require_target_entry(
    system: RegistrySystem,
    target: EntryTarget,
) -> Result<Entry, RegistryError> {
    match target_entry(system, target) {
        Some(entry) => Ok(entry),
        None => Err(RegistryError::InvalidEntryAccount),
    }
}

fn target_entry(system: RegistrySystem, target: EntryTarget) -> Option<Entry> {
    match target {
        EntryTarget::Primary => system.primary,
        EntryTarget::Replacement => system.replacement,
    }
}

fn replace_target(system: RegistrySystem, target: EntryTarget, entry: Entry) -> RegistrySystem {
    match target {
        EntryTarget::Primary => RegistrySystem {
            primary: Some(entry),
            ..system
        },
        EntryTarget::Replacement => RegistrySystem {
            replacement: Some(entry),
            ..system
        },
    }
}

fn entry_matches_registry(registry: Registry, entry: Entry) -> bool {
    entry.pool == registry.pool && entry.policy == registry.policy
}

fn active_at(entry: Entry, slot: u64) -> bool {
    entry.status == EntryStatus::Active
        && entry.activation_slot <= slot
        && (entry.retirement_slot == NO_RETIREMENT_SLOT || slot < entry.retirement_slot)
}

fn exact_replacement(retiring: Entry, replacement: Entry, slot: u64) -> bool {
    replacement.pool == retiring.pool
        && replacement.policy == retiring.policy
        && replacement.profile == retiring.profile
        && replacement.statement_version == retiring.statement_version
        && replacement.release != retiring.release
        && active_at(replacement, slot)
}

fn apply_initialize(
    before: RegistrySystem,
    input: InitializeInput,
) -> Result<RegistrySystem, RegistryError> {
    if before.registry.is_some() {
        return Err(RegistryError::AlreadyInitialized);
    }
    if !input.all_accounts_unique {
        return Err(RegistryError::DuplicateAccount);
    }
    if input.authority == 0
        || !input.authority_signer
        || !input.authority_readonly
        || !input.authority_nonexecutable
    {
        return Err(RegistryError::InvalidAuthority);
    }
    if input.pool == 0 || input.policy == 0 || input.minimum_activation_delay_slots == 0 {
        return Err(RegistryError::InvalidBinding);
    }
    if !input.registry_pda_exact {
        return Err(RegistryError::InvalidFreshAccount);
    }
    valid_creation(input.creation)?;
    if !input.commit_borrow_succeeds {
        return Err(RegistryError::CommitBorrowFailed);
    }
    Ok(RegistrySystem {
        registry: Some(Registry {
            paused: false,
            immutable: false,
            pool: input.pool,
            authority: input.authority,
            policy: input.policy,
            generation: 0,
            minimum_activation_delay_slots: input.minimum_activation_delay_slots,
        }),
        ..before
    })
}

fn schedule(before: RegistrySystem, input: ScheduleInput) -> Result<RegistrySystem, RegistryError> {
    let registry = require_registry(before)?;
    require_authority(registry, input.gate, input.expected_generation)?;
    valid_creation(input.creation)?;
    if target_entry(before, input.target).is_some() {
        return Err(RegistryError::InvalidFreshAccount);
    }
    let earliest = match input
        .current_slot
        .checked_add(registry.minimum_activation_delay_slots)
    {
        Some(value) => value,
        None => return Err(RegistryError::ActivationDelayOverflow),
    };
    if input.activation_slot < earliest {
        return Err(RegistryError::ActivationDelayNotElapsed);
    }
    if input.verifier_program == 0
        || input.profile == 0
        || input.release == 0
        || input.statement_version == 0
    {
        return Err(RegistryError::InvalidBinding);
    }
    if !input.gate.commit_borrows_succeed {
        return Err(RegistryError::CommitBorrowFailed);
    }
    let next_registry = next_generation(registry)?;
    let entry = Entry {
        status: EntryStatus::Pending,
        statement_version: input.statement_version,
        pool: registry.pool,
        verifier_program: input.verifier_program,
        profile: input.profile,
        release: input.release,
        activation_slot: input.activation_slot,
        retirement_slot: NO_RETIREMENT_SLOT,
        policy: registry.policy,
    };
    let with_entry = replace_target(before, input.target, entry);
    Ok(RegistrySystem {
        registry: Some(next_registry),
        ..with_entry
    })
}

fn pause_change(
    before: RegistrySystem,
    input: SimpleMutationInput,
    paused: bool,
) -> Result<RegistrySystem, RegistryError> {
    let registry = require_registry(before)?;
    require_authority(registry, input.gate, input.expected_generation)?;
    if registry.paused == paused {
        return Err(if paused {
            RegistryError::RegistryAlreadyPaused
        } else {
            RegistryError::RegistryNotPaused
        });
    }
    if !input.gate.commit_borrows_succeed {
        return Err(RegistryError::CommitBorrowFailed);
    }
    let mut next = next_generation(registry)?;
    next.paused = paused;
    Ok(RegistrySystem {
        registry: Some(next),
        ..before
    })
}

fn activate(
    before: RegistrySystem,
    input: SimpleMutationInput,
) -> Result<RegistrySystem, RegistryError> {
    let registry = require_registry(before)?;
    require_authority(registry, input.gate, input.expected_generation)?;
    let entry = require_target_entry(before, input.target)?;
    if !entry_matches_registry(registry, entry) {
        return Err(RegistryError::InvalidEntryAccount);
    }
    if entry.status != EntryStatus::Pending {
        return Err(RegistryError::EntryNotPending);
    }
    if entry.retirement_slot != NO_RETIREMENT_SLOT {
        return Err(RegistryError::InvalidEntryState);
    }
    if input.current_slot < entry.activation_slot {
        return Err(RegistryError::ActivationDelayNotElapsed);
    }
    if !input.gate.commit_borrows_succeed {
        return Err(RegistryError::CommitBorrowFailed);
    }
    let next_registry = next_generation(registry)?;
    let next_entry = Entry {
        status: EntryStatus::Active,
        ..entry
    };
    let with_entry = replace_target(before, input.target, next_entry);
    Ok(RegistrySystem {
        registry: Some(next_registry),
        ..with_entry
    })
}

fn retire(
    before: RegistrySystem,
    input: SimpleMutationInput,
) -> Result<RegistrySystem, RegistryError> {
    let registry = require_registry(before)?;
    require_authority(registry, input.gate, input.expected_generation)?;
    let retiring = require_target_entry(before, input.target)?;
    let replacement = match before.replacement {
        Some(entry) => entry,
        None => return Err(RegistryError::InvalidEntryAccount),
    };
    if !entry_matches_registry(registry, retiring) || !entry_matches_registry(registry, replacement)
    {
        return Err(RegistryError::InvalidEntryAccount);
    }
    if !active_at(retiring, input.current_slot) {
        return Err(RegistryError::EntryNotActive);
    }
    if retiring.retirement_slot != NO_RETIREMENT_SLOT {
        return Err(RegistryError::InvalidEntryState);
    }
    if !active_at(replacement, input.current_slot) {
        return Err(RegistryError::ReplacementNotActive);
    }
    if !exact_replacement(retiring, replacement, input.current_slot) {
        return Err(RegistryError::IncompatibleReplacement);
    }
    if input.current_slot <= retiring.activation_slot {
        return Err(RegistryError::InvalidRetirementSlot);
    }
    if !input.gate.commit_borrows_succeed {
        return Err(RegistryError::CommitBorrowFailed);
    }
    let next_registry = next_generation(registry)?;
    let next_entry = Entry {
        status: EntryStatus::Retired,
        retirement_slot: input.current_slot,
        ..retiring
    };
    let with_entry = replace_target(before, input.target, next_entry);
    Ok(RegistrySystem {
        registry: Some(next_registry),
        ..with_entry
    })
}

fn freeze(
    before: RegistrySystem,
    input: SimpleMutationInput,
) -> Result<RegistrySystem, RegistryError> {
    let registry = require_registry(before)?;
    require_authority(registry, input.gate, input.expected_generation)?;
    if !input.gate.commit_borrows_succeed {
        return Err(RegistryError::CommitBorrowFailed);
    }
    let mut next = next_generation(registry)?;
    next.immutable = true;
    next.authority = 0;
    Ok(RegistrySystem {
        registry: Some(next),
        ..before
    })
}

fn apply_operator(
    before: RegistrySystem,
    operation: RegistryOperation,
) -> Result<RegistrySystem, RegistryError> {
    match operation {
        RegistryOperation::Initialize(input) => apply_initialize(before, input),
        RegistryOperation::Schedule(input) => schedule(before, input),
        RegistryOperation::Pause(input) => pause_change(before, input, true),
        RegistryOperation::Unpause(input) => pause_change(before, input, false),
        RegistryOperation::Activate(input) => activate(before, input),
        RegistryOperation::Retire(input) => retire(before, input),
        RegistryOperation::Freeze(input) => freeze(before, input),
    }
}

pub fn execute_atomic_registry_operation(
    before: RegistrySystem,
    operation: RegistryOperation,
) -> RegistryOutcome {
    match apply_operator(before, operation) {
        Ok(state) => {
            // The registry program never owns or mutates Pool lane/history/
            // vault state. Keep that source-level frame condition explicit in
            // the operational projection instead of leaving it implicit in
            // account omission.
            let framed_state = RegistrySystem {
                unrelated_pool_state: before.unrelated_pool_state,
                ..state
            };
            RegistryOutcome {
                committed: true,
                state: framed_state,
                error: None,
            }
        }
        Err(error) => RegistryOutcome {
            committed: false,
            state: before,
            error: Some(error),
        },
    }
}

fn authenticate_registry(input: SelectionInput) -> Result<(), SelectionError> {
    if input.policy_registry_program == 0 || input.policy_binding == 0 {
        return Err(SelectionError::InvalidPolicy);
    }
    if !input.registry_account_program_owned
        || !input.registry_account_readonly
        || !input.registry_pda_exact
        || input.registry.pool != input.pool
        || input.registry.authority != input.policy_authority
        || input.registry.policy != input.policy_binding
        || input.registry.immutable != input.policy_requires_immutable
    {
        return Err(SelectionError::InvalidRegistry);
    }
    if input.registry.paused {
        return Err(SelectionError::RegistryPaused);
    }
    Ok(())
}

fn authenticate_entry(input: SelectionInput) -> Result<(), SelectionError> {
    if !input.entry_account_program_owned
        || !input.entry_account_readonly
        || !input.entry_pda_exact
        || input.entry.pool != input.pool
        || input.entry.policy != input.policy_binding
    {
        return Err(SelectionError::InvalidEntry);
    }
    if input.entry.verifier_program != input.selected_verifier_program
        || input.entry.profile != input.selected_profile
        || input.entry.release != input.selected_release
        || input.entry.statement_version != input.statement_version
    {
        return Err(SelectionError::SelectionMismatch);
    }
    if input.entry.status != EntryStatus::Active {
        return Err(SelectionError::EntryInactive);
    }
    if input.current_slot < input.entry.activation_slot {
        return Err(SelectionError::EntryNotActiveYet);
    }
    if input.entry.retirement_slot != NO_RETIREMENT_SLOT
        && input.current_slot >= input.entry.retirement_slot
    {
        return Err(SelectionError::EntryRetired);
    }
    Ok(())
}

fn authenticate_verifier_accounts(input: SelectionInput) -> Result<(), SelectionError> {
    if input.verifier_key != input.selected_verifier_program
        || input.verifier_loader == SupportedLoader::Unsupported
        || !input.verifier_executable
        || !input.verifier_readonly
        || !input.verifier_nonsigner
    {
        return Err(SelectionError::InvalidVerifierProgram);
    }
    if input.proof_owner != input.selected_verifier_program
        || !input.proof_readonly
        || !input.proof_nonsigner
    {
        return Err(SelectionError::InvalidProof);
    }
    Ok(())
}

fn authenticate_verifier_return(input: SelectionInput) -> Result<(), SelectionError> {
    if !input.verifier_cpi_succeeds {
        return Err(SelectionError::VerifierCpi);
    }
    if !input.return_present {
        return Err(SelectionError::MissingReturn);
    }
    if input.returned_program != input.selected_verifier_program {
        return Err(SelectionError::WrongReturnProgram);
    }
    if input.returned_length != ASR8_BYTES {
        return Err(SelectionError::WrongReturnLength);
    }
    if !input.returned_canonical {
        return Err(SelectionError::InvalidReturn);
    }
    if !input.returned_semantics_exact {
        return Err(SelectionError::ResultBinding);
    }
    Ok(())
}

pub fn authenticate_and_invoke_selected_verifier(
    input: SelectionInput,
) -> Result<AuthenticatedSelection, SelectionError> {
    authenticate_registry(input)?;
    authenticate_entry(input)?;
    authenticate_verifier_accounts(input)?;
    authenticate_verifier_return(input)?;
    Ok(AuthenticatedSelection {
        pool: input.pool,
        registry_program: input.policy_registry_program,
        registry_generation: input.registry.generation,
        verifier_program: input.selected_verifier_program,
        profile: input.selected_profile,
        release: input.selected_release,
        statement_version: input.statement_version,
        authenticated_at_slot: input.current_slot,
    })
}

/// The single Charon root keeps both production-facing control-flow families
/// in the extracted call graph without conflating operator mutation with the
/// Pool's read-only selected-verifier use.
pub fn registry_operator_and_selected_verifier_source_roots(
    before: RegistrySystem,
    operation: RegistryOperation,
    selection: SelectionInput,
) -> SourceRoots {
    SourceRoots {
        operator: execute_atomic_registry_operation(before, operation),
        selected: authenticate_and_invoke_selected_verifier(selection),
    }
}
