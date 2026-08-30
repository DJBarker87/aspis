#![no_std]

pub const NULLIFIER_MARKER_BYTES: u16 = 208;
pub const NULLIFIER_MARKER_SEED_TAG: u64 = 0x4153_504e;
pub const SYSTEM_PROGRAM_ID: u64 = 1;
pub const NATIVE_LOADER_ID: u64 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MarkerError {
    NonCanonicalRent,
    DuplicateAccount,
    InvalidPayer,
    InvalidSystemProgram,
    InvalidMarkerAddress,
    InvalidMarkerAccount,
    SpentNullifier,
    InsufficientFunds,
    CreateAccountCpi,
    TransferCpi,
    AllocateCpi,
    AssignCpi,
    ReplanMismatch,
    VerifierCpi,
    CoreApply,
    MarkerWrite,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MarkerPreparation {
    CreateZeroLamport,
    AllocateDusted,
    ProgramOwnedZeroed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReservationPath {
    CreateAccount,
    TransferAllocateAssign,
    AllocateAssign,
    AlreadyProgramOwned,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccountView {
    pub key: u64,
    pub owner: u64,
    pub writable: bool,
    pub signer: bool,
    pub executable: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PayerAccount {
    pub account: AccountView,
    pub lamports: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerImage {
    pub transition_kind: u8,
    pub pool: u64,
    pub deployment_domain: u64,
    pub nullifier: u64,
    pub retained_anchor_sequence: u64,
    pub retained_anchor_root: u64,
    pub verifier_profile: u64,
    pub verifier_release: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerAccount {
    pub account: AccountView,
    pub lamports: u64,
    pub data_len: u16,
    pub data_zeroed: bool,
    pub stored_marker: Option<MarkerImage>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerDerivation {
    pub expected_address: u64,
    pub seed_tag: u64,
    pub pool: u64,
    pub canonical_nullifier: u64,
    pub bump: u8,
    pub pda_exact: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RentSchedule {
    /// The production dispatcher obtains this value through `Rent::get()`;
    /// there is deliberately no caller-supplied Rent account meta.
    pub loaded_from_sysvar: bool,
    /// This is `Rent::minimum_balance(208).max(1)` in the production caller.
    pub required_lamports: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeOutcomes {
    pub create_account_succeeds: bool,
    pub transfer_succeeds: bool,
    pub allocate_succeeds: bool,
    pub assign_succeeds: bool,
    pub verifier_cpi_succeeds: bool,
    /// The already-proved one-terminal caller body after verifier acceptance.
    pub core_apply_succeeds: bool,
    pub marker_write_succeeds: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerTerminalInput {
    pub program_id: u64,
    pub pool: u64,
    pub all_terminal_accounts_unique: bool,
    pub system_program: AccountView,
    pub derivation: MarkerDerivation,
    pub expected_marker: MarkerImage,
    pub rent: RentSchedule,
    pub runtime: RuntimeOutcomes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerTerminalState {
    pub payer: PayerAccount,
    pub marker: MarkerAccount,
    /// This is the seam to the frozen one-terminal lane/history/custody bridge.
    pub core_writeback_applied: bool,
    pub unrelated: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlannedMarker {
    pub preparation: MarkerPreparation,
    pub address_bump: u8,
    pub marker: MarkerImage,
}

/// A zero step means that action did not complete. Nonzero values are the
/// exact successful operational order in this focused projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CallTrace {
    pub create_account_step: u8,
    pub transfer_step: u8,
    pub allocate_step: u8,
    pub assign_step: u8,
    pub replan_step: u8,
    pub verifier_step: u8,
    pub core_apply_step: u8,
    pub consume_step: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AcceptedMarkerLifecycle {
    pub path: ReservationPath,
    pub marker: MarkerImage,
    pub payer_before: u64,
    pub payer_after: u64,
    pub ready_marker_lamports: u64,
    pub trace: CallTrace,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerTerminalOutcome {
    pub committed: bool,
    pub state: MarkerTerminalState,
    pub trace: CallTrace,
    pub certificate: Option<AcceptedMarkerLifecycle>,
    pub error: Option<MarkerError>,
}

fn empty_trace() -> CallTrace {
    CallTrace {
        create_account_step: 0,
        transfer_step: 0,
        allocate_step: 0,
        assign_step: 0,
        replan_step: 0,
        verifier_step: 0,
        core_apply_step: 0,
        consume_step: 0,
    }
}

fn marker_images_equal(left: MarkerImage, right: MarkerImage) -> bool {
    left.transition_kind == right.transition_kind
        && left.pool == right.pool
        && left.deployment_domain == right.deployment_domain
        && left.nullifier == right.nullifier
        && left.retained_anchor_sequence == right.retained_anchor_sequence
        && left.retained_anchor_root == right.retained_anchor_root
        && left.verifier_profile == right.verifier_profile
        && left.verifier_release == right.verifier_release
}

fn authenticate_payer_and_system(
    input: MarkerTerminalInput,
    state: MarkerTerminalState,
) -> Result<(), MarkerError> {
    if !input.all_terminal_accounts_unique {
        return Err(MarkerError::DuplicateAccount);
    }
    if !state.payer.account.signer
        || !state.payer.account.writable
        || state.payer.account.executable
        || state.payer.account.owner != SYSTEM_PROGRAM_ID
    {
        return Err(MarkerError::InvalidPayer);
    }
    if input.system_program.key != SYSTEM_PROGRAM_ID
        || input.system_program.owner != NATIVE_LOADER_ID
        || !input.system_program.executable
        || input.system_program.signer
        || input.system_program.writable
    {
        return Err(MarkerError::InvalidSystemProgram);
    }
    Ok(())
}

fn plan_marker(
    input: MarkerTerminalInput,
    marker: MarkerAccount,
) -> Result<PlannedMarker, MarkerError> {
    if !input.derivation.pda_exact
        || input.derivation.seed_tag != NULLIFIER_MARKER_SEED_TAG
        || input.derivation.pool != input.pool
        || input.derivation.canonical_nullifier != input.expected_marker.nullifier
        || input.expected_marker.pool != input.pool
        || marker.account.key != input.derivation.expected_address
        || marker.account.key == input.pool
    {
        return Err(MarkerError::InvalidMarkerAddress);
    }
    if marker.account.executable || marker.account.signer || !marker.account.writable {
        return Err(MarkerError::InvalidMarkerAccount);
    }

    let preparation = if marker.account.owner == input.program_id {
        if marker.data_len != NULLIFIER_MARKER_BYTES {
            return Err(MarkerError::InvalidMarkerAccount);
        }
        match marker.stored_marker {
            Some(_) => return Err(MarkerError::SpentNullifier),
            None => {
                if !marker.data_zeroed {
                    return Err(MarkerError::InvalidMarkerAccount);
                }
                MarkerPreparation::ProgramOwnedZeroed
            }
        }
    } else if marker.account.owner == SYSTEM_PROGRAM_ID {
        if marker.data_len != 0 || !marker.data_zeroed {
            return Err(MarkerError::InvalidMarkerAccount);
        }
        match marker.stored_marker {
            Some(_) => return Err(MarkerError::InvalidMarkerAccount),
            None => {
                if marker.lamports == 0 {
                    MarkerPreparation::CreateZeroLamport
                } else {
                    MarkerPreparation::AllocateDusted
                }
            }
        }
    } else {
        return Err(MarkerError::InvalidMarkerAccount);
    };

    Ok(PlannedMarker {
        preparation,
        address_bump: input.derivation.bump,
        marker: input.expected_marker,
    })
}

fn reserve_marker(
    input: MarkerTerminalInput,
    mut state: MarkerTerminalState,
    planned: PlannedMarker,
) -> Result<(MarkerTerminalState, ReservationPath), MarkerError> {
    match planned.preparation {
        MarkerPreparation::ProgramOwnedZeroed => Ok((state, ReservationPath::AlreadyProgramOwned)),
        MarkerPreparation::CreateZeroLamport => {
            if state.payer.lamports < input.rent.required_lamports {
                return Err(MarkerError::InsufficientFunds);
            }
            if !input.runtime.create_account_succeeds {
                return Err(MarkerError::CreateAccountCpi);
            }
            state.payer.lamports -= input.rent.required_lamports;
            state.marker.lamports = input.rent.required_lamports;
            state.marker.account.owner = input.program_id;
            state.marker.data_len = NULLIFIER_MARKER_BYTES;
            state.marker.data_zeroed = true;
            state.marker.stored_marker = None;
            Ok((state, ReservationPath::CreateAccount))
        }
        MarkerPreparation::AllocateDusted => {
            let needs_top_up = state.marker.lamports < input.rent.required_lamports;
            if needs_top_up {
                let deficit = input.rent.required_lamports - state.marker.lamports;
                if state.payer.lamports < deficit {
                    return Err(MarkerError::InsufficientFunds);
                }
                if !input.runtime.transfer_succeeds {
                    return Err(MarkerError::TransferCpi);
                }
                state.payer.lamports -= deficit;
                state.marker.lamports = input.rent.required_lamports;
            }
            if !input.runtime.allocate_succeeds {
                return Err(MarkerError::AllocateCpi);
            }
            state.marker.data_len = NULLIFIER_MARKER_BYTES;
            state.marker.data_zeroed = true;
            state.marker.stored_marker = None;
            if !input.runtime.assign_succeeds {
                return Err(MarkerError::AssignCpi);
            }
            state.marker.account.owner = input.program_id;
            if needs_top_up {
                Ok((state, ReservationPath::TransferAllocateAssign))
            } else {
                Ok((state, ReservationPath::AllocateAssign))
            }
        }
    }
}

fn reservation_trace(path: ReservationPath) -> CallTrace {
    match path {
        ReservationPath::AlreadyProgramOwned => CallTrace {
            replan_step: 1,
            ..empty_trace()
        },
        ReservationPath::CreateAccount => CallTrace {
            create_account_step: 1,
            replan_step: 2,
            ..empty_trace()
        },
        ReservationPath::AllocateAssign => CallTrace {
            allocate_step: 1,
            assign_step: 2,
            replan_step: 3,
            ..empty_trace()
        },
        ReservationPath::TransferAllocateAssign => CallTrace {
            transfer_step: 1,
            allocate_step: 2,
            assign_step: 3,
            replan_step: 4,
            ..empty_trace()
        },
    }
}

fn record_verifier(mut trace: CallTrace, path: ReservationPath) -> CallTrace {
    trace.verifier_step = match path {
        ReservationPath::AlreadyProgramOwned => 2,
        ReservationPath::CreateAccount => 3,
        ReservationPath::AllocateAssign => 4,
        ReservationPath::TransferAllocateAssign => 5,
    };
    trace
}

fn record_core_apply(mut trace: CallTrace, path: ReservationPath) -> CallTrace {
    trace.core_apply_step = match path {
        ReservationPath::AlreadyProgramOwned => 3,
        ReservationPath::CreateAccount => 4,
        ReservationPath::AllocateAssign => 5,
        ReservationPath::TransferAllocateAssign => 6,
    };
    trace
}

fn record_consumption(mut trace: CallTrace, path: ReservationPath) -> CallTrace {
    trace.consume_step = match path {
        ReservationPath::AlreadyProgramOwned => 4,
        ReservationPath::CreateAccount => 5,
        ReservationPath::AllocateAssign => 6,
        ReservationPath::TransferAllocateAssign => 7,
    };
    trace
}

fn rejected_inner(
    state: MarkerTerminalState,
    trace: CallTrace,
    error: MarkerError,
) -> MarkerTerminalOutcome {
    MarkerTerminalOutcome {
        committed: false,
        state,
        trace,
        certificate: None,
        error: Some(error),
    }
}

/// Fixed-width projection of the production order:
/// authenticate -> plan -> System CPI reservation -> exact replan/rent gate ->
/// verifier CPI -> frozen caller core -> marker consumption.
pub fn execute_marker_terminal_inner(
    input: MarkerTerminalInput,
    before: MarkerTerminalState,
) -> MarkerTerminalOutcome {
    if !input.rent.loaded_from_sysvar || input.rent.required_lamports == 0 {
        return rejected_inner(before, empty_trace(), MarkerError::NonCanonicalRent);
    }
    if let Err(error) = authenticate_payer_and_system(input, before) {
        return rejected_inner(before, empty_trace(), error);
    }
    let planned = match plan_marker(input, before.marker) {
        Ok(planned) => planned,
        Err(error) => return rejected_inner(before, empty_trace(), error),
    };
    let (mut state, path) = match reserve_marker(input, before, planned) {
        Ok(reserved) => reserved,
        Err(error) => return rejected_inner(before, empty_trace(), error),
    };

    // This is the production second call to marker planning. It rejects any
    // owner/size/zero/PDA drift after create/allocate/assign and then enforces
    // the exact Rent exemption used by the live runtime.
    let ready = match plan_marker(input, state.marker) {
        Ok(ready) => ready,
        Err(error) => return rejected_inner(state, empty_trace(), error),
    };
    if ready.preparation != MarkerPreparation::ProgramOwnedZeroed
        || ready.address_bump != planned.address_bump
        || !marker_images_equal(ready.marker, planned.marker)
        || state.marker.lamports < input.rent.required_lamports
    {
        return rejected_inner(state, empty_trace(), MarkerError::ReplanMismatch);
    }

    let mut trace = reservation_trace(path);
    trace = record_verifier(trace, path);
    if !input.runtime.verifier_cpi_succeeds {
        return rejected_inner(state, trace, MarkerError::VerifierCpi);
    }

    trace = record_core_apply(trace, path);
    if !input.runtime.core_apply_succeeds {
        return rejected_inner(state, trace, MarkerError::CoreApply);
    }
    state.core_writeback_applied = true;

    if !input.runtime.marker_write_succeeds {
        return rejected_inner(state, trace, MarkerError::MarkerWrite);
    }
    state.marker.data_zeroed = false;
    state.marker.stored_marker = Some(ready.marker);
    trace = record_consumption(trace, path);

    MarkerTerminalOutcome {
        committed: true,
        state,
        trace,
        certificate: Some(AcceptedMarkerLifecycle {
            path,
            marker: ready.marker,
            payer_before: before.payer.lamports,
            payer_after: state.payer.lamports,
            ready_marker_lamports: state.marker.lamports,
            trace,
        }),
        error: None,
    }
}

/// Solana's instruction journal is modeled only here: every rejected inner
/// execution returns the exact full pre-state, including payer lamports and a
/// marker that may have been reserved before verifier failure.
pub fn execute_atomic_marker_terminal(
    input: MarkerTerminalInput,
    before: MarkerTerminalState,
) -> MarkerTerminalOutcome {
    let inner = execute_marker_terminal_inner(input, before);
    if inner.committed {
        inner
    } else {
        MarkerTerminalOutcome {
            committed: false,
            state: before,
            trace: inner.trace,
            certificate: None,
            error: inner.error,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn account(
        key: u64,
        owner: u64,
        writable: bool,
        signer: bool,
        executable: bool,
    ) -> AccountView {
        AccountView {
            key,
            owner,
            writable,
            signer,
            executable,
        }
    }

    fn fixture(path: ReservationPath) -> (MarkerTerminalInput, MarkerTerminalState) {
        let program_id = 10;
        let pool = 20;
        let required = 1_000;
        let expected_marker = MarkerImage {
            transition_kind: 1,
            pool,
            deployment_domain: 21,
            nullifier: 22,
            retained_anchor_sequence: 23,
            retained_anchor_root: 24,
            verifier_profile: 25,
            verifier_release: 26,
        };
        let (marker_owner, marker_lamports, marker_len) = match path {
            ReservationPath::CreateAccount => (SYSTEM_PROGRAM_ID, 0, 0),
            ReservationPath::TransferAllocateAssign => (SYSTEM_PROGRAM_ID, required - 7, 0),
            ReservationPath::AllocateAssign => (SYSTEM_PROGRAM_ID, required + 5, 0),
            ReservationPath::AlreadyProgramOwned => (program_id, required, NULLIFIER_MARKER_BYTES),
        };
        let input = MarkerTerminalInput {
            program_id,
            pool,
            all_terminal_accounts_unique: true,
            system_program: account(SYSTEM_PROGRAM_ID, NATIVE_LOADER_ID, false, false, true),
            derivation: MarkerDerivation {
                expected_address: 30,
                seed_tag: NULLIFIER_MARKER_SEED_TAG,
                pool,
                canonical_nullifier: expected_marker.nullifier,
                bump: 254,
                pda_exact: true,
            },
            expected_marker,
            rent: RentSchedule {
                loaded_from_sysvar: true,
                required_lamports: required,
            },
            runtime: RuntimeOutcomes {
                create_account_succeeds: true,
                transfer_succeeds: true,
                allocate_succeeds: true,
                assign_succeeds: true,
                verifier_cpi_succeeds: true,
                core_apply_succeeds: true,
                marker_write_succeeds: true,
            },
        };
        let state = MarkerTerminalState {
            payer: PayerAccount {
                account: account(40, SYSTEM_PROGRAM_ID, true, true, false),
                lamports: 10_000,
            },
            marker: MarkerAccount {
                account: account(30, marker_owner, true, false, false),
                lamports: marker_lamports,
                data_len: marker_len,
                data_zeroed: true,
                stored_marker: None,
            },
            core_writeback_applied: false,
            unrelated: 99,
        };
        (input, state)
    }

    #[test]
    fn every_admissible_reservation_path_commits_and_consumes_exact_marker() {
        for path in [
            ReservationPath::CreateAccount,
            ReservationPath::TransferAllocateAssign,
            ReservationPath::AllocateAssign,
            ReservationPath::AlreadyProgramOwned,
        ] {
            let (input, before) = fixture(path);
            let out = execute_atomic_marker_terminal(input, before);
            assert!(out.committed);
            assert_eq!(out.error, None);
            assert_eq!(out.state.marker.account.owner, input.program_id);
            assert_eq!(out.state.marker.data_len, NULLIFIER_MARKER_BYTES);
            assert!(out.state.marker.lamports >= input.rent.required_lamports);
            assert_eq!(out.state.marker.stored_marker, Some(input.expected_marker));
            assert!(!out.state.marker.data_zeroed);
            assert!(out.state.core_writeback_applied);
            assert_eq!(out.state.unrelated, before.unrelated);
            let certificate = out.certificate.expect("accepted marker certificate");
            assert_eq!(certificate.path, path);
            assert!(certificate.trace.replan_step < certificate.trace.verifier_step);
            assert!(certificate.trace.verifier_step < certificate.trace.core_apply_step);
            assert!(certificate.trace.core_apply_step < certificate.trace.consume_step);
        }
    }

    #[test]
    fn verifier_and_post_verifier_failures_rollback_reserved_marker_and_payer() {
        for failure in 0..3 {
            let (mut input, before) = fixture(ReservationPath::CreateAccount);
            match failure {
                0 => input.runtime.verifier_cpi_succeeds = false,
                1 => input.runtime.core_apply_succeeds = false,
                2 => input.runtime.marker_write_succeeds = false,
                _ => unreachable!(),
            }
            let inner = execute_marker_terminal_inner(input, before);
            assert!(!inner.committed);
            assert_eq!(inner.state.marker.account.owner, input.program_id);
            assert_eq!(inner.state.marker.data_len, NULLIFIER_MARKER_BYTES);
            let atomic = execute_atomic_marker_terminal(input, before);
            assert!(!atomic.committed);
            assert_eq!(atomic.state, before);
            assert_eq!(atomic.certificate, None);
            assert!(atomic.error.is_some());
        }
    }

    #[test]
    fn system_cpi_failures_and_insufficient_funds_are_atomic() {
        for failure in 0..5 {
            let path = if failure < 2 {
                ReservationPath::CreateAccount
            } else {
                ReservationPath::TransferAllocateAssign
            };
            let (mut input, mut before) = fixture(path);
            match failure {
                0 => before.payer.lamports = 0,
                1 => input.runtime.create_account_succeeds = false,
                2 => input.runtime.transfer_succeeds = false,
                3 => input.runtime.allocate_succeeds = false,
                4 => input.runtime.assign_succeeds = false,
                _ => unreachable!(),
            }
            let out = execute_atomic_marker_terminal(input, before);
            assert!(!out.committed);
            assert_eq!(out.state, before);
            assert_eq!(out.certificate, None);
            assert!(out.error.is_some());
        }
    }

    #[test]
    fn payer_system_rent_pda_owner_size_and_zero_checks_fail_closed() {
        for failure in 0..10 {
            let (mut input, mut before) = fixture(ReservationPath::AlreadyProgramOwned);
            match failure {
                0 => before.payer.account.signer = false,
                1 => before.payer.account.owner = 77,
                2 => input.system_program.key = 77,
                3 => input.system_program.owner = 77,
                4 => input.rent.loaded_from_sysvar = false,
                5 => input.derivation.pda_exact = false,
                6 => input.derivation.canonical_nullifier += 1,
                7 => before.marker.account.owner = 77,
                8 => before.marker.data_len -= 1,
                9 => before.marker.data_zeroed = false,
                _ => unreachable!(),
            }
            let out = execute_atomic_marker_terminal(input, before);
            assert!(!out.committed);
            assert_eq!(out.state, before);
        }
    }

    #[test]
    fn exact_success_is_single_use_and_replay_is_pre_verifier_rejection() {
        let (input, before) = fixture(ReservationPath::CreateAccount);
        let success = execute_atomic_marker_terminal(input, before);
        assert!(success.committed);
        let replay = execute_atomic_marker_terminal(input, success.state);
        assert!(!replay.committed);
        assert_eq!(replay.state, success.state);
        assert_eq!(replay.error, Some(MarkerError::SpentNullifier));
        assert_eq!(replay.trace, empty_trace());
    }
}
