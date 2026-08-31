#![no_std]

pub const ASQ8_BYTES: u16 = 320;
pub const ASR8_BYTES: u16 = 792;
pub const ROOT_HISTORY_CAPACITY: u16 = 256;
pub const STATEMENT_VERSION: u8 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaymentKind {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PageRoute {
    SamePage,
    Rollover,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallerError {
    WrongRequest,
    WrongAccount,
    WrongRegistry,
    SpentNullifier,
    WrongHistory,
    WithdrawalPlan,
    VerifierCpi,
    VerifierReturn,
    ResultBinding,
    NextLane,
    Borrow,
    WithdrawalAccounts,
    WithdrawalCpi,
    WithdrawalDelta,
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
pub struct SelectedRelease {
    pub pool_program: u64,
    pub verifier_program: u64,
    pub registry_program: u64,
    pub loader_program: u64,
    pub registry_programdata: u64,
    pub verifier_programdata: u64,
    pub profile: u64,
    pub release: u64,
    pub policy_binding: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierPolicy {
    pub registry_program: u64,
    pub registry_authority: u64,
    pub policy_binding: u64,
    pub immutable_registry: bool,
    pub immutable_deployment: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MasterState {
    pub account: AccountView,
    pub deployment_domain: u64,
    pub policy: VerifierPolicy,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointState {
    pub account: AccountView,
    pub master: u64,
    pub sequence: u64,
    pub global_root: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneState {
    pub account: AccountView,
    pub master: u64,
    pub lane_id: u8,
    pub next_pair_index: u64,
    pub root: u64,
    pub frontier: u64,
    pub invariant_capability: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryState {
    pub account: AccountView,
    pub canonical_v2: bool,
    pub pda_exact: bool,
    pub pool: u64,
    pub authority: u64,
    pub policy_binding: u64,
    pub immutable: bool,
    pub paused: bool,
    pub registry_program: u64,
    pub loader_program: u64,
    pub programdata_address: u64,
    pub programdata_pda_exact: bool,
    pub executable_hash: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryEntry {
    pub account: AccountView,
    pub canonical_v2: bool,
    pub pda_exact: bool,
    pub pool: u64,
    pub verifier_program: u64,
    pub profile: u64,
    pub release: u64,
    pub loader_program: u64,
    pub programdata_address: u64,
    pub programdata_pda_exact: bool,
    pub executable_hash: u64,
    pub expected_upgrade_authority: u64,
    pub statement_version: u8,
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub enabled: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Request {
    pub encoded_len: u16,
    pub canonical: bool,
    pub pool_program: u64,
    pub master_account: u64,
    pub checkpoint_account: u64,
    pub selected_lane_account: u64,
    pub profile: u64,
    pub release: u64,
    pub nullifier: u64,
    pub output_lane: u8,
    pub payment_kind: PaymentKind,
    pub withdrawal_amount: u64,
    pub withdrawal_destination: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofState {
    pub account: AccountView,
    pub bound_master: u64,
    pub bound_checkpoint: u64,
    pub bound_lane: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReturnedResult {
    pub transition_kind: PaymentKind,
    pub master_account: u64,
    pub selected_lane_account: u64,
    pub output_lane: u8,
    pub nullifier: u64,
    pub next_pair_index: u64,
    pub next_root: u64,
    pub next_frontier: u64,
    pub next_frontier_canonical: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierReturn {
    pub program: u64,
    pub encoded_len: u16,
    pub canonical: bool,
    pub exact_bytes_id: u64,
    pub decoded: Option<ReturnedResult>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PageInput {
    pub account: AccountView,
    pub pool_lane: u64,
    pub page_number: u64,
    pub filled: u16,
    pub canonical: bool,
    pub zeroed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerInput {
    pub account: AccountView,
    pub pda_exact: bool,
    pub program_owned_zeroed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TokenInput {
    pub exact_five_accounts: bool,
    pub token_program_exact: bool,
    pub mint_exact: bool,
    pub vault_authority_exact: bool,
    pub destination_exact: bool,
    pub vault_before: u64,
    pub destination_before: u64,
    pub vault_after: u64,
    pub destination_after: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeOutcomes {
    pub verifier_cpi_succeeded: bool,
    pub lane_borrow_succeeded: bool,
    pub page_borrow_succeeded: bool,
    pub marker_borrow_succeeded: bool,
    pub withdrawal_cpi_succeeded: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CallerInput {
    pub release: SelectedRelease,
    pub request: Request,
    pub master: MasterState,
    pub checkpoint: CheckpointState,
    pub lane: LaneState,
    pub registry: RegistryState,
    pub entry: RegistryEntry,
    pub verifier: AccountView,
    pub proof: ProofState,
    pub current_page: PageInput,
    pub rollover_page: PageInput,
    pub marker: MarkerInput,
    pub tokens: TokenInput,
    pub current_slot: u64,
    pub verifier_return: VerifierReturn,
    pub runtime: RuntimeOutcomes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MarkerImage {
    pub master: u64,
    pub deployment_domain: u64,
    pub nullifier: u64,
    pub checkpoint_sequence: u64,
    pub checkpoint_root: u64,
    pub profile: u64,
    pub release: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistoryWrite {
    pub route: PageRoute,
    pub page_number: u64,
    pub first_sequence: u64,
    pub root: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpiMeta {
    pub key: u64,
    pub writable: bool,
    pub signer: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolImages {
    pub lane: LaneState,
    pub current_page_last_root: u64,
    pub current_page_filled: u16,
    pub rollover_page_last_root: u64,
    pub rollover_page_filled: u16,
    pub marker: Option<MarkerImage>,
    pub vault_balance: u64,
    pub destination_balance: u64,
    pub returned_result: Option<ReturnedResult>,
    pub returned_result_bytes_id: Option<u64>,
    pub unrelated: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AcceptanceCertificate {
    pub path_kind: PaymentKind,
    pub page_route: PageRoute,
    pub cpi_accounts: [CpiMeta; 6],
    pub result: ReturnedResult,
    pub result_bytes_id: u64,
    pub history_write: HistoryWrite,
    pub marker: MarkerImage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AcceptedExecution {
    pub state: PoolImages,
    pub certificate: AcceptanceCertificate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTerminal {
    pub marker: MarkerImage,
    pub result: ReturnedResult,
    pub history: HistoryWrite,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TransactionOutcome {
    pub committed: bool,
    pub state: PoolImages,
    pub certificate: Option<AcceptanceCertificate>,
    pub error: Option<CallerError>,
}

pub fn exact_cpi_accounts(input: &CallerInput) -> [CpiMeta; 6] {
    [
        CpiMeta {
            key: input.proof.account.key,
            writable: false,
            signer: false,
        },
        CpiMeta {
            key: input.master.account.key,
            writable: false,
            signer: false,
        },
        CpiMeta {
            key: input.checkpoint.account.key,
            writable: false,
            signer: false,
        },
        CpiMeta {
            key: input.lane.account.key,
            writable: false,
            signer: false,
        },
        CpiMeta {
            key: input.registry.account.key,
            writable: false,
            signer: false,
        },
        CpiMeta {
            key: input.entry.account.key,
            writable: false,
            signer: false,
        },
    ]
}

fn authenticate_request(input: &CallerInput) -> Result<(), CallerError> {
    let release = input.release;
    let request = input.request;
    if request.encoded_len != ASQ8_BYTES
        || !request.canonical
        || request.pool_program != release.pool_program
        || request.master_account != input.master.account.key
        || request.checkpoint_account != input.checkpoint.account.key
        || request.selected_lane_account != input.lane.account.key
        || request.profile != release.profile
        || request.release != release.release
        || request.output_lane != input.lane.lane_id
    {
        return Err(CallerError::WrongRequest);
    }
    Ok(())
}

fn authenticate_pool_accounts(input: &CallerInput) -> Result<(), CallerError> {
    let release = input.release;
    if input.master.account.owner != release.pool_program
        || input.checkpoint.account.owner != release.pool_program
        || input.lane.account.owner != release.pool_program
        || input.master.account.writable
        || input.master.account.signer
        || input.checkpoint.account.writable
        || input.checkpoint.account.signer
        || !input.lane.account.writable
        || input.lane.account.signer
        || input.checkpoint.master != input.master.account.key
        || input.lane.master != input.master.account.key
        || !input.lane.invariant_capability
    {
        return Err(CallerError::WrongAccount);
    }
    Ok(())
}

fn authenticate_registry_policy_and_accounts(input: &CallerInput) -> Result<(), CallerError> {
    let release = input.release;
    if input.master.policy.registry_program != release.registry_program
        || input.master.policy.registry_authority != 0
        || input.master.policy.policy_binding != release.policy_binding
        || !input.master.policy.immutable_registry
        || !input.master.policy.immutable_deployment
        || input.registry.account.owner != release.registry_program
        || input.entry.account.owner != release.registry_program
        || input.registry.account.writable
        || input.registry.account.signer
        || input.entry.account.writable
        || input.entry.account.signer
    {
        return Err(CallerError::WrongRegistry);
    }
    Ok(())
}

fn authenticate_registry_v2_certificate(input: &CallerInput) -> Result<(), CallerError> {
    let release = input.release;
    if !input.registry.canonical_v2
        || !input.registry.pda_exact
        || input.registry.pool != input.master.account.key
        || input.registry.authority != 0
        || input.registry.policy_binding != release.policy_binding
        || !input.registry.immutable
        || input.registry.paused
        || input.registry.registry_program != release.registry_program
        || input.registry.loader_program != release.loader_program
        || input.registry.programdata_address != release.registry_programdata
        || !input.registry.programdata_pda_exact
        || input.registry.executable_hash == 0
    {
        return Err(CallerError::WrongRegistry);
    }
    Ok(())
}

fn authenticate_entry_v2_certificate(input: &CallerInput) -> Result<(), CallerError> {
    let release = input.release;
    if !input.entry.canonical_v2
        || !input.entry.pda_exact
        || input.entry.pool != input.master.account.key
        || input.entry.verifier_program != release.verifier_program
        || input.entry.profile != release.profile
        || input.entry.release != release.release
        || input.entry.loader_program != release.loader_program
        || input.entry.programdata_address != release.verifier_programdata
        || !input.entry.programdata_pda_exact
        || input.entry.executable_hash == 0
        || input.entry.expected_upgrade_authority != 0
        || input.entry.statement_version != STATEMENT_VERSION
    {
        return Err(CallerError::WrongRegistry);
    }
    Ok(())
}

fn authenticate_entry_active(input: &CallerInput) -> Result<(), CallerError> {
    if !input.entry.enabled
        || input.current_slot < input.entry.activation_slot
        || (input.entry.retirement_slot != 0 && input.current_slot >= input.entry.retirement_slot)
    {
        return Err(CallerError::WrongRegistry);
    }
    Ok(())
}

fn authenticate_registry(input: &CallerInput) -> Result<(), CallerError> {
    authenticate_registry_policy_and_accounts(input)?;
    authenticate_registry_v2_certificate(input)?;
    authenticate_entry_v2_certificate(input)?;
    authenticate_entry_active(input)?;
    Ok(())
}

/* The split above is extraction-only structure: it preserves the exact
 * fail-closed conjunction while keeping each generated Lean declaration
 * below the elaborator's pathological nested-if threshold. */

fn authenticate_selected_verifier(input: &CallerInput) -> Result<(), CallerError> {
    let release = input.release;
    if input.verifier.key != release.verifier_program
        || input.verifier.owner != release.loader_program
        || !input.verifier.executable
        || input.verifier.writable
        || input.verifier.signer
        || input.proof.account.owner != release.verifier_program
        || input.proof.account.writable
        || input.proof.account.signer
        || input.proof.bound_master != input.master.account.key
        || input.proof.bound_checkpoint != input.checkpoint.account.key
        || input.proof.bound_lane != input.lane.account.key
    {
        return Err(CallerError::WrongAccount);
    }
    Ok(())
}

fn authenticate_distinct_cpi_accounts(input: &CallerInput) -> Result<(), CallerError> {
    let proof = input.proof.account.key;
    let master = input.master.account.key;
    let checkpoint = input.checkpoint.account.key;
    let lane = input.lane.account.key;
    let registry = input.registry.account.key;
    let entry = input.entry.account.key;
    if proof == master
        || proof == checkpoint
        || proof == lane
        || proof == registry
        || proof == entry
        || master == checkpoint
        || master == lane
        || master == registry
        || master == entry
        || checkpoint == lane
        || checkpoint == registry
        || checkpoint == entry
        || lane == registry
        || lane == entry
        || registry == entry
    {
        return Err(CallerError::WrongAccount);
    }
    Ok(())
}

pub fn authenticate_accounts_and_release(input: &CallerInput) -> Result<(), CallerError> {
    authenticate_request(input)?;
    authenticate_pool_accounts(input)?;
    authenticate_registry(input)?;
    authenticate_selected_verifier(input)?;
    authenticate_distinct_cpi_accounts(input)?;
    Ok(())
}

pub fn select_history_route(
    input: &CallerInput,
    next_sequence: u64,
) -> Result<HistoryWrite, CallerError> {
    if !input.current_page.canonical
        || input.current_page.account.owner != input.release.pool_program
        || !input.current_page.account.writable
        || input.current_page.account.signer
        || input.current_page.pool_lane != input.lane.account.key
        || input.current_page.filled > ROOT_HISTORY_CAPACITY
    {
        return Err(CallerError::WrongHistory);
    }
    let destination_page = next_sequence / u64::from(ROOT_HISTORY_CAPACITY);
    if destination_page == input.current_page.page_number {
        if input.current_page.filled == ROOT_HISTORY_CAPACITY {
            return Err(CallerError::WrongHistory);
        }
        Ok(HistoryWrite {
            route: PageRoute::SamePage,
            page_number: destination_page,
            first_sequence: next_sequence,
            root: 0,
        })
    } else if destination_page == input.current_page.page_number.wrapping_add(1)
        && input.rollover_page.page_number == destination_page
        && input.rollover_page.pool_lane == input.lane.account.key
        && input.rollover_page.account.owner == input.release.pool_program
        && input.rollover_page.account.writable
        && !input.rollover_page.account.signer
        && input.rollover_page.zeroed
    {
        Ok(HistoryWrite {
            route: PageRoute::Rollover,
            page_number: destination_page,
            first_sequence: next_sequence,
            root: 0,
        })
    } else {
        Err(CallerError::WrongHistory)
    }
}

pub fn authenticate_result(input: &CallerInput) -> Result<ReturnedResult, CallerError> {
    if !input.runtime.verifier_cpi_succeeded {
        return Err(CallerError::VerifierCpi);
    }
    if input.verifier_return.program != input.release.verifier_program
        || input.verifier_return.encoded_len != ASR8_BYTES
        || !input.verifier_return.canonical
    {
        return Err(CallerError::VerifierReturn);
    }
    let result = match input.verifier_return.decoded {
        Some(result) => result,
        None => return Err(CallerError::VerifierReturn),
    };
    if result.transition_kind != input.request.payment_kind
        || result.master_account != input.master.account.key
        || result.selected_lane_account != input.lane.account.key
        || result.output_lane != input.request.output_lane
        || result.nullifier != input.request.nullifier
        || input.lane.next_pair_index.checked_add(1) != Some(result.next_pair_index)
        || !result.next_frontier_canonical
    {
        return Err(CallerError::ResultBinding);
    }
    Ok(result)
}

fn exact_marker(input: &CallerInput) -> Result<MarkerImage, CallerError> {
    if !input.marker.pda_exact
        || !input.marker.program_owned_zeroed
        || !input.marker.account.writable
        || input.marker.account.signer
        || input.marker.account.owner != input.release.pool_program
    {
        return Err(CallerError::SpentNullifier);
    }
    Ok(MarkerImage {
        master: input.master.account.key,
        deployment_domain: input.master.deployment_domain,
        nullifier: input.request.nullifier,
        checkpoint_sequence: input.checkpoint.sequence,
        checkpoint_root: input.checkpoint.global_root,
        profile: input.request.profile,
        release: input.request.release,
    })
}

fn apply_withdrawal(input: &CallerInput, state: &mut PoolImages) -> Result<(), CallerError> {
    let tokens = input.tokens;
    let amount = input.request.withdrawal_amount;
    if !tokens.exact_five_accounts
        || !tokens.token_program_exact
        || !tokens.mint_exact
        || !tokens.vault_authority_exact
        || !tokens.destination_exact
        || input.request.withdrawal_destination == 0
    {
        return Err(CallerError::WithdrawalAccounts);
    }
    if !input.runtime.withdrawal_cpi_succeeded {
        return Err(CallerError::WithdrawalCpi);
    }
    if tokens.vault_before.checked_sub(amount) != Some(tokens.vault_after)
        || tokens.destination_before.checked_add(amount) != Some(tokens.destination_after)
    {
        return Err(CallerError::WithdrawalDelta);
    }
    state.vault_balance = tokens.vault_after;
    state.destination_balance = tokens.destination_after;
    Ok(())
}

pub fn prepare_terminal(input: &CallerInput) -> Result<PreparedTerminal, CallerError> {
    authenticate_accounts_and_release(&input)?;
    let marker = exact_marker(&input)?;
    let result = authenticate_result(&input)?;
    let mut history = select_history_route(&input, result.next_pair_index)?;
    history.first_sequence = result.next_pair_index;
    history.root = result.next_root;
    Ok(PreparedTerminal {
        marker,
        result,
        history,
    })
}

fn finalize_prepared_terminal(
    input: CallerInput,
    mut after: PoolImages,
    prepared: PreparedTerminal,
) -> AcceptedExecution {
    let marker = prepared.marker;
    let result = prepared.result;
    let history = prepared.history;
    after.lane = LaneState {
        account: input.lane.account,
        master: input.lane.master,
        lane_id: input.lane.lane_id,
        next_pair_index: result.next_pair_index,
        root: result.next_root,
        frontier: result.next_frontier,
        invariant_capability: input.lane.invariant_capability,
    };
    match history.route {
        PageRoute::SamePage => {
            after.current_page_last_root = result.next_root;
            after.current_page_filled = input.current_page.filled.wrapping_add(1);
        }
        PageRoute::Rollover => {
            after.rollover_page_last_root = result.next_root;
            after.rollover_page_filled = 1;
        }
    }
    after.marker = Some(marker);
    after.returned_result = Some(result);
    after.returned_result_bytes_id = Some(input.verifier_return.exact_bytes_id);
    let certificate = AcceptanceCertificate {
        path_kind: input.request.payment_kind,
        page_route: history.route,
        cpi_accounts: exact_cpi_accounts(&input),
        result,
        result_bytes_id: input.verifier_return.exact_bytes_id,
        history_write: history,
        marker,
    };
    AcceptedExecution {
        state: after,
        certificate,
    }
}

fn apply_transfer_prepared(
    input: CallerInput,
    before: PoolImages,
    prepared: PreparedTerminal,
) -> Result<AcceptedExecution, CallerError> {
    Ok(finalize_prepared_terminal(input, before, prepared))
}

fn apply_withdrawal_prepared(
    input: CallerInput,
    before: PoolImages,
    prepared: PreparedTerminal,
) -> Result<AcceptedExecution, CallerError> {
    let mut after = before;
    apply_withdrawal(&input, &mut after)?;
    Ok(finalize_prepared_terminal(input, after, prepared))
}

pub fn apply_prepared_terminal(
    input: CallerInput,
    before: PoolImages,
    prepared: PreparedTerminal,
) -> Result<AcceptedExecution, CallerError> {
    if !input.runtime.lane_borrow_succeeded
        || !input.runtime.page_borrow_succeeded
        || !input.runtime.marker_borrow_succeeded
    {
        return Err(CallerError::Borrow);
    }
    match input.request.payment_kind {
        PaymentKind::PrivateTransfer => apply_transfer_prepared(input, before, prepared),
        PaymentKind::Withdrawal => apply_withdrawal_prepared(input, before, prepared),
    }
}

pub fn execute_terminal_caller(
    input: CallerInput,
    before: PoolImages,
) -> Result<AcceptedExecution, CallerError> {
    let prepared = prepare_terminal(&input)?;
    apply_prepared_terminal(input, before, prepared)
}

/// Solana commits all account/CPI effects only when the instruction returns
/// success. This wrapper makes that runtime boundary explicit: every rejected
/// caller run has the byte-identical pre-state, including a withdrawal whose
/// token CPI succeeded but whose post-CPI delta check failed.
pub fn execute_atomic_transaction(input: CallerInput, before: PoolImages) -> TransactionOutcome {
    match execute_terminal_caller(input, before) {
        Ok(accepted) => TransactionOutcome {
            committed: true,
            state: accepted.state,
            certificate: Some(accepted.certificate),
            error: None,
        },
        Err(error) => TransactionOutcome {
            committed: false,
            state: before,
            certificate: None,
            error: Some(error),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn account(key: u64, owner: u64, writable: bool, executable: bool) -> AccountView {
        AccountView {
            key,
            owner,
            writable,
            signer: false,
            executable,
        }
    }

    fn fixture(kind: PaymentKind, route: PageRoute) -> (CallerInput, PoolImages) {
        let release = SelectedRelease {
            pool_program: 10,
            verifier_program: 20,
            registry_program: 30,
            loader_program: 40,
            registry_programdata: 41,
            verifier_programdata: 42,
            profile: 50,
            release: 60,
            policy_binding: 70,
        };
        let source_index = match route {
            PageRoute::SamePage => 12,
            PageRoute::Rollover => 255,
        };
        let next_index = source_index + 1;
        let lane_account = account(103, release.pool_program, true, false);
        let master_account = account(101, release.pool_program, false, false);
        let checkpoint_account = account(102, release.pool_program, false, false);
        let result = ReturnedResult {
            transition_kind: kind,
            master_account: master_account.key,
            selected_lane_account: lane_account.key,
            output_lane: 5,
            nullifier: 900,
            next_pair_index: next_index,
            next_root: 1_001,
            next_frontier: 2_001,
            next_frontier_canonical: true,
        };
        let input = CallerInput {
            release,
            request: Request {
                encoded_len: ASQ8_BYTES,
                canonical: true,
                pool_program: release.pool_program,
                master_account: master_account.key,
                checkpoint_account: checkpoint_account.key,
                selected_lane_account: lane_account.key,
                profile: release.profile,
                release: release.release,
                nullifier: 900,
                output_lane: 5,
                payment_kind: kind,
                withdrawal_amount: if kind == PaymentKind::Withdrawal {
                    25
                } else {
                    0
                },
                withdrawal_destination: if kind == PaymentKind::Withdrawal {
                    800
                } else {
                    0
                },
            },
            master: MasterState {
                account: master_account,
                deployment_domain: 77,
                policy: VerifierPolicy {
                    registry_program: release.registry_program,
                    registry_authority: 0,
                    policy_binding: release.policy_binding,
                    immutable_registry: true,
                    immutable_deployment: true,
                },
            },
            checkpoint: CheckpointState {
                account: checkpoint_account,
                master: master_account.key,
                sequence: 8,
                global_root: 3_000,
            },
            lane: LaneState {
                account: lane_account,
                master: master_account.key,
                lane_id: 5,
                next_pair_index: source_index,
                root: 1_000,
                frontier: 2_000,
                invariant_capability: true,
            },
            registry: RegistryState {
                account: account(104, release.registry_program, false, false),
                canonical_v2: true,
                pda_exact: true,
                pool: master_account.key,
                authority: 0,
                policy_binding: release.policy_binding,
                immutable: true,
                paused: false,
                registry_program: release.registry_program,
                loader_program: release.loader_program,
                programdata_address: release.registry_programdata,
                programdata_pda_exact: true,
                executable_hash: 3_001,
            },
            entry: RegistryEntry {
                account: account(105, release.registry_program, false, false),
                canonical_v2: true,
                pda_exact: true,
                pool: master_account.key,
                verifier_program: release.verifier_program,
                profile: release.profile,
                release: release.release,
                loader_program: release.loader_program,
                programdata_address: release.verifier_programdata,
                programdata_pda_exact: true,
                executable_hash: 3_002,
                expected_upgrade_authority: 0,
                statement_version: STATEMENT_VERSION,
                activation_slot: 5,
                retirement_slot: 0,
                enabled: true,
            },
            verifier: account(
                release.verifier_program,
                release.loader_program,
                false,
                true,
            ),
            proof: ProofState {
                account: account(106, release.verifier_program, false, false),
                bound_master: master_account.key,
                bound_checkpoint: checkpoint_account.key,
                bound_lane: lane_account.key,
            },
            current_page: PageInput {
                account: account(107, release.pool_program, true, false),
                pool_lane: lane_account.key,
                page_number: 0,
                filled: match route {
                    PageRoute::SamePage => 13,
                    PageRoute::Rollover => ROOT_HISTORY_CAPACITY,
                },
                canonical: true,
                zeroed: false,
            },
            rollover_page: PageInput {
                account: account(108, release.pool_program, true, false),
                pool_lane: lane_account.key,
                page_number: 1,
                filled: 0,
                canonical: true,
                zeroed: true,
            },
            marker: MarkerInput {
                account: account(109, release.pool_program, true, false),
                pda_exact: true,
                program_owned_zeroed: true,
            },
            tokens: TokenInput {
                exact_five_accounts: true,
                token_program_exact: true,
                mint_exact: true,
                vault_authority_exact: true,
                destination_exact: true,
                vault_before: 1_000,
                destination_before: 100,
                vault_after: 975,
                destination_after: 125,
            },
            current_slot: 10,
            verifier_return: VerifierReturn {
                program: release.verifier_program,
                encoded_len: ASR8_BYTES,
                canonical: true,
                exact_bytes_id: 4_001,
                decoded: Some(result),
            },
            runtime: RuntimeOutcomes {
                verifier_cpi_succeeded: true,
                lane_borrow_succeeded: true,
                page_borrow_succeeded: true,
                marker_borrow_succeeded: true,
                withdrawal_cpi_succeeded: true,
            },
        };
        let before = PoolImages {
            lane: input.lane,
            current_page_last_root: input.lane.root,
            current_page_filled: input.current_page.filled,
            rollover_page_last_root: 0,
            rollover_page_filled: 0,
            marker: None,
            vault_balance: input.tokens.vault_before,
            destination_balance: input.tokens.destination_before,
            returned_result: None,
            returned_result_bytes_id: None,
            unrelated: 42,
        };
        (input, before)
    }

    fn assert_success(kind: PaymentKind, route: PageRoute) {
        let (input, before) = fixture(kind, route);
        let outcome = execute_atomic_transaction(input, before);
        assert!(outcome.committed);
        assert_eq!(outcome.error, None);
        let certificate = outcome.certificate.expect("accepted certificate");
        let result = input.verifier_return.decoded.expect("fixture result");
        assert_eq!(certificate.path_kind, kind);
        assert_eq!(certificate.page_route, route);
        assert_eq!(certificate.cpi_accounts, exact_cpi_accounts(&input));
        assert_eq!(certificate.result, result);
        assert_eq!(outcome.state.lane.next_pair_index, result.next_pair_index);
        assert_eq!(outcome.state.lane.root, result.next_root);
        assert_eq!(outcome.state.lane.frontier, result.next_frontier);
        assert_eq!(outcome.state.marker, Some(certificate.marker));
        assert_eq!(outcome.state.returned_result, Some(result));
        assert_eq!(certificate.result_bytes_id, input.verifier_return.exact_bytes_id);
        assert_eq!(
            outcome.state.returned_result_bytes_id,
            Some(input.verifier_return.exact_bytes_id)
        );
        assert_eq!(outcome.state.unrelated, before.unrelated);
        match (kind, route) {
            (PaymentKind::PrivateTransfer, PageRoute::SamePage) => {
                assert_eq!(outcome.state.vault_balance, before.vault_balance);
                assert_eq!(
                    outcome.state.current_page_filled,
                    before.current_page_filled + 1
                );
            }
            (PaymentKind::PrivateTransfer, PageRoute::Rollover) => {
                assert_eq!(outcome.state.vault_balance, before.vault_balance);
                assert_eq!(outcome.state.rollover_page_filled, 1);
            }
            (PaymentKind::Withdrawal, PageRoute::SamePage) => {
                assert_eq!(outcome.state.vault_balance, input.tokens.vault_after);
                assert_eq!(
                    outcome.state.destination_balance,
                    input.tokens.destination_after
                );
                assert_eq!(
                    outcome.state.current_page_filled,
                    before.current_page_filled + 1
                );
            }
            (PaymentKind::Withdrawal, PageRoute::Rollover) => {
                assert_eq!(outcome.state.vault_balance, input.tokens.vault_after);
                assert_eq!(
                    outcome.state.destination_balance,
                    input.tokens.destination_after
                );
                assert_eq!(outcome.state.rollover_page_filled, 1);
            }
        }
    }

    #[test]
    fn all_four_selected_paths_commit_exact_images() {
        assert_success(PaymentKind::PrivateTransfer, PageRoute::SamePage);
        assert_success(PaymentKind::PrivateTransfer, PageRoute::Rollover);
        assert_success(PaymentKind::Withdrawal, PageRoute::SamePage);
        assert_success(PaymentKind::Withdrawal, PageRoute::Rollover);
    }

    #[test]
    fn every_runtime_failure_rolls_back_byte_exactly() {
        for failure in 0..8 {
            let (mut input, before) = fixture(PaymentKind::Withdrawal, PageRoute::Rollover);
            match failure {
                0 => input.runtime.verifier_cpi_succeeded = false,
                1 => input.runtime.lane_borrow_succeeded = false,
                2 => input.runtime.page_borrow_succeeded = false,
                3 => input.runtime.marker_borrow_succeeded = false,
                4 => input.runtime.withdrawal_cpi_succeeded = false,
                5 => input.verifier_return.program += 1,
                6 => input.tokens.vault_after += 1,
                7 => input.marker.program_owned_zeroed = false,
                _ => unreachable!(),
            }
            let outcome = execute_atomic_transaction(input, before);
            assert!(!outcome.committed);
            assert_eq!(outcome.state, before);
            assert_eq!(outcome.certificate, None);
            assert!(outcome.error.is_some());
        }
    }

    #[test]
    fn wrong_release_and_bad_asr8_are_rejected_atomically() {
        for failure in 0..4 {
            let (mut input, before) = fixture(PaymentKind::PrivateTransfer, PageRoute::SamePage);
            match failure {
                0 => input
                    .verifier_return
                    .decoded
                    .as_mut()
                    .unwrap()
                    .next_pair_index += 1,
                1 => input.entry.release += 1,
                2 => input.verifier_return.encoded_len -= 1,
                3 => input.lane.invariant_capability = false,
                _ => unreachable!(),
            }
            let outcome = execute_atomic_transaction(input, before);
            assert!(!outcome.committed);
            assert_eq!(outcome.state, before);
        }
    }

    #[test]
    fn every_registry_v2_deployment_certificate_binding_fails_closed() {
        for failure in 0..18 {
            let (mut input, before) = fixture(PaymentKind::PrivateTransfer, PageRoute::SamePage);
            match failure {
                0 => input.master.policy.registry_authority = 1,
                1 => input.master.policy.immutable_registry = false,
                2 => input.master.policy.immutable_deployment = false,
                3 => input.registry.canonical_v2 = false,
                4 => input.registry.pda_exact = false,
                5 => input.registry.authority = 1,
                6 => input.registry.registry_program += 1,
                7 => input.registry.loader_program += 1,
                8 => input.registry.programdata_address += 1,
                9 => input.registry.programdata_pda_exact = false,
                10 => input.registry.executable_hash = 0,
                11 => input.entry.canonical_v2 = false,
                12 => input.entry.pda_exact = false,
                13 => input.entry.loader_program += 1,
                14 => input.entry.programdata_address += 1,
                15 => input.entry.programdata_pda_exact = false,
                16 => input.entry.executable_hash = 0,
                17 => input.entry.expected_upgrade_authority = 1,
                _ => unreachable!(),
            }
            let outcome = execute_atomic_transaction(input, before);
            assert!(!outcome.committed);
            assert_eq!(outcome.state, before);
            assert_eq!(outcome.certificate, None);
            assert_eq!(outcome.error, Some(CallerError::WrongRegistry));
        }
    }

    #[test]
    fn asq8_and_asr8_canonicality_and_exact_return_bytes_fail_closed() {
        for failure in 0..3 {
            let (mut input, before) = fixture(PaymentKind::PrivateTransfer, PageRoute::SamePage);
            match failure {
                0 => input.request.canonical = false,
                1 => input.verifier_return.canonical = false,
                2 => input.verifier_return.exact_bytes_id = 0,
                _ => unreachable!(),
            }
            if failure == 2 {
                // A zero identifier is not inherently malformed; it is used
                // here to prove that the caller copies the exact authenticated
                // bytes identity rather than synthesizing a new result image.
                let outcome = execute_atomic_transaction(input, before);
                assert!(outcome.committed);
                assert_eq!(outcome.state.returned_result_bytes_id, Some(0));
                assert_eq!(outcome.certificate.unwrap().result_bytes_id, 0);
            } else {
                let outcome = execute_atomic_transaction(input, before);
                assert!(!outcome.committed);
                assert_eq!(outcome.state, before);
            }
        }
    }
}
