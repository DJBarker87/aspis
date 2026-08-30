#![no_std]

pub const LEGACY_TOKEN_PROGRAM_ID: u64 = 1;
pub const TOKEN_2022_PROGRAM_ID: u64 = 2;
pub const BPF_LOADER_ID: u64 = 10;
pub const BPF_UPGRADEABLE_LOADER_ID: u64 = 11;
pub const LOADER_V4_ID: u64 = 12;
pub const SYSTEM_PROGRAM_ID: u64 = 20;
pub const LEGACY_MINT_BYTES: u16 = 82;
pub const LEGACY_TOKEN_ACCOUNT_BYTES: u16 = 165;
pub const VALUE_LIMIT: u64 = 1_073_741_824;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CustodyError {
    DuplicateAccount,
    InvalidAmount,
    InvalidTokenProgram,
    InvalidMint,
    InvalidSourceAuthority,
    InvalidTokenAccount,
    InvalidVaultAddress,
    InvalidVaultAuthority,
    UnsupportedTokenConfiguration,
    ArithmeticOverflow,
    InsufficientFunds,
    VerifierCpi,
    TokenCpi,
    TokenDelta,
    PoolWrite,
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
pub struct MintView {
    pub account: AccountView,
    pub data_len: u16,
    pub initialized: bool,
    pub option_tags_canonical: bool,
    pub decimals: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TokenAccountView {
    pub account: AccountView,
    pub data_len: u16,
    pub mint: u64,
    pub authority: u64,
    pub amount: u64,
    pub initialized: bool,
    pub option_tags_canonical: bool,
    pub has_delegate: bool,
    pub is_native: bool,
    pub delegated_amount: u64,
    pub has_close_authority: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CustodyState {
    pub source_balance: u64,
    pub vault_balance: u64,
    pub destination_balance: u64,
    pub lane_image: u64,
    pub history_image: u64,
    pub marker_consumed: bool,
    pub unrelated: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeOutcomes {
    pub verifier_cpi_succeeds: bool,
    pub token_cpi_succeeds: bool,
    pub observed_source_after: u64,
    pub observed_vault_after: u64,
    pub observed_destination_after: u64,
    pub pool_write_succeeds: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositInput {
    pub program_id: u64,
    pub pool: u64,
    pub identity_token_program: u64,
    pub identity_mint: u64,
    pub expected_vault: u64,
    pub expected_vault_authority: u64,
    pub exact_account_count_and_unique: bool,
    pub amount: u64,
    pub token_program: AccountView,
    pub mint: MintView,
    pub source: TokenAccountView,
    pub source_authority: AccountView,
    pub vault: TokenAccountView,
    pub next_lane_image: u64,
    pub next_history_image: u64,
    pub runtime: RuntimeOutcomes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawalInput {
    pub program_id: u64,
    pub pool: u64,
    pub identity_token_program: u64,
    pub identity_mint: u64,
    pub expected_vault: u64,
    pub expected_vault_authority: u64,
    pub requested_destination: u64,
    pub exact_account_count_and_unique: bool,
    pub amount: u64,
    pub token_program: AccountView,
    pub mint: MintView,
    pub vault: TokenAccountView,
    pub destination: TokenAccountView,
    pub vault_authority: AccountView,
    /// The seam already closed by the selected one-terminal caller and marker
    /// source bridges.  It is consumed before verifier execution and is not a
    /// substitute for any custody check below.
    pub terminal_prefix_authenticated: bool,
    pub next_lane_image: u64,
    pub next_history_image: u64,
    pub runtime: RuntimeOutcomes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TransferCheckedPlan {
    pub program_id: u64,
    pub source: u64,
    pub mint: u64,
    pub destination: u64,
    pub authority: u64,
    pub amount: u64,
    pub decimals: u8,
    pub pda_signed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositPlan {
    pub instruction: TransferCheckedPlan,
    pub source_before: u64,
    pub source_after: u64,
    pub vault_before: u64,
    pub vault_after: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawalPlan {
    pub instruction: TransferCheckedPlan,
    pub vault_before: u64,
    pub vault_after: u64,
    pub destination_before: u64,
    pub destination_after: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CallTrace {
    pub plan_step: u8,
    pub verifier_step: u8,
    pub token_cpi_attempt_step: u8,
    pub token_cpi_success_step: u8,
    pub delta_step: u8,
    pub pool_write_step: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositCertificate {
    pub plan: DepositPlan,
    pub trace: CallTrace,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawalCertificate {
    pub plan: WithdrawalPlan,
    pub trace: CallTrace,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CustodyCertificate {
    Deposit(DepositCertificate),
    Withdrawal(WithdrawalCertificate),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CustodyRequest {
    Deposit(DepositInput),
    Withdrawal(WithdrawalInput),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CustodyOutcome {
    pub committed: bool,
    pub state: CustodyState,
    pub certificate: Option<CustodyCertificate>,
    pub error: Option<CustodyError>,
    pub trace: CallTrace,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ExecutionFailure {
    error: CustodyError,
    trace: CallTrace,
}

fn empty_trace() -> CallTrace {
    CallTrace {
        plan_step: 0,
        verifier_step: 0,
        token_cpi_attempt_step: 0,
        token_cpi_success_step: 0,
        delta_step: 0,
        pool_write_step: 0,
    }
}

fn supported_loader(owner: u64) -> bool {
    owner == BPF_LOADER_ID || owner == BPF_UPGRADEABLE_LOADER_ID || owner == LOADER_V4_ID
}

fn authenticate_token_program(
    identity_token_program: u64,
    token_program: AccountView,
) -> Result<(), CustodyError> {
    if identity_token_program != LEGACY_TOKEN_PROGRAM_ID
        || token_program.key != LEGACY_TOKEN_PROGRAM_ID
        || !token_program.executable
        || token_program.signer
        || token_program.writable
        || !supported_loader(token_program.owner)
    {
        return Err(CustodyError::InvalidTokenProgram);
    }
    Ok(())
}

fn authenticate_mint(expected_mint: u64, mint: MintView) -> Result<(), CustodyError> {
    if mint.account.key != expected_mint
        || mint.account.owner != LEGACY_TOKEN_PROGRAM_ID
        || mint.account.executable
        || mint.account.signer
        || mint.account.writable
        || mint.data_len != LEGACY_MINT_BYTES
        || !mint.initialized
        || !mint.option_tags_canonical
    {
        return Err(CustodyError::InvalidMint);
    }
    Ok(())
}

fn authenticate_token_account(
    account: TokenAccountView,
    writable: bool,
) -> Result<(), CustodyError> {
    if account.account.owner != LEGACY_TOKEN_PROGRAM_ID
        || account.account.executable
        || account.account.signer
        || account.account.writable != writable
        || account.data_len != LEGACY_TOKEN_ACCOUNT_BYTES
        || !account.initialized
        || !account.option_tags_canonical
    {
        return Err(CustodyError::InvalidTokenAccount);
    }
    Ok(())
}

fn plan_deposit(input: DepositInput) -> Result<DepositPlan, CustodyError> {
    if !input.exact_account_count_and_unique {
        return Err(CustodyError::DuplicateAccount);
    }
    if input.amount == 0 || input.amount >= VALUE_LIMIT {
        return Err(CustodyError::InvalidAmount);
    }
    authenticate_token_program(input.identity_token_program, input.token_program)?;
    authenticate_mint(input.identity_mint, input.mint)?;
    authenticate_token_account(input.source, true)?;
    authenticate_token_account(input.vault, true)?;
    if !input.source_authority.signer
        || input.source_authority.writable
        || input.source_authority.executable
    {
        return Err(CustodyError::InvalidSourceAuthority);
    }
    if input.source.mint != input.identity_mint
        || input.vault.mint != input.identity_mint
        || input.source.authority != input.source_authority.key
    {
        return Err(CustodyError::InvalidTokenAccount);
    }
    if input.vault.account.key != input.expected_vault {
        return Err(CustodyError::InvalidVaultAddress);
    }
    if input.vault.authority != input.expected_vault_authority {
        return Err(CustodyError::InvalidVaultAuthority);
    }
    if input.vault.has_delegate
        || input.vault.is_native
        || input.vault.delegated_amount != 0
        || input.vault.has_close_authority
    {
        return Err(CustodyError::UnsupportedTokenConfiguration);
    }
    let source_after = input
        .source
        .amount
        .checked_sub(input.amount)
        .ok_or(CustodyError::InsufficientFunds)?;
    let vault_after = input
        .vault
        .amount
        .checked_add(input.amount)
        .ok_or(CustodyError::ArithmeticOverflow)?;
    Ok(DepositPlan {
        instruction: TransferCheckedPlan {
            program_id: LEGACY_TOKEN_PROGRAM_ID,
            source: input.source.account.key,
            mint: input.mint.account.key,
            destination: input.vault.account.key,
            authority: input.source_authority.key,
            amount: input.amount,
            decimals: input.mint.decimals,
            pda_signed: false,
        },
        source_before: input.source.amount,
        source_after,
        vault_before: input.vault.amount,
        vault_after,
    })
}

fn plan_withdrawal(input: WithdrawalInput) -> Result<WithdrawalPlan, CustodyError> {
    if !input.terminal_prefix_authenticated || !input.exact_account_count_and_unique {
        return Err(CustodyError::DuplicateAccount);
    }
    if input.amount == 0 || input.amount >= VALUE_LIMIT {
        return Err(CustodyError::InvalidAmount);
    }
    authenticate_token_program(input.identity_token_program, input.token_program)?;
    authenticate_mint(input.identity_mint, input.mint)?;
    authenticate_token_account(input.vault, true)?;
    authenticate_token_account(input.destination, true)?;
    if input.vault_authority.key != input.expected_vault_authority
        || input.vault_authority.owner != SYSTEM_PROGRAM_ID
        || input.vault_authority.executable
        || input.vault_authority.signer
        || input.vault_authority.writable
    {
        return Err(CustodyError::InvalidVaultAuthority);
    }
    if input.destination.account.key != input.requested_destination {
        return Err(CustodyError::InvalidTokenAccount);
    }
    if input.vault.account.key != input.expected_vault {
        return Err(CustodyError::InvalidVaultAddress);
    }
    if input.vault.mint != input.identity_mint
        || input.destination.mint != input.identity_mint
        || input.vault.authority != input.expected_vault_authority
    {
        return Err(CustodyError::InvalidTokenAccount);
    }
    if input.vault.has_delegate
        || input.vault.is_native
        || input.vault.delegated_amount != 0
        || input.vault.has_close_authority
        || input.destination.is_native
    {
        return Err(CustodyError::UnsupportedTokenConfiguration);
    }
    let vault_after = input
        .vault
        .amount
        .checked_sub(input.amount)
        .ok_or(CustodyError::InsufficientFunds)?;
    let destination_after = input
        .destination
        .amount
        .checked_add(input.amount)
        .ok_or(CustodyError::ArithmeticOverflow)?;
    Ok(WithdrawalPlan {
        instruction: TransferCheckedPlan {
            program_id: LEGACY_TOKEN_PROGRAM_ID,
            source: input.vault.account.key,
            mint: input.mint.account.key,
            destination: input.destination.account.key,
            authority: input.vault_authority.key,
            amount: input.amount,
            decimals: input.mint.decimals,
            pda_signed: true,
        },
        vault_before: input.vault.amount,
        vault_after,
        destination_before: input.destination.amount,
        destination_after,
    })
}

fn execute_deposit(
    input: DepositInput,
    before: CustodyState,
) -> Result<(CustodyState, DepositCertificate), ExecutionFailure> {
    let mut trace = empty_trace();
    let plan = match plan_deposit(input) {
        Ok(plan) => plan,
        Err(error) => return Err(ExecutionFailure { error, trace }),
    };
    trace.plan_step = 1;
    trace.token_cpi_attempt_step = 2;
    if !input.runtime.token_cpi_succeeds {
        return Err(ExecutionFailure {
            error: CustodyError::TokenCpi,
            trace,
        });
    }
    trace.token_cpi_success_step = 2;
    let mut after = before;
    after.source_balance = input.runtime.observed_source_after;
    after.vault_balance = input.runtime.observed_vault_after;
    if input.runtime.observed_source_after != plan.source_after
        || input.runtime.observed_vault_after != plan.vault_after
    {
        return Err(ExecutionFailure {
            error: CustodyError::TokenDelta,
            trace,
        });
    }
    trace.delta_step = 3;
    if !input.runtime.pool_write_succeeds {
        return Err(ExecutionFailure {
            error: CustodyError::PoolWrite,
            trace,
        });
    }
    after.lane_image = input.next_lane_image;
    after.history_image = input.next_history_image;
    trace.pool_write_step = 4;
    Ok((after, DepositCertificate { plan, trace }))
}

fn execute_withdrawal(
    input: WithdrawalInput,
    before: CustodyState,
) -> Result<(CustodyState, WithdrawalCertificate), ExecutionFailure> {
    let mut trace = empty_trace();
    let plan = match plan_withdrawal(input) {
        Ok(plan) => plan,
        Err(error) => return Err(ExecutionFailure { error, trace }),
    };
    trace.plan_step = 1;
    if !input.runtime.verifier_cpi_succeeds {
        return Err(ExecutionFailure {
            error: CustodyError::VerifierCpi,
            trace,
        });
    }
    trace.verifier_step = 2;
    trace.token_cpi_attempt_step = 3;
    if !input.runtime.token_cpi_succeeds {
        return Err(ExecutionFailure {
            error: CustodyError::TokenCpi,
            trace,
        });
    }
    trace.token_cpi_success_step = 3;
    let mut after = before;
    after.vault_balance = input.runtime.observed_vault_after;
    after.destination_balance = input.runtime.observed_destination_after;
    if input.runtime.observed_vault_after != plan.vault_after
        || input.runtime.observed_destination_after != plan.destination_after
    {
        return Err(ExecutionFailure {
            error: CustodyError::TokenDelta,
            trace,
        });
    }
    trace.delta_step = 4;
    if !input.runtime.pool_write_succeeds {
        return Err(ExecutionFailure {
            error: CustodyError::PoolWrite,
            trace,
        });
    }
    after.lane_image = input.next_lane_image;
    after.history_image = input.next_history_image;
    after.marker_consumed = true;
    trace.pool_write_step = 5;
    Ok((after, WithdrawalCertificate { plan, trace }))
}

pub fn execute_atomic_custody(request: CustodyRequest, before: CustodyState) -> CustodyOutcome {
    match request {
        CustodyRequest::Deposit(input) => match execute_deposit(input, before) {
            Ok((state, certificate)) => CustodyOutcome {
                committed: true,
                state,
                certificate: Some(CustodyCertificate::Deposit(certificate)),
                error: None,
                trace: certificate.trace,
            },
            Err(failure) => CustodyOutcome {
                committed: false,
                state: before,
                certificate: None,
                error: Some(failure.error),
                trace: failure.trace,
            },
        },
        CustodyRequest::Withdrawal(input) => match execute_withdrawal(input, before) {
            Ok((state, certificate)) => CustodyOutcome {
                committed: true,
                state,
                certificate: Some(CustodyCertificate::Withdrawal(certificate)),
                error: None,
                trace: certificate.trace,
            },
            Err(failure) => CustodyOutcome {
                committed: false,
                state: before,
                certificate: None,
                error: Some(failure.error),
                trace: failure.trace,
            },
        },
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

    fn mint() -> MintView {
        MintView {
            account: account(100, LEGACY_TOKEN_PROGRAM_ID, false, false, false),
            data_len: LEGACY_MINT_BYTES,
            initialized: true,
            option_tags_canonical: true,
            decimals: 6,
        }
    }

    fn token(key: u64, authority: u64, amount: u64) -> TokenAccountView {
        TokenAccountView {
            account: account(key, LEGACY_TOKEN_PROGRAM_ID, true, false, false),
            data_len: LEGACY_TOKEN_ACCOUNT_BYTES,
            mint: 100,
            authority,
            amount,
            initialized: true,
            option_tags_canonical: true,
            has_delegate: false,
            is_native: false,
            delegated_amount: 0,
            has_close_authority: false,
        }
    }

    fn runtime(source: u64, vault: u64, destination: u64) -> RuntimeOutcomes {
        RuntimeOutcomes {
            verifier_cpi_succeeds: true,
            token_cpi_succeeds: true,
            observed_source_after: source,
            observed_vault_after: vault,
            observed_destination_after: destination,
            pool_write_succeeds: true,
        }
    }

    fn deposit(loader: u64) -> DepositInput {
        DepositInput {
            program_id: 900,
            pool: 901,
            identity_token_program: LEGACY_TOKEN_PROGRAM_ID,
            identity_mint: 100,
            expected_vault: 102,
            expected_vault_authority: 200,
            exact_account_count_and_unique: true,
            amount: 25,
            token_program: account(LEGACY_TOKEN_PROGRAM_ID, loader, false, false, true),
            mint: mint(),
            source: token(101, 201, 100),
            source_authority: account(201, 300, false, true, false),
            vault: token(102, 200, 40),
            next_lane_image: 501,
            next_history_image: 502,
            runtime: runtime(75, 65, 9),
        }
    }

    fn withdrawal(loader: u64) -> WithdrawalInput {
        WithdrawalInput {
            program_id: 900,
            pool: 901,
            identity_token_program: LEGACY_TOKEN_PROGRAM_ID,
            identity_mint: 100,
            expected_vault: 102,
            expected_vault_authority: 200,
            requested_destination: 103,
            exact_account_count_and_unique: true,
            amount: 25,
            token_program: account(LEGACY_TOKEN_PROGRAM_ID, loader, false, false, true),
            mint: mint(),
            vault: token(102, 200, 100),
            destination: token(103, 202, 10),
            vault_authority: account(200, SYSTEM_PROGRAM_ID, false, false, false),
            terminal_prefix_authenticated: true,
            next_lane_image: 601,
            next_history_image: 602,
            runtime: runtime(7, 75, 35),
        }
    }

    fn before() -> CustodyState {
        CustodyState {
            source_balance: 100,
            vault_balance: 40,
            destination_balance: 10,
            lane_image: 1,
            history_image: 2,
            marker_consumed: false,
            unrelated: 777,
        }
    }

    #[test]
    fn all_supported_loaders_accept_exact_deposit_and_withdrawal_effects() {
        for loader in [BPF_LOADER_ID, BPF_UPGRADEABLE_LOADER_ID, LOADER_V4_ID] {
            let deposit_out =
                execute_atomic_custody(CustodyRequest::Deposit(deposit(loader)), before());
            assert!(deposit_out.committed);
            assert_eq!(deposit_out.state.source_balance, 75);
            assert_eq!(deposit_out.state.vault_balance, 65);
            assert_eq!(deposit_out.state.lane_image, 501);
            assert_eq!(deposit_out.state.unrelated, 777);

            let mut withdrawal_before = before();
            withdrawal_before.vault_balance = 100;
            let withdrawal_out = execute_atomic_custody(
                CustodyRequest::Withdrawal(withdrawal(loader)),
                withdrawal_before,
            );
            assert!(withdrawal_out.committed);
            assert_eq!(withdrawal_out.state.vault_balance, 75);
            assert_eq!(withdrawal_out.state.destination_balance, 35);
            assert!(withdrawal_out.state.marker_consumed);
            assert_eq!(withdrawal_out.state.unrelated, 777);
        }
    }

    #[test]
    fn token_2022_program_and_account_shapes_fail_closed() {
        let mut bad_program = deposit(BPF_LOADER_ID);
        bad_program.token_program.key = TOKEN_2022_PROGRAM_ID;
        let before = before();
        let out = execute_atomic_custody(CustodyRequest::Deposit(bad_program), before);
        assert!(!out.committed);
        assert_eq!(out.state, before);
        assert_eq!(out.error, Some(CustodyError::InvalidTokenProgram));
        assert_eq!(out.trace.token_cpi_attempt_step, 0);

        let mut bad_account = withdrawal(BPF_LOADER_ID);
        bad_account.destination.account.owner = TOKEN_2022_PROGRAM_ID;
        let out = execute_atomic_custody(CustodyRequest::Withdrawal(bad_account), before);
        assert!(!out.committed);
        assert_eq!(out.state, before);
        assert_eq!(out.error, Some(CustodyError::InvalidTokenAccount));
        assert_eq!(out.trace.verifier_step, 0);
    }

    #[test]
    fn bad_loader_mint_vault_authority_and_destination_never_reach_cpi() {
        let before = before();
        let mut cases = [withdrawal(BPF_LOADER_ID); 5];
        cases[0].token_program.owner = 999;
        cases[1].mint.account.key = 999;
        cases[2].vault.account.key = 999;
        cases[3].vault_authority.key = 999;
        cases[4].destination.account.key = 999;
        for input in cases {
            let out = execute_atomic_custody(CustodyRequest::Withdrawal(input), before);
            assert!(!out.committed);
            assert_eq!(out.state, before);
            assert_eq!(out.trace.verifier_step, 0);
            assert_eq!(out.trace.token_cpi_attempt_step, 0);
        }
    }

    #[test]
    fn cpi_delta_and_late_write_failures_roll_back_exact_prestate() {
        let before = before();
        let mut cpi = deposit(BPF_LOADER_ID);
        cpi.runtime.token_cpi_succeeds = false;
        let out = execute_atomic_custody(CustodyRequest::Deposit(cpi), before);
        assert_eq!(out.state, before);
        assert_eq!(out.error, Some(CustodyError::TokenCpi));

        let mut delta = deposit(BPF_LOADER_ID);
        delta.runtime.observed_vault_after = 64;
        let out = execute_atomic_custody(CustodyRequest::Deposit(delta), before);
        assert_eq!(out.state, before);
        assert_eq!(out.error, Some(CustodyError::TokenDelta));
        assert_eq!(out.trace.token_cpi_success_step, 2);

        let mut withdrawal_before = before;
        withdrawal_before.vault_balance = 100;
        let mut late = withdrawal(BPF_LOADER_ID);
        late.runtime.pool_write_succeeds = false;
        let out = execute_atomic_custody(CustodyRequest::Withdrawal(late), withdrawal_before);
        assert_eq!(out.state, withdrawal_before);
        assert_eq!(out.error, Some(CustodyError::PoolWrite));
        assert_eq!(out.trace.token_cpi_success_step, 3);
        assert_eq!(out.trace.delta_step, 4);
        assert_eq!(out.trace.pool_write_step, 0);
    }
}
