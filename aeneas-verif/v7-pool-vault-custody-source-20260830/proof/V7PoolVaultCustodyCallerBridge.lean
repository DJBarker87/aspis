import V7PoolVaultCustodySourceBridge

/-!
# Literal Pool vault custody caller bridge

This file composes the accepted planner facts with the translated CPI/result
control flow and the public atomic caller.  The wrapper-level rejection theorem
records the Solana transaction property relied on by the production caller:
every modeled failure returns the exact prestate, including failures after a
successful token CPI but before the Pool writeback commits.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace V7PoolVaultCustodyGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

attribute [local simp] UScalar.eq_equiv

def ExactDepositExecution
    (input : DepositInput) (before after : CustodyState)
    (certificate : DepositCertificate) : Prop :=
  ExactDepositPlan input certificate.plan ∧
  input.runtime.token_cpi_succeeds = true ∧
  input.runtime.observed_source_after = certificate.plan.source_after ∧
  input.runtime.observed_vault_after = certificate.plan.vault_after ∧
  input.runtime.pool_write_succeeds = true ∧
  after = {
    before with
      source_balance := certificate.plan.source_after
      vault_balance := certificate.plan.vault_after
      lane_image := input.next_lane_image
      history_image := input.next_history_image
  } ∧
  certificate.trace = {
    plan_step := 1#u8
    verifier_step := 0#u8
    token_cpi_attempt_step := 2#u8
    token_cpi_success_step := 2#u8
    delta_step := 3#u8
    pool_write_step := 4#u8
  }

def ExactWithdrawalExecution
    (input : WithdrawalInput) (before after : CustodyState)
    (certificate : WithdrawalCertificate) : Prop :=
  ExactWithdrawalPlan input certificate.plan ∧
  input.runtime.verifier_cpi_succeeds = true ∧
  input.runtime.token_cpi_succeeds = true ∧
  input.runtime.observed_vault_after = certificate.plan.vault_after ∧
  input.runtime.observed_destination_after = certificate.plan.destination_after ∧
  input.runtime.pool_write_succeeds = true ∧
  after = {
    before with
      vault_balance := certificate.plan.vault_after
      destination_balance := certificate.plan.destination_after
      lane_image := input.next_lane_image
      history_image := input.next_history_image
      marker_consumed := true
  } ∧
  certificate.trace = {
    plan_step := 1#u8
    verifier_step := 2#u8
    token_cpi_attempt_step := 3#u8
    token_cpi_success_step := 3#u8
    delta_step := 4#u8
    pool_write_step := 5#u8
  }

theorem translated_deposit_execution_success_is_exact
    (input : DepositInput) (before after : CustodyState)
    (certificate : DepositCertificate)
    (run : execute_deposit input before =
      .ok (.Ok (after, certificate))) :
    ExactDepositExecution input before after certificate := by
  unfold execute_deposit empty_trace at run
  cases planRun : plan_deposit input with
  | fail error => simp [planRun] at run
  | div => simp [planRun] at run
  | ok planResult =>
      cases planResult with
      | Err error => simp [planRun] at run
      | Ok plan =>
          have planExact :=
            translated_deposit_plan_success_is_exact input plan planRun
          by_cases tokenCpi : input.runtime.token_cpi_succeeds = true
          · simp only [planRun, tokenCpi, if_pos] at run
            have sourceAfter :
                input.runtime.observed_source_after = plan.source_after := by
              by_contra different
              have castDifferent := u64_cast_ne_of_ne different
              simp [different, castDifferent] at run
            simp [sourceAfter] at run
            have vaultAfter :
                input.runtime.observed_vault_after = plan.vault_after := by
              by_contra different
              have castDifferent := u64_cast_ne_of_ne different
              simp [different, castDifferent] at run
            simp [vaultAfter] at run
            have poolWrite : input.runtime.pool_write_succeeds = true := by
              by_contra different
              have falseValue := Bool.eq_false_of_not_eq_true different
              simp [falseValue] at run
            simp [poolWrite] at run
            rcases run with ⟨afterEq, certificateEq⟩
            cases afterEq
            cases certificateEq
            simp [ExactDepositExecution, planExact, tokenCpi, sourceAfter,
              vaultAfter, poolWrite]
          · have falseValue := Bool.eq_false_of_not_eq_true tokenCpi
            simp [planRun, falseValue] at run

theorem translated_withdrawal_execution_success_is_exact
    (input : WithdrawalInput) (before after : CustodyState)
    (certificate : WithdrawalCertificate)
    (run : execute_withdrawal input before =
      .ok (.Ok (after, certificate))) :
    ExactWithdrawalExecution input before after certificate := by
  unfold execute_withdrawal empty_trace at run
  cases planRun : plan_withdrawal input with
  | fail error => simp [planRun] at run
  | div => simp [planRun] at run
  | ok planResult =>
      cases planResult with
      | Err error => simp [planRun] at run
      | Ok plan =>
          have planExact :=
            translated_withdrawal_plan_success_is_exact input plan planRun
          by_cases verifierCpi : input.runtime.verifier_cpi_succeeds = true
          · simp only [planRun, verifierCpi, if_pos] at run
            by_cases tokenCpi : input.runtime.token_cpi_succeeds = true
            · simp only [tokenCpi, if_pos] at run
              have vaultAfter :
                  input.runtime.observed_vault_after = plan.vault_after := by
                by_contra different
                have castDifferent := u64_cast_ne_of_ne different
                simp [different, castDifferent] at run
              simp [vaultAfter] at run
              have destinationAfter :
                  input.runtime.observed_destination_after =
                    plan.destination_after := by
                by_contra different
                have castDifferent := u64_cast_ne_of_ne different
                simp [different, castDifferent] at run
              simp [destinationAfter] at run
              have poolWrite : input.runtime.pool_write_succeeds = true := by
                by_contra different
                have falseValue := Bool.eq_false_of_not_eq_true different
                simp [falseValue] at run
              simp [poolWrite] at run
              rcases run with ⟨afterEq, certificateEq⟩
              cases afterEq
              cases certificateEq
              simp [ExactWithdrawalExecution, planExact, verifierCpi,
                tokenCpi, vaultAfter, destinationAfter, poolWrite]
            · have falseValue := Bool.eq_false_of_not_eq_true tokenCpi
              simp [falseValue] at run
          · have falseValue := Bool.eq_false_of_not_eq_true verifierCpi
            simp [planRun, falseValue] at run

def ExactCommittedDepositOutcome
    (input : DepositInput) (before : CustodyState)
    (outcome : CustodyOutcome) : Prop :=
  ∃ certificate,
    ExactDepositExecution input before outcome.state certificate ∧
    outcome.committed = true ∧
    outcome.certificate = some (CustodyCertificate.Deposit certificate) ∧
    outcome.error = none ∧
    outcome.trace = certificate.trace

def ExactCommittedWithdrawalOutcome
    (input : WithdrawalInput) (before : CustodyState)
    (outcome : CustodyOutcome) : Prop :=
  ∃ certificate,
    ExactWithdrawalExecution input before outcome.state certificate ∧
    outcome.committed = true ∧
    outcome.certificate = some (CustodyCertificate.Withdrawal certificate) ∧
    outcome.error = none ∧
    outcome.trace = certificate.trace

theorem translated_atomic_deposit_success_is_exact
    (input : DepositInput) (before : CustodyState) (outcome : CustodyOutcome)
    (run : execute_atomic_custody (.Deposit input) before = .ok outcome)
    (committed : outcome.committed = true) :
    ExactCommittedDepositOutcome input before outcome := by
  unfold execute_atomic_custody at run
  cases executionRun : execute_deposit input before with
  | fail error => simp [executionRun] at run
  | div => simp [executionRun] at run
  | ok executionResult =>
      cases executionResult with
      | Err failure =>
          simp [executionRun] at run
          subst outcome
          simp at committed
      | Ok pair =>
          cases pair with
          | mk after certificate =>
              have executionExact :=
                translated_deposit_execution_success_is_exact input before
                  after certificate executionRun
              simp [executionRun] at run
              subst outcome
              exact ⟨certificate, executionExact, rfl, rfl, rfl, rfl⟩

theorem translated_atomic_withdrawal_success_is_exact
    (input : WithdrawalInput) (before : CustodyState)
    (outcome : CustodyOutcome)
    (run : execute_atomic_custody (.Withdrawal input) before = .ok outcome)
    (committed : outcome.committed = true) :
    ExactCommittedWithdrawalOutcome input before outcome := by
  unfold execute_atomic_custody at run
  cases executionRun : execute_withdrawal input before with
  | fail error => simp [executionRun] at run
  | div => simp [executionRun] at run
  | ok executionResult =>
      cases executionResult with
      | Err failure =>
          simp [executionRun] at run
          subst outcome
          simp at committed
      | Ok pair =>
          cases pair with
          | mk after certificate =>
              have executionExact :=
                translated_withdrawal_execution_success_is_exact input before
                  after certificate executionRun
              simp [executionRun] at run
              subst outcome
              exact ⟨certificate, executionExact, rfl, rfl, rfl, rfl⟩

theorem translated_atomic_rejection_is_exact_prestate
    (request : CustodyRequest) (before : CustodyState)
    (outcome : CustodyOutcome)
    (run : execute_atomic_custody request before = .ok outcome)
    (rejected : outcome.committed = false) :
    outcome.state = before ∧
    outcome.certificate = none ∧
    outcome.error ≠ none := by
  cases request with
  | Deposit input =>
      unfold execute_atomic_custody at run
      cases executionRun : execute_deposit input before with
      | fail error => simp [executionRun] at run
      | div => simp [executionRun] at run
      | ok executionResult =>
          cases executionResult with
          | Ok pair =>
              cases pair with
              | mk after certificate =>
                  simp [executionRun] at run
                  subst outcome
                  simp at rejected
          | Err failure =>
              simp [executionRun] at run
              subst outcome
              simp
  | Withdrawal input =>
      unfold execute_atomic_custody at run
      cases executionRun : execute_withdrawal input before with
      | fail error => simp [executionRun] at run
      | div => simp [executionRun] at run
      | ok executionResult =>
          cases executionResult with
          | Ok pair =>
              cases pair with
              | mk after certificate =>
                  simp [executionRun] at run
                  subst outcome
                  simp at rejected
          | Err failure =>
              simp [executionRun] at run
              subst outcome
              simp

theorem translated_committed_deposit_is_legacy_not_token2022
    (input : DepositInput) (before : CustodyState) (outcome : CustodyOutcome)
    (run : execute_atomic_custody (.Deposit input) before = .ok outcome)
    (committed : outcome.committed = true) :
    input.token_program.key = LEGACY_TOKEN_PROGRAM_ID ∧
    input.token_program.key ≠ 2#u64 ∧
    input.mint.account.owner = LEGACY_TOKEN_PROGRAM_ID ∧
    input.source.account.owner = LEGACY_TOKEN_PROGRAM_ID ∧
    input.vault.account.owner = LEGACY_TOKEN_PROGRAM_ID := by
  obtain ⟨certificate, execution, _⟩ :=
    translated_atomic_deposit_success_is_exact input before outcome run committed
  rcases execution with ⟨plan, _⟩
  rcases plan with
    ⟨_, _, _, tokenProgram, mint, source, vault, _⟩
  rcases tokenProgram with ⟨_, tokenKey, _⟩
  rcases mint with ⟨_, mintOwner, _⟩
  rcases source with ⟨sourceOwner, _⟩
  rcases vault with ⟨vaultOwner, _⟩
  exact ⟨tokenKey, by simp [tokenKey, LEGACY_TOKEN_PROGRAM_ID], mintOwner,
    sourceOwner, vaultOwner⟩

theorem translated_committed_withdrawal_is_legacy_not_token2022
    (input : WithdrawalInput) (before : CustodyState)
    (outcome : CustodyOutcome)
    (run : execute_atomic_custody (.Withdrawal input) before = .ok outcome)
    (committed : outcome.committed = true) :
    input.token_program.key = LEGACY_TOKEN_PROGRAM_ID ∧
    input.token_program.key ≠ 2#u64 ∧
    input.mint.account.owner = LEGACY_TOKEN_PROGRAM_ID ∧
    input.vault.account.owner = LEGACY_TOKEN_PROGRAM_ID ∧
    input.destination.account.owner = LEGACY_TOKEN_PROGRAM_ID := by
  obtain ⟨certificate, execution, _⟩ :=
    translated_atomic_withdrawal_success_is_exact input before outcome run
      committed
  rcases execution with ⟨plan, _⟩
  rcases plan with
    ⟨_, _, _, _, tokenProgram, mint, vault, destination, _⟩
  rcases tokenProgram with ⟨_, tokenKey, _⟩
  rcases mint with ⟨_, mintOwner, _⟩
  rcases vault with ⟨vaultOwner, _⟩
  rcases destination with ⟨destinationOwner, _⟩
  exact ⟨tokenKey, by simp [tokenKey, LEGACY_TOKEN_PROGRAM_ID], mintOwner,
    vaultOwner, destinationOwner⟩

theorem translated_token2022_deposit_is_rejected_with_exact_rollback
    (input : DepositInput) (before : CustodyState) (outcome : CustodyOutcome)
    (token2022 : input.token_program.key = 2#u64)
    (run : execute_atomic_custody (.Deposit input) before = .ok outcome) :
    outcome.committed = false ∧
    outcome.state = before ∧
    outcome.certificate = none ∧
    outcome.error ≠ none := by
  have notCommitted : outcome.committed ≠ true := by
    intro committed
    have legacy := translated_committed_deposit_is_legacy_not_token2022
      input before outcome run committed
    exact legacy.2.1 token2022
  have rejected := Bool.eq_false_of_not_eq_true notCommitted
  exact ⟨rejected,
    translated_atomic_rejection_is_exact_prestate
      (.Deposit input) before outcome run rejected⟩

theorem translated_token2022_withdrawal_is_rejected_with_exact_rollback
    (input : WithdrawalInput) (before : CustodyState)
    (outcome : CustodyOutcome)
    (token2022 : input.token_program.key = 2#u64)
    (run : execute_atomic_custody (.Withdrawal input) before = .ok outcome) :
    outcome.committed = false ∧
    outcome.state = before ∧
    outcome.certificate = none ∧
    outcome.error ≠ none := by
  have notCommitted : outcome.committed ≠ true := by
    intro committed
    have legacy := translated_committed_withdrawal_is_legacy_not_token2022
      input before outcome run committed
    exact legacy.2.1 token2022
  have rejected := Bool.eq_false_of_not_eq_true notCommitted
  exact ⟨rejected,
    translated_atomic_rejection_is_exact_prestate
      (.Withdrawal input) before outcome run rejected⟩

theorem translated_deposit_token_cpi_failure_is_exact_rollback
    (input : DepositInput) (before : CustodyState) (outcome : CustodyOutcome)
    (plan : DepositPlan)
    (planned : plan_deposit input = .ok (.Ok plan))
    (tokenCpiFails : input.runtime.token_cpi_succeeds = false)
    (run : execute_atomic_custody (.Deposit input) before = .ok outcome) :
    outcome.committed = false ∧
    outcome.state = before ∧
    outcome.certificate = none ∧
    outcome.error = some CustodyError.TokenCpi ∧
    outcome.trace = {
      plan_step := 1#u8
      verifier_step := 0#u8
      token_cpi_attempt_step := 2#u8
      token_cpi_success_step := 0#u8
      delta_step := 0#u8
      pool_write_step := 0#u8
    } := by
  unfold execute_atomic_custody execute_deposit empty_trace at run
  simp [planned, tokenCpiFails] at run
  subst outcome
  simp

theorem translated_withdrawal_token_cpi_failure_is_exact_rollback
    (input : WithdrawalInput) (before : CustodyState)
    (outcome : CustodyOutcome) (plan : WithdrawalPlan)
    (planned : plan_withdrawal input = .ok (.Ok plan))
    (verifierCpiSucceeds : input.runtime.verifier_cpi_succeeds = true)
    (tokenCpiFails : input.runtime.token_cpi_succeeds = false)
    (run : execute_atomic_custody (.Withdrawal input) before = .ok outcome) :
    outcome.committed = false ∧
    outcome.state = before ∧
    outcome.certificate = none ∧
    outcome.error = some CustodyError.TokenCpi ∧
    outcome.trace = {
      plan_step := 1#u8
      verifier_step := 2#u8
      token_cpi_attempt_step := 3#u8
      token_cpi_success_step := 0#u8
      delta_step := 0#u8
      pool_write_step := 0#u8
    } := by
  unfold execute_atomic_custody execute_withdrawal empty_trace at run
  simp [planned, verifierCpiSucceeds, tokenCpiFails] at run
  subst outcome
  simp

#print axioms translated_deposit_execution_success_is_exact
#print axioms translated_withdrawal_execution_success_is_exact
#print axioms translated_atomic_deposit_success_is_exact
#print axioms translated_atomic_withdrawal_success_is_exact
#print axioms translated_atomic_rejection_is_exact_prestate
#print axioms translated_committed_deposit_is_legacy_not_token2022
#print axioms translated_committed_withdrawal_is_legacy_not_token2022
#print axioms translated_token2022_deposit_is_rejected_with_exact_rollback
#print axioms translated_token2022_withdrawal_is_rejected_with_exact_rollback
#print axioms translated_deposit_token_cpi_failure_is_exact_rollback
#print axioms translated_withdrawal_token_cpi_failure_is_exact_rollback

end V7PoolVaultCustodyGenerated
