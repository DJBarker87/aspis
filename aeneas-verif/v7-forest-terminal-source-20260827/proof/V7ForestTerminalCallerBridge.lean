import V7ForestTerminal.Funs

/-!
# ASF8 / ASR8 accepted-caller source bridge

These predicates deliberately describe source control flow, not cryptographic
semantics.  Poseidon and the complete forest relation remain behind the two
named residual-evaluator callbacks.  A successful translated caller must have
selected the matching trace variant, received the exact residual count, seen
`all_zero = true`, revalidated the result against the statement, and returned
the canonical ASR8 fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

namespace V7ForestTerminalCallerBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ForestTerminalGenerated

abbrev Statement :=
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Accounts := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalAccountsV1
abbrev Compilation := pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev TerminalResult := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
abbrev Residuals :=
  pool_v1.pair_forest_constraint_residuals.PoolV1PairForestConstraintResidualsV1

def transferResult (common : Common)
    (publicInput : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    TerminalResult := {
  transition_kind := pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
  master_account := common.master_account
  selected_lane_account := common.selected_lane_account
  output_lane := common.output_lane
  nullifier := publicInput.nullifier
  verified_afterstate := common.lane_transition.candidate_afterstate
}

def withdrawalResult (common : Common)
    (publicInput : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    TerminalResult := {
  transition_kind := pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal
  master_account := common.master_account
  selected_lane_account := common.selected_lane_account
  output_lane := common.output_lane
  nullifier := publicInput.nullifier
  verified_afterstate := common.lane_transition.candidate_afterstate
}

def TransferAcceptedSourceContract
    (common : Common)
    (publicInput : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (accounts : Accounts) (compilation : Compilation)
    (result : TerminalResult) : Prop :=
  let statement :=
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
      common publicInput
  pool_v1.pair_forest_terminal.host.validate_accounts statement accounts =
      .ok (.Ok ()) ∧
  core.cmp.PartialEq.ne.trait_default
      pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1
      compilation.public_statement common.lane_transition = .ok false ∧
  core.cmp.PartialEq.ne.trait_default
      pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1
      compilation.trace.afterstate common.lane_transition.candidate_afterstate =
      .ok false ∧
  core.cmp.PartialEq.ne.trait_default
      pool_v1.pair_trace.PoolV1PairTraceVariantV1.Insts.CoreCmpPartialEqPoolV1PairTraceVariantV1
      compilation.trace.variant
      pool_v1.pair_trace.PoolV1PairTraceVariantV1.PrivateTransfer = .ok false ∧
  ∃ residuals : Residuals, ∃ expected actual : Std.Usize,
    pool_v1.pair_forest_constraint_residuals.evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1
        publicInput compilation.public_statement compilation.semantic_c1 =
      .ok (.Ok residuals) ∧
    pool_v1.pair_forest_constraint_residuals.POOL_V1_PAIR_FOREST_TRANSFER_TOTAL_RESIDUAL_COUNT =
      .ok expected ∧
    pool_v1.pair_forest_constraint_residuals.PoolV1PairForestConstraintResidualsV1.residual_count
        residuals = .ok actual ∧
    actual.val = expected.val ∧
    pool_v1.pair_forest_constraint_residuals.PoolV1PairForestConstraintResidualsV1.all_zero
        residuals = .ok true ∧
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
        statement (transferResult common publicInput) = .ok (.Ok ()) ∧
    result = transferResult common publicInput

def WithdrawalAcceptedSourceContract
    (common : Common)
    (publicInput : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (accounts : Accounts) (compilation : Compilation)
    (result : TerminalResult) : Prop :=
  let statement :=
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
      common publicInput
  pool_v1.pair_forest_terminal.host.validate_accounts statement accounts =
      .ok (.Ok ()) ∧
  core.cmp.PartialEq.ne.trait_default
      pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1
      compilation.public_statement common.lane_transition = .ok false ∧
  core.cmp.PartialEq.ne.trait_default
      pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1
      compilation.trace.afterstate common.lane_transition.candidate_afterstate =
      .ok false ∧
  core.cmp.PartialEq.ne.trait_default
      pool_v1.pair_trace.PoolV1PairTraceVariantV1.Insts.CoreCmpPartialEqPoolV1PairTraceVariantV1
      compilation.trace.variant
      pool_v1.pair_trace.PoolV1PairTraceVariantV1.Withdrawal = .ok false ∧
  ∃ residuals : Residuals, ∃ expected actual : Std.Usize,
    pool_v1.pair_forest_constraint_residuals.evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1
        publicInput compilation.public_statement compilation.semantic_c1 =
      .ok (.Ok residuals) ∧
    pool_v1.pair_forest_constraint_residuals.POOL_V1_PAIR_FOREST_WITHDRAWAL_TOTAL_RESIDUAL_COUNT =
      .ok expected ∧
    pool_v1.pair_forest_constraint_residuals.PoolV1PairForestConstraintResidualsV1.residual_count
        residuals = .ok actual ∧
    actual.val = expected.val ∧
    pool_v1.pair_forest_constraint_residuals.PoolV1PairForestConstraintResidualsV1.all_zero
        residuals = .ok true ∧
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
        statement (withdrawalResult common publicInput) = .ok (.Ok ()) ∧
    result = withdrawalResult common publicInput

private theorem break_residual_cannot_return_ok
    {A E F B : Type}
    (input : core.result.Result A E)
    (residual : core.result.Result core.convert.Infallible E)
    (convert : core.convert.From F E)
    (output : B)
    (branchRun :
      core.result.Result.Insts.CoreOpsTry.branch input = .ok (.Break residual))
    (residualRun :
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          B convert residual = .ok (.Ok output)) : False := by
  cases input with
  | Ok value => simp [core.result.Result.Insts.CoreOpsTry.branch] at branchRun
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at branchRun
      subst residual
      simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at residualRun
      cases convertRun : convert.from error <;> simp [convertRun] at residualRun

@[simp] private theorem branch_eq_continue_iff
    {A E : Type} (input : core.result.Result A E) (value : A) :
    core.result.Result.Insts.CoreOpsTry.branch input = .ok (.Continue value) ↔
      input = .Ok value := by
  cases input <;> simp [core.result.Result.Insts.CoreOpsTry.branch]

@[simp] private theorem map_err_eq_ok_iff
    {T E F O : Type} (callback : core.ops.function.FnOnce O E F)
    (input : core.result.Result T E) (state : O) (value : T) :
    core.result.Result.map_err callback input state = .ok (.Ok value) ↔
      input = .Ok value := by
  cases input with
  | Ok current => simp [core.result.Result.map_err]
  | Err error =>
      simp only [core.result.Result.map_err]
      cases callbackRun : callback.call_once state error <;>
        simp [callbackRun]

theorem accepted_transfer_source_has_exact_contract
    (common : Common)
    (publicInput : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (accounts : Accounts) (compilation : Compilation)
    (result : TerminalResult)
    (run :
      pool_v1.pair_forest_terminal.host.verify_pool_v1_pair_forest_terminal_inactive_v1
          (.PrivateTransfer common publicInput) accounts compilation =
        .ok (.Ok result)) :
    TransferAcceptedSourceContract common publicInput accounts compilation result := by
  unfold pool_v1.pair_forest_terminal.host.verify_pool_v1_pair_forest_terminal_inactive_v1 at run
  simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok, bind_tc_fail,
    bind_tc_div, Aeneas.Std.Result.ok.injEq]
  repeat'
    (split at run <;>
      try dsimp at run <;>
      try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
        bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
        core.convert.FromSame.from])
  all_goals try
    (exfalso
     eapply break_residual_cannot_return_ok <;> assumption)
  all_goals simp_all [TransferAcceptedSourceContract, transferResult,
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common,
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind,
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.nullifier,
    core.convert.FromSame.from]

theorem accepted_withdrawal_source_has_exact_contract
    (common : Common)
    (publicInput : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (accounts : Accounts) (compilation : Compilation)
    (result : TerminalResult)
    (run :
      pool_v1.pair_forest_terminal.host.verify_pool_v1_pair_forest_terminal_inactive_v1
          (.Withdrawal common publicInput) accounts compilation =
        .ok (.Ok result)) :
    WithdrawalAcceptedSourceContract common publicInput accounts compilation result := by
  unfold pool_v1.pair_forest_terminal.host.verify_pool_v1_pair_forest_terminal_inactive_v1 at run
  simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok, bind_tc_fail,
    bind_tc_div, Aeneas.Std.Result.ok.injEq]
  repeat'
    (split at run <;>
      try dsimp at run <;>
      try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
        bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
        core.convert.FromSame.from])
  all_goals try
    (exfalso
     eapply break_residual_cannot_return_ok <;> assumption)
  all_goals simp_all [WithdrawalAcceptedSourceContract, withdrawalResult,
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common,
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind,
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.nullifier,
    core.convert.FromSame.from]

#print axioms accepted_transfer_source_has_exact_contract
#print axioms accepted_withdrawal_source_has_exact_contract

end V7ForestTerminalCallerBridge
