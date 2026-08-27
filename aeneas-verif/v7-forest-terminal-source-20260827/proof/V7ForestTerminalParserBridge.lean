import V7ForestTerminal.Funs

/-!
# ASF8 / ASR8 translated parser bridge

The two theorems below state the key fail-closed parser property: a successful
literal translated decoder can only return a value that also passed the
production validator called at the end of that decoder.  Nested codecs are
kept as the named external interfaces emitted in `FunsExternal.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace V7ForestTerminalParserBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ForestTerminalGenerated

private theorem break_residual_cannot_return_ok
    {A E F B : Type}
    (input : core.result.Result A E)
    (residual : core.result.Result core.convert.Infallible E)
    (convert : core.convert.From F E)
    (output : B)
    (branchRun :
      core.result.Result.Insts.CoreOpsTry.branch input =
        .ok (.Break residual))
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

theorem statement_decode_success_implies_validation_success
    (bytes : Slice Std.U8)
    (statement : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
    (run :
      pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
          bytes = .ok (.Ok statement)) :
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
        statement = .ok (.Ok ()) := by
  unfold pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 at run
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
  all_goals simp_all [
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem result_decode_success_implies_validation_success
    (bytes : Slice Std.U8)
    (result : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1)
    (run :
      pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_result_v1
          bytes = .ok (.Ok result)) :
    pool_v1.pair_forest_terminal.validate_result result = .ok (.Ok ()) := by
  unfold pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_result_v1 at run
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
  all_goals simp_all [
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

#print axioms statement_decode_success_implies_validation_success
#print axioms result_decode_success_implies_validation_success

end V7ForestTerminalParserBridge
