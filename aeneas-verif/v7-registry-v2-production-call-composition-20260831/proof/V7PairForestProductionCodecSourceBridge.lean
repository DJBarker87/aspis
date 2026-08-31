import V7PairForestProductionCodecs.Funs

/-!
# Current production ASQ8 reconstruction and ASR8 emission

These theorems invert successful runs of the literal translated production
functions.  They do not assume verifier acceptance.  The only runtime model is
the transparent `set_return_data` callback in `FunsExternal`: it records that
the Rust control flow reached the syscall after canonical encoding, while the
Solana runtime's persistence of return bytes stays an explicit external
boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

namespace V7PairForestProductionCodecsGenerated
namespace ProductionCodecSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error

abbrev Request :=
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Statement :=
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common :=
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev TerminalResult :=
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
abbrev Authenticated :=
  v7_pair_forest_dispatch.AuthenticatedV7PairForestAsq8AccountsV1
abbrev Afterstate :=
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

def exactCommon (authenticated : Authenticated)
    (candidate : Afterstate) : Common := {
  master_account := authenticated.master_account
  checkpoint_account := authenticated.checkpoint_account
  selected_lane_account := authenticated.selected_lane_account
  output_lane := authenticated.selected_lane.lane_id
  checkpoint_sequence := authenticated.checkpoint.checkpoint_sequence
  historical_global_anchor := authenticated.checkpoint.global_root
  lane_transition := {
    live_snapshot := authenticated.live_snapshot
    candidate_afterstate := candidate
  }
}

def exactStatement (request : Request) (authenticated : Authenticated)
    (candidate : Afterstate) : Statement :=
  match request.«public» with
  | .PrivateTransfer payment => .PrivateTransfer
      (exactCommon authenticated candidate) payment
  | .Withdrawal payment => .Withdrawal
      (exactCommon authenticated candidate) payment

def resultFromAccessors
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : Common)
    (nullifier : Array aspis_core.field.M31 8#usize) : TerminalResult := {
  transition_kind := kind
  master_account := common.master_account
  selected_lane_account := common.selected_lane_account
  output_lane := common.output_lane
  nullifier
  verified_afterstate := common.lane_transition.candidate_afterstate
}

def exactResult : Statement → TerminalResult
  | .PrivateTransfer common payment =>
      resultFromAccessors .PrivateTransfer common payment.nullifier
  | .Withdrawal common payment =>
      resultFromAccessors .Withdrawal common payment.nullifier

private theorem transfer_statement_success_is_exact
    (common : Common)
    (payment :
      aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (statement : Statement)
    (run : v7_pair_forest_dispatch.transfer_statement_box_v1
      common payment = .ok (.Ok statement)) :
    statement = .PrivateTransfer common payment := by
  unfold v7_pair_forest_dispatch.transfer_statement_box_v1 at run
  cases validationRun :
      aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
        (.PrivateTransfer common payment) with
  | fail error => simp [validationRun] at run
  | div => simp [validationRun] at run
  | ok validation =>
      cases validation with
      | Err error =>
          simp [validationRun, core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch,
            v7_pair_forest_dispatch.transfer_statement_box_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
      | Ok value =>
          have h : (.PrivateTransfer common payment : Statement) = statement := by
            simpa [validationRun, core.result.Result.map_err,
              core.result.Result.Insts.CoreOpsTry.branch] using run
          exact h.symm

private theorem withdrawal_statement_success_is_exact
    (common : Common)
    (payment :
      aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (statement : Statement)
    (run : v7_pair_forest_dispatch.withdrawal_statement_box_v1
      common payment = .ok (.Ok statement)) :
    statement = .Withdrawal common payment := by
  unfold v7_pair_forest_dispatch.withdrawal_statement_box_v1 at run
  cases validationRun :
      aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
        (.Withdrawal common payment) with
  | fail error => simp [validationRun] at run
  | div => simp [validationRun] at run
  | ok validation =>
      cases validation with
      | Err error =>
          simp [validationRun, core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch,
            v7_pair_forest_dispatch.withdrawal_statement_box_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
      | Ok value =>
          have h : (.Withdrawal common payment : Statement) = statement := by
            simpa [validationRun, core.result.Result.map_err,
              core.result.Result.Insts.CoreOpsTry.branch] using run
          exact h.symm

theorem translated_reconstruction_success_is_exact
    (request : Request) (authenticated : Authenticated)
    (candidate : Afterstate) (statement : Statement)
    (run :
      v7_pair_forest_dispatch.reconstruct_asq8_statement_box_v1
          request authenticated candidate = .ok (.Ok statement)) :
    statement = exactStatement request authenticated candidate := by
  unfold v7_pair_forest_dispatch.reconstruct_asq8_statement_box_v1 at run
  cases indexRun :
      lift (U64.checked_add authenticated.live_snapshot.next_pair_index 1#u64) with
  | fail error => simp [indexRun] at run
  | div => simp [indexRun] at run
  | ok nextIndex =>
      cases indexCompareRun :
          core.cmp.PartialEq.ne.trait_default
            (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
            nextIndex (some candidate.next_pair_index) with
      | fail error => simp [indexRun, indexCompareRun] at run
      | div => simp [indexRun, indexCompareRun] at run
      | ok indexDifferent =>
          cases indexDifferent with
          | true => simp [indexRun, indexCompareRun] at run
          | false =>
              cases paymentRun : request.«public» with
              | PrivateTransfer payment =>
                  cases assetRun :
                      core.cmp.PartialEq.ne.trait_default
                        aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                        authenticated.master.identity.asset_id
                        payment.asset_id with
                  | fail error =>
                      simp [indexRun, indexCompareRun, paymentRun,
                        assetRun] at run
                  | div =>
                      simp [indexRun, indexCompareRun, paymentRun,
                        assetRun] at run
                  | ok assetDifferent =>
                      cases assetDifferent with
                      | true =>
                          simp [indexRun, indexCompareRun, paymentRun,
                            assetRun] at run
                      | false =>
                          have transferRun :
                              v7_pair_forest_dispatch.transfer_statement_box_v1
                                (exactCommon authenticated candidate) payment =
                                  .ok (.Ok statement) := by
                            simpa [indexRun, indexCompareRun, paymentRun,
                              assetRun, exactCommon,
                              v7_pair_forest_dispatch.asq8_common_box_v1]
                              using run
                          simpa [exactStatement, paymentRun] using
                            transfer_statement_success_is_exact
                              (exactCommon authenticated candidate) payment
                              statement transferRun
              | Withdrawal payment =>
                  cases assetRun :
                      core.cmp.PartialEq.ne.trait_default
                        aspis_core.field.M31.Insts.CoreCmpPartialEqM31
                        authenticated.master.identity.asset_id
                        payment.asset_id with
                  | fail error =>
                      simp [indexRun, indexCompareRun, paymentRun,
                        assetRun] at run
                  | div =>
                      simp [indexRun, indexCompareRun, paymentRun,
                        assetRun] at run
                  | ok assetDifferent =>
                      cases assetDifferent with
                      | true =>
                          simp [indexRun, indexCompareRun, paymentRun,
                            assetRun] at run
                      | false =>
                          have withdrawalRun :
                              v7_pair_forest_dispatch.withdrawal_statement_box_v1
                                (exactCommon authenticated candidate) payment =
                                  .ok (.Ok statement) := by
                            simpa [indexRun, indexCompareRun, paymentRun,
                              assetRun, exactCommon,
                              v7_pair_forest_dispatch.asq8_common_box_v1]
                              using run
                          simpa [exactStatement, paymentRun] using
                            withdrawal_statement_success_is_exact
                              (exactCommon authenticated candidate) payment
                              statement withdrawalRun

private theorem emit_success_from_exact_accessors
    (statement : Statement)
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : Common)
    (nullifier : Array aspis_core.field.M31 8#usize)
    (kindRun :
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind
        statement = .ok kind)
    (commonRun :
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
        statement = .ok common)
    (nullifierRun :
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.nullifier
        statement = .ok nullifier)
    (run : v7_pair_forest_dispatch.emit_result_v1 statement = .ok (.Ok ())) :
    ∃ encoded : Array Std.U8 792#usize,
      aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
          statement (resultFromAccessors kind common nullifier) =
            .ok (.Ok ()) ∧
      aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1
          (resultFromAccessors kind common nullifier) = .ok (.Ok encoded) := by
  unfold v7_pair_forest_dispatch.emit_result_v1 at run
  simp only [kindRun, commonRun, nullifierRun, bind_tc_ok] at run
  have resultEq :
      ({
        transition_kind := kind
        master_account := common.master_account
        selected_lane_account := common.selected_lane_account
        output_lane := common.output_lane
        nullifier
        verified_afterstate := common.lane_transition.candidate_afterstate
      } : TerminalResult) = resultFromAccessors kind common nullifier := rfl
  rw [resultEq] at run
  cases validationRun :
      aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
        statement (resultFromAccessors kind common nullifier) with
  | fail error =>
      simp [validationRun] at run
  | div =>
      simp [validationRun] at run
  | ok validation =>
      cases validation with
      | Err error =>
          simp [validationRun,
            core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch,
            v7_pair_forest_dispatch.emit_result_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
      | Ok value =>
          cases value
          cases encodingRun :
              aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1
                (resultFromAccessors kind common nullifier) with
          | fail error =>
              simp [validationRun, encodingRun,
                core.result.Result.map_err,
                core.result.Result.Insts.CoreOpsTry.branch] at run
          | div =>
              simp [validationRun, encodingRun,
                core.result.Result.map_err,
                core.result.Result.Insts.CoreOpsTry.branch] at run
          | ok encoding =>
              cases encoding with
              | Err error =>
                  simp [validationRun, encodingRun,
                    core.result.Result.map_err,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    v7_pair_forest_dispatch.emit_result_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at run
              | Ok encoded =>
                  refine ⟨encoded, ?_, ?_⟩
                  simpa using validationRun
                  rfl

theorem translated_emit_success_has_exact_canonical_result
    (statement : Statement)
    (run : v7_pair_forest_dispatch.emit_result_v1 statement = .ok (.Ok ())) :
    ∃ encoded : Array Std.U8 792#usize,
      aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
          statement (exactResult statement) = .ok (.Ok ()) ∧
      aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1
          (exactResult statement) = .ok (.Ok encoded) := by
  cases statement with
  | PrivateTransfer common payment =>
      simpa [exactResult] using emit_success_from_exact_accessors
        (.PrivateTransfer common payment) .PrivateTransfer common
        payment.nullifier (by rfl) (by rfl) (by rfl) run
  | Withdrawal common payment =>
      simpa [exactResult] using emit_success_from_exact_accessors
        (.Withdrawal common payment) .Withdrawal common
        payment.nullifier (by rfl) (by rfl) (by rfl) run

#print axioms translated_reconstruction_success_is_exact
#print axioms translated_emit_success_has_exact_canonical_result

end ProductionCodecSourceBridge
end V7PairForestProductionCodecsGenerated
