import PoolV1PrevalidateNewPage.Funs

/-!
# Pool V1 new-page prevalidation token source bridge

The outer token constructor is literal production source.  Its successful
result is proved to be possible only after successful execution of the exact
combined new-page validator, and all four private token identities are pinned.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace PoolV1PrevalidateNewPageBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1PrevalidateNewPage

theorem prevalidate_new_page_success_requires_validator_success
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (page : solana_account_info.AccountInfo)
    (token : transition.PrevalidatedNewHistoryPageV1)
    (validationResult :
      Result (core.result.Result Unit solana_program_error.ProgramError))
    (validationRun : history.validate_new_page_account
      programId pool pageNumber page = validationResult)
    (run : transition.prevalidate_new_history_page_v1
      programId pool pageNumber page = .ok (.Ok token)) :
    validationResult = .ok (.Ok ()) := by
  have analyzedRun := run
  unfold transition.prevalidate_new_history_page_v1 at analyzedRun
  rw [validationRun] at analyzedRun
  cases validationResult with
  | fail error => simp at analyzedRun
  | div => simp at analyzedRun
  | ok validation =>
    cases validation with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at analyzedRun
    | Ok unitValue => cases unitValue; rfl

theorem prevalidate_new_page_success_exact_token
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (page : solana_account_info.AccountInfo)
    (token : transition.PrevalidatedNewHistoryPageV1)
    (run : transition.prevalidate_new_history_page_v1
      programId pool pageNumber page = .ok (.Ok token)) :
    history.validate_new_page_account programId pool pageNumber page =
        .ok (.Ok ()) ∧
      token.program_id = programId ∧
      token.pool = pool ∧
      token.page = page.key ∧
      token.page_number = pageNumber := by
  let validationResult := history.validate_new_page_account
    programId pool pageNumber page
  have validationRun : history.validate_new_page_account
      programId pool pageNumber page = validationResult := rfl
  have validationExact := prevalidate_new_page_success_requires_validator_success
    programId pool pageNumber page token validationResult validationRun run
  have exactValidation : history.validate_new_page_account
      programId pool pageNumber page = .ok (.Ok ()) :=
    validationRun.trans validationExact
  have analyzedRun := run
  unfold transition.prevalidate_new_history_page_v1 at analyzedRun
  rw [exactValidation] at analyzedRun
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
    Result.ok.injEq, core.result.Result.Ok.injEq] at analyzedRun
  subst token
  exact ⟨exactValidation, rfl, rfl, rfl, rfl⟩

#print axioms prevalidate_new_page_success_requires_validator_success
#print axioms prevalidate_new_page_success_exact_token

end PoolV1PrevalidateNewPageBridge
