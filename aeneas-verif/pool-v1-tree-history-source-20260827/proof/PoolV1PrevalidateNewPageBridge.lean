import PoolV1PrevalidateNewPage.Funs
import PoolV1NormalizedNewPageDataBridge

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

theorem require_program_account_success_exact
    (account : solana_account_info.AccountInfo)
    (programId : solana_pubkey.Pubkey) (writable : Bool)
    (run : history.require_program_account account programId writable =
      .ok (.Ok ())) :
    account.owner = programId ∧ account.executable = false ∧
      account.is_writable = writable := by
  unfold history.require_program_account at run
  by_cases ownerValues : account.owner.val = programId.val
  · have ownerExact : account.owner = programId := Subtype.ext ownerValues
    simp [ownerValues] at run
    by_cases executableTrue : account.executable = true
    · simp [executableTrue] at run
    · have executableFalse := Bool.eq_false_of_not_eq_true executableTrue
      by_cases writableExact : account.is_writable = writable
      · exact ⟨ownerExact, executableFalse, writableExact⟩
      · simp [executableTrue, writableExact] at run
  · simp [ownerValues] at run

theorem require_root_page_address_success_exact
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (account : solana_account_info.AccountInfo)
    (expected : solana_pubkey.Pubkey) (bump : Std.U8)
    (addressRun : history.pool_v1_root_page_address
      programId pool pageNumber = .ok (expected, bump))
    (run : history.require_root_page_address
      programId pool pageNumber account = .ok (.Ok ())) :
    account.key = expected := by
  unfold history.require_root_page_address at run
  rw [addressRun] at run
  by_cases keyValues : account.key.val = expected.val
  · exact Subtype.ext keyValues
  · simp [keyValues] at run

theorem validate_new_page_success_components
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (account : solana_account_info.AccountInfo)
    (run : history.validate_new_page_account
      programId pool pageNumber account = .ok (.Ok ())) :
    history.require_program_account account programId true = .ok (.Ok ()) ∧
      history.require_root_page_address programId pool pageNumber account =
        .ok (.Ok ()) ∧
      ∃ data : Slice Std.U8,
        SolanaAccountDataBorrow.tryBorrowData account = .ok (.Ok data) ∧
        PoolV1NormalizedNewPageData.normalized_validate_new_page_borrowed_data data =
          .ok true := by
  unfold history.validate_new_page_account at run
  generalize ownerEq : history.require_program_account account programId true =
    ownerResult at run
  cases ownerResult with
  | fail error => simp at run
  | div => simp at run
  | ok ownerResult =>
    cases ownerResult with
    | Err error => simp at run
    | Ok ownerUnit =>
      cases ownerUnit
      generalize addressEq : history.require_root_page_address
        programId pool pageNumber account = addressResult at run
      cases addressResult with
      | fail error => simp at run
      | div => simp at run
      | ok addressResult =>
        cases addressResult with
        | Err error => simp at run
        | Ok addressUnit =>
          cases addressUnit
          generalize borrowEq : SolanaAccountDataBorrow.tryBorrowData account =
            borrowResult at run
          cases borrowResult with
          | fail error => simp at run
          | div => simp at run
          | ok borrowResult =>
            cases borrowResult with
            | Err error => simp at run
            | Ok data =>
              generalize checkEq :
                PoolV1NormalizedNewPageData.normalized_validate_new_page_borrowed_data data =
                  checkResult at run
              cases checkResult with
              | fail error => simp [checkEq] at run
              | div => simp [checkEq] at run
              | ok valid =>
                cases valid <;> simp_all

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

theorem literal_prevalidate_success_has_exact_gates_borrow_data_and_token
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (page : solana_account_info.AccountInfo)
    (expected : solana_pubkey.Pubkey) (bump : Std.U8)
    (data : Slice Std.U8)
    (token : transition.PrevalidatedNewHistoryPageV1)
    (addressRun : history.pool_v1_root_page_address
      programId pool pageNumber = .ok (expected, bump))
    (borrowRun : SolanaAccountDataBorrow.tryBorrowData page = .ok (.Ok data))
    (run : transition.prevalidate_new_history_page_v1
      programId pool pageNumber page = .ok (.Ok token)) :
    page.owner = programId ∧
      page.executable = false ∧
      page.is_writable = true ∧
      page.key = expected ∧
      data.len = 8256#usize ∧
      (∀ j (hj : j < data.length), data.val[j] = 0#u8) ∧
      token.program_id = programId ∧
      token.pool = pool ∧
      token.page = page.key ∧
      token.page_number = pageNumber := by
  have tokenExact := prevalidate_new_page_success_exact_token
    programId pool pageNumber page token run
  rcases tokenExact with
    ⟨validationRun, tokenProgram, tokenPool, tokenPage, tokenPageNumber⟩
  have components := validate_new_page_success_components
    programId pool pageNumber page validationRun
  rcases components with ⟨ownerRun, pageAddressRun, borrowedData,
    borrowedRun, dataRun⟩
  rw [borrowRun] at borrowedRun
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at borrowedRun
  subst borrowedData
  rcases require_program_account_success_exact page programId true ownerRun with
    ⟨ownerExact, executableFalse, writableTrue⟩
  have pageKey := require_root_page_address_success_exact
    programId pool pageNumber page expected bump addressRun pageAddressRun
  have dataExact :=
    PoolV1NormalizedNewPageDataBridge.normalized_validate_new_page_borrowed_data_success_exact
      data dataRun
  exact ⟨ownerExact, executableFalse, writableTrue, pageKey,
    dataExact.1, dataExact.2, tokenProgram, tokenPool, tokenPage, tokenPageNumber⟩

#print axioms prevalidate_new_page_success_requires_validator_success
#print axioms prevalidate_new_page_success_exact_token
#print axioms require_program_account_success_exact
#print axioms require_root_page_address_success_exact
#print axioms validate_new_page_success_components
#print axioms literal_prevalidate_success_has_exact_gates_borrow_data_and_token

end PoolV1PrevalidateNewPageBridge
