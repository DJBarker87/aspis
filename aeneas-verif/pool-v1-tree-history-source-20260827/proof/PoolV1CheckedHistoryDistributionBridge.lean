import PoolV1CheckedHistoryDistribution.Funs
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 literal current/rollover distribution bridge

This is the exact production routing helper used by prepared settlement plan
construction and replay.  It is intentionally separate from account runtime
behavior: the theorem exposes the two root-history locations, exact current /
next split and page-capacity gate from successful source execution.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace PoolV1CheckedHistoryDistributionBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1CheckedDistribution

def expectedCurrent
    (count firstPage lastPage currentPage : Nat) : Nat :=
  if firstPage = currentPage then
    if lastPage = currentPage then count else 1
  else 0

theorem checked_history_distribution_success_exact
    (sourceSequence : Std.U64) (header : history.RootPageHeaderV1)
    (count : Std.U64) (current next : Std.Usize)
    (run : prepared_settlement.checked_history_distribution
      sourceSequence header count = .ok (.Ok (current, next))) :
    ∃ firstSequence finalSequence : Std.U64,
      ∃ firstLocation lastLocation :
        aspis_statement.pool_v1.root_history.RootHistoryLocationV1,
        firstSequence.val = sourceSequence.val + 1 ∧
        finalSequence.val = sourceSequence.val + count.val ∧
        aspis_statement.pool_v1.root_history.root_history_location
            firstSequence = .ok firstLocation ∧
        aspis_statement.pool_v1.root_history.root_history_location
            finalSequence = .ok lastLocation ∧
        header.page_number.val ≤ firstLocation.page_number.val ∧
        lastLocation.page_number.val ≤ header.page_number.val + 1 ∧
        current.val = expectedCurrent (UScalar.cast .Usize count).val
          firstLocation.page_number.val
          lastLocation.page_number.val header.page_number.val ∧
        next.val = (UScalar.cast .Usize count).val - current.val ∧
        header.filled.val + current.val ≤ 256 := by
  unfold prepared_settlement.checked_history_distribution at run
  simp only [lift] at run
  generalize firstRun : U64.checked_add sourceSequence 1#u64 = firstResult at run
  cases firstResult with
  | none =>
    simp [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
      at run
  | some firstSequence =>
    have firstSpec := U64.checked_add_bv_spec sourceSequence 1#u64
    rw [firstRun] at firstSpec
    simp only at firstSpec
    simp [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch] at run
    generalize finalRun : U64.checked_add sourceSequence count = finalResult at run
    cases finalResult with
    | none =>
      simp [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
        at run
    | some finalSequence =>
      have finalSpec := U64.checked_add_bv_spec sourceSequence count
      rw [finalRun] at finalSpec
      simp only at finalSpec
      simp [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch] at run
      generalize firstLocationRun :
        aspis_statement.pool_v1.root_history.root_history_location firstSequence =
          firstLocationResult at run
      cases firstLocationResult with
      | fail error => simp [firstLocationRun] at run
      | div => simp [firstLocationRun] at run
      | ok firstLocation =>
        simp only [bind_tc_ok] at run
        generalize lastLocationRun :
          aspis_statement.pool_v1.root_history.root_history_location finalSequence =
            lastLocationResult at run
        cases lastLocationResult with
        | fail error => simp [lastLocationRun] at run
        | div => simp [lastLocationRun] at run
        | ok lastLocation =>
          simp only [bind_tc_ok, UScalar.lt_equiv] at run
          have firstNotBefore :
              header.page_number.val ≤ firstLocation.page_number.val := by
            by_contra contradiction
            have before :
                firstLocation.page_number.val < header.page_number.val := by omega
            simp [before,
              solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
              at run
          have notBefore :
              ¬ firstLocation.page_number.val < header.page_number.val := by omega
          simp only [notBefore, ↓reduceIte] at run
          generalize pageAddRun : header.page_number + 1#u64 = pageAddResult at run
          cases pageAddResult with
          | fail error => simp [pageAddRun] at run
          | div => simp [pageAddRun] at run
          | ok nextPage =>
            simp only [bind_tc_ok] at run
            have nextPageEquiv := @UScalar.add_equiv .U64
              header.page_number 1#u64
            rw [pageAddRun] at nextPageEquiv
            have nextPageExact :
                nextPage.val = header.page_number.val + 1 := by
              exact nextPageEquiv.2.1
            have lastNotAfter :
                lastLocation.page_number.val ≤ header.page_number.val + 1 := by
              by_contra contradiction
              have after : nextPage.val < lastLocation.page_number.val := by
                omega
              simp [after,
                solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
                at run
            have notAfter :
                ¬ nextPage.val < lastLocation.page_number.val := by omega
            have notAfterScalar :
                ¬ lastLocation.page_number > nextPage := by
              simpa only [UScalar.lt_equiv] using notAfter
            rw [if_neg notAfter] at run
            generalize currentRun :
              (if firstLocation.page_number = header.page_number then
                if lastLocation.page_number = header.page_number then
                  (Result.ok (UScalar.cast .Usize count) : Result Std.Usize)
                else Result.ok 1#usize
              else Result.ok 0#usize) = currentResult at run
            cases currentResult with
            | fail error => simp at run
            | div => simp at run
            | ok routedCurrent =>
              simp only [bind_tc_ok, lift] at run
              generalize nextRun :
                UScalar.cast .Usize count - routedCurrent = nextResult at run
              cases nextResult with
              | fail error => simp at run
              | div => simp at run
              | ok routedNext =>
                simp only [nextRun, bind_tc_ok] at run
                generalize filledAddRun :
                  core.convert.num.FromUsizeU16.from header.filled +
                    routedCurrent = filledAddResult at run
                cases filledAddResult with
                | fail error => simp at run
                | div => simp at run
                | ok filledAfter =>
                  simp only [filledAddRun, bind_tc_ok] at run
                  simp only [
                    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY,
                    aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY_LOG2]
                    at run
                  have capacityRun :
                      (1#usize <<< 8#u8) =
                        (Result.ok 256#usize : Result Std.Usize) := by
                    change UScalar.shiftLeft_UScalar 1#usize 8#u8 = _
                    unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
                    cases platformBits : System.Platform.numBits_eq <;> simp_all
                    all_goals
                      apply UScalar.eq_of_val_eq
                      simp [UScalar.val, *]
                  rw [capacityRun] at run
                  simp only [bind_tc_ok] at run
                  have withinCapacity : filledAfter.val ≤ 256 := by
                    by_contra contradiction
                    have exceeds : 256 < filledAfter.val := by omega
                    simp [exceeds,
                      solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
                      at run
                  have notExceeds : ¬ 256 < filledAfter.val := by omega
                  have notExceedsLiteral :
                      ¬ (256#usize).val < filledAfter.val := by
                    simpa using notExceeds
                  rw [if_neg notExceedsLiteral] at run
                  simp only [Result.ok.injEq,
                    core.result.Result.Ok.injEq, Prod.mk.injEq] at run
                  rcases run with ⟨rfl, rfl⟩
                  have nextSpec := Usize.sub_spec
                    (x := UScalar.cast .Usize count) (y := routedCurrent) (by
                      have nextEquiv := @UScalar.sub_equiv .Usize
                        (UScalar.cast .Usize count) routedCurrent
                      rw [nextRun] at nextEquiv
                      exact nextEquiv.1)
                  rw [nextRun] at nextSpec
                  simp only [WP.spec_ok] at nextSpec
                  have filledEquiv := @UScalar.add_equiv .Usize
                    (core.convert.num.FromUsizeU16.from header.filled)
                    routedCurrent
                  rw [filledAddRun] at filledEquiv
                  have filledSpec : filledAfter.val =
                      (core.convert.num.FromUsizeU16.from header.filled).val +
                        routedCurrent.val :=
                    filledEquiv.2.1
                  have currentExpected :
                      routedCurrent.val = expectedCurrent
                        (UScalar.cast .Usize count).val
                        firstLocation.page_number.val
                        lastLocation.page_number.val
                        header.page_number.val := by
                    unfold expectedCurrent
                    by_cases firstOnCurrent :
                        firstLocation.page_number = header.page_number
                    · by_cases lastOnCurrent :
                          lastLocation.page_number = header.page_number
                      · simp [firstOnCurrent, lastOnCurrent] at currentRun
                        cases currentRun
                        have firstVal : firstLocation.page_number.val =
                            header.page_number.val :=
                          congrArg UScalar.val firstOnCurrent
                        have lastVal : lastLocation.page_number.val =
                            header.page_number.val :=
                          congrArg UScalar.val lastOnCurrent
                        simp [firstVal, lastVal]
                      · simp [firstOnCurrent, lastOnCurrent] at currentRun
                        cases currentRun
                        have firstVal : firstLocation.page_number.val =
                            header.page_number.val :=
                          congrArg UScalar.val firstOnCurrent
                        have lastValNe : lastLocation.page_number.val ≠
                            header.page_number.val := by
                          intro valueEquality
                          exact lastOnCurrent
                            (UScalar.eq_of_val_eq valueEquality)
                        simp [firstVal, lastValNe]
                    · simp [firstOnCurrent] at currentRun
                      cases currentRun
                      have firstValNe : firstLocation.page_number.val ≠
                          header.page_number.val := by
                        intro valueEquality
                        exact firstOnCurrent
                          (UScalar.eq_of_val_eq valueEquality)
                      simp [firstValNe]
                  refine ⟨firstSequence, finalSequence, firstLocation,
                    lastLocation, ?_, ?_, firstLocationRun, lastLocationRun,
                    firstNotBefore, lastNotAfter, currentExpected, ?_, ?_⟩
                  · simpa using firstSpec.2.1
                  · simpa using finalSpec.2.1
                  · omega
                  · have fromExact :=
                      core.convert.num.FromUsizeU16.from_val_eq header.filled
                    omega

#print axioms checked_history_distribution_success_exact

end PoolV1CheckedHistoryDistributionBridge
