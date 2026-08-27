import PoolV1NormalizedPreparedWriteback.Funs
import PoolV1HistoryResultImagesRoutingBridge

/-!
# Pool V1 prepared-history write-back normalization

This is the pure suffix after Solana has returned all requested mutable
account-data borrows at their exact fixed lengths.  Fixed-array assignment is
the semantic result of the production equal-length `copy_from_slice` calls.
The theorem composes that extracted suffix with the literal result-image
checker, so Pool routing and image selection never move behind a runtime
interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace PoolV1NormalizedPreparedWritebackBridge

open Aeneas Aeneas.Std Result ControlFlow Error

open PoolV1NormalizedPreparedWriteback

theorem normalized_writeback_success_exact
    (sourceCurrent : Array Std.U8 8256#usize)
    (sourceRollover : Option (Array Std.U8 8256#usize))
    (nextPool : Array Std.U8 1000#usize)
    (nextCurrent : Array Std.U8 8256#usize)
    (nextRollover : Option (Array Std.U8 8256#usize))
    (currentWritable : Bool)
    (out : NormalizedPreparedHistoryWritebackV1)
    (run : normalized_prepared_history_writeback sourceCurrent sourceRollover
      nextPool nextCurrent nextRollover currentWritable = .ok (.some out)) :
    out.pool = nextPool ∧
      out.current = (if currentWritable then nextCurrent else sourceCurrent) ∧
      out.rollover = nextRollover ∧
      ((sourceRollover = .none ∧ nextRollover = .none) ∨
        (∃ source image, sourceRollover = .some source ∧
          nextRollover = .some image)) := by
  unfold normalized_prepared_history_writeback at run
  cases writable : currentWritable <;>
    cases sourceEq : sourceRollover <;>
    cases nextEq : nextRollover <;>
    simp_all
  all_goals (cases run; simp_all)

theorem checked_history_images_have_exact_normalized_writeback
    (programId pool : solana_pubkey.Pubkey)
    (plan :
      PoolV1HistoryResultImages.prepared_settlement_format.PreparedSettlementPlanViewV1)
    (sourceCurrent : Array Std.U8 8256#usize)
    (sourceNext : Option (Array Std.U8 8256#usize))
    (currentWritable : Bool)
    (imageRun :
      PoolV1HistoryResultImages.prepared_settlement.history_result_images_match
        programId pool plan sourceCurrent sourceNext = .ok (.Ok ())) :
    ∃ out : NormalizedPreparedHistoryWritebackV1,
      normalized_prepared_history_writeback sourceCurrent sourceNext
        plan.next_pool_image plan.next_current_page_image
        plan.next_rollover_page_image currentWritable = .ok (.some out) ∧
      out.pool = plan.next_pool_image ∧
      out.current =
        (if currentWritable then plan.next_current_page_image else sourceCurrent) ∧
      out.rollover = plan.next_rollover_page_image := by
  rcases
      PoolV1HistoryResultImagesRoutingBridge.history_result_images_success_has_exact_page_route
        programId pool plan sourceCurrent sourceNext imageRun with
    ⟨location, header, count, current, next, locationRun, validationRun,
      countExact, distributionRun, route⟩
  rcases route with route | route
  · rcases route with ⟨nextZero, planNone, sourceNone, resultNone⟩
    subst sourceNext
    rw [resultNone]
    cases writable : currentWritable
    · refine ⟨{
          pool := plan.next_pool_image,
          current := sourceCurrent,
          rollover := .none }, ?_⟩
      simp [normalized_prepared_history_writeback]
    · refine ⟨{
          pool := plan.next_pool_image,
          current := plan.next_current_page_image,
          rollover := .none }, ?_⟩
      simp [normalized_prepared_history_writeback]
  · rcases route with
      ⟨nextNonzero, address, source, result, planSome, sourceSome, resultSome⟩
    subst sourceNext
    rw [resultSome]
    cases writable : currentWritable
    · refine ⟨{
          pool := plan.next_pool_image,
          current := sourceCurrent,
          rollover := .some result }, ?_⟩
      simp [normalized_prepared_history_writeback]
    · refine ⟨{
          pool := plan.next_pool_image,
          current := plan.next_current_page_image,
          rollover := .some result }, ?_⟩
      simp [normalized_prepared_history_writeback]

#print axioms normalized_writeback_success_exact
#print axioms checked_history_images_have_exact_normalized_writeback

end PoolV1NormalizedPreparedWritebackBridge
