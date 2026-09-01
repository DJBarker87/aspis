import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition

/-!
# Projection of the complete 518-slot controller

The outer one-shot fold selector does not alter the cursor, exposure index, or
memory evolution of the existing 517-slot controller.  These equalities let
the established accepted-source routing proofs be reused at every distinct
root exposure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerProjection

open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

@[simp] theorem underlying_indexed_state_after_fold_answer
    {globalOracleCalls : Nat} {Memory : Type}
    (transitionFuel foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory Memory))
    (answer : Digest256) :
    underlyingIndexedState
        ((foldAlphaFinalWorkQ16Controller foldExposureIndex underlying
          ).afterAnswer transitionFuel state answer) =
      underlying.afterAnswer transitionFuel (underlyingIndexedState state)
        answer := by
  rfl

theorem underlying_indexed_state_after_fold_records
    {globalOracleCalls : Nat} {Memory : Type}
    (transitionFuel foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (FoldAlphaFinalWorkQ16ControllerMemory Memory)),
      underlyingIndexedState
          (indexedStateAfterRecords transitionFuel
            (foldAlphaFinalWorkQ16Controller foldExposureIndex underlying)
            records state) =
        indexedStateAfterRecords transitionFuel underlying records
          (underlyingIndexedState state) := by
  intro records
  induction records with
  | nil => intro state; rfl
  | cons record records ih =>
      intro state
      rw [indexed_state_after_records_cons, indexed_state_after_records_cons]
      rw [ih]
      rfl

/-- At every exposure other than the one selected fold exposure, an existing
517-slot preference is preserved under the right summand. -/
theorem underlying_preferred_lifts_at_distinct_exposure
    {globalOracleCalls : Nat} {Memory : Type}
    (foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory Memory))
    (slot : AlphaFinalWorkQ16DigestSlot)
    (distinct : state.exposureIndex ≠ foldExposureIndex)
    (preferred : underlying.preferredSlot (underlyingIndexedState state) =
      some slot) :
    (foldAlphaFinalWorkQ16Controller foldExposureIndex underlying).preferredSlot
        state = some (some slot) := by
  apply fold_controller_preferred_of_underlying foldExposureIndex underlying
    state slot
  · intro collision
    exact distinct collision.2
  · exact preferred

#print axioms underlying_indexed_state_after_fold_answer
#print axioms underlying_indexed_state_after_fold_records
#print axioms underlying_preferred_lifts_at_distinct_exposure

end

end AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerProjection
