import AspisFormal.K1.V7Tag73AlphaZeroCausalController
import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting

/-!
# Component projections of the 517-slot product controller

The alpha and final-work/q16 memories evolve independently while sharing the
literal unified cursor and exposure index.  These replay equalities let the
accepted-source proofs for each component be reused without identifying two
separately simulated executions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaFinalWorkQ16ControllerProjection

open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

@[simp] theorem alpha_indexed_state_after_composed_answer
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory))
    (answer : Digest256) :
    alphaIndexedState
        ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
          alphaController).afterAnswer transitionFuel state answer) =
      alphaController.afterAnswer transitionFuel (alphaIndexedState state)
        answer := by
  rfl

@[simp] theorem final_work_q16_indexed_state_after_composed_answer
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory))
    (answer : Digest256) :
    finalWorkQ16IndexedState
        ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
          alphaController).afterAnswer transitionFuel state answer) =
      (finalWorkQ16DagController globalOracleCalls transitionFuel anchorIndex
        ).afterAnswer transitionFuel (finalWorkQ16IndexedState state) answer := by
  rfl

theorem alpha_indexed_state_after_composed_records
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (AlphaFinalWorkQ16ControllerMemory AlphaMemory)),
      alphaIndexedState
          (indexedStateAfterRecords transitionFuel
            (alphaFinalWorkQ16DagController transitionFuel anchorIndex
              alphaController) records state) =
        indexedStateAfterRecords transitionFuel alphaController records
          (alphaIndexedState state) := by
  intro records
  induction records with
  | nil => intro state; rfl
  | cons record records ih =>
      intro state
      rw [indexed_state_after_records_cons, indexed_state_after_records_cons]
      rw [ih]
      rfl

theorem final_work_q16_indexed_state_after_composed_records
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (AlphaFinalWorkQ16ControllerMemory AlphaMemory)),
      finalWorkQ16IndexedState
          (indexedStateAfterRecords transitionFuel
            (alphaFinalWorkQ16DagController transitionFuel anchorIndex
              alphaController) records state) =
        indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) records (finalWorkQ16IndexedState state) := by
  intro records
  induction records with
  | nil => intro state; rfl
  | cons record records ih =>
      intro state
      rw [indexed_state_after_records_cons, indexed_state_after_records_cons]
      rw [ih]
      rfl

#print axioms alpha_indexed_state_after_composed_answer
#print axioms final_work_q16_indexed_state_after_composed_answer
#print axioms alpha_indexed_state_after_composed_records
#print axioms final_work_q16_indexed_state_after_composed_records

end


end AspisK1.V7Tag73AlphaFinalWorkQ16ControllerProjection
