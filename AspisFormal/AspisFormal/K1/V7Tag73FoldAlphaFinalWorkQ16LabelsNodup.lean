import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16LabelsNodup
import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition

/-!
# Duplicate-free labels for the complete 518-slot controller

The outer fold-work slot is one-shot.  Every other label is the sum-tagged
label of the already duplicate-free 517-slot controller.  A single used-slot
invariant proves duplicate freedom for every answer stream, independently of
the accepted-source trace.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup

open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaFinalWorkQ16LabelsNodup
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def foldAlphaFinalWorkQ16SlotUsed
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory))) :
    FoldAlphaFinalWorkQ16DigestSlot → Prop
  | none => state.memory.1 = true
  | some slot => alphaFinalWorkQ16SlotUsed (underlyingIndexedState state) slot

theorem fold_alpha_final_work_q16_slot_used_mono
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)))
    (answer : Digest256) (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (used : foldAlphaFinalWorkQ16SlotUsed state slot) :
    foldAlphaFinalWorkQ16SlotUsed
      ((foldAlphaFinalWorkQ16Controller foldExposureIndex
        (alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex))).afterAnswer
            transitionFuel state answer) slot := by
  cases slot with
  | none =>
      change state.memory.1 = true at used
      simpa [foldAlphaFinalWorkQ16SlotUsed,
        IndexedUnifiedExposureController.afterAnswer,
        foldAlphaFinalWorkQ16Controller] using
          (Or.inl used : state.memory.1 = true ∨
            state.exposureIndex = foldExposureIndex)
  | some underlyingSlot =>
      change alphaFinalWorkQ16SlotUsed
        ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex)).afterAnswer
            transitionFuel (underlyingIndexedState state) answer)
          underlyingSlot
      exact alpha_final_work_q16_slot_used_mono transitionFuel anchorIndex
        boundaryIndex (underlyingIndexedState state) answer underlyingSlot used

theorem fold_alpha_final_work_q16_preferred_slot_fresh
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)))
    (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (preferred :
      (foldAlphaFinalWorkQ16Controller foldExposureIndex
        (alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex))).preferredSlot
            state = some slot) :
    ¬ foldAlphaFinalWorkQ16SlotUsed state slot := by
  by_cases atFold : state.memory.1 = false ∧
      state.exposureIndex = foldExposureIndex
  · have slotExact : slot = none := by
      have preferred' : some none = some slot := by
        simpa [foldAlphaFinalWorkQ16Controller, atFold] using preferred
      exact (Option.some.inj preferred').symm
    subst slot
    simpa [foldAlphaFinalWorkQ16SlotUsed] using atFold.1
  · change
      (if state.memory.1 = false ∧ state.exposureIndex = foldExposureIndex then
        some none
      else
        ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
            (underlyingIndexedState state)).map some) = some slot at preferred
    rw [if_neg atFold] at preferred
    cases underlyingPreferred :
        (alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
            (underlyingIndexedState state) with
    | none => simp [underlyingPreferred] at preferred
    | some underlyingSlot =>
        have slotExact : slot = some underlyingSlot := by
          have preferred' : some (some underlyingSlot) = some slot := by
            simpa [underlyingPreferred] using preferred
          exact (Option.some.inj preferred').symm
        subst slot
        exact alpha_final_work_q16_preferred_slot_fresh transitionFuel
          anchorIndex boundaryIndex (underlyingIndexedState state)
            underlyingSlot underlyingPreferred

theorem fold_alpha_final_work_q16_preferred_slot_used_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)))
    (answer : Digest256) (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (preferred :
      (foldAlphaFinalWorkQ16Controller foldExposureIndex
        (alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex))).preferredSlot
            state = some slot) :
    foldAlphaFinalWorkQ16SlotUsed
      ((foldAlphaFinalWorkQ16Controller foldExposureIndex
        (alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex))).afterAnswer
            transitionFuel state answer) slot := by
  by_cases atFold : state.memory.1 = false ∧
      state.exposureIndex = foldExposureIndex
  · have slotExact : slot = none := by
      have preferred' : some none = some slot := by
        simpa [foldAlphaFinalWorkQ16Controller, atFold] using preferred
      exact (Option.some.inj preferred').symm
    subst slot
    simp [foldAlphaFinalWorkQ16SlotUsed,
      IndexedUnifiedExposureController.afterAnswer,
      foldAlphaFinalWorkQ16Controller, atFold.2]
  · change
      (if state.memory.1 = false ∧ state.exposureIndex = foldExposureIndex then
        some none
      else
        ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
            (underlyingIndexedState state)).map some) = some slot at preferred
    rw [if_neg atFold] at preferred
    cases underlyingPreferred :
        (alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
            (underlyingIndexedState state) with
    | none => simp [underlyingPreferred] at preferred
    | some underlyingSlot =>
        have slotExact : slot = some underlyingSlot := by
          have preferred' : some (some underlyingSlot) = some slot := by
            simpa [underlyingPreferred] using preferred
          exact (Option.some.inj preferred').symm
        subst slot
        change alphaFinalWorkQ16SlotUsed
          ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
            (alphaZeroCausalController transitionFuel boundaryIndex)).afterAnswer
              transitionFuel (underlyingIndexedState state) answer)
            underlyingSlot
        exact alpha_final_work_q16_preferred_slot_used_after_answer
          transitionFuel anchorIndex boundaryIndex (underlyingIndexedState state)
            answer underlyingSlot underlyingPreferred

theorem fold_alpha_final_work_q16_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex anchorIndex boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (FoldAlphaFinalWorkQ16ControllerMemory
          (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory))),
      let controller : IndexedUnifiedExposureController globalOracleCalls
          Digest256 FoldAlphaFinalWorkQ16DigestSlot
          (FoldAlphaFinalWorkQ16ControllerMemory
            (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :=
        foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel anchorIndex
            (alphaZeroCausalController transitionFuel boundaryIndex))
      let labels := indexedControllerLabeledRecords transitionFuel controller
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          ¬ foldAlphaFinalWorkQ16SlotUsed state slot := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state
      let controller : IndexedUnifiedExposureController globalOracleCalls
          Digest256 FoldAlphaFinalWorkQ16DigestSlot
          (FoldAlphaFinalWorkQ16ControllerMemory
            (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :=
        foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel anchorIndex
            (alphaZeroCausalController transitionFuel boundaryIndex))
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : ∀ slot, foldAlphaFinalWorkQ16SlotUsed state slot →
          foldAlphaFinalWorkQ16SlotUsed next slot := by
        intro slot used
        simpa [next, controller] using
          fold_alpha_final_work_q16_slot_used_mono transitionFuel
            foldExposureIndex anchorIndex boundaryIndex state record.answer slot
              used
      change
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller state
            (record :: records))).Nodup ∧
          ∀ slot ∈ namedTraceSlots
            (indexedControllerLabeledRecords transitionFuel controller state
              (record :: records)),
            ¬ foldAlphaFinalWorkQ16SlotUsed state slot
      cases preferred : controller.preferredSlot state with
      | none =>
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          exact And.intro tail.1 (fun slot member used =>
            tail.2 slot member (usedMono slot used))
      | some slot =>
          have slotFresh : ¬ foldAlphaFinalWorkQ16SlotUsed state slot :=
            fold_alpha_final_work_q16_preferred_slot_fresh transitionFuel
              foldExposureIndex anchorIndex boundaryIndex state slot (by
                simpa [controller] using preferred)
          have nextUsed : foldAlphaFinalWorkQ16SlotUsed next slot := by
            simpa [next, controller] using
              fold_alpha_final_work_q16_preferred_slot_used_after_answer
                transitionFuel foldExposureIndex anchorIndex boundaryIndex state
                  record.answer slot (by simpa [controller] using preferred)
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), ¬ foldAlphaFinalWorkQ16SlotUsed state candidate := by
            intro candidate member used
            exact tail.2 candidate member (usedMono candidate used)
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          constructor
          · exact List.nodup_cons.mpr ⟨slotNotTail, tail.1⟩
          · intro candidate member
            simp only [List.mem_cons] at member
            rcases member with equal | tailMember
            · subst candidate
              exact slotFresh
            · exact tailAvoidsInitial candidate tailMember

theorem fold_alpha_final_work_q16_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex anchorIndex boundaryIndex : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory))) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel anchorIndex
            (alphaZeroCausalController transitionFuel boundaryIndex))) state
        records)).Nodup :=
  (fold_alpha_final_work_q16_labeled_records_nodup_and_avoid_initial
    transitionFuel foldExposureIndex anchorIndex boundaryIndex records state).1

#print axioms foldAlphaFinalWorkQ16SlotUsed
#print axioms fold_alpha_final_work_q16_slot_used_mono
#print axioms fold_alpha_final_work_q16_preferred_slot_fresh
#print axioms fold_alpha_final_work_q16_preferred_slot_used_after_answer
#print axioms fold_alpha_final_work_q16_labeled_records_nodup_and_avoid_initial
#print axioms fold_alpha_final_work_q16_labeled_records_named_slots_nodup

end

end AspisK1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup
