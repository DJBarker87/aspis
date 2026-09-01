import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16ControllerProjection
import AspisFormal.K1.V7Tag73AlphaZeroLabeledRecordsNodup

/-!
# Duplicate-free labels for the composed 517-slot controller

The product controller gives alpha priority, but both component memories
still advance on every answer.  A sum-tagged used-slot predicate proves that
every emitted label is fresh and becomes permanently used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaFinalWorkQ16LabelsNodup

open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroLabeledRecordsNodup
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Sum-tagged used-slot inventory of the product controller. -/
def alphaFinalWorkQ16SlotUsed
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :
    AlphaFinalWorkQ16DigestSlot → Prop
  | Sum.inl slot => slot ∈ state.memory.1.usedSlots
  | Sum.inr slot => slot ∈ state.memory.2.usedSlots

theorem alpha_final_work_q16_slot_used_mono
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory))
    (answer : Digest256) (slot : AlphaFinalWorkQ16DigestSlot)
    (used : alphaFinalWorkQ16SlotUsed state slot) :
    alphaFinalWorkQ16SlotUsed
      ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
        (alphaZeroCausalController transitionFuel boundaryIndex)).afterAnswer
          transitionFuel state answer) slot := by
  cases slot with
  | inl alphaSlot =>
      change alphaSlot ∈
        (alphaZeroAfterMemory transitionFuel boundaryIndex
          (alphaIndexedState state) answer).usedSlots
      rw [alpha_zero_after_memory_used_slots]
      cases preferred : alphaZeroPreferredSlot transitionFuel
          (alphaIndexedState state) with
      | none => exact used
      | some selected => exact Finset.mem_insert_of_mem used
  | inr dagSlot =>
      change dagSlot ∈
        (dagCandidateAfterMemory transitionFuel anchorIndex
          (finalWorkQ16IndexedState state) answer).usedSlots
      exact dag_candidate_memory_used_slots_mono transitionFuel anchorIndex
        (finalWorkQ16IndexedState state) answer used

theorem alpha_final_work_q16_preferred_slot_fresh
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory))
    (slot : AlphaFinalWorkQ16DigestSlot)
    (preferred :
      (alphaFinalWorkQ16DagController transitionFuel anchorIndex
        (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
          state = some slot) :
    ¬ alphaFinalWorkQ16SlotUsed state slot := by
  change (match alphaZeroPreferredSlot transitionFuel
      (alphaIndexedState state) with
    | some alphaSlot => some (Sum.inl alphaSlot)
    | none => (dagCandidatePreferredSlot transitionFuel anchorIndex
        (finalWorkQ16IndexedState state)).map Sum.inr) = some slot at preferred
  cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
      (alphaIndexedState state) with
  | some alphaSlot =>
      rw [alphaPreferred] at preferred
      have slotExact : slot = Sum.inl alphaSlot := by
        exact Option.some.inj preferred.symm
      subst slot
      exact alpha_zero_preferred_slot_fresh transitionFuel
        (alphaIndexedState state) alphaSlot alphaPreferred
  | none =>
      rw [alphaPreferred] at preferred
      cases dagPreferred : dagCandidatePreferredSlot transitionFuel anchorIndex
          (finalWorkQ16IndexedState state) with
      | none => simp [dagPreferred] at preferred
      | some dagSlot =>
          simp only [dagPreferred, Option.map_some] at preferred
          have slotExact : slot = Sum.inr dagSlot := by
            exact Option.some.inj preferred.symm
          subst slot
          exact dag_candidate_preferred_slot_fresh transitionFuel anchorIndex
            (finalWorkQ16IndexedState state) dagSlot dagPreferred

theorem alpha_final_work_q16_preferred_slot_used_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory))
    (answer : Digest256) (slot : AlphaFinalWorkQ16DigestSlot)
    (preferred :
      (alphaFinalWorkQ16DagController transitionFuel anchorIndex
        (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
          state = some slot) :
    alphaFinalWorkQ16SlotUsed
      ((alphaFinalWorkQ16DagController transitionFuel anchorIndex
        (alphaZeroCausalController transitionFuel boundaryIndex)).afterAnswer
          transitionFuel state answer) slot := by
  change (match alphaZeroPreferredSlot transitionFuel
      (alphaIndexedState state) with
    | some alphaSlot => some (Sum.inl alphaSlot)
    | none => (dagCandidatePreferredSlot transitionFuel anchorIndex
        (finalWorkQ16IndexedState state)).map Sum.inr) = some slot at preferred
  cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
      (alphaIndexedState state) with
  | some alphaSlot =>
      rw [alphaPreferred] at preferred
      have slotExact : slot = Sum.inl alphaSlot :=
        Option.some.inj preferred.symm
      subst slot
      change alphaSlot ∈
        (alphaZeroAfterMemory transitionFuel boundaryIndex
          (alphaIndexedState state) answer).usedSlots
      rw [alpha_zero_after_memory_used_slots, alphaPreferred]
      exact Finset.mem_insert_self alphaSlot
        (alphaIndexedState state).memory.usedSlots
  | none =>
      rw [alphaPreferred] at preferred
      cases dagPreferred : dagCandidatePreferredSlot transitionFuel anchorIndex
          (finalWorkQ16IndexedState state) with
      | none => simp [dagPreferred] at preferred
      | some dagSlot =>
          simp only [dagPreferred, Option.map_some] at preferred
          have slotExact : slot = Sum.inr dagSlot :=
            Option.some.inj preferred.symm
          subst slot
          change dagSlot ∈
            (dagCandidateAfterMemory transitionFuel anchorIndex
              (finalWorkQ16IndexedState state) answer).usedSlots
          rw [dag_candidate_after_memory_used_slots, dagPreferred]
          exact Finset.mem_insert_self dagSlot
            (finalWorkQ16IndexedState state).memory.usedSlots

/-- Every product-controller label is duplicate-free and avoids the complete
sum-tagged used inventory present before the segment. -/
theorem alpha_final_work_q16_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)),
      let controller := alphaFinalWorkQ16DagController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
        (alphaZeroCausalController (globalOracleCalls := globalOracleCalls)
          transitionFuel boundaryIndex)
      let labels := indexedControllerLabeledRecords transitionFuel controller
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          ¬ alphaFinalWorkQ16SlotUsed state slot := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state
      let controller := alphaFinalWorkQ16DagController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
        (alphaZeroCausalController (globalOracleCalls := globalOracleCalls)
          transitionFuel boundaryIndex)
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : ∀ slot, alphaFinalWorkQ16SlotUsed state slot →
          alphaFinalWorkQ16SlotUsed next slot := by
        intro slot used
        simpa [next, controller] using
          alpha_final_work_q16_slot_used_mono transitionFuel anchorIndex
            boundaryIndex state record.answer slot used
      change
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller state
            (record :: records))).Nodup ∧
          ∀ slot ∈ namedTraceSlots
            (indexedControllerLabeledRecords transitionFuel controller state
              (record :: records)),
            ¬ alphaFinalWorkQ16SlotUsed state slot
      cases preferred : controller.preferredSlot state with
      | none =>
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          exact And.intro tail.1 (fun slot member used =>
            tail.2 slot member (usedMono slot used))
      | some slot =>
          have slotFresh : ¬ alphaFinalWorkQ16SlotUsed state slot :=
            alpha_final_work_q16_preferred_slot_fresh transitionFuel
              anchorIndex boundaryIndex state slot (by
                simpa [controller] using preferred)
          have nextUsed : alphaFinalWorkQ16SlotUsed next slot := by
            simpa [next, controller] using
              alpha_final_work_q16_preferred_slot_used_after_answer
                transitionFuel anchorIndex boundaryIndex state record.answer
                  slot (by simpa [controller] using preferred)
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), ¬ alphaFinalWorkQ16SlotUsed state candidate := by
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

theorem alpha_final_work_q16_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (alphaFinalWorkQ16DagController transitionFuel anchorIndex
          (alphaZeroCausalController transitionFuel boundaryIndex)) state
        records)).Nodup :=
  (alpha_final_work_q16_labeled_records_nodup_and_avoid_initial
    transitionFuel anchorIndex boundaryIndex records state).1

#print axioms alphaFinalWorkQ16SlotUsed
#print axioms alpha_final_work_q16_slot_used_mono
#print axioms alpha_final_work_q16_preferred_slot_fresh
#print axioms alpha_final_work_q16_preferred_slot_used_after_answer
#print axioms alpha_final_work_q16_labeled_records_nodup_and_avoid_initial
#print axioms alpha_final_work_q16_labeled_records_named_slots_nodup

end


end AspisK1.V7Tag73AlphaFinalWorkQ16LabelsNodup
