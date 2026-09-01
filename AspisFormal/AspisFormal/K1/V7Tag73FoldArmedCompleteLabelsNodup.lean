import AspisFormal.K1.V7Tag73FoldArmedAlphaZeroController
import AspisFormal.K1.V7Tag73AlphaZeroLabeledRecordsNodup
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-!
# Duplicate-free labels for the fold-armed 518-slot controller

The causal fold-armed controller may install alpha block zero from an earlier
machine exposure, but it never retroactively labels that exposure.  This file
proves the property the probability router actually needs: every label that
is emitted online is one-shot.  The proof tracks the outer fold slot, the four
alpha slots, and the final-work/q16 DAG slots in one explicit used inventory.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldArmedCompleteLabelsNodup

open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroLabeledRecordsNodup
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def foldArmedCompleteSlotUsed
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory) : FoldAlphaFinalWorkQ16DigestSlot → Prop
  | none => state.memory.1 = true
  | some (Sum.inl slot) => slot ∈ state.memory.2.1.alpha.usedSlots
  | some (Sum.inr slot) => slot ∈ state.memory.2.2.usedSlots

/-- Reachable controller states remember whether the unique fold exposure has
already been crossed.  This excludes synthetic states that sit at the fold
ordinal while claiming the outer fold slot was consumed earlier. -/
def FoldArmedOuterCoherent
    {globalOracleCalls : Nat}
    (foldExposureIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory) : Prop :=
  state.memory.1 = decide (foldExposureIndex < state.exposureIndex)

theorem fold_armed_outer_coherent_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (answer : Digest256)
    (coherent : FoldArmedOuterCoherent foldExposureIndex state) :
    FoldArmedOuterCoherent foldExposureIndex
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterAnswer transitionFuel state answer) := by
  unfold FoldArmedOuterCoherent at coherent ⊢
  simp only [IndexedUnifiedExposureController.afterAnswer,
    foldArmedCompleteController]
  rw [coherent]
  by_cases passed : foldExposureIndex < state.exposureIndex
  · simp [passed]
    omega
  · by_cases atFold : state.exposureIndex = foldExposureIndex
    · have nextPassed : foldExposureIndex < state.exposureIndex + 1 := by omega
      simp [passed, atFold, nextPassed]
    · have before : state.exposureIndex < foldExposureIndex := by omega
      simp [passed, atFold]
      exact before

theorem fold_armed_complete_slot_used_mono
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (answer : Digest256) (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (used : foldArmedCompleteSlotUsed state slot) :
    foldArmedCompleteSlotUsed
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterAnswer transitionFuel state answer) slot := by
  cases slot with
  | none =>
      change state.memory.1 = true at used
      simpa [foldArmedCompleteSlotUsed,
        IndexedUnifiedExposureController.afterAnswer,
        foldArmedCompleteController] using
          (Or.inl used : state.memory.1 = true ∨
            state.exposureIndex = foldExposureIndex)
  | some slot =>
      cases slot with
      | inl alphaSlot =>
          change alphaSlot ∈ state.memory.2.1.alpha.usedSlots at used
          change alphaSlot ∈
            ((foldArmedCompleteController transitionFuel foldExposureIndex
              finalWorkAnchorIndex).afterMemory state answer).2.1.alpha.usedSlots
          simp only [foldArmedCompleteController,
            alphaFinalWorkQ16DagController, foldArmedAlphaZeroController]
          split
          · rw [arm_fold_alpha_memory_used_slots]
            exact used
          · change alphaSlot ∈
              (foldArmedAlphaAfterMemory transitionFuel
                (alphaIndexedState (foldArmedUnderlyingState state))
                answer).alpha.usedSlots
            rw [fold_armed_alpha_after_memory_used_slots]
            split
            · exact used
            · exact Finset.mem_insert_of_mem used
      | inr dagSlot =>
          change dagSlot ∈ state.memory.2.2.usedSlots at used
          change dagSlot ∈
            ((foldArmedCompleteController transitionFuel foldExposureIndex
              finalWorkAnchorIndex).afterMemory state answer).2.2.usedSlots
          simp only [foldArmedCompleteController,
            alphaFinalWorkQ16DagController]
          exact dag_candidate_memory_used_slots_mono transitionFuel
            finalWorkAnchorIndex (finalWorkQ16IndexedState
              (foldArmedUnderlyingState state)) answer used

theorem fold_armed_complete_preferred_slot_fresh
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (preferred :
      (foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).preferredSlot state = some slot) :
    ¬ foldArmedCompleteSlotUsed state slot := by
  by_cases atFold : state.memory.1 = false ∧
      state.exposureIndex = foldExposureIndex
  · have slotExact : slot = none := by
      have : some none = some slot := by
        simpa [foldArmedCompleteController, atFold] using preferred
      exact (Option.some.inj this).symm
    subst slot
    simpa [foldArmedCompleteSlotUsed] using atFold.1
  · change
      (if state.memory.1 = false ∧ state.exposureIndex = foldExposureIndex then
        some none
      else
        ((alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
          (foldArmedAlphaZeroController transitionFuel)).preferredSlot
            (foldArmedUnderlyingState state)).map some) = some slot at preferred
    rw [if_neg atFold] at preferred
    cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
        (foldArmedAlphaIndexedState
          (alphaIndexedState (foldArmedUnderlyingState state))) with
    | some alphaSlot =>
        have underlying :
            (alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
              (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                (foldArmedUnderlyingState state) = some (Sum.inl alphaSlot) := by
          apply alpha_final_work_q16_preferred_of_alpha
          simpa [foldArmedAlphaZeroController] using
            alphaPreferred
        rw [underlying] at preferred
        have slotExact : slot = some (Sum.inl alphaSlot) := by
          simpa using (Option.some.inj preferred).symm
        subst slot
        change alphaSlot ∉ state.memory.2.1.alpha.usedSlots
        exact alpha_zero_preferred_slot_fresh transitionFuel
          (foldArmedAlphaIndexedState
            (alphaIndexedState (foldArmedUnderlyingState state))) alphaSlot
          alphaPreferred
    | none =>
        cases dagPreferred : dagCandidatePreferredSlot transitionFuel
            finalWorkAnchorIndex
            (finalWorkQ16IndexedState (foldArmedUnderlyingState state)) with
        | none =>
            have alphaNone :
                (foldArmedAlphaZeroController transitionFuel).preferredSlot
                    (alphaIndexedState (foldArmedUnderlyingState state)) =
                  none := by
              simpa [foldArmedAlphaZeroController] using
                alphaPreferred
            have underlyingNone :
                (alphaFinalWorkQ16DagController transitionFuel
                  finalWorkAnchorIndex
                  (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                    (foldArmedUnderlyingState state) = none := by
              change (match
                  (foldArmedAlphaZeroController transitionFuel).preferredSlot
                    (alphaIndexedState (foldArmedUnderlyingState state)) with
                | some alphaSlot => some (Sum.inl alphaSlot)
                | none => Option.map Sum.inr
                    (dagCandidatePreferredSlot transitionFuel
                      finalWorkAnchorIndex
                      (finalWorkQ16IndexedState
                        (foldArmedUnderlyingState state)))) = none
              rw [alphaNone]
              simp [dagPreferred]
            rw [underlyingNone] at preferred
            simp at preferred
        | some dagSlot =>
            have underlying :
                (alphaFinalWorkQ16DagController transitionFuel
                  finalWorkAnchorIndex
                  (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                    (foldArmedUnderlyingState state) =
                  some (Sum.inr dagSlot) := by
              apply alpha_final_work_q16_preferred_of_dag
              · simpa [foldArmedAlphaZeroController] using
                  alphaPreferred
              · exact dagPreferred
            rw [underlying] at preferred
            have slotExact : slot = some (Sum.inr dagSlot) := by
              simpa using (Option.some.inj preferred).symm
            subst slot
            change dagSlot ∉ state.memory.2.2.usedSlots
            exact dag_candidate_preferred_slot_fresh transitionFuel
              finalWorkAnchorIndex
              (finalWorkQ16IndexedState (foldArmedUnderlyingState state))
              dagSlot dagPreferred

theorem fold_armed_complete_preferred_slot_used_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (answer : Digest256) (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (coherent : FoldArmedOuterCoherent foldExposureIndex state)
    (preferred :
      (foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).preferredSlot state = some slot) :
    foldArmedCompleteSlotUsed
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterAnswer transitionFuel state answer) slot := by
  by_cases atFold : state.memory.1 = false ∧
      state.exposureIndex = foldExposureIndex
  · have slotExact : slot = none := by
      have : some none = some slot := by
        simpa [foldArmedCompleteController, atFold] using preferred
      exact (Option.some.inj this).symm
    subst slot
    simp [foldArmedCompleteSlotUsed,
      IndexedUnifiedExposureController.afterAnswer,
      foldArmedCompleteController, atFold.2]
  · change
      (if state.memory.1 = false ∧ state.exposureIndex = foldExposureIndex then
        some none
      else
        ((alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
          (foldArmedAlphaZeroController transitionFuel)).preferredSlot
            (foldArmedUnderlyingState state)).map some) = some slot at preferred
    rw [if_neg atFold] at preferred
    cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
        (foldArmedAlphaIndexedState
          (alphaIndexedState (foldArmedUnderlyingState state))) with
    | some alphaSlot =>
        have underlying :
            (alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
              (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                (foldArmedUnderlyingState state) = some (Sum.inl alphaSlot) := by
          apply alpha_final_work_q16_preferred_of_alpha
          simpa [foldArmedAlphaZeroController] using
            alphaPreferred
        rw [underlying] at preferred
        have slotExact : slot = some (Sum.inl alphaSlot) := by
          simpa using (Option.some.inj preferred).symm
        subst slot
        change alphaSlot ∈
          ((foldArmedCompleteController transitionFuel foldExposureIndex
            finalWorkAnchorIndex).afterMemory state answer).2.1.alpha.usedSlots
        simp only [foldArmedCompleteController,
          alphaFinalWorkQ16DagController, foldArmedAlphaZeroController]
        have indexNe : state.exposureIndex ≠ foldExposureIndex := by
          intro equal
          apply atFold
          refine ⟨?_, equal⟩
          unfold FoldArmedOuterCoherent at coherent
          rw [equal] at coherent
          simpa using coherent
        rw [if_neg indexNe]
        change alphaSlot ∈
          (foldArmedAlphaAfterMemory transitionFuel
            (alphaIndexedState (foldArmedUnderlyingState state))
            answer).alpha.usedSlots
        rw [fold_armed_alpha_after_memory_used_slots, alphaPreferred]
        exact Finset.mem_insert_self alphaSlot _
    | none =>
        cases dagPreferred : dagCandidatePreferredSlot transitionFuel
            finalWorkAnchorIndex
            (finalWorkQ16IndexedState (foldArmedUnderlyingState state)) with
        | none =>
            have alphaNone :
                (foldArmedAlphaZeroController transitionFuel).preferredSlot
                    (alphaIndexedState (foldArmedUnderlyingState state)) =
                  none := by
              simpa [foldArmedAlphaZeroController] using
                alphaPreferred
            have underlyingNone :
                (alphaFinalWorkQ16DagController transitionFuel
                  finalWorkAnchorIndex
                  (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                    (foldArmedUnderlyingState state) = none := by
              change (match
                  (foldArmedAlphaZeroController transitionFuel).preferredSlot
                    (alphaIndexedState (foldArmedUnderlyingState state)) with
                | some alphaSlot => some (Sum.inl alphaSlot)
                | none => Option.map Sum.inr
                    (dagCandidatePreferredSlot transitionFuel
                      finalWorkAnchorIndex
                      (finalWorkQ16IndexedState
                        (foldArmedUnderlyingState state)))) = none
              rw [alphaNone]
              simp [dagPreferred]
            rw [underlyingNone] at preferred
            simp at preferred
        | some dagSlot =>
            have underlying :
                (alphaFinalWorkQ16DagController transitionFuel
                  finalWorkAnchorIndex
                  (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                    (foldArmedUnderlyingState state) =
                  some (Sum.inr dagSlot) := by
              apply alpha_final_work_q16_preferred_of_dag
              · simpa [foldArmedAlphaZeroController] using
                  alphaPreferred
              · exact dagPreferred
            rw [underlying] at preferred
            have slotExact : slot = some (Sum.inr dagSlot) := by
              simpa using (Option.some.inj preferred).symm
            subst slot
            change dagSlot ∈
              ((foldArmedCompleteController transitionFuel foldExposureIndex
                finalWorkAnchorIndex).afterMemory state answer).2.2.usedSlots
            simp only [foldArmedCompleteController,
              alphaFinalWorkQ16DagController]
            change dagSlot ∈
              (dagCandidateAfterMemory transitionFuel finalWorkAnchorIndex
                (finalWorkQ16IndexedState (foldArmedUnderlyingState state))
                answer).usedSlots
            rw [dag_candidate_after_memory_used_slots, dagPreferred]
            exact Finset.mem_insert_self dagSlot _

theorem fold_armed_complete_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory),
      FoldArmedOuterCoherent foldExposureIndex state →
      let controller := foldArmedCompleteController transitionFuel
        foldExposureIndex finalWorkAnchorIndex
      let labels := indexedControllerLabeledRecords transitionFuel controller
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          ¬ foldArmedCompleteSlotUsed state slot := by
  intro records
  induction records with
  | nil =>
      intro state _coherent
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state coherent
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalWorkAnchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextCoherent : FoldArmedOuterCoherent foldExposureIndex next := by
        simpa [next, controller] using
          fold_armed_outer_coherent_after_answer transitionFuel
            foldExposureIndex finalWorkAnchorIndex state record.answer coherent
      have tail := ih next nextCoherent
      have usedMono : ∀ slot, foldArmedCompleteSlotUsed state slot →
          foldArmedCompleteSlotUsed next slot := by
        intro slot used
        simpa [next, controller] using
          fold_armed_complete_slot_used_mono transitionFuel foldExposureIndex
            finalWorkAnchorIndex state record.answer slot used
      change
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller state
            (record :: records))).Nodup ∧
          ∀ slot ∈ namedTraceSlots
            (indexedControllerLabeledRecords transitionFuel controller state
              (record :: records)),
            ¬ foldArmedCompleteSlotUsed state slot
      cases preferred : controller.preferredSlot state with
      | none =>
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          exact And.intro tail.1 (fun slot member used =>
            tail.2 slot member (usedMono slot used))
      | some slot =>
          have slotFresh : ¬ foldArmedCompleteSlotUsed state slot :=
            fold_armed_complete_preferred_slot_fresh transitionFuel
              foldExposureIndex finalWorkAnchorIndex state slot (by
                simpa [controller] using preferred)
          have nextUsed : foldArmedCompleteSlotUsed next slot := by
            simpa [next, controller] using
              fold_armed_complete_preferred_slot_used_after_answer
                transitionFuel foldExposureIndex finalWorkAnchorIndex state
                  record.answer slot coherent
                    (by simpa [controller] using preferred)
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), ¬ foldArmedCompleteSlotUsed state candidate := by
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

theorem fold_armed_complete_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (coherent : FoldArmedOuterCoherent foldExposureIndex state) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (foldArmedCompleteController transitionFuel foldExposureIndex
          finalWorkAnchorIndex) state records)).Nodup :=
  (fold_armed_complete_labeled_records_nodup_and_avoid_initial
    transitionFuel foldExposureIndex finalWorkAnchorIndex records state
      coherent).1

#print axioms fold_armed_complete_slot_used_mono
#print axioms fold_armed_complete_preferred_slot_fresh
#print axioms fold_armed_complete_preferred_slot_used_after_answer
#print axioms fold_armed_complete_labeled_records_named_slots_nodup

end

end AspisK1.V7Tag73FoldArmedCompleteLabelsNodup
