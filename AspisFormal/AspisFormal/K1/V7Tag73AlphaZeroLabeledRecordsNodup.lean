import AspisFormal.K1.V7Tag73AlphaZeroCausalController
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-!
# One-shot alpha-zero label invariant

The four alpha slots are consumed at most once for every possible answer
stream.  This is a controller invariant, not an honest-trace assumption.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaZeroLabeledRecordsNodup

open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The alpha controller never selects an already-consumed one-shot slot. -/
theorem alpha_zero_preferred_slot_fresh
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory) (slot : Fin 4)
    (preferred : alphaZeroPreferredSlot transitionFuel state = some slot) :
    slot ∉ state.memory.usedSlots := by
  unfold alphaZeroPreferredSlot at preferred
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simp [inputExact] at preferred
  | some input =>
      simp only [inputExact] at preferred
      cases output : alphaZeroOutputSlot? state.memory.producers input with
      | none => simp [output] at preferred
      | some outputSlot =>
          by_cases used : outputSlot ∈ state.memory.usedSlots
          · simp [output, used] at preferred
          · have slotExact : outputSlot = slot := by
              have equal : some outputSlot = some slot := by
                simpa [output, used] using preferred
              exact Option.some.inj equal
            simpa [← slotExact] using used

/-- Named alpha labels are duplicate-free and avoid every slot already used
at the beginning of the replay segment. -/
theorem alpha_zero_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      let labels := indexedControllerLabeledRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels, slot ∉ state.memory.usedSlots := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state
      let controller := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : state.memory.usedSlots ⊆ next.memory.usedSlots := by
        intro slot member
        change slot ∈
          (alphaZeroAfterMemory transitionFuel boundaryIndex state
            record.answer).usedSlots
        rw [alpha_zero_after_memory_used_slots]
        cases preferred : alphaZeroPreferredSlot transitionFuel state with
        | none => exact member
        | some selected => exact Finset.mem_insert_of_mem member
      cases preferred : controller.preferredSlot state with
      | none =>
          have preferred' : alphaZeroPreferredSlot transitionFuel state =
              none := by
            simpa [controller, alphaZeroCausalController] using preferred
          simpa [indexedControllerLabeledRecords, controller, next, preferred,
            preferred', namedTraceSlots] using
            And.intro tail.1 (fun slot member used =>
              tail.2 slot member (usedMono used))
      | some slot =>
          have preferred' : alphaZeroPreferredSlot transitionFuel state =
              some slot := by
            simpa [controller, alphaZeroCausalController] using preferred
          have slotFresh : slot ∉ state.memory.usedSlots :=
            alpha_zero_preferred_slot_fresh transitionFuel state slot preferred'
          have nextUsed : slot ∈ next.memory.usedSlots := by
            change slot ∈
              (alphaZeroAfterMemory transitionFuel boundaryIndex state
                record.answer).usedSlots
            rw [alpha_zero_after_memory_used_slots, preferred']
            exact Finset.mem_insert_self slot state.memory.usedSlots
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), candidate ∉ state.memory.usedSlots := by
            intro candidate member used
            exact tail.2 candidate member (usedMono used)
          simpa [indexedControllerLabeledRecords, controller, next, preferred,
            preferred', namedTraceSlots] using
            And.intro (List.nodup_cons.mpr ⟨slotNotTail, tail.1⟩)
              ⟨slotFresh, tailAvoidsInitial⟩

theorem alpha_zero_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) state
        records)).Nodup :=
  (alpha_zero_labeled_records_nodup_and_avoid_initial transitionFuel
    boundaryIndex records state).1

#print axioms alpha_zero_preferred_slot_fresh
#print axioms alpha_zero_labeled_records_nodup_and_avoid_initial
#print axioms alpha_zero_labeled_records_named_slots_nodup

end


end AspisK1.V7Tag73AlphaZeroLabeledRecordsNodup
