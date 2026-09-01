import AspisFormal.K1.V7Tag73CausalMachineLabeledTraceRouting
import AspisFormal.K1.V7Tag73IndexedControllerTraceAlignment

/-!
# Literal record labels of an indexed exposure controller

This file records, for each already-generated scheduler record, the slot
chosen by an indexed controller immediately before that record's answer is
consumed.  The resulting list is definitionally a `MachineLabeledTrace` for
the same pre-answer machine compiled into the causal router.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73IndexedControllerLabeledRecords

open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- Chronological `(pre-answer label, answer)` pairs obtained by replaying a
record list through an indexed controller. -/
def indexedControllerLabeledRecords
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory) :
    IndexedUnifiedExposureState globalOracleCalls Memory →
      List UnifiedExposureRecord →
        List (Option Slot × Digest256)
  | _state, [] => []
  | state, record :: records =>
      (controller.preferredSlot state, record.answer) ::
        indexedControllerLabeledRecords transitionFuel controller
          (controller.afterAnswer transitionFuel state record.answer) records

@[simp] theorem indexed_controller_labeled_records_nil
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory) :
    indexedControllerLabeledRecords transitionFuel controller state [] = [] := by
  rfl

@[simp] theorem indexed_controller_labeled_records_cons
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (record : UnifiedExposureRecord) (records : List UnifiedExposureRecord) :
    indexedControllerLabeledRecords transitionFuel controller state
        (record :: records) =
      (controller.preferredSlot state, record.answer) ::
        indexedControllerLabeledRecords transitionFuel controller
          (controller.afterAnswer transitionFuel state record.answer) records := by
  rfl

/-- Forgetting labels recovers the literal record-answer list. -/
theorem indexed_controller_labeled_records_answers
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory) :
    ∀ (state : IndexedUnifiedExposureState globalOracleCalls Memory)
      (records : List UnifiedExposureRecord),
      (indexedControllerLabeledRecords transitionFuel controller state
        records).map Prod.snd = records.map UnifiedExposureRecord.answer := by
  intro state records
  induction records generalizing state with
  | nil => rfl
  | cons record records ih =>
      simp only [indexedControllerLabeledRecords, List.map_cons]
      rw [ih]

/-- The terminal state of the labelled execution is the ordinary indexed
record replay state. -/
theorem indexed_controller_labeled_records_form_trace
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory) :
    ∀ (state : IndexedUnifiedExposureState globalOracleCalls Memory)
      (records : List UnifiedExposureRecord),
      MachineLabeledTrace (controller.machine transitionFuel) state
        (indexedControllerLabeledRecords transitionFuel controller state
          records)
        (indexedStateAfterRecords transitionFuel controller records state) := by
  intro state records
  induction records generalizing state with
  | nil => exact .nil state
  | cons record records ih =>
      exact .cons rfl (ih
        (controller.afterAnswer transitionFuel state record.answer))

/-- Splitting the record list also splits the generated labels at the exact
controller state reached by the first segment. -/
theorem indexed_controller_labeled_records_append
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (first second : List UnifiedExposureRecord) :
    indexedControllerLabeledRecords transitionFuel controller state
        (first ++ second) =
      indexedControllerLabeledRecords transitionFuel controller state first ++
        indexedControllerLabeledRecords transitionFuel controller
          (indexedStateAfterRecords transitionFuel controller first state)
          second := by
  induction first generalizing state with
  | nil => rfl
  | cons record records ih =>
      simp only [List.cons_append, indexedControllerLabeledRecords,
        indexed_state_after_records_cons]
      rw [ih (controller.afterAnswer transitionFuel state record.answer)]

#print axioms indexedControllerLabeledRecords
#print axioms indexed_controller_labeled_records_answers
#print axioms indexed_controller_labeled_records_form_trace
#print axioms indexed_controller_labeled_records_append

end

end AspisK1.V7Tag73IndexedControllerLabeledRecords
