import AspisFormal.K1.V7Tag73ExactFinalWorkPairRootOrder
import AspisFormal.K1.V7Tag73IndexedControllerTraceAlignment

/-!
# Aligned record replay for the final-work/q16 controller

The production trace already identifies the exact pre-answer cursor at every
record.  This file packages that fact as a prefix-stable predicate and proves
the two monotone memory invariants needed between the accepted final-work pair:

* after the work input, unrelated records preserve `workSeen = true` and an
  absent q16 base; and
* after the nonce-absorb input, records before the work input preserve the
  exact q16 base while allowing the branch tracker to evolve.

These are deterministic controller facts.  They do not classify a raw SHA
input by its future protocol role.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73IndexedAlignedRecordReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- The pre-answer input carried by a nonpadding exposure record. -/
def causalInput? : UnifiedExposureRecord → Option ShaInput
  | .padding _ => none
  | .machineFresh _ input _ => some input
  | .forkOutput _ outputInput _ _ _ => some outputInput
  | .forkAdvance scheduled => some scheduled.advanceInput

/-- Replaying an appended record list is replaying the first list and then the
second. -/
theorem indexed_state_after_records_append
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory) :
    ∀ (first second : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls Memory),
      indexedStateAfterRecords transitionFuel controller (first ++ second)
          state =
        indexedStateAfterRecords transitionFuel controller second
          (indexedStateAfterRecords transitionFuel controller first state) := by
  intro first
  induction first with
  | nil =>
      intro second state
      rfl
  | cons head tail ih =>
      intro second state
      simp only [List.cons_append, indexed_state_after_records_cons]
      exact ih second (controller.afterAnswer transitionFuel state head.answer)

/-- Every selected record is the literal record emitted at the cursor reached
by replaying its strict prefix. -/
def IndexedRecordsAligned
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (records : List UnifiedExposureRecord) : Prop :=
  ∀ prior selected later,
    records = prior ++ selected :: later →
    unifiedRecordAtAnswer transitionFuel
        (indexedStateAfterRecords transitionFuel controller prior state).cursor
        selected.answer = selected

/-- A literal scheduler trace supplies aligned-record replay for any indexed
controller driven by the same cursor transition. -/
theorem indexed_records_aligned_of_trace
    {globalOracleCalls remaining : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (tape : FreshAnswerTape Digest256 remaining)
    (records : List UnifiedExposureRecord)
    (traceExact : runUnifiedExposureTrace transitionFuel remaining state.cursor
      tape = records) :
    IndexedRecordsAligned transitionFuel controller state records := by
  intro prior selected later decomposition
  exact trace_prefix_aligns_indexed_state transitionFuel controller prior later
    selected remaining state tape (traceExact.trans decomposition)

/-- Alignment restricts to a contiguous segment after replaying the preceding
prefix. -/
theorem indexed_records_aligned_segment
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (records preceding segment suffix : List UnifiedExposureRecord)
    (aligned : IndexedRecordsAligned transitionFuel controller state records)
    (decomposition : records = preceding ++ segment ++ suffix) :
    IndexedRecordsAligned transitionFuel controller
      (indexedStateAfterRecords transitionFuel controller preceding state)
      segment := by
  intro prior selected later segmentExact
  have fullExact : records =
      (preceding ++ prior) ++ selected :: (later ++ suffix) := by
    rw [decomposition, segmentExact]
    simp only [List.cons_append, List.append_assoc]
  have selectedAligned := aligned (preceding ++ prior) selected
    (later ++ suffix) fullExact
  rw [indexed_state_after_records_append] at selectedAligned
  exact selectedAligned

/-- A list consists solely of machine-fresh root coordinates, with either
source actor allowed. -/
def OnlyMachineFreshRecords (records : List UnifiedExposureRecord) : Prop :=
  ∀ record ∈ records,
    ∃ actor input answer, record = .machineFresh actor input answer

/-- Machine-only status restricts to a sublist in a known decomposition. -/
theorem only_machine_fresh_records_segment
    (records preceding segment suffix : List UnifiedExposureRecord)
    (onlyMachine : OnlyMachineFreshRecords records)
    (decomposition : records = preceding ++ segment ++ suffix) :
    OnlyMachineFreshRecords segment := by
  intro record member
  apply onlyMachine record
  rw [decomposition]
  simpa only [List.append_assoc] using
    List.mem_append_right preceding (List.mem_append_left suffix member)

/-- With work already observed but no q16 base, any aligned machine-fresh
segment that avoids the nonce-absorb input leaves the controller memory
unchanged. -/
theorem aligned_machine_records_preserve_work_without_base
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (key : RawFinalWorkKey)
    (branches : Fin 64 → RawQ16BranchPhase) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16CandidateMemory),
      IndexedRecordsAligned transitionFuel
          (finalWorkQ16CandidateController globalOracleCalls transitionFuel
            anchor) state records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records,
        causalInput? record ≠ some key.absorbInput) →
      state.memory = .tracked key true none branches →
      (indexedStateAfterRecords transitionFuel
        (finalWorkQ16CandidateController globalOracleCalls transitionFuel
          anchor) records state).memory =
        .tracked key true none branches := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _onlyMachine _avoids stateMemory
      simpa only [indexed_state_after_records_nil] using stateMemory
  | cons head tail ih =>
      intro state aligned onlyMachine avoids stateMemory
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have inputNe : input ≠ key.absorbInput := by
        intro equal
        apply avoids (.machineFresh actor input answer) (by simp)
        simp [causalInput?, equal]
      let controller := finalWorkQ16CandidateController globalOracleCalls
        transitionFuel anchor
      let next := controller.afterAnswer transitionFuel state answer
      have nextMemory : next.memory = .tracked key true none branches := by
        simp [next, controller, finalWorkQ16CandidateController,
          IndexedUnifiedExposureController.afterAnswer, candidateAfterMemory,
          stateMemory, inputExact, inputNe]
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have tailAvoids : ∀ record ∈ tail,
          causalInput? record ≠ some key.absorbInput := by
        intro record member
        exact avoids record (by simp [member])
      rw [indexed_state_after_records_cons]
      exact ih next tailAligned tailOnly tailAvoids nextMemory

/-- With the exact q16 base already retained, aligned machine-fresh records
before the work input preserve that base and `workSeen = false`; only the
branch map may evolve as adversarial prequeries are replayed. -/
theorem aligned_machine_records_preserve_base_without_work
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat)
    (key : RawFinalWorkKey) (base : Digest256) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16CandidateMemory)
      (branches : Fin 64 → RawQ16BranchPhase),
      IndexedRecordsAligned transitionFuel
          (finalWorkQ16CandidateController globalOracleCalls transitionFuel
            anchor) state records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records,
        causalInput? record ≠ some key.workInput) →
      state.memory = .tracked key false (some base) branches →
      ∃ laterBranches,
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16CandidateController globalOracleCalls transitionFuel
            anchor) records state).memory =
          .tracked key false (some base) laterBranches := by
  intro records
  induction records with
  | nil =>
      intro state branches _aligned _onlyMachine _avoids stateMemory
      exact ⟨branches, by
        simpa only [indexed_state_after_records_nil] using stateMemory⟩
  | cons head tail ih =>
      intro state branches aligned onlyMachine avoids stateMemory
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      have headAligned := aligned [] (.machineFresh actor input answer) tail
        (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have inputNe : input ≠ key.workInput := by
        intro equal
        apply avoids (.machineFresh actor input answer) (by simp)
        simp [causalInput?, equal]
      let controller := finalWorkQ16CandidateController globalOracleCalls
        transitionFuel anchor
      let next := controller.afterAnswer transitionFuel state answer
      let nextBranches := updateRawQ16Branches base branches input answer
      have nextMemory : next.memory =
          .tracked key false (some base) nextBranches := by
        simp [next, nextBranches, controller,
          finalWorkQ16CandidateController,
          IndexedUnifiedExposureController.afterAnswer, candidateAfterMemory,
          stateMemory, inputExact, inputNe]
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have tailAvoids : ∀ record ∈ tail,
          causalInput? record ≠ some key.workInput := by
        intro record member
        exact avoids record (by simp [member])
      rw [indexed_state_after_records_cons]
      exact ih next nextBranches tailAligned tailOnly tailAvoids nextMemory

#print axioms indexed_state_after_records_append
#print axioms IndexedRecordsAligned
#print axioms indexed_records_aligned_of_trace
#print axioms indexed_records_aligned_segment
#print axioms aligned_machine_records_preserve_work_without_base
#print axioms aligned_machine_records_preserve_base_without_work

end

end AspisK1.V7Tag73IndexedAlignedRecordReplay
