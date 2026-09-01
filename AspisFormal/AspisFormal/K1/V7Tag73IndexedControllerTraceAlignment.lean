import AspisFormal.K1.V7Tag73ExactFinalWorkEarliestExposure

/-!
# Exact trace alignment for an indexed pre-answer controller

The causal final-work/q16 controller is driven by the same cursor transition
as the production unified-exposure trace.  This module makes that statement
prefix-sensitive: replaying the answers of an actual flat-trace prefix reaches
the exact cursor whose next record is the selected coordinate.

It also proves the protocol-specific fact needed at the selected chronological
anchor.  Starting from inactive memory at exposure zero, the final-work/q16
controller remains inactive throughout any prefix whose length is exactly the
anchor.  Thus the selected record, rather than an earlier answer or a
retrospective role assignment, performs the first state transition.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73IndexedControllerTraceAlignment

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FinalWorkEarliestExposure
open AspisK1.V7Tag73ExactFinalWorkEarliestExposure
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

@[simp] theorem unified_record_at_answer_answer
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (answer : Digest256) :
    (unifiedRecordAtAnswer transitionFuel cursor answer).answer = answer := by
  unfold unifiedRecordAtAnswer
  cases request : seekUnifiedExposure transitionFuel cursor <;> rfl

/-- Replay a literal record prefix through an indexed controller.  Only each
record's already-exposed answer is consumed; the next slot is always chosen
from the state before that answer. -/
def indexedStateAfterRecords
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory) :
    List UnifiedExposureRecord →
      IndexedUnifiedExposureState globalOracleCalls Memory →
      IndexedUnifiedExposureState globalOracleCalls Memory
  | [], state => state
  | record :: records, state =>
      indexedStateAfterRecords transitionFuel controller records
        (controller.afterAnswer transitionFuel state record.answer)

@[simp] theorem indexed_state_after_records_nil
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory) :
    indexedStateAfterRecords transitionFuel controller [] state = state := by
  rfl

@[simp] theorem indexed_state_after_records_cons
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (record : UnifiedExposureRecord) (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory) :
    indexedStateAfterRecords transitionFuel controller (record :: records)
        state =
      indexedStateAfterRecords transitionFuel controller records
        (controller.afterAnswer transitionFuel state record.answer) := by
  rfl

theorem indexed_state_after_records_exposure_index
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls Memory),
      (indexedStateAfterRecords transitionFuel controller records state).exposureIndex =
        state.exposureIndex + records.length := by
  intro records
  induction records with
  | nil =>
      intro state
      rfl
  | cons record records ih =>
      intro state
      rw [indexed_state_after_records_cons, ih]
      simp only [indexed_after_answer_exposure_index, List.length_cons]
      omega

/-- A trace decomposition determines the controller's exact pre-answer cursor
at the selected record after replaying precisely the preceding answers. -/
theorem trace_prefix_aligns_indexed_state
    {globalOracleCalls : Nat} {Slot : Type} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory) :
    ∀ (prior later : List UnifiedExposureRecord)
      (selected : UnifiedExposureRecord) (remaining : Nat)
      (state : IndexedUnifiedExposureState globalOracleCalls Memory)
      (tape : FreshAnswerTape Digest256 remaining),
      runUnifiedExposureTrace transitionFuel remaining state.cursor tape =
          prior ++ selected :: later →
        unifiedRecordAtAnswer transitionFuel
            (indexedStateAfterRecords transitionFuel controller prior state).cursor
            selected.answer = selected := by
  intro prior
  induction prior with
  | nil =>
      intro later selected remaining state tape traceExact
      cases remaining with
      | zero =>
          simp [runUnifiedExposureTrace] at traceExact
      | succ remaining =>
          rcases tape with ⟨answer, tail⟩
          rw [run_unified_exposure_trace_succ_eq_record_and_cursor] at traceExact
          simp only [List.nil_append, List.cons.injEq] at traceExact
          have answerExact : answer = selected.answer := by
            have exactAnswer := congrArg UnifiedExposureRecord.answer
              traceExact.1
            simpa only [unified_record_at_answer_answer] using exactAnswer
          subst answer
          simpa only [indexed_state_after_records_nil] using traceExact.1
  | cons priorHead prior ih =>
      intro later selected remaining state tape traceExact
      cases remaining with
      | zero =>
          simp [runUnifiedExposureTrace] at traceExact
      | succ remaining =>
          rcases tape with ⟨answer, tail⟩
          rw [run_unified_exposure_trace_succ_eq_record_and_cursor] at traceExact
          simp only [List.cons_append, List.cons.injEq] at traceExact
          have answerExact : answer = priorHead.answer := by
            have exactAnswer := congrArg UnifiedExposureRecord.answer
              traceExact.1
            simpa only [unified_record_at_answer_answer] using exactAnswer
          subst answer
          have tailExact := traceExact.2
          change runUnifiedExposureTrace transitionFuel remaining
              (controller.afterAnswer transitionFuel state priorHead.answer).cursor tail =
            prior ++ selected :: later at tailExact
          simpa only [indexed_state_after_records_cons] using
            ih later selected remaining
              (controller.afterAnswer transitionFuel state priorHead.answer)
              tail tailExact

/-- A machine record selected by the aligned trace exposes its literal input
at the controller's pre-answer cursor. -/
theorem aligned_machine_record_has_exact_input
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (recordExact : unifiedRecordAtAnswer transitionFuel cursor answer =
      .machineFresh actor input answer) :
    unifiedInputBeforeAnswer? transitionFuel cursor = some input := by
  unfold unifiedRecordAtAnswer at recordExact
  unfold unifiedInputBeforeAnswer?
  generalize requestExact : seekUnifiedExposure transitionFuel cursor = request
  cases request <;> simp_all

/-- Before its fixed anchor, the candidate controller cannot activate: every
earlier state has a strictly smaller exposure ordinal. -/
theorem candidate_memory_stays_inactive_before_anchor
    {globalOracleCalls : Nat}
    (transitionFuel anchor : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16CandidateMemory),
      state.exposureIndex + records.length = anchor →
      state.memory = inactiveCandidateMemory →
      (indexedStateAfterRecords transitionFuel
        (finalWorkQ16CandidateController globalOracleCalls transitionFuel
          anchor) records state).memory = inactiveCandidateMemory := by
  intro records
  induction records with
  | nil =>
      intro state _anchorExact inactive
      simpa only [indexed_state_after_records_nil] using inactive
  | cons record records ih =>
      intro state anchorExact inactive
      have beforeAnchor : state.exposureIndex ≠ anchor := by
        intro equal
        rw [equal] at anchorExact
        simp only [List.length_cons] at anchorExact
        omega
      let next :=
        (finalWorkQ16CandidateController globalOracleCalls transitionFuel
          anchor).afterAnswer transitionFuel state record.answer
      have nextInactive : next.memory = inactiveCandidateMemory := by
        simp only [next, finalWorkQ16CandidateController,
          IndexedUnifiedExposureController.afterAnswer]
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor <;>
          simp [candidateAfterMemory, inputExact, inactive, beforeAnchor,
            inactiveCandidateMemory]
      have nextAnchor : next.exposureIndex + records.length = anchor := by
        simp only [next, indexed_after_answer_exposure_index,
          List.length_cons] at anchorExact ⊢
        omega
      rw [indexed_state_after_records_cons]
      exact ih next nextAnchor nextInactive

/-! ## Literal earliest-pair anchor -/

/-- An actual earliest literal final-work pair record is reached with the
candidate controller still inactive and its exposure counter equal to the
selected chronological index.  The current pre-answer cursor sees the exact
deployed input, and consuming the selected answer performs the corresponding
first controller transition.

This theorem is deterministic.  It does not assume that final work succeeds
or that the q16 forest is bad; those source facts are attached to the exact
answers by the subsequent production cover. -/
theorem earliest_literal_pair_aligns_candidate_controller
    {globalOracleCalls transitionFuel remaining index : Nat}
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining)
    (records : List UnifiedExposureRecord)
    (digest : Digest256) (nonce : NonceBytes)
    (earliest : EarliestFinalWorkPairOccurrence
      (literalFinalWorkKey digest nonce) records index)
    (traceExact : runUnifiedExposureTrace transitionFuel remaining cursor tape =
      records) :
    ∃ prior selected later reached actor answer,
      records = prior ++ selected :: later ∧
      prior.length = index ∧
      reached = indexedStateAfterRecords transitionFuel
        (finalWorkQ16CandidateController globalOracleCalls transitionFuel index)
        prior
        { exposureIndex := 0
          cursor := cursor
          memory := inactiveCandidateMemory } ∧
      reached.exposureIndex = index ∧
      reached.memory = inactiveCandidateMemory ∧
      ((selected = .machineFresh actor
            (bytes digest ++ [domGrind] ++ bytes nonce) answer ∧
          unifiedInputBeforeAnswer? transitionFuel reached.cursor =
            some (bytes digest ++ [domGrind] ++ bytes nonce) ∧
          candidatePreferredSlot transitionFuel index reached = some none ∧
          candidateAfterMemory transitionFuel index reached answer =
            .tracked (literalFinalWorkKey digest nonce) true none
              emptyRawQ16Branches) ∨
        (selected = .machineFresh actor
            (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce)
              answer ∧
          unifiedInputBeforeAnswer? transitionFuel reached.cursor =
            some (bytes digest ++
              [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) ∧
          candidateAfterMemory transitionFuel index reached answer =
            .tracked (literalFinalWorkKey digest nonce) false (some answer)
              emptyRawQ16Branches)) := by
  obtain ⟨prior, selected, later, recordsExact, lengthExact, pair⟩ :=
    earliest_final_work_pair_trace_decomposition earliest
  let controller :=
    finalWorkQ16CandidateController globalOracleCalls transitionFuel index
  let initial : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16CandidateMemory :=
    { exposureIndex := 0
      cursor := cursor
      memory := inactiveCandidateMemory }
  let reached :=
    indexedStateAfterRecords transitionFuel controller prior initial
  have selectedAligned :
      unifiedRecordAtAnswer transitionFuel reached.cursor selected.answer =
        selected := by
    exact trace_prefix_aligns_indexed_state transitionFuel controller prior
      later selected remaining initial tape (traceExact.trans recordsExact)
  have reachedIndex : reached.exposureIndex = index := by
    calc
      reached.exposureIndex = initial.exposureIndex + prior.length := by
        exact indexed_state_after_records_exposure_index transitionFuel
          controller prior initial
      _ = index := by simp only [initial, lengthExact, Nat.zero_add]
  have reachedInactive : reached.memory = inactiveCandidateMemory := by
    apply candidate_memory_stays_inactive_before_anchor transitionFuel index
      prior initial
    · simp only [initial, lengthExact, Nat.zero_add]
    · rfl
  obtain ⟨actor, answer, selectedWork | selectedAbsorb⟩ :=
    final_work_pair_record_cases (literalFinalWorkKey digest nonce) selected pair
  · have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
        some (bytes digest ++ [domGrind] ++ bytes nonce) := by
      apply aligned_machine_record_has_exact_input transitionFuel reached.cursor
        actor (bytes digest ++ [domGrind] ++ bytes nonce) answer
      have recordExact := selectedAligned
      rw [selectedWork] at recordExact
      simpa only [UnifiedExposureRecord.answer,
        literal_final_work_key_work_input] using recordExact
    have selectedWorkLiteral : selected = .machineFresh actor
        (bytes digest ++ [domGrind] ++ bytes nonce) answer := by
      simpa only [literal_final_work_key_work_input] using selectedWork
    have slotExact : candidatePreferredSlot transitionFuel index reached =
        some none := by
      simp [candidatePreferredSlot, inputExact, reachedIndex, reachedInactive,
        inactiveCandidateMemory]
    have afterExact : candidateAfterMemory transitionFuel index reached answer =
        .tracked (literalFinalWorkKey digest nonce) true none
          emptyRawQ16Branches := by
      simp [candidateAfterMemory, inputExact, reachedIndex, reachedInactive,
        inactiveCandidateMemory]
    exact ⟨prior, selected, later, reached, actor, answer, recordsExact,
      lengthExact, rfl, reachedIndex, reachedInactive, Or.inl
        ⟨selectedWorkLiteral, inputExact, slotExact, afterExact⟩⟩
  · have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
        some (bytes digest ++
          [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) := by
      apply aligned_machine_record_has_exact_input transitionFuel reached.cursor
        actor
        (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) answer
      have recordExact := selectedAligned
      rw [selectedAbsorb] at recordExact
      simpa only [UnifiedExposureRecord.answer,
        literal_final_work_key_absorb_input] using recordExact
    have selectedAbsorbLiteral : selected = .machineFresh actor
        (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce)
          answer := by
      simpa only [literal_final_work_key_absorb_input] using selectedAbsorb
    have afterExact : candidateAfterMemory transitionFuel index reached answer =
        .tracked (literalFinalWorkKey digest nonce) false (some answer)
          emptyRawQ16Branches := by
      simp [candidateAfterMemory, inputExact, reachedIndex, reachedInactive,
        inactiveCandidateMemory]
    exact ⟨prior, selected, later, reached, actor, answer, recordsExact,
      lengthExact, rfl, reachedIndex, reachedInactive, Or.inr
        ⟨selectedAbsorbLiteral, inputExact, afterExact⟩⟩

/-! ## Exact accepted-answer anchor -/

/-- Complete deterministic anchor object for the exact accepted work/q16-base
record pair. -/
def ExactLiteralPairControllerAnchor
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (cursor : UnifiedExposureCursor globalOracleCalls)
    (records : List UnifiedExposureRecord)
    (digest : Digest256) (nonce : NonceBytes)
    (workAnswer q16Base : Digest256) (index : Nat) : Prop :=
  ∃ prior selected later reached actor,
    records = prior ++ selected :: later ∧
    prior.length = index ∧
    reached = indexedStateAfterRecords transitionFuel
      (finalWorkQ16CandidateController globalOracleCalls transitionFuel index)
      prior
      { exposureIndex := 0
        cursor := cursor
        memory := inactiveCandidateMemory } ∧
    reached.exposureIndex = index ∧
    reached.memory = inactiveCandidateMemory ∧
    ((selected = .machineFresh actor
          (bytes digest ++ [domGrind] ++ bytes nonce) workAnswer ∧
        unifiedInputBeforeAnswer? transitionFuel reached.cursor =
          some (bytes digest ++ [domGrind] ++ bytes nonce) ∧
        candidatePreferredSlot transitionFuel index reached = some none ∧
        candidateAfterMemory transitionFuel index reached workAnswer =
          .tracked (literalFinalWorkKey digest nonce) true none
            emptyRawQ16Branches) ∨
      (selected = .machineFresh actor
          (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce)
            q16Base ∧
        unifiedInputBeforeAnswer? transitionFuel reached.cursor =
          some (bytes digest ++
            [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) ∧
        candidateAfterMemory transitionFuel index reached q16Base =
          .tracked (literalFinalWorkKey digest nonce) false (some q16Base)
            emptyRawQ16Branches))

/-- The earlier of the two exact accepted records constructs the complete
pre-answer controller anchor.  No record-answer uniqueness premise is needed. -/
theorem earliest_exact_literal_pair_aligns_candidate_controller
    {globalOracleCalls transitionFuel remaining index : Nat}
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining)
    (records : List UnifiedExposureRecord)
    (digest : Digest256) (nonce : NonceBytes)
    (workAnswer q16Base : Digest256)
    (earliest : EarliestExactFinalWorkPairOccurrence
      (literalFinalWorkKey digest nonce) workAnswer q16Base records index)
    (traceExact : runUnifiedExposureTrace transitionFuel remaining cursor tape =
      records) :
    ExactLiteralPairControllerAnchor transitionFuel cursor records digest nonce
      workAnswer q16Base index := by
  obtain ⟨prior, selected, later, recordsExact, lengthExact, pair⟩ :=
    earliest_exact_pair_trace_decomposition earliest
  let controller :=
    finalWorkQ16CandidateController globalOracleCalls transitionFuel index
  let initial : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16CandidateMemory :=
    { exposureIndex := 0
      cursor := cursor
      memory := inactiveCandidateMemory }
  let reached :=
    indexedStateAfterRecords transitionFuel controller prior initial
  have selectedAligned :
      unifiedRecordAtAnswer transitionFuel reached.cursor selected.answer =
        selected := by
    exact trace_prefix_aligns_indexed_state transitionFuel controller prior
      later selected remaining initial tape (traceExact.trans recordsExact)
  have reachedIndex : reached.exposureIndex = index := by
    calc
      reached.exposureIndex = initial.exposureIndex + prior.length := by
        exact indexed_state_after_records_exposure_index transitionFuel
          controller prior initial
      _ = index := by simp only [initial, lengthExact, Nat.zero_add]
  have reachedInactive : reached.memory = inactiveCandidateMemory := by
    apply candidate_memory_stays_inactive_before_anchor transitionFuel index
      prior initial
    · simp only [initial, lengthExact, Nat.zero_add]
    · rfl
  obtain ⟨actor, selectedWork | selectedAbsorb⟩ :=
    exact_final_work_pair_record_cases (literalFinalWorkKey digest nonce)
      workAnswer q16Base selected pair
  · have selectedWorkLiteral : selected = .machineFresh actor
        (bytes digest ++ [domGrind] ++ bytes nonce) workAnswer := by
      simpa only [literal_final_work_key_work_input] using selectedWork
    have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
        some (bytes digest ++ [domGrind] ++ bytes nonce) := by
      apply aligned_machine_record_has_exact_input transitionFuel reached.cursor
        actor (bytes digest ++ [domGrind] ++ bytes nonce) workAnswer
      have recordExact := selectedAligned
      rw [selectedWorkLiteral] at recordExact
      simpa only [UnifiedExposureRecord.answer] using recordExact
    have slotExact : candidatePreferredSlot transitionFuel index reached =
        some none := by
      simp [candidatePreferredSlot, inputExact, reachedIndex, reachedInactive,
        inactiveCandidateMemory]
    have afterExact :
        candidateAfterMemory transitionFuel index reached workAnswer =
          .tracked (literalFinalWorkKey digest nonce) true none
            emptyRawQ16Branches := by
      simp [candidateAfterMemory, inputExact, reachedIndex, reachedInactive,
        inactiveCandidateMemory]
    exact ⟨prior, selected, later, reached, actor, recordsExact, lengthExact,
      rfl, reachedIndex, reachedInactive, Or.inl
        ⟨selectedWorkLiteral, inputExact, slotExact, afterExact⟩⟩
  · have selectedAbsorbLiteral : selected = .machineFresh actor
        (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce)
          q16Base := by
      simpa only [literal_final_work_key_absorb_input] using selectedAbsorb
    have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
        some (bytes digest ++
          [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) := by
      apply aligned_machine_record_has_exact_input transitionFuel reached.cursor
        actor
        (bytes digest ++ [domAbsorb, finalWorkNonceLabel] ++ bytes nonce) q16Base
      have recordExact := selectedAligned
      rw [selectedAbsorbLiteral] at recordExact
      simpa only [UnifiedExposureRecord.answer] using recordExact
    have afterExact :
        candidateAfterMemory transitionFuel index reached q16Base =
          .tracked (literalFinalWorkKey digest nonce) false (some q16Base)
            emptyRawQ16Branches := by
      simp [candidateAfterMemory, inputExact, reachedIndex, reachedInactive,
        inactiveCandidateMemory]
    exact ⟨prior, selected, later, reached, actor, recordsExact, lengthExact,
      rfl, reachedIndex, reachedInactive, Or.inr
        ⟨selectedAbsorbLiteral, inputExact, afterExact⟩⟩

#print axioms unified_record_at_answer_answer
#print axioms indexed_state_after_records_exposure_index
#print axioms trace_prefix_aligns_indexed_state
#print axioms aligned_machine_record_has_exact_input
#print axioms candidate_memory_stays_inactive_before_anchor
#print axioms earliest_literal_pair_aligns_candidate_controller
#print axioms earliest_exact_literal_pair_aligns_candidate_controller

end

end AspisK1.V7Tag73IndexedControllerTraceAlignment
