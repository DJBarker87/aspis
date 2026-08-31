import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords
import AspisFormal.K1.V7Tag73Q16CandidateParserExact
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Causal-DAG final-work/q16 controller

The q16 duplex is a dependency DAG, not a sequential transcript from an
arbitrary prover's point of view.  Once an advance answer is known, later
block queries can be exposed before the earlier sibling output.  This
controller therefore tracks every causally produced block digest separately.

Each candidate absorb produces block zero.  Each advance query whose input is
derived from a known producer creates the next block producer immediately.
Output queries only consume the corresponding named slot; they do not gate
the next block.  A monotone `usedSlots` set makes every emitted final-work/q16
label one-shot by construction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalDagFinalWorkQ16Controller

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16CandidateParserExact
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- One digest that causally determines a q16 output/advance sibling pair. -/
structure Q16DagProducer where
  digest : Digest256
  slot : Q16DigestSlot
  sourceInput : ShaInput
  deriving DecidableEq, Repr

/-- The pair key selected at the trial anchor.  `workSeen` is independent of
q16 progress because an adversary may expose q16 coordinates between the
nonce absorb and the verifier's work lookup. -/
inductive FinalWorkDagAnchor where
  | inactive
  | tracked (key : RawFinalWorkKey) (workSeen : Bool)
  deriving DecidableEq, Repr

/-- Complete causal memory for one exposure-indexed trial. -/
structure FinalWorkQ16DagMemory where
  anchor : FinalWorkDagAnchor
  q16Base : Option Digest256
  producers : List Q16DagProducer
  usedSlots : Finset FinalWorkQ16DigestSlot
  deriving DecidableEq

def inactiveDagMemory : FinalWorkQ16DagMemory :=
  { anchor := .inactive
    q16Base := none
    producers := []
    usedSlots := ∅ }

/-- A known producer labels its literal squeeze input.  The first match is
deterministic; clean-root answer uniqueness later proves the source producer
is the unique match. -/
def q16DagOutputSlot? (producers : List Q16DagProducer)
    (input : ShaInput) : Option Q16DigestSlot :=
  (producers.find? fun producer =>
    decide (input = bytes producer.digest ++ [domSqueeze])).map
      Q16DagProducer.slot

/-- An advance input derived from a known block creates the following block
producer, if that following block remains inside the deployed eight-block
cap. -/
def q16DagAdvancedSlot? (producers : List Q16DagProducer)
    (input : ShaInput) : Option Q16DigestSlot :=
  match producers.find? fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance]) with
  | none => none
  | some producer =>
      if bounded : producer.slot.2.val + 1 < 8 then
        some (producer.slot.1, ⟨producer.slot.2.val + 1, bounded⟩)
      else
        none

/-- A producer with a digest unique in the inventory is the deterministic
output-input match selected by the executable scan. -/
theorem q16_dag_output_slot_of_digest_nodup
    (producer : Q16DagProducer) :
    ∀ (producers : List Q16DagProducer),
      (producers.map Q16DagProducer.digest).Nodup →
      producer ∈ producers →
      q16DagOutputSlot? producers
          (bytes producer.digest ++ [domSqueeze]) = some producer.slot := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup member
      have nodup' : head.digest ∉
            tail.map Q16DagProducer.digest ∧
          (tail.map Q16DagProducer.digest).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      have tailNodup := nodup'.2
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        simp [q16DagOutputSlot?]
      · have digestNe : producer.digest ≠ head.digest := by
          intro equal
          apply nodup'.1
          rw [List.mem_map]
          exact ⟨producer, member, equal⟩
        have bytesNe : bytes producer.digest ≠ bytes head.digest := by
          intro equal
          exact digestNe (digest_bytes_injective equal)
        have reduce : q16DagOutputSlot? (head :: tail)
              (bytes producer.digest ++ [domSqueeze]) =
            q16DagOutputSlot? tail
              (bytes producer.digest ++ [domSqueeze]) := by
          simp [q16DagOutputSlot?, bytesNe]
        rw [reduce]
        exact ih tailNodup member

/-- The analogous deterministic scan for an advance-derived next slot. -/
theorem q16_dag_advanced_slot_of_digest_nodup
    (producer : Q16DagProducer)
    (bounded : producer.slot.2.val + 1 < 8) :
    ∀ (producers : List Q16DagProducer),
      (producers.map Q16DagProducer.digest).Nodup →
      producer ∈ producers →
      q16DagAdvancedSlot? producers
          (bytes producer.digest ++ [domAdvance]) =
        some (producer.slot.1,
          ⟨producer.slot.2.val + 1, bounded⟩) := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup member
      have nodup' : head.digest ∉
            tail.map Q16DagProducer.digest ∧
          (tail.map Q16DagProducer.digest).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      have tailNodup := nodup'.2
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        simp [q16DagAdvancedSlot?, bounded]
      · have digestNe : producer.digest ≠ head.digest := by
          intro equal
          apply nodup'.1
          rw [List.mem_map]
          exact ⟨producer, member, equal⟩
        have bytesNe : bytes producer.digest ≠ bytes head.digest := by
          intro equal
          exact digestNe (digest_bytes_injective equal)
        have reduce : q16DagAdvancedSlot? (head :: tail)
              (bytes producer.digest ++ [domAdvance]) =
            q16DagAdvancedSlot? tail
              (bytes producer.digest ++ [domAdvance]) := by
          simp [q16DagAdvancedSlot?, bytesNe]
        rw [reduce]
        exact ih tailNodup member

/-- The slot produced by the current causal edge, if any. -/
def q16DagProducedSlot? (base : Digest256)
    (producers : List Q16DagProducer) (input : ShaInput) :
    Option Q16DigestSlot :=
  match q16CandidateOfBaseInput? base input with
  | some counter => some (counter, ⟨0, by omega⟩)
  | none => q16DagAdvancedSlot? producers input

/-- Update only the causal producer inventory.  Candidate absorbs depend on
the already exposed q16 base; advance answers extend their branch without
waiting for the sibling output. -/
def updateQ16DagProducers (base : Digest256)
    (producers : List Q16DagProducer) (input : ShaInput) (answer : Digest256) :
    List Q16DagProducer :=
  match q16DagProducedSlot? base producers input with
  | some slot => producers ++
      [Q16DagProducer.mk answer slot input]
  | none => producers

theorem update_q16_dag_producers_eq_or_append
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (answer : Digest256) :
    updateQ16DagProducers base producers input answer = producers ∨
      ∃ slot, updateQ16DagProducers base producers input answer =
        producers ++
          [Q16DagProducer.mk answer slot input] := by
  unfold updateQ16DagProducers
  cases produced : q16DagProducedSlot? base producers input with
  | none => exact Or.inl rfl
  | some slot => exact Or.inr ⟨slot, rfl⟩

theorem update_q16_dag_producers_prefix
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (answer : Digest256) :
    producers <+: updateQ16DagProducers base producers input answer := by
  rcases update_q16_dag_producers_eq_or_append base producers input answer with
    unchanged | ⟨slot, appended⟩
  · rw [unchanged]
  · rw [appended]
    exact List.prefix_append _ _

theorem update_q16_dag_producers_new_digest
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (answer : Digest256)
    (producer : Q16DagProducer)
    (member : producer ∈ updateQ16DagProducers base producers input answer) :
    producer ∈ producers ∨ producer.digest = answer := by
  rcases update_q16_dag_producers_eq_or_append base producers input answer with
    unchanged | ⟨slot, appended⟩
  · rw [unchanged] at member
    exact Or.inl member
  · rw [appended, List.mem_append] at member
    rcases member with old | added
    · exact Or.inl old
    · simp only [List.mem_singleton] at added
      exact Or.inr (by rw [added])

/-- Raw pre-answer label before enforcing one-shot use. -/
def dagRawPreferredSlot (anchorIndex exposureIndex : Nat)
    (memory : FinalWorkQ16DagMemory) (input : ShaInput) :
    Option FinalWorkQ16DigestSlot :=
  match memory.anchor with
  | .inactive =>
      if exposureIndex = anchorIndex then
        match rawFinalWorkKeyOfWorkInput? input with
        | some _key => some none
        | none => none
      else
        none
  | .tracked key workSeen =>
      if workSeen = false ∧ input = key.workInput then
        some none
      else
        (q16DagOutputSlot? memory.producers input).map some

/-- A named slot is emitted only on its first causal exposure. -/
def dagPreferredSlotForInput (anchorIndex exposureIndex : Nat)
    (memory : FinalWorkQ16DagMemory) (input : ShaInput) :
    Option FinalWorkQ16DigestSlot :=
  match dagRawPreferredSlot anchorIndex exposureIndex memory input with
  | some slot => if slot ∈ memory.usedSlots then none else some slot
  | none => none

/-- Advance the anchor, q16 base, and producer DAG while leaving the monotone
used-slot component untouched. -/
def dagCoreMemoryAfterInput (anchorIndex exposureIndex : Nat)
    (memory : FinalWorkQ16DagMemory) (input : ShaInput) (answer : Digest256) :
    FinalWorkQ16DagMemory :=
  match memory.anchor with
  | .inactive =>
      if exposureIndex = anchorIndex then
        match rawFinalWorkKeyOfWorkInput? input with
        | some key =>
            { anchor := .tracked key true
              q16Base := none
              producers := memory.producers
              usedSlots := memory.usedSlots }
        | none =>
            match rawFinalWorkKeyOfAbsorbInput? input with
            | some key =>
                { anchor := .tracked key false
                  q16Base := some answer
                  producers := memory.producers
                  usedSlots := memory.usedSlots }
            | none => memory
      else
        memory
  | .tracked key workSeen =>
      let nextWorkSeen := workSeen || decide (input = key.workInput)
      match memory.q16Base with
      | none =>
          if input = key.absorbInput then
            { anchor := .tracked key nextWorkSeen
              q16Base := some answer
              producers := memory.producers
              usedSlots := memory.usedSlots }
          else
            { anchor := .tracked key nextWorkSeen
              q16Base := none
              producers := memory.producers
              usedSlots := memory.usedSlots }
      | some base =>
          { anchor := .tracked key nextWorkSeen
            q16Base := some base
            producers := updateQ16DagProducers base memory.producers input answer
            usedSlots := memory.usedSlots }

/-- Causal producers are append-only across one raw memory step. -/
theorem dag_core_memory_producers_prefix
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256) :
    memory.producers <+:
      (dagCoreMemoryAfterInput anchorIndex exposureIndex memory input answer).producers := by
  cases anchorExact : memory.anchor with
  | inactive =>
      simp only [dagCoreMemoryAfterInput, anchorExact]
      split
      · split
        · exact List.prefix_refl _
        · split <;> exact List.prefix_refl _
      · exact List.prefix_refl _
  | tracked key workSeen =>
      simp only [dagCoreMemoryAfterInput, anchorExact]
      cases baseExact : memory.q16Base with
      | none =>
          simp only [baseExact]
          split <;> exact List.prefix_refl _
      | some base =>
          simp only [baseExact]
          simpa using
            update_q16_dag_producers_prefix base memory.producers input answer

/-- Advance all causal memory and mark the pre-answer label as consumed. -/
def dagMemoryAfterInput (anchorIndex exposureIndex : Nat)
    (memory : FinalWorkQ16DagMemory) (input : ShaInput) (answer : Digest256) :
    FinalWorkQ16DagMemory :=
  let core :=
    dagCoreMemoryAfterInput anchorIndex exposureIndex memory input answer
  { core with
    usedSlots :=
      match dagPreferredSlotForInput anchorIndex exposureIndex memory input with
      | some slot => insert slot memory.usedSlots
      | none => memory.usedSlots }

/-- Marking a label does not disturb the append-only producer inventory. -/
theorem dag_memory_producers_prefix
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256) :
    memory.producers <+:
      (dagMemoryAfterInput anchorIndex exposureIndex memory input answer).producers := by
  exact dag_core_memory_producers_prefix anchorIndex exposureIndex memory input answer

/-- One memory step either keeps the producer inventory or appends exactly
the current answer with the causally derived slot. -/
theorem dag_memory_producers_eq_or_append
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256) :
    (dagMemoryAfterInput anchorIndex exposureIndex memory input answer).producers =
        memory.producers ∨
      ∃ (slot : Q16DigestSlot),
        (dagMemoryAfterInput anchorIndex exposureIndex memory input answer).producers =
          memory.producers ++
            [Q16DagProducer.mk answer slot input] := by
  unfold dagMemoryAfterInput
  cases anchorExact : memory.anchor with
  | inactive =>
      simp only [dagCoreMemoryAfterInput, anchorExact]
      split
      · split
        · exact Or.inl rfl
        · split <;> exact Or.inl rfl
      · exact Or.inl rfl
  | tracked key workSeen =>
      simp only [dagCoreMemoryAfterInput, anchorExact]
      cases baseExact : memory.q16Base with
      | none =>
          simp only [baseExact]
          split <;> exact Or.inl rfl
      | some base =>
          simp only [baseExact]
          simpa using
            update_q16_dag_producers_eq_or_append base memory.producers input
              answer

def dagCandidatePreferredSlot
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory) : Option FinalWorkQ16DigestSlot :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | some input =>
      dagPreferredSlotForInput anchorIndex state.exposureIndex state.memory input
  | none => none

def dagCandidateAfterMemory
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256) : FinalWorkQ16DagMemory :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | some input =>
      dagMemoryAfterInput anchorIndex state.exposureIndex state.memory input
        answer
  | none => state.memory

/-- Executable exposure-indexed controller for the causal DAG. -/
def finalWorkQ16DagController
    (globalOracleCalls transitionFuel anchorIndex : Nat) :
    IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot FinalWorkQ16DagMemory where
  preferredSlot := dagCandidatePreferredSlot transitionFuel anchorIndex
  afterMemory := dagCandidateAfterMemory transitionFuel anchorIndex

@[simp] theorem dag_preferred_slot_for_input_mem_iff
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (slot : FinalWorkQ16DigestSlot)
    (preferred : dagPreferredSlotForInput anchorIndex exposureIndex memory input =
      some slot) :
    slot ∉ memory.usedSlots := by
  unfold dagPreferredSlotForInput at preferred
  cases raw : dagRawPreferredSlot anchorIndex exposureIndex memory input with
  | none => simp [raw] at preferred
  | some rawSlot =>
      simp only [raw] at preferred
      split at preferred
      · simp_all
      · rename_i fresh
        exact (Option.some.inj preferred) ▸ fresh

@[simp] theorem dag_memory_after_input_used_slots
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256) :
    (dagMemoryAfterInput anchorIndex exposureIndex memory input answer).usedSlots =
      match dagPreferredSlotForInput anchorIndex exposureIndex memory input with
      | some slot => insert slot memory.usedSlots
      | none => memory.usedSlots := by
  rfl

theorem dag_memory_used_slots_mono
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256) :
    memory.usedSlots ⊆
      (dagMemoryAfterInput anchorIndex exposureIndex memory input answer).usedSlots := by
  rw [dag_memory_after_input_used_slots]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.rfl

theorem dag_candidate_preferred_slot_fresh
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (slot : FinalWorkQ16DigestSlot)
    (preferred : dagCandidatePreferredSlot transitionFuel anchorIndex state =
      some slot) :
    slot ∉ state.memory.usedSlots := by
  unfold dagCandidatePreferredSlot at preferred
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simp [inputExact] at preferred
  | some input =>
      exact dag_preferred_slot_for_input_mem_iff anchorIndex
        state.exposureIndex state.memory input slot (by
          simpa [inputExact] using preferred)

theorem dag_candidate_after_memory_used_slots
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256) :
    (dagCandidateAfterMemory transitionFuel anchorIndex state answer).usedSlots =
      match dagCandidatePreferredSlot transitionFuel anchorIndex state with
      | some slot => insert slot state.memory.usedSlots
      | none => state.memory.usedSlots := by
  unfold dagCandidateAfterMemory dagCandidatePreferredSlot
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor <;>
    simp [dag_memory_after_input_used_slots]

theorem dag_candidate_memory_used_slots_mono
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256) :
    state.memory.usedSlots ⊆
      (dagCandidateAfterMemory transitionFuel anchorIndex state answer).usedSlots := by
  rw [dag_candidate_after_memory_used_slots]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.rfl

/-- One indexed controller step can only append causal producers. -/
theorem dag_candidate_memory_producers_prefix
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256) :
    state.memory.producers <+:
      (dagCandidateAfterMemory transitionFuel anchorIndex state answer).producers := by
  unfold dagCandidateAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => exact List.prefix_refl _
  | some input =>
      exact dag_memory_producers_prefix anchorIndex state.exposureIndex
        state.memory input answer

/-- Indexed form of the exact keep-or-single-append transition. -/
theorem dag_candidate_memory_producers_eq_or_append
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256) :
    (dagCandidateAfterMemory transitionFuel anchorIndex state answer).producers =
        state.memory.producers ∨
      ∃ (slot : Q16DigestSlot),
        (dagCandidateAfterMemory transitionFuel anchorIndex state answer).producers =
          state.memory.producers ++
            [Q16DagProducer.mk answer slot
              (Option.getD
                (unifiedInputBeforeAnswer? transitionFuel state.cursor) [])] := by
  unfold dagCandidateAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => exact Or.inl rfl
  | some input =>
      exact dag_memory_producers_eq_or_append anchorIndex state.exposureIndex
        state.memory input answer

/-- A fresh answer preserves uniqueness of producer digests. -/
theorem dag_candidate_memory_producer_digests_nodup
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory)
    (answer : Digest256)
    (currentNodup : (state.memory.producers.map Q16DagProducer.digest).Nodup)
    (answerFresh : answer ∉ state.memory.producers.map Q16DagProducer.digest) :
    ((dagCandidateAfterMemory transitionFuel anchorIndex state answer).producers.map
      Q16DagProducer.digest).Nodup := by
  rcases dag_candidate_memory_producers_eq_or_append transitionFuel anchorIndex
      state answer with unchanged | ⟨slot, appended⟩
  · simpa [unchanged] using currentNodup
  · rw [appended, List.map_append]
    simp only [List.map_singleton]
    rw [List.nodup_append]
    refine ⟨currentNodup, by simp, ?_⟩
    intro prior priorMember singleton singletonMember
    simp only [List.mem_singleton] at singletonMember
    subst singleton
    exact fun equal => answerFresh (equal ▸ priorMember)

/-- Exact-root answer uniqueness implies producer-digest uniqueness throughout
the full causal-DAG replay. -/
theorem dag_indexed_state_producer_digests_nodup
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      (records.map UnifiedExposureRecord.answer).Nodup →
      (state.memory.producers.map Q16DagProducer.digest).Nodup →
      (∀ producer ∈ state.memory.producers,
        producer.digest ∉ records.map UnifiedExposureRecord.answer) →
      ((indexedStateAfterRecords transitionFuel
        (finalWorkQ16DagController globalOracleCalls transitionFuel anchorIndex)
        records state).memory.producers.map Q16DagProducer.digest).Nodup := by
  intro records
  induction records with
  | nil =>
      intro state _recordsNodup producerNodup _disjoint
      simpa only [indexed_state_after_records_nil] using producerNodup
  | cons record records ih =>
      intro state recordsNodup producerNodup disjoint
      have splitNodup := List.nodup_cons.mp recordsNodup
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have answerFresh : record.answer ∉
          state.memory.producers.map Q16DagProducer.digest := by
        intro answerMember
        obtain ⟨producer, producerMember, producerDigest⟩ :=
          List.mem_map.mp answerMember
        apply disjoint producer producerMember
        simp only [List.map_cons, List.mem_cons]
        exact Or.inl producerDigest
      have nextNodup :
          (next.memory.producers.map Q16DagProducer.digest).Nodup := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          dag_candidate_memory_producer_digests_nodup transitionFuel
            anchorIndex state record.answer producerNodup answerFresh
      have nextDisjoint : ∀ producer ∈ next.memory.producers,
          producer.digest ∉ records.map UnifiedExposureRecord.answer := by
        intro producer producerMember tailMember
        change producer ∈
          (dagCandidateAfterMemory transitionFuel anchorIndex state
            record.answer).producers at producerMember
        rcases dag_candidate_memory_producers_eq_or_append transitionFuel
            anchorIndex state record.answer with unchanged | ⟨slot, appended⟩
        · rw [unchanged] at producerMember
          exact disjoint producer producerMember (by
            simpa only [List.map_cons] using
              List.mem_cons_of_mem record.answer tailMember)
        · rw [appended, List.mem_append] at producerMember
          rcases producerMember with old | added
          · exact disjoint producer old (by
              simpa only [List.map_cons] using
                List.mem_cons_of_mem record.answer tailMember)
          · simp only [List.mem_singleton] at added
            subst producer
            exact splitNodup.1 tailMember
      rw [indexed_state_after_records_cons]
      exact ih next splitNodup.2 nextNodup nextDisjoint

/-- Producer monotonicity lifts through an arbitrary literal record replay. -/
theorem dag_indexed_state_producers_prefix
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      state.memory.producers <+:
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel anchorIndex)
          records state).memory.producers := by
  intro records
  induction records with
  | nil =>
      intro state
      exact List.prefix_refl _
  | cons record records ih =>
      intro state
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have oneStep : state.memory.producers <+: next.memory.producers := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          dag_candidate_memory_producers_prefix transitionFuel anchorIndex state
            record.answer
      rw [indexed_state_after_records_cons]
      exact oneStep.trans (ih next)

/-- The monotone used-set contains exactly the initial slots together with
the labels emitted by the replayed record prefix. -/
theorem dag_indexed_state_used_slots_eq_initial_union_labels
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      (indexedStateAfterRecords transitionFuel
        (finalWorkQ16DagController globalOracleCalls transitionFuel anchorIndex)
        records state).memory.usedSlots =
      state.memory.usedSlots ∪
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel
            (finalWorkQ16DagController globalOracleCalls transitionFuel
              anchorIndex) state records)).toFinset := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords, namedTraceSlots]
  | cons record records ih =>
      intro state
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      rw [indexed_state_after_records_cons]
      rw [ih next]
      have nextUsed : next.memory.usedSlots =
          match controller.preferredSlot state with
          | some slot => insert slot state.memory.usedSlots
          | none => state.memory.usedSlots := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          dag_candidate_after_memory_used_slots transitionFuel anchorIndex
            state record.answer
      cases preferred : controller.preferredSlot state with
      | none =>
          rw [nextUsed]
          simp [indexedControllerLabeledRecords, next, controller, preferred]
      | some slot =>
          rw [nextUsed]
          simp [indexedControllerLabeledRecords, next, controller, preferred,
            Finset.insert_union]

/-- Every slot newly present after a record prefix was emitted at one literal
earlier pre-answer state in that prefix. -/
theorem dag_used_slot_has_prior_record
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory)
      (slot : FinalWorkQ16DigestSlot),
      slot ∉ state.memory.usedSlots →
      slot ∈
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) records state).memory.usedSlots →
      ∃ prior record later,
        records = prior ++ record :: later ∧
        (finalWorkQ16DagController globalOracleCalls transitionFuel
          anchorIndex).preferredSlot
          (indexedStateAfterRecords transitionFuel
            (finalWorkQ16DagController globalOracleCalls transitionFuel
              anchorIndex) prior state) = some slot := by
  intro records
  induction records with
  | nil =>
      intro state slot fresh used
      simp only [indexed_state_after_records_nil] at used
      exact (fresh used).elim
  | cons head tail ih =>
      intro state slot fresh used
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state head.answer
      have tailUsed : slot ∈
          (indexedStateAfterRecords transitionFuel controller tail next).memory.usedSlots := by
        simpa [controller, next, indexed_state_after_records_cons] using used
      cases preferred : controller.preferredSlot state with
      | none =>
          have preferred' : dagCandidatePreferredSlot transitionFuel
              anchorIndex state = none := by
            simpa [controller, finalWorkQ16DagController] using preferred
          have nextFresh : slot ∉ next.memory.usedSlots := by
            have nextUsed := dag_candidate_after_memory_used_slots
              transitionFuel anchorIndex state head.answer
            rw [show next.memory.usedSlots = state.memory.usedSlots by
              simpa [next, controller, finalWorkQ16DagController,
                IndexedUnifiedExposureController.afterAnswer, preferred'] using
                nextUsed]
            exact fresh
          obtain ⟨prior, record, later, decomposition, selected⟩ :=
            ih next slot nextFresh tailUsed
          refine ⟨head :: prior, record, later, ?_, ?_⟩
          · simp [decomposition]
          · simpa [controller, next, indexed_state_after_records_cons] using
              selected
      | some current =>
          have preferred' : dagCandidatePreferredSlot transitionFuel
              anchorIndex state = some current := by
            simpa [controller, finalWorkQ16DagController] using preferred
          by_cases currentExact : current = slot
          · subst current
            exact ⟨[], head, tail, by simp, by
              simpa [controller, indexed_state_after_records_nil] using
                preferred⟩
          · have nextFresh : slot ∉ next.memory.usedSlots := by
              have nextUsed := dag_candidate_after_memory_used_slots
                transitionFuel anchorIndex state head.answer
              rw [show next.memory.usedSlots =
                  insert current state.memory.usedSlots by
                simpa [next, controller, finalWorkQ16DagController,
                  IndexedUnifiedExposureController.afterAnswer, preferred']
                  using nextUsed]
              have slotNe : slot ≠ current := fun equal =>
                currentExact equal.symm
              simp [fresh, slotNe]
            obtain ⟨prior, record, later, decomposition, selected⟩ :=
              ih next slot nextFresh tailUsed
            refine ⟨head :: prior, record, later, ?_, ?_⟩
            · simp [decomposition]
            · simpa [controller, next, indexed_state_after_records_cons] using
                selected

/-- Every named label emitted by the causal-DAG controller is distinct, for
every answer stream.  This is an executable controller invariant rather than
a source-trace assumption.  The stronger second conclusion records freshness
relative to all slots used before the segment. -/
theorem dag_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      let labels := indexedControllerLabeledRecords transitionFuel
        (finalWorkQ16DagController globalOracleCalls transitionFuel anchorIndex)
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels, slot ∉ state.memory.usedSlots := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : state.memory.usedSlots ⊆ next.memory.usedSlots := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer] using
          dag_candidate_memory_used_slots_mono transitionFuel anchorIndex state
            record.answer
      cases preferred : controller.preferredSlot state with
      | none =>
          simpa [indexedControllerLabeledRecords, controller, next, preferred,
            namedTraceSlots] using
            And.intro tail.1 (fun slot member used =>
              tail.2 slot member (usedMono used))
      | some slot =>
          have preferred' : dagCandidatePreferredSlot transitionFuel
              anchorIndex state = some slot := by
            simpa [controller, finalWorkQ16DagController] using preferred
          have slotFresh : slot ∉ state.memory.usedSlots := by
            exact dag_candidate_preferred_slot_fresh transitionFuel anchorIndex
              state slot preferred'
          have nextUsed : slot ∈ next.memory.usedSlots := by
            change slot ∈
              (dagCandidateAfterMemory transitionFuel anchorIndex state
                record.answer).usedSlots
            rw [dag_candidate_after_memory_used_slots, preferred']
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
            namedTraceSlots] using
            And.intro (List.nodup_cons.mpr ⟨slotNotTail, tail.1⟩)
              ⟨slotFresh, tailAvoidsInitial⟩

theorem dag_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FinalWorkQ16DagMemory) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (finalWorkQ16DagController globalOracleCalls transitionFuel anchorIndex)
        state records)).Nodup :=
  (dag_labeled_records_nodup_and_avoid_initial transitionFuel anchorIndex
    records state).1

#print axioms Q16DagProducer
#print axioms q16DagOutputSlot?
#print axioms q16DagAdvancedSlot?
#print axioms updateQ16DagProducers
#print axioms dagRawPreferredSlot
#print axioms dagPreferredSlotForInput
#print axioms dagCoreMemoryAfterInput
#print axioms dagMemoryAfterInput
#print axioms finalWorkQ16DagController
#print axioms dag_preferred_slot_for_input_mem_iff
#print axioms dag_memory_after_input_used_slots
#print axioms dag_memory_used_slots_mono
#print axioms dag_candidate_preferred_slot_fresh
#print axioms dag_candidate_after_memory_used_slots
#print axioms dag_candidate_memory_used_slots_mono
#print axioms dag_memory_producers_eq_or_append
#print axioms dag_candidate_memory_producers_prefix
#print axioms dag_candidate_memory_producers_eq_or_append
#print axioms dag_candidate_memory_producer_digests_nodup
#print axioms dag_indexed_state_producer_digests_nodup
#print axioms dag_indexed_state_producers_prefix
#print axioms dag_indexed_state_used_slots_eq_initial_union_labels
#print axioms dag_used_slot_has_prior_record
#print axioms dag_labeled_records_nodup_and_avoid_initial
#print axioms dag_labeled_records_named_slots_nodup

end

end AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
