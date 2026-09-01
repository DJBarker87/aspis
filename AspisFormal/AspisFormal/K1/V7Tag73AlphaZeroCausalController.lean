import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16ControllerComposition
import AspisFormal.K1.V7Tag73IndexedControllerTraceAlignment
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Pre-answer causal controller for the four alpha-zero blocks

The alpha-zero sampler starts after the fold-nonce absorption.  Its output
and advance siblings may be exposed in either order, and later advance-derived
queries may occur before an earlier output.  This controller therefore stores
the digest produced by the literal fold-nonce boundary and extends a producer
chain whenever an advance answer is exposed.

Every output slot is selected from the current cursor before its answer is
seen.  A source theorem must still identify the chosen boundary exposure with
the accepted fold-nonce absorption and prove the usual clean-trace producer
uniqueness; this file supplies the executable controller, not that conclusion.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaZeroCausalController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SqueezeInputStateInjectivity

noncomputable section

/-! ## Literal fold-nonce boundary grammar -/

/-- Recognize the deployed fold-nonce absorption by its exact byte length,
absorb domain, and payload label.  The preceding digest and nonce remain
opaque byte strings. -/
def isAlphaZeroBoundaryInput (input : ShaInput) : Bool :=
  input.length = 43 &&
    input[32]? = some domAbsorb &&
    input[33]? = some foldWorkNonceLabel

@[simp] theorem literal_fold_nonce_is_alpha_zero_boundary
    (digest : Digest256) (nonce : NonceBytes) :
    isAlphaZeroBoundaryInput
        (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++ bytes nonce) =
      true := by
  simp [isAlphaZeroBoundaryInput]

/-! ## Causal producer inventory -/

structure AlphaZeroProducer where
  digest : Digest256
  block : Fin 4
  sourceInput : ShaInput
  deriving DecidableEq, Repr

structure AlphaZeroControllerMemory where
  producers : List AlphaZeroProducer
  usedSlots : Finset (Fin 4)
  deriving DecidableEq

def inactiveAlphaZeroMemory : AlphaZeroControllerMemory :=
  { producers := []
    usedSlots := ∅ }

/-- Deterministically locate the output sibling of a known alpha producer. -/
def alphaZeroOutputSlot? (producers : List AlphaZeroProducer)
    (input : ShaInput) : Option (Fin 4) :=
  (producers.find? fun producer =>
    decide (input = bytes producer.digest ++ [domSqueeze])).map
      AlphaZeroProducer.block

/-- An advance sibling produces the next alpha block when it remains inside
the deployed four-block cap. -/
def alphaZeroAdvancedSlot? (producers : List AlphaZeroProducer)
    (input : ShaInput) : Option (Fin 4) :=
  match producers.find? fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance]) with
  | none => none
  | some producer =>
      if bounded : producer.block.val + 1 < 4 then
        some ⟨producer.block.val + 1, bounded⟩
      else
        none

/-- A producer whose digest is unique in the inventory is the deterministic
output sibling selected by the executable scan. -/
theorem alpha_zero_output_slot_of_digest_nodup
    (producer : AlphaZeroProducer) :
    ∀ (producers : List AlphaZeroProducer),
      (producers.map AlphaZeroProducer.digest).Nodup →
      producer ∈ producers →
      alphaZeroOutputSlot? producers
          (bytes producer.digest ++ [domSqueeze]) = some producer.block := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup member
      have nodup' : head.digest ∉
            tail.map AlphaZeroProducer.digest ∧
          (tail.map AlphaZeroProducer.digest).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      have tailNodup := nodup'.2
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        simp [alphaZeroOutputSlot?]
      · have digestNe : producer.digest ≠ head.digest := by
          intro equal
          apply nodup'.1
          rw [List.mem_map]
          exact ⟨producer, member, equal⟩
        have bytesNe : bytes producer.digest ≠ bytes head.digest := by
          intro equal
          exact digestNe (digest_bytes_injective equal)
        have reduce : alphaZeroOutputSlot? (head :: tail)
              (bytes producer.digest ++ [domSqueeze]) =
            alphaZeroOutputSlot? tail
              (bytes producer.digest ++ [domSqueeze]) := by
          simp [alphaZeroOutputSlot?, bytesNe]
        rw [reduce]
        exact ih tailNodup member

/-- The analogous deterministic scan for the advance-derived next block. -/
theorem alpha_zero_advanced_slot_of_digest_nodup
    (producer : AlphaZeroProducer)
    (bounded : producer.block.val + 1 < 4) :
    ∀ (producers : List AlphaZeroProducer),
      (producers.map AlphaZeroProducer.digest).Nodup →
      producer ∈ producers →
      alphaZeroAdvancedSlot? producers
          (bytes producer.digest ++ [domAdvance]) =
        some ⟨producer.block.val + 1, bounded⟩ := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup member
      have nodup' : head.digest ∉
            tail.map AlphaZeroProducer.digest ∧
          (tail.map AlphaZeroProducer.digest).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      have tailNodup := nodup'.2
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        simp [alphaZeroAdvancedSlot?, bounded]
      · have digestNe : producer.digest ≠ head.digest := by
          intro equal
          apply nodup'.1
          rw [List.mem_map]
          exact ⟨producer, member, equal⟩
        have bytesNe : bytes producer.digest ≠ bytes head.digest := by
          intro equal
          exact digestNe (digest_bytes_injective equal)
        have reduce : alphaZeroAdvancedSlot? (head :: tail)
              (bytes producer.digest ++ [domAdvance]) =
            alphaZeroAdvancedSlot? tail
              (bytes producer.digest ++ [domAdvance]) := by
          simp [alphaZeroAdvancedSlot?, bytesNe]
        rw [reduce]
        exact ih tailNodup member

def updateAlphaZeroProducers (producers : List AlphaZeroProducer)
    (input : ShaInput) (answer : Digest256) : List AlphaZeroProducer :=
  match alphaZeroAdvancedSlot? producers input with
  | none => producers
  | some block => producers ++
      [{ digest := answer, block := block, sourceInput := input }]

theorem update_alpha_zero_producers_eq_or_append
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256) :
    updateAlphaZeroProducers producers input answer = producers ∨
      ∃ block, updateAlphaZeroProducers producers input answer =
        producers ++
          [{ digest := answer, block := block, sourceInput := input }] := by
  unfold updateAlphaZeroProducers
  cases advanced : alphaZeroAdvancedSlot? producers input with
  | none => exact Or.inl rfl
  | some block => exact Or.inr ⟨block, rfl⟩

theorem update_alpha_zero_producers_prefix
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256) :
    producers <+: updateAlphaZeroProducers producers input answer := by
  rcases update_alpha_zero_producers_eq_or_append producers input answer with
    unchanged | ⟨block, appended⟩
  · rw [unchanged]
  · rw [appended]
    exact List.prefix_append _ _

/-- Every newly appended producer carries exactly the current root answer and
its literal source input. -/
theorem update_alpha_zero_producers_new_digest
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256) (producer : AlphaZeroProducer)
    (member : producer ∈ updateAlphaZeroProducers producers input answer) :
    producer ∈ producers ∨
      (producer.digest = answer ∧ producer.sourceInput = input) := by
  rcases update_alpha_zero_producers_eq_or_append producers input answer with
    unchanged | ⟨block, appended⟩
  · rw [unchanged] at member
    exact Or.inl member
  · rw [appended, List.mem_append] at member
    rcases member with old | added
    · exact Or.inl old
    · simp only [List.mem_singleton] at added
      subst producer
      exact Or.inr ⟨rfl, rfl⟩

/-! ## Indexed pre-answer controller -/

def alphaZeroPreferredSlot
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory) : Option (Fin 4) :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => none
  | some input =>
      match alphaZeroOutputSlot? state.memory.producers input with
      | none => none
      | some slot =>
          if slot ∈ state.memory.usedSlots then none else some slot

/-- Update after the answer.  At the selected boundary exposure the answer
becomes block zero's producer.  Otherwise an advance answer may extend the
chain.  An output slot chosen before this answer becomes permanently used. -/
def alphaZeroAfterMemory
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256) : AlphaZeroControllerMemory :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => state.memory
  | some input =>
      let nextUsed :=
        match alphaZeroPreferredSlot transitionFuel state with
        | none => state.memory.usedSlots
        | some slot => insert slot state.memory.usedSlots
      let nextProducers :=
        if state.exposureIndex = boundaryIndex &&
            isAlphaZeroBoundaryInput input then
          [{ digest := answer, block := 0, sourceInput := input }]
        else
          updateAlphaZeroProducers state.memory.producers input answer
      { producers := nextProducers, usedSlots := nextUsed }

def alphaZeroCausalController
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256 (Fin 4)
      AlphaZeroControllerMemory where
  preferredSlot := alphaZeroPreferredSlot transitionFuel
  afterMemory := alphaZeroAfterMemory transitionFuel boundaryIndex

@[simp] theorem alpha_zero_controller_preferred
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory) :
    (alphaZeroCausalController transitionFuel boundaryIndex).preferredSlot
        state = alphaZeroPreferredSlot transitionFuel state := by
  rfl

@[simp] theorem alpha_zero_controller_after_memory
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256) :
    (alphaZeroCausalController transitionFuel boundaryIndex).afterMemory
        state answer =
      alphaZeroAfterMemory transitionFuel boundaryIndex state answer := by
  rfl

/-- At the indexed literal boundary, the returned digest is installed as the
unique initial producer for block zero. -/
theorem alpha_zero_after_boundary_has_block_zero_producer
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (indexExact : state.exposureIndex = boundaryIndex)
    (boundary : isAlphaZeroBoundaryInput input = true) :
    (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers =
      [{ digest := answer, block := 0, sourceInput := input }] := by
  simp [alphaZeroAfterMemory, inputExact, indexExact, boundary]

/-- A known unused producer labels its output sibling before the answer. -/
theorem alpha_zero_preferred_of_output_match
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput) (slot : Fin 4)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (matched : alphaZeroOutputSlot? state.memory.producers input = some slot)
    (unused : slot ∉ state.memory.usedSlots) :
    alphaZeroPreferredSlot transitionFuel state = some slot := by
  simp [alphaZeroPreferredSlot, inputExact, matched, unused]

/-- Once selected, a slot is inserted into the monotone used set on the same
answer transition. -/
theorem alpha_zero_selected_slot_used_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput) (answer : Digest256) (slot : Fin 4)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (selected : alphaZeroPreferredSlot transitionFuel state = some slot) :
    slot ∈ (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).usedSlots := by
  simp [alphaZeroAfterMemory, inputExact, selected]

/-- Every producer retained after one answer was either already present or
was created by that answer and its literal pre-answer input.  This includes
the unique boundary reset. -/
theorem alpha_zero_after_memory_member_old_or_current
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput) (answer : Digest256) (producer : AlphaZeroProducer)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (member : producer ∈
      (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers) :
    producer ∈ state.memory.producers ∨
      (producer.sourceInput = input ∧ producer.digest = answer) := by
  unfold alphaZeroAfterMemory at member
  rw [inputExact] at member
  change producer ∈
    (if (state.exposureIndex = boundaryIndex &&
        isAlphaZeroBoundaryInput input) then
      [{ digest := answer, block := 0, sourceInput := input }]
    else updateAlphaZeroProducers state.memory.producers input answer) at member
  split at member
  · simp only [List.mem_singleton] at member
    subst producer
    exact Or.inr ⟨rfl, rfl⟩
  · rcases update_alpha_zero_producers_new_digest state.memory.producers input
      answer producer member with old | ⟨digestExact, sourceExact⟩
    · exact Or.inl old
    · exact Or.inr ⟨sourceExact, digestExact⟩

/-- A fresh root answer preserves producer-digest uniqueness, including at
the unique boundary reset where the inventory becomes a singleton. -/
theorem alpha_zero_after_memory_producer_digests_nodup
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (currentNodup :
      (state.memory.producers.map AlphaZeroProducer.digest).Nodup)
    (answerFresh :
      answer ∉ state.memory.producers.map AlphaZeroProducer.digest) :
    ((alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers.map
      AlphaZeroProducer.digest).Nodup := by
  unfold alphaZeroAfterMemory
  rw [inputExact]
  change
    ((if (state.exposureIndex = boundaryIndex &&
        isAlphaZeroBoundaryInput input) then
      [{ digest := answer, block := 0, sourceInput := input }]
    else updateAlphaZeroProducers state.memory.producers input answer).map
      AlphaZeroProducer.digest).Nodup
  split
  · simp
  · rcases update_alpha_zero_producers_eq_or_append state.memory.producers
      input answer with unchanged | ⟨block, appended⟩
    · simpa [unchanged] using currentNodup
    · rw [appended, List.map_append]
      simp only [List.map_singleton]
      rw [List.nodup_append]
      refine ⟨currentNodup, by simp, ?_⟩
      intro prior priorMember singleton singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst singleton
      exact fun equal => answerFresh (equal ▸ priorMember)

/-- A fresh advance sibling below a known producer appends the exact next
block producer, provided the unique boundary reset is already behind us. -/
theorem alpha_zero_memory_after_advance_contains_producer
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput) (answer : Digest256) (parent : AlphaZeroProducer)
    (bounded : parent.block.val + 1 < 4)
    (indexNe : state.exposureIndex ≠ boundaryIndex)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (inputIsAdvance : input = bytes parent.digest ++ [domAdvance])
    (digestNodup :
      (state.memory.producers.map AlphaZeroProducer.digest).Nodup)
    (parentMember : parent ∈ state.memory.producers) :
    ({ digest := answer, block := ⟨parent.block.val + 1, bounded⟩, sourceInput := input } : AlphaZeroProducer) ∈
        (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers := by
  have advanced : alphaZeroAdvancedSlot? state.memory.producers input =
      some ⟨parent.block.val + 1, bounded⟩ := by
    rw [inputIsAdvance]
    exact alpha_zero_advanced_slot_of_digest_nodup parent bounded
      state.memory.producers digestNodup parentMember
  unfold alphaZeroAfterMemory
  rw [inputExact]
  change ({ digest := answer, block := ⟨parent.block.val + 1, bounded⟩, sourceInput := input } : AlphaZeroProducer) ∈
    (if (state.exposureIndex = boundaryIndex &&
        isAlphaZeroBoundaryInput input) then
      [{ digest := answer, block := 0, sourceInput := input }]
    else updateAlphaZeroProducers state.memory.producers input answer)
  have boundaryFalse :
      (state.exposureIndex = boundaryIndex &&
        isAlphaZeroBoundaryInput input) = false := by
    simp [indexNe]
  rw [if_neg (Bool.eq_false_iff.mp boundaryFalse)]
  unfold updateAlphaZeroProducers
  rw [advanced]
  simp

/-- Once the unique boundary record has been consumed, every later memory
step preserves the existing producer inventory as a prefix. -/
theorem alpha_zero_after_memory_producers_prefix_of_index_ne
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256)
    (indexNe : state.exposureIndex ≠ boundaryIndex) :
    state.memory.producers <+:
      (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers := by
  unfold alphaZeroAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => exact List.prefix_refl _
  | some input =>
      simp only [inputExact]
      have boundaryFalse :
          (state.exposureIndex = boundaryIndex &&
            isAlphaZeroBoundaryInput input) = false := by
        simp [indexNe]
      rw [if_neg]
      exact update_alpha_zero_producers_prefix state.memory.producers input
        answer
      exact Bool.eq_false_iff.mp boundaryFalse

/-- Away from the unique boundary reset, one controller step either preserves
the inventory or appends exactly the current answer/source pair. -/
theorem alpha_zero_after_memory_producers_eq_or_append_of_index_ne
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256)
    (indexNe : state.exposureIndex ≠ boundaryIndex) :
    (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers =
        state.memory.producers ∨
      ∃ block,
        (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers =
          state.memory.producers ++
            [{ digest := answer, block := block, sourceInput := Option.getD
                (unifiedInputBeforeAnswer? transitionFuel state.cursor) [] }] := by
  unfold alphaZeroAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => exact Or.inl rfl
  | some input =>
      simp only [inputExact]
      have boundaryFalse :
          (state.exposureIndex = boundaryIndex &&
            isAlphaZeroBoundaryInput input) = false := by
        simp [indexNe]
      rw [if_neg]
      simpa using update_alpha_zero_producers_eq_or_append
        state.memory.producers input answer
      exact Bool.eq_false_iff.mp boundaryFalse

/-- A fresh exact-root answer preserves uniqueness of producer digests after
the selected boundary. -/
theorem alpha_zero_after_memory_producer_digests_nodup_of_index_ne
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256)
    (indexNe : state.exposureIndex ≠ boundaryIndex)
    (currentNodup :
      (state.memory.producers.map AlphaZeroProducer.digest).Nodup)
    (answerFresh :
      answer ∉ state.memory.producers.map AlphaZeroProducer.digest) :
    ((alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers.map
      AlphaZeroProducer.digest).Nodup := by
  rcases alpha_zero_after_memory_producers_eq_or_append_of_index_ne
      transitionFuel boundaryIndex state answer indexNe with
    unchanged | ⟨block, appended⟩
  · simpa [unchanged] using currentNodup
  · rw [appended, List.map_append]
    simp only [List.map_singleton]
    rw [List.nodup_append]
    refine ⟨currentNodup, by simp, ?_⟩
    intro prior priorMember singleton singletonMember
    simp only [List.mem_singleton] at singletonMember
    subst singleton
    exact fun equal => answerFresh (equal ▸ priorMember)

/-- Producer monotonicity through an arbitrary replay suffix strictly after
the selected boundary ordinal. -/
theorem alpha_zero_indexed_state_producers_prefix_after_boundary
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      boundaryIndex < state.exposureIndex →
      state.memory.producers <+:
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          records state).memory.producers := by
  intro records
  induction records with
  | nil =>
      intro state _afterBoundary
      exact List.prefix_refl _
  | cons record records ih =>
      intro state afterBoundary
      let controller := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have oneStep : state.memory.producers <+: next.memory.producers := by
        simpa [next, controller, alphaZeroCausalController,
          IndexedUnifiedExposureController.afterAnswer] using
          alpha_zero_after_memory_producers_prefix_of_index_ne transitionFuel
            boundaryIndex state record.answer (Nat.ne_of_gt afterBoundary)
      have nextAfterBoundary : boundaryIndex < next.exposureIndex := by
        simp [next]
        omega
      rw [indexed_state_after_records_cons]
      exact oneStep.trans (ih next nextAfterBoundary)

/-- Exact-root answer uniqueness lifts to producer-digest uniqueness through
any replay suffix that starts strictly after the selected boundary. -/
theorem alpha_zero_indexed_state_producer_digests_nodup_after_boundary
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      boundaryIndex < state.exposureIndex →
      (records.map UnifiedExposureRecord.answer).Nodup →
      (state.memory.producers.map AlphaZeroProducer.digest).Nodup →
      (∀ producer ∈ state.memory.producers,
        producer.digest ∉ records.map UnifiedExposureRecord.answer) →
      ((indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex)
        records state).memory.producers.map AlphaZeroProducer.digest).Nodup := by
  intro records
  induction records with
  | nil =>
      intro state _afterBoundary _recordsNodup producerNodup _disjoint
      simpa only [indexed_state_after_records_nil] using producerNodup
  | cons record records ih =>
      intro state afterBoundary recordsNodup producerNodup disjoint
      have splitNodup := List.nodup_cons.mp recordsNodup
      let controller := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have answerFresh : record.answer ∉
          state.memory.producers.map AlphaZeroProducer.digest := by
        intro answerMember
        obtain ⟨producer, producerMember, producerDigest⟩ :=
          List.mem_map.mp answerMember
        apply disjoint producer producerMember
        simp only [List.map_cons, List.mem_cons]
        exact Or.inl producerDigest
      have nextNodup :
          (next.memory.producers.map AlphaZeroProducer.digest).Nodup := by
        simpa [next, controller, alphaZeroCausalController,
          IndexedUnifiedExposureController.afterAnswer] using
          alpha_zero_after_memory_producer_digests_nodup_of_index_ne
            transitionFuel boundaryIndex state record.answer
              (Nat.ne_of_gt afterBoundary) producerNodup answerFresh
      have nextDisjoint : ∀ producer ∈ next.memory.producers,
          producer.digest ∉ records.map UnifiedExposureRecord.answer := by
        intro producer producerMember tailMember
        change producer ∈
          (alphaZeroAfterMemory transitionFuel boundaryIndex state
            record.answer).producers at producerMember
        rcases alpha_zero_after_memory_producers_eq_or_append_of_index_ne
            transitionFuel boundaryIndex state record.answer
              (Nat.ne_of_gt afterBoundary) with unchanged | ⟨block, appended⟩
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
      have nextAfterBoundary : boundaryIndex < next.exposureIndex := by
        simp [next]
        omega
      rw [indexed_state_after_records_cons]
      exact ih next nextAfterBoundary splitNodup.2 nextNodup nextDisjoint

/-- Plug the concrete alpha controller into the existing composed 517-slot
router. -/
def exactCompilerConcreteAlphaFinalWorkQ16Router
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel boundaryIndex finalWorkAnchorIndex : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalAlphaFinalWorkQ16Router parameters :=
  exactCompilerAlphaFinalWorkQ16DagRouter parameters transitionFuel
    finalWorkAnchorIndex (alphaZeroCausalController transitionFuel boundaryIndex)
    inactiveAlphaZeroMemory cursor

#print axioms isAlphaZeroBoundaryInput
#print axioms literal_fold_nonce_is_alpha_zero_boundary
#print axioms alphaZeroOutputSlot?
#print axioms alphaZeroAdvancedSlot?
#print axioms alpha_zero_output_slot_of_digest_nodup
#print axioms alpha_zero_advanced_slot_of_digest_nodup
#print axioms updateAlphaZeroProducers
#print axioms update_alpha_zero_producers_prefix
#print axioms update_alpha_zero_producers_new_digest
#print axioms alphaZeroCausalController
#print axioms alpha_zero_after_boundary_has_block_zero_producer
#print axioms alpha_zero_preferred_of_output_match
#print axioms alpha_zero_selected_slot_used_after_answer
#print axioms alpha_zero_after_memory_member_old_or_current
#print axioms alpha_zero_after_memory_producer_digests_nodup
#print axioms alpha_zero_memory_after_advance_contains_producer
#print axioms alpha_zero_after_memory_producers_prefix_of_index_ne
#print axioms alpha_zero_after_memory_producers_eq_or_append_of_index_ne
#print axioms alpha_zero_after_memory_producer_digests_nodup_of_index_ne
#print axioms alpha_zero_indexed_state_producers_prefix_after_boundary
#print axioms alpha_zero_indexed_state_producer_digests_nodup_after_boundary
#print axioms exactCompilerConcreteAlphaFinalWorkQ16Router

end

end AspisK1.V7Tag73AlphaZeroCausalController
