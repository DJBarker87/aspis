import AspisFormal.K1.V7Tag73AlphaZeroCausalController
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Structural invariants of the alpha-zero producer chain

The four-block alpha-zero controller is a single causal chain.  Block zero is
installed only by the selected boundary record; every later producer is made
by the advance input of an existing predecessor.  This file proves the local
inventory facts needed to show that an adversarial query schedule cannot
create two producers for one logical alpha block.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaZeroProducerInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Every nonzero producer remembers an advance input from a predecessor in
the immediately preceding block. -/
def AlphaZeroProducerSourceValid
    (producers : List AlphaZeroProducer) (producer : AlphaZeroProducer) : Prop :=
  producer.block.val = 0 ∨
    ∃ parent ∈ producers,
      parent.block.val + 1 = producer.block.val ∧
      producer.sourceInput = bytes parent.digest ++ [domAdvance]

def AlphaZeroProducerInventoryValid
    (producers : List AlphaZeroProducer) : Prop :=
  ∀ producer ∈ producers, AlphaZeroProducerSourceValid producers producer

/-- A successful output scan returns the literal matching producer. -/
theorem alpha_zero_output_slot_cases
    (producers : List AlphaZeroProducer) (input : ShaInput) (block : Fin 4)
    (output : alphaZeroOutputSlot? producers input = some block) :
    ∃ producer ∈ producers,
      input = bytes producer.digest ++ [domSqueeze] ∧
      producer.block = block := by
  unfold alphaZeroOutputSlot? at output
  generalize foundExact : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domSqueeze])) = found at output
  cases found with
  | none => simp at output
  | some producer =>
      have producerMember : producer ∈ producers :=
        List.mem_of_find?_eq_some foundExact
      have predicate := List.find?_some foundExact
      have inputExact : input = bytes producer.digest ++ [domSqueeze] :=
        of_decide_eq_true predicate
      have blockExact : producer.block = block := by
        simpa using Option.some.inj output
      exact ⟨producer, producerMember, inputExact, blockExact⟩

/-- A successful advance scan returns its literal predecessor and successor
block equation. -/
theorem alpha_zero_advanced_slot_cases
    (producers : List AlphaZeroProducer) (input : ShaInput) (block : Fin 4)
    (advanced : alphaZeroAdvancedSlot? producers input = some block) :
    ∃ parent ∈ producers,
      input = bytes parent.digest ++ [domAdvance] ∧
      parent.block.val + 1 = block.val := by
  unfold alphaZeroAdvancedSlot? at advanced
  generalize foundExact : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = found at advanced
  cases found with
  | none => simp at advanced
  | some parent =>
      have parentMember : parent ∈ producers :=
        List.mem_of_find?_eq_some foundExact
      have predicate := List.find?_some foundExact
      have inputExact : input = bytes parent.digest ++ [domAdvance] :=
        of_decide_eq_true predicate
      by_cases bounded : parent.block.val + 1 < 4
      · simp only [bounded, dite_true] at advanced
        have blockExact := Option.some.inj advanced |>.symm
        subst block
        exact ⟨parent, parentMember, inputExact, rfl⟩
      · simp [bounded] at advanced

/-- Valid source witnesses remain valid when the producer inventory grows. -/
theorem alpha_zero_producer_source_valid_mono
    {before after : List AlphaZeroProducer}
    (subset : ∀ producer, producer ∈ before → producer ∈ after)
    {producer : AlphaZeroProducer}
    (valid : AlphaZeroProducerSourceValid before producer) :
    AlphaZeroProducerSourceValid after producer := by
  rcases valid with zero | ⟨parent, parentMember, blockExact, sourceExact⟩
  · exact Or.inl zero
  · exact Or.inr ⟨parent, subset parent parentMember, blockExact, sourceExact⟩

/-- Updating the chain preserves recursive source validity. -/
theorem update_alpha_zero_producers_preserves_inventory_valid
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256)
    (valid : AlphaZeroProducerInventoryValid producers) :
    AlphaZeroProducerInventoryValid
      (updateAlphaZeroProducers producers input answer) := by
  intro producer producerMember
  cases advanced : alphaZeroAdvancedSlot? producers input with
  | none =>
      simp only [updateAlphaZeroProducers, advanced] at producerMember ⊢
      exact valid producer producerMember
  | some block =>
      simp only [updateAlphaZeroProducers, advanced] at producerMember ⊢
      rw [List.mem_append] at producerMember
      rcases producerMember with old | added
      · exact alpha_zero_producer_source_valid_mono
          (fun candidate member => by
            rw [List.mem_append]
            exact Or.inl member)
          (valid producer old)
      · simp only [List.mem_singleton] at added
        subst producer
        obtain ⟨parent, parentMember, inputExact, blockExact⟩ :=
          alpha_zero_advanced_slot_cases producers input block advanced
        exact Or.inr ⟨parent, by
          rw [List.mem_append]
          exact Or.inl parentMember, blockExact, inputExact⟩

/-- Block uniqueness makes the producer at a logical block unique. -/
theorem alpha_zero_producer_eq_of_block_eq
    (first second : AlphaZeroProducer) :
    ∀ (producers : List AlphaZeroProducer),
      (producers.map AlphaZeroProducer.block).Nodup →
      first ∈ producers → second ∈ producers →
      first.block = second.block → first = second := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup firstMember secondMember blockExact
      have splitNodup : head.block ∉ tail.map AlphaZeroProducer.block ∧
          (tail.map AlphaZeroProducer.block).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      rcases List.mem_cons.mp firstMember with firstHead | firstTail
      · subst first
        rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · exact secondHead.symm
        · exfalso
          apply splitNodup.1
          rw [List.mem_map]
          exact ⟨second, secondTail, blockExact.symm⟩
      · rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · subst second
          exfalso
          apply splitNodup.1
          rw [List.mem_map]
          exact ⟨first, firstTail, blockExact⟩
        · exact ih splitNodup.2 firstTail secondTail blockExact

/-- With valid recursive provenance and a fresh source input, an advance
cannot recreate a block already present in the inventory. -/
theorem alpha_zero_advanced_block_fresh
    (producers : List AlphaZeroProducer) (input : ShaInput) (block : Fin 4)
    (valid : AlphaZeroProducerInventoryValid producers)
    (blocksNodup : (producers.map AlphaZeroProducer.block).Nodup)
    (sourceFresh : input ∉ producers.map AlphaZeroProducer.sourceInput)
    (advanced : alphaZeroAdvancedSlot? producers input = some block) :
    block ∉ producers.map AlphaZeroProducer.block := by
  intro blockMember
  obtain ⟨existing, existingMember, existingBlock⟩ :=
    List.mem_map.mp blockMember
  obtain ⟨parent, parentMember, inputExact, blockExact⟩ :=
    alpha_zero_advanced_slot_cases producers input block advanced
  rcases valid existing existingMember with existingZero |
      ⟨otherParent, otherParentMember, otherBlock, sourceExact⟩
  · have positive : 0 < block.val := by omega
    have zero : block.val = 0 := by rw [← existingBlock, existingZero]
    omega
  · have parentsBlockVal : otherParent.block.val = parent.block.val := by
      have existingSuccessor : otherParent.block.val + 1 = block.val := by
        rw [← existingBlock]
        exact otherBlock
      omega
    have parentsBlock : otherParent.block = parent.block :=
      Fin.ext parentsBlockVal
    have parentsExact : otherParent = parent :=
      alpha_zero_producer_eq_of_block_eq otherParent parent producers
        blocksNodup otherParentMember parentMember parentsBlock
    subst otherParent
    apply sourceFresh
    rw [List.mem_map]
    refine ⟨existing, existingMember, ?_⟩
    rw [sourceExact, ← inputExact]

/-- A fresh advance input preserves logical block uniqueness. -/
theorem update_alpha_zero_producers_blocks_nodup
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256)
    (valid : AlphaZeroProducerInventoryValid producers)
    (blocksNodup : (producers.map AlphaZeroProducer.block).Nodup)
    (sourceFresh : input ∉ producers.map AlphaZeroProducer.sourceInput) :
    ((updateAlphaZeroProducers producers input answer).map
      AlphaZeroProducer.block).Nodup := by
  unfold updateAlphaZeroProducers
  cases advanced : alphaZeroAdvancedSlot? producers input with
  | none => exact blocksNodup
  | some block =>
      rw [List.map_append, List.nodup_append]
      refine ⟨blocksNodup, by simp, ?_⟩
      intro prior priorMember singleton singletonMember
      change singleton ∈ [block] at singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst singleton
      exact fun equal =>
        alpha_zero_advanced_block_fresh producers input block valid blocksNodup
          sourceFresh advanced (equal ▸ priorMember)

theorem update_alpha_zero_producers_source_inputs_nodup
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256)
    (sourceNodup : (producers.map AlphaZeroProducer.sourceInput).Nodup)
    (sourceFresh : input ∉ producers.map AlphaZeroProducer.sourceInput) :
    ((updateAlphaZeroProducers producers input answer).map
      AlphaZeroProducer.sourceInput).Nodup := by
  unfold updateAlphaZeroProducers
  cases advanced : alphaZeroAdvancedSlot? producers input with
  | none => exact sourceNodup
  | some block =>
      rw [List.map_append, List.nodup_append]
      refine ⟨sourceNodup, by simp, ?_⟩
      intro prior priorMember singleton singletonMember
      change singleton ∈ [input] at singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst singleton
      exact fun equal => sourceFresh (equal ▸ priorMember)

structure AlphaZeroMemoryProducerInvariant
    (memory : AlphaZeroControllerMemory) : Prop where
  inventoryValid : AlphaZeroProducerInventoryValid memory.producers
  blocksNodup : (memory.producers.map AlphaZeroProducer.block).Nodup
  sourceInputsNodup :
    (memory.producers.map AlphaZeroProducer.sourceInput).Nodup

theorem inactive_alpha_zero_memory_producer_invariant :
    AlphaZeroMemoryProducerInvariant inactiveAlphaZeroMemory := by
  constructor <;> simp [AlphaZeroProducerInventoryValid,
    inactiveAlphaZeroMemory]

/-- One aligned fresh-input step preserves recursive provenance and uniqueness
of both logical blocks and remembered source inputs. -/
theorem alpha_zero_after_memory_preserves_producer_invariant
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (invariant : AlphaZeroMemoryProducerInvariant state.memory)
    (sourceFresh :
      input ∉ state.memory.producers.map AlphaZeroProducer.sourceInput) :
    AlphaZeroMemoryProducerInvariant
      (alphaZeroAfterMemory transitionFuel boundaryIndex state answer) := by
  unfold alphaZeroAfterMemory
  rw [inputExact]
  change AlphaZeroMemoryProducerInvariant
    { producers :=
        if (state.exposureIndex = boundaryIndex &&
            isAlphaZeroBoundaryInput input) then
          [{ digest := answer, block := 0, sourceInput := input }]
        else updateAlphaZeroProducers state.memory.producers input answer
      usedSlots := _ }
  split
  · constructor
    · intro producer member
      simp only [List.mem_singleton] at member
      subst producer
      exact Or.inl rfl
    · simp
    · simp
  · constructor
    · exact update_alpha_zero_producers_preserves_inventory_valid
        state.memory.producers input answer invariant.inventoryValid
    · exact update_alpha_zero_producers_blocks_nodup state.memory.producers
        input answer invariant.inventoryValid invariant.blocksNodup sourceFresh
    · exact update_alpha_zero_producers_source_inputs_nodup
        state.memory.producers input answer invariant.sourceInputsNodup
          sourceFresh

/-- A live producer's squeeze input receives its exact alpha block whenever
that one-shot slot has not been consumed already. -/
theorem alpha_zero_output_is_preferred_of_producer
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (producer : AlphaZeroProducer)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some (bytes producer.digest ++ [domSqueeze]))
    (digestNodup :
      (state.memory.producers.map AlphaZeroProducer.digest).Nodup)
    (producerMember : producer ∈ state.memory.producers)
    (slotUnused : producer.block ∉ state.memory.usedSlots) :
    alphaZeroPreferredSlot transitionFuel state = some producer.block := by
  have outputSlot : alphaZeroOutputSlot? state.memory.producers
      (bytes producer.digest ++ [domSqueeze]) = some producer.block :=
    alpha_zero_output_slot_of_digest_nodup producer state.memory.producers
      digestNodup producerMember
  simp [alphaZeroPreferredSlot, inputExact, outputSlot, slotUnused]

/-- Every emitted alpha label is backed by a literal current producer and its
exact squeeze input. -/
theorem alpha_zero_preferred_slot_has_producer
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory) (slot : Fin 4)
    (preferred : alphaZeroPreferredSlot transitionFuel state = some slot) :
    ∃ input producer,
      unifiedInputBeforeAnswer? transitionFuel state.cursor = some input ∧
      producer ∈ state.memory.producers ∧
      input = bytes producer.digest ++ [domSqueeze] ∧
      producer.block = slot := by
  unfold alphaZeroPreferredSlot at preferred
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simp [inputExact] at preferred
  | some input =>
      simp only [inputExact] at preferred
      cases output : alphaZeroOutputSlot? state.memory.producers input with
      | none => simp [output] at preferred
      | some outputSlot =>
          simp only [output] at preferred
          by_cases used : outputSlot ∈ state.memory.usedSlots
          · simp [used] at preferred
          · have slotExact : outputSlot = slot := by
              have preferredSome : some outputSlot = some slot := by
                simpa [used] using preferred
              exact Option.some.inj preferredSome
            subst outputSlot
            obtain ⟨producer, producerMember, inputIsOutput, blockExact⟩ :=
              alpha_zero_output_slot_cases state.memory.producers input slot
                output
            refine ⟨input, producer, ?_, producerMember, inputIsOutput,
              blockExact⟩
            simp

/-- Replaying a fresh-input machine trace preserves the recursive alpha-chain
invariant.  Freshness is discharged from the exact root input inventory, not
from an honest sequential query schedule. -/
theorem aligned_machine_records_preserve_alpha_zero_producer_invariant
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      IndexedRecordsAligned transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex) state
          records →
      OnlyMachineFreshRecords records →
      (records.map causalInput?).Nodup →
      AlphaZeroMemoryProducerInvariant state.memory →
      (∀ producer ∈ state.memory.producers,
        some producer.sourceInput ∉ records.map causalInput?) →
      AlphaZeroMemoryProducerInvariant
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          records state).memory := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _onlyMachine _inputsNodup invariant _disjoint
      simpa only [indexed_state_after_records_nil] using invariant
  | cons head tail ih =>
      intro state aligned onlyMachine inputsNodup invariant disjoint
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
      have splitInputs : some input ∉ tail.map causalInput? ∧
          (tail.map causalInput?).Nodup := by
        simpa [causalInput?] using List.nodup_cons.mp inputsNodup
      have sourceFresh : input ∉
          state.memory.producers.map AlphaZeroProducer.sourceInput := by
        intro sourceMember
        obtain ⟨producer, producerMember, sourceExact⟩ :=
          List.mem_map.mp sourceMember
        apply disjoint producer producerMember
        simp [causalInput?, sourceExact]
      let controller := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let next := controller.afterAnswer transitionFuel state answer
      have nextInvariant : AlphaZeroMemoryProducerInvariant next.memory := by
        simpa [next, controller, alphaZeroCausalController,
          IndexedUnifiedExposureController.afterAnswer] using
          alpha_zero_after_memory_preserves_producer_invariant transitionFuel
            boundaryIndex state input answer inputExact invariant sourceFresh
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: tail)
          [(.machineFresh actor input answer)] tail [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have nextDisjoint : ∀ producer ∈ next.memory.producers,
          some producer.sourceInput ∉ tail.map causalInput? := by
        intro producer producerMember tailMember
        change producer ∈
          (alphaZeroAfterMemory transitionFuel boundaryIndex state
            answer).producers at producerMember
        rcases alpha_zero_after_memory_member_old_or_current transitionFuel
            boundaryIndex state input answer producer inputExact producerMember with
          old | ⟨sourceExact, _digestExact⟩
        · exact disjoint producer old (by
            simp only [List.map_cons, causalInput?, List.mem_cons]
            exact Or.inr tailMember)
        · rw [sourceExact] at tailMember
          exact splitInputs.1 tailMember
      rw [indexed_state_after_records_cons]
      exact ih next tailAligned tailOnly splitInputs.2 nextInvariant
        nextDisjoint

#print axioms AlphaZeroProducerSourceValid
#print axioms AlphaZeroProducerInventoryValid
#print axioms alpha_zero_output_slot_cases
#print axioms alpha_zero_advanced_slot_cases
#print axioms update_alpha_zero_producers_preserves_inventory_valid
#print axioms alpha_zero_producer_eq_of_block_eq
#print axioms alpha_zero_advanced_block_fresh
#print axioms update_alpha_zero_producers_blocks_nodup
#print axioms update_alpha_zero_producers_source_inputs_nodup
#print axioms AlphaZeroMemoryProducerInvariant
#print axioms inactive_alpha_zero_memory_producer_invariant
#print axioms alpha_zero_after_memory_preserves_producer_invariant
#print axioms alpha_zero_output_is_preferred_of_producer
#print axioms alpha_zero_preferred_slot_has_producer
#print axioms aligned_machine_records_preserve_alpha_zero_producer_invariant

end

end AspisK1.V7Tag73AlphaZeroProducerInvariant
