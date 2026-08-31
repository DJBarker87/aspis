import AspisFormal.K1.V7Tag73CausalDagFinalWorkQ16Controller
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Structural invariants of the causal q16 producer DAG

Every producer remembers the literal root input that created it.  Block zero
comes only from the candidate absorb for its counter; every later block comes
only from the advance input of an already-known producer in the preceding
slot.  This provenance is what turns exact root-input freshness into slot
uniqueness without assuming an honest query order.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalDagProducerInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16CandidateParserExact
open AspisK1.V7Tag73SchedulerHistoryQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Every key returned by the raw work parser has the deployed 32-byte digest
and 8-byte nonce widths. -/
theorem raw_final_work_key_of_work_input_some_lengths
    (input : ShaInput) (key : RawFinalWorkKey)
    (parsed : rawFinalWorkKeyOfWorkInput? input = some key) :
    key.digest.length = 32 ∧ key.nonce.length = 8 := by
  unfold rawFinalWorkKeyOfWorkInput? at parsed
  split at parsed <;> try contradiction
  rename_i inputLength
  split at parsed <;> try contradiction
  simp only [Option.some.injEq] at parsed
  subst key
  constructor
  · simp [inputLength]
  · simp [inputLength]

/-- The nonce-absorb parser establishes the same canonical key widths. -/
theorem raw_final_work_key_of_absorb_input_some_lengths
    (input : ShaInput) (key : RawFinalWorkKey)
    (parsed : rawFinalWorkKeyOfAbsorbInput? input = some key) :
    key.digest.length = 32 ∧ key.nonce.length = 8 := by
  unfold rawFinalWorkKeyOfAbsorbInput? at parsed
  split at parsed <;> try contradiction
  rename_i inputLength
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  simp only [Option.some.injEq] at parsed
  subst key
  constructor
  · simp [inputLength]
  · simp [inputLength]

def Q16DagAnchorWellFormed : FinalWorkDagAnchor → Prop
  | .inactive => True
  | .tracked key _workSeen =>
      key.digest.length = 32 ∧ key.nonce.length = 8

/-- One arbitrary input step preserves canonical final-work key widths. -/
theorem dag_memory_after_input_preserves_anchor_well_formed
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256)
    (wellFormed : Q16DagAnchorWellFormed memory.anchor) :
    Q16DagAnchorWellFormed
      (dagMemoryAfterInput anchorIndex exposureIndex memory input answer).anchor := by
  unfold dagMemoryAfterInput dagCoreMemoryAfterInput
  cases anchorExact : memory.anchor with
  | inactive =>
      simp only
      by_cases atAnchor : exposureIndex = anchorIndex
      · simp only [atAnchor, if_pos]
        cases work : rawFinalWorkKeyOfWorkInput? input with
        | some key =>
            simpa [Q16DagAnchorWellFormed] using
              raw_final_work_key_of_work_input_some_lengths input key work
        | none =>
            simp only [work]
            cases absorb : rawFinalWorkKeyOfAbsorbInput? input with
            | some key =>
                simpa [Q16DagAnchorWellFormed] using
                  raw_final_work_key_of_absorb_input_some_lengths input key
                    absorb
            | none =>
                simpa [anchorExact, Q16DagAnchorWellFormed] using wellFormed
      · simpa [atAnchor, anchorExact, Q16DagAnchorWellFormed] using
          wellFormed
  | tracked key workSeen =>
      have keyWellFormed : key.digest.length = 32 ∧ key.nonce.length = 8 := by
        simpa [anchorExact, Q16DagAnchorWellFormed] using wellFormed
      cases baseExact : memory.q16Base with
      | none =>
          by_cases absorb : input = key.absorbInput <;>
            simp [baseExact, absorb, Q16DagAnchorWellFormed, keyWellFormed]
      | some base =>
          simp [baseExact, Q16DagAnchorWellFormed, keyWellFormed]

/-- Canonical key widths lift through any indexed causal-DAG replay. -/
theorem dag_indexed_state_anchor_well_formed
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      Q16DagAnchorWellFormed state.memory.anchor →
      Q16DagAnchorWellFormed
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) records state).memory.anchor := by
  intro records
  induction records with
  | nil =>
      intro state wellFormed
      simpa only [indexed_state_after_records_nil] using wellFormed
  | cons record records ih =>
      intro state wellFormed
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextWellFormed : Q16DagAnchorWellFormed next.memory.anchor := by
        unfold next controller finalWorkQ16DagController
        simp only [IndexedUnifiedExposureController.afterAnswer]
        unfold dagCandidateAfterMemory
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor
        · exact wellFormed
        · exact dag_memory_after_input_preserves_anchor_well_formed
            anchorIndex state.exposureIndex state.memory _ record.answer
              wellFormed
      rw [indexed_state_after_records_cons]
      exact ih next nextWellFormed

/-- A producer's remembered source is either its unique block-zero candidate
absorb or the advance edge of an existing predecessor. -/
def Q16DagProducerSourceValid (base : Digest256)
    (producers : List Q16DagProducer) (producer : Q16DagProducer) : Prop :=
  (producer.slot.2.val = 0 ∧
    producer.sourceInput =
      bytes base ++ [domAbsorb, queryCandidateLabel,
        UInt8.ofNat producer.slot.1.val]) ∨
  ∃ parent ∈ producers,
    parent.slot.1 = producer.slot.1 ∧
    parent.slot.2.val + 1 = producer.slot.2.val ∧
    producer.sourceInput = bytes parent.digest ++ [domAdvance]

def Q16DagProducerInventoryValid (base : Digest256)
    (producers : List Q16DagProducer) : Prop :=
  ∀ producer ∈ producers,
    Q16DagProducerSourceValid base producers producer

/-- A successful output-slot scan returns a literal producer whose digest
forms the queried squeeze input. -/
theorem q16_dag_output_slot_cases
    (producers : List Q16DagProducer) (input : ShaInput)
    (slot : Q16DigestSlot)
    (output : q16DagOutputSlot? producers input = some slot) :
    ∃ producer ∈ producers,
      input = bytes producer.digest ++ [domSqueeze] ∧
      producer.slot = slot := by
  unfold q16DagOutputSlot? at output
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
      have slotExact : producer.slot = slot := by
        simpa using Option.some.inj output
      exact ⟨producer, producerMember, inputExact, slotExact⟩

/-- A q16-valued preferred label is backed by a literal producer in the
current causal inventory.  The final-work label cannot inhabit this case. -/
theorem dag_preferred_q16_slot_has_producer
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (slot : Q16DigestSlot)
    (preferred : dagPreferredSlotForInput anchorIndex exposureIndex memory
      input = some (some slot)) :
    ∃ producer ∈ memory.producers,
      input = bytes producer.digest ++ [domSqueeze] ∧
      producer.slot = slot := by
  have rawPreferred : dagRawPreferredSlot anchorIndex exposureIndex memory
      input = some (some slot) := by
    unfold dagPreferredSlotForInput at preferred
    cases raw : dagRawPreferredSlot anchorIndex exposureIndex memory input with
    | none => simp [raw] at preferred
    | some rawSlot =>
        by_cases used : rawSlot ∈ memory.usedSlots
        · simp [raw, used] at preferred
        · simp only [raw, used, if_false] at preferred
          have slotExact : rawSlot = some slot := Option.some.inj preferred
          simpa [slotExact] using raw
  cases anchorExact : memory.anchor with
  | inactive =>
      unfold dagRawPreferredSlot at rawPreferred
      rw [anchorExact] at rawPreferred
      by_cases atAnchor : exposureIndex = anchorIndex
      · simp only [atAnchor, if_pos] at rawPreferred
        cases work : rawFinalWorkKeyOfWorkInput? input <;>
          simp [work] at rawPreferred
      · simp [atAnchor] at rawPreferred
  | tracked key workSeen =>
      unfold dagRawPreferredSlot at rawPreferred
      rw [anchorExact] at rawPreferred
      by_cases work : workSeen = false ∧ input = key.workInput
      · simp [work] at rawPreferred
      · simp only [work, if_false] at rawPreferred
        have output : q16DagOutputSlot? memory.producers input = some slot := by
          simpa using rawPreferred
        exact q16_dag_output_slot_cases memory.producers input slot output

theorem q16_dag_advanced_slot_cases
    (producers : List Q16DagProducer) (input : ShaInput)
    (slot : Q16DigestSlot)
    (produced : q16DagAdvancedSlot? producers input = some slot) :
    ∃ parent ∈ producers,
      input = bytes parent.digest ++ [domAdvance] ∧
      parent.slot.2.val + 1 < 8 ∧
      slot.1 = parent.slot.1 ∧
      slot.2.val = parent.slot.2.val + 1 := by
  unfold q16DagAdvancedSlot? at produced
  generalize foundExact : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = found at produced
  cases found with
  | none =>
      simp at produced
  | some parent =>
      have parentMember : parent ∈ producers :=
        List.mem_of_find?_eq_some foundExact
      have predicate := List.find?_some foundExact
      have inputExact : input = bytes parent.digest ++ [domAdvance] :=
        of_decide_eq_true predicate
      by_cases bounded : parent.slot.2.val + 1 < 8
      · simp only [bounded, dite_true] at produced
        have slotExact := Option.some.inj produced |>.symm
        subst slot
        exact ⟨parent, parentMember, inputExact, bounded, rfl, rfl⟩
      · simp [bounded] at produced

theorem q16_dag_produced_slot_cases
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (slot : Q16DigestSlot)
    (produced : q16DagProducedSlot? base producers input = some slot) :
    (∃ counter : Fin 64,
      input = bytes base ++ [domAbsorb, queryCandidateLabel,
        UInt8.ofNat counter.val] ∧
      slot.1 = counter ∧ slot.2.val = 0) ∨
    (∃ parent ∈ producers,
      input = bytes parent.digest ++ [domAdvance] ∧
      parent.slot.2.val + 1 < 8 ∧
      slot.1 = parent.slot.1 ∧
      slot.2.val = parent.slot.2.val + 1) := by
  unfold q16DagProducedSlot? at produced
  cases candidate : q16CandidateOfBaseInput? base input with
  | some counter =>
      rw [candidate] at produced
      left
      refine ⟨counter, q16_candidate_of_base_input_exact base input counter
        candidate, ?_, ?_⟩
      · exact congrArg Prod.fst (Option.some.inj produced |>.symm)
      · exact congrArg (fun value => value.2.val)
          (Option.some.inj produced |>.symm)
  | none =>
      rw [candidate] at produced
      right
      exact q16_dag_advanced_slot_cases producers input slot produced

/-- Producer source validity is monotone when the inventory grows. -/
theorem q16_dag_producer_source_valid_mono
    (base : Digest256) {before after : List Q16DagProducer}
    (subset : ∀ producer, producer ∈ before → producer ∈ after)
    {producer : Q16DagProducer}
    (valid : Q16DagProducerSourceValid base before producer) :
    Q16DagProducerSourceValid base after producer := by
  rcases valid with baseSource | ⟨parent, parentMember, rest⟩
  · exact Or.inl baseSource
  · exact Or.inr ⟨parent, subset parent parentMember, rest⟩

/-- One producer update preserves the recursive source certificate. -/
theorem update_q16_dag_producers_preserves_inventory_valid
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (answer : Digest256)
    (valid : Q16DagProducerInventoryValid base producers) :
    Q16DagProducerInventoryValid base
      (updateQ16DagProducers base producers input answer) := by
  intro producer producerMember
  cases produced : q16DagProducedSlot? base producers input with
  | none =>
      simp only [updateQ16DagProducers, produced] at producerMember ⊢
      exact valid producer producerMember
  | some slot =>
      simp only [updateQ16DagProducers, produced] at producerMember ⊢
      rw [List.mem_append] at producerMember
      rcases producerMember with old | added
      · exact q16_dag_producer_source_valid_mono base
          (fun candidate member => by
            rw [List.mem_append]
            exact Or.inl member)
          (valid producer old)
      · simp only [List.mem_singleton] at added
        subst producer
        rcases q16_dag_produced_slot_cases base producers input slot produced with
          ⟨counter, inputExact, counterExact, blockExact⟩ |
          ⟨parent, parentMember, inputExact, bounded, counterExact,
            blockExact⟩
        · left
          constructor
          · exact blockExact
          · simpa [counterExact] using inputExact
        · right
          refine ⟨parent, ?_, ?_, ?_, ?_⟩
          · rw [List.mem_append]
            exact Or.inl parentMember
          · exact counterExact.symm
          · exact blockExact.symm
          · simpa using inputExact

/-- A list whose projected slots are duplicate-free contains at most one
producer for a given slot. -/
theorem q16_dag_producer_eq_of_slot_eq
    (first second : Q16DagProducer) :
    ∀ (producers : List Q16DagProducer),
      (producers.map Q16DagProducer.slot).Nodup →
      first ∈ producers → second ∈ producers →
      first.slot = second.slot → first = second := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup firstMember secondMember slotExact
      have splitNodup : head.slot ∉ tail.map Q16DagProducer.slot ∧
          (tail.map Q16DagProducer.slot).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      rcases List.mem_cons.mp firstMember with firstHead | firstTail
      · subst first
        rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · exact secondHead.symm
        · exfalso
          apply splitNodup.1
          rw [List.mem_map]
          exact ⟨second, secondTail, slotExact.symm⟩
      · rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · subst second
          exfalso
          apply splitNodup.1
          rw [List.mem_map]
          exact ⟨first, firstTail, slotExact⟩
        · exact ih splitNodup.2 firstTail secondTail slotExact

/-- With valid source provenance and fresh root input, the newly produced
slot cannot already occur in the producer inventory. -/
theorem q16_dag_produced_slot_fresh
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (slot : Q16DigestSlot)
    (valid : Q16DagProducerInventoryValid base producers)
    (slotNodup : (producers.map Q16DagProducer.slot).Nodup)
    (sourceFresh : input ∉ producers.map Q16DagProducer.sourceInput)
    (produced : q16DagProducedSlot? base producers input = some slot) :
    slot ∉ producers.map Q16DagProducer.slot := by
  intro slotMember
  obtain ⟨existing, existingMember, existingSlot⟩ :=
    List.mem_map.mp slotMember
  have existingValid := valid existing existingMember
  rcases q16_dag_produced_slot_cases base producers input slot produced with
    ⟨counter, inputExact, counterExact, blockExact⟩ |
    ⟨parent, parentMember, inputExact, bounded, counterExact, blockExact⟩
  · rcases existingValid with baseSource |
        ⟨parent, parentMember, parentCounter, parentBlock, sourceExact⟩
    · have existingCounter : existing.slot.1 = counter := by
        rw [existingSlot, counterExact]
      have inputIsExistingSource : input = existing.sourceInput := by
        rw [inputExact, baseSource.2, existingCounter]
      apply sourceFresh
      rw [List.mem_map]
      exact ⟨existing, existingMember, inputIsExistingSource.symm⟩
    · have existingBlock : existing.slot.2.val = 0 := by
        rw [existingSlot, blockExact]
      omega
  · rcases existingValid with baseSource |
        ⟨otherParent, otherParentMember, otherCounter, otherBlock,
          sourceExact⟩
    · have existingBlock : existing.slot.2.val =
          parent.slot.2.val + 1 := by
        rw [existingSlot, blockExact]
      omega
    · have parentsCounter : otherParent.slot.1 = parent.slot.1 := by
        rw [otherCounter, existingSlot, counterExact]
      have parentsBlockVal : otherParent.slot.2.val = parent.slot.2.val := by
        have existingBlock : existing.slot.2.val =
            parent.slot.2.val + 1 := by
          rw [existingSlot, blockExact]
        omega
      have parentsBlock : otherParent.slot.2 = parent.slot.2 :=
        Fin.ext parentsBlockVal
      have parentsSlot : otherParent.slot = parent.slot :=
        Prod.ext parentsCounter parentsBlock
      have parentsExact : otherParent = parent :=
        q16_dag_producer_eq_of_slot_eq otherParent parent producers slotNodup
          otherParentMember parentMember parentsSlot
      subst otherParent
      have inputIsExistingSource : input = existing.sourceInput := by
        rw [inputExact, sourceExact]
      apply sourceFresh
      rw [List.mem_map]
      exact ⟨existing, existingMember, inputIsExistingSource.symm⟩

/-- A fresh source input preserves producer-slot uniqueness. -/
theorem update_q16_dag_producers_slots_nodup
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (answer : Digest256)
    (valid : Q16DagProducerInventoryValid base producers)
    (slotNodup : (producers.map Q16DagProducer.slot).Nodup)
    (sourceFresh : input ∉ producers.map Q16DagProducer.sourceInput) :
    ((updateQ16DagProducers base producers input answer).map
      Q16DagProducer.slot).Nodup := by
  unfold updateQ16DagProducers
  cases produced : q16DagProducedSlot? base producers input with
  | none => exact slotNodup
  | some slot =>
      rw [List.map_append, List.nodup_append]
      refine ⟨slotNodup, by simp, ?_⟩
      intro prior priorMember singleton singletonMember
      change singleton ∈ [slot] at singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst singleton
      exact fun equal =>
        q16_dag_produced_slot_fresh base producers input slot valid slotNodup
          sourceFresh produced (equal ▸ priorMember)

theorem update_q16_dag_producers_source_inputs_nodup
    (base : Digest256) (producers : List Q16DagProducer)
    (input : ShaInput) (answer : Digest256)
    (sourceNodup : (producers.map Q16DagProducer.sourceInput).Nodup)
    (sourceFresh : input ∉ producers.map Q16DagProducer.sourceInput) :
    ((updateQ16DagProducers base producers input answer).map
      Q16DagProducer.sourceInput).Nodup := by
  unfold updateQ16DagProducers
  cases produced : q16DagProducedSlot? base producers input with
  | none => exact sourceNodup
  | some slot =>
      rw [List.map_append, List.nodup_append]
      refine ⟨sourceNodup, by simp, ?_⟩
      intro prior priorMember singleton singletonMember
      change singleton ∈ [input] at singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst singleton
      exact fun equal => sourceFresh (equal ▸ priorMember)

/-- Reachable controller memories keep an empty producer list until the q16
base exists; afterwards every producer has valid recursive provenance and
both slots and remembered source inputs are duplicate-free. -/
structure Q16DagMemoryProducerInvariant
    (memory : FinalWorkQ16DagMemory) : Prop where
  inactiveHasNoBase : memory.anchor = .inactive → memory.q16Base = none
  noBaseHasNoProducers : memory.q16Base = none → memory.producers = []
  inventoryValid : ∀ base, memory.q16Base = some base →
    Q16DagProducerInventoryValid base memory.producers
  slotsNodup : (memory.producers.map Q16DagProducer.slot).Nodup
  sourceInputsNodup :
    (memory.producers.map Q16DagProducer.sourceInput).Nodup

@[simp] theorem literal_q16_candidate_parses
    (base : Digest256) (counter : Fin 64) :
    q16CandidateOfBaseInput? base
        (bytes base ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val]) = some counter := by
  exact q16_candidate_of_literal_base_input base counter

@[simp] theorem advance_input_is_not_q16_candidate
    (base digest : Digest256) :
    q16CandidateOfBaseInput? base (bytes digest ++ [domAdvance]) = none := by
  simp [q16CandidateOfBaseInput?, q16CandidateCounterOfInput?]

/-- Once a tracked DAG memory has a q16 base, arbitrary inputs preserve that
same base. -/
theorem dag_memory_after_input_preserves_tracked_base
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (workSeen : Bool) (base : Digest256)
    (input : ShaInput) (answer : Digest256)
    (anchorExact : memory.anchor = .tracked key workSeen)
    (baseExact : memory.q16Base = some base) :
    (dagMemoryAfterInput anchorIndex exposureIndex memory input answer).q16Base =
      some base := by
  unfold dagMemoryAfterInput dagCoreMemoryAfterInput
  rw [anchorExact, baseExact]

/-- A literal candidate absorb answer installs the exact block-zero producer. -/
theorem dag_memory_after_candidate_contains_producer
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (workSeen : Bool) (base answer : Digest256)
    (counter : Fin 64)
    (anchorExact : memory.anchor = .tracked key workSeen)
    (baseExact : memory.q16Base = some base) :
    Q16DagProducer.mk answer (counter, ⟨0, by omega⟩)
        (bytes base ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val]) ∈
      (dagMemoryAfterInput anchorIndex exposureIndex memory
        (bytes base ++ [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val]) answer).producers := by
  have produced :
      q16DagProducedSlot? base memory.producers
          (bytes base ++ [domAbsorb, queryCandidateLabel,
            UInt8.ofNat counter.val]) =
        some (counter, ⟨0, by omega⟩) := by
    simp [q16DagProducedSlot?]
  simp only [dagMemoryAfterInput, dagCoreMemoryAfterInput, anchorExact,
    baseExact]
  unfold updateQ16DagProducers
  rw [produced]
  simp

/-- A literal advance answer from a known bounded parent installs the exact
next-block producer without waiting for the sibling output. -/
theorem dag_memory_after_advance_contains_producer
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (key : RawFinalWorkKey) (workSeen : Bool) (base answer : Digest256)
    (parent : Q16DagProducer)
    (bounded : parent.slot.2.val + 1 < 8)
    (anchorExact : memory.anchor = .tracked key workSeen)
    (baseExact : memory.q16Base = some base)
    (digestNodup : (memory.producers.map Q16DagProducer.digest).Nodup)
    (parentMember : parent ∈ memory.producers) :
    Q16DagProducer.mk answer
        (parent.slot.1, ⟨parent.slot.2.val + 1, bounded⟩)
        (bytes parent.digest ++ [domAdvance]) ∈
      (dagMemoryAfterInput anchorIndex exposureIndex memory
        (bytes parent.digest ++ [domAdvance]) answer).producers := by
  have advanced := q16_dag_advanced_slot_of_digest_nodup parent bounded
    memory.producers digestNodup parentMember
  unfold dagMemoryAfterInput dagCoreMemoryAfterInput updateQ16DagProducers
  rw [anchorExact, baseExact]
  simp only [q16DagProducedSlot?, advance_input_is_not_q16_candidate,
    advanced]
  simp

theorem inactive_dag_memory_producer_invariant :
    Q16DagMemoryProducerInvariant inactiveDagMemory := by
  constructor <;> simp [inactiveDagMemory, Q16DagProducerInventoryValid]

theorem empty_no_base_dag_memory_producer_invariant
    (anchor : FinalWorkDagAnchor)
    (usedSlots : Finset FinalWorkQ16DigestSlot) :
    Q16DagMemoryProducerInvariant
      { anchor := anchor, q16Base := none, producers := [],
        usedSlots := usedSlots } := by
  constructor <;> simp [Q16DagProducerInventoryValid]

theorem empty_based_dag_memory_producer_invariant
    (key : RawFinalWorkKey) (workSeen : Bool) (base : Digest256)
    (usedSlots : Finset FinalWorkQ16DigestSlot) :
    Q16DagMemoryProducerInvariant
      { anchor := .tracked key workSeen, q16Base := some base, producers := [],
        usedSlots := usedSlots } := by
  constructor <;> simp [Q16DagProducerInventoryValid]

/-- One concrete pre-answer input preserves the complete producer invariant
when it is fresh relative to all previously recorded producer sources. -/
theorem dag_memory_after_input_preserves_producer_invariant
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256)
    (invariant : Q16DagMemoryProducerInvariant memory)
    (sourceFresh : input ∉ memory.producers.map Q16DagProducer.sourceInput) :
    Q16DagMemoryProducerInvariant
      (dagMemoryAfterInput anchorIndex exposureIndex memory input answer) := by
  unfold dagMemoryAfterInput
  cases anchorExact : memory.anchor with
  | inactive =>
      have baseNone := invariant.inactiveHasNoBase anchorExact
      have producersEmpty := invariant.noBaseHasNoProducers baseNone
      simp only [dagCoreMemoryAfterInput, anchorExact]
      by_cases atAnchor : exposureIndex = anchorIndex
      · simp only [atAnchor, if_pos]
        cases work : rawFinalWorkKeyOfWorkInput? input with
        | some key =>
            simp only [work]
            rw [producersEmpty]
            exact empty_no_base_dag_memory_producer_invariant _ _
        | none =>
            simp only [work]
            cases absorb : rawFinalWorkKeyOfAbsorbInput? input with
            | some key =>
                simp only [absorb]
                rw [producersEmpty]
                exact empty_based_dag_memory_producer_invariant _ _ _ _
            | none =>
                simp only [absorb]
                rw [baseNone, producersEmpty]
                exact empty_no_base_dag_memory_producer_invariant _ _
      · simp [atAnchor]
        rw [baseNone, producersEmpty]
        exact empty_no_base_dag_memory_producer_invariant _ _
  | tracked key workSeen =>
      simp only [dagCoreMemoryAfterInput, anchorExact]
      cases baseExact : memory.q16Base with
      | none =>
          have producersEmpty := invariant.noBaseHasNoProducers baseExact
          by_cases isAbsorb : input = key.absorbInput
          · simp only [isAbsorb, if_pos]
            rw [producersEmpty]
            exact empty_based_dag_memory_producer_invariant _ _ _ _
          · simp only [isAbsorb, if_neg]
            rw [producersEmpty]
            exact empty_no_base_dag_memory_producer_invariant _ _
      | some base =>
          let updated := updateQ16DagProducers base memory.producers input answer
          have valid := invariant.inventoryValid base baseExact
          have updatedValid :=
            update_q16_dag_producers_preserves_inventory_valid base
              memory.producers input answer valid
          have updatedSlots := update_q16_dag_producers_slots_nodup base
            memory.producers input answer valid invariant.slotsNodup sourceFresh
          have updatedSources := update_q16_dag_producers_source_inputs_nodup
            base memory.producers input answer invariant.sourceInputsNodup
              sourceFresh
          change Q16DagMemoryProducerInvariant
            { anchor := .tracked key
                (workSeen || decide (input = key.workInput)),
              q16Base := some base,
              producers := updateQ16DagProducers base memory.producers input answer,
              usedSlots :=
                match dagPreferredSlotForInput anchorIndex exposureIndex
                    memory input with
                | some slot => insert slot memory.usedSlots
                | none => memory.usedSlots }
          constructor
          · intro impossible
            cases impossible
          · intro impossible
            simp at impossible
          · intro otherBase otherExact
            have equal : otherBase = base := Option.some.inj otherExact.symm
            subst otherBase
            exact updatedValid
          · exact updatedSlots
          · exact updatedSources

/-- A live producer's squeeze coordinate receives its q16 slot whenever that
slot has not been consumed already.  Canonical parser widths rule out the
33-byte squeeze coordinate being mistaken for the 41-byte work coordinate. -/
theorem dag_q16_output_is_preferred_of_producer
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (producer : Q16DagProducer)
    (invariant : Q16DagMemoryProducerInvariant memory)
    (anchorWellFormed : Q16DagAnchorWellFormed memory.anchor)
    (digestNodup : (memory.producers.map Q16DagProducer.digest).Nodup)
    (producerMember : producer ∈ memory.producers)
    (slotUnused : some producer.slot ∉ memory.usedSlots) :
    dagPreferredSlotForInput anchorIndex exposureIndex memory
        (bytes producer.digest ++ [domSqueeze]) =
      some (some producer.slot) := by
  have outputSlot : q16DagOutputSlot? memory.producers
      (bytes producer.digest ++ [domSqueeze]) = some producer.slot :=
    q16_dag_output_slot_of_digest_nodup producer memory.producers digestNodup
      producerMember
  cases anchorExact : memory.anchor with
  | inactive =>
      have baseNone := invariant.inactiveHasNoBase anchorExact
      have producersEmpty := invariant.noBaseHasNoProducers baseNone
      rw [producersEmpty] at producerMember
      exact (by simpa using producerMember : False).elim
  | tracked key workSeen =>
      have keyWellFormed : key.digest.length = 32 ∧
          key.nonce.length = 8 := by
        simpa [anchorExact, Q16DagAnchorWellFormed] using anchorWellFormed
      have outputNeWork : bytes producer.digest ++ [domSqueeze] ≠
          key.workInput := by
        intro equal
        have lengths := congrArg List.length equal
        simp [RawFinalWorkKey.workInput, keyWellFormed.1,
          keyWellFormed.2] at lengths
      have notWork : ¬ (workSeen = false ∧
          bytes producer.digest ++ [domSqueeze] = key.workInput) := by
        intro work
        exact outputNeWork work.2
      unfold dagPreferredSlotForInput dagRawPreferredSlot
      rw [anchorExact]
      simp [notWork, outputSlot, slotUnused]

/-- Replaying a fresh-input machine trace preserves the recursive producer
invariant.  The disjointness premise is deliberately stated against the
literal remaining root inputs: it is discharged by the clean-root input
uniqueness theorem, rather than by imposing an honest sequential q16 order. -/
theorem aligned_machine_records_preserve_dag_producer_invariant
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FinalWorkQ16DagMemory),
      IndexedRecordsAligned transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) state records →
      OnlyMachineFreshRecords records →
      (records.map causalInput?).Nodup →
      Q16DagMemoryProducerInvariant state.memory →
      (∀ producer ∈ state.memory.producers,
        some producer.sourceInput ∉ records.map causalInput?) →
      Q16DagMemoryProducerInvariant
        (indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            anchorIndex) records state).memory := by
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
          state.memory.producers.map Q16DagProducer.sourceInput := by
        intro sourceMember
        obtain ⟨producer, producerMember, sourceExact⟩ :=
          List.mem_map.mp sourceMember
        apply disjoint producer producerMember
        simp [causalInput?, sourceExact]
      let controller := finalWorkQ16DagController globalOracleCalls
        transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state answer
      have nextInvariant : Q16DagMemoryProducerInvariant next.memory := by
        simpa [next, controller, finalWorkQ16DagController,
          IndexedUnifiedExposureController.afterAnswer,
          dagCandidateAfterMemory, inputExact] using
          dag_memory_after_input_preserves_producer_invariant anchorIndex
            state.exposureIndex state.memory input answer invariant sourceFresh
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
          (dagCandidateAfterMemory transitionFuel anchorIndex state
            answer).producers at producerMember
        rcases dag_candidate_memory_producers_eq_or_append transitionFuel
            anchorIndex state answer with unchanged | ⟨slot, appended⟩
        · rw [unchanged] at producerMember
          exact disjoint producer producerMember (by
            simp only [List.map_cons, causalInput?, List.mem_cons]
            exact Or.inr tailMember)
        · rw [appended, List.mem_append] at producerMember
          rcases producerMember with old | added
          · exact disjoint producer old (by
              simp only [List.map_cons, causalInput?, List.mem_cons]
              exact Or.inr tailMember)
          · simp only [List.mem_singleton] at added
            subst producer
            have sourceIsInput :
                (Q16DagProducer.mk answer slot
                    (Option.getD
                      (unifiedInputBeforeAnswer? transitionFuel state.cursor)
                      [])).sourceInput = input := by
              simp [inputExact]
            rw [sourceIsInput] at tailMember
            exact splitInputs.1 tailMember
      rw [indexed_state_after_records_cons]
      exact ih next tailAligned tailOnly splitInputs.2 nextInvariant
        nextDisjoint

#print axioms q16_dag_advanced_slot_cases
#print axioms q16_dag_output_slot_cases
#print axioms dag_preferred_q16_slot_has_producer
#print axioms raw_final_work_key_of_work_input_some_lengths
#print axioms raw_final_work_key_of_absorb_input_some_lengths
#print axioms Q16DagAnchorWellFormed
#print axioms dag_memory_after_input_preserves_anchor_well_formed
#print axioms dag_indexed_state_anchor_well_formed
#print axioms q16_dag_produced_slot_cases
#print axioms q16_dag_producer_source_valid_mono
#print axioms update_q16_dag_producers_preserves_inventory_valid
#print axioms q16_dag_producer_eq_of_slot_eq
#print axioms q16_dag_produced_slot_fresh
#print axioms update_q16_dag_producers_slots_nodup
#print axioms update_q16_dag_producers_source_inputs_nodup
#print axioms Q16DagMemoryProducerInvariant
#print axioms literal_q16_candidate_parses
#print axioms advance_input_is_not_q16_candidate
#print axioms dag_memory_after_input_preserves_tracked_base
#print axioms dag_memory_after_candidate_contains_producer
#print axioms dag_memory_after_advance_contains_producer
#print axioms inactive_dag_memory_producer_invariant
#print axioms dag_memory_after_input_preserves_producer_invariant
#print axioms dag_q16_output_is_preferred_of_producer
#print axioms aligned_machine_records_preserve_dag_producer_invariant

end

end AspisK1.V7Tag73CausalDagProducerInvariant
