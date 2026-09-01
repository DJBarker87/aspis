import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16ControllerComposition

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
open AspisK1.V7Tag73TranscriptSchedule

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

def updateAlphaZeroProducers (producers : List AlphaZeroProducer)
    (input : ShaInput) (answer : Digest256) : List AlphaZeroProducer :=
  match alphaZeroAdvancedSlot? producers input with
  | none => producers
  | some block => producers ++ [{ digest := answer, block := block }]

theorem update_alpha_zero_producers_eq_or_append
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256) :
    updateAlphaZeroProducers producers input answer = producers ∨
      ∃ block, updateAlphaZeroProducers producers input answer =
        producers ++ [{ digest := answer, block := block }] := by
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
          [{ digest := answer, block := ⟨0, by omega⟩ }]
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
      [{ digest := answer, block := ⟨0, by omega⟩ }] := by
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
#print axioms updateAlphaZeroProducers
#print axioms update_alpha_zero_producers_prefix
#print axioms alphaZeroCausalController
#print axioms alpha_zero_after_boundary_has_block_zero_producer
#print axioms alpha_zero_preferred_of_output_match
#print axioms alpha_zero_selected_slot_used_after_answer
#print axioms exactCompilerConcreteAlphaFinalWorkQ16Router

end

end AspisK1.V7Tag73AlphaZeroCausalController
