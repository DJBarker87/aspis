import AspisFormal.K1.V7Tag73AlphaZeroProducerInvariant

/-!
# Boundary-source invariant for alpha-zero producers

Block zero can only be installed by the literal 43-byte fold-nonce boundary.
Every later producer comes from an advance edge and therefore has positive
block index.  This invariant is independent of the actor/query schedule.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaZeroBoundaryInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def AlphaZeroBlockZeroBoundaryValid
    (producers : List AlphaZeroProducer) : Prop :=
  ∀ producer ∈ producers, producer.block.val = 0 →
    producer.sourceInput.length = 43

theorem update_alpha_zero_producers_preserves_block_zero_boundary
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256)
    (valid : AlphaZeroBlockZeroBoundaryValid producers) :
    AlphaZeroBlockZeroBoundaryValid
      (updateAlphaZeroProducers producers input answer) := by
  intro producer member blockZero
  rcases update_alpha_zero_producers_eq_or_append producers input answer with
    unchanged | ⟨block, appended⟩
  · rw [unchanged] at member
    exact valid producer member blockZero
  · rw [appended, List.mem_append] at member
    rcases member with old | added
    · exact valid producer old blockZero
    · simp only [List.mem_singleton] at added
      subst producer
      unfold updateAlphaZeroProducers at appended
      cases advanced : alphaZeroAdvancedSlot? producers input with
      | none => simp [advanced] at appended
      | some selected =>
          have blockExact : block = selected := by
            simp only [advanced] at appended
            have singletonExact := List.append_cancel_left appended
            have selectedExact : selected = block := by
              simpa using singletonExact
            exact selectedExact.symm
          subst selected
          obtain ⟨parent, parentMember, inputExact, successor⟩ :=
            alpha_zero_advanced_slot_cases producers input block advanced
          simp at blockZero
          omega

theorem alpha_zero_after_memory_preserves_block_zero_boundary
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256)
    (valid : AlphaZeroBlockZeroBoundaryValid state.memory.producers) :
    AlphaZeroBlockZeroBoundaryValid
      (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers := by
  unfold alphaZeroAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simpa [inputExact] using valid
  | some input =>
      simp only [inputExact]
      split
      next boundary =>
        intro producer member _blockZero
        simp only [List.mem_singleton] at member
        subst producer
        unfold isAlphaZeroBoundaryInput at boundary
        simp only [Bool.and_eq_true, decide_eq_true_eq] at boundary
        exact boundary.2.1.1
      next _boundary =>
        exact update_alpha_zero_producers_preserves_block_zero_boundary
          state.memory.producers input answer valid

theorem alpha_zero_indexed_state_preserves_block_zero_boundary
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      AlphaZeroBlockZeroBoundaryValid state.memory.producers →
      AlphaZeroBlockZeroBoundaryValid
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          records state).memory.producers := by
  intro records
  induction records with
  | nil => intro state valid; simpa using valid
  | cons record records ih =>
      intro state valid
      rw [indexed_state_after_records_cons]
      apply ih
      change AlphaZeroBlockZeroBoundaryValid
        (alphaZeroAfterMemory transitionFuel boundaryIndex state
          record.answer).producers
      exact alpha_zero_after_memory_preserves_block_zero_boundary
        transitionFuel boundaryIndex state record.answer valid

theorem inactive_alpha_zero_block_zero_boundary_valid :
    AlphaZeroBlockZeroBoundaryValid inactiveAlphaZeroMemory.producers := by
  simp [AlphaZeroBlockZeroBoundaryValid, inactiveAlphaZeroMemory]

#print axioms AlphaZeroBlockZeroBoundaryValid
#print axioms update_alpha_zero_producers_preserves_block_zero_boundary
#print axioms alpha_zero_after_memory_preserves_block_zero_boundary
#print axioms alpha_zero_indexed_state_preserves_block_zero_boundary
#print axioms inactive_alpha_zero_block_zero_boundary_valid

end

end AspisK1.V7Tag73AlphaZeroBoundaryInvariant
