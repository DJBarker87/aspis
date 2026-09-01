import AspisFormal.K1.V7Tag73AlphaZeroBoundaryInvariant
import AspisFormal.K1.V7Tag73FoldArmedAlphaZeroController

/-!
# Core producer invariant for the fold-armed alpha controller

The dynamically armed controller may seed block zero from an earlier cached
machine query or from the later literal boundary exposure.  In either case the
seed remains a 43-byte boundary producer; every other producer is introduced
only by the established alpha advance rule.  This file isolates that fact from
the accepted-root provenance argument used by q16 separation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldArmedAlphaCoreInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AlphaZeroBoundaryInvariant
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The fold-derived boundary parser always produces the exact 43-byte input
shape required by the alpha/q16 structural separation theorem. -/
theorem fold_work_input_to_alpha_boundary_length
    (input target : ShaInput)
    (parsed : foldWorkInputToAlphaBoundary? input = some target) :
    target.length = 43 := by
  unfold foldWorkInputToAlphaBoundary? at parsed
  split at parsed
  next accepted =>
    have inputLength : input.length = 41 := accepted.1
    injection parsed with targetExact
    subst target
    simp only [List.length_append, List.length_cons, List.length_nil]
    have takeLength : (input.take 32).length = 32 := by
      rw [List.length_take, inputLength]
      omega
    have dropLength : (input.drop 33).length = 8 := by
      rw [List.length_drop, inputLength]
    omega
  next rejected => contradiction

/-- The inventory facts needed by alpha/q16 disjointness, together with the
well-formedness of any dynamically armed boundary. -/
structure FoldArmedAlphaCoreInvariant
    (memory : FoldArmedAlphaZeroMemory) : Prop where
  producer : AlphaZeroMemoryProducerInvariant memory.alpha
  blockZeroBoundary :
    AlphaZeroBlockZeroBoundaryValid memory.alpha.producers
  expectedBoundaryLength : ∀ target,
    memory.expectedBoundary = some target → target.length = 43

theorem inactive_fold_armed_alpha_core_invariant :
    FoldArmedAlphaCoreInvariant inactiveFoldArmedAlphaZeroMemory := by
  refine
    { producer := inactive_alpha_zero_memory_producer_invariant
      blockZeroBoundary := inactive_alpha_zero_block_zero_boundary_valid
      expectedBoundaryLength := ?_ }
  intro target impossible
  simp [inactiveFoldArmedAlphaZeroMemory] at impossible

/-- Arming at the selected fold preserves the recursive producer inventory.
If the boundary was queried earlier, its cached answer becomes the unique
block-zero seed; otherwise the existing (pre-fold empty in the exact replay)
inventory is retained. -/
theorem arm_fold_alpha_memory_preserves_core
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256)
    (invariant : FoldArmedAlphaCoreInvariant state.memory) :
    FoldArmedAlphaCoreInvariant
      (armFoldAlphaMemory transitionFuel state answer) := by
  unfold armFoldAlphaMemory
  cases parsed : armFoldAlphaBoundary transitionFuel state with
  | none => simpa [parsed] using invariant
  | some target =>
      have targetLength : target.length = 43 := by
        unfold armFoldAlphaBoundary at parsed
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
        | none => simp [inputExact] at parsed
        | some input =>
            simp only [inputExact, Option.bind_some] at parsed
            exact fold_work_input_to_alpha_boundary_length input target parsed
      cases cached : seenMachineAnswer? state.memory target with
      | none =>
          refine
            { producer := ?_
              blockZeroBoundary := ?_
              expectedBoundaryLength := ?_ }
          · simpa [parsed, cached] using invariant.producer
          · simpa [parsed, cached] using invariant.blockZeroBoundary
          · intro selected selectedExact
            simp [parsed, cached] at selectedExact
            simpa [selectedExact] using targetLength
      | some boundaryAnswer =>
          refine
            { producer := ?_
              blockZeroBoundary := ?_
              expectedBoundaryLength := ?_ }
          · constructor
            · intro producer member
              simp [parsed, cached] at member
              subst producer
              exact Or.inl rfl
            · simp [parsed, cached]
            · simp [parsed, cached]
          · intro producer member blockZero
            simp [parsed, cached] at member
            subst producer
            exact targetLength
          · intro selected selectedExact
            simp [parsed, cached] at selectedExact
            simpa [selectedExact] using targetLength

/-- One ordinary post-fold step preserves the core invariant whenever the
current source input has not already occurred in the producer inventory. -/
theorem fold_armed_alpha_after_memory_preserves_core
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256)
    (invariant : FoldArmedAlphaCoreInvariant state.memory)
    (sourceFresh : ∀ input,
      unifiedInputBeforeAnswer? transitionFuel state.cursor = some input →
      input ∉ state.memory.alpha.producers.map AlphaZeroProducer.sourceInput) :
    FoldArmedAlphaCoreInvariant
      (foldArmedAlphaAfterMemory transitionFuel state answer) := by
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none =>
      simpa [foldArmedAlphaAfterMemory, inputExact] using invariant
  | some input =>
      have fresh := sourceFresh input inputExact
      have expectedExact :
          (foldArmedAlphaAfterMemory transitionFuel state answer).expectedBoundary =
            state.memory.expectedBoundary := by
        simp [foldArmedAlphaAfterMemory, inputExact]
      by_cases boundary : state.memory.expectedBoundary = some input
      · have boundaryLength := invariant.expectedBoundaryLength input boundary
        have alphaExact := fold_armed_alpha_exact_boundary_installs_block_zero
          transitionFuel state input answer inputExact boundary
        refine
          { producer := ?_
            blockZeroBoundary := ?_
            expectedBoundaryLength := ?_ }
        · constructor
          · intro producer member
            simp [foldArmedAlphaAfterMemory, inputExact, boundary] at member
            subst producer
            exact Or.inl rfl
          · simp [foldArmedAlphaAfterMemory, inputExact, boundary]
          · simp [foldArmedAlphaAfterMemory, inputExact, boundary]
        · intro producer member blockZero
          simp [foldArmedAlphaAfterMemory, inputExact, boundary] at member
          subst producer
          exact boundaryLength
        · intro target targetExact
          apply invariant.expectedBoundaryLength target
          rw [← expectedExact]
          exact targetExact
      · refine
          { producer := ?_
            blockZeroBoundary := ?_
            expectedBoundaryLength := ?_ }
        · have producersExact :=
            fold_armed_alpha_nonboundary_uses_advance_update transitionFuel
              state input answer inputExact boundary
          constructor
          · rw [producersExact]
            exact update_alpha_zero_producers_preserves_inventory_valid
              state.memory.alpha.producers input answer
                invariant.producer.inventoryValid
          · rw [producersExact]
            exact update_alpha_zero_producers_blocks_nodup
              state.memory.alpha.producers input answer
                invariant.producer.inventoryValid invariant.producer.blocksNodup
                  fresh
          · rw [producersExact]
            exact update_alpha_zero_producers_source_inputs_nodup
              state.memory.alpha.producers input answer
                invariant.producer.sourceInputsNodup fresh
        · rw [fold_armed_alpha_nonboundary_uses_advance_update
            transitionFuel state input answer inputExact boundary]
          exact update_alpha_zero_producers_preserves_block_zero_boundary
            state.memory.alpha.producers input answer
              invariant.blockZeroBoundary
        · intro target targetExact
          apply invariant.expectedBoundaryLength target
          rw [← expectedExact]
          exact targetExact

#print axioms fold_work_input_to_alpha_boundary_length
#print axioms arm_fold_alpha_memory_preserves_core
#print axioms fold_armed_alpha_after_memory_preserves_core

end

end AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
