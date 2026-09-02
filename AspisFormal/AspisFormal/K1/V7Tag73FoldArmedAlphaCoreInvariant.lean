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
open AspisK1.V7Tag73SqueezeInputStateInjectivity
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

theorem replay_seen_alpha_pass_preserves_producer_invariant
    (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer)
    (usedSlots : Finset (Fin 4))
    (valid : AlphaZeroMemoryProducerInvariant
      { producers := producers, usedSlots := usedSlots }) :
    AlphaZeroMemoryProducerInvariant
      { producers := replaySeenAlphaPass seen producers,
        usedSlots := usedSlots } := by
  induction seen generalizing producers with
  | nil => simpa [replaySeenAlphaPass] using valid
  | cons pair tail ih =>
      simp only [replaySeenAlphaPass, List.foldl_cons]
      by_cases used : pair.1 ∈ producers.map AlphaZeroProducer.sourceInput
      · simp only [used, if_pos]
        exact ih producers valid
      · simp only [used, if_neg]
        apply ih (updateAlphaZeroProducers producers pair.1 pair.2)
        exact
          { inventoryValid :=
              update_alpha_zero_producers_preserves_inventory_valid
                producers pair.1 pair.2 valid.inventoryValid
            blocksNodup := update_alpha_zero_producers_blocks_nodup
              producers pair.1 pair.2 valid.inventoryValid valid.blocksNodup used
            sourceInputsNodup :=
              update_alpha_zero_producers_source_inputs_nodup
                producers pair.1 pair.2 valid.sourceInputsNodup used }

theorem replay_seen_alpha_closure_preserves_producer_invariant
    (fuel : Nat) (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer)
    (usedSlots : Finset (Fin 4))
    (valid : AlphaZeroMemoryProducerInvariant
      { producers := producers, usedSlots := usedSlots }) :
    AlphaZeroMemoryProducerInvariant
      { producers := replaySeenAlphaClosure fuel seen producers,
        usedSlots := usedSlots } := by
  induction fuel generalizing producers with
  | zero => exact valid
  | succ fuel ih =>
      simp only [replaySeenAlphaClosure]
      exact ih (replaySeenAlphaPass seen producers)
        (replay_seen_alpha_pass_preserves_producer_invariant seen producers
          usedSlots valid)

theorem replay_seen_alpha_pass_preserves_block_zero_boundary
    (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer)
    (valid : AlphaZeroBlockZeroBoundaryValid producers) :
    AlphaZeroBlockZeroBoundaryValid
      (replaySeenAlphaPass seen producers) := by
  induction seen generalizing producers with
  | nil => simpa [replaySeenAlphaPass] using valid
  | cons pair tail ih =>
      simp only [replaySeenAlphaPass, List.foldl_cons]
      by_cases used : pair.1 ∈ producers.map AlphaZeroProducer.sourceInput
      · simp only [used, if_pos]
        exact ih producers valid
      · simp only [used, if_neg]
        exact ih (updateAlphaZeroProducers producers pair.1 pair.2)
          (update_alpha_zero_producers_preserves_block_zero_boundary
            producers pair.1 pair.2 valid)

theorem replay_seen_alpha_closure_preserves_block_zero_boundary
    (fuel : Nat) (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer)
    (valid : AlphaZeroBlockZeroBoundaryValid producers) :
    AlphaZeroBlockZeroBoundaryValid
      (replaySeenAlphaClosure fuel seen producers) := by
  induction fuel generalizing producers with
  | zero => exact valid
  | succ fuel ih =>
      simp only [replaySeenAlphaClosure]
      exact ih (replaySeenAlphaPass seen producers)
        (replay_seen_alpha_pass_preserves_block_zero_boundary seen producers
          valid)

/-- One complete cached replay pass contains the exact successor of a parent
whose advance record occurs after the point where that parent is already
available.  If the source input was consumed earlier in the same pass,
first-input uniqueness and the producer invariants identify that earlier
producer with the requested successor. -/
theorem replay_seen_alpha_pass_contains_ordered_advance_successor
    (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer) (usedSlots : Finset (Fin 4))
    (seed parent : AlphaZeroProducer) (advanced : Digest256)
    (bounded : parent.block.val + 1 < 4)
    (seenInputsNodup : (seen.map Prod.fst).Nodup)
    (seedLength : seed.sourceInput.length = 43)
    (currentInvariant : AlphaZeroMemoryProducerInvariant
      { producers := replaySeenAlphaPass seen producers,
        usedSlots := usedSlots })
    (currentBoundary : AlphaZeroBlockZeroBoundaryValid
      (replaySeenAlphaPass seen producers))
    (currentDigestNodup :
      ((replaySeenAlphaPass seen producers).map
        AlphaZeroProducer.digest).Nodup)
    (currentProvenance : ∀ producer,
      producer ∈ replaySeenAlphaPass seen producers →
        producer = seed ∨ (producer.sourceInput, producer.digest) ∈ seen)
    (advanceMember :
      (bytes parent.digest ++ [domAdvance], advanced) ∈ seen)
    (parentOrdered : ∃ seenBefore seenAfter,
      seen = seenBefore ++
        (bytes parent.digest ++ [domAdvance], advanced) :: seenAfter ∧
      parent ∈ replaySeenAlphaPass seenBefore producers) :
    ({ digest := advanced,
        block := ⟨parent.block.val + 1, bounded⟩,
        sourceInput := bytes parent.digest ++ [domAdvance] } :
      AlphaZeroProducer) ∈ replaySeenAlphaPass seen producers := by
  let current := replaySeenAlphaPass seen producers
  let next : AlphaZeroProducer :=
    { digest := advanced,
      block := ⟨parent.block.val + 1, bounded⟩,
      sourceInput := bytes parent.digest ++ [domAdvance] }
  obtain ⟨seenBefore, seenAfter, seenExact, parentBefore⟩ := parentOrdered
  have beforePrefix : replaySeenAlphaPass seenBefore producers <+: current := by
    simpa [current, seenExact] using
      replay_seen_alpha_pass_prefix_of_append seenBefore
      ((bytes parent.digest ++ [domAdvance], advanced) :: seenAfter)
        producers
  have parentMember : parent ∈ current := beforePrefix.subset parentBefore
  by_cases sourceFresh : bytes parent.digest ++ [domAdvance] ∉
      current.map AlphaZeroProducer.sourceInput
  · have beforeDigestNodup :
        ((replaySeenAlphaPass seenBefore producers).map
          AlphaZeroProducer.digest).Nodup :=
      (beforePrefix.map AlphaZeroProducer.digest).nodup currentDigestNodup
    have beforeSourceFresh : bytes parent.digest ++ [domAdvance] ∉
        (replaySeenAlphaPass seenBefore producers).map
          AlphaZeroProducer.sourceInput := by
      intro member
      apply sourceFresh
      exact (beforePrefix.map AlphaZeroProducer.sourceInput).subset member
    subst seen
    simpa [next] using
      replay_seen_alpha_pass_append_advance_contains_next seenBefore seenAfter
        producers parent advanced bounded parentBefore beforeDigestNodup
          beforeSourceFresh
  · have sourceUsed : bytes parent.digest ++ [domAdvance] ∈
        current.map AlphaZeroProducer.sourceInput := by
      simpa using sourceFresh
    obtain ⟨existing, existingMember, existingSource⟩ :=
      List.mem_map.mp sourceUsed
    have existingNotSeed : existing ≠ seed := by
      intro exact
      subst existing
      have lengthExact := congrArg List.length existingSource
      simp [seedLength, bytes_length] at lengthExact
    have existingSeen : (existing.sourceInput, existing.digest) ∈ seen :=
      (currentProvenance existing existingMember).resolve_left existingNotSeed
    have digestExact : existing.digest = advanced := by
      have pairExact :
          (existing.sourceInput, existing.digest) =
            (bytes parent.digest ++ [domAdvance], advanced) :=
        List.inj_on_of_nodup_map seenInputsNodup existingSeen advanceMember
          (by simpa using existingSource)
      injection pairExact
    have existingPositive : existing.block.val ≠ 0 := by
      intro zero
      have boundaryLength := currentBoundary existing existingMember zero
      have lengthExact := congrArg List.length existingSource
      simp [boundaryLength, bytes_length] at lengthExact
    rcases currentInvariant.inventoryValid existing existingMember with
      existingZero | ⟨otherParent, otherParentMember, successor,
        sourceExact⟩
    · exact (existingPositive existingZero).elim
    · have parentDigestExact : otherParent.digest = parent.digest := by
        apply digest_bytes_injective
        have fullExact : bytes otherParent.digest ++ [domAdvance] =
            bytes parent.digest ++ [domAdvance] := by
          rw [← sourceExact]
          exact existingSource
        have prefixExact := congrArg (List.take 32) fullExact
        simpa [bytes_length] using prefixExact
      have parentExact : otherParent = parent := by
        apply List.inj_on_of_nodup_map currentDigestNodup
          otherParentMember parentMember
        exact parentDigestExact
      have blockExact : existing.block =
          ⟨parent.block.val + 1, bounded⟩ := by
        apply Fin.ext
        simpa [parentExact] using successor.symm
      have existingExact : existing = next := by
        cases existing
        simp only [next, AlphaZeroProducer.mk.injEq]
        exact ⟨digestExact, blockExact, existingSource⟩
      simpa [current, next, ← existingExact] using existingMember

theorem cached_alpha_producer_closure_invariant
    (seen : List (ShaInput × Digest256))
    (target : ShaInput) (boundaryAnswer : Digest256)
    (usedSlots : Finset (Fin 4))
    (targetLength : target.length = 43) :
    AlphaZeroMemoryProducerInvariant
        { producers := cachedAlphaProducerClosure seen target boundaryAnswer,
          usedSlots := usedSlots } ∧
      AlphaZeroBlockZeroBoundaryValid
        (cachedAlphaProducerClosure seen target boundaryAnswer) := by
  let seed : AlphaZeroProducer :=
    { digest := boundaryAnswer, block := 0, sourceInput := target }
  have seedProducer : AlphaZeroMemoryProducerInvariant
      { producers := [seed], usedSlots := usedSlots } := by
    constructor
    · intro producer member
      simp only [List.mem_singleton] at member
      subst producer
      exact Or.inl rfl
    · simp
    · simp
  have seedBoundary : AlphaZeroBlockZeroBoundaryValid [seed] := by
    intro producer member _zero
    simp only [List.mem_singleton] at member
    subst producer
    exact targetLength
  exact ⟨
    replay_seen_alpha_closure_preserves_producer_invariant 3 seen [seed]
      usedSlots seedProducer,
    replay_seen_alpha_closure_preserves_block_zero_boundary 3 seen [seed]
      seedBoundary⟩

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
          have closed := cached_alpha_producer_closure_invariant
            state.memory.seenMachine target boundaryAnswer
              state.memory.alpha.usedSlots targetLength
          refine
            { producer := ?_
              blockZeroBoundary := ?_
              expectedBoundaryLength := ?_ }
          · simpa [parsed, cached] using closed.1
          · simpa [parsed, cached] using closed.2
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
#print axioms replay_seen_alpha_pass_contains_ordered_advance_successor
#print axioms arm_fold_alpha_memory_preserves_core
#print axioms fold_armed_alpha_after_memory_preserves_core

end

end AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
