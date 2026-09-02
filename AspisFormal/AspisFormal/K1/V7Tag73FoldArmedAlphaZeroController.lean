import AspisFormal.K1.V7Tag73AlphaZeroCausalController
import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates

/-!
# Fold-armed causal controller for the deployed alpha-zero sampler

The older alpha controller is parameterised by the root ordinal of the
fold-nonce absorption.  That is suitable for a source theorem after the fact,
but not for the probability router: the ordinal is answer-tape dependent and
therefore cannot be fixed to zero on every fibre.

This module removes that mismatch.  At the already selected fold-work
exposure, the controller sees the literal SHA input *before* its answer.  That
input contains both the pre-fold digest and selected nonce, so it determines
the exact subsequent fold-nonce absorption input.  The controller stores that
input and installs alpha block zero only when the exact input is encountered.
No answer, logical role classifier, SHA injectivity, or adversary-origin
assumption is used to arm the boundary.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldArmedAlphaZeroController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Construct the exact fold-nonce absorb input from a candidate fold-work
input.  The deployed work input is 32 digest bytes, `domGrind`, and an
eight-byte nonce.  Malformed inputs do not arm the alpha boundary. -/
def foldWorkInputToAlphaBoundary? (input : ShaInput) : Option ShaInput :=
  if input.length = 41 ∧ input[32]? = some domGrind then
    some (input.take 32 ++ [domAbsorb, foldWorkNonceLabel, 0] ++ input.drop 33)
  else
    none

/-- The literal accepted fold-work input determines exactly the deployed
fold-nonce absorption input. -/
@[simp] theorem literal_fold_work_arms_exact_alpha_boundary
    (digest : Digest256) (nonce : NonceBytes) :
    foldWorkInputToAlphaBoundary?
        (bytes digest ++ [domGrind] ++ bytes nonce) =
      some (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++ bytes nonce) := by
  have dropExact :
      List.drop 33 (bytes digest ++ domGrind :: bytes nonce) = bytes nonce := by
    simpa using
      (List.drop_length_add_append (l₁ := bytes digest)
        (l₂ := domGrind :: bytes nonce) 1)
  simp [foldWorkInputToAlphaBoundary?, bytes_length, dropExact]

/-- Alpha memory augmented with the exact boundary input learned at the
selected fold-work exposure. -/
structure FoldArmedAlphaZeroMemory where
  expectedBoundary : Option ShaInput
  /-- Chronological machine-fresh coordinates already exposed to the causal
  controller.  Fork outputs are deliberately absent. -/
  seenMachine : List (ShaInput × Digest256)
  alpha : AlphaZeroControllerMemory
  deriving DecidableEq

def inactiveFoldArmedAlphaZeroMemory : FoldArmedAlphaZeroMemory :=
  { expectedBoundary := none
    seenMachine := []
    alpha := inactiveAlphaZeroMemory }

def foldArmedAlphaIndexedState
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory) :
    IndexedUnifiedExposureState globalOracleCalls AlphaZeroControllerMemory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.alpha }

/-- Arm from the current pre-answer input.  This operation is intended to be
invoked exactly at the already selected fold-work exposure. -/
def armFoldAlphaBoundary
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory) : Option ShaInput :=
  (unifiedInputBeforeAnswer? transitionFuel state.cursor).bind
    foldWorkInputToAlphaBoundary?

/-- Lookup in the immutable oracle table visible at the current pre-answer
machine pause.  Fork coordinates are not machine-table pauses and therefore
return `none`. -/
def unifiedCachedAnswerBefore?
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (target : ShaInput) : Option Digest256 :=
  match seekUnifiedExposure transitionFuel cursor with
  | .machineFresh _limits _limitBound _actor state _input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      (lookupEntry state target).map TableEntry.output
  | .forkOutput .. | .forkAdvance .. | .halted | .transitionLimit => none

/-- The current input only when the next unified exposure is a genuine
machine-table first creation. -/
def unifiedMachineFreshInputBefore?
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Option ShaInput :=
  match seekUnifiedExposure transitionFuel cursor with
  | .machineFresh _limits _limitBound _actor _state input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      some input
  | .forkOutput .. | .forkAdvance .. | .halted | .transitionLimit => none

theorem unified_machine_fresh_input_is_unified_input
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (input : ShaInput)
    (exact : unifiedMachineFreshInputBefore? transitionFuel cursor =
      some input) :
    unifiedInputBeforeAnswer? transitionFuel cursor = some input := by
  unfold unifiedMachineFreshInputBefore? at exact
  unfold unifiedInputBeforeAnswer?
  generalize requestExact : seekUnifiedExposure transitionFuel cursor = request
  cases request <;> simp_all

/-- First already-exposed machine answer for an exact input.  The causal
controller records a pair only after seeing its answer, so this lookup cannot
inspect the current or any future tape coordinate. -/
def seenMachineAnswer? (memory : FoldArmedAlphaZeroMemory)
    (target : ShaInput) : Option Digest256 :=
  (memory.seenMachine.find? (fun pair => pair.1 = target)).map Prod.snd

/-- Replay one bounded alpha-producer discovery pass over coordinates whose
answers were exposed before the fold controller was armed.  A source input is
used at most once, making repeated passes idempotent on already discovered
edges.  This is deliberately an after-the-fact inventory update: earlier
answers keep their original residual coordinates, while later children can be
labelled from facts already present in the causal memory. -/
def replaySeenAlphaPass (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer) : List AlphaZeroProducer :=
  seen.foldl (fun current pair =>
    if pair.1 ∈ current.map AlphaZeroProducer.sourceInput then
      current
    else
      updateAlphaZeroProducers current pair.1 pair.2) producers

/-- Iterate cached discovery through the maximum three advance edges following
block zero.  Three passes suffice even for reverse-ordered adversarial
prequeries and cannot change the deployed four-block cap. -/
def replaySeenAlphaClosure : Nat → List (ShaInput × Digest256) →
    List AlphaZeroProducer → List AlphaZeroProducer
  | 0, _seen, producers => producers
  | fuel + 1, seen, producers =>
      replaySeenAlphaClosure fuel seen (replaySeenAlphaPass seen producers)

def cachedAlphaProducerClosure (seen : List (ShaInput × Digest256))
    (target : ShaInput) (boundaryAnswer : Digest256) :
    List AlphaZeroProducer :=
  replaySeenAlphaClosure 3 seen
    [{ digest := boundaryAnswer, block := 0, sourceInput := target }]

/-- Append the current coordinate exactly when the unified scheduler is at a
machine-fresh exposure. -/
def rememberCurrentMachine
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) : List (ShaInput × Digest256) :=
  match unifiedMachineFreshInputBefore? transitionFuel state.cursor with
  | none => state.memory.seenMachine
  | some input => state.memory.seenMachine ++ [(input, answer)]

theorem remember_current_machine_contains_prior
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) (pair : ShaInput × Digest256)
    (member : pair ∈ state.memory.seenMachine) :
    pair ∈ rememberCurrentMachine transitionFuel state answer := by
  unfold rememberCurrentMachine
  split
  · exact member
  · exact List.mem_append_left _ member

/-- Arm the exact future boundary, installing block zero immediately when an
adversary-first query has already populated that coordinate.  Otherwise the
ordinary future-boundary branch remains armed. -/
def armFoldAlphaMemory
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) : FoldArmedAlphaZeroMemory :=
  match armFoldAlphaBoundary transitionFuel state with
  | none => state.memory
  | some target =>
      match seenMachineAnswer? state.memory target with
      | none =>
          { state.memory with
            expectedBoundary := some target
            seenMachine := rememberCurrentMachine transitionFuel state answer }
      | some boundaryAnswer =>
          { expectedBoundary := some target
            seenMachine := rememberCurrentMachine transitionFuel state answer
            alpha :=
              { producers := cachedAlphaProducerClosure
                  state.memory.seenMachine target boundaryAnswer
                usedSlots := state.memory.alpha.usedSlots } }

theorem arm_fold_alpha_memory_expected_boundary
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (target : ShaInput) (answer : Digest256)
    (armed : armFoldAlphaBoundary transitionFuel state = some target) :
    (armFoldAlphaMemory transitionFuel state answer).expectedBoundary =
      some target := by
  simp only [armFoldAlphaMemory, armed]
  split <;> rfl

theorem replay_seen_alpha_pass_prefix
    (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer) :
    producers <+: replaySeenAlphaPass seen producers := by
  induction seen generalizing producers with
  | nil => simp [replaySeenAlphaPass]
  | cons pair tail ih =>
      simp only [replaySeenAlphaPass, List.foldl_cons]
      split
      · exact List.IsPrefix.trans (List.prefix_refl _) (ih producers)
      · exact List.IsPrefix.trans
          (update_alpha_zero_producers_prefix producers pair.1 pair.2)
          (ih (updateAlphaZeroProducers producers pair.1 pair.2))

theorem replay_seen_alpha_pass_member_old_or_seen
    (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer) (producer : AlphaZeroProducer)
    (member : producer ∈ replaySeenAlphaPass seen producers) :
    producer ∈ producers ∨
      (producer.sourceInput, producer.digest) ∈ seen := by
  induction seen generalizing producers with
  | nil => exact Or.inl (by simpa [replaySeenAlphaPass] using member)
  | cons pair tail ih =>
      simp only [replaySeenAlphaPass, List.foldl_cons] at member
      rcases ih _ member with nextMember | tailMember
      · by_cases used : pair.1 ∈
            producers.map AlphaZeroProducer.sourceInput
        · left
          simpa [used] using nextMember
        · have updated : producer ∈
              updateAlphaZeroProducers producers pair.1 pair.2 := by
            simpa [used] using nextMember
          rcases update_alpha_zero_producers_new_digest producers pair.1
              pair.2 producer updated with old | ⟨digest, source⟩
          · exact Or.inl old
          · right
            simp only [List.mem_cons]
            left
            cases pair
            simp_all
      · exact Or.inr (List.mem_cons_of_mem _ tailMember)

theorem replay_seen_alpha_closure_prefix
    (fuel : Nat) (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer) :
    producers <+: replaySeenAlphaClosure fuel seen producers := by
  induction fuel generalizing producers with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
      simp only [replaySeenAlphaClosure]
      exact List.IsPrefix.trans (replay_seen_alpha_pass_prefix seen producers)
        (ih (replaySeenAlphaPass seen producers))

theorem replay_seen_alpha_closure_member_old_or_seen
    (fuel : Nat) (seen : List (ShaInput × Digest256))
    (producers : List AlphaZeroProducer) (producer : AlphaZeroProducer)
    (member : producer ∈ replaySeenAlphaClosure fuel seen producers) :
    producer ∈ producers ∨
      (producer.sourceInput, producer.digest) ∈ seen := by
  induction fuel generalizing producers with
  | zero => exact Or.inl member
  | succ fuel ih =>
      simp only [replaySeenAlphaClosure] at member
      rcases ih _ member with passMember | seenMember
      · exact replay_seen_alpha_pass_member_old_or_seen seen producers
          producer passMember
      · exact Or.inr seenMember

theorem cached_alpha_producer_closure_member_seed_or_seen
    (seen : List (ShaInput × Digest256))
    (target : ShaInput) (boundaryAnswer : Digest256)
    (producer : AlphaZeroProducer)
    (member : producer ∈
      cachedAlphaProducerClosure seen target boundaryAnswer) :
    producer = (⟨boundaryAnswer, 0, target⟩ : AlphaZeroProducer) ∨
      (producer.sourceInput, producer.digest) ∈ seen := by
  rcases replay_seen_alpha_closure_member_old_or_seen 3 seen
      [{ digest := boundaryAnswer, block := 0, sourceInput := target }]
      producer member with seed | seenMember
  · left
    simpa using seed
  · exact Or.inr seenMember

theorem cached_alpha_producer_closure_contains_block_zero
    (seen : List (ShaInput × Digest256))
    (target : ShaInput) (boundaryAnswer : Digest256) :
    ({ digest := boundaryAnswer, block := 0, sourceInput := target } :
        AlphaZeroProducer) ∈
      cachedAlphaProducerClosure seen target boundaryAnswer := by
  apply (replay_seen_alpha_closure_prefix 3 seen [_]).subset
  simp

theorem arm_fold_alpha_memory_cached_contains_block_zero
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (target : ShaInput) (answer boundaryAnswer : Digest256)
    (armed : armFoldAlphaBoundary transitionFuel state = some target)
    (cached : seenMachineAnswer? state.memory target = some boundaryAnswer) :
    ({ digest := boundaryAnswer, block := 0, sourceInput := target } :
        AlphaZeroProducer) ∈
      (armFoldAlphaMemory transitionFuel state answer).alpha.producers := by
  simp only [armFoldAlphaMemory, armed, cached]
  exact cached_alpha_producer_closure_contains_block_zero
    state.memory.seenMachine target boundaryAnswer

theorem arm_fold_alpha_memory_uncached_retains_inventory
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (target : ShaInput) (answer : Digest256)
    (armed : armFoldAlphaBoundary transitionFuel state = some target)
    (uncached : seenMachineAnswer? state.memory target = none) :
    (armFoldAlphaMemory transitionFuel state answer).alpha =
      state.memory.alpha := by
  simp [armFoldAlphaMemory, armed, uncached]

theorem arm_fold_alpha_memory_seen_machine_monotone
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) (pair : ShaInput × Digest256)
    (member : pair ∈ state.memory.seenMachine) :
    pair ∈ (armFoldAlphaMemory transitionFuel state answer).seenMachine := by
  unfold armFoldAlphaMemory
  split
  · exact member
  · split <;> exact remember_current_machine_contains_prior
      transitionFuel state answer pair member

/-- Arming changes only the expected boundary, causal cache, and possibly the
producer seed.  It never consumes or restores an alpha coordinate. -/
theorem arm_fold_alpha_memory_used_slots
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) :
    (armFoldAlphaMemory transitionFuel state answer).alpha.usedSlots =
      state.memory.alpha.usedSlots := by
  unfold armFoldAlphaMemory
  split
  · rfl
  · split <;> rfl

/-- Dynamic alpha update.  An exact armed-boundary match resets the producer
inventory to block zero; every other input follows the ordinary append-only
advance logic.  The used-slot set is never reset. -/
def foldArmedAlphaAfterMemory
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) : FoldArmedAlphaZeroMemory :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => state.memory
  | some input =>
      let alphaState := foldArmedAlphaIndexedState state
      let nextUsed :=
        match alphaZeroPreferredSlot transitionFuel alphaState with
        | none => state.memory.alpha.usedSlots
        | some slot => insert slot state.memory.alpha.usedSlots
      let nextProducers :=
        if state.memory.expectedBoundary = some input then
          [{ digest := answer, block := 0, sourceInput := input }]
        else
          updateAlphaZeroProducers state.memory.alpha.producers input answer
      let nextAlpha : AlphaZeroControllerMemory :=
        { producers := nextProducers, usedSlots := nextUsed }
      { expectedBoundary := state.memory.expectedBoundary
        seenMachine := rememberCurrentMachine transitionFuel state answer
        alpha := nextAlpha }

theorem fold_armed_alpha_after_memory_seen_machine_monotone
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) (pair : ShaInput × Digest256)
    (member : pair ∈ state.memory.seenMachine) :
    pair ∈
      (foldArmedAlphaAfterMemory transitionFuel state answer).seenMachine := by
  unfold foldArmedAlphaAfterMemory
  split
  · exact member
  · exact remember_current_machine_contains_prior transitionFuel state
      answer pair member

/-- The dynamic alpha controller consumes exactly the slot preferred before
the answer, and never removes an already consumed slot.  Boundary arming may
replace the producer inventory, but it deliberately cannot reset this
one-shot inventory. -/
theorem fold_armed_alpha_after_memory_used_slots
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) :
    (foldArmedAlphaAfterMemory transitionFuel state answer).alpha.usedSlots =
      match alphaZeroPreferredSlot transitionFuel
          (foldArmedAlphaIndexedState state) with
      | none => state.memory.alpha.usedSlots
      | some slot => insert slot state.memory.alpha.usedSlots := by
  unfold foldArmedAlphaAfterMemory
  split
  · simp [alphaZeroPreferredSlot, foldArmedAlphaIndexedState, *]
  · rfl

def foldArmedAlphaZeroController
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256 (Fin 4)
      FoldArmedAlphaZeroMemory where
  preferredSlot := fun state =>
    alphaZeroPreferredSlot transitionFuel (foldArmedAlphaIndexedState state)
  afterMemory := fun state answer =>
    foldArmedAlphaAfterMemory transitionFuel state answer

@[simp] theorem fold_armed_alpha_preferred
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory) :
    (foldArmedAlphaZeroController transitionFuel).preferredSlot state =
      alphaZeroPreferredSlot transitionFuel
        (foldArmedAlphaIndexedState state) := by
  rfl

/-- Once armed, an exact boundary encounter installs precisely the returned
digest as alpha block zero. -/
theorem fold_armed_alpha_exact_boundary_installs_block_zero
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (armed : state.memory.expectedBoundary = some input) :
    (foldArmedAlphaAfterMemory transitionFuel state answer).alpha.producers =
      [{ digest := answer, block := 0, sourceInput := input }] := by
  simp [foldArmedAlphaAfterMemory, inputExact, armed]

/-- A non-boundary step retains the established alpha advance semantics. -/
theorem fold_armed_alpha_nonboundary_uses_advance_update
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (notBoundary : state.memory.expectedBoundary ≠ some input) :
    (foldArmedAlphaAfterMemory transitionFuel state answer).alpha.producers =
      updateAlphaZeroProducers state.memory.alpha.producers input answer := by
  simp [foldArmedAlphaAfterMemory, inputExact, notBoundary]

/-! ## Fold/final/q16 composition -/

/-- Complete causal memory.  The selected fold slot is used once; the
underlying product retains the armed alpha state and the established
final-work/q16 DAG state. -/
abbrev FoldArmedCompleteMemory :=
  Bool × AlphaFinalWorkQ16ControllerMemory FoldArmedAlphaZeroMemory

def foldArmedUnderlyingState
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory) :
    IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory FoldArmedAlphaZeroMemory) :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.2 }

def foldArmedAlphaState
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory) :
    IndexedUnifiedExposureState globalOracleCalls FoldArmedAlphaZeroMemory :=
  alphaIndexedState (foldArmedUnderlyingState state)

/-- The complete 518-slot controller.  At the selected fold exposure it both
labels the fold-work answer and arms the exact future alpha boundary from the
current input.  All other alpha/final/q16 behavior is delegated to the
established product controller. -/
def foldArmedCompleteController
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16DigestSlot FoldArmedCompleteMemory where
  preferredSlot := fun state =>
    if state.memory.1 = false ∧ state.exposureIndex = foldExposureIndex then
      some none
    else
      ((alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
        (foldArmedAlphaZeroController transitionFuel)).preferredSlot
          (foldArmedUnderlyingState state)).map some
  afterMemory := fun state answer =>
    let underlyingNext :=
      (alphaFinalWorkQ16DagController transitionFuel finalWorkAnchorIndex
        (foldArmedAlphaZeroController transitionFuel)).afterMemory
          (foldArmedUnderlyingState state) answer
    let alphaNext :=
      if state.exposureIndex = foldExposureIndex then
        armFoldAlphaMemory transitionFuel (foldArmedAlphaState state) answer
      else
        underlyingNext.1
    (state.memory.1 || decide (state.exposureIndex = foldExposureIndex),
      (alphaNext, underlyingNext.2))

@[simp] theorem fold_armed_complete_preferred_at_fold
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (unused : state.memory.1 = false)
    (atFold : state.exposureIndex = foldExposureIndex) :
    (foldArmedCompleteController transitionFuel foldExposureIndex
      finalWorkAnchorIndex).preferredSlot state = some none := by
  simp [foldArmedCompleteController, unused, atFold]

/-- Complete-controller replay never forgets a machine coordinate already
recorded in its causal memory. -/
theorem fold_armed_complete_seen_machine_monotone
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (answer : Digest256) (pair : ShaInput × Digest256)
    (member : pair ∈ state.memory.2.1.seenMachine) :
    pair ∈
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterMemory state answer).2.1.seenMachine := by
  simp only [foldArmedCompleteController]
  split
  · exact arm_fold_alpha_memory_seen_machine_monotone transitionFuel
      (foldArmedAlphaState state) answer pair member
  · simp only [alphaFinalWorkQ16DagController,
      foldArmedAlphaZeroController, foldArmedAlphaAfterMemory,
      alphaIndexedState, foldArmedUnderlyingState]
    exact fold_armed_alpha_after_memory_seen_machine_monotone transitionFuel
      (foldArmedAlphaState state) answer pair member

/-- Every aligned machine exposure strictly before the selected fold ordinal
is appended to the causal seen-machine memory. -/
theorem fold_armed_complete_before_fold_remembers_current_machine
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (input : ShaInput) (answer : Digest256)
    (beforeFold : state.exposureIndex ≠ foldExposureIndex)
    (inputExact : unifiedMachineFreshInputBefore? transitionFuel state.cursor =
      some input) :
    (input, answer) ∈
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterMemory state answer).2.1.seenMachine := by
  simp only [foldArmedCompleteController, beforeFold, if_false,
    alphaFinalWorkQ16DagController, foldArmedAlphaZeroController,
    foldArmedAlphaAfterMemory, alphaIndexedState, foldArmedUnderlyingState]
  have causalInput := unified_machine_fresh_input_is_unified_input
    transitionFuel state.cursor input inputExact
  rw [causalInput]
  unfold rememberCurrentMachine
  rw [inputExact]
  simp

/-- Once the selected fold exposure has passed, later controller steps retain
the armed boundary input exactly. -/
theorem fold_armed_complete_after_fold_preserves_expected_boundary
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (answer : Digest256)
    (afterFold : foldExposureIndex < state.exposureIndex) :
    ((foldArmedCompleteController transitionFuel foldExposureIndex
      finalWorkAnchorIndex).afterMemory state answer).2.1.expectedBoundary =
      state.memory.2.1.expectedBoundary := by
  have indexNe : state.exposureIndex ≠ foldExposureIndex := by omega
  simp only [foldArmedCompleteController, indexNe, if_false,
    alpha_final_work_q16_after_memory]
  change (foldArmedAlphaAfterMemory transitionFuel
    (foldArmedAlphaState state) answer).expectedBoundary = _
  unfold foldArmedAlphaAfterMemory
  split <;> rfl

/-- At the later exact boundary exposure, an armed post-fold controller
installs the returned digest as alpha block zero. -/
theorem fold_armed_complete_after_fold_boundary_installs_block_zero
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (input : ShaInput) (answer : Digest256)
    (afterFold : foldExposureIndex < state.exposureIndex)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (armed : state.memory.2.1.expectedBoundary = some input) :
    ((foldArmedCompleteController transitionFuel foldExposureIndex
      finalWorkAnchorIndex).afterMemory state answer).2.1.alpha.producers =
      [⟨answer, 0, input⟩] := by
  have indexNe : state.exposureIndex ≠ foldExposureIndex := by omega
  simp only [foldArmedCompleteController, indexNe, if_false,
    alpha_final_work_q16_after_memory]
  apply fold_armed_alpha_exact_boundary_installs_block_zero transitionFuel
    (foldArmedAlphaState state) input answer
  · simpa [foldArmedAlphaState, foldArmedUnderlyingState,
      alphaIndexedState] using inputExact
  · exact armed

/-- Processing the selected literal fold-work record installs the exact
fold-nonce absorption input into the alpha memory. -/
theorem fold_armed_complete_literal_fold_step_arms_boundary
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (digest answer : Digest256) (nonce : NonceBytes)
    (atFold : state.exposureIndex = foldExposureIndex)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some (bytes digest ++ [domGrind] ++ bytes nonce)) :
    ((foldArmedCompleteController transitionFuel foldExposureIndex
      finalWorkAnchorIndex).afterMemory state answer).2.1.expectedBoundary =
        some (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes nonce) := by
  have projectedInputExact :
      unifiedInputBeforeAnswer? transitionFuel
          (foldArmedAlphaState state).cursor =
        some (bytes digest ++ [domGrind] ++ bytes nonce) := by
    simpa [foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]
      using inputExact
  have armedExact :
      armFoldAlphaBoundary transitionFuel (foldArmedAlphaState state) =
        some (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes nonce) := by
    simp only [armFoldAlphaBoundary, projectedInputExact, Option.bind_some]
    exact literal_fold_work_arms_exact_alpha_boundary digest nonce
  simp only [foldArmedCompleteController, atFold, if_pos]
  exact arm_fold_alpha_memory_expected_boundary transitionFuel
    (foldArmedAlphaState state) _ answer armedExact

/-- If the literal fold boundary was already exposed, processing the selected
fold-work answer installs that retained boundary answer as alpha block zero. -/
theorem fold_armed_complete_literal_fold_step_cached_contains_block_zero
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedCompleteMemory)
    (digest answer boundaryAnswer : Digest256) (nonce : NonceBytes)
    (atFold : state.exposureIndex = foldExposureIndex)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some (bytes digest ++ [domGrind] ++ bytes nonce))
    (cached : seenMachineAnswer? (foldArmedAlphaState state).memory
        (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++ bytes nonce) =
      some boundaryAnswer) :
    ({ digest := boundaryAnswer, block := 0,
        sourceInput := bytes digest ++
          [domAbsorb, foldWorkNonceLabel, 0] ++ bytes nonce } :
      AlphaZeroProducer) ∈
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalWorkAnchorIndex).afterMemory state answer).2.1.alpha.producers := by
  have projectedInputExact :
      unifiedInputBeforeAnswer? transitionFuel
          (foldArmedAlphaState state).cursor =
        some (bytes digest ++ [domGrind] ++ bytes nonce) := by
    simpa [foldArmedAlphaState, foldArmedUnderlyingState, alphaIndexedState]
      using inputExact
  have armedExact :
      armFoldAlphaBoundary transitionFuel (foldArmedAlphaState state) =
        some (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes nonce) := by
    simp only [armFoldAlphaBoundary, projectedInputExact, Option.bind_some]
    exact literal_fold_work_arms_exact_alpha_boundary digest nonce
  simp only [foldArmedCompleteController, atFold, if_pos]
  exact arm_fold_alpha_memory_cached_contains_block_zero transitionFuel
    (foldArmedAlphaState state) _ answer boundaryAnswer armedExact cached

/-- Compile the fold-armed controller into the same 518-coordinate shape used
by the K1.3 probability theorem. -/
def foldArmedInitialState
    {globalOracleCalls : Nat}
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    IndexedUnifiedExposureState globalOracleCalls FoldArmedCompleteMemory :=
  { exposureIndex := 0
    cursor := cursor
    memory := (false,
      (inactiveFoldArmedAlphaZeroMemory, inactiveDagMemory)) }

def exactCompilerFoldArmedAlphaFinalWorkQ16Router
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters :=
  ((foldArmedCompleteController transitionFuel foldExposureIndex
    finalWorkAnchorIndex).machine transitionFuel).fullRouter
      ((exactCompilerTargetCaps parameters).length - 518)
      (foldArmedInitialState cursor)

#print axioms literal_fold_work_arms_exact_alpha_boundary
#print axioms fold_armed_alpha_preferred
#print axioms fold_armed_alpha_exact_boundary_installs_block_zero
#print axioms fold_armed_alpha_nonboundary_uses_advance_update
#print axioms fold_armed_alpha_after_memory_used_slots
#print axioms arm_fold_alpha_memory_used_slots
#print axioms fold_armed_complete_preferred_at_fold
#print axioms fold_armed_complete_literal_fold_step_arms_boundary
#print axioms exactCompilerFoldArmedAlphaFinalWorkQ16Router

end

end AspisK1.V7Tag73FoldArmedAlphaZeroController
