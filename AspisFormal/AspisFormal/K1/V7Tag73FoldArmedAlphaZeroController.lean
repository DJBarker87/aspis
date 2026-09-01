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
  alpha : AlphaZeroControllerMemory
  deriving DecidableEq

def inactiveFoldArmedAlphaZeroMemory : FoldArmedAlphaZeroMemory :=
  { expectedBoundary := none
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

/-- Arm the exact future boundary, installing block zero immediately when an
adversary-first query has already populated that coordinate.  Otherwise the
ordinary future-boundary branch remains armed. -/
def armFoldAlphaMemory
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory) : FoldArmedAlphaZeroMemory :=
  match armFoldAlphaBoundary transitionFuel state with
  | none => state.memory
  | some target =>
      match unifiedCachedAnswerBefore? transitionFuel state.cursor target with
      | none => { state.memory with expectedBoundary := some target }
      | some answer =>
          { expectedBoundary := some target
            alpha :=
              { producers :=
                  [{ digest := answer, block := 0, sourceInput := target }]
                usedSlots := state.memory.alpha.usedSlots } }

theorem arm_fold_alpha_memory_expected_boundary
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (target : ShaInput)
    (armed : armFoldAlphaBoundary transitionFuel state = some target) :
    (armFoldAlphaMemory transitionFuel state).expectedBoundary = some target := by
  simp only [armFoldAlphaMemory, armed]
  split <;> rfl

theorem arm_fold_alpha_memory_cached_installs_block_zero
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (target : ShaInput) (answer : Digest256)
    (armed : armFoldAlphaBoundary transitionFuel state = some target)
    (cached : unifiedCachedAnswerBefore? transitionFuel state.cursor target =
      some answer) :
    (armFoldAlphaMemory transitionFuel state).alpha.producers =
      [{ digest := answer, block := 0, sourceInput := target }] := by
  simp [armFoldAlphaMemory, armed, cached]

theorem arm_fold_alpha_memory_uncached_retains_inventory
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (target : ShaInput)
    (armed : armFoldAlphaBoundary transitionFuel state = some target)
    (uncached : unifiedCachedAnswerBefore? transitionFuel state.cursor target =
      none) :
    (armFoldAlphaMemory transitionFuel state).alpha = state.memory.alpha := by
  simp [armFoldAlphaMemory, armed, uncached]

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
        alpha := nextAlpha }

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
        armFoldAlphaMemory transitionFuel (foldArmedAlphaState state)
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
    (foldArmedAlphaState state) _ armedExact

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
#print axioms fold_armed_complete_preferred_at_fold
#print axioms fold_armed_complete_literal_fold_step_arms_boundary
#print axioms exactCompilerFoldArmedAlphaFinalWorkQ16Router

end

end AspisK1.V7Tag73FoldArmedAlphaZeroController
