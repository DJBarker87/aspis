import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16ControllerComposition
import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
import AspisFormal.K1.V7Tag73ExactCompilerFoldWorkTraceOccurrence
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords
import AspisFormal.K1.V7Tag73IndexedControllerTraceAlignment

/-!
# Fold-work plus alpha/final-work/q16 controller composition

One exposure-indexed slot records the literal fold-work answer.  The existing
517-slot causal controller remains unchanged underneath it.  Both choose from
the same pre-answer scheduler state, so the resulting 518-slot router is a
genuine causal coordinate equivalence.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev FoldAlphaFinalWorkQ16ControllerMemory (Memory : Type) :=
  Bool × Memory

def foldTrialUsed
    {globalOracleCalls : Nat} {Memory : Type}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory Memory)) : Bool :=
  state.memory.1

def underlyingIndexedState
    {globalOracleCalls : Nat} {Memory : Type}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory Memory)) :
    IndexedUnifiedExposureState globalOracleCalls Memory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.2 }

/-- Fold receives its one named slot exactly at the precommitted first-exposure
index.  Otherwise the established 517-slot controller decides normally. -/
def foldAlphaFinalWorkQ16Controller
    {globalOracleCalls : Nat} {Memory : Type}
    (foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16DigestSlot
      (FoldAlphaFinalWorkQ16ControllerMemory Memory) where
  preferredSlot := fun state =>
    if state.memory.1 = false ∧ state.exposureIndex = foldExposureIndex then
      some none
    else
      (underlying.preferredSlot (underlyingIndexedState state)).map some
  afterMemory := fun state answer =>
    (state.memory.1 || decide (state.exposureIndex = foldExposureIndex),
      underlying.afterMemory (underlyingIndexedState state) answer)

@[simp] theorem fold_controller_preferred_at_fresh_index
    {globalOracleCalls : Nat} {Memory : Type}
    (foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory Memory))
    (unused : state.memory.1 = false)
    (atIndex : state.exposureIndex = foldExposureIndex) :
    (foldAlphaFinalWorkQ16Controller foldExposureIndex underlying).preferredSlot
        state = some none := by
  simp [foldAlphaFinalWorkQ16Controller, unused, atIndex]

@[simp] theorem fold_controller_preferred_of_underlying
    {globalOracleCalls : Nat} {Memory : Type}
    (foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory Memory))
    (slot : AlphaFinalWorkQ16DigestSlot)
    (notFold : ¬(state.memory.1 = false ∧
      state.exposureIndex = foldExposureIndex))
    (preferred : underlying.preferredSlot (underlyingIndexedState state) =
      some slot) :
    (foldAlphaFinalWorkQ16Controller foldExposureIndex underlying).preferredSlot
        state = some (some slot) := by
  simp [foldAlphaFinalWorkQ16Controller, notFold, preferred]

@[simp] theorem fold_controller_after_memory
    {globalOracleCalls : Nat} {Memory : Type}
    (foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (FoldAlphaFinalWorkQ16ControllerMemory Memory))
    (answer : Digest256) :
    (foldAlphaFinalWorkQ16Controller foldExposureIndex underlying).afterMemory
        state answer =
      (state.memory.1 || decide (state.exposureIndex = foldExposureIndex),
        underlying.afterMemory (underlyingIndexedState state) answer) := by
  rfl

/-- Before the selected index is processed, the fold slot remains unused. -/
theorem fold_controller_unused_before_index
    {globalOracleCalls : Nat} {Memory : Type}
    (transitionFuel foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController globalOracleCalls
      Digest256 AlphaFinalWorkQ16DigestSlot Memory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (FoldAlphaFinalWorkQ16ControllerMemory Memory)),
      state.memory.1 = false →
      state.exposureIndex + records.length ≤ foldExposureIndex →
      (indexedStateAfterRecords transitionFuel
        (foldAlphaFinalWorkQ16Controller foldExposureIndex underlying)
        records state).memory.1 = false := by
  intro records
  induction records with
  | nil =>
      intro state unused _
      simpa using unused
  | cons record rest ih =>
      intro state unused before
      simp only [List.length_cons] at before
      have indexNe : state.exposureIndex ≠ foldExposureIndex := by omega
      let next :=
        (foldAlphaFinalWorkQ16Controller foldExposureIndex underlying).afterAnswer
          transitionFuel state record.answer
      have nextUnused : next.memory.1 = false := by
        simp [next, IndexedUnifiedExposureController.afterAnswer,
          foldAlphaFinalWorkQ16Controller, unused, indexNe]
      have nextBefore : next.exposureIndex + rest.length ≤ foldExposureIndex := by
        have nextIndex : next.exposureIndex = state.exposureIndex + 1 := by
          simp [next, IndexedUnifiedExposureController.afterAnswer]
        rw [nextIndex]
        omega
      rw [indexed_state_after_records_cons]
      exact ih next nextUnused nextBefore

/-- Compile the composed controller into the exact 518-slot router. -/
def exactCompilerFoldAlphaFinalWorkQ16Router
    {Memory : Type}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters :=
  ((foldAlphaFinalWorkQ16Controller foldExposureIndex underlying).machine
    transitionFuel).fullRouter
      ((exactCompilerTargetCaps parameters).length - 518)
      { exposureIndex := 0
        cursor := cursor
        memory := (false, initialMemory) }

/-- Probability-ready coordinates from the identical composed controller. -/
def exactCompilerFoldAlphaFinalWorkQ16Coordinates
    {Memory : Type}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel foldExposureIndex : Nat)
    (underlying : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 AlphaFinalWorkQ16DigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :=
  exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
    (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
      foldExposureIndex underlying initialMemory cursor)

end


#print axioms foldAlphaFinalWorkQ16Controller
#print axioms fold_controller_preferred_at_fresh_index
#print axioms fold_controller_preferred_of_underlying
#print axioms fold_controller_after_memory
#print axioms fold_controller_unused_before_index
#print axioms exactCompilerFoldAlphaFinalWorkQ16Router
#print axioms exactCompilerFoldAlphaFinalWorkQ16Coordinates

end AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
