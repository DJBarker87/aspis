import AspisFormal.K1.V7Tag73CausalQ16FinalWorkProbability
import AspisFormal.K1.V7Tag73SchedulerCausalQ16Router

/-!
# Counted pre-answer routing on the exact unified scheduler

The final-work/q16 trial cover must be anchored at an actual chronological
master-tape exposure.  A raw SHA input cannot be classified retrospectively
by the role it will acquire later, so this module adds an explicit exposure
ordinal and source-controlled finite memory to the existing unified cursor.

The controller sees the current cursor, ordinal, and memory before the current
answer.  Its memory transition receives that answer only after the slot choice
has been fixed.  The cursor transition is exactly
`unifiedCursorAfterAnswer`; no alternative scheduler or restore function is
introduced.

This is an operational constructor, not the Tag-73 source cover.  The next
layer must instantiate the controller with the literal final-work/nonce/q16
grammar and prove that every accepted failing execution is caught by one
exposure-indexed controller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73IndexedExposureCausalRouter

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- Exact unified cursor together with the number of full-256 master-tape
answers already consumed and finite source-controller memory. -/
structure IndexedUnifiedExposureState
    (globalOracleCalls : Nat) (Memory : Type u) where
  exposureIndex : Nat
  cursor : UnifiedExposureCursor.{u} globalOracleCalls
  memory : Memory

/-- A protocol-specific controller may inspect the complete pre-answer state
to choose a slot.  Its memory update may use the answer afterwards. -/
structure IndexedUnifiedExposureController
    (globalOracleCalls : Nat) (Output Slot : Type) (Memory : Type u) where
  preferredSlot :
    IndexedUnifiedExposureState globalOracleCalls Memory → Option Slot
  afterMemory :
    IndexedUnifiedExposureState globalOracleCalls Memory → Output → Memory

/-- Canonical one-answer transition: increment the literal exposure ordinal,
advance the production cursor exactly once, and then update controller memory.
-/
def IndexedUnifiedExposureController.afterAnswer
    {globalOracleCalls : Nat} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (answer : Digest256) :
    IndexedUnifiedExposureState globalOracleCalls Memory :=
  { exposureIndex := state.exposureIndex + 1
    cursor := unifiedCursorAfterAnswer transitionFuel state.cursor answer
    memory := controller.afterMemory state answer }

@[simp] theorem indexed_after_answer_exposure_index
    {globalOracleCalls : Nat} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (answer : Digest256) :
    (controller.afterAnswer transitionFuel state answer).exposureIndex =
      state.exposureIndex + 1 := by
  rfl

@[simp] theorem indexed_after_answer_cursor
    {globalOracleCalls : Nat} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory)
    (answer : Digest256) :
    (controller.afterAnswer transitionFuel state answer).cursor =
      unifiedCursorAfterAnswer transitionFuel state.cursor answer := by
  rfl

/-- The counted controller as the generic pre-answer machine used by the
measure-preserving causal router. -/
def IndexedUnifiedExposureController.machine
    {globalOracleCalls : Nat} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot Memory) :
    PreAnswerSlotMachine Digest256 FinalWorkQ16DigestSlot
      (IndexedUnifiedExposureState globalOracleCalls Memory) where
  preferredSlot := controller.preferredSlot
  afterAnswer := controller.afterAnswer transitionFuel

/-- Exact 513-slot final-work/q16 router compiled from one counted production
scheduler controller.  Unused named slots and early halts are handled by the
existing total padding equivalence. -/
def exactCompilerIndexedFinalWorkQ16Router
    {Memory : Type u}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 FinalWorkQ16DigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFinalWorkQ16Router parameters :=
  (controller.machine transitionFuel).fullRouter
    ((exactCompilerTargetCaps parameters).length - 513)
    { exposureIndex := 0, cursor := cursor, memory := initialMemory }

/-- The resulting router has exactly the adaptive coordinate equivalence used
by the joint final-work/q16 probability theorem. -/
def exactCompilerIndexedFinalWorkQ16Coordinates
    {Memory : Type u}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 FinalWorkQ16DigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerFinalWorkQ16Residual parameters ×
        (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerCausalFinalWorkQ16Coordinates parameters
    (exactCompilerIndexedFinalWorkQ16Router parameters transitionFuel
      controller initialMemory cursor)

/-- A controller slot choice is definitionally made from the pre-answer
state.  This theorem is intentionally small: it is the rewrite used when the
source layer proves that an indexed exposure receives its literal digest. -/
theorem indexed_controller_preferred_slot_exact
    {globalOracleCalls : Nat} {Memory : Type u}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory) :
    (controller.machine transitionFuel).preferredSlot state =
      controller.preferredSlot state := by
  rfl

#print axioms IndexedUnifiedExposureController.afterAnswer
#print axioms indexed_after_answer_exposure_index
#print axioms indexed_after_answer_cursor
#print axioms IndexedUnifiedExposureController.machine
#print axioms exactCompilerIndexedFinalWorkQ16Router
#print axioms exactCompilerIndexedFinalWorkQ16Coordinates

end

end AspisK1.V7Tag73IndexedExposureCausalRouter
