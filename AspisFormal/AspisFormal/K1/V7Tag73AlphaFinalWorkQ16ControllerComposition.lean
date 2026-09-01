import AspisFormal.K1.V7Tag73CausalDagFinalWorkQ16Controller
import AspisFormal.K1.V7Tag73IndexedAlphaFinalWorkQ16Router

/-!
# Composition of alpha-zero and final-work/q16 causal controllers

The production final-work/q16 controller already follows the exact unified
scheduler and handles adversary-first exposure through its causal producer
DAG.  The corrected K1.3 factor additionally needs four alpha-zero output
coordinates.  This module composes an arbitrary pre-answer alpha controller
with that existing controller and compiles the result into the exact 517-slot
coordinate system.

Alpha receives priority only if both controllers label the same pre-answer
state.  The accepted-source layer must prove that this cannot hide a required
work/q16 label; the existing alpha/q16 separation lemmas provide that fact on
the literal accepted path.  No disjointness premise is needed for the total
coordinate equivalence itself.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedAlphaFinalWorkQ16Router
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Product memory keeps the alpha controller independent of the already
verified causal-DAG state machine. -/
abbrev AlphaFinalWorkQ16ControllerMemory (AlphaMemory : Type) :=
  AlphaMemory × FinalWorkQ16DagMemory

def alphaIndexedState
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory)) :
    IndexedUnifiedExposureState globalOracleCalls AlphaMemory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.1 }

def finalWorkQ16IndexedState
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory)) :
    IndexedUnifiedExposureState globalOracleCalls FinalWorkQ16DagMemory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.2 }

/-- Combine a four-slot alpha controller with the deployed final-work/q16
controller.  Both labels are computed from the same pre-answer cursor. -/
def alphaFinalWorkQ16DagController
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      AlphaFinalWorkQ16DigestSlot
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory) where
  preferredSlot := fun state =>
    match alphaController.preferredSlot (alphaIndexedState state) with
    | some alphaSlot => some (Sum.inl alphaSlot)
    | none =>
        ((finalWorkQ16DagController globalOracleCalls transitionFuel
          anchorIndex).preferredSlot
            (finalWorkQ16IndexedState state)).map Sum.inr
  afterMemory := fun state answer =>
    (alphaController.afterMemory (alphaIndexedState state) answer,
      (finalWorkQ16DagController globalOracleCalls transitionFuel
        anchorIndex).afterMemory (finalWorkQ16IndexedState state) answer)

@[simp] theorem alpha_final_work_q16_preferred_of_alpha
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory))
    (slot : Fin 4)
    (preferred : alphaController.preferredSlot (alphaIndexedState state) =
      some slot) :
    (alphaFinalWorkQ16DagController transitionFuel anchorIndex
      alphaController).preferredSlot state = some (Sum.inl slot) := by
  simp [alphaFinalWorkQ16DagController, preferred]

@[simp] theorem alpha_final_work_q16_preferred_of_dag
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory))
    (slot : FinalWorkQ16DigestSlot)
    (alphaNone : alphaController.preferredSlot (alphaIndexedState state) = none)
    (dagPreferred :
      (finalWorkQ16DagController globalOracleCalls transitionFuel
        anchorIndex).preferredSlot (finalWorkQ16IndexedState state) =
          some slot) :
    (alphaFinalWorkQ16DagController transitionFuel anchorIndex
      alphaController).preferredSlot state = some (Sum.inr slot) := by
  simp [alphaFinalWorkQ16DagController, alphaNone, dagPreferred]

@[simp] theorem alpha_final_work_q16_after_memory
    {globalOracleCalls : Nat} {AlphaMemory : Type}
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 (Fin 4) AlphaMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (AlphaFinalWorkQ16ControllerMemory AlphaMemory))
    (answer : Digest256) :
    (alphaFinalWorkQ16DagController transitionFuel anchorIndex
      alphaController).afterMemory state answer =
      (alphaController.afterMemory (alphaIndexedState state) answer,
        (finalWorkQ16DagController globalOracleCalls transitionFuel
          anchorIndex).afterMemory (finalWorkQ16IndexedState state) answer) := by
  rfl

/-- Exact 517-slot router from the composed controller. -/
def exactCompilerAlphaFinalWorkQ16DagRouter
    {AlphaMemory : Type}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256 (Fin 4) AlphaMemory)
    (initialAlphaMemory : AlphaMemory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalAlphaFinalWorkQ16Router parameters :=
  exactCompilerIndexedAlphaFinalWorkQ16Router parameters transitionFuel
    (alphaFinalWorkQ16DagController transitionFuel anchorIndex alphaController)
    (initialAlphaMemory, inactiveDagMemory) cursor

/-- Exact probability-ready coordinates from the same composed controller. -/
def exactCompilerAlphaFinalWorkQ16DagCoordinates
    {AlphaMemory : Type}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel anchorIndex : Nat)
    (alphaController : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256 (Fin 4) AlphaMemory)
    (initialAlphaMemory : AlphaMemory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerAlphaFinalWorkQ16Context parameters ×
        (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerIndexedAlphaFinalWorkQ16Coordinates parameters transitionFuel
    (alphaFinalWorkQ16DagController transitionFuel anchorIndex alphaController)
    (initialAlphaMemory, inactiveDagMemory) cursor

#print axioms alphaFinalWorkQ16DagController
#print axioms alpha_final_work_q16_preferred_of_alpha
#print axioms alpha_final_work_q16_preferred_of_dag
#print axioms alpha_final_work_q16_after_memory
#print axioms exactCompilerAlphaFinalWorkQ16DagRouter
#print axioms exactCompilerAlphaFinalWorkQ16DagCoordinates

end

end AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
