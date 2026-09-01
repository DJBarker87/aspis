import AspisFormal.K1.V7Tag73CausalQ16CoordinateRouter
import AspisFormal.K1.V7Tag73ExactCompilerResources
import AspisFormal.K1.V7Tag73IndexedExposureCausalRouter
import AspisFormal.K1.V7Tag73VariablePrefixGammaSampler

/-!
# Causal coordinates for the Tag-73 gamma duplex prefix

The deployed nonzero gamma sampler can inspect at most twelve SHA-256 output
blocks and their twelve paired transcript-advance answers. This file gives
those 24 adaptively selected answers named slots in the exact compiler tape.
It is purely a lossless coordinate equivalence; the production scheduler
controller and its realization proof are supplied separately.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalGammaPrefixCoordinates

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

universe u

/-- Twelve chronological block positions, with `false` naming the squeeze
output and `true` naming its paired transcript advance. -/
abbrev GammaPrefixDigestSlot := Fin 12 × Bool

theorem gamma_prefix_digest_slot_card :
    Fintype.card GammaPrefixDigestSlot = 24 := by
  simp [GammaPrefixDigestSlot]

/-- Repackage the 24 named digest slots as the exact duplex tape consumed by
the variable-prefix sampler. -/
def gammaPrefixDigestSlotFunctionEquiv :
    (GammaPrefixDigestSlot → Digest256) ≃ TotalGammaDuplexTape where
  toFun values :=
    (fun index ↦ values (index, false),
      fun index ↦ values (index, true))
  invFun tape
    | (index, false) => tape.1 index
    | (index, true) => tape.2 index
  left_inv values := by
    funext slot
    rcases slot with ⟨index, side⟩
    cases side <;> rfl
  right_inv tape := by
    apply Prod.ext <;> funext index <;> rfl

abbrev ExactCompilerGammaPrefixResidual
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256
    ((exactCompilerTargetCaps parameters).length - 24)

/-- A complete causal router names all 24 gamma-duplex slots once and retains
every other compiler answer in an exact residual tape. -/
abbrev ExactCompilerCausalGammaPrefixRouter
    (parameters : ExactCompilerResourceParameters) :=
  CausalSlotRouter Digest256 GammaPrefixDigestSlot Finset.univ
    ((exactCompilerTargetCaps parameters).length - 24)

theorem exact_compiler_tape_has_gamma_prefix_capacity
    (parameters : ExactCompilerResourceParameters) :
    24 ≤ (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap
    sameTapeStartCap deployedFull256VerifierCallCap
  omega

/-- The compiler tape factors exactly into all non-gamma answers and the
chronological twelve-output/twelve-advance gamma tape. -/
def exactCompilerCausalGammaPrefixCoordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalGammaPrefixRouter parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 24 ≤ total :=
    exact_compiler_tape_has_gamma_prefix_capacity parameters
  have totalEq : total = 24 + (total - 24) := by omega
  have slotCard : Fintype.card GammaPrefixDigestSlot = 24 :=
    gamma_prefix_digest_slot_card
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      ((castFreshAnswerTape
          (congrArg (fun count ↦ count + (total - 24)) slotCard).symm).trans
        (router.fullCoordinateEquiv.trans
          ((Equiv.prodCongr gammaPrefixDigestSlotFunctionEquiv
            (Equiv.refl (FreshAnswerTape Digest256 (total - 24)))).trans
              (Equiv.prodComm TotalGammaDuplexTape
                (FreshAnswerTape Digest256 (total - 24))))))

/-- Compile any source controller whose pre-answer decisions label the 24
gamma slots into the exact causal router. Unused slots are filled only by the
router's total padding path. -/
def exactCompilerIndexedGammaPrefixRouter
    {Memory : Type u}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 GammaPrefixDigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalGammaPrefixRouter parameters :=
  (controller.machine transitionFuel).fullRouter
    ((exactCompilerTargetCaps parameters).length - 24)
    { exposureIndex := 0, cursor := cursor, memory := initialMemory }

/-- Coordinate equivalence induced by a concrete pre-answer gamma-labeling
controller on the production unified scheduler. -/
def exactCompilerIndexedGammaPrefixCoordinates
    {Memory : Type u}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters)
      Digest256 GammaPrefixDigestSlot Memory)
    (initialMemory : Memory)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerCausalGammaPrefixCoordinates parameters
    (exactCompilerIndexedGammaPrefixRouter parameters transitionFuel
      controller initialMemory cursor)

#print axioms gamma_prefix_digest_slot_card
#print axioms gammaPrefixDigestSlotFunctionEquiv
#print axioms exact_compiler_tape_has_gamma_prefix_capacity
#print axioms exactCompilerCausalGammaPrefixCoordinates
#print axioms exactCompilerIndexedGammaPrefixRouter
#print axioms exactCompilerIndexedGammaPrefixCoordinates

end

end AspisK1.V7Tag73CausalGammaPrefixCoordinates
