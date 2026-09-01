import AspisFormal.K1.V7Tag73CausalQ16FinalWorkDependentBad
import AspisFormal.K1.V7Tag73IndexedExposureCausalRouter

/-!
# Joint causal alpha-zero, final-work, and q16 coordinates

The old 513-coordinate factor exposes final work and the 512 q16 digest
blocks, leaving every other answer in chronological residual order.  That is
insufficient for a pointwise source theorem when the adversary may decide
when to query the already-determined alpha-zero input after observing named
q16 answers: the alpha answer remains independent, but its residual index may
move.

This module states the correct finite factorization.  Four additional causal
slots hold the complete deployed alpha-zero sampler cap.  The remaining
context may therefore contain arbitrary adaptive transcript history while the
q16 forest stays an independent uniform factor conditional on the exact alpha
blocks and final-work answer.  No security parameter or protocol transcript
is changed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkDependentBad
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Four ordinary-QM31 output blocks followed by the existing final-work/q16
slots. -/
abbrev AlphaFinalWorkQ16DigestSlot :=
  Fin 4 ⊕ FinalWorkQ16DigestSlot

/-- The four raw alpha-zero output blocks are kept explicit.  The decoder may
use any nonempty prefix allowed by the deployed four-block cap. -/
abbrev AlphaZeroDigestBlocks := Fin 4 → Digest256

theorem alpha_final_work_q16_digest_slot_card :
    Fintype.card AlphaFinalWorkQ16DigestSlot = 517 := by
  simp [AlphaFinalWorkQ16DigestSlot]

/-- Split a complete named-slot function into alpha blocks and the existing
work/q16 product. -/
def alphaFinalWorkQ16DigestSlotFunctionEquiv :
    (AlphaFinalWorkQ16DigestSlot → Digest256) ≃
      AlphaZeroDigestBlocks × (Digest256 × Q16CandidateDigestForest) :=
  (Equiv.sumArrowEquivProdArrow (Fin 4) FinalWorkQ16DigestSlot
      Digest256).trans
    (Equiv.prodCongr (Equiv.refl AlphaZeroDigestBlocks)
      finalWorkQ16DigestSlotFunctionEquiv)

/-- Residual answers together with the complete alpha-zero block vector form
the context on which the work-dependent q16 bad family may depend. -/
abbrev ExactCompilerAlphaFinalWorkQ16Context
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256
      ((exactCompilerTargetCaps parameters).length - 517) ×
    AlphaZeroDigestBlocks

abbrev ExactCompilerCausalAlphaFinalWorkQ16Router
    (parameters : ExactCompilerResourceParameters) :=
  CausalSlotRouter Digest256 AlphaFinalWorkQ16DigestSlot Finset.univ
    ((exactCompilerTargetCaps parameters).length - 517)

theorem exact_compiler_tape_has_alpha_final_work_q16_capacity
    (parameters : ExactCompilerResourceParameters) :
    517 ≤ (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap
    sameTapeStartCap deployedFull256VerifierCallCap
  omega

/-- Pure reassociation used after the causal router exposes its named-slot
function. -/
def alphaFinalWorkQ16CoordinateRegroup
    (Residual : Type) :
    (AlphaZeroDigestBlocks × (Digest256 × Q16CandidateDigestForest)) ×
        Residual ≃
      (Residual × AlphaZeroDigestBlocks) ×
        (Digest256 × Q16CandidateDigestForest) where
  toFun coordinates :=
    ((coordinates.2, coordinates.1.1), coordinates.1.2)
  invFun coordinates :=
    ((coordinates.1.2, coordinates.2), coordinates.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The 517-slot causal router is an exact coordinate equivalence.  In the
result, alpha belongs to the conditioning context while final work and q16
retain the same product shape used by the checked probability theorem. -/
def exactCompilerCausalAlphaFinalWorkQ16Coordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalAlphaFinalWorkQ16Router parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerAlphaFinalWorkQ16Context parameters ×
        (Digest256 × Q16CandidateDigestForest) := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 517 ≤ total :=
    exact_compiler_tape_has_alpha_final_work_q16_capacity parameters
  have totalEq : total = 517 + (total - 517) := by omega
  have slotCard : Fintype.card AlphaFinalWorkQ16DigestSlot = 517 :=
    alpha_final_work_q16_digest_slot_card
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      ((castFreshAnswerTape
          (congrArg (fun count => count + (total - 517)) slotCard).symm
        ).trans
        (router.fullCoordinateEquiv.trans
          ((Equiv.prodCongr alphaFinalWorkQ16DigestSlotFunctionEquiv
            (Equiv.refl (FreshAnswerTape Digest256 (total - 517)))).trans
              (alphaFinalWorkQ16CoordinateRegroup
                (FreshAnswerTape Digest256 (total - 517))))))

/-- Conditioning the q16 consistency set on all four raw alpha-zero blocks
costs no extra probability factor.  It is simply part of the residual
context in the existing exact product theorem. -/
theorem uniform_tape_dependent_alpha_final_work_answer_q16_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Equiv Tape
      ((Residual × AlphaZeroDigestBlocks) ×
        (Digest256 × Q16CandidateDigestForest)))
    (bad : Residual → AlphaZeroDigestBlocks → Digest256 →
      Finset (Fin 262144))
    (badCard : ∀ residual alpha work,
      (bad residual alpha work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun context => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulDependentBadEvent
            (fun work => bad context.1 context.2 work))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
            ENNReal)) := by
  exact uniform_tape_dependent_final_work_answer_q16_probability_le
    coordinates (fun context work => bad context.1 context.2 work)
      (fun context work => badCard context.1 context.2 work)
      reference traceExists event covered

#print axioms alpha_final_work_q16_digest_slot_card
#print axioms alphaFinalWorkQ16DigestSlotFunctionEquiv
#print axioms exact_compiler_tape_has_alpha_final_work_q16_capacity
#print axioms alphaFinalWorkQ16CoordinateRegroup
#print axioms exactCompilerCausalAlphaFinalWorkQ16Coordinates
#print axioms
  uniform_tape_dependent_alpha_final_work_answer_q16_probability_le

end

end AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
