import AspisFormal.K1.V7Tag73AdaptiveQ16TrialAccounting
import AspisFormal.K1.V7Tag73CausalQ16FinalWorkDependentBad
import AspisFormal.K1.V7Tag73HiddenTapeAveraging
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
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkDependentBad
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
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

/-- Hidden-tape averaging for the corrected 517-slot compiler factor.  The
four alpha-zero blocks are explicit conditioning data; only final work and
the q16 forest contribute probability factors. -/
theorem exact_compiler_causal_alpha_final_work_answer_q16_event_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape →
      ExactCompilerCausalAlphaFinalWorkQ16Router parameters)
    (bad : HiddenTape →
      FreshAnswerTape Digest256
          ((exactCompilerTargetCaps parameters).length - 517) →
        AlphaZeroDigestBlocks → Digest256 → Finset (Fin 262144))
    (badCard : ∀ hidden residual alpha work,
      (bad hidden residual alpha work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalAlphaFinalWorkQ16Coordinates parameters
          (router hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
          (fun context => successfulFinalWorkQ16TotalEquiv ⁻¹'
            finalWorkQ16SuccessfulDependentBadEvent
              (fun work => bad hidden context.1 context.2 work))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
            ENNReal)) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_alpha_final_work_answer_q16_probability_le
    (exactCompilerCausalAlphaFinalWorkQ16Coordinates parameters
      (router hidden))
    (bad hidden) (badCard hidden) reference traceExists
    (jointEventSlice event hidden) (covered hidden)

/-! ## Corrected exposure-trial package -/

/-- A finite family of exact 517-slot factors.  This is the probability-ready
replacement for the old 513-slot package; the source layer supplies a router
that is fixed by the trial and hidden tape before the uniform answer tape is
sampled. -/
structure ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    (parameters : ExactCompilerResourceParameters) where
  event : Trial → Set (ExactCompilerSample HiddenTape parameters)
  router : Trial → HiddenTape →
    ExactCompilerCausalAlphaFinalWorkQ16Router parameters
  bad : Trial → HiddenTape →
    FreshAnswerTape Digest256
        ((exactCompilerTargetCaps parameters).length - 517) →
      AlphaZeroDigestBlocks → Digest256 → Finset (Fin 262144)
  badCard : ∀ trial hidden residual alpha work,
    (bad trial hidden residual alpha work).card ≤ 9557
  reference : AdmittedResult SemanticCap203Admitted
  traceExists : Nonempty
    (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
      reference.1)
  covered : ∀ trial hidden, jointEventSlice (event trial) hidden ⊆
    exactCompilerCausalAlphaFinalWorkQ16Coordinates parameters
        (router trial hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun context => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulDependentBadEvent
            (fun work => bad trial hidden context.1 context.2 work))

theorem ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials.event_probability_le_product
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trial : Trial) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      q16SemanticOneForestRawError / (2 : ENNReal) ^ 34 := by
  have bound :=
    exact_compiler_causal_alpha_final_work_answer_q16_event_probability_le
      hiddenLaw parameters (trials.router trial) (trials.bad trial)
      (trials.badCard trial) trials.reference trials.traceExists
      (trials.event trial) (trials.covered trial)
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (trials.event trial) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        q16SemanticOneForestRawError at bound
  calc
    _ ≤ ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          q16SemanticOneForestRawError := bound
    _ = q16SemanticOneForestRawError / (2 : ENNReal) ^ 34 := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      simp

theorem ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials.failure_union_probability_le_one_forest
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (trialCap : Fintype.card Trial ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) ≤ q16SemanticOneForestRawError := by
  exact work_qualified_q16_trial_union_probability_le_one_forest
    (exactCompilerJointLaw hiddenLaw parameters) trials.event
    trials.event_probability_le_product trialCap

#print axioms alpha_final_work_q16_digest_slot_card
#print axioms alphaFinalWorkQ16DigestSlotFunctionEquiv
#print axioms exact_compiler_tape_has_alpha_final_work_q16_capacity
#print axioms alphaFinalWorkQ16CoordinateRegroup
#print axioms exactCompilerCausalAlphaFinalWorkQ16Coordinates
#print axioms
  uniform_tape_dependent_alpha_final_work_answer_q16_probability_le
#print axioms
  exact_compiler_causal_alpha_final_work_answer_q16_event_probability_le
#print axioms ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials
#print axioms
  ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials.event_probability_le_product
#print axioms
  ExactCompilerCausalAlphaFinalWorkAnswerQ16Trials.failure_union_probability_le_one_forest

end

end AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
