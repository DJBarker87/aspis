import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability

/-!
# Exact 518-slot compiler coordinates

This module extends the established 517-slot alpha/final-work/q16 factor by
one separately positioned fold-work digest.  It is a coordinate equivalence
only: no protocol transcript, security parameter, or verifier behavior is
changed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
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

/-- The fold-work answer precedes the complete 517-slot factor. -/
abbrev FoldAlphaFinalWorkQ16DigestSlot :=
  Option AlphaFinalWorkQ16DigestSlot

theorem fold_alpha_final_work_q16_digest_slot_card :
    Fintype.card FoldAlphaFinalWorkQ16DigestSlot = 518 := by
  simp [FoldAlphaFinalWorkQ16DigestSlot]

def foldAlphaFinalWorkQ16DigestSlotFunctionEquiv :
    (FoldAlphaFinalWorkQ16DigestSlot → Digest256) ≃
      Digest256 ×
        (AlphaZeroDigestBlocks ×
          (Digest256 × Q16CandidateDigestForest)) where
  toFun values :=
    (values none,
      alphaFinalWorkQ16DigestSlotFunctionEquiv
        (fun slot => values (some slot)))
  invFun coordinates
    | none => coordinates.1
    | some slot => alphaFinalWorkQ16DigestSlotFunctionEquiv.symm
        coordinates.2 slot
  left_inv values := by
    funext slot
    cases slot with
    | none => rfl
    | some inner =>
        exact congrFun
          (alphaFinalWorkQ16DigestSlotFunctionEquiv.symm_apply_apply
            (fun slot => values (some slot))) inner
  right_inv coordinates := by
    apply Prod.ext
    · rfl
    · exact alphaFinalWorkQ16DigestSlotFunctionEquiv.apply_symm_apply
        coordinates.2

abbrev ExactCompilerFoldAlphaFinalWorkQ16Residual
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256
    ((exactCompilerTargetCaps parameters).length - 518)

abbrev ExactCompilerCausalFoldAlphaFinalWorkQ16Router
    (parameters : ExactCompilerResourceParameters) :=
  CausalSlotRouter Digest256 FoldAlphaFinalWorkQ16DigestSlot Finset.univ
    ((exactCompilerTargetCaps parameters).length - 518)

theorem exact_compiler_tape_has_fold_alpha_final_work_q16_capacity
    (parameters : ExactCompilerResourceParameters) :
    518 ≤ (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap
    sameTapeStartCap deployedFull256VerifierCallCap
  omega

/-- Reassociate named coordinates so alpha remains conditioning data while
the two positioned work answers and q16 form the probability-bearing factor. -/
def foldAlphaFinalWorkQ16CoordinateRegroup
    (Residual : Type) :
    (Digest256 ×
        (AlphaZeroDigestBlocks ×
          (Digest256 × Q16CandidateDigestForest))) × Residual ≃
      (Residual × AlphaZeroDigestBlocks) ×
        (Digest256 × (Digest256 × Q16CandidateDigestForest)) where
  toFun coordinates :=
    ((coordinates.2, coordinates.1.2.1),
      (coordinates.1.1, coordinates.1.2.2))
  invFun coordinates :=
    ((coordinates.2.1, (coordinates.1.2, coordinates.2.2)),
      coordinates.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal compiler answer tape is exactly residual/alpha context times
fold work, final work, and the q16 forest. -/
def exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      (ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
        AlphaZeroDigestBlocks) ×
        (Digest256 × (Digest256 × Q16CandidateDigestForest)) := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 518 ≤ total :=
    exact_compiler_tape_has_fold_alpha_final_work_q16_capacity parameters
  have totalEq : total = 518 + (total - 518) := by omega
  have slotCard : Fintype.card FoldAlphaFinalWorkQ16DigestSlot = 518 :=
    fold_alpha_final_work_q16_digest_slot_card
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      ((castFreshAnswerTape
          (congrArg (fun count => count + (total - 518)) slotCard).symm
        ).trans
        (router.fullCoordinateEquiv.trans
          ((Equiv.prodCongr foldAlphaFinalWorkQ16DigestSlotFunctionEquiv
            (Equiv.refl (FreshAnswerTape Digest256 (total - 518)))).trans
              (foldAlphaFinalWorkQ16CoordinateRegroup
                (FreshAnswerTape Digest256 (total - 518))))))

/-- Hidden-tape averaging for any exact 518-slot causal router. -/
theorem exact_compiler_causal_fold_alpha_final_work_answer_q16_event_probability_le
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape →
      ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (bad : HiddenTape →
      ExactCompilerFoldAlphaFinalWorkQ16Residual parameters →
        AlphaZeroDigestBlocks → Digest256 → Digest256 →
          Finset (Fin 262144))
    (badCard : ∀ hidden residual alpha fold work,
      (bad hidden residual alpha fold work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
          (router hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent foldFinalWorkQ16TotalSucceeds
          (fun context => successfulFoldFinalWorkQ16TotalEquiv ⁻¹'
            foldFinalWorkQ16SuccessfulBadEvent
              (fun fold work =>
                bad hidden context.1 context.2 fold work))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((Nat.choose 9557 16 : ENNReal) /
            (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
              ENNReal))) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact
    uniform_tape_dependent_fold_alpha_final_work_answer_q16_probability_le
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (router hidden))
      (fun context fold work => bad hidden context.1 context.2 fold work)
      (fun context fold work => badCard hidden context.1 context.2 fold work)
      reference traceExists (jointEventSlice event hidden) (covered hidden)

end


#print axioms fold_alpha_final_work_q16_digest_slot_card
#print axioms foldAlphaFinalWorkQ16DigestSlotFunctionEquiv
#print axioms exact_compiler_tape_has_fold_alpha_final_work_q16_capacity
#print axioms foldAlphaFinalWorkQ16CoordinateRegroup
#print axioms exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates
#print axioms
  exact_compiler_causal_fold_alpha_final_work_answer_q16_event_probability_le

end AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
