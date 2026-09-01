import AspisFormal.K1.V7Tag73CausalQ16ProbabilityBridge
import AspisFormal.K1.V7Tag73FinalWorkDigestProbability

/-!
# Joint causal q16 and final-work accounting

The deployed final 34-bit work digest is exposed before the cloned q16 scan.
This module routes that digest and all 512 q16 digest blocks as 513 distinct
causal slots.  The resulting coordinate equivalence makes the work digest an
independent uniform factor of the complete q16 forest, even though the
chronological fresh-answer indices may depend on earlier answers.

Consequently one selectable q16 trial costs the product of the exact
`2^-34` final-work probability and the existing one-forest semantic q16
bound.  This is internal raw-event accounting, not a post-hoc division of a
reported soundness theorem by grinding work.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalQ16FinalWorkProbability

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16ProbabilityBridge
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16CompilerTapeCoordinates
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-! ## Exact finite product probability -/

def finalWorkQ16TotalSucceeds
    (coordinates : Digest256 × Q16CandidateDigestForest) : Prop :=
  q16DigestForestSucceeds coordinates.2

abbrev SuccessfulFinalWorkQ16Total :=
  {coordinates : Digest256 × Q16CandidateDigestForest //
    finalWorkQ16TotalSucceeds coordinates}

def successfulFinalWorkQ16TotalEquiv :
    SuccessfulFinalWorkQ16Total ≃ Digest256 × SuccessfulQ16Coordinates where
  toFun coordinates :=
    (coordinates.1.1,
      successfulQ16DigestForestEquiv
        ⟨coordinates.1.2, coordinates.2⟩)
  invFun coordinates :=
    let forest := successfulQ16DigestForestEquiv.symm coordinates.2
    ⟨(coordinates.1, forest.1), forest.2⟩
  left_inv coordinates := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        (successfulQ16DigestForestEquiv.symm_apply_apply
          ⟨coordinates.1.2, coordinates.2⟩)
  right_inv coordinates := by
    apply Prod.ext
    · rfl
    · exact successfulQ16DigestForestEquiv.apply_symm_apply coordinates.2

def finalWorkQ16SuccessfulBadEvent (bad : Finset (Fin 262144)) :
    Set (Digest256 × SuccessfulQ16Coordinates) :=
  {coordinates |
    FinalWork34Accepted coordinates.1 ∧
      coordinates.2 ∈ q16SuccessfulCoordinatesBadEvent bad}

def finalWorkQ16SuccessfulBadSubtypeEquiv
    (bad : Finset (Fin 262144)) :
    {coordinates : Digest256 × SuccessfulQ16Coordinates //
      coordinates ∈ finalWorkQ16SuccessfulBadEvent bad} ≃
      FinalWork34AcceptedDigest ×
        {coordinates : SuccessfulQ16Coordinates //
          coordinates ∈ q16SuccessfulCoordinatesBadEvent bad} where
  toFun coordinates :=
    (⟨coordinates.1.1, coordinates.2.1⟩,
      ⟨coordinates.1.2, coordinates.2.2⟩)
  invFun coordinates :=
    ⟨(coordinates.1.1, coordinates.2.1),
      ⟨coordinates.1.2, coordinates.2.2⟩⟩
  left_inv coordinates := by ext <;> rfl
  right_inv coordinates := by ext <;> rfl

theorem uniform_final_work_q16_bad_probability_eq_product
    [Nonempty SuccessfulQ16Coordinates]
    (bad : Finset (Fin 262144)) :
    (PMF.uniformOfFintype
      (Digest256 × SuccessfulQ16Coordinates)).toOuterMeasure
        (finalWorkQ16SuccessfulBadEvent bad) =
      (PMF.uniformOfFintype Digest256).toOuterMeasure
          finalWork34AcceptedEvent *
        (PMF.uniformOfFintype SuccessfulQ16Coordinates).toOuterMeasure
          (q16SuccessfulCoordinatesBadEvent bad) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_congr (finalWorkQ16SuccessfulBadSubtypeEquiv bad),
    Fintype.card_congr finalWork34AcceptedEventSubtypeEquiv,
    Fintype.card_prod, Fintype.card_prod]
  repeat' rw [Nat.cast_mul]
  exact ENNReal.mul_div_mul_comm
    (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (Or.inl (ENNReal.natCast_ne_top _))

theorem uniform_final_work_q16_bad_probability_le_semantic
    [Nonempty SuccessfulQ16Coordinates]
    (bad : Finset (Fin 262144))
    (badCard : bad.card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    (PMF.uniformOfFintype
      (Digest256 × SuccessfulQ16Coordinates)).toOuterMeasure
        (finalWorkQ16SuccessfulBadEvent bad) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
            ENNReal)) := by
  classical
  let sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64 := ⟨reference, Classical.choice traceExists⟩
  letI : Nonempty (FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64) := ⟨sample⟩
  rw [uniform_final_work_q16_bad_probability_eq_product,
    uniform_final_work_34_probability_exact]
  gcongr
  exact q16_successful_coordinates_bad_measure_le_semantic_choose bad badCard
    reference traceExists

/-! ## Conditioning an arbitrary causal tape factorisation -/

theorem uniform_tape_dependent_final_work_q16_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates :
      Tape ≃ Residual × (Digest256 × Q16CandidateDigestForest))
    (bad : Residual → Finset (Fin 262144))
    (badCard : ∀ residual, (bad residual).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulBadEvent (bad residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
            ENNReal)) := by
  classical
  let sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64 := ⟨reference, Classical.choice traceExists⟩
  letI : Nonempty (FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64) := ⟨sample⟩
  let successfulCoordinates : SuccessfulQ16Coordinates :=
    (Classical.choice inferInstance, sample)
  letI : Nonempty SuccessfulQ16Coordinates := ⟨successfulCoordinates⟩
  letI : Nonempty SuccessfulFinalWorkQ16Total :=
    ⟨successfulFinalWorkQ16TotalEquiv.symm
      (Classical.choice inferInstance, successfulCoordinates)⟩
  apply uniform_tape_dependent_successful_event_probability_le
    finalWorkQ16TotalSucceeds coordinates successfulFinalWorkQ16TotalEquiv
    (fun residual => finalWorkQ16SuccessfulBadEvent (bad residual))
    (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
      ((Nat.choose 9557 16 : ENNReal) /
        (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
          ENNReal)))
  · intro residual
    exact uniform_final_work_q16_bad_probability_le_semantic
      (bad residual) (badCard residual) reference traceExists
  · exact covered

/-! ## The 513-slot exact compiler router -/

abbrev FinalWorkQ16DigestSlot := Option Q16DigestSlot

def finalWorkQ16DigestSlotFunctionEquiv :
    (FinalWorkQ16DigestSlot → Digest256) ≃
      Digest256 × Q16CandidateDigestForest where
  toFun values := (values none, fun counter block => values (some (counter, block)))
  invFun coordinates
    | none => coordinates.1
    | some (counter, block) => coordinates.2 counter block
  left_inv values := by funext slot; cases slot <;> rfl
  right_inv coordinates := by ext <;> rfl

theorem finalWorkQ16DigestSlot_card :
    Fintype.card FinalWorkQ16DigestSlot = 513 := by
  simp [FinalWorkQ16DigestSlot, Q16DigestSlot]

abbrev ExactCompilerFinalWorkQ16Residual
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256
    ((exactCompilerTargetCaps parameters).length - 513)

abbrev ExactCompilerCausalFinalWorkQ16Router
    (parameters : ExactCompilerResourceParameters) :=
  CausalSlotRouter Digest256 FinalWorkQ16DigestSlot Finset.univ
    ((exactCompilerTargetCaps parameters).length - 513)

theorem exact_compiler_tape_has_final_work_q16_capacity
    (parameters : ExactCompilerResourceParameters) :
    513 ≤ (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap
    sameTapeStartCap deployedFull256VerifierCallCap
  omega

def exactCompilerCausalFinalWorkQ16Coordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFinalWorkQ16Router parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerFinalWorkQ16Residual parameters ×
        (Digest256 × Q16CandidateDigestForest) := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 513 ≤ total :=
    exact_compiler_tape_has_final_work_q16_capacity parameters
  have totalEq : total = 513 + (total - 513) := by omega
  have slotCard : Fintype.card FinalWorkQ16DigestSlot = 513 :=
    finalWorkQ16DigestSlot_card
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      ((castFreshAnswerTape
          (congrArg (fun count => count + (total - 513)) slotCard).symm
        ).trans
        (router.fullCoordinateEquiv.trans
          ((Equiv.prodCongr finalWorkQ16DigestSlotFunctionEquiv
            (Equiv.refl (ExactCompilerFinalWorkQ16Residual parameters))).trans
              (Equiv.prodComm
                (Digest256 × Q16CandidateDigestForest)
                (ExactCompilerFinalWorkQ16Residual parameters)))))

theorem exact_compiler_causal_final_work_q16_event_probability_le_semantic
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape → ExactCompilerCausalFinalWorkQ16Router parameters)
    (bad : HiddenTape → ExactCompilerFinalWorkQ16Residual parameters →
      Finset (Fin 262144))
    (badCard : ∀ hidden residual, (bad hidden residual).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalFinalWorkQ16Coordinates parameters (router hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
          (fun residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
            finalWorkQ16SuccessfulBadEvent (bad hidden residual))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
            ENNReal)) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_final_work_q16_probability_le
    (exactCompilerCausalFinalWorkQ16Coordinates parameters (router hidden))
    (bad hidden) (badCard hidden) reference traceExists
    (jointEventSlice event hidden) (covered hidden)

end

#print axioms successfulFinalWorkQ16TotalEquiv
#print axioms uniform_final_work_q16_bad_probability_eq_product
#print axioms uniform_final_work_q16_bad_probability_le_semantic
#print axioms uniform_tape_dependent_final_work_q16_probability_le
#print axioms finalWorkQ16DigestSlotFunctionEquiv
#print axioms exactCompilerCausalFinalWorkQ16Coordinates
#print axioms exact_compiler_causal_final_work_q16_event_probability_le_semantic

end AspisK1.V7Tag73CausalQ16FinalWorkProbability
