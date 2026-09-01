import AspisFormal.K1.V7Tag73CausalAlphaFinalWorkQ16Probability

/-!
# Joint fold-work, alpha, final-work, and q16 probability

The accepted Tag-73 schedule places a 31-bit fold-work digest before the
alpha-zero sampler and a distinct 34-bit final-work digest before q16.  This
module counts the fold predicate exactly and proves the finite product needed
when source routing must precommit both an alpha-boundary trial and a
final-work/q16 trial.  The two work factors remain at their literal transcript
positions; no reported soundness bound is divided by grinding work.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability

open MeasureTheory
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalQ16FinalWorkDependentBad
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The literal deployed fold-work predicate. -/
def FoldWork31Accepted (digest : Digest256) : Prop :=
  workDigestAccepted .fold digest = true

instance foldWork31AcceptedDecidable (digest : Digest256) :
    Decidable (FoldWork31Accepted digest) := by
  unfold FoldWork31Accepted
  infer_instance

theorem fold_work_31_accepted_iff_head_lt
    (digest : Digest256) :
    FoldWork31Accepted digest ↔
      (bigEndianHeadBytesEquiv (digestHeadTailEquiv digest).1).val < 2 ^ 33 := by
  rw [FoldWork31Accepted, work_digest_accepted_iff,
    bigEndianHead64_eq_head_equiv]
  norm_num [workBits]

abbrev FoldWork31AcceptedDigest :=
  {digest : Digest256 // FoldWork31Accepted digest}

def foldWork31AcceptedDigestEquiv :
    FoldWork31AcceptedDigest ≃ Fin (2 ^ 33) × FinalWorkTailBytes where
  toFun digest :=
    let split := digestHeadTailEquiv digest.1
    let head := bigEndianHeadBytesEquiv split.1
    (⟨head.val, (fold_work_31_accepted_iff_head_lt digest.1).mp digest.2⟩,
      split.2)
  invFun coordinates :=
    let head : Fin (2 ^ 64) :=
      ⟨coordinates.1.val, coordinates.1.isLt.trans_le (by norm_num)⟩
    let digest := digestHeadTailEquiv.symm
      (bigEndianHeadBytesEquiv.symm head, coordinates.2)
    ⟨digest, (fold_work_31_accepted_iff_head_lt digest).mpr (by
      simp [digest, head])⟩
  left_inv digest := by
    apply Subtype.ext
    apply digestHeadTailEquiv.injective
    apply Prod.ext
    · apply bigEndianHeadBytesEquiv.injective
      apply Fin.ext
      simp
    · simp
  right_inv coordinates := by
    apply Prod.ext
    · apply Fin.ext
      simp
    · simp

noncomputable instance foldWork31AcceptedDigestFintype :
    Fintype FoldWork31AcceptedDigest :=
  Fintype.ofEquiv
    (Fin (2 ^ 33) × FinalWorkTailBytes)
    foldWork31AcceptedDigestEquiv.symm

def foldWork31AcceptedDigestPackedEquiv :
    FoldWork31AcceptedDigest ≃ Fin (2 ^ 225) :=
  foldWork31AcceptedDigestEquiv.trans
    ((Equiv.prodCongr (Equiv.refl (Fin (2 ^ 33)))
      finalWorkTailBytesEquiv).trans
        (finProdFinEquiv.trans (finCongr (by rw [← pow_add]))))

theorem fold_work_31_accepted_digest_card :
    Fintype.card FoldWork31AcceptedDigest = 2 ^ 225 := by
  rw [Fintype.card_congr foldWork31AcceptedDigestPackedEquiv,
    Fintype.card_fin]

def foldWork31AcceptedEvent : Set Digest256 :=
  {digest | FoldWork31Accepted digest}

def foldWork31AcceptedEventSubtypeEquiv :
    {digest : Digest256 // digest ∈ foldWork31AcceptedEvent} ≃
      FoldWork31AcceptedDigest :=
  Equiv.refl _

noncomputable instance foldWork31AcceptedEventFintype :
    Fintype {digest : Digest256 // digest ∈ foldWork31AcceptedEvent} :=
  Fintype.ofEquiv FoldWork31AcceptedDigest
    foldWork31AcceptedEventSubtypeEquiv.symm

theorem uniform_fold_work_31_probability_exact :
    (PMF.uniformOfFintype Digest256).toOuterMeasure
        foldWork31AcceptedEvent =
      (1 : ENNReal) / (2 : ENNReal) ^ 31 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    Fintype.card_congr foldWork31AcceptedEventSubtypeEquiv,
    fold_work_31_accepted_digest_card]
  have digestCard : Fintype.card Digest256 = 2 ^ 256 := by
    rw [Fintype.card_congr digest256PackedEquiv, Fintype.card_fin]
  rw [digestCard]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show 256 = 225 + 31 by norm_num, pow_add]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by simp) (by positivity))
    (ENNReal.div_ne_top (by simp) (by positivity))).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  rw [div_mul_eq_div_div]
  simp

/-- A successful final-work/q16 coordinate together with a separately
positioned fold-work answer. -/
def foldFinalWorkQ16TotalSucceeds
    (coordinates : Digest256 × (Digest256 × Q16CandidateDigestForest)) : Prop :=
  finalWorkQ16TotalSucceeds coordinates.2

abbrev SuccessfulFoldFinalWorkQ16Total :=
  {coordinates : Digest256 × (Digest256 × Q16CandidateDigestForest) //
    foldFinalWorkQ16TotalSucceeds coordinates}

def successfulFoldFinalWorkQ16TotalEquiv :
    SuccessfulFoldFinalWorkQ16Total ≃
      Digest256 × (Digest256 × SuccessfulQ16Coordinates) where
  toFun coordinates :=
    (coordinates.1.1,
      successfulFinalWorkQ16TotalEquiv
        ⟨coordinates.1.2, coordinates.2⟩)
  invFun coordinates :=
    let finalCoordinates := successfulFinalWorkQ16TotalEquiv.symm coordinates.2
    ⟨(coordinates.1, finalCoordinates.1), finalCoordinates.2⟩
  left_inv coordinates := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        (successfulFinalWorkQ16TotalEquiv.symm_apply_apply
          ⟨coordinates.1.2, coordinates.2⟩)
  right_inv coordinates := by
    apply Prod.ext
    · rfl
    · exact successfulFinalWorkQ16TotalEquiv.apply_symm_apply coordinates.2

def foldFinalWorkQ16SuccessfulBadEvent
    (bad : Digest256 → Digest256 → Finset (Fin 262144)) :
    Set (Digest256 × (Digest256 × SuccessfulQ16Coordinates)) :=
  {coordinates |
    FoldWork31Accepted coordinates.1 ∧
      coordinates.2 ∈
        finalWorkQ16SuccessfulDependentBadEvent (bad coordinates.1)}

theorem product_slice_fold_final_work_q16_dependent_bad
    (bad : Digest256 → Digest256 → Finset (Fin 262144))
    (fold : Digest256) :
    productEventFstSlice
        (foldFinalWorkQ16SuccessfulBadEvent bad) fold =
      if FoldWork31Accepted fold then
        finalWorkQ16SuccessfulDependentBadEvent (bad fold)
      else ∅ := by
  classical
  ext coordinates
  by_cases accepted : FoldWork31Accepted fold <;>
    simp [productEventFstSlice,
      foldFinalWorkQ16SuccessfulBadEvent, accepted]

theorem uniform_fold_final_work_q16_dependent_bad_probability_le
    [Nonempty SuccessfulQ16Coordinates]
    (bad : Digest256 → Digest256 → Finset (Fin 262144))
    (badCard : ∀ fold work, (bad fold work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    (PMF.uniformOfFintype
      (Digest256 × (Digest256 × SuccessfulQ16Coordinates))).toOuterMeasure
        (foldFinalWorkQ16SuccessfulBadEvent bad) ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((Nat.choose 9557 16 : ENNReal) /
            (semanticCompactFavourable : ENNReal))) := by
  classical
  let bound : ENNReal :=
    ((1 : ENNReal) / (2 : ENNReal) ^ 34) *
      ((Nat.choose 9557 16 : ENNReal) /
        (semanticCompactFavourable : ENNReal))
  rw [uniform_product_event_probability_eq_weighted_slices]
  calc
    (∑' fold : Digest256,
        (PMF.uniformOfFintype Digest256) fold *
          (PMF.uniformOfFintype
            (Digest256 × SuccessfulQ16Coordinates)).toOuterMeasure
              (productEventFstSlice
                (foldFinalWorkQ16SuccessfulBadEvent bad) fold)) ≤
        ∑' fold : Digest256,
          (PMF.uniformOfFintype Digest256) fold *
            (if FoldWork31Accepted fold then bound else 0) := by
      exact ENNReal.tsum_le_tsum fun fold => by
        apply mul_le_mul_left'
        rw [product_slice_fold_final_work_q16_dependent_bad]
        by_cases accepted : FoldWork31Accepted fold
        · simp only [accepted, if_true]
          exact uniform_final_work_q16_dependent_bad_probability_le_semantic
            (bad fold) (badCard fold) reference traceExists
        · simp [accepted]
    _ = (∑' fold : Digest256,
          foldWork31AcceptedEvent.indicator
            (fun fold => (PMF.uniformOfFintype Digest256) fold) fold) *
          bound := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro fold
      by_cases accepted : FoldWork31Accepted fold <;>
        simp [foldWork31AcceptedEvent, accepted]
    _ = (PMF.uniformOfFintype Digest256).toOuterMeasure
          foldWork31AcceptedEvent * bound := by
      rw [PMF.toOuterMeasure_apply]
    _ = ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((Nat.choose 9557 16 : ENNReal) /
            (semanticCompactFavourable : ENNReal))) := by
      rw [uniform_fold_work_31_probability_exact]

/-- An arbitrary residual context—including the four alpha-zero blocks—may
select the q16 bad family after seeing both positioned work answers.  Only the
two work digests and q16 forest contribute probability factors. -/
theorem uniform_tape_dependent_fold_alpha_final_work_answer_q16_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    (coordinates : Tape ≃
      Residual ×
        (Digest256 × (Digest256 × Q16CandidateDigestForest)))
    (bad : Residual → Digest256 → Digest256 → Finset (Fin 262144))
    (badCard : ∀ residual fold work,
      (bad residual fold work).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent foldFinalWorkQ16TotalSucceeds
        (fun residual => successfulFoldFinalWorkQ16TotalEquiv ⁻¹'
          foldFinalWorkQ16SuccessfulBadEvent (bad residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      ((1 : ENNReal) / (2 : ENNReal) ^ 31) *
        (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
          ((Nat.choose 9557 16 : ENNReal) /
            (semanticCompactFavourable : ENNReal))) := by
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
  letI : Nonempty SuccessfulFoldFinalWorkQ16Total :=
    ⟨successfulFoldFinalWorkQ16TotalEquiv.symm
      (Classical.choice inferInstance,
        Classical.choice inferInstance, successfulCoordinates)⟩
  apply uniform_tape_dependent_successful_event_probability_le
    foldFinalWorkQ16TotalSucceeds coordinates
      successfulFoldFinalWorkQ16TotalEquiv
    (fun residual => foldFinalWorkQ16SuccessfulBadEvent (bad residual))
    (((1 : ENNReal) / (2 : ENNReal) ^ 31) *
      (((1 : ENNReal) / (2 : ENNReal) ^ 34) *
        ((Nat.choose 9557 16 : ENNReal) /
          (semanticCompactFavourable : ENNReal))))
  · intro residual
    exact uniform_fold_final_work_q16_dependent_bad_probability_le
      (bad residual) (badCard residual) reference traceExists
  · exact covered

end

#print axioms fold_work_31_accepted_iff_head_lt
#print axioms foldWork31AcceptedDigestEquiv
#print axioms fold_work_31_accepted_digest_card
#print axioms uniform_fold_work_31_probability_exact
#print axioms product_slice_fold_final_work_q16_dependent_bad
#print axioms uniform_fold_final_work_q16_dependent_bad_probability_le
#print axioms
  uniform_tape_dependent_fold_alpha_final_work_answer_q16_probability_le

end AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
