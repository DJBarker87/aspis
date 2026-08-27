import AspisFormal.K1.V7Tag73CausalGammaProbability

/-!
# Complete duplex causal gamma probability

This is the causal sampler theorem used by the future-response argument.  In
addition to every squeeze-output word and stopping path, its nuisance factor
retains all independent DOM_ADVANCE digests.  The returned nonzero gamma is
the only coordinate separated from that complete nuisance.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73CompleteCausalGammaProbability

open MeasureTheory
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisV5ComponentCQM31TowerExact

noncomputable section

def completeFixedSkeletonValueLaw
    (skeleton : Tag73CompleteSamplerSkeleton) :
    PMF (Tag73CompleteSamplerSkeleton × NonzeroQM31Exact) :=
  (PMF.uniformOfFintype NonzeroQM31Exact).map
    fun value => (skeleton, value)

def completeSkeletonValueJointLaw :
    PMF (Tag73CompleteSamplerSkeleton × NonzeroQM31Exact) :=
  (PMF.uniformOfFintype Tag73CompleteSamplerSkeleton).bind
    completeFixedSkeletonValueLaw

theorem completeSkeletonValueJointLaw_eq_uniform :
    completeSkeletonValueJointLaw =
      PMF.uniformOfFintype
        (Tag73CompleteSamplerSkeleton × NonzeroQM31Exact) := by
  classical
  ext pair
  rw [completeSkeletonValueJointLaw, PMF.bind_apply]
  rw [tsum_eq_single pair.1]
  · unfold completeFixedSkeletonValueLaw
    rw [PMF.map_apply, tsum_eq_single pair.2]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply,
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
        Fintype.card_prod, Nat.cast_mul]
      simp only [Fintype.card_prod, Nat.cast_mul]
      change
        (((Fintype.card Tag73OrdinaryAttemptSkeletons : ENNReal) *
              (Fintype.card Tag73NonzeroValueSkeleton : ENNReal)) *
            (Fintype.card Tag73AdvanceDigestGhosts : ENNReal))⁻¹ *
            (Fintype.card NonzeroQM31Exact : ENNReal)⁻¹ =
          ((((Fintype.card Tag73OrdinaryAttemptSkeletons : ENNReal) *
                (Fintype.card Tag73NonzeroValueSkeleton : ENNReal)) *
              (Fintype.card Tag73AdvanceDigestGhosts : ENNReal)) *
            (Fintype.card NonzeroQM31Exact : ENNReal))⁻¹
      exact (ENNReal.mul_inv
        (a := ((Fintype.card Tag73OrdinaryAttemptSkeletons : ENNReal) *
            (Fintype.card Tag73NonzeroValueSkeleton : ENNReal)) *
          (Fintype.card Tag73AdvanceDigestGhosts : ENNReal))
        (b := (Fintype.card NonzeroQM31Exact : ENNReal))
        (Or.inl (mul_ne_zero
          (mul_ne_zero
            (Nat.cast_ne_zero.mpr
              (Fintype.card_ne_zero :
                Fintype.card Tag73OrdinaryAttemptSkeletons ≠ 0))
            (Nat.cast_ne_zero.mpr
              (Fintype.card_ne_zero :
                Fintype.card Tag73NonzeroValueSkeleton ≠ 0)))
          (Nat.cast_ne_zero.mpr
            (Fintype.card_ne_zero :
              Fintype.card Tag73AdvanceDigestGhosts ≠ 0))))
        (Or.inl (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.natCast_ne_top
              (Fintype.card Tag73OrdinaryAttemptSkeletons))
            (ENNReal.natCast_ne_top
              (Fintype.card Tag73NonzeroValueSkeleton)))
          (ENNReal.natCast_ne_top
            (Fintype.card Tag73AdvanceDigestGhosts))))).symm
    · intro value valueNe
      rw [if_neg]
      intro equal
      exact valueNe (congrArg Prod.snd equal).symm
  · intro skeleton skeletonNe
    have mappedZero : completeFixedSkeletonValueLaw skeleton pair = 0 := by
      unfold completeFixedSkeletonValueLaw
      rw [PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro value
      rw [if_neg]
      intro equal
      exact skeletonNe (congrArg Prod.fst equal).symm
    rw [mappedZero, mul_zero]

theorem successful_duplex_factorization_law :
    (PMF.uniformOfFintype SuccessfulTag73DuplexNonzeroAttempts).map
        successfulDuplexNonzeroFactorization =
      completeSkeletonValueJointLaw := by
  calc
    (PMF.uniformOfFintype SuccessfulTag73DuplexNonzeroAttempts).map
        successfulDuplexNonzeroFactorization =
      PMF.uniformOfFintype
        (Tag73CompleteSamplerSkeleton × NonzeroQM31Exact) :=
      AspisV5RankOneOpeningHiding.uniform_map_equiv
        successfulDuplexNonzeroFactorization
    _ = completeSkeletonValueJointLaw :=
      completeSkeletonValueJointLaw_eq_uniform.symm

def completeSkeletonDependentGammaEvent
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact) :
    Set (Tag73CompleteSamplerSkeleton × NonzeroQM31Exact) :=
  {pair | pair.2.1 ∈ target pair.1}

def completeSkeletonGammaEventSlice
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact)
    (skeleton : Tag73CompleteSamplerSkeleton) : Set NonzeroQM31Exact :=
  {value | value.1 ∈ target skeleton}

def duplexSkeletonDependentGammaEvent
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact) :
    Set SuccessfulTag73DuplexNonzeroAttempts :=
  successfulDuplexNonzeroFactorization ⁻¹'
    completeSkeletonDependentGammaEvent target

@[simp] theorem mem_duplexSkeletonDependentGammaEvent
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact)
    (sample : SuccessfulTag73DuplexNonzeroAttempts) :
    sample ∈ duplexSkeletonDependentGammaEvent target ↔
      (successfulDuplexNonzeroFactorization sample).2.1 ∈
        target (successfulDuplexNonzeroFactorization sample).1 := by
  rfl

theorem complete_joint_event_probability_eq_weighted_slices
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact) :
    completeSkeletonValueJointLaw.toOuterMeasure
        (completeSkeletonDependentGammaEvent target) =
      ∑' skeleton : Tag73CompleteSamplerSkeleton,
        (PMF.uniformOfFintype Tag73CompleteSamplerSkeleton) skeleton *
          (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
            (completeSkeletonGammaEventSlice target skeleton) := by
  unfold completeSkeletonValueJointLaw completeFixedSkeletonValueLaw
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro skeleton
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem complete_successful_value_slice_probability_le
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact)
    (skeleton : Tag73CompleteSamplerSkeleton) :
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (completeSkeletonGammaEventSlice target skeleton) ≤
      ((target skeleton).card : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  change (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
      (nonzeroTargetEvent (target skeleton)) ≤ _
  exact uniform_nonzero_target_probability_le (target skeleton)

theorem complete_skeleton_dependent_gamma_probability_le
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    completeSkeletonValueJointLaw.toOuterMeasure
        (completeSkeletonDependentGammaEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  rw [complete_joint_event_probability_eq_weighted_slices]
  calc
    (∑' skeleton : Tag73CompleteSamplerSkeleton,
        (PMF.uniformOfFintype Tag73CompleteSamplerSkeleton) skeleton *
          (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
            (completeSkeletonGammaEventSlice target skeleton)) ≤
        ∑' skeleton : Tag73CompleteSamplerSkeleton,
          (PMF.uniformOfFintype Tag73CompleteSamplerSkeleton) skeleton *
            ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      exact ENNReal.tsum_le_tsum fun skeleton => mul_le_mul_left'
        ((complete_successful_value_slice_probability_le target skeleton).trans <| by
          gcongr
          exact_mod_cast targetCap skeleton)
        ((PMF.uniformOfFintype Tag73CompleteSamplerSkeleton) skeleton)
    _ = (∑' skeleton : Tag73CompleteSamplerSkeleton,
          (PMF.uniformOfFintype Tag73CompleteSamplerSkeleton) skeleton) *
          ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      exact ENNReal.tsum_mul_right
    _ = (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
      rw [PMF.tsum_coe, one_mul]

/-- Complete deployed-sampler causal bound.  Unlike the output-word marginal,
this theorem permits the target family to depend on every independent duplex
advance answer. -/
theorem duplex_skeleton_dependent_gamma_probability_le
    (target : Tag73CompleteSamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype
        SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
        (duplexSkeletonDependentGammaEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype
        SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
        (duplexSkeletonDependentGammaEvent target) =
      ((PMF.uniformOfFintype
          SuccessfulTag73DuplexNonzeroAttempts).map
        successfulDuplexNonzeroFactorization).toOuterMeasure
          (completeSkeletonDependentGammaEvent target) := by
            rw [PMF.toOuterMeasure_map_apply]
            rfl
    _ = completeSkeletonValueJointLaw.toOuterMeasure
          (completeSkeletonDependentGammaEvent target) := by
            rw [successful_duplex_factorization_law]
    _ ≤ (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) :=
      complete_skeleton_dependent_gamma_probability_le target cap targetCap

end


#print axioms successful_duplex_factorization_law
#print axioms complete_skeleton_dependent_gamma_probability_le
#print axioms duplex_skeleton_dependent_gamma_probability_le

end AspisK1.V7Tag73CompleteCausalGammaProbability
