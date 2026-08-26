import AspisFormal.K1.V7Tag73RawNonzeroSamplerFactorization

/-!
# Causal gamma probability with the complete sampler nuisance retained

This module averages the exact nonzero-QM31 target bound over the complete
deployed sampler skeleton.  Consequently the target selected by a restored
prover may depend on rejection positions, discarded high bits, unused words,
and the independent duplex-advance outputs represented in that skeleton.  It
may not depend on the independently factored nonzero gamma value itself.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73CausalGammaProbability

open MeasureTheory
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

def fixedSkeletonSuccessfulValueLaw
    (skeleton : Tag73OuterSamplerSkeleton) :
    PMF (Tag73OuterSamplerSkeleton × NonzeroQM31Exact) :=
  (PMF.uniformOfFintype NonzeroQM31Exact).map
    fun value => (skeleton, value)

def skeletonSuccessfulValueJointLaw :
    PMF (Tag73OuterSamplerSkeleton × NonzeroQM31Exact) :=
  (PMF.uniformOfFintype Tag73OuterSamplerSkeleton).bind
    fixedSkeletonSuccessfulValueLaw

theorem skeletonSuccessfulValueJointLaw_eq_uniform :
    skeletonSuccessfulValueJointLaw =
      PMF.uniformOfFintype
        (Tag73OuterSamplerSkeleton × NonzeroQM31Exact) := by
  classical
  ext pair
  rw [skeletonSuccessfulValueJointLaw, PMF.bind_apply]
  rw [tsum_eq_single pair.1]
  · unfold fixedSkeletonSuccessfulValueLaw
    rw [PMF.map_apply, tsum_eq_single pair.2]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply,
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
        Fintype.card_prod, Nat.cast_mul]
      have outerCard : Fintype.card Tag73OuterSamplerSkeleton =
          Fintype.card Tag73OrdinaryAttemptSkeletons *
            Fintype.card Tag73NonzeroValueSkeleton := by
        exact Fintype.card_prod _ _
      rw [Fintype.card_prod, outerCard, Nat.cast_mul]
      rw [Nat.cast_mul]
      change
        ((Fintype.card Tag73OrdinaryAttemptSkeletons : ENNReal) *
            (Fintype.card Tag73NonzeroValueSkeleton : ENNReal))⁻¹ *
            (Fintype.card NonzeroQM31Exact : ENNReal)⁻¹ =
          (((Fintype.card Tag73OrdinaryAttemptSkeletons : ENNReal) *
              (Fintype.card Tag73NonzeroValueSkeleton : ENNReal)) *
            (Fintype.card NonzeroQM31Exact : ENNReal))⁻¹
      exact (ENNReal.mul_inv
        (a := (Fintype.card Tag73OrdinaryAttemptSkeletons : ENNReal) *
          (Fintype.card Tag73NonzeroValueSkeleton : ENNReal))
        (b := (Fintype.card NonzeroQM31Exact : ENNReal))
        (Or.inl (mul_ne_zero
          (Nat.cast_ne_zero.mpr
            (Fintype.card_ne_zero : Fintype.card
              Tag73OrdinaryAttemptSkeletons ≠ 0))
          (Nat.cast_ne_zero.mpr
            (Fintype.card_ne_zero : Fintype.card
              Tag73NonzeroValueSkeleton ≠ 0))))
        (Or.inl (ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top
            (Fintype.card Tag73OrdinaryAttemptSkeletons))
          (ENNReal.natCast_ne_top
            (Fintype.card Tag73NonzeroValueSkeleton))))).symm
    · intro attempts attemptsNe
      rw [if_neg]
      intro equal
      exact attemptsNe (congrArg Prod.snd equal).symm
  · intro skeleton skeletonNe
    have mappedZero : fixedSkeletonSuccessfulValueLaw skeleton pair = 0 := by
      unfold fixedSkeletonSuccessfulValueLaw
      rw [PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro attempts
      rw [if_neg]
      intro equal
      exact skeletonNe (congrArg Prod.fst equal).symm
    rw [mappedZero, mul_zero]

theorem successful_raw_factorization_law :
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).map
        successfulRawNonzeroFactorization =
      skeletonSuccessfulValueJointLaw := by
  calc
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).map
        successfulRawNonzeroFactorization =
      PMF.uniformOfFintype
        (Tag73OuterSamplerSkeleton × NonzeroQM31Exact) :=
      AspisV5RankOneOpeningHiding.uniform_map_equiv
        successfulRawNonzeroFactorization
    _ = skeletonSuccessfulValueJointLaw :=
      skeletonSuccessfulValueJointLaw_eq_uniform.symm

def skeletonDependentGammaEvent
    (target : Tag73OuterSamplerSkeleton → Finset QM31Exact) :
    Set (Tag73OuterSamplerSkeleton × NonzeroQM31Exact) :=
  {pair | pair.2.1 ∈ target pair.1}

def skeletonGammaEventSlice
    (target : Tag73OuterSamplerSkeleton → Finset QM31Exact)
    (skeleton : Tag73OuterSamplerSkeleton) :
    Set NonzeroQM31Exact :=
  {value | value.1 ∈ target skeleton}

def rawSkeletonDependentGammaEvent
    (target : Tag73OuterSamplerSkeleton → Finset QM31Exact) :
    Set SuccessfulTag73RawNonzeroAttempts :=
  successfulRawNonzeroFactorization ⁻¹'
    skeletonDependentGammaEvent target

theorem skeleton_joint_event_probability_eq_weighted_slices
    (target : Tag73OuterSamplerSkeleton → Finset QM31Exact) :
    skeletonSuccessfulValueJointLaw.toOuterMeasure
        (skeletonDependentGammaEvent target) =
      ∑' skeleton : Tag73OuterSamplerSkeleton,
        (PMF.uniformOfFintype Tag73OuterSamplerSkeleton) skeleton *
          (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
            (skeletonGammaEventSlice target skeleton) := by
  unfold skeletonSuccessfulValueJointLaw fixedSkeletonSuccessfulValueLaw
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro skeleton
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem successful_value_slice_probability_le
    (target : Tag73OuterSamplerSkeleton → Finset QM31Exact)
    (skeleton : Tag73OuterSamplerSkeleton) :
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (skeletonGammaEventSlice target skeleton) ≤
      ((target skeleton).card : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  change (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
      (nonzeroTargetEvent (target skeleton)) ≤ _
  exact uniform_nonzero_target_probability_le (target skeleton)

/-- A target family chosen from the complete sampler skeleton has the same
cap as a single target fixed before gamma.  Averaging over nuisance data costs
nothing. -/
theorem skeleton_dependent_gamma_probability_le
    (target : Tag73OuterSamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    skeletonSuccessfulValueJointLaw.toOuterMeasure
        (skeletonDependentGammaEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  rw [skeleton_joint_event_probability_eq_weighted_slices]
  calc
    (∑' skeleton : Tag73OuterSamplerSkeleton,
        (PMF.uniformOfFintype Tag73OuterSamplerSkeleton) skeleton *
          (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
            (skeletonGammaEventSlice target skeleton)) ≤
        ∑' skeleton : Tag73OuterSamplerSkeleton,
          (PMF.uniformOfFintype Tag73OuterSamplerSkeleton) skeleton *
            ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      exact ENNReal.tsum_le_tsum fun skeleton => mul_le_mul_left'
        ((successful_value_slice_probability_le target skeleton).trans <| by
          gcongr
          exact_mod_cast targetCap skeleton)
        ((PMF.uniformOfFintype Tag73OuterSamplerSkeleton) skeleton)
    _ = (∑' skeleton : Tag73OuterSamplerSkeleton,
          (PMF.uniformOfFintype Tag73OuterSamplerSkeleton) skeleton) *
          ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      exact ENNReal.tsum_mul_right
    _ = (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
      rw [PMF.tsum_coe, one_mul]

/-- The literal successful raw-word experiment inherits the causal target
bound through the exact skeleton/value factorization. -/
theorem raw_skeleton_dependent_gamma_probability_le
    (target : Tag73OuterSamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).toOuterMeasure
        (rawSkeletonDependentGammaEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  have lawEquality := congrArg PMF.toOuterMeasure
    successful_raw_factorization_law
  calc
    (PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).toOuterMeasure
        (rawSkeletonDependentGammaEvent target) =
      ((PMF.uniformOfFintype SuccessfulTag73RawNonzeroAttempts).map
        successfulRawNonzeroFactorization).toOuterMeasure
          (skeletonDependentGammaEvent target) := by
            rw [PMF.toOuterMeasure_map_apply]
            rfl
    _ = skeletonSuccessfulValueJointLaw.toOuterMeasure
          (skeletonDependentGammaEvent target) := by
            rw [successful_raw_factorization_law]
    _ ≤ (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) :=
      skeleton_dependent_gamma_probability_le target cap targetCap

end


#print axioms successful_value_slice_probability_le
#print axioms skeleton_dependent_gamma_probability_le
#print axioms raw_skeleton_dependent_gamma_probability_le

end AspisK1.V7Tag73CausalGammaProbability
