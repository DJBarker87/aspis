import AspisFormal.K1.V7Tag73CompleteCausalOrdinaryProbability
import AspisFormal.K1.V7Tag73VariablePrefixGammaProbability
import AspisFormal.Pool.V7K15IndependentRootCertificates

/-!
# Mathematical sampler adapters for the fixed K1.5 families

This file contains only finite uniform-sampler mathematics.  It does not
claim that an exact compiler event is covered by one of these target events.
That last inclusion remains a source/causal-coordinate obligation.

In particular, the OOD adapter models the two deployed ordinary challenges
as one exact ordered pair.  Its law is derived from the sequential bind and
then transported through the complete duplex factorization; no independence
premise is accepted.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K15FixedSamplerProbabilityAdapters

open MeasureTheory
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaProbability
open AspisPool.V7K15IndependentRootCertificates
open AspisPool.V7PointClaimBatchBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5RelationSumcheckSoundness

noncomputable section

/-! ## One complete ordinary challenge -/

/-- A reusable spelling of the exact complete-duplex ordinary target event.
The target is fixed by all rejection and advance nuisance before the isolated
ordinary value is exposed. -/
def fixedOrdinarySamplerTargetEvent
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact) :
    Set SuccessfulTag73DuplexOrdinaryAttempt :=
  duplexOrdinaryDependentEvent target

/-- Exact `cap / P^4` bound for one complete ordinary challenge. -/
theorem fixed_ordinary_sampler_target_probability_le
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (cap : Nat) (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).toOuterMeasure
        (fixedOrdinarySamplerTargetEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  exact duplex_ordinary_dependent_probability_le target cap targetCap

/-- The literal zero target used by `muZero` and `inactiveChi` costs exactly
one ordinary-field root. -/
theorem fixed_ordinary_zero_target_probability_le
    (target : Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (targetZero : ∀ skeleton, target skeleton = zeroChallengeSet) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryAttempt).toOuterMeasure
        (fixedOrdinarySamplerTargetEvent target) ≤
      (1 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  have bound := fixed_ordinary_sampler_target_probability_le target 1 (by
    intro skeleton
    rw [targetZero skeleton, zeroChallengeSet_card])
  simpa using bound

/-! ## Two sequential complete ordinary challenges -/

abbrev SuccessfulTag73DuplexOrdinaryPair :=
  SuccessfulTag73DuplexOrdinaryAttempt × SuccessfulTag73DuplexOrdinaryAttempt

abbrev Tag73CompleteOrdinaryPairSkeleton :=
  Tag73CompleteOrdinarySamplerSkeleton ×
    Tag73CompleteOrdinarySamplerSkeleton

/-- Retain both complete rejection/advance paths and isolate the ordered pair
of returned ordinary values. -/
def successfulDuplexOrdinaryPairFactorization :
    SuccessfulTag73DuplexOrdinaryPair ≃
      Tag73CompleteOrdinaryPairSkeleton × (QM31Exact × QM31Exact) :=
  (Equiv.prodCongr successfulDuplexOrdinaryFactorization
      successfulDuplexOrdinaryFactorization).trans
    { toFun := fun pair =>
        ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))
      invFun := fun pair =>
        ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))
      left_inv := by intro pair; rfl
      right_inv := by intro pair; rfl }

/-- The literal sequential experiment: draw the first ordinary value, then
draw the second and retain their order. -/
def sequentialUniformOrdinaryPairLaw : PMF (QM31Exact × QM31Exact) :=
  (PMF.uniformOfFintype QM31Exact).bind fun first =>
    (PMF.uniformOfFintype QM31Exact).map fun second => (first, second)

/-- The sequential bind is exactly uniform on ordered pairs.  Thus later uses
of the pair law need no independence assumption. -/
theorem sequentialUniformOrdinaryPairLaw_eq_uniform :
    sequentialUniformOrdinaryPairLaw =
      PMF.uniformOfFintype (QM31Exact × QM31Exact) := by
  classical
  ext pair
  rw [sequentialUniformOrdinaryPairLaw, PMF.bind_apply]
  rw [tsum_eq_single pair.1]
  · rw [PMF.map_apply, tsum_eq_single pair.2]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply,
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
        Fintype.card_prod, Nat.cast_mul]
      change
        (Fintype.card QM31Exact : ENNReal)⁻¹ *
            (Fintype.card QM31Exact : ENNReal)⁻¹ =
          ((Fintype.card QM31Exact : ENNReal) *
            (Fintype.card QM31Exact : ENNReal))⁻¹
      exact (ENNReal.mul_inv
        (a := (Fintype.card QM31Exact : ENNReal))
        (b := (Fintype.card QM31Exact : ENNReal))
        (Or.inl (Nat.cast_ne_zero.mpr
          (Fintype.card_ne_zero : Fintype.card QM31Exact ≠ 0)))
        (Or.inl (ENNReal.natCast_ne_top
          (Fintype.card QM31Exact)))).symm
    · intro second secondNe
      rw [if_neg]
      intro equal
      exact secondNe (congrArg Prod.snd equal).symm
  · intro first firstNe
    have mappedZero :
        ((PMF.uniformOfFintype QM31Exact).map
          fun second => (first, second)) pair = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro second
      rw [if_neg]
      intro equal
      exact firstNe (congrArg Prod.fst equal).symm
    rw [mappedZero, mul_zero]

/-- The complete two-attempt tape also has the exact ordered product law. -/
theorem successful_duplex_ordinary_pair_factorization_law :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryPair).map
        successfulDuplexOrdinaryPairFactorization =
      PMF.uniformOfFintype
        (Tag73CompleteOrdinaryPairSkeleton ×
          (QM31Exact × QM31Exact)) := by
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv
    successfulDuplexOrdinaryPairFactorization

/-- Exact mass of any finite ordered-pair target. -/
theorem uniform_ordinary_pair_target_probability_exact
    (target : Finset (QM31Exact × QM31Exact)) :
    sequentialUniformOrdinaryPairLaw.toOuterMeasure
        {pair | pair ∈ target} =
      (target.card : ENNReal) /
        (((P ^ 4 : Nat) * (P ^ 4 : Nat) : Nat) : ENNReal) := by
  classical
  rw [sequentialUniformOrdinaryPairLaw_eq_uniform,
    PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_prod,
    qm31Exact_card]
  congr 1
  norm_cast
  exact Fintype.card_coe target

/-- A target occupying at most `cap * |QM31|` ordered pairs costs at most
`cap / |QM31|`.  This is the exact shape used by the two sequential OOD
mixes. -/
theorem uniform_ordinary_pair_target_probability_le
    (target : Finset (QM31Exact × QM31Exact)) (cap : Nat)
    (targetCap : target.card ≤ cap * Fintype.card QM31Exact) :
    sequentialUniformOrdinaryPairLaw.toOuterMeasure
        {pair | pair ∈ target} ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  rw [uniform_ordinary_pair_target_probability_exact]
  rw [qm31Exact_card] at targetCap
  rw [Nat.cast_mul]
  have denominatorNe : ((P ^ 4 : Nat) : ENNReal) ≠ 0 := by
    norm_num [P]
  rw [ENNReal.div_le_iff (mul_ne_zero denominatorNe denominatorNe)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _))]
  calc
    (target.card : ENNReal) ≤
        (cap : ENNReal) * ((P ^ 4 : Nat) : ENNReal) := by
      exact_mod_cast targetCap
    _ = ((cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) *
        (((P ^ 4 : Nat) : ENNReal) *
          ((P ^ 4 : Nat) : ENNReal)) := by
      rw [← mul_assoc,
        ENNReal.div_mul_cancel denominatorNe (ENNReal.natCast_ne_top _)]

def completeOrdinaryPairDependentEvent
    (target : Tag73CompleteOrdinaryPairSkeleton →
      Finset (QM31Exact × QM31Exact)) :
    Set (Tag73CompleteOrdinaryPairSkeleton ×
      (QM31Exact × QM31Exact)) :=
  {pair | pair.2 ∈ target pair.1}

def duplexOrdinaryPairDependentEvent
    (target : Tag73CompleteOrdinaryPairSkeleton →
      Finset (QM31Exact × QM31Exact)) :
    Set SuccessfulTag73DuplexOrdinaryPair :=
  successfulDuplexOrdinaryPairFactorization ⁻¹'
    completeOrdinaryPairDependentEvent target

/-- Nuisance-dependent ordered-pair bound.  The target may depend on both
complete rejection/advance paths, but not on either isolated value. -/
theorem duplex_ordinary_pair_dependent_probability_le
    (target : Tag73CompleteOrdinaryPairSkeleton →
      Finset (QM31Exact × QM31Exact))
    (cap : Nat)
    (targetCap : ∀ skeleton,
      (target skeleton).card ≤ cap * Fintype.card QM31Exact) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryPair).toOuterMeasure
        (duplexOrdinaryPairDependentEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryPair).toOuterMeasure
        (duplexOrdinaryPairDependentEvent target) =
      (PMF.uniformOfFintype
        (Tag73CompleteOrdinaryPairSkeleton ×
          (QM31Exact × QM31Exact))).toOuterMeasure
        (completeOrdinaryPairDependentEvent target) := by
      calc
        _ = ((PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryPair).map
              successfulDuplexOrdinaryPairFactorization).toOuterMeasure
              (completeOrdinaryPairDependentEvent target) := by
            rw [PMF.toOuterMeasure_map_apply]
            rfl
        _ = _ := by rw [successful_duplex_ordinary_pair_factorization_law]
    _ ≤ _ := by
      apply uniform_product_event_probability_le_of_every_slice_le
      intro skeleton
      rw [show productEventFstSlice
          (completeOrdinaryPairDependentEvent target) skeleton =
            {pair | pair ∈ target skeleton} by rfl]
      rw [← sequentialUniformOrdinaryPairLaw_eq_uniform]
      exact uniform_ordinary_pair_target_probability_le
        (target skeleton) cap (targetCap skeleton)

/-- The exact OOD target may depend on all pre-pair nuisance.  In particular,
the second value-error function may depend on the first mix, exactly as in the
deployed sequential recurrence. -/
noncomputable def fixedOodMixPairTarget
    (trace : Tag73CompleteOrdinaryPairSkeleton →
      FourRoundDiscrepancyTrace QM31Exact)
    (round : Fin 4) (skeleton : Tag73CompleteOrdinaryPairSkeleton) :
    Finset (QM31Exact × QM31Exact) :=
  falseSequentialTwoMixCancellationSet
    ((trace skeleton).before round.castSucc)
    ((trace skeleton).firstValueError round)
    ((trace skeleton).secondValueError round)

/-- Concrete OOD specialization using the exact nuisance-dependent algebraic
pair set. -/
theorem duplex_ordinary_ood_mix_probability_le
    (trace : Tag73CompleteOrdinaryPairSkeleton →
      FourRoundDiscrepancyTrace QM31Exact)
    (round : Fin 4) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexOrdinaryPair).toOuterMeasure
        (duplexOrdinaryPairDependentEvent
          (fixedOodMixPairTarget trace round)) ≤
      (2 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply duplex_ordinary_pair_dependent_probability_le
    (fixedOodMixPairTarget trace round) 2
  intro skeleton
  exact oodMixCancellation_exact_pair_set_card_le (trace skeleton) round

/-! ## Variable-prefix nonzero challenge (kappa) -/

/-- Reusable exact variable-prefix nonzero target bound.  This is independent
of whether the supplied pre-value target will later be used for gamma or
kappa. -/
theorem variable_prefix_nonzero_target_probability_le
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat) (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).toOuterMeasure
        (routedSkeletonDependentGammaEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact routed_skeleton_dependent_gamma_probability_le target cap targetCap

/-- Concrete degree-two kappa target specialization. -/
theorem variable_prefix_kappa_two_root_probability_le
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ 2) :
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).toOuterMeasure
        (routedSkeletonDependentGammaEvent target) ≤
      (2 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact variable_prefix_nonzero_target_probability_le target 2 targetCap

/-- Literal degree-two nonzero kappa root set chosen by a complete nuisance
skeleton. -/
noncomputable def variablePrefixKappaCollisionTarget
    (values : VariableGammaCompleteSkeleton → Fin 3 → QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) : Finset QM31Exact :=
  threeRowNonzeroCollisionSet (values skeleton)

/-- Exact kappa specialization from the existing degree-two polynomial root
theorem.  The discrepancy vector is fixed by the nuisance skeleton and must
be nonzero before kappa is exposed. -/
theorem variable_prefix_kappa_collision_probability_le
    (values : VariableGammaCompleteSkeleton → Fin 3 → QM31Exact)
    (nonzero : ∀ skeleton, values skeleton ≠ 0) :
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).toOuterMeasure
        (routedSkeletonDependentGammaEvent
          (variablePrefixKappaCollisionTarget values)) ≤
      (2 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply variable_prefix_kappa_two_root_probability_le
  intro skeleton
  exact threeRow_nonzero_collision_card_le_two
    (values skeleton) (nonzero skeleton)

end

#print axioms fixed_ordinary_sampler_target_probability_le
#print axioms fixed_ordinary_zero_target_probability_le
#print axioms sequentialUniformOrdinaryPairLaw_eq_uniform
#print axioms successful_duplex_ordinary_pair_factorization_law
#print axioms uniform_ordinary_pair_target_probability_exact
#print axioms uniform_ordinary_pair_target_probability_le
#print axioms duplex_ordinary_pair_dependent_probability_le
#print axioms duplex_ordinary_ood_mix_probability_le
#print axioms variable_prefix_nonzero_target_probability_le
#print axioms variable_prefix_kappa_two_root_probability_le
#print axioms variable_prefix_kappa_collision_probability_le

end AspisK1.V7Tag73K15FixedSamplerProbabilityAdapters
