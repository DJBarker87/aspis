import AspisFormal.K1.V7Tag73VariablePrefixGammaFactorization
import AspisFormal.K1.V7Tag73CounterfactualK13Provider
import AspisFormal.K1.V7Tag73CausalRestoredFamily
import AspisFormal.K1.V7Tag73RestoredPointCompatibleK14

/-!
# Exact probability for the variable-prefix Tag-73 gamma sampler

The production outer sampler stops after the first successful, nonzero
ordinary decode.  Its successful routed tape factors into a complete nuisance
skeleton and one nonzero QM31 value.  This file transports the uniform law
through that exact equivalence and proves the corresponding dependent-family
cardinality bound.

No completed execution context or source-level coverage statement occurs in
this probability layer.  A target may depend on the complete pre-value
nuisance skeleton, but never on the subsequently exposed value coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73VariablePrefixGammaProbability

open MeasureTheory
open AspisK1.V7Tag73CounterfactualK13Provider
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- With the complete variable-prefix nuisance fixed, the remaining law is
exactly uniform on nonzero QM31. -/
def variablePrefixFixedSkeletonValueLaw
    (skeleton : VariableGammaCompleteSkeleton) :
    PMF (VariableGammaCompleteSkeleton × NonzeroQM31Exact) :=
  (PMF.uniformOfFintype NonzeroQM31Exact).map
    fun value => (skeleton, value)

/-- First sample all variable-prefix nuisance, then the returned nonzero
challenge. -/
def variablePrefixSkeletonValueJointLaw :
    PMF (VariableGammaCompleteSkeleton × NonzeroQM31Exact) :=
  (PMF.uniformOfFintype VariableGammaCompleteSkeleton).bind
    variablePrefixFixedSkeletonValueLaw

theorem variablePrefixSkeletonValueJointLaw_eq_uniform :
    variablePrefixSkeletonValueJointLaw =
      PMF.uniformOfFintype
        (VariableGammaCompleteSkeleton × NonzeroQM31Exact) := by
  classical
  ext pair
  rw [variablePrefixSkeletonValueJointLaw, PMF.bind_apply]
  rw [tsum_eq_single pair.1]
  · unfold variablePrefixFixedSkeletonValueLaw
    rw [PMF.map_apply, tsum_eq_single pair.2]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply,
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
        Fintype.card_prod, Nat.cast_mul]
      change
        (Fintype.card VariableGammaCompleteSkeleton : ENNReal)⁻¹ *
            (Fintype.card NonzeroQM31Exact : ENNReal)⁻¹ =
          ((Fintype.card VariableGammaCompleteSkeleton : ENNReal) *
            (Fintype.card NonzeroQM31Exact : ENNReal))⁻¹
      exact (ENNReal.mul_inv
        (a := (Fintype.card VariableGammaCompleteSkeleton : ENNReal))
        (b := (Fintype.card NonzeroQM31Exact : ENNReal))
        (Or.inl (Nat.cast_ne_zero.mpr
          (Fintype.card_ne_zero :
            Fintype.card VariableGammaCompleteSkeleton ≠ 0)))
        (Or.inl (ENNReal.natCast_ne_top
          (Fintype.card VariableGammaCompleteSkeleton)))).symm
    · intro value valueNe
      rw [if_neg]
      intro equal
      exact valueNe (congrArg Prod.snd equal).symm
  · intro skeleton skeletonNe
    have mappedZero :
        variablePrefixFixedSkeletonValueLaw skeleton pair = 0 := by
      unfold variablePrefixFixedSkeletonValueLaw
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro value
      rw [if_neg]
      intro equal
      exact skeletonNe (congrArg Prod.fst equal).symm
    rw [mappedZero, mul_zero]

/-- Uniform successful routed tapes become exactly the independent
skeleton/nonzero-value law under the operational factorization. -/
theorem routedSuccessfulGammaFactorization_law :
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).map
        routedSuccessfulGammaFactorization =
      variablePrefixSkeletonValueJointLaw := by
  calc
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).map
        routedSuccessfulGammaFactorization =
      PMF.uniformOfFintype
        (VariableGammaCompleteSkeleton × NonzeroQM31Exact) :=
      AspisV5RankOneOpeningHiding.uniform_map_equiv
        routedSuccessfulGammaFactorization
    _ = variablePrefixSkeletonValueJointLaw :=
      variablePrefixSkeletonValueJointLaw_eq_uniform.symm

/-- A challenge target chosen from the complete nuisance skeleton. -/
def variablePrefixSkeletonDependentGammaEvent
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact) :
    Set (VariableGammaCompleteSkeleton × NonzeroQM31Exact) :=
  {pair | pair.2.1 ∈ target pair.1}

def variablePrefixSkeletonGammaEventSlice
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) : Set NonzeroQM31Exact :=
  {value | value.1 ∈ target skeleton}

def routedSkeletonDependentGammaEvent
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact) :
    Set RoutedSuccessfulGammaTape :=
  routedSuccessfulGammaFactorization ⁻¹'
    variablePrefixSkeletonDependentGammaEvent target

@[simp] theorem mem_routedSkeletonDependentGammaEvent
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (sample : RoutedSuccessfulGammaTape) :
    sample ∈ routedSkeletonDependentGammaEvent target ↔
      (routedSuccessfulGammaFactorization sample).2.1 ∈
        target (routedSuccessfulGammaFactorization sample).1 := by
  rfl

theorem variablePrefix_joint_event_probability_eq_weighted_slices
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact) :
    variablePrefixSkeletonValueJointLaw.toOuterMeasure
        (variablePrefixSkeletonDependentGammaEvent target) =
      ∑' skeleton : VariableGammaCompleteSkeleton,
        (PMF.uniformOfFintype VariableGammaCompleteSkeleton) skeleton *
          (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
            (variablePrefixSkeletonGammaEventSlice target skeleton) := by
  unfold variablePrefixSkeletonValueJointLaw
    variablePrefixFixedSkeletonValueLaw
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro skeleton
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem variablePrefix_successful_value_slice_probability_le
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) :
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (variablePrefixSkeletonGammaEventSlice target skeleton) ≤
      ((target skeleton).card : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  change (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
      (nonzeroTargetEvent (target skeleton)) ≤ _
  exact uniform_nonzero_target_probability_le (target skeleton)

/-- Exact dependent-family bound.  The target family is fixed with the whole
nuisance skeleton before the returned gamma coordinate is sampled. -/
theorem variablePrefix_skeleton_dependent_gamma_probability_le
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    variablePrefixSkeletonValueJointLaw.toOuterMeasure
        (variablePrefixSkeletonDependentGammaEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  rw [variablePrefix_joint_event_probability_eq_weighted_slices]
  calc
    (∑' skeleton : VariableGammaCompleteSkeleton,
        (PMF.uniformOfFintype VariableGammaCompleteSkeleton) skeleton *
          (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
            (variablePrefixSkeletonGammaEventSlice target skeleton)) ≤
        ∑' skeleton : VariableGammaCompleteSkeleton,
          (PMF.uniformOfFintype VariableGammaCompleteSkeleton) skeleton *
            ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      exact ENNReal.tsum_le_tsum fun skeleton => mul_le_mul_right
        ((variablePrefix_successful_value_slice_probability_le
          target skeleton).trans <| by
            gcongr
            exact_mod_cast targetCap skeleton)
        ((PMF.uniformOfFintype VariableGammaCompleteSkeleton) skeleton)
    _ = (∑' skeleton : VariableGammaCompleteSkeleton,
          (PMF.uniformOfFintype VariableGammaCompleteSkeleton) skeleton) *
          ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      exact ENNReal.tsum_mul_right
    _ = (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
      rw [PMF.tsum_coe, one_mul]

/-- The exact routed successful-tape version of the dependent-family bound. -/
theorem routed_skeleton_dependent_gamma_probability_le
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).toOuterMeasure
        (routedSkeletonDependentGammaEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).toOuterMeasure
        (routedSkeletonDependentGammaEvent target) =
      ((PMF.uniformOfFintype RoutedSuccessfulGammaTape).map
        routedSuccessfulGammaFactorization).toOuterMeasure
          (variablePrefixSkeletonDependentGammaEvent target) := by
            rw [PMF.toOuterMeasure_map_apply]
            rfl
    _ = variablePrefixSkeletonValueJointLaw.toOuterMeasure
          (variablePrefixSkeletonDependentGammaEvent target) := by
            rw [routedSuccessfulGammaFactorization_law]
    _ ≤ (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) :=
      variablePrefix_skeleton_dependent_gamma_probability_le
        target cap targetCap

/-! ## Restoration-aware K1.5 specialization

The selected response family below is an ordinary piece of pre-value data:
one total family is supplied for each complete variable-prefix nuisance
skeleton.  Its target is then bounded by the existing algebraic/root-counting
theorem. -/

structure VariablePrefixRestoredK15PreGammaProvider
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  point : VariableGammaCompleteSkeleton → Fin 10 → QM31Exact
  claims : VariableGammaCompleteSkeleton → Fin 3 → Fin 29 → QM31Exact
  selected : VariableGammaCompleteSkeleton →
    RestoredSelectedBranchProvider decoder words

noncomputable def variablePrefixRestoredK15GammaTarget
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words)
    (skeleton : VariableGammaCompleteSkeleton) : Finset QM31Exact :=
  acceptedRestoredPointConstrainedGammaSet decoder words
    (provider.point skeleton) (provider.claims skeleton)
    (restoredSelectedChainFamilyOfK13Provider
      (provider.selected skeleton))

noncomputable def variablePrefixRestoredK15ResidualGammaTarget
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words)
    (skeleton : VariableGammaCompleteSkeleton) : Finset QM31Exact := by
  classical
  exact (variablePrefixRestoredK15GammaTarget provider skeleton).filter
    fun _ =>
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder words
        (provider.point skeleton) (provider.claims skeleton)
        (restoredSelectedChainFamilyOfK13Provider
          (provider.selected skeleton))

def variablePrefixRestoredK15ResidualRoutedEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words) :
    Set RoutedSuccessfulGammaTape :=
  routedSkeletonDependentGammaEvent
    (variablePrefixRestoredK15ResidualGammaTarget provider)

theorem variablePrefix_restored_k15_residual_target_card_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words)
    (skeleton : VariableGammaCompleteSkeleton) :
    (variablePrefixRestoredK15ResidualGammaTarget provider skeleton).card ≤
      initialBatchChallengeCap := by
  classical
  by_cases restored : HasAcceptedRestoredPointCompatibleK14 decoder words
      (provider.point skeleton) (provider.claims skeleton)
      (restoredSelectedChainFamilyOfK13Provider
        (provider.selected skeleton))
  · have cardZero :
        (variablePrefixRestoredK15ResidualGammaTarget
          provider skeleton).card = 0 := by
      rw [variablePrefixRestoredK15ResidualGammaTarget, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro gamma _member noRestored
      exact noRestored restored
    rw [cardZero]
    exact Nat.zero_le initialBatchChallengeCap
  · exact
      (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (no_accepted_restored_point_compatible_k14_card_le decoder published
          words (provider.point skeleton) (provider.claims skeleton)
          (restoredSelectedChainFamilyOfK13Provider
            (provider.selected skeleton)) restored)

/-- Exact raw residual-gamma bound for the genuine variable-prefix successful
sampler.  The published K1.5 numerator is unchanged and no grinding factor is
divided out. -/
theorem variablePrefix_restored_k15_residual_routed_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words) :
    (PMF.uniformOfFintype RoutedSuccessfulGammaTape).toOuterMeasure
        (variablePrefixRestoredK15ResidualRoutedEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply routed_skeleton_dependent_gamma_probability_le
  intro skeleton
  exact variablePrefix_restored_k15_residual_target_card_le
    published provider skeleton

end

#print axioms variablePrefixSkeletonValueJointLaw_eq_uniform
#print axioms routedSuccessfulGammaFactorization_law
#print axioms variablePrefix_joint_event_probability_eq_weighted_slices
#print axioms variablePrefix_skeleton_dependent_gamma_probability_le
#print axioms routed_skeleton_dependent_gamma_probability_le
#print axioms variablePrefix_restored_k15_residual_target_card_le
#print axioms variablePrefix_restored_k15_residual_routed_probability_le

end AspisK1.V7Tag73VariablePrefixGammaProbability
