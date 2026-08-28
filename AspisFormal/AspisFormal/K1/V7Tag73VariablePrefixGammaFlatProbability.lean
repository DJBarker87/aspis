import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting
import AspisFormal.K1.V7Tag73VariablePrefixGammaProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Exact probability on the chronological variable-prefix gamma tape

The routed probability theorem is transported through the exact equivalence
with the literal chronological production-success subtype.  Consequently the
successful law conditions only on the prefix read before the first nonzero
decode.  Unread output and advance suffix coordinates remain arbitrary.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73VariablePrefixGammaFlatProbability

open MeasureTheory
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

noncomputable instance : Nonempty SuccessfulGammaPrefixTape :=
  Nonempty.map successfulGammaPrefixFlatRoutingEquiv.symm inferInstance

/-- Uniform chronological successful tapes factor exactly into the complete
pre-gamma nuisance skeleton and one uniform nonzero QM31 value. -/
theorem successfulGammaPrefixFactorization_law :
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).map
        successfulGammaPrefixFactorization =
      variablePrefixSkeletonValueJointLaw := by
  calc
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).map
        successfulGammaPrefixFactorization =
      PMF.uniformOfFintype
        (VariableGammaCompleteSkeleton × NonzeroQM31Exact) :=
      AspisV5RankOneOpeningHiding.uniform_map_equiv
        successfulGammaPrefixFactorization
    _ = variablePrefixSkeletonValueJointLaw :=
      variablePrefixSkeletonValueJointLaw_eq_uniform.symm

def successfulGammaPrefixSkeletonDependentEvent
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact) :
    Set SuccessfulGammaPrefixTape :=
  successfulGammaPrefixFactorization ⁻¹'
    variablePrefixSkeletonDependentGammaEvent target

/-- Exact nuisance-dependent bad-challenge probability on the actual
variable-prefix success subtype. -/
theorem successful_gamma_prefix_skeleton_dependent_probability_le
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).toOuterMeasure
        (successfulGammaPrefixSkeletonDependentEvent target) ≤
      (cap : ENNReal) /
        ((AspisV5ComponentCQM31TowerExact.P ^ 4 - 1 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).toOuterMeasure
        (successfulGammaPrefixSkeletonDependentEvent target) =
      ((PMF.uniformOfFintype SuccessfulGammaPrefixTape).map
          successfulGammaPrefixFactorization).toOuterMeasure
        (variablePrefixSkeletonDependentGammaEvent target) := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl
    _ = variablePrefixSkeletonValueJointLaw.toOuterMeasure
        (variablePrefixSkeletonDependentGammaEvent target) := by
      rw [successfulGammaPrefixFactorization_law]
    _ ≤ _ := variablePrefix_skeleton_dependent_gamma_probability_le
      target cap targetCap

def variablePrefixRestoredK15ResidualFlatEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words) :
    Set SuccessfulGammaPrefixTape :=
  successfulGammaPrefixSkeletonDependentEvent
    (variablePrefixRestoredK15ResidualGammaTarget provider)

/-- The frozen restoration-aware root count on the chronological sampler law.
The raw numerator is unchanged. -/
theorem variablePrefix_restored_k15_residual_flat_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words) :
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).toOuterMeasure
        (variablePrefixRestoredK15ResidualFlatEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((AspisV5ComponentCQM31TowerExact.P ^ 4 - 1 : Nat) : ENNReal) := by
  apply successful_gamma_prefix_skeleton_dependent_probability_le
  intro skeleton
  exact variablePrefix_restored_k15_residual_target_card_le
    published provider skeleton

/-- The corresponding event on the raw total production tape.  Failed
sampler executions contribute no event mass; conditioning on genuine prefix
success can only increase its probability. -/
theorem variablePrefix_restored_k15_residual_total_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixRestoredK15PreGammaProvider decoder words) :
    (PMF.uniformOfFintype TotalGammaDuplexTape).toOuterMeasure
        (successfulSubtypeEvent GammaPrefixSucceeds
          (variablePrefixRestoredK15ResidualFlatEvent provider)) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact (uniform_successful_subtype_event_probability_le GammaPrefixSucceeds
      (variablePrefixRestoredK15ResidualFlatEvent provider)).trans
    (variablePrefix_restored_k15_residual_flat_probability_le
      published provider)

#print axioms successfulGammaPrefixFactorization_law
#print axioms successful_gamma_prefix_skeleton_dependent_probability_le
#print axioms variablePrefix_restored_k15_residual_flat_probability_le
#print axioms variablePrefix_restored_k15_residual_total_probability_le

end

end AspisK1.V7Tag73VariablePrefixGammaFlatProbability
