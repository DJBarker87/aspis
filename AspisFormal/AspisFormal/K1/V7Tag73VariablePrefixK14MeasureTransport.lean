import AspisFormal.K1.V7Tag73VariablePrefixK14Probability
import AspisFormal.K1.V7Tag73HiddenTapeAveraging

/-!
# Low-memory variable-prefix K1.4 measure transport

This leaf caches the generic conditioning and hidden-tape averaging argument.
The production-law bridge then instantiates only a finite target and its exact
cardinality bound, without elaborating the complete verifier configuration
inside the probability proof.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73VariablePrefixK14MeasureTransport

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Average a residual-dependent variable-prefix bad-gamma target over an
arbitrary hidden-tape distribution. -/
theorem hidden_tape_variable_prefix_k14_event_probability_le
    {HiddenTape Residual : Type}
    [Fintype HiddenTape] [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 freshExposures ≃
        Residual × TotalGammaDuplexTape)
    (target : HiddenTape → Residual →
      VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤ cap)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
          successfulGammaPrefixSkeletonDependentEventK14
            (target hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  apply uniform_tape_dependent_successful_event_probability_le
    GammaPrefixSucceeds (coordinates hidden)
    (Equiv.refl SuccessfulGammaPrefixTape)
    (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
      (target hidden residual))
    ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))
  · intro residual
    exact successful_gamma_prefix_skeleton_dependent_probability_le_k14
      (target hidden residual) cap (targetCap hidden residual)
  · exact covered hidden

#print axioms hidden_tape_variable_prefix_k14_event_probability_le

end

end AspisK1.V7Tag73VariablePrefixK14MeasureTransport
