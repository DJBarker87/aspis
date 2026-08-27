import AspisFormal.K1.V7Tag73CompleteCausalGammaProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Generic compiler-tape conditioning for a successful nonzero Tag-73 sampler

This is the nonzero analogue of the existing ordinary-challenge conditioning
theorem.  It retains the complete rejection and duplex-advance nuisance, while
allowing every residual compiler coordinate and hidden prover tape to select a
different pre-challenge target set with one uniform cardinality cap.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SuccessfulNonzeroConditioningBridge

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalGammaProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Transport a residual-dependent causal nonzero challenge event from the
successful sampler subtype to one complete uniform fresh-answer tape. -/
theorem uniform_tape_dependent_nonzero_event_probability_le
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexNonzeroAttempts)
    (target : Residual → Tag73CompleteSamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ residual skeleton, (target residual skeleton).card ≤ cap)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual =>
        successfulCoordinates ⁻¹'
          duplexSkeletonDependentGammaEvent (target residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply uniform_tape_dependent_successful_event_probability_le success
    coordinates successfulCoordinates
    (fun residual => duplexSkeletonDependentGammaEvent (target residual))
    ((cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal))
  · intro residual
    exact duplex_skeleton_dependent_gamma_probability_le
      (target residual) cap (targetCap residual)
  · exact covered

/-- Average the fixed-hidden nonzero conditioning theorem over the compiler's
arbitrary hidden-tape law. -/
theorem exact_compiler_dependent_nonzero_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 freshExposures ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexNonzeroAttempts)
    (target : HiddenTape → Residual →
      Tag73CompleteSamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤ cap)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual =>
          successfulCoordinates ⁻¹'
            duplexSkeletonDependentGammaEvent
              (target hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (cap : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_nonzero_event_probability_le success
    (coordinates hidden) successfulCoordinates (target hidden) cap
    (targetCap hidden) (jointEventSlice event hidden) (covered hidden)

end


#print axioms uniform_tape_dependent_nonzero_event_probability_le
#print axioms exact_compiler_dependent_nonzero_event_probability_le

end AspisK1.V7Tag73SuccessfulNonzeroConditioningBridge
