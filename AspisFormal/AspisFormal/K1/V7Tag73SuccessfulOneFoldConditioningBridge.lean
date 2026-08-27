import AspisFormal.K1.V7Tag73CausalOneFoldProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Compiler-tape conditioning for causal Tag-73 one-fold extraction

The causal one-fold theorem isolates the returned ordinary QM31 alpha from
all rejection-path and duplex-advance nuisance data.  This module transports
that successful-sampler bound to the exact compiler fresh-answer tape, while
allowing every residual coordinate and hidden prover tape to select a
different complete pre-alpha response strategy.

Only a coordinate equivalence and deterministic source-event inclusion remain
for the production bridge.  No independence premise or work normalization is
used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SuccessfulOneFoldConditioningBridge

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Transport a residual-dependent causal one-fold event from the successful
ordinary sampler subtype to one complete uniform fresh-answer tape. -/
theorem uniform_tape_dependent_onefold_event_probability_le
    {F Tape Total Residual : Type}
    [Field F] [Algebra F QM31Exact]
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (context : Residual → Tag73CompleteOrdinarySamplerSkeleton →
      CausalOneFoldSamplerContext F)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual =>
        successfulCoordinates ⁻¹'
          duplexOrdinaryDependentEvent
            (causalOneFoldSamplerTarget (context residual)))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_tape_dependent_successful_event_probability_le success
    coordinates successfulCoordinates
    (fun residual => duplexOrdinaryDependentEvent
      (causalOneFoldSamplerTarget (context residual)))
    ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal))
  · intro residual
    exact causal_oneFold_duplex_alpha_probability_le (context residual)
  · exact covered

/-- Average the fixed-hidden one-fold conditioning bridge over the exact
compiler's arbitrary hidden-tape law. -/
theorem exact_compiler_dependent_onefold_event_probability_le
    {F HiddenTape Total Residual : Type}
    [Field F] [Algebra F QM31Exact]
    [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 freshExposures ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexOrdinaryAttempt)
    (context : HiddenTape → Residual →
      Tag73CompleteOrdinarySamplerSkeleton → CausalOneFoldSamplerContext F)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual =>
          successfulCoordinates ⁻¹'
            duplexOrdinaryDependentEvent
              (causalOneFoldSamplerTarget (context hidden residual)))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_onefold_event_probability_le success
    (coordinates hidden) successfulCoordinates (context hidden)
    (jointEventSlice event hidden) (covered hidden)

end

#print axioms uniform_tape_dependent_onefold_event_probability_le
#print axioms exact_compiler_dependent_onefold_event_probability_le

end AspisK1.V7Tag73SuccessfulOneFoldConditioningBridge
