import AspisFormal.K1.V7Tag73CausalRestoredK15Probability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Compiler-tape conditioning for restoration-aware Tag-73 K1.5

The causal K1.5 theorem is stated on the successful deployed nonzero-gamma
sampler.  The exact compiler samples one larger uniform fresh-answer tape and
may abort when that sampler fails.  This module transports the causal bound
back to the unconditioned compiler tape, while allowing every non-gamma tape
coordinate and the hidden prover tape to choose a different pre-gamma context.

Only an exact coordinate equivalence and deterministic event inclusion remain
for the source bridge.  There is no independence or probability premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73SuccessfulRestoredK15ConditioningBridge

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalRestoredK15Probability
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Transport a residual-dependent causal K1.5 event from the successful
sampler subtype back to one complete uniform fresh-answer tape. -/
theorem uniform_tape_dependent_restored_k15_event_probability_le
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates :
      {a : Total // success a} ≃ SuccessfulTag73DuplexNonzeroAttempts)
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : Residual → AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (provider : ∀ residual,
      RestoredK15PreGammaProvider decoder (words residual))
    (noRestored : ∀ residual skeleton,
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder (words residual)
        ((provider residual).point skeleton)
        ((provider residual).claims skeleton)
        (restoredSelectedChainFamilyOfK13Provider
          ((provider residual).selected skeleton)))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual =>
        successfulCoordinates ⁻¹'
          causalRestoredK15DuplexGammaEvent (provider residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply uniform_tape_dependent_successful_event_probability_le success
    coordinates successfulCoordinates
    (fun residual => causalRestoredK15DuplexGammaEvent (provider residual))
    ((initialBatchChallengeCap : ENNReal) /
      ((P ^ 4 - 1 : Nat) : ENNReal))
  · intro residual
    exact causal_restored_k15_duplex_gamma_probability_le published
      (provider residual) (noRestored residual)
  · exact covered

/-- Average the exact fixed-hidden conditioning bridge over the compiler's
arbitrary hidden-tape law. -/
theorem exact_compiler_dependent_restored_k15_event_probability_le
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
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : HiddenTape → Residual →
      AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (provider : ∀ hidden residual,
      RestoredK15PreGammaProvider decoder (words hidden residual))
    (noRestored : ∀ hidden residual skeleton,
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder (words hidden residual)
        ((provider hidden residual).point skeleton)
        ((provider hidden residual).claims skeleton)
        (restoredSelectedChainFamilyOfK13Provider
          ((provider hidden residual).selected skeleton)))
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual =>
          successfulCoordinates ⁻¹'
            causalRestoredK15DuplexGammaEvent
              (provider hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_restored_k15_event_probability_le success
    (coordinates hidden) successfulCoordinates published (words hidden)
    (provider hidden) (noRestored hidden) (jointEventSlice event hidden)
    (covered hidden)

end

#print axioms uniform_tape_dependent_restored_k15_event_probability_le
#print axioms exact_compiler_dependent_restored_k15_event_probability_le

end AspisK1.V7Tag73SuccessfulRestoredK15ConditioningBridge
