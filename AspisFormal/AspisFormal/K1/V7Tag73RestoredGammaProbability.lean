import AspisFormal.K1.V7Tag73EightRetrySamplerLaw
import AspisFormal.K1.V7Tag73RestoredPointCompatibleK14

/-!
# Exact restored-family gamma probability

This leaf combines the causal K1.4 finite-set theorem with the exact
three-attempt nonzero Tag-73 sampler law.  It does not divide the result by
grinding work: gamma is charged at its literal field-sampling probability.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73RestoredGammaProbability

open MeasureTheory
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- If restoration-wide K1.4 extraction fails, uniform nonzero gamma lands
in the complete accepted restored-family bad set with at most the published
list-decoding cardinality divided by the exact nonzero QM31 field size. -/
theorem no_k14_uniform_restored_gamma_probability_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (family : RestoredSelectedChainFamily decoder words)
    (failure : ¬ HasAcceptedRestoredPointCompatibleK14 decoder words point
      claims family) :
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (nonzeroTargetEvent
          (acceptedRestoredPointConstrainedGammaSet decoder words point claims
            family)) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  let target :=
    acceptedRestoredPointConstrainedGammaSet decoder words point claims family
  calc
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (nonzeroTargetEvent target) ≤
        (target.card : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) :=
      uniform_nonzero_target_probability_le target
    _ ≤ (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
      gcongr
      exact_mod_cast no_accepted_restored_point_compatible_k14_card_le
        decoder published words point claims family failure

/-- Concrete magnitude of the un-work-normalized restored-family gamma
event.  The exact coefficient is below `2^-75`. -/
theorem initial_batch_nonzero_qm31_ratio_le_two_pow_neg75 :
    (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) ≤
      1 / ((2 : ENNReal) ^ 75) := by
  rw [ENNReal.div_le_iff (by norm_num [P]) (by norm_num)]
  rw [mul_comm, one_div, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num [initialBatchChallengeCap, P]

theorem no_k14_uniform_restored_gamma_probability_le_two_pow_neg75
    (decoder : ExactDecoderInstantiation QM31Exact)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (claims : Fin 3 → Fin 29 → QM31Exact)
    (family : RestoredSelectedChainFamily decoder words)
    (failure : ¬ HasAcceptedRestoredPointCompatibleK14 decoder words point
      claims family) :
    (PMF.uniformOfFintype NonzeroQM31Exact).toOuterMeasure
        (nonzeroTargetEvent
          (acceptedRestoredPointConstrainedGammaSet decoder words point claims
            family)) ≤
      1 / ((2 : ENNReal) ^ 75) :=
  (no_k14_uniform_restored_gamma_probability_le decoder published words point
    claims family failure).trans
      initial_batch_nonzero_qm31_ratio_le_two_pow_neg75

end

#print axioms no_k14_uniform_restored_gamma_probability_le
#print axioms initial_batch_nonzero_qm31_ratio_le_two_pow_neg75
#print axioms no_k14_uniform_restored_gamma_probability_le_two_pow_neg75

end AspisK1.V7Tag73RestoredGammaProbability
