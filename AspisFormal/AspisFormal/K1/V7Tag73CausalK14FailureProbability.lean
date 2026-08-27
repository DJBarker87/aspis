import AspisFormal.K1.V7Tag73CounterfactualK13Provider
import AspisFormal.K1.V7Tag73CompleteCausalGammaProbability

/-!
# Causal probability bound for the exact Tag-73 K1.4 failure

The K1.4 width-29 decomposition failure is a plain correlated-decoding bad
response.  It does not require the later K1.5 point-claim constraints.  For
each complete gamma-sampler nuisance skeleton, the future-free K1.3 provider
defines one restoration-wide response strategy before the returned nonzero
gamma is supplied.  The published degree-28 theorem therefore bounds the
entire bad-response set directly, with no decoder-list union and no
post-gamma choice.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73CausalK14FailureProbability

open MeasureTheory
open AspisK1.V7Tag73CompleteCausalGammaProbability
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73CounterfactualK13Provider
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- One pre-gamma provider induces exactly one restoration-wide width-29 bad
set.  Defaults on unavailable branches may enlarge this set, which is safe:
the published theorem caps the complete strategy without any availability or
list-size factor. -/
noncomputable def causalK14FailureGammaTarget
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words)
    (skeleton : Tag73CompleteSamplerSkeleton) : Finset QM31Exact :=
  let family := restoredSelectedChainFamilyOfK13Provider (provider skeleton)
  width29GoodChallenges decoder.initialEncoder
    AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
    (extractedWidth29InitialWords words)
    (width29BadStrategy decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response))

def causalK14FailureDuplexGammaEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words) :
    Set SuccessfulTag73DuplexNonzeroAttempts :=
  duplexSkeletonDependentGammaEvent (causalK14FailureGammaTarget provider)

/-- Every causal K1.4 target has the single published degree-28 cardinality
cap. -/
theorem causal_k14_failure_target_card_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words)
    (skeleton : Tag73CompleteSamplerSkeleton) :
    (causalK14FailureGammaTarget provider skeleton).card ≤
      initialBatchChallengeCap := by
  exact restored_width29_bad_challenges_card_le decoder published words
    (restoredSelectedChainFamilyOfK13Provider
      (provider skeleton)).response

/-- Exact raw-sampler probability bound.  The sampler nuisance may determine
the whole response strategy, but the returned nonzero gamma remains the sole
uniform second factor. -/
theorem causal_k14_failure_duplex_gamma_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
        (causalK14FailureDuplexGammaEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply duplex_skeleton_dependent_gamma_probability_le
  intro skeleton
  exact causal_k14_failure_target_card_le published provider skeleton

end

#print axioms causal_k14_failure_target_card_le
#print axioms causal_k14_failure_duplex_gamma_probability_le

end AspisK1.V7Tag73CausalK14FailureProbability
