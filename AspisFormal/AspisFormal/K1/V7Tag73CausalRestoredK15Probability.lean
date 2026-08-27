import AspisFormal.K1.V7Tag73CompleteCausalGammaProbability
import AspisFormal.K1.V7Tag73CounterfactualK13Provider
import AspisFormal.K1.V7Tag73RestoredPointCompatibleK14

/-!
# Causal probability of the restoration-aware Tag-73 K1.5 residual

After point-compatible restored branches have been routed to extraction, the
remaining gamma-shaped K1.5 error is membership in one constrained width-29
set while no point-compatible restored certificate exists.

This file puts that residual on the complete deployed nonzero-gamma sample
space.  For each complete sampler nuisance skeleton, the point, serialized
point-claim table, and selected-chain provider are fixed before the returned
nonzero gamma coordinate is exposed.  They may conservatively depend on every
other raw sampler word and every independent duplex-advance digest.  The exact
factorization theorem then charges one published width-29 numerator and no
grinding normalization.

The membership equivalence is deterministic.  The source/restoration layer
only has to identify the actual pre-gamma point and claims and the actual
counterfactual selected-chain family at the sample's skeleton.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73CausalRestoredK15Probability

open MeasureTheory
open AspisK1.V7Tag73CompleteCausalGammaProbability
open AspisK1.V7Tag73CounterfactualK13Provider
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Complete pre-value data for the constrained restoration event.  The
fields are functions of the nuisance skeleton, never of the returned gamma
coordinate. -/
structure RestoredK15PreGammaProvider
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  point : Tag73CompleteSamplerSkeleton → Fin 10 → QM31Exact
  claims : Tag73CompleteSamplerSkeleton → Fin 3 → Fin 29 → QM31Exact
  selected : Tag73CompleteSamplerSkeleton →
    RestoredSelectedBranchProvider decoder words

/-- The one constrained gamma target fixed by a complete nuisance skeleton. -/
noncomputable def causalRestoredK15GammaTarget
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK15PreGammaProvider decoder words)
    (skeleton : Tag73CompleteSamplerSkeleton) : Finset QM31Exact :=
  acceptedRestoredPointConstrainedGammaSet decoder words
    (provider.point skeleton) (provider.claims skeleton)
    (restoredSelectedChainFamilyOfK13Provider
      (provider.selected skeleton))

/-- The exact deployed duplex event for the restoration-aware constrained
K1.5 branch. -/
def causalRestoredK15DuplexGammaEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK15PreGammaProvider decoder words) :
    Set SuccessfulTag73DuplexNonzeroAttempts :=
  duplexSkeletonDependentGammaEvent
    (causalRestoredK15GammaTarget provider)

@[simp] theorem mem_causalRestoredK15DuplexGammaEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK15PreGammaProvider decoder words)
    (sample : SuccessfulTag73DuplexNonzeroAttempts) :
    sample ∈ causalRestoredK15DuplexGammaEvent provider ↔
      (successfulDuplexNonzeroFactorization sample).2.1 ∈
        causalRestoredK15GammaTarget provider
          (successfulDuplexNonzeroFactorization sample).1 := by
  exact mem_duplexSkeletonDependentGammaEvent
    (causalRestoredK15GammaTarget provider) sample

/-- Every nuisance slice has the published width-29 cap once usable restored
K1.4 certificates have been routed out of the error event. -/
theorem causal_restored_k15_target_card_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK15PreGammaProvider decoder words)
    (noRestored : ∀ skeleton,
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder words
        (provider.point skeleton) (provider.claims skeleton)
        (restoredSelectedChainFamilyOfK13Provider
          (provider.selected skeleton)))
    (skeleton : Tag73CompleteSamplerSkeleton) :
    (causalRestoredK15GammaTarget provider skeleton).card ≤
      initialBatchChallengeCap := by
  exact no_accepted_restored_point_compatible_k14_card_le decoder published
    words (provider.point skeleton) (provider.claims skeleton)
    (restoredSelectedChainFamilyOfK13Provider
      (provider.selected skeleton)) (noRestored skeleton)

/-- Exact raw causal probability of the restoration-aware K1.5 constrained
event.  No work factor is divided out. -/
theorem causal_restored_k15_duplex_gamma_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK15PreGammaProvider decoder words)
    (noRestored : ∀ skeleton,
      ¬ HasAcceptedRestoredPointCompatibleK14 decoder words
        (provider.point skeleton) (provider.claims skeleton)
        (restoredSelectedChainFamilyOfK13Provider
          (provider.selected skeleton))) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
        (causalRestoredK15DuplexGammaEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply duplex_skeleton_dependent_gamma_probability_le
  intro skeleton
  exact causal_restored_k15_target_card_le published provider noRestored
    skeleton

end

#print axioms mem_causalRestoredK15DuplexGammaEvent
#print axioms causal_restored_k15_target_card_le
#print axioms causal_restored_k15_duplex_gamma_probability_le

end AspisK1.V7Tag73CausalRestoredK15Probability
