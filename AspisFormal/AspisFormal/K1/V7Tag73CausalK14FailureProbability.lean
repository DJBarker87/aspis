import AspisFormal.K1.V7Tag73CounterfactualK13Provider
import AspisFormal.K1.V7Tag73CounterfactualK14Membership
import AspisFormal.K1.V7Tag73CompleteCausalGammaProbability
import AspisFormal.K1.V7ExactCorrelatedAgreementInitial

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
open AspisK1.V7ExactCorrelatedAgreementTerminal
open AspisK1.V7Tag73CompleteCausalGammaProbability
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73CounterfactualK13Provider
open AspisK1.V7Tag73CounterfactualK14Membership
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
noncomputable abbrev causalK14FailureGammaTarget
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

abbrev causalK14FailureDuplexGammaEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words) :
    Set SuccessfulTag73DuplexNonzeroAttempts :=
  duplexSkeletonDependentGammaEvent (causalK14FailureGammaTarget provider)

@[simp] theorem mem_causalK14FailureDuplexGammaEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words)
    (sample : SuccessfulTag73DuplexNonzeroAttempts) :
    sample ∈ causalK14FailureDuplexGammaEvent provider ↔
      (successfulDuplexNonzeroFactorization sample).2.1 ∈
        causalK14FailureGammaTarget provider
          (successfulDuplexNonzeroFactorization sample).1 := by
  exact mem_duplexSkeletonDependentGammaEvent
    (causalK14FailureGammaTarget provider) sample

/-- Every causal K1.4 target has the internally proved degree-28 cardinality
cap. -/
theorem causal_k14_failure_target_card_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words)
    (skeleton : Tag73CompleteSamplerSkeleton) :
    (causalK14FailureGammaTarget provider skeleton).card ≤
      initialBatchChallengeCap := by
  have published : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder := by
    rw [initialEncoderExact]
    exact exactV7InitialPublishedWidth29CurveDecodability
  exact restored_width29_bad_challenges_card_le decoder published words
    (restoredSelectedChainFamilyOfK13Provider
      (provider skeleton)).response

/-- Exact raw-sampler probability bound.  The sampler nuisance may determine
the whole response strategy, but the returned nonzero gamma remains the sole
uniform second factor. -/
theorem causal_k14_failure_duplex_gamma_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : Tag73CompleteSamplerSkeleton →
      RestoredSelectedBranchProvider decoder words) :
    (PMF.uniformOfFintype SuccessfulTag73DuplexNonzeroAttempts).toOuterMeasure
        (causalK14FailureDuplexGammaEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply duplex_skeleton_dependent_gamma_probability_le
  intro skeleton
  exact causal_k14_failure_target_card_le initialEncoderExact provider skeleton

set_option maxHeartbeats 1000000 in
-- Normalize the complete dependent parser/provider event without changing it.
set_option linter.constructorNameAsVariable false in
/-- The dependent parser/provider transports require additional elaboration
heartbeats to normalize the complete sampler equivalence and event preimage;
the proof itself is a short deterministic inclusion.  A
literal parsed K1.4 decomposition failure is a member of the complete
duplex causal event generated by the same future-free execution oracle.  This
is the deterministic inclusion needed before applying the probability bound;
it neither assumes nor concludes a probability statement. -/
theorem parsed_k14_failure_mem_counterfactual_duplex_event
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (sample : SuccessfulTag73DuplexNonzeroAttempts)
    (proof : Tag73K12ParsedProof)
    (proofExact : oracle.proof? sample = some proof)
    (k13 : ParsedK13Certificate decoder words proof)
    (k13Exact : classifyParsedK13 decoder words proof = .inl k13)
    (failure : Width29DecompositionFailure decoder words proof.gamma
      proof.disclosedFinal proof.schedule) :
    sample ∈ causalK14FailureDuplexGammaEvent
      (fun skeleton => counterfactualK13Provider oracle skeleton) := by
  classical
  rw [mem_causalK14FailureDuplexGammaEvent]
  unfold causalK14FailureGammaTarget
  rw [successfulDuplexNonzeroFactorization_value]
  let gamma := (successfulDuplexNonzeroValue sample).1
  let family := restoredSelectedChainFamilyOfK13Provider
    (counterfactualK13Provider oracle
      (successfulDuplexNonzeroFactorization sample).1)
  have gammaExact : proof.gamma = gamma :=
    oracle.proofGammaExact sample proof proofExact
  have gammaNonzero : proof.gamma ≠ 0 := by
    rw [gammaExact]
    exact (successfulDuplexNonzeroValue sample).2
  let selected := Classical.choose failure
  have selectedFacts := Classical.choose_spec failure
  have selectedExact := selectedFacts.1
  have noMatching := selectedFacts.2
  have familySelectedExact :=
    actual_duplex_counterfactual_selected_exact oracle sample proof proofExact
      k13 k13Exact
  have familySelected : family.selected gamma = selected :=
    Option.some.inj (familySelectedExact.symm.trans selectedExact)
  have familyAvailable : family.available gamma :=
    actual_duplex_counterfactual_branch_available oracle sample proof proofExact
      k13 k13Exact
  have responseAt : family.response gamma = selected.1 := by
    calc
      family.response gamma = (family.selected gamma).1 :=
        family.responseAt gamma familyAvailable
      _ = selected.1 := by rw [familySelected]
  have fixedMember : proof.gamma ∈
      width29GoodChallenges decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (width29BadStrategy decoder.initialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
          (extractedWidth29InitialWords words)
          (selectedCandidateStrategy decoder
            (extractedWidth29InitialWords words) selected)) := by
    rw [mem_width29BadStrategy_good_iff]
    refine ⟨gammaNonzero, ?_, noMatching⟩
    exact selected_chain_yields_valid_width29_response decoder words proof.gamma
      proof.disclosedFinal proof.schedule selected selectedExact
  rw [gammaExact] at fixedMember
  rw [mem_width29BadStrategy_good_iff] at fixedMember ⊢
  have supportEq := restoredWidth29Strategy_support_eq_selected decoder
    (extractedWidth29InitialWords words) selected family.response gamma responseAt
  have restoredValid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response) gamma := by
    constructor
    · rw [supportEq]
      exact fixedMember.2.1.1
    · intro index member
      rw [supportEq] at member
      have fixedAgreement := fixedMember.2.1.2 index member
      rw [restoredWidth29Strategy_candidate, responseAt]
      rw [selectedCandidateStrategy_candidate] at fixedAgreement
      exact fixedAgreement
  have restoredNoMatching : ¬ HasMatchingWidth29Decomposition
      decoder.initialEncoder (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response) gamma := by
    intro restoredMatching
    apply fixedMember.2.2
    rcases restoredMatching with ⟨components, shared, onCurve⟩
    refine ⟨components, ?_, ?_⟩
    · rw [← supportEq]
      exact shared
    · unfold Width29CandidateOnCurve at onCurve ⊢
      rw [restoredWidth29Strategy_candidate, responseAt] at onCurve
      rw [selectedCandidateStrategy_candidate]
      exact onCurve
  exact ⟨fixedMember.1, restoredValid, restoredNoMatching⟩

end

#print axioms causal_k14_failure_target_card_le
#print axioms causal_k14_failure_duplex_gamma_probability_le
#print axioms parsed_k14_failure_mem_counterfactual_duplex_event

end AspisK1.V7Tag73CausalK14FailureProbability
