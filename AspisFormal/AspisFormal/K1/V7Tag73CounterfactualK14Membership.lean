import AspisFormal.K1.V7Tag73CounterfactualK13Provider
import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction

/-!
# Deterministic counterfactual K1.4 membership

This lightweight module proves the literal inclusion which precedes the
complete-duplex probability theorem.  It is kept separate from measure theory
so dependent parser data is normalized before the event wrapper is unfolded.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CounterfactualK14Membership

open AspisK1.V7Tag73CounterfactualK13Provider
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

noncomputable section

set_option linter.constructorNameAsVariable false in
/-- One literal parsed decomposition failure belongs to the restored
width-29 bad set selected by the same complete-duplex future-free execution.
No probability premise occurs in this theorem. -/
theorem parsed_k14_failure_mem_restored_counterfactual_target
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
    (successfulDuplexNonzeroFactorization sample).2.1 ∈
      (let family := restoredSelectedChainFamilyOfK13Provider
        (counterfactualK13Provider oracle
          (successfulDuplexNonzeroFactorization sample).1)
      width29GoodChallenges decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (width29BadStrategy decoder.initialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
          (extractedWidth29InitialWords words)
          (restoredWidth29Strategy decoder
            (extractedWidth29InitialWords words) family.response))) := by
  classical
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


#print axioms parsed_k14_failure_mem_restored_counterfactual_target

end AspisK1.V7Tag73CounterfactualK14Membership
