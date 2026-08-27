import AspisFormal.K1.V7Tag73CausalRestoredFamily

/-!
# Counterfactual Tag-73 K1.3 response provider

For a fixed hidden prover tape and fixed pre-gamma transcript, the
future-free machine is a deterministic function of the successful duplex
gamma sampler: both squeeze-output blocks and the independent transcript
advance digests.  The complete nuisance/value factorization therefore turns
that function into a response provider fixed before the returned gamma.

This file isolates the remaining operational source task in one narrow
record: run the future-free prover on a supplied raw stream and prove that a
returned parsed proof records the sampler's literal returned gamma.  No
acceptance, K1.3 success, K1.4 success, probability bound, witness, or
extraction conclusion is a field of that record.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CounterfactualK13Provider

open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73CausalRestoredFamily
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

@[simp] theorem transported_selected_branch_disclosedFinal
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {fromGamma toGamma : QM31Exact}
    (exact : fromGamma = toGamma)
    (branch : RestoredSelectedBranch decoder words fromGamma) :
    (exact ▸ branch).disclosedFinal = branch.disclosedFinal := by
  cases exact
  rfl

@[simp] theorem transported_selected_branch_schedule
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {fromGamma toGamma : QM31Exact}
    (exact : fromGamma = toGamma)
    (branch : RestoredSelectedBranch decoder words fromGamma) :
    (exact ▸ branch).schedule = branch.schedule := by
  cases exact
  rfl

/-- The exact duplex sampler execution reconstructed from complete nuisance and
one returned nonzero gamma. -/
def duplexForSkeletonValue
    (skeleton : Tag73CompleteSamplerSkeleton)
    (value : NonzeroQM31Exact) : SuccessfulTag73DuplexNonzeroAttempts :=
  successfulDuplexNonzeroFactorization.symm (skeleton, value)

@[simp] theorem duplexForSkeletonValue_factorization
    (sample : SuccessfulTag73DuplexNonzeroAttempts) :
    duplexForSkeletonValue (successfulDuplexNonzeroFactorization sample).1
        (successfulDuplexNonzeroFactorization sample).2 = sample := by
  exact successfulDuplexNonzeroFactorization.symm_apply_apply sample

@[simp] theorem duplexForSkeletonValue_returns_value
    (skeleton : Tag73CompleteSamplerSkeleton)
    (value : NonzeroQM31Exact) :
    successfulDuplexNonzeroValue (duplexForSkeletonValue skeleton value) = value := by
  have factorExact := successfulDuplexNonzeroFactorization.apply_symm_apply
    (skeleton, value)
  rw [← successfulDuplexNonzeroFactorization_value]
  exact congrArg Prod.snd factorExact

/-- Minimal future-free execution boundary for one fixed hidden state.  The
defaults are pre-gamma data used only to totalize unavailable branches. -/
structure CounterfactualParsedK13Oracle
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  defaultResponse : InitialMessage QM31Exact
  defaultDisclosedFinal : FinalMessage QM31Exact
  defaultSchedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule
  defaultSelected : ExactCandidatePair
  proof? : SuccessfulTag73DuplexNonzeroAttempts → Option Tag73K12ParsedProof
  proofGammaExact : ∀ sample proof,
    proof? sample = some proof →
      proof.gamma = (successfulDuplexNonzeroValue sample).1

/-- Classify the counterfactual parsed proof for a single nonzero gamma.  A
machine rejection or a typed K1.3 error makes that challenge unavailable;
neither can manufacture a selected branch. -/
noncomputable def counterfactualParsedK13Branch?
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (skeleton : Tag73CompleteSamplerSkeleton)
    (gamma : QM31Exact) : Option (RestoredSelectedBranch decoder words gamma) := by
  classical
  by_cases nonzero : gamma ≠ 0
  · let value : NonzeroQM31Exact := ⟨gamma, nonzero⟩
    let sample := duplexForSkeletonValue skeleton value
    match proofEq : oracle.proof? sample with
    | none => exact none
    | some proof =>
        have gammaExact : proof.gamma = gamma := by
          calc
            proof.gamma = (successfulDuplexNonzeroValue sample).1 :=
              oracle.proofGammaExact sample proof proofEq
            _ = gamma := by
              rw [show sample = duplexForSkeletonValue skeleton value by rfl,
                duplexForSkeletonValue_returns_value]
        match classifyParsedK13 decoder words proof with
        | .inr _error => exact none
        | .inl k13 =>
            exact some (gammaExact ▸ restoredSelectedBranchOfParsedK13 k13)
  · exact none

/-- The deterministic raw-stream oracle constructs the exact provider shape
consumed by the causal K1.4 probability theorem. -/
noncomputable def counterfactualK13Provider
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (skeleton : Tag73CompleteSamplerSkeleton) :
    RestoredSelectedBranchProvider decoder words where
  defaultResponse := oracle.defaultResponse
  defaultDisclosedFinal := oracle.defaultDisclosedFinal
  defaultSchedule := oracle.defaultSchedule
  defaultSelected := oracle.defaultSelected
  branch := counterfactualParsedK13Branch? oracle skeleton

@[simp] theorem counterfactual_provider_zero_unavailable
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (skeleton : Tag73CompleteSamplerSkeleton) :
    (counterfactualK13Provider oracle skeleton).branch 0 = none := by
  simp [counterfactualK13Provider, counterfactualParsedK13Branch?]

/-- The counterfactual provider contains the actually executed branch whenever
the future-free machine returned that parsed proof and its exact K1.3
classifier succeeded.  This is the deterministic identity needed before any
probability argument is applied. -/
theorem actual_duplex_counterfactual_branch_source_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (sample : SuccessfulTag73DuplexNonzeroAttempts)
    (proof : Tag73K12ParsedProof)
    (proofExact : oracle.proof? sample = some proof)
    (k13 : ParsedK13Certificate decoder words proof)
    (k13Exact : classifyParsedK13 decoder words proof = .inl k13) :
    ∃ branch,
      (counterfactualK13Provider oracle
          (successfulDuplexNonzeroFactorization sample).1).branch
          (successfulDuplexNonzeroValue sample).1 = some branch ∧
        branch.disclosedFinal = proof.disclosedFinal ∧
        branch.schedule = proof.schedule := by
  classical
  have gammaNonzero : (successfulDuplexNonzeroValue sample).1 ≠ 0 :=
    (successfulDuplexNonzeroValue sample).2
  have sampleExact :
      duplexForSkeletonValue (successfulDuplexNonzeroFactorization sample).1
        (successfulDuplexNonzeroValue sample) = sample := by
    rw [← successfulDuplexNonzeroFactorization_value]
    exact duplexForSkeletonValue_factorization sample
  unfold counterfactualK13Provider
  simp only
  unfold counterfactualParsedK13Branch?
  split
  · rename_i h
    have reconstructed :
        duplexForSkeletonValue (successfulDuplexNonzeroFactorization sample).1
            ⟨(successfulDuplexNonzeroValue sample).1, h⟩ = sample := by
      convert sampleExact using 1
    dsimp only
    have proofExact' :
        oracle.proof?
            (duplexForSkeletonValue (successfulDuplexNonzeroFactorization sample).1
              ⟨(successfulDuplexNonzeroValue sample).1, h⟩) = some proof := by
      simpa only [reconstructed] using proofExact
    split
    · rename_i noneExact
      rw [proofExact'] at noneExact
      cases noneExact
    · rename_i returned returnedExact
      have returnedEq : returned = proof :=
        Option.some.inj (returnedExact.symm.trans proofExact')
      subst returned
      split
      · rename_i error classifierExact
        rw [k13Exact] at classifierExact
        cases classifierExact
      · rename_i returnedK13 classifierExact
        have k13Eq : returnedK13 = k13 :=
          Sum.inl.inj (classifierExact.symm.trans k13Exact)
        subst returnedK13
        refine ⟨_, rfl, ?_, ?_⟩
        · simp [restoredSelectedBranchOfParsedK13]
        · simp [restoredSelectedBranchOfParsedK13]
  · rename_i h
    exact (h gammaNonzero).elim

/-- Forgetting the exact branch identity yields the availability fact used by
restoration-wide selected-chain families. -/
theorem actual_duplex_counterfactual_branch_available
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (sample : SuccessfulTag73DuplexNonzeroAttempts)
    (proof : Tag73K12ParsedProof)
    (proofExact : oracle.proof? sample = some proof)
    (k13 : ParsedK13Certificate decoder words proof)
    (k13Exact : classifyParsedK13 decoder words proof = .inl k13) :
    selectedProviderAvailable
        (counterfactualK13Provider oracle
          (successfulDuplexNonzeroFactorization sample).1)
        (successfulDuplexNonzeroValue sample).1 := by
  unfold selectedProviderAvailable
  obtain ⟨branch, branchExact, _finalExact, _scheduleExact⟩ :=
    actual_duplex_counterfactual_branch_source_exact oracle sample proof
    proofExact k13 k13Exact
  simp [branchExact]

/-- The selected response exposed by the counterfactual family is exactly the
canonical selected chain of the literal parsed proof.  The statement hides
the dependent transport used internally by the restored branch. -/
theorem actual_duplex_counterfactual_selected_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (sample : SuccessfulTag73DuplexNonzeroAttempts)
    (proof : Tag73K12ParsedProof)
    (proofExact : oracle.proof? sample = some proof)
    (k13 : ParsedK13Certificate decoder words proof)
    (k13Exact : classifyParsedK13 decoder words proof = .inl k13) :
    selectCandidateChain
        (decoder.decodeBoth
          (parsedK13Transcript words proof).initial
          (foldedReceived proof.schedule
            (parsedK13Transcript words proof)))
        proof.schedule proof.disclosedFinal =
      some ((restoredSelectedChainFamilyOfK13Provider
        (counterfactualK13Provider oracle
          (successfulDuplexNonzeroFactorization sample).1)).selected
            (successfulDuplexNonzeroValue sample).1) := by
  let provider := counterfactualK13Provider oracle
    (successfulDuplexNonzeroFactorization sample).1
  let gamma := (successfulDuplexNonzeroValue sample).1
  obtain ⟨branch, branchExact, finalExact, scheduleExact⟩ :=
    actual_duplex_counterfactual_branch_source_exact oracle sample proof
      proofExact k13 k13Exact
  have familyFacts := k13_family_selected_of_branch provider gamma branch
    branchExact
  have branchSelectedExact := branch.selectedExact
  have gammaExact : proof.gamma = gamma :=
    oracle.proofGammaExact sample proof proofExact
  dsimp [gamma, provider] at gammaExact familyFacts
  calc
    selectCandidateChain
        (decoder.decodeBoth
          (parsedK13Transcript words proof).initial
          (foldedReceived proof.schedule
            (parsedK13Transcript words proof)))
        proof.schedule proof.disclosedFinal = some branch.selected := by
      simpa [parsedK13Transcript, gammaExact, finalExact, scheduleExact] using
        branchSelectedExact
    _ = some ((restoredSelectedChainFamilyOfK13Provider provider).selected
        gamma) := by rw [familyFacts.2]

end

#print axioms duplexForSkeletonValue_factorization
#print axioms duplexForSkeletonValue_returns_value
#print axioms counterfactualParsedK13Branch?
#print axioms counterfactualK13Provider
#print axioms counterfactual_provider_zero_unavailable
#print axioms actual_duplex_counterfactual_branch_source_exact
#print axioms actual_duplex_counterfactual_branch_available
#print axioms actual_duplex_counterfactual_selected_exact

end AspisK1.V7Tag73CounterfactualK13Provider
