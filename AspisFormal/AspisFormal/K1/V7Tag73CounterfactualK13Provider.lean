import AspisFormal.K1.V7Tag73CausalRestoredFamily

/-!
# Counterfactual Tag-73 K1.3 response provider

For a fixed hidden prover tape and fixed pre-gamma transcript, the
future-free machine is a deterministic function of the successful raw gamma
sampler stream.  The complete nuisance/value factorization therefore turns
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

/-- The exact raw sampler execution reconstructed from complete nuisance and
one returned nonzero gamma. -/
def rawForSkeletonValue
    (skeleton : Tag73OuterSamplerSkeleton)
    (value : NonzeroQM31Exact) : SuccessfulTag73RawNonzeroAttempts :=
  successfulRawNonzeroFactorization.symm (skeleton, value)

@[simp] theorem rawForSkeletonValue_factorization
    (raw : SuccessfulTag73RawNonzeroAttempts) :
    rawForSkeletonValue (successfulRawNonzeroFactorization raw).1
        (successfulRawNonzeroFactorization raw).2 = raw := by
  exact successfulRawNonzeroFactorization.symm_apply_apply raw

@[simp] theorem rawForSkeletonValue_returns_value
    (skeleton : Tag73OuterSamplerSkeleton)
    (value : NonzeroQM31Exact) :
    successfulRawNonzeroValue (rawForSkeletonValue skeleton value) = value := by
  have factorExact := successfulRawNonzeroFactorization.apply_symm_apply
    (skeleton, value)
  rw [← successfulRawNonzeroFactorization_value]
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
  proof? : SuccessfulTag73RawNonzeroAttempts → Option Tag73K12ParsedProof
  proofGammaExact : ∀ raw proof,
    proof? raw = some proof →
      proof.gamma = (successfulRawNonzeroValue raw).1

/-- Classify the counterfactual parsed proof for a single nonzero gamma.  A
machine rejection or a typed K1.3 error makes that challenge unavailable;
neither can manufacture a selected branch. -/
noncomputable def counterfactualParsedK13Branch?
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (skeleton : Tag73OuterSamplerSkeleton)
    (gamma : QM31Exact) : Option (RestoredSelectedBranch decoder words gamma) := by
  classical
  by_cases nonzero : gamma ≠ 0
  · let value : NonzeroQM31Exact := ⟨gamma, nonzero⟩
    let raw := rawForSkeletonValue skeleton value
    match proofEq : oracle.proof? raw with
    | none => exact none
    | some proof =>
        have gammaExact : proof.gamma = gamma := by
          calc
            proof.gamma = (successfulRawNonzeroValue raw).1 :=
              oracle.proofGammaExact raw proof proofEq
            _ = gamma := by
              rw [show raw = rawForSkeletonValue skeleton value by rfl,
                rawForSkeletonValue_returns_value]
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
    (skeleton : Tag73OuterSamplerSkeleton) :
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
    (skeleton : Tag73OuterSamplerSkeleton) :
    (counterfactualK13Provider oracle skeleton).branch 0 = none := by
  simp [counterfactualK13Provider, counterfactualParsedK13Branch?]

/-- The counterfactual provider contains the actually executed branch whenever
the future-free machine returned that parsed proof and its exact K1.3
classifier succeeded.  This is the deterministic identity needed before any
probability argument is applied. -/
theorem actual_raw_counterfactual_branch_available
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : CounterfactualParsedK13Oracle decoder words)
    (raw : SuccessfulTag73RawNonzeroAttempts)
    (proof : Tag73K12ParsedProof)
    (proofExact : oracle.proof? raw = some proof)
    (k13 : ParsedK13Certificate decoder words proof)
    (k13Exact : classifyParsedK13 decoder words proof = .inl k13) :
    selectedProviderAvailable
        (counterfactualK13Provider oracle
          (successfulRawNonzeroFactorization raw).1)
        (successfulRawNonzeroValue raw).1 := by
  classical
  have gammaNonzero : (successfulRawNonzeroValue raw).1 ≠ 0 :=
    (successfulRawNonzeroValue raw).2
  have rawExact :
      rawForSkeletonValue (successfulRawNonzeroFactorization raw).1
        (successfulRawNonzeroValue raw) = raw := by
    rw [← successfulRawNonzeroFactorization_value]
    exact rawForSkeletonValue_factorization raw
  unfold selectedProviderAvailable counterfactualK13Provider
  simp only
  unfold counterfactualParsedK13Branch?
  split
  · rename_i h
    have reconstructed :
        rawForSkeletonValue (successfulRawNonzeroFactorization raw).1
            ⟨(successfulRawNonzeroValue raw).1, h⟩ = raw := by
      convert rawExact using 1
    dsimp only
    have proofExact' :
        oracle.proof?
            (rawForSkeletonValue (successfulRawNonzeroFactorization raw).1
              ⟨(successfulRawNonzeroValue raw).1, h⟩) = some proof := by
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
      · rfl
  · rename_i h
    exact (h gammaNonzero).elim

end

#print axioms rawForSkeletonValue_factorization
#print axioms rawForSkeletonValue_returns_value
#print axioms counterfactualParsedK13Branch?
#print axioms counterfactualK13Provider
#print axioms counterfactual_provider_zero_unavailable
#print axioms actual_raw_counterfactual_branch_available

end AspisK1.V7Tag73CounterfactualK13Provider
