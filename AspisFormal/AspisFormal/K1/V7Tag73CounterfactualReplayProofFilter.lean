import AspisFormal.K1.V7Tag73CounterfactualK13Provider
import AspisFormal.K1.V7Tag73VariablePrefixGammaFactorization
import AspisFormal.K1.V7Tag73RawSameTapeSource
import AspisFormal.K1.V7Tag73ProductionCounterfactualReplay

/-!
# Parsed-proof families constructed from executable counterfactual replay

A replay may abort, exhaust its fuel, return a malformed value at a higher
layer, or return a parsed proof whose embedded gamma disagrees with the gamma
supplied to the replay.  The correct total provider maps every such branch to
`none`.  Only a normally returned proof with literal gamma equality is
exposed.

Consequently the all-gamma property required by the K1.3 provider is a
theorem of the executable filter.  It is not a caller-supplied coherence
assumption.  This file gives both the legacy three-success sampler adapter
and the exact routed variable-prefix provider; the latter never requires an
unread ordinary attempt to decode.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CounterfactualReplayProofFilter

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73CounterfactualK13Provider
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73ProductionCounterfactualReplay
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Extract a parsed proof only from a normal replay return whose literal raw
proof gamma equals the counterfactual gamma supplied to that replay. -/
def replayedProofAtGamma?
    {Statement Payload : Type*}
    (gamma : QM31Exact)
    (run : MachineRun
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload)) : Option Tag73K12ParsedProof :=
  match run.halt with
  | .returned value =>
      let proof := value.1.publicProof.proof.rawProof
      if proof.gamma = gamma then some proof else none
  | .oracleAbort _ => none
  | .outOfFuel => none

/-- The executable filter cannot expose a proof under the wrong gamma. -/
theorem replayedProofAtGamma_gammaExact
    {Statement Payload : Type*}
    (gamma : QM31Exact)
    (run : MachineRun
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload))
    (proof : Tag73K12ParsedProof)
    (proofExact : replayedProofAtGamma? gamma run = some proof) :
    proof.gamma = gamma := by
  cases haltExact : run.halt with
  | returned value =>
      simp only [replayedProofAtGamma?, haltExact]
        at proofExact
      split at proofExact
      next gammaExact =>
        exact Option.some.inj proofExact ▸ gammaExact
      next gammaMismatch => simp at proofExact
  | oracleAbort reason =>
      simp [replayedProofAtGamma?, haltExact] at proofExact
  | outOfFuel =>
      simp [replayedProofAtGamma?, haltExact] at proofExact

/-- A literal normal return with matching parsed gamma is exposed by the
filter.  This is the actual-branch endpoint used after proving replay
equality from machine semantics. -/
theorem replayedProofAtGamma_of_returned
    {Statement Payload : Type*}
    (gamma : QM31Exact)
    (run : MachineRun
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload))
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload)
    (returned : run.halt = .returned value)
    (gammaExact : value.1.publicProof.proof.rawProof.gamma = gamma) :
    replayedProofAtGamma? gamma run =
      some value.1.publicProof.proof.rawProof := by
  simp [replayedProofAtGamma?, returned, gammaExact]

/-- The corresponding filter for the total production replay driver.  A
failure is unavailable; a successful response is exposed exactly when the
returned raw proof records the supplied gamma. -/
def counterfactualResponseProofAtGamma?
    {Failure Statement Payload : Type*}
    (gamma : QM31Exact)
    (result : Except Failure
      (CounterfactualResponse
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload))) : Option Tag73K12ParsedProof :=
  match result with
  | .error _ => none
  | .ok response =>
      let proof := response.value.1.publicProof.proof.rawProof
      if proof.gamma = gamma then some proof else none

theorem counterfactualResponseProofAtGamma_gammaExact
    {Failure Statement Payload : Type*}
    (gamma : QM31Exact)
    (result : Except Failure
      (CounterfactualResponse
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload)))
    (proof : Tag73K12ParsedProof)
    (proofExact : counterfactualResponseProofAtGamma? gamma result =
      some proof) : proof.gamma = gamma := by
  cases result with
  | error failure =>
      simp [counterfactualResponseProofAtGamma?] at proofExact
  | ok response =>
      simp only [counterfactualResponseProofAtGamma?] at proofExact
      split at proofExact
      next gammaExact => exact Option.some.inj proofExact ▸ gammaExact
      next gammaMismatch => simp at proofExact

theorem counterfactualResponseProofAtGamma_of_ok
    {Failure Statement Payload : Type*}
    (gamma : QM31Exact)
    (result : Except Failure
      (CounterfactualResponse
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload)))
    (response : CounterfactualResponse
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload))
    (returned : result = .ok response)
    (gammaExact : response.value.1.publicProof.proof.rawProof.gamma = gamma) :
    counterfactualResponseProofAtGamma? gamma result =
      some response.value.1.publicProof.proof.rawProof := by
  simp [counterfactualResponseProofAtGamma?, returned, gammaExact]

/-- Build the existing K1.3 provider from one executable replay function.
The only caller data are harmless defaults for unavailable K1.3 branches and
the replay itself; `proof?` and its cross-gamma theorem are constructed here.

This adapter preserves the legacy provider's overly strong sample domain so
existing downstream files can consume it.  It does not claim that domain
covers the production variable-prefix sampler. -/
def counterfactualParsedK13OracleOfReplay
    {Statement Payload : Type*}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (replay : SuccessfulTag73DuplexNonzeroAttempts →
      MachineRun
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload)) : CounterfactualParsedK13Oracle decoder words where
  defaultResponse := defaultResponse
  defaultDisclosedFinal := defaultDisclosedFinal
  defaultSchedule := defaultSchedule
  defaultSelected := defaultSelected
  proof? := fun sample =>
    replayedProofAtGamma? (successfulDuplexNonzeroValue sample).1
      (replay sample)
  proofGammaExact := by
    intro sample proof proofExact
    exact replayedProofAtGamma_gammaExact
      (successfulDuplexNonzeroValue sample).1 (replay sample) proof proofExact

/-- Correct parsed-proof provider over the exact routed variable-prefix
sampler.  Unexecuted attempts are arbitrary raw streams in the sample type. -/
structure RoutedCounterfactualParsedK13Oracle where
  proof? : RoutedSuccessfulGammaTape → Option Tag73K12ParsedProof
  proofGammaExact : ∀ sample proof,
    proof? sample = some proof →
      proof.gamma = (routedSuccessfulGammaValue sample).1

/-- Construct the correct routed provider from one executable replay family.
No cross-gamma or selected-branch premise is accepted. -/
def routedCounterfactualParsedK13OracleOfReplay
    {Statement Payload : Type*}
    (replay : RoutedSuccessfulGammaTape →
      MachineRun
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload)) : RoutedCounterfactualParsedK13Oracle where
  proof? := fun sample =>
    replayedProofAtGamma? (routedSuccessfulGammaValue sample).1
      (replay sample)
  proofGammaExact := by
    intro sample proof proofExact
    exact replayedProofAtGamma_gammaExact
      (routedSuccessfulGammaValue sample).1 (replay sample) proof proofExact

/-- Direct construction from the executable total replay result, including
explicit failure branches. -/
def routedCounterfactualParsedK13OracleOfResponseReplay
    {Failure Statement Payload : Type*}
    (replay : RoutedSuccessfulGammaTape →
      Except Failure
        (CounterfactualResponse
          (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
            Payload))) : RoutedCounterfactualParsedK13Oracle where
  proof? := fun sample =>
    counterfactualResponseProofAtGamma?
      (routedSuccessfulGammaValue sample).1 (replay sample)
  proofGammaExact := by
    intro sample proof proofExact
    exact counterfactualResponseProofAtGamma_gammaExact
      (routedSuccessfulGammaValue sample).1 (replay sample) proof proofExact

theorem routed_response_replay_provider_actual_proof
    {Failure Statement Payload : Type*}
    (replay : RoutedSuccessfulGammaTape →
      Except Failure
        (CounterfactualResponse
          (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
            Payload)))
    (sample : RoutedSuccessfulGammaTape)
    (response : CounterfactualResponse
      (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
        Payload))
    (returned : replay sample = .ok response)
    (gammaExact : response.value.1.publicProof.proof.rawProof.gamma =
      (routedSuccessfulGammaValue sample).1) :
    (routedCounterfactualParsedK13OracleOfResponseReplay replay).proof?
        sample = some response.value.1.publicProof.proof.rawProof := by
  exact counterfactualResponseProofAtGamma_of_ok
    (routedSuccessfulGammaValue sample).1 (replay sample) response returned
      gammaExact

/-- Actual-branch source equality for the routed executable provider.  The
premises are the literal machine halt and parser-data gamma equality; no
provider coherence or probability statement is assumed. -/
theorem routed_replay_provider_actual_proof
    {Statement Payload : Type*}
    (replay : RoutedSuccessfulGammaTape →
      MachineRun
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload))
    (sample : RoutedSuccessfulGammaTape)
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload)
    (returned : (replay sample).halt = .returned value)
    (gammaExact : value.1.publicProof.proof.rawProof.gamma =
      (routedSuccessfulGammaValue sample).1) :
    (routedCounterfactualParsedK13OracleOfReplay replay).proof? sample =
      some value.1.publicProof.proof.rawProof := by
  exact replayedProofAtGamma_of_returned
    (routedSuccessfulGammaValue sample).1 (replay sample) value returned
      gammaExact

/-- Reconstruct the exact routed execution for one fixed nuisance skeleton
and one supplied nonzero challenge. -/
def routedForSkeletonValue
    (skeleton : VariableGammaCompleteSkeleton)
    (value : NonzeroQM31Exact) : RoutedSuccessfulGammaTape :=
  routedSuccessfulGammaFactorization.symm (skeleton, value)

@[simp] theorem routedForSkeletonValue_factorization
    (sample : RoutedSuccessfulGammaTape) :
    routedForSkeletonValue (routedSuccessfulGammaFactorization sample).1
      (routedSuccessfulGammaFactorization sample).2 = sample := by
  exact routedSuccessfulGammaFactorization.symm_apply_apply sample

@[simp] theorem routedForSkeletonValue_returns_value
    (skeleton : VariableGammaCompleteSkeleton)
    (value : NonzeroQM31Exact) :
    routedSuccessfulGammaValue (routedForSkeletonValue skeleton value) =
      value := by
  have factorExact := routedSuccessfulGammaFactorization.apply_symm_apply
    (skeleton, value)
  rw [← routedSuccessfulGammaFactorization_value]
  exact congrArg Prod.snd factorExact

/-- Parse and classify one branch of the routed replay family.  The sample
for every nonzero gamma is reconstructed from the same fixed skeleton. -/
noncomputable def routedCounterfactualParsedK13Branch?
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : QM31Exact) :
    Option (RestoredSelectedBranch decoder words gamma) := by
  classical
  by_cases nonzero : gamma ≠ 0
  · let value : NonzeroQM31Exact := ⟨gamma, nonzero⟩
    let sample := routedForSkeletonValue skeleton value
    match proofEq : oracle.proof? sample with
    | none => exact none
    | some proof =>
        have gammaExact : proof.gamma = gamma := by
          calc
            proof.gamma = (routedSuccessfulGammaValue sample).1 :=
              oracle.proofGammaExact sample proof proofEq
            _ = gamma := by
              rw [show sample = routedForSkeletonValue skeleton value by rfl,
                routedForSkeletonValue_returns_value]
        match classifyParsedK13 decoder words proof with
        | .inr _error => exact none
        | .inl k13 =>
            exact some (gammaExact ▸ restoredSelectedBranchOfParsedK13 k13)
  · exact none

/-- The routed replay constructs one whole response family from the fixed
pre-gamma skeleton.  Defaults are consulted only on unavailable branches. -/
noncomputable def routedCounterfactualK13Provider
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton) :
    RestoredSelectedBranchProvider decoder words where
  defaultResponse := defaultResponse
  defaultDisclosedFinal := defaultDisclosedFinal
  defaultSchedule := defaultSchedule
  defaultSelected := defaultSelected
  branch := routedCounterfactualParsedK13Branch? oracle skeleton

@[simp] theorem routed_counterfactual_provider_zero_unavailable
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton) :
    (@routedCounterfactualK13Provider decoder words defaultResponse
      defaultDisclosedFinal defaultSchedule defaultSelected oracle
      skeleton).branch 0 = none := by
  simp [routedCounterfactualK13Provider,
    routedCounterfactualParsedK13Branch?]

/-- The whole routed family contains the actually replayed parsed K1.3
branch at the actual gamma.  The proof reconstructs the sample from the
factorization and uses only executable provider and classifier equalities. -/
theorem actual_routed_counterfactual_branch_source_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (sample : RoutedSuccessfulGammaTape)
    (proof : Tag73K12ParsedProof)
    (proofExact : oracle.proof? sample = some proof)
    (k13 : ParsedK13Certificate decoder words proof)
    (k13Exact : classifyParsedK13 decoder words proof = .inl k13) :
    ∃ branch,
      (@routedCounterfactualK13Provider decoder words defaultResponse
        defaultDisclosedFinal defaultSchedule defaultSelected oracle
        (routedSuccessfulGammaFactorization sample).1).branch
          (routedSuccessfulGammaValue sample).1 = some branch ∧
        branch.disclosedFinal = proof.disclosedFinal ∧
        branch.schedule = proof.schedule := by
  classical
  have gammaNonzero : (routedSuccessfulGammaValue sample).1 ≠ 0 :=
    (routedSuccessfulGammaValue sample).2
  have sampleExact :
      routedForSkeletonValue (routedSuccessfulGammaFactorization sample).1
        (routedSuccessfulGammaValue sample) = sample := by
    rw [← routedSuccessfulGammaFactorization_value]
    exact routedForSkeletonValue_factorization sample
  unfold routedCounterfactualK13Provider
  simp only
  unfold routedCounterfactualParsedK13Branch?
  split
  · rename_i h
    have reconstructed :
        routedForSkeletonValue
            (routedSuccessfulGammaFactorization sample).1
            ⟨(routedSuccessfulGammaValue sample).1, h⟩ = sample := by
      convert sampleExact using 1
    dsimp only
    have proofExact' :
        oracle.proof?
            (routedForSkeletonValue
              (routedSuccessfulGammaFactorization sample).1
              ⟨(routedSuccessfulGammaValue sample).1, h⟩) =
          some proof := by
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

/-- The routed provider's family is literally fixed as a whole once the
pre-gamma replay function is fixed. -/
theorem routed_provider_proof_is_replay_filter
    {Statement Payload : Type*}
    (replay : RoutedSuccessfulGammaTape →
      MachineRun
        (CheckedRawTag73AdversaryReturnedValue Statement Tag73K12ParsedProof
          Payload))
    (sample : RoutedSuccessfulGammaTape) :
    (routedCounterfactualParsedK13OracleOfReplay replay).proof? sample =
      replayedProofAtGamma? (routedSuccessfulGammaValue sample).1
        (replay sample) := by
  rfl

#print axioms replayedProofAtGamma_gammaExact
#print axioms replayedProofAtGamma_of_returned
#print axioms counterfactualResponseProofAtGamma_gammaExact
#print axioms counterfactualResponseProofAtGamma_of_ok
#print axioms counterfactualParsedK13OracleOfReplay
#print axioms routedCounterfactualParsedK13OracleOfReplay
#print axioms routedCounterfactualParsedK13OracleOfResponseReplay
#print axioms routed_response_replay_provider_actual_proof
#print axioms routed_replay_provider_actual_proof
#print axioms routedForSkeletonValue_factorization
#print axioms routedForSkeletonValue_returns_value
#print axioms routed_counterfactual_provider_zero_unavailable
#print axioms actual_routed_counterfactual_branch_source_exact
#print axioms routed_provider_proof_is_replay_filter

end

end AspisK1.V7Tag73CounterfactualReplayProofFilter
