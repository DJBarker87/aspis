import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixReplayLift
import AspisFormal.K1.V7Tag73CounterfactualReplayProofFilter

/-!
# Exact compiler selected-proof closure after gamma replay

This file composes the source-derived padded gamma replay with the existing
parsed-proof source binding.  It closes the selected, actually sampled branch
of the pre-fixed routed oracle; it does not assert any cross-gamma family or
event-cover conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactCompilerGammaSelectedProofClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- An existing exact K1.3 certificate rules out every error branch of the
parser-data classifier on the same literal proof.  We only expose the
classifier's own returned certificate, avoiding any equality between records
whose proof fields are definitionally irrelevant. -/
theorem classify_parsed_k13_succeeds_of_exact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k13 : ExactK13Certificate decoder input k12) :
    ∃ parsed : ParsedK13Certificate decoder k12.words
        (exactK13ParsedProof input),
      classifyParsedK13 decoder k12.words (exactK13ParsedProof input) =
        .inl parsed := by
  let parsed := parsedK13CertificateOfExact k13
  cases classifierExact :
      classifyParsedK13 decoder k12.words (exactK13ParsedProof input) with
  | inl returned =>
      exact ⟨returned, rfl⟩
  | inr error =>
      cases error with
      | idealRejected rejected => exact (rejected parsed.accepts).elim
      | queryPhaseFailure failure =>
          exact (parsed.noQueryFailure failure).elim
      | oneFoldReductionFailure failure =>
          exact (parsed.noFoldFailure failure).elim
      | initialListCapFailure failure =>
          exact (parsed.noListCapFailure failure).elim

/-- The source-derived actual gamma replay selects the literal parsed proof in
the one whole pre-fixed routed oracle.  The only causal input is the local
coordinate-step interface; the parsed-wire equality is supplied by the
data-only source binding. -/
theorem exact_compiler_actual_gamma_selected_proof_closure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (response : SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerRoutedGammaReplay input initialDigest
          (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response ∧
      response.run = runExactPlainRom transitionFuel configuration sample ∧
      (exactCompilerRoutedParsedOracle input initialDigest).proof?
          (successfulGammaPrefixFlatRoutingEquiv flat) =
        some (exactK13ParsedProof input) := by
  obtain ⟨initialDigest, flat, response, gammaExact, replayExact, runExact⟩ :=
    exact_compiler_actual_gamma_routed_replay_closure input coordinateStep
  have returned :
      response.run.terminal =
        .returned (.completed (exactK12Runtime input)
          input.package.root.full.clientRun) := by
    rw [runExact]
    simpa [exactK12Runtime] using input.package.root.full.fullCompleted
  have proofExact :=
    exact_compiler_routed_parsed_oracle_actual_proof_of_source input source
      initialDigest (successfulGammaPrefixFlatRoutingEquiv flat) response
      input.package.root.full.clientRun replayExact returned gammaExact
  exact ⟨initialDigest, flat, response, gammaExact, replayExact, runExact,
    proofExact⟩

/-- The same actual replay occurs as a real branch of the complete
counterfactual provider.  In particular, the provider branch is not filled by
a default value and its parsed final message and schedule are source-exact. -/
theorem exact_compiler_actual_gamma_provider_branch_closure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactK13Certificate decoder input k12)
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (coordinateStep : ExactCompilerGammaCoordinateStep input)
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule)
    (defaultSelected : ExactCandidatePair) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (response : SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerRoutedGammaReplay input initialDigest
          (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response ∧
      response.run = runExactPlainRom transitionFuel configuration sample ∧
      ∃ (parsed : ParsedK13Certificate decoder k12.words
          (exactK13ParsedProof input)),
        classifyParsedK13 decoder k12.words (exactK13ParsedProof input) =
            .inl parsed ∧
        ∃ branch : RestoredSelectedBranch decoder k12.words
            (routedSuccessfulGammaValue
              (successfulGammaPrefixFlatRoutingEquiv flat)).1,
          (exactCompilerRestoredSelectedProvider defaultResponse
              defaultDisclosedFinal defaultSchedule defaultSelected input
              initialDigest
              (routedSuccessfulGammaFactorization
                (successfulGammaPrefixFlatRoutingEquiv flat)).1).branch
              (routedSuccessfulGammaValue
                (successfulGammaPrefixFlatRoutingEquiv flat)).1 = some branch ∧
          branch.disclosedFinal = (exactK13ParsedProof input).disclosedFinal ∧
          branch.schedule = (exactK13ParsedProof input).schedule := by
  obtain ⟨initialDigest, flat, response, gammaExact, replayExact, runExact,
      proofExact⟩ :=
    exact_compiler_actual_gamma_selected_proof_closure input source
      coordinateStep
  obtain ⟨parsed, classifierExact⟩ :=
    classify_parsed_k13_succeeds_of_exact k13
  obtain ⟨branch, branchExact, finalExact, scheduleExact⟩ :=
    actual_routed_counterfactual_branch_source_exact defaultResponse
      defaultDisclosedFinal defaultSchedule defaultSelected
      (exactCompilerRoutedParsedOracle input initialDigest)
      (successfulGammaPrefixFlatRoutingEquiv flat) (exactK13ParsedProof input)
      proofExact parsed classifierExact
  refine ⟨initialDigest, flat, response, gammaExact, replayExact, runExact,
    parsed, classifierExact, branch, ?_, finalExact, scheduleExact⟩
  simpa only [exactCompilerRestoredSelectedProvider] using branchExact

/-- At the actual gamma, the family constructed from the one pre-fixed replay
is available and selects the same canonical candidate pair as the literal
exact K1.4 extraction.  This is an actual-branch theorem only: it deliberately
does not identify an independently supplied restoration family at all gamma
values. -/
theorem exact_compiler_actual_gamma_provider_family_selected
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactK13Certificate decoder input k12)
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (coordinateStep : ExactCompilerGammaCoordinateStep input)
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : AspisPool.V7CoherentTraceExtraction.ExactSchedule)
    (defaultSelected : ExactCandidatePair) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (response : SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerRoutedGammaReplay input initialDigest
          (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response ∧
      response.run = runExactPlainRom transitionFuel configuration sample ∧
      let routed := successfulGammaPrefixFlatRoutingEquiv flat
      let provider : RestoredSelectedBranchProvider decoder k12.words :=
        exactCompilerRestoredSelectedProvider defaultResponse
          defaultDisclosedFinal defaultSchedule defaultSelected input
          initialDigest (routedSuccessfulGammaFactorization routed).1
      (restoredSelectedChainFamilyOfK13Provider provider).available
          (routedSuccessfulGammaValue routed).1 ∧
        (restoredSelectedChainFamilyOfK13Provider provider).selected
            (routedSuccessfulGammaValue routed).1 =
          k14.extraction.combined := by
  obtain ⟨initialDigest, flat, response, gammaExact, replayExact, runExact,
      parsed, classifierExact, branch, branchExact, finalExact, scheduleExact⟩ :=
    exact_compiler_actual_gamma_provider_branch_closure input k12 k13 source
      coordinateStep defaultResponse defaultDisclosedFinal defaultSchedule
      defaultSelected
  let routed := successfulGammaPrefixFlatRoutingEquiv flat
  let provider : RestoredSelectedBranchProvider decoder k12.words :=
    exactCompilerRestoredSelectedProvider defaultResponse
      defaultDisclosedFinal defaultSchedule defaultSelected input initialDigest
      (routedSuccessfulGammaFactorization routed).1
  have branchExact' :
      provider.branch (routedSuccessfulGammaValue routed).1 = some branch := by
    simpa only [provider, routed] using branchExact
  have familyFacts := k13_family_selected_of_branch provider
    (routedSuccessfulGammaValue routed).1 branch branchExact'
  have proofGammaExact :
      (exactK13ParsedProof input).gamma =
        (routedSuccessfulGammaValue routed).1 :=
    source.gammaExact.trans gammaExact
  have branchSelectedOnProof :
      selectCandidateChain
          (decoder.decodeBoth
            (exactK13Transcript input k12).initial
            (foldedReceived (exactK13ParsedProof input).schedule
              (exactK13Transcript input k12)))
        (exactK13ParsedProof input).schedule
        (exactK13ParsedProof input).disclosedFinal = some branch.selected := by
    simpa [exactK13Transcript, proofGammaExact, finalExact, scheduleExact] using
      branch.selectedExact
  have selectedExact : branch.selected = k14.extraction.combined := by
    apply Option.some.inj
    exact branchSelectedOnProof.symm.trans k14.extraction.combinedSelected
  refine ⟨initialDigest, flat, response, gammaExact, replayExact, runExact, ?_⟩
  dsimp only [routed, provider]
  exact ⟨familyFacts.1, familyFacts.2.trans selectedExact⟩

#print axioms classify_parsed_k13_succeeds_of_exact
#print axioms exact_compiler_actual_gamma_selected_proof_closure
#print axioms exact_compiler_actual_gamma_provider_branch_closure
#print axioms exact_compiler_actual_gamma_provider_family_selected

end

end AspisK1.V7Tag73ExactCompilerGammaSelectedProofClosure
