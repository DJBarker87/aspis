import AspisFormal.K1.V7Tag73ExactCompilerSchedulerReplayProof
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting

/-!
# One scheduler-native response family fixed before gamma

This module packages the executable scheduler-native counterfactual replay in
the required quantifier order.  A routed nuisance skeleton, exact first-target
scan, and retained scheduler state are fixed once.  The resulting function is
then total over every nonzero challenge.  Its chronological duplex tape is
constructed by the variable-prefix routing map, so no unused suffix is
required to decode.

The absent branch remains part of the same executable family and is constant
in the supplied challenge.  On an occurrence branch, every successful replay
returns exactly the challenge supplied to the family.  No completed-context
provider, cross-gamma coherence premise, or probability statement is used.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativePreGammaFamily

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73ExactCompilerSchedulerReplayProof
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73CausalRestoredFamily
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Execute the scheduler-native replay on the chronological production tape
represented by one routed successful sample. -/
def schedulerNativeRoutedReplay
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls Result
      (gammaOutputInput nuisance.initialDigest))
    (sample : RoutedSuccessfulGammaTape) :
    Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeGammaResponse Result) :=
  replaySchedulerNativeAtGamma transitionFuel nuisance firstScan
    (routedSuccessfulGammaToFlat sample).1
    (routedSuccessfulGammaValue sample)

/-- The actual pre-gamma strategy: the nuisance skeleton and scheduler pause
are fixed before its argument is supplied.  Each counterfactual gamma gets the
unique routed sample reconstructed from that same skeleton. -/
def schedulerNativePreGammaFamily
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls Result
      (gammaOutputInput nuisance.initialDigest))
    (skeleton : VariableGammaCompleteSkeleton) :
    NonzeroQM31Exact → Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeGammaResponse Result) :=
  fun gamma =>
    schedulerNativeRoutedReplay transitionFuel nuisance firstScan
      (routedForSkeletonValue skeleton gamma)

/-! ## Exact compiler instantiation -/

/-- Bind the routed replay family to the literal result-carrying exact compiler
scan and its actual unified master tape.  The only additional datum is the
pre-gamma transcript digest naming the first output input. -/
def exactCompilerRoutedGammaReplay
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (sample : RoutedSuccessfulGammaTape) :
    Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)) :=
  schedulerNativeRoutedReplay transitionFuel ⟨initialDigest⟩
    (exactCompilerFullTargetScan input (gammaOutputInput initialDigest)) sample

/-- The exact compiler strategy has the required pre-challenge quantifier
order: the compiler run, initial digest, and nuisance skeleton are fixed before
the function receives its counterfactual gamma. -/
def exactCompilerPreGammaFamily
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) :
    NonzeroQM31Exact → Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)) :=
  schedulerNativePreGammaFamily transitionFuel ⟨initialDigest⟩
    (exactCompilerFullTargetScan input (gammaOutputInput initialDigest))
      skeleton

/-- The actual routed sample is a member of the exact compiler family by
factorization, with no selected-sample witness supplied by a caller. -/
theorem exact_compiler_pre_gamma_family_contains_routed_sample
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (sample : RoutedSuccessfulGammaTape) :
    exactCompilerPreGammaFamily input initialDigest
        (routedSuccessfulGammaFactorization sample).1
        (routedSuccessfulGammaValue sample) =
      exactCompilerRoutedGammaReplay input initialDigest sample := by
  unfold exactCompilerPreGammaFamily exactCompilerRoutedGammaReplay
    schedulerNativePreGammaFamily
  rw [← routedSuccessfulGammaFactorization_value]
  rw [routedForSkeletonValue_factorization]

@[simp] theorem schedulerNativePreGammaFamily_sample_value
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : NonzeroQM31Exact) :
    routedSuccessfulGammaValue (routedForSkeletonValue skeleton gamma) =
      gamma :=
  routedForSkeletonValue_returns_value skeleton gamma

/-- The member selected by an actually routed successful sample is exactly
that sample, not a separately chosen witness. -/
theorem scheduler_native_pre_gamma_family_contains_routed_sample
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls Result
      (gammaOutputInput nuisance.initialDigest))
    (sample : RoutedSuccessfulGammaTape) :
    schedulerNativePreGammaFamily transitionFuel nuisance firstScan
        (routedSuccessfulGammaFactorization sample).1
        (routedSuccessfulGammaValue sample) =
      schedulerNativeRoutedReplay transitionFuel nuisance firstScan sample := by
  unfold schedulerNativePreGammaFamily
  rw [← routedSuccessfulGammaFactorization_value]
  rw [routedForSkeletonValue_factorization]

/-- On an occurrence branch, a successful member of the pre-fixed family
returns the literal challenge supplied to that member. -/
theorem scheduler_native_pre_gamma_occurrence_returned_exact
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput nuisance.initialDigest))
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : NonzeroQM31Exact)
    (response : SchedulerNativeGammaResponse Result)
    (run : schedulerNativePreGammaFamily transitionFuel nuisance
      (.paused pause) skeleton gamma = .ok response) :
    response.returnedGamma = some gamma.1 := by
  have occurrenceRun : replaySchedulerNativeOccurrenceAtGamma transitionFuel
      pause (routedSuccessfulGammaToFlat
        (routedForSkeletonValue skeleton gamma)).1 gamma = .ok response := by
    simpa [schedulerNativePreGammaFamily, schedulerNativeRoutedReplay,
      replaySchedulerNativeAtGamma, routedForSkeletonValue_returns_value]
      using run
  exact replay_scheduler_native_occurrence_returned_gamma_exact transitionFuel
    pause (routedSuccessfulGammaToFlat
      (routedForSkeletonValue skeleton gamma)).1 gamma response occurrenceRun

/-- The corresponding parsed response contains the supplied gamma, derived
from the production decoder equality inside the replay. -/
theorem scheduler_native_pre_gamma_occurrence_decoded_exact
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (pause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput nuisance.initialDigest))
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : NonzeroQM31Exact)
    (response : SchedulerNativeGammaResponse Result)
    (run : schedulerNativePreGammaFamily transitionFuel nuisance
      (.paused pause) skeleton gamma = .ok response) :
    ∃ encoded : Qm31Bytes,
      response.decodedBytes = some encoded ∧
      decodeTagQM31ExactLE encoded = some gamma.1 := by
  have occurrenceRun : replaySchedulerNativeOccurrenceAtGamma transitionFuel
      pause (routedSuccessfulGammaToFlat
        (routedForSkeletonValue skeleton gamma)).1 gamma = .ok response := by
    simpa [schedulerNativePreGammaFamily, schedulerNativeRoutedReplay,
      replaySchedulerNativeAtGamma, routedForSkeletonValue_returns_value]
      using run
  exact replay_scheduler_native_occurrence_decoded_gamma_exact transitionFuel
    pause (routedSuccessfulGammaToFlat
      (routedForSkeletonValue skeleton gamma)).1 gamma response occurrenceRun

/-- The exhaustive no-target branch is one constant response family.  This
keeps occurrence and no-occurrence cases in the total counterfactual model. -/
theorem scheduler_native_pre_gamma_absent_constant
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (run : SchedulerNativeRun Result)
    (skeleton : VariableGammaCompleteSkeleton)
    (left right : NonzeroQM31Exact) :
    schedulerNativePreGammaFamily transitionFuel nuisance
        (.absent run : SchedulerNativeTargetScan globalOracleCalls Result
          (gammaOutputInput nuisance.initialDigest))
        skeleton left =
      schedulerNativePreGammaFamily transitionFuel nuisance
        (.absent run : SchedulerNativeTargetScan globalOracleCalls Result
          (gammaOutputInput nuisance.initialDigest))
        skeleton right := by
  rfl

/-- Construct the parsed-proof oracle from the single pre-fixed executable
family.  The oracle is therefore obtained as a whole function, not selected
after observing the actual gamma. -/
def routedParsedOracleOfSchedulerPreGammaFamily
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Payload Result : Type}
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest)) :
    RoutedCounterfactualParsedK13Oracle :=
  routedCounterfactualParsedK13OracleOfExactCompilerSchedulerReplay
    (schedulerNativeRoutedReplay transitionFuel nuisance firstScan)

/-- Parsed-proof oracle whose replay function and first scan are both the
literal exact compiler definitions. -/
def exactCompilerRoutedParsedOracle
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256) : RoutedCounterfactualParsedK13Oracle :=
  routedCounterfactualParsedK13OracleOfExactCompilerSchedulerReplay
    (exactCompilerRoutedGammaReplay input initialDigest)

/-- Construct the complete selected-response family for one fixed nuisance
skeleton from the executable parsed-proof oracle.  Every nonzero gamma branch
is queried through the same pre-fixed scheduler replay function. -/
noncomputable def restoredSelectedProviderOfSchedulerPreGammaFamily
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Payload Result : Type}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest))
    (skeleton : VariableGammaCompleteSkeleton) :
    RestoredSelectedBranchProvider decoder words :=
  routedCounterfactualK13Provider defaultResponse defaultDisclosedFinal
    defaultSchedule defaultSelected
      (routedParsedOracleOfSchedulerPreGammaFamily transitionFuel nuisance
        firstScan) skeleton

/-- Complete selected-response family with the exact compiler scan fixed
definitionally. -/
noncomputable def exactCompilerRestoredSelectedProvider
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) :
    RestoredSelectedBranchProvider decoder words :=
  routedCounterfactualK13Provider defaultResponse defaultDisclosedFinal
    defaultSchedule defaultSelected
      (exactCompilerRoutedParsedOracle input initialDigest) skeleton

/-- Selected-branch source theorem for the oracle constructed from the whole
pre-gamma family.  Its remaining premises are literal executable/source
equalities, not provider coherence or probability bounds. -/
theorem routed_parsed_oracle_of_pre_gamma_family_actual_proof
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest))
    (sample : RoutedSuccessfulGammaTape)
    (response : SchedulerNativeGammaResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (clientRun : ConcreteRestorationClientRun Statement Tag73K12ParsedProof
      Payload Result)
    (replayExact : schedulerNativeRoutedReplay transitionFuel nuisance
      firstScan sample = .ok response)
    (returned : response.run.terminal =
      .returned (.completed (exactK12Runtime input) clientRun))
    (gammaExact : (exactK13ParsedProof input).gamma =
      (routedSuccessfulGammaValue sample).1) :
    (routedParsedOracleOfSchedulerPreGammaFamily transitionFuel nuisance
      firstScan).proof? sample = some (exactK13ParsedProof input) := by
  unfold routedParsedOracleOfSchedulerPreGammaFamily
  exact exact_compiler_scheduler_replay_provider_actual_proof input
    (schedulerNativeRoutedReplay transitionFuel nuisance firstScan) sample
    response clientRun replayExact returned gammaExact

/-- The accepted parser/source binding removes the separate parsed-proof gamma
premise.  The literal replay result, returned terminal, and equality between
the operational sampler value and routed chronological sample remain explicit
source obligations. -/
theorem routed_parsed_oracle_of_pre_gamma_family_actual_proof_of_source
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest))
    (sample : RoutedSuccessfulGammaTape)
    (response : SchedulerNativeGammaResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (clientRun : ConcreteRestorationClientRun Statement Tag73K12ParsedProof
      Payload Result)
    (replayExact : schedulerNativeRoutedReplay transitionFuel nuisance
      firstScan sample = .ok response)
    (returned : response.run.terminal =
      .returned (.completed (exactK12Runtime input) clientRun))
    (operationalGammaExact : exactOperationalChallenge input .gamma =
      (routedSuccessfulGammaValue sample).1) :
    (routedParsedOracleOfSchedulerPreGammaFamily transitionFuel nuisance
      firstScan).proof? sample = some (exactK13ParsedProof input) := by
  exact routed_parsed_oracle_of_pre_gamma_family_actual_proof input nuisance
    firstScan sample response clientRun replayExact returned
      (source.gammaExact.trans operationalGammaExact)

/-- Exact-compiler specialization of the selected proof equality.  The scan
and replay function are no longer parameters; the remaining hypotheses are
the literal multi-query replay result, terminal reconstruction, and source
gamma coordinate equality. -/
theorem exact_compiler_routed_parsed_oracle_actual_proof_of_source
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (initialDigest : Digest256)
    (sample : RoutedSuccessfulGammaTape)
    (response : SchedulerNativeGammaResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (clientRun : ConcreteRestorationClientRun Statement Tag73K12ParsedProof
      Payload Result)
    (replayExact : exactCompilerRoutedGammaReplay input initialDigest sample =
      .ok response)
    (returned : response.run.terminal =
      .returned (.completed (exactK12Runtime input) clientRun))
    (operationalGammaExact : exactOperationalChallenge input .gamma =
      (routedSuccessfulGammaValue sample).1) :
    (exactCompilerRoutedParsedOracle input initialDigest).proof? sample =
      some (exactK13ParsedProof input) := by
  unfold exactCompilerRoutedParsedOracle exactCompilerRoutedGammaReplay
  exact exact_compiler_scheduler_replay_provider_actual_proof input
    (schedulerNativeRoutedReplay transitionFuel ⟨initialDigest⟩
      (exactCompilerFullTargetScan input (gammaOutputInput initialDigest)))
    sample response clientRun replayExact returned
      (source.gammaExact.trans operationalGammaExact)

#print axioms scheduler_native_pre_gamma_occurrence_returned_exact
#print axioms scheduler_native_pre_gamma_occurrence_decoded_exact
#print axioms scheduler_native_pre_gamma_absent_constant
#print axioms scheduler_native_pre_gamma_family_contains_routed_sample
#print axioms exact_compiler_pre_gamma_family_contains_routed_sample
#print axioms routedParsedOracleOfSchedulerPreGammaFamily
#print axioms restoredSelectedProviderOfSchedulerPreGammaFamily
#print axioms exactCompilerRoutedParsedOracle
#print axioms exactCompilerRestoredSelectedProvider
#print axioms routed_parsed_oracle_of_pre_gamma_family_actual_proof
#print axioms
  routed_parsed_oracle_of_pre_gamma_family_actual_proof_of_source
#print axioms
  exact_compiler_routed_parsed_oracle_actual_proof_of_source

end

end AspisK1.V7Tag73SchedulerNativePreGammaFamily
