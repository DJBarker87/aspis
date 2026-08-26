import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.Pool.V7MerklePartialPathExtractor

/-!
# Exact fixed-run prefix K1.2 classifier for Tag-73

The received oracle used by proximity extraction is fixed at the literal
prover-final shared-oracle state, before the verifier begins its dependent
run.  The verifier-final history is retained only for supplied-opening trace
coverage and the shared 208-bit collision event.

Unlike the earlier complete-query-graph classifier, this construction does
not demand preimages for unopened subtrees and does not require the arbitrary
completion to recommit to the public roots.  It follows each sampled path in
the prover-final prefix and fills every unresolved coordinate with a fixed
default.  A sampled unresolved path is an explicit ROM failure event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedK12PrefixClassifier

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerklePartialPathExtractor

noncomputable section

def exactK12ProverPrefixQueries
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : OrderedRawQueryLog :=
  (exactK12Runtime input).proverFinalOracle.history.map
    (fun record => runtimeInputToRawHashInput record.input)

def exactPrefixK12Words
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : ExtractedWords :=
  extractPrefixFixedWords (exactK12Truncate input)
    (exactK12ProverPrefixQueries input) (exactK12Roots input)

def ExactPrefixK12SuppliedCoverage
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Prop :=
  (∀ ordinal : Fin disclosedQueryPairs,
    TraceIncludedInLog
      (openingInputTrace (exactK12Truncate input)
        (exactK12Openings input ordinal).position
        (.c1Leaf (exactK12Openings input ordinal).c1Value
          (exactK12Openings input ordinal).sharedSalt)
        (exactK12Openings input ordinal).c1Siblings)
      (exactK12OrderedQueries input)) ∧
  (∀ ordinal : Fin disclosedQueryPairs,
    TraceIncludedInLog
      (openingInputTrace (exactK12Truncate input)
        (exactK12Openings input ordinal).position
        (.c2Leaf (exactK12Openings input ordinal).c2Value
          (exactK12Openings input ordinal).sharedSalt)
        (exactK12Openings input ordinal).c2Siblings)
      (exactK12OrderedQueries input))

def ExactPrefixK12PrefixIncluded
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Prop :=
  TraceIncludedInLog (exactK12ProverPrefixQueries input)
    (exactK12OrderedQueries input)

theorem exactK12_prover_history_is_prefix_of_verifier_final_history
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactK12Runtime input).proverFinalOracle.history <+:
      (exactK12Runtime input).verifierFinalOracle.history := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have suffix := projected_fresh_returned_trace_preserves_suffix
    configuration.machine.verifierLimits .verifier
    prefixes.adversary.finalState.history []
    configuration.machine.verifierFuel prefixes.adversary.finalState
    (schedulerStageProgram
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result)
      (totalizeOracleMachine configuration.machine.verifierFuel
        (initialRawFutureFreeProgram configuration.machine.environment
          prefixes.adversaryValue.rawMessages
          configuration.machine.driverFuel)))
    prefixes.verifier.freshQueries prefixes.verifier.result
    prefixes.verifier.finalState prefixes.verifier.steps
    (projected_fresh_suffix_initial prefixes.adversary.finalState)
    prefixes.verifier.trace
  obtain ⟨appended, historyExact, _freshExact⟩ := suffix
  have projectedPrefix : prefixes.adversary.finalState.history <+:
      prefixes.verifier.finalState.history :=
    ⟨appended, historyExact.symm⟩
  have runtimeExact := prefixes.runtimeExact
  have proverExact :
      (exactK12Runtime input).proverFinalOracle =
        prefixes.adversary.finalState := by
    have projectionExact := congrArg
      (fun runtime => runtime.proverFinalOracle) runtimeExact
    simpa [exactK12Runtime, prefixes, operationalRootRuntime] using
      projectionExact
  have verifierExact :
      (exactK12Runtime input).verifierFinalOracle =
        prefixes.verifier.finalState := by
    have projectionExact := congrArg
      (fun runtime => runtime.verifierFinalOracle) runtimeExact
    simpa [exactK12Runtime, prefixes, operationalRootRuntime] using
      projectionExact
  simpa [proverExact, verifierExact] using projectedPrefix

theorem exactK12_prover_prefix_is_included_in_full_log
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactPrefixK12PrefixIncluded input := by
  have historyPrefix :=
    exactK12_prover_history_is_prefix_of_verifier_final_history input
  have mappedPrefix := historyPrefix.map
    (fun record => runtimeInputToRawHashInput record.input)
  intro rawInput inputIn
  exact mappedPrefix.subset inputIn

structure ExactPrefixK12Certificate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) where
  words : ExtractedWords
  wordsExact : words = exactPrefixK12Words input
  openingsAccepted : accepted_two_tree_openings (exactK12Truncate input)
    (exactK12Roots input) (exactK12Openings input)
  prefixIncluded : ExactPrefixK12PrefixIncluded input
  noResolutionFailure :
    ¬ PrefixPathResolutionFailure (exactK12Truncate input)
      (exactK12ProverPrefixQueries input) (exactK12Roots input)
      (exactK12Openings input)
  suppliedCovered : ExactPrefixK12SuppliedCoverage input
  noCollision :
    ¬ RawLogTruncatedDigestCollision (exactK12Truncate input)
      (exactK12OrderedQueries input)
  projections : disclosuresAreProjections words (exactK12Openings input)

inductive ExactPrefixK12Error
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type
  | openingAuthenticationRejected
      (failure : ¬ accepted_two_tree_openings (exactK12Truncate input)
        (exactK12Roots input) (exactK12Openings input))
  | prefixPathResolution
      (failure : PrefixPathResolutionFailure (exactK12Truncate input)
        (exactK12ProverPrefixQueries input) (exactK12Roots input)
        (exactK12Openings input))
  | suppliedOpeningTraceMissing
      (failure : ¬ ExactPrefixK12SuppliedCoverage input)
  | sharedRawPrefixCollision
      (failure : RawLogTruncatedDigestCollision (exactK12Truncate input)
        (exactK12OrderedQueries input))

noncomputable def classifyExactPrefixK12
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactPrefixK12Certificate input ⊕ ExactPrefixK12Error input := by
  classical
  by_cases accepted : accepted_two_tree_openings (exactK12Truncate input)
      (exactK12Roots input) (exactK12Openings input)
  · have prefixIncluded := exactK12_prover_prefix_is_included_in_full_log input
    by_cases resolutionFailure : PrefixPathResolutionFailure
        (exactK12Truncate input) (exactK12ProverPrefixQueries input)
        (exactK12Roots input) (exactK12Openings input)
    · exact .inr (.prefixPathResolution resolutionFailure)
    · by_cases suppliedCovered : ExactPrefixK12SuppliedCoverage input
      · by_cases collision : RawLogTruncatedDigestCollision
            (exactK12Truncate input) (exactK12OrderedQueries input)
        · exact .inr (.sharedRawPrefixCollision collision)
        · let words := exactPrefixK12Words input
          have projections : disclosuresAreProjections words
              (exactK12Openings input) := by
            exact accepted_openings_are_prefix_fixed_projections
              (exactK12Truncate input) (exactK12ProverPrefixQueries input)
              (exactK12OrderedQueries input) (exactK12Roots input)
              (exactK12Openings input) accepted prefixIncluded
              resolutionFailure suppliedCovered.1 suppliedCovered.2 collision
          exact .inl
            { words := words
              wordsExact := rfl
              openingsAccepted := accepted
              prefixIncluded := prefixIncluded
              noResolutionFailure := resolutionFailure
              suppliedCovered := suppliedCovered
              noCollision := collision
              projections := projections }
      · exact .inr (.suppliedOpeningTraceMissing suppliedCovered)
  · exact .inr (.openingAuthenticationRejected accepted)

theorem exactPrefixK12_words_have_frozen_lengths
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (certificate : ExactPrefixK12Certificate input) :
    certificate.words.c1.length = 2 ^ treeDepth ∧
      certificate.words.c2.length = 2 ^ treeDepth := by
  rw [certificate.wordsExact]
  exact ⟨extractPrefixFixedWords_c1_length _ _ _,
    extractPrefixFixedWords_c2_length _ _ _⟩

#print axioms classifyExactPrefixK12
#print axioms exactK12_prover_history_is_prefix_of_verifier_final_history
#print axioms exactK12_prover_prefix_is_included_in_full_log
#print axioms exactPrefixK12_words_have_frozen_lengths

end

end AspisK1.V7Tag73ExactFixedK12PrefixClassifier
