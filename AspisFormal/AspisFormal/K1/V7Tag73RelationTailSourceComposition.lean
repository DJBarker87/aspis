import AspisFormal.K1.V7Tag73BatchedQuerySourceBridge
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events

/-!
# Exact Tag-73 accepted relation-tail source composition

The two focused Rust/Aeneas bundles expose complementary pieces of one
accepted Tag-73 relation execution:

* the query-batch bundle exposes the shifted `rho, ..., rho^16` covector and
  the shifted claim of the sixteen authenticated fold values; and
* the accepted relation-tail bundle exposes the three later transcript
  challenges, their execution-array updates, and the literal terminal dot
  comparison.

This file is the maintained-model handoff between those raw facts and K1.3.
It deliberately carries only named values and equalities matching translated
intermediates.  In particular it has no field asserting `IdealAccepts`,
pointwise query equality, a zero residual, `QueryInjectionExact`, or an
aggregate terminal-acceptance proposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RelationTailSourceComposition

open AspisK1.V7Tag73BatchedQuerySourceBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge

noncomputable section

/-- Exact maintained projection of the values returned by
`AcceptedRoundTailTrace`.  The three `translatedAlpha*` values are the values
returned by the three literal `challenge_qm31` calls.  `terminalDot` and
`runningClaim` are the two raw values compared by the final `ne` call.

The record states no terminal acceptance predicate: the accepted comparison
is the literal value equality exposed by inversion of the successful
translated call. -/
structure ExactAcceptedRelationTailSourceTrace
    (execution : CandidateExecution QM31Exact)
    (operationalAlpha : Fin 4 → QM31Exact) : Type where
  translatedAlphaOne : QM31Exact
  translatedAlphaTwo : QM31Exact
  translatedAlphaThree : QM31Exact
  executionAlphaOneExact : execution.alpha 1 = translatedAlphaOne
  executionAlphaTwoExact : execution.alpha 2 = translatedAlphaTwo
  executionAlphaThreeExact : execution.alpha 3 = translatedAlphaThree
  transcriptAlphaOneExact : translatedAlphaOne = operationalAlpha 1
  transcriptAlphaTwoExact : translatedAlphaTwo = operationalAlpha 2
  transcriptAlphaThreeExact : translatedAlphaThree = operationalAlpha 3
  terminalDot : QM31Exact
  runningClaim : QM31Exact
  terminalDotExact : terminalDot =
    candidateClaim execution.weights4 execution.values4
  runningClaimExact : runningClaim = execution.claim4
  acceptedComparison : terminalDot = runningClaim

/-- The raw accepted-tail values construct the small terminal equality trace
already consumed by operational K1.5. -/
def ExactAcceptedRelationTailSourceTrace.toTerminalSourceTrace
    {execution : CandidateExecution QM31Exact}
    {operationalAlpha : Fin 4 → QM31Exact}
    (source : ExactAcceptedRelationTailSourceTrace execution operationalAlpha) :
    ExactRelationTerminalSourceTrace execution where
  terminalDot := source.terminalDot
  runningClaim := source.runningClaim
  terminalDotExact := source.terminalDotExact
  runningClaimExact := source.runningClaimExact
  acceptedComparison := source.acceptedComparison

/-- The accepted translated tail implies the maintained terminal predicate
only through its two exact value projections and literal successful
comparison. -/
theorem ExactAcceptedRelationTailSourceTrace.relationTerminal
    {execution : CandidateExecution QM31Exact}
    {operationalAlpha : Fin 4 → QM31Exact}
    (source : ExactAcceptedRelationTailSourceTrace execution operationalAlpha) :
    execution.RelationTerminalAccepts :=
  relation_terminal_accepts_of_source_trace source.toTerminalSourceTrace

/-- One accepted production relation run, before any K1.3 query-consistency
reasoning.  The decoded final vector and alpha-zero equality are setup/parser
facts; rounds one through three and the terminal comparison live in `tail`.
-/
structure ExactAcceptedTag73RelationSourceRun
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  decoded : Fin 641 → QM31Exact
  parsedSource : ExactParsedProofSourceBinding input decoded
  execution : CandidateExecution QM31Exact
  finalEncoderExact : decoder.finalEncoder = exactFinalEncoder
  executionDisclosedFinalExact : execution.disclosedFinal256 =
    decodedFinalMessage decoded
  executionAlphaZeroExact : execution.alpha 0 =
    (exactK13ParsedProof input).schedule.alpha
  tail : ExactAcceptedRelationTailSourceTrace execution
    (fun round => exactOperationalChallenge input (.alpha round))

/-- Alpha zero comes from the parsed/transcript source binding.  The other
three entries come from the three successful challenge calls and execution
updates exposed by the translated relation tail. -/
theorem ExactAcceptedTag73RelationSourceRun.alphaExact
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
    (source : ExactAcceptedTag73RelationSourceRun decoder input)
    (round : Fin 4) :
    source.execution.alpha round =
      exactOperationalChallenge input (.alpha round) := by
  fin_cases round
  · exact source.executionAlphaZeroExact.trans
      source.parsedSource.alphaZeroExact
  · exact source.tail.executionAlphaOneExact.trans
      source.tail.transcriptAlphaOneExact
  · exact source.tail.executionAlphaTwoExact.trans
      source.tail.transcriptAlphaTwoExact
  · exact source.tail.executionAlphaThreeExact.trans
      source.tail.transcriptAlphaThreeExact

/-- The disclosed-final value selected by the parser is exactly the value
carried by the candidate execution. -/
theorem ExactAcceptedTag73RelationSourceRun.parsedDisclosedFinalExact
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
    (source : ExactAcceptedTag73RelationSourceRun decoder input) :
    (exactK13ParsedProof input).disclosedFinal =
      source.execution.disclosedFinal256 := by
  exact source.parsedSource.disclosedFinalExact.trans
    source.executionDisclosedFinalExact.symm

/-- The exact K1.3 expected vector is the final-code vector named by the
translated query-covector insertion. -/
theorem ExactAcceptedTag73RelationSourceRun.expectedQueryVectorExact
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
    (source : ExactAcceptedTag73RelationSourceRun decoder input)
    (k12 : ExactPrefixK12Certificate input) :
    exactTag73K13ExpectedQueryVector decoder input k12 =
      fun ordinal => exactFinalEncoder source.execution.disclosedFinal256
        ((exactK13ParsedProof input).queries ordinal) := by
  funext ordinal
  change decoder.finalEncoder (exactK13ParsedProof input).disclosedFinal
      ((exactK13ParsedProof input).queries ordinal) =
    exactFinalEncoder source.execution.disclosedFinal256
      ((exactK13ParsedProof input).queries ordinal)
  rw [source.finalEncoderExact, source.parsedDisclosedFinalExact]

/-- Sample-indexed source material shared by the K1.3 handoff and the later
K1.5 material constructor.  The authenticated source binding contains only
the shifted covector and shifted callback claim equalities. -/
structure ExactTag73RelationSourceEnvironment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Type where
  run :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
      ExactAcceptedTag73RelationSourceRun decoder input
  authenticatedSource :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
      ExactAuthenticatedQueryBatchSourceBinding
        (run sample input).execution
        (exactK13ParsedProof input).queries
        (exactOperationalChallenge input .queryBatch)
        (exactTag73K13AuthenticatedQueryVector decoder input k12)

/-- The same raw query-insertion facts, in the legacy operational record
shape consumed by K1.5.  This conversion adds no query-consistency premise.
-/
theorem ExactTag73RelationSourceEnvironment.operationalQuerySource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactTag73RelationSourceEnvironment transitionFuel configuration
      projection fixedInstance decoder)
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) :
    ExactQueryInjectionSourceBinding (source.run sample input).execution
      (exactK13ParsedProof input).queries
      (exactOperationalChallenge input .queryBatch)
      (exactTag73K13AuthenticatedQueryVector decoder input k12) :=
  (source.authenticatedSource sample input k12).toOperationalSourceBinding

/-- Exact construction of the corrected K1.3 source obligations from the
literal parsed setup, shifted query insertion, and accepted relation tail.
No cryptographic/probability conclusion is introduced by this composition.
-/
noncomputable def ExactTag73RelationSourceEnvironment.toK13SourceObligations
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73RelationSourceEnvironment transitionFuel configuration
      projection fixedInstance decoder) :
    ExactTag73K13SourceObligations transitionFuel configuration projection
      fixedInstance decoder where
  execution := fun sample input => (source.run sample input).execution
  preQueryDiscrepancy := fun sample input =>
    AspisK1.V7Tag73BatchedQuerySourceBridge.preQueryDiscrepancy
      (source.run sample input).execution
  preQueryDiscrepancyExact := by
    intro sample input
    rfl
  beforeOneExact := by
    intro sample input k12
    let run := source.run sample input
    have exactSource :=
      before_one_eq_joint_discrepancy_of_authenticated_source
        (source.authenticatedSource sample input k12)
    rw [run.expectedQueryVectorExact k12]
    exact exactSource
  relationTerminal := by
    intro sample input
    exact (source.run sample input).tail.relationTerminal
  alphaExact := by
    intro sample input round
    exact (source.run sample input).alphaExact round

#print axioms ExactAcceptedRelationTailSourceTrace.toTerminalSourceTrace
#print axioms ExactAcceptedRelationTailSourceTrace.relationTerminal
#print axioms ExactAcceptedTag73RelationSourceRun.alphaExact
#print axioms ExactAcceptedTag73RelationSourceRun.parsedDisclosedFinalExact
#print axioms ExactAcceptedTag73RelationSourceRun.expectedQueryVectorExact
#print axioms ExactTag73RelationSourceEnvironment.operationalQuerySource
#print axioms ExactTag73RelationSourceEnvironment.toK13SourceObligations

end

end AspisK1.V7Tag73RelationTailSourceComposition
