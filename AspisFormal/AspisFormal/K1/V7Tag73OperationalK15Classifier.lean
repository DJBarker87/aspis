import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.Pool.V7DeterministicSpendWitness

/-!
# Operational Tag-73 K1.5 classifier

This module specializes the deterministic K1.5 trace-to-witness theorem to
the literal fixed Tag-73 scheduler execution.  Every Fiat--Shamir challenge
passed to K1.5 is projected from the same accepted operational tape, and the
accepted semantic transcript is constructed by the exact compact replay.

The remaining positive arguments are the concrete source/layout facts for
the mask, helper and four-round relation evaluator.  They are kept
field-by-field so the Rust/Aeneas bridges have precise targets; no aggregate
"K1.5 accepted" premise is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73OperationalK15Classifier

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SemanticTranscriptBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7Tag73InactiveHelperAggregate
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5SumcheckTranscriptBinding
open AspisV6AcceptedPathObligations
open AspisV6TranscriptRelationGrammar

noncomputable section

def operationalFixedFields (decoded : Fin 641 → QM31Exact) :
    FixedFieldView QM31Exact :=
  decodedFixedFieldView decoded

def operationalSemanticPoint
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Fin 10 → QM31Exact :=
  fun round => exactOperationalChallenge input (.semantic round)

theorem operationalSemanticCertificate
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
    (decoded : Fin 641 → QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded) :
    ExactCompactSemanticReplay
      (semanticPreEtaOf (exactOperationalTable input)
        (exactOperationalTape input).messages)
      (exactOperationalChallenge input .eta)
      (operationalFixedFields decoded)
      (operationalSemanticPoint input) := by
  exact exact_operational_input_constructs_compact_semantic_replay input decoded
    fixedDecode

def operationalAcceptedRun
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
    (decoded : Fin 641 → QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded) :
    AcceptedRun tag73SemanticSchedule :=
  (operationalSemanticCertificate input decoded fixedDecode).acceptedRun

theorem operationalCompactEvidence
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
    (decoded : Fin 641 → QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded) :
    CompactAcceptedRunEvidence (operationalFixedFields decoded)
      (operationalAcceptedRun input decoded fixedDecode) :=
  (operationalSemanticCertificate input decoded fixedDecode).compactEvidence

/- The actual operational challenges and exact K1.4 extraction yield the
literal decoded spend witness, or one of the thirteen named K1.5 failure
events.  The source binding ensures that K1.4's gamma/final/q16 data are the
ones used by this same accepted execution. -/
set_option maxHeartbeats 5000000 in
-- The fully specialized dependent K1.5 endpoint needs additional elaboration fuel.
theorem operational_k14_implies_decoded_witness_or_k15_failure
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
    {k12 : ExactPrefixK12Certificate input}
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    (decoded : Fin 641 → QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded)
    (sourceBinding : ExactParsedProofSourceBinding input decoded)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (statement : V5PublicStatement)
    (masks : InactiveMasks)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle (operationalAcceptedRun input decoded fixedDecode).eta
        (extractedUnmaskedSemanticTable basis statement k14.extraction
          (deployedPoseidonRows rc
            (extractedPhysicalTrace k14.extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection k14.extraction)
            (exactOperationalChallenge input .lambda)
            (exactOperationalChallenge input .chi) helper)
          (exactOperationalChallenge input .theta)
          (fun coordinate => exactOperationalChallenge input
            (.zerocheckPoint coordinate))
          (exactOperationalChallenge input .mu) helper)
        mask)
      (operationalAcceptedRun input decoded fixedDecode).point)
    (maskInitialExact : (operationalFixedFields decoded).initialClaim =
      tableSum mask)
    (terminalOpeningExact :
      semanticTerminalClaim (operationalFixedFields decoded)
          (operationalAcceptedRun input decoded fixedDecode).point =
        claimAtStep
          (tableSum
            (maskedOracle (operationalAcceptedRun input decoded fixedDecode).eta
              (extractedUnmaskedSemanticTable basis statement k14.extraction
                (deployedPoseidonRows rc
                  (extractedPhysicalTrace k14.extraction))
                (deployedCompiledCopyLane
                  (concreteDeployedCopyRegistryProjection k14.extraction)
                  (exactOperationalChallenge input .lambda)
                  (exactOperationalChallenge input .chi) helper)
                (exactOperationalChallenge input .theta)
                (fun coordinate => exactOperationalChallenge input
                  (.zerocheckPoint coordinate))
                (exactOperationalChallenge input .mu) helper)
              mask))
          honest.messages
          (operationalAcceptedRun input decoded fixedDecode).point
          (Fin.last 10))
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (execution : CandidateExecution QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (executionInitialValues : execution.initialValues =
      k14.extraction.combined.1)
    (executionInitialWeights : execution.initialWeights =
      extractedInitialRelationWeights masks
        (operationalAcceptedRun input decoded fixedDecode).point
        (exactOperationalChallenge input .kappa))
    (executionInitialClaim : execution.initialClaim =
      relationClaimBeforeOod (operationalFixedFields decoded)
        (exactK13ParsedProof input).gamma
        (exactOperationalChallenge input .kappa))
    (inactiveExact : (operationalFixedFields decoded).inactiveClaim =
      inactiveClaim masks k14.extraction.combined.1)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (relationTerminal : execution.RelationTerminalAccepts) :
    ExactParsedProofSourceBinding input decoded ∧
      (let witness := decodeTag73SpendWitness statement k14.extraction
       (OpenedColumnsMatchStatement statement witness.opened ∧
        SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
          witness.opened witness.inputValue witness.outputValue) ∨
        CausalFailureEvidence
          (failureEvent basis rc statement (operationalFixedFields decoded)
            (operationalAcceptedRun input decoded fixedDecode)
            (operationalCompactEvidence input decoded fixedDecode)
            k14.extraction
            (exactOperationalChallenge input .lambda)
            (exactOperationalChallenge input .chi)
            (exactOperationalChallenge input .theta)
            (fun coordinate => exactOperationalChallenge input
              (.zerocheckPoint coordinate))
            (exactOperationalChallenge input .mu) helper mask honest
            (exactOperationalChallenge input .kappa) execution)) := by
  refine ⟨sourceBinding, ?_⟩
  exact accepted_semantic_relation_implies_decoded_witness_or_causal_k15_failure
      basis rc poseidon statement masks (operationalFixedFields decoded)
      (operationalAcceptedRun input decoded fixedDecode)
      (operationalCompactEvidence input decoded fixedDecode) k14.extraction
      (exactOperationalChallenge input .lambda)
      (exactOperationalChallenge input .chi)
      (exactOperationalChallenge input .theta)
      (fun coordinate => exactOperationalChallenge input
        (.zerocheckPoint coordinate))
      (exactOperationalChallenge input .mu) helper mask honest maskInitialExact
      terminalOpeningExact inactiveSumZero
      (exactOperationalChallenge input .kappa) execution initialEncoderEq
      executionInitialValues executionInitialWeights executionInitialClaim
      inactiveExact finalMatches queryExact relationTerminal

#print axioms operationalSemanticCertificate
#print axioms operationalAcceptedRun
#print axioms operationalCompactEvidence
#print axioms operational_k14_implies_decoded_witness_or_k15_failure

end

end AspisK1.V7Tag73OperationalK15Classifier
