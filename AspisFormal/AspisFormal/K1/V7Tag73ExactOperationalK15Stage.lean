import AspisFormal.K1.V7Tag73ExactConcreteStageAssembly
import AspisFormal.K1.V7Tag73OperationalClientExtractionBridge
import AspisFormal.K1.V7Tag73OperationalRelationSourceFacts

/-!
# Concrete operational K1.5 stage for exact Tag-73

This module fills the last abstract classifier slot in the concrete K1 stage
assembly.  For every literal K1.4 certificate, a source material record
contains only decoded production data, evaluator intermediates, exact
equalities and the restoration-client handoff.  The already proved
operational K1.5 theorem then returns either:

* the deterministic decoded spend witness, packaged as the actual extractor
  result of the completed restoration client; or
* one of the thirteen typed K1.5 failure events.

No aggregate acceptance proposition or numerical probability bound is a
field of this construction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactOperationalK15Stage

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73OperationalClientExtractionBridge
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73ExactConcreteStageAssembly
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

/-- Exact public relation extracted by K1.5. -/
def exactTag73SpendRelation
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (publicInstance : PublicInstance V5PublicStatement)
    (witness : DecodedSpendWitness) : Prop :=
  OpenedColumnsMatchStatement publicInstance.statement witness.opened ∧
    SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
      witness.opened witness.inputValue witness.outputValue

/-- Raw data returned by the accepted semantic and relation evaluators.  The
trace is stored against named table and point values; a separate
proposition-valued record proves that they are the operational values. -/
structure ExactTag73OperationalK15Data
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  decoded : Fin 641 → QM31Exact
  fixedDecode : FixedFieldDecodeExact
    (rawOfMessages (exactOperationalTape input).messages) decoded
  masks : InactiveMasks
  helper : Fin 1024 → QM31Exact
  mask : Fin 1024 → QM31Exact
  honestTable : Fin 1024 → QM31Exact
  honestPoint : Fin 10 → QM31Exact
  honest : FixedOracleTenRoundTrace honestTable honestPoint
  execution : CandidateExecution QM31Exact
  terminalSource : ExactRelationTerminalSourceTrace execution

/-- The exact operational table named by the accepted Tag-73 source. -/
def exactTag73OperationalTable
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    (data : ExactTag73OperationalK15Data input) : Fin 1024 → QM31Exact :=
  maskedOracle (operationalAcceptedRun input data.decoded data.fixedDecode).eta
    (extractedUnmaskedSemanticTable basis fixedInstance.statement k14.extraction
      (deployedPoseidonRows rc (extractedPhysicalTrace k14.extraction))
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection k14.extraction)
        (exactOperationalChallenge input .lambda)
        (exactOperationalChallenge input .chi) data.helper)
      (exactOperationalChallenge input .theta)
      (fun coordinate => exactOperationalChallenge input
        (.zerocheckPoint coordinate))
      (exactOperationalChallenge input .mu) data.helper)
    data.mask

/-- Transport a ten-round trace along literal table and point equalities. -/
def castFixedOracleTenRoundTrace
    {table expectedTable : Fin 1024 → QM31Exact}
    {point expectedPoint : Fin 10 → QM31Exact}
    (honest : FixedOracleTenRoundTrace table point)
    (tableExact : table = expectedTable)
    (pointExact : point = expectedPoint) :
    FixedOracleTenRoundTrace expectedTable expectedPoint := by
  subst expectedTable
  subst expectedPoint
  exact honest

/-- Literal evaluator equalities and authenticated openings.  This record is
proposition-valued and contains no selectable execution data. -/
structure ExactTag73OperationalK15SourceBinding
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    (data : ExactTag73OperationalK15Data input) : Prop where
  sourceBinding : ExactParsedProofSourceBinding input data.decoded
  honestTableExact : data.honestTable =
    exactTag73OperationalTable k14 basis rc data
  honestPointExact : data.honestPoint =
    (operationalAcceptedRun input data.decoded data.fixedDecode).point
  maskInitialExact : (operationalFixedFields data.decoded).initialClaim =
    tableSum data.mask
  terminalOpeningExact :
    semanticTerminalClaim (operationalFixedFields data.decoded)
        (operationalAcceptedRun input data.decoded data.fixedDecode).point =
      claimAtStep (tableSum (exactTag73OperationalTable k14 basis rc data))
        (castFixedOracleTenRoundTrace data.honest honestTableExact
          honestPointExact).messages
        (operationalAcceptedRun input data.decoded data.fixedDecode).point
        (Fin.last 10)
  inactiveSumZero : DeployedCopyHelperInactiveSumZero data.helper
  initialEncoderEq : decoder.initialEncoder = exactInitialEncoder
  executionInitialWeights : data.execution.initialWeights =
    extractedInitialRelationWeights data.masks
      (operationalAcceptedRun input data.decoded data.fixedDecode).point
      (exactOperationalChallenge input .kappa)
  executionInitialClaim : data.execution.initialClaim =
    relationClaimBeforeOod (operationalFixedFields data.decoded)
      (exactK13ParsedProof input).gamma
      (exactOperationalChallenge input .kappa)
  inactiveExact : (operationalFixedFields data.decoded).inactiveClaim =
    inactiveClaim data.masks k14.extraction.combined.1
  finalSource : ExactFinal256ExecutionBinding k14 data.decoded data.execution
  querySource : ExactQueryInjectionSourceBinding data.execution
    (exactK13ParsedProof input).queries
    (exactOperationalChallenge input .queryBatch)

/-- All literal per-run material needed by the operational K1.5 theorem. -/
structure ExactTag73OperationalK15Material
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k14 : ExactK14Certificate decoder decoderBinding input k12)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode) : Type where
  data : ExactTag73OperationalK15Data input
  source : ExactTag73OperationalK15SourceBinding k14 basis rc data
  clientExtractor : ExactPlainRomWitnessExtractor V5PublicStatement
    Tag73K12ParsedProof Payload DecodedSpendWitness
  clientReturned : input.package.root.full.clientRun.halt =
    .returned clientExtractor
  clientExtracts : clientExtractor
      input.package.root.full.clientRun.accumulator =
    some (decodeTag73SpendWitness fixedInstance.statement k14.extraction)

/-- The semantic trace after transport to the exact operational table and
point. -/
def ExactTag73OperationalK15Material.exactHonest
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {k14 : ExactK14Certificate decoder decoderBinding input k12}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (material : ExactTag73OperationalK15Material input k12 k14 basis rc
      poseidon) :
    FixedOracleTenRoundTrace
      (exactTag73OperationalTable k14 basis rc material.data)
      (operationalAcceptedRun input material.data.decoded
        material.data.fixedDecode).point :=
  castFixedOracleTenRoundTrace material.data.honest
    material.source.honestTableExact material.source.honestPointExact

/-- The exact typed error returned by the concrete K1.5 classifier.  The
proposition-level causal evidence is wrapped as data because the dependent
stage interface returns a `Sum` in `Type`. -/
structure ExactTag73OperationalK15Failure
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {k14 : ExactK14Certificate decoder decoderBinding input k12}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (material : ExactTag73OperationalK15Material input k12 k14 basis rc
      poseidon) : Type where
  evidence : CausalFailureEvidence
    (failureEvent basis rc fixedInstance.statement
      (operationalFixedFields material.data.decoded)
      (operationalAcceptedRun input material.data.decoded
        material.data.fixedDecode)
      (operationalCompactEvidence input material.data.decoded
        material.data.fixedDecode)
      k14.extraction
      (exactOperationalChallenge input .lambda)
      (exactOperationalChallenge input .chi)
      (exactOperationalChallenge input .theta)
      (fun coordinate => exactOperationalChallenge input
        (.zerocheckPoint coordinate))
      (exactOperationalChallenge input .mu) material.data.helper
      material.data.mask material.exactHonest
      (exactOperationalChallenge input .kappa) material.data.execution)

/-- A sample-indexed source of exact K1.5 material.  Construction of this
environment is the Rust/Aeneas and restoration-client bridge; its consumer
below is fully kernel checked. -/
structure ExactTag73OperationalK15Environment
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload)
    (fixedInstance : PublicInstance V5PublicStatement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode) : Type where
  material :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (_k13 : ExactK13Certificate decoder input k12)
      (k14 : ExactK14Certificate decoder decoderBinding input k12),
      ExactTag73OperationalK15Material input k12 k14 basis rc poseidon

set_option maxHeartbeats 5000000 in
/- The classifier normalizes the complete operational trace-to-witness
theorem.  It contains no user-selected success map and sends only a valid
decoded witness through the actual client handoff. -/
noncomputable def exactTag73OperationalK15Classifier
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload)
    (fixedInstance : PublicInstance V5PublicStatement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (environment : ExactTag73OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) :
    ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance
      (exactTag73SpendRelation (deployedOwner := deployedOwner)
        (deployedNote := deployedNote)
        (deployedNullifier := deployedNullifier)
        (deployedNode := deployedNode)) decoder decoderBinding where
  error := fun sample input k12 k13 k14 =>
    ExactTag73OperationalK15Failure
      (environment.material sample input k12 k13 k14)
  classify := by
    intro sample input k12 k13 k14
    let material := environment.material sample input k12 k13 k14
    have classified :=
      operational_k14_source_implies_decoded_witness_or_k15_failure input k14
        material.data.decoded material.data.fixedDecode
        material.source.sourceBinding basis rc poseidon fixedInstance.statement
        material.data.masks material.data.helper material.data.mask
        material.exactHonest material.source.maskInitialExact
        material.source.terminalOpeningExact material.source.inactiveSumZero
        material.data.execution material.source.initialEncoderEq
        material.source.executionInitialWeights
        material.source.executionInitialClaim material.source.inactiveExact
        material.source.finalSource material.source.querySource
        material.data.terminalSource
    have inhabitedResult : Nonempty
        (ExactFixedClientExtractionCertificate transitionFuel configuration
            fixedInstance
            (exactTag73SpendRelation (deployedOwner := deployedOwner)
              (deployedNote := deployedNote)
              (deployedNullifier := deployedNullifier)
              (deployedNode := deployedNode)) sample ⊕
          ExactTag73OperationalK15Failure material) := by
      rcases classified with ⟨_sourceExact, valid | failure⟩
      · exact ⟨.inl
          (exactFixedClientExtractionCertificateOfOperationalInput input
            material.clientExtractor
            (decodeTag73SpendWitness fixedInstance.statement k14.extraction)
            material.clientReturned material.clientExtracts valid)⟩
      · exact ⟨.inr ⟨failure⟩⟩
    exact Classical.choice inhabitedResult

#print axioms exactTag73SpendRelation
#print axioms ExactTag73OperationalK15Failure
#print axioms exactTag73OperationalK15Classifier

end

end AspisK1.V7Tag73ExactOperationalK15Stage
