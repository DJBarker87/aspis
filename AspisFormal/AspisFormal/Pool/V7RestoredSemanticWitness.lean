import AspisFormal.Pool.V7K15FixedFamilyCausalCover
import AspisFormal.Pool.V7DeterministicSpendWitness

/-!
# Restored point-compatible trace to a valid spend witness

This module closes the deterministic mathematical part of the restored K1.5
handoff.  Once K1.4 supplies all 87 point claims for one coherent restored
trace, and none of the eight fixed-family K1.5 failures occurs, the ordinary
accepted semantic/relation endpoint cannot take any of its thirteen failure
branches.  Its literal decoded witness therefore satisfies the public spend
relation.

The theorem deliberately says nothing about the concrete restoration client.
Showing that the fixed finite client returns an extractor which recovers this
witness from its actual accumulator is a separate operational obligation.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

namespace AspisPool.V7RestoredSemanticWitness

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7AcceptedSpendRelationCapstone
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PointClaimBatchBinding
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7SelectedSemanticPointClaims
open AspisPool.V7Tag73InactiveHelperAggregate
open AspisPool.V7Width29ComponentExtraction
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15FixedFamilyCausalCover
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge
open AspisV5SequentialTerminalChallengeBound
open AspisV5SumcheckTranscriptBinding
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

noncomputable section

/-- The deterministic restored-trace endpoint.  The hypotheses before
`fixedMember` are exactly the accepted semantic/relation source facts.  The
last five hypotheses place the restored trace in the pre-challenge fixed
family and exclude that complete family. -/
theorem accepted_restored_trace_implies_decoded_witness_valid
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
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
    (fields : FixedFieldView QM31Exact)
    (transcript : AcceptedRun scheme)
    (compact : CompactAcceptedRunEvidence fields transcript)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (lambda chi theta : QM31Exact)
    (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle transcript.eta
        (extractedUnmaskedSemanticTable basis statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper)
          theta zerocheckPoint mu helper)
        mask)
      transcript.point)
    (maskInitialExact : fields.initialClaim = tableSum mask)
    (terminalOpeningExact : semanticTerminalClaim fields transcript.point =
      claimAtStep
        (tableSum
          (maskedOracle transcript.eta
            (extractedUnmaskedSemanticTable basis statement extraction
              (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
              (deployedCompiledCopyLane
                (concreteDeployedCopyRegistryProjection extraction)
                lambda chi helper)
              theta zerocheckPoint mu helper)
            mask))
        honest.messages transcript.point (Fin.last 10))
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (executionInitialValues : execution.initialValues = extraction.combined.1)
    (executionInitialWeights : execution.initialWeights =
      extractedInitialRelationWeights masks transcript.point kappa)
    (executionInitialClaim : execution.initialClaim =
      relationClaimBeforeOod fields gamma kappa)
    (inactiveExact : fields.inactiveClaim =
      inactiveClaim masks extraction.combined.1)
    (finalMatches : execution.Final256Matches)
    (queryExact : execution.QueryInjectionExact)
    (relationTerminal : execution.RelationTerminalAccepts)
    (fixedMember : extraction.components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words))
    (terminal : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder
      (extractedWidth29InitialWords words) → AdaptiveDegree27MessagePlan QM31Exact)
    (terminalExact : terminal
      (extractedFixedWidth29Candidate extraction fixedMember) =
        extractedFixedTerminalPlan basis rc statement extraction lambda chi helper)
    (sumcheckCausal : WireUsesAdaptiveDegree27Plan
      (acceptedProductionWireOfCompact fields transcript compact) honest
      (sumcheck (extractedFixedWidth29Candidate extraction fixedMember)))
    (allPointClaimsExact : ∀ row lane,
      fields.pointClaim row lane =
        componentPointClaim extraction transcript.point row lane)
    (noFixedFailure : ¬ FixedFamilyK15Failure terminal sumcheck fields
      extraction zerocheckPoint transcript.point lambda chi theta mu kappa
      execution) :
    let witness := decodeTag73SpendWitness statement extraction
    OpenedColumnsMatchStatement statement witness.opened ∧
      SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
        witness.opened witness.inputValue witness.outputValue := by
  have classified :=
    accepted_semantic_relation_implies_decoded_witness_or_causal_k15_failure
      basis rc poseidon statement masks fields transcript compact extraction
      lambda chi theta zerocheckPoint mu helper mask honest maskInitialExact
      terminalOpeningExact inactiveSumZero kappa execution initialEncoderEq
      executionInitialValues executionInitialWeights executionInitialClaim
      inactiveExact finalMatches queryExact relationTerminal
  rcases classified with valid | failure
  · exact valid
  · exact (noFixedFailure
      (failureEvidence_implies_fixedFamilyK15Failure basis rc statement fields
        transcript compact extraction lambda chi theta zerocheckPoint mu helper
        mask honest kappa execution fixedMember terminal sumcheck terminalExact
        sumcheckCausal allPointClaimsExact failure.toFailureEvidence)).elim

#print axioms accepted_restored_trace_implies_decoded_witness_valid

end

end AspisPool.V7RestoredSemanticWitness
