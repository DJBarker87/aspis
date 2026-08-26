import AspisFormal.Pool.V7AcceptedSpendRelationCapstone

/-!
# Complete deterministic K1.5 spend-failure ledger

This module removes every sampled-challenge exclusion from the accepted
semantic/relation-to-spend composition.  Given the deterministic transcript,
opening, helper-support and candidate-execution bindings, acceptance yields
either the exact public spend witness or one of thirteen typed K1.5 events.
Probability accounting remains a separate layer over this exhaustive result.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisPool.V7AcceptedSpendK15FailureLedger

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendRelationCapstone
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
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
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5ConstraintLaneBatching
open AspisV5FriRelationCandidateBridge
open AspisV5ProductionPublicResidualBinding
open AspisV5SumcheckTranscriptBinding
open AspisV5TowerPackedResidualExtraction
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29CorrelatedAgreement

/-- Stable event identifiers for the deterministic K1.5 ledger. -/
inductive FailureKind where
  | tenRoundRepair
  | helperCancellation
  | zerocheckEvaluation
  | thetaLane
  | muZero
  | inactiveChi
  | activePole
  | copyChi
  | tupleCompression
  | oodMix
  | relationAlpha
  | kappaPointRow
  | gammaPointLane
  deriving DecidableEq, Repr, Fintype

theorem failureKind_card : Fintype.card FailureKind = 13 := by decide

/-- One witnessed event selected from an exact context-dependent event map. -/
def FailureEvidence (event : FailureKind → Prop) : Prop :=
  ∃ kind, event kind

/-- Proof-relevant causal form of the ledger.  Only the final gamma branch
needs predecessor information downstream: reaching it means the relation OOD,
relation-alpha and kappa-row branches were already ruled out. -/
def CausalFailureEvidence (event : FailureKind → Prop) : Prop :=
  ∃ kind, event kind ∧
    (kind = .gammaPointLane →
      ¬ event .oodMix ∧ ¬ event .relationAlpha ∧
        ¬ event .kappaPointRow)

theorem CausalFailureEvidence.toFailureEvidence
    {event : FailureKind → Prop}
    (failure : CausalFailureEvidence event) : FailureEvidence event := by
  rcases failure with ⟨kind, holds, _clear⟩
  exact ⟨kind, holds⟩

theorem causalFailureEvidence_of_nonGamma
    {event : FailureKind → Prop} {kind : FailureKind}
    (notGamma : kind ≠ .gammaPointLane) (holds : event kind) :
    CausalFailureEvidence event := by
  exact ⟨kind, holds, fun equal => (notGamma equal).elim⟩

/-- The thirteen exact predicates omitted by no deterministic step.  Their
order is fixed by `FailureKind`, avoiding an opaque nested disjunction. -/
def failureEvent
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    (statement : V5PublicStatement)
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
    (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact) : FailureKind → Prop
  | .tenRoundRepair =>
      TenRoundRepair
        (acceptedProductionWireOfCompact fields transcript compact) honest
  | .helperCancellation =>
      HelperCancellation basis
        (extractedConstraintRows statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper))
        theta zerocheckPoint mu helper
  | .zerocheckEvaluation =>
      ZerocheckEvaluationCollision basis
        (extractedConstraintRows statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper))
        theta zerocheckPoint
  | .thetaLane =>
      ThetaLaneCollision basis
        (extractedConstraintRows statement extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection extraction)
            lambda chi helper))
        theta
  | .muZero => mu = 0
  | .inactiveChi => DeployedCopyInactiveSlotCollision chi
  | .activePole => DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi
  | .copyChi => CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi
  | .tupleCompression => CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda
  | .oodMix => execution.discrepancyTrace.MixCancellation 0
  | .relationAlpha => ∃ round : Fin 4,
      execution.discrepancyTrace.AlphaRepair round
  | .kappaPointRow => KappaPointRowCollision fields extraction
      transcript.point kappa
  | .gammaPointLane => GammaPointLaneCollision fields extraction transcript.point

/-- Complete deterministic K1.5 endpoint.  All positive premises are exact
data/refinement facts supplied by the transcript, PCS, helper builder and
candidate extractor.  No sampled-challenge goodness premise remains. -/
theorem accepted_semantic_relation_implies_spend_witness_or_causal_k15_failure
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
    (relationTerminal : execution.RelationTerminalAccepts) :
    StatementHasSpendWitness statement deployedOwner deployedNote
        deployedNullifier deployedNode ∨
      CausalFailureEvidence (failureEvent basis rc statement fields transcript compact
        extraction lambda chi theta zerocheckPoint mu helper mask honest kappa
        execution) := by
  classical
  let event := failureEvent basis rc statement fields transcript compact
    extraction lambda chi theta zerocheckPoint mu helper mask honest kappa
    execution
  by_cases repair : event .tenRoundRepair
  · exact Or.inr (causalFailureEvidence_of_nonGamma (by decide) repair)
  by_cases helperCollision : event .helperCancellation
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) helperCollision)
  by_cases zerocheckCollision : event .zerocheckEvaluation
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) zerocheckCollision)
  by_cases thetaCollision : event .thetaLane
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) thetaCollision)
  by_cases muZero : event .muZero
  · exact Or.inr (causalFailureEvidence_of_nonGamma (by decide) muZero)
  by_cases inactiveChi : event .inactiveChi
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) inactiveChi)
  by_cases activePole : event .activePole
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) activePole)
  by_cases copyChi : event .copyChi
  · exact Or.inr (causalFailureEvidence_of_nonGamma (by decide) copyChi)
  by_cases tupleCompression : event .tupleCompression
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) tupleCompression)
  by_cases oodMix : event .oodMix
  · exact Or.inr (causalFailureEvidence_of_nonGamma (by decide) oodMix)
  by_cases relationAlpha : event .relationAlpha
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) relationAlpha)
  by_cases kappaPointRow : event .kappaPointRow
  · exact Or.inr
      (causalFailureEvidence_of_nonGamma (by decide) kappaPointRow)
  by_cases gammaPointLane : event .gammaPointLane
  · exact Or.inr ⟨.gammaPointLane, gammaPointLane, fun _ =>
      ⟨oodMix, relationAlpha, kappaPointRow⟩⟩
  have noRelationAlpha : ∀ round : Fin 4,
      ¬ execution.discrepancyTrace.AlphaRepair round := by
    intro round repair
    exact relationAlpha ⟨round, repair⟩
  have accepted :=
    accepted_semantic_relation_deployed_copy_lane_consequence basis statement
      masks fields transcript compact extraction
      (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
      lambda chi theta zerocheckPoint mu helper mask honest maskInitialExact
      terminalOpeningExact repair helperCollision zerocheckCollision
      thetaCollision inactiveSumZero muZero inactiveChi activePole copyChi
      tupleCompression kappa execution initialEncoderEq executionInitialValues
      executionInitialWeights executionInitialClaim inactiveExact finalMatches
      queryExact relationTerminal oodMix noRelationAlpha kappaPointRow
      gammaPointLane
  exact Or.inl
    (acceptedDeployedRows_implies_statementHasSpendWitness rc poseidon statement
      masks fields extraction transcript.point kappa execution lambda chi helper
      accepted copyChi tupleCompression)

#print axioms failureKind_card
#print axioms CausalFailureEvidence.toFailureEvidence
#print axioms causalFailureEvidence_of_nonGamma
#print axioms
  accepted_semantic_relation_implies_spend_witness_or_causal_k15_failure

end AspisPool.V7AcceptedSpendK15FailureLedger
