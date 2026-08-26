import AspisFormal.Pool.V7AcceptedSpendRelationCapstone

/-!
# Accepted Tag-73 spend witness or exact Copy LogUp failure

This total wrapper removes the two Copy LogUp exclusions from the complete
spend-relation API.  An accepted deployed-row execution either has the exact
public spend witness or returns one of the two typed isolation failures for
the probability ledger.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace AspisPool.V7AcceptedSpendFailureDisjunction

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendRelationCapstone
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV5ProductionPublicResidualBinding
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

/-- An accepted deployed-row execution either has a witness for the complete
public spend statement or lies in one of the two exact Copy LogUp isolation
failure events.  No sampled-challenge goodness is assumed by this theorem. -/
theorem acceptedDeployedRows_implies_statementHasSpendWitness_or_copyFailure
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
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
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (execution : CandidateExecution QM31Exact)
    (lambda chi : QM31Exact)
    (helper : Fin 1024 → QM31Exact)
    (accepted : AcceptedDeployedCopyLaneConsequence statement masks fields
      extraction point kappa execution
        (deployedPoseidonRows rc (extractedPhysicalTrace extraction))
        lambda chi helper) :
    StatementHasSpendWitness statement deployedOwner deployedNote
        deployedNullifier deployedNode ∨
      CopyChiCollision
        (concreteDeployedCopyRegistryProjection extraction) lambda chi ∨
      CopyTupleCompressionCollision
        (concreteDeployedCopyRegistryProjection extraction) lambda := by
  classical
  by_cases noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi
  · by_cases noCompressionCollision : ¬ CopyTupleCompressionCollision
        (concreteDeployedCopyRegistryProjection extraction) lambda
    · exact Or.inl
        (acceptedDeployedRows_implies_statementHasSpendWitness rc poseidon
          statement masks fields extraction point kappa execution lambda chi
          helper accepted noChiCollision noCompressionCollision)
    · exact Or.inr (Or.inr (not_not.mp noCompressionCollision))
  · exact Or.inr (Or.inl (not_not.mp noChiCollision))

#print axioms
  acceptedDeployedRows_implies_statementHasSpendWitness_or_copyFailure

end AspisPool.V7AcceptedSpendFailureDisjunction
