import AspisFormal.Pool.V7AcceptedDeployedCopyLaneCapstone
import AspisFormal.Pool.V7HashBlocksFromTrace

/-!
# Accepted Tag-73 execution to the complete spend relation

This capstone specializes the accepted semantic oracle to the literal 49-block
Poseidon trace.  Outside the two sampled Copy LogUp collision events, its
global rational balance recovers the complete tagged endpoint multiset.  That
single equality now supplies scalar aliases, path bitness, forty Merkle levels,
and all nine typed owner/note/nullifier blocks.

The only hash boundary in the final theorem is the maintained
`Poseidon2Faithful` interface relating the typed round constants to the
deployed primitives.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7AcceptedSpendRelationCapstone

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyPathSelectionClosure
open AspisPool.V7HashBlocksFromTrace
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV5ProductionPublicResidualBinding
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

/-- The accepted deployed rows construct the complete normalized trace used
by the existing deterministic spend-relation theorem. -/
noncomputable def extractedV5TraceOfAcceptedDeployedRows
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (rc : RoundConstants)
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
        lambda chi helper)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda) :
    ExtractedV5Trace rc
      (openedColumnsFromTrace (extractedPhysicalTrace extraction)
        (boundedFeeFromStatement statement)) := by
  let source := concreteDeployedCopyRegistryProjection extraction
  have compressedEqual := compressed_multisets_equal_outside_chi_collision
    source lambda chi accepted.rationalBalance noChiCollision
  have taggedEqual := tagged_multisets_equal_outside_compression_collision
    source lambda compressedEqual noCompressionCollision
  have binary := pathBitsAreBinary_of_tagged_multisets_equal
    extraction taggedEqual
  have hashAndMerkle := extractedHashMerkleResidualsOfTrace rc extraction
    (boundedFeeFromStatement statement) (terminalSpendFields statement)
    accepted.semanticRelation.rows.semantic
    accepted.semanticRelation.rows.poseidon taggedEqual binary
  exact {
    arithmetic := accepted.semanticRelation.arithmetic
    hashAndMerkle := hashAndMerkle
  }

/-- Outside the explicit Copy LogUp collision events, an accepted Tag-73
deployed-row execution has a witness for the exact public spend statement.
Poseidon implementation faithfulness remains the named external boundary. -/
theorem acceptedDeployedRows_implies_statementHasSpendWitness
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
        lambda chi helper)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda) :
    StatementHasSpendWitness statement deployedOwner deployedNote
      deployedNullifier deployedNode := by
  have trace := extractedV5TraceOfAcceptedDeployedRows rc statement masks fields
    extraction point kappa execution lambda chi helper accepted
    noChiCollision noCompressionCollision
  obtain ⟨inputValue, outputValue, relation⟩ :=
    extracted_trace_implies_spend_relation rc
      (openedColumnsFromTrace (extractedPhysicalTrace extraction)
        (boundedFeeFromStatement statement)) poseidon trace
  exact ⟨openedColumnsFromTrace (extractedPhysicalTrace extraction)
      (boundedFeeFromStatement statement), inputValue, outputValue,
    accepted.semanticRelation.publicFields, relation⟩

#print axioms extractedV5TraceOfAcceptedDeployedRows
#print axioms acceptedDeployedRows_implies_statementHasSpendWitness

end AspisPool.V7AcceptedSpendRelationCapstone
