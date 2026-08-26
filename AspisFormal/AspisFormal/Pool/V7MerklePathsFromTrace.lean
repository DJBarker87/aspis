import AspisFormal.Pool.V7MerkleLevelFromTrace

/-!
# Full Tag-73 same-path Merkle witnesses from the physical trace

The boundary digest at level `n` is the final row immediately preceding path
block `n`.  Input boundaries are rows `59 + 16n`; output boundary zero is the
output commitment at row 779 and later boundaries are rows `379 + 16n`.
This file composes the forty typed levels into the two twenty-level paths while
sharing exactly the decoded path bits and sibling digests in `OpenedColumns`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7MerklePathsFromTrace

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyPathCurrentClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7MerkleLevelFromTrace
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PoseidonRowsFromTrace
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV5ProductionPublicResidualBinding
open AspisV6OneFoldCandidateExtraction

/-- Boundary digests are only semantically used at indices zero through 20;
the totalized tail is canonical zero. -/
def selectedPathBoundaryDigest
    (trace : PhysicalTrace) (output : Bool) (index : Nat) : Digest :=
  if bound : index ≤ 20 then
    if output then
      if index = 0 then lowDigestAt trace 779
      else lowDigestAt trace ⟨379 + 16 * index, by omega⟩
    else lowDigestAt trace ⟨59 + 16 * index, by omega⟩
  else fun _ => 0

@[simp] theorem selectedPathBoundaryDigest_input_zero (trace : PhysicalTrace) :
    selectedPathBoundaryDigest trace false 0 = lowDigestAt trace 59 := by
  simp [selectedPathBoundaryDigest]

@[simp] theorem selectedPathBoundaryDigest_output_zero (trace : PhysicalTrace) :
    selectedPathBoundaryDigest trace true 0 = lowDigestAt trace 779 := by
  simp [selectedPathBoundaryDigest]

@[simp] theorem selectedPathBoundaryDigest_input_twenty (trace : PhysicalTrace) :
    selectedPathBoundaryDigest trace false 20 = lowDigestAt trace 379 := by
  simp [selectedPathBoundaryDigest]

@[simp] theorem selectedPathBoundaryDigest_output_twenty (trace : PhysicalTrace) :
    selectedPathBoundaryDigest trace true 20 = lowDigestAt trace 699 := by
  simp [selectedPathBoundaryDigest]

theorem selectedPathBoundaryDigest_at_level
    (trace : PhysicalTrace) (level : Fin 20) (output : Bool) :
    selectedPathBoundaryDigest trace output level.val =
      lowDigestAt trace
        (if output then outputPathFinalRow level else inputPathFinalRow level) := by
  cases output with
  | false =>
      simp [selectedPathBoundaryDigest, inputPathFinalRow]
  | true =>
      by_cases first : level.val = 0
      · simp [selectedPathBoundaryDigest, outputPathFinalRow, first]
      · simp [selectedPathBoundaryDigest, outputPathFinalRow, first]

theorem selectedPathBoundaryDigest_succ_level
    (trace : PhysicalTrace) (level : Fin 20) (output : Bool) :
    selectedPathBoundaryDigest trace output (level.val + 1) =
      truncate8 (blockFinalState trace (selectedPathBlock level output)) := by
  funext limb
  cases output with
  | false =>
      simp [selectedPathBoundaryDigest, truncate8, blockFinalState, stateAt,
        selectedPathBlock, lowDigestAt]
      congr 2
      ring
  | true =>
      simp [selectedPathBoundaryDigest, truncate8, blockFinalState, stateAt,
        selectedPathBlock, lowDigestAt]
      congr 2
      ring

theorem selectedPathBoundary_current_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (level : Fin 20) (output : Bool) :
    selectedPathBoundaryDigest (extractedPhysicalTrace extraction)
        output level.val =
      pathDigestAt (extractedPhysicalTrace extraction)
        (selectedPathCurrentRow level output) := by
  rw [selectedPathBoundaryDigest_at_level]
  cases output with
  | false =>
      exact inputPathCurrent_exact_of_tagged_multisets_equal
        extraction taggedEqual level
  | true =>
      exact outputPathCurrent_exact_of_tagged_multisets_equal
        extraction taggedEqual level

/-! ## Complete input path -/

def inputMerklePathOfTrace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (rc : RoundConstants)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (poseidonVanish : DeployedPoseidonRowsVanish rc
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (binary : PathBitsAreBinary
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction))) :
    ExtractedMerklePath rc
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).L_in
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).A
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).bits
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).sib := by
  let trace := extractedPhysicalTrace extraction
  let opened := openedColumnsFromTrace trace fee
  refine {
    current := selectedPathBoundaryDigest trace false
    startResidual := ?_
    finishResidual := ?_
    level := ?_
  }
  · exact sub_self _
  · exact sub_self _
  · intro level
    have typed := extractedMerkleLevelOfTrace rc extraction fee fields
      semanticVanish poseidonVanish taggedEqual binary level false
    have currentExact := selectedPathBoundary_current_exact
      extraction taggedEqual level false
    have nextExact := selectedPathBoundaryDigest_succ_level trace level false
    rw [← currentExact, ← nextExact] at typed
    simpa [trace, opened, openedColumnsFromTrace, completeOpenedColumns,
      decodedOpenedCore, rawOpenedColumnsFromTrace] using typed

/-! ## Complete output path, sharing the same `bits` and `sib` fields -/

def outputMerklePathOfTrace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (rc : RoundConstants)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee) (fields : TerminalSpendFields)
    (semanticVanish : AtomicSemanticRowsVanish fields
      (extractedPhysicalTrace extraction))
    (poseidonVanish : DeployedPoseidonRowsVanish rc
      (extractedPhysicalTrace extraction))
    (taggedEqual :
      producerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction) =
        consumerTaggedMultiset
          (concreteDeployedCopyRegistryProjection extraction))
    (binary : PathBitsAreBinary
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction))) :
    ExtractedMerklePath rc
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).C_out
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).A'
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).bits
      (openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).sib := by
  let trace := extractedPhysicalTrace extraction
  let opened := openedColumnsFromTrace trace fee
  refine {
    current := selectedPathBoundaryDigest trace true
    startResidual := ?_
    finishResidual := ?_
    level := ?_
  }
  · exact sub_self _
  · exact sub_self _
  · intro level
    have typed := extractedMerkleLevelOfTrace rc extraction fee fields
      semanticVanish poseidonVanish taggedEqual binary level true
    have currentExact := selectedPathBoundary_current_exact
      extraction taggedEqual level true
    have nextExact := selectedPathBoundaryDigest_succ_level trace level true
    rw [← currentExact, ← nextExact] at typed
    simpa [trace, opened, openedColumnsFromTrace, completeOpenedColumns,
      decodedOpenedCore, rawOpenedColumnsFromTrace] using typed

#print axioms selectedPathBoundaryDigest_at_level
#print axioms selectedPathBoundaryDigest_succ_level
#print axioms selectedPathBoundary_current_exact
#print axioms inputMerklePathOfTrace
#print axioms outputMerklePathOfTrace

end AspisPool.V7MerklePathsFromTrace
