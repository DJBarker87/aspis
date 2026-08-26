import AspisFormal.Pool.V7DeployedCopyPathSelectionClosure
import AspisFormal.Pool.V7PoseidonRowsFromTrace

/-!
# Constructing Tag-73 Merkle levels from the exact trace

This leaf projects the proved path-selection tuple matchings into the M31
trace.  The resulting left and right children are the literal node-block
sources: low lanes from local absorption row 12, and high lanes from local row
zero after removing the fixed node tweak in the last lane.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7MerkleLevelFromTrace

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7DeployedCopyPathSelectionClosure
open AspisPool.V7ExtractedCopyAliasBridge
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PoseidonRowsFromTrace
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV5ProductionPublicResidualBinding
open AspisV6OneFoldCandidateExtraction

/-- The left child is stored in the low eight lanes of local row 12. -/
def selectedPathLeftDigest
    (trace : PhysicalTrace) (level : Fin 20) (output : Bool) : Digest :=
  lowDigestAt trace (selectedPathLeftRow level output)

/-- The high-lane row stores the right child with `NODE_TWEAK` already added
to lane 15.  Pattern 14 adds its M31 negative to recover the typed digest. -/
def selectedPathRightDigest
    (trace : PhysicalTrace) (level : Fin 20) (output : Bool) : Digest :=
  fun limb =>
    trace (selectedPathRightRow level output) ⟨8 + limb.val, by omega⟩ +
      if limb.val = 7 then (1051521018 : F) else 0

/-- Path blocks 4--23 are input levels and blocks 24--43 are output levels. -/
def selectedPathBlock (level : Fin 20) (output : Bool) : PoseidonBlock :=
  if output then ⟨24 + level.val, by omega⟩ else ⟨4 + level.val, by omega⟩

def selectedPathInitialIndex (level : Fin 20) (output : Bool) : Fin 40 :=
  if output then ⟨20 + level.val, by omega⟩ else ⟨level.val, by omega⟩

@[simp] theorem selectedPathBlock_false (level : Fin 20) :
    (selectedPathBlock level false).val = 4 + level.val := rfl

@[simp] theorem selectedPathBlock_true (level : Fin 20) :
    (selectedPathBlock level true).val = 24 + level.val := rfl

theorem selectedPathRightRow_eq_block_zero
    (level : Fin 20) (output : Bool) :
    selectedPathRightRow level output =
      ⟨16 * (selectedPathBlock level output).val, by
        cases output <;> simp <;> omega⟩ := by
  apply Fin.ext
  cases output <;>
    simp [selectedPathRightRow, inputPathRightRow, outputPathRightRow] <;>
    omega

theorem selectedPathLeftRow_eq_block_twelve
    (level : Fin 20) (output : Bool) :
    selectedPathLeftRow level output =
      ⟨16 * (selectedPathBlock level output).val + 12, by
        cases output <;> simp <;> omega⟩ := by
  apply Fin.ext
  cases output <;>
    simp [selectedPathLeftRow, inputPathLeftRow, outputPathLeftRow] <;>
    omega

theorem selectedPathRightRow_eq_pathInitialRow
    (level : Fin 20) (output : Bool) :
    selectedPathRightRow level output =
      pathInitialRow (selectedPathInitialIndex level output) := by
  apply Fin.ext
  cases output <;>
    simp [selectedPathRightRow, selectedPathInitialIndex,
      inputPathRightRow, outputPathRightRow, pathInitialRow] <;>
    omega

theorem right_offset_cancels_node_tweak :
    (1051521018 : F) + NODE_TWEAK = 0 := by
  rw [NODE_TWEAK]
  change ((1051521018 : Nat) : F) + ((1095962629 : Nat) : F) = 0
  rw [← Nat.cast_add]
  change ((2147483647 : Nat) : ZMod 2147483647) = 0
  exact ZMod.natCast_self 2147483647

theorem initialResidual_at_pathInitialRow_low
    (trace : PhysicalTrace) (block : Fin 40) (column : Fin 16)
    (low : column.val < 8) :
    initialResidual trace (pathInitialRow block) column =
      trace (pathInitialRow block) column := by
  have noRetained : ∀ which : Fin 4,
      pathInitialRow block ≠ retainedInitialRow which := by
    intro which equal
    have values := congrArg Fin.val equal
    fin_cases which <;>
      simp [pathInitialRow, retainedInitialRow] at values <;> omega
  have pathEqual : ∀ other : Fin 40,
      pathInitialRow block = pathInitialRow other ↔ other = block := by
    intro other
    constructor
    · intro equal
      apply Fin.ext
      have values := congrArg Fin.val equal
      simp [pathInitialRow] at values
      omega
    · intro equal
      subst other
      rfl
  simp [initialResidual, low, noRetained, pathEqual]

theorem pathInitialLow_zero_of_semantic_rows_vanish
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace)
    (block : Fin 40) (column : Fin 16) (low : column.val < 8) :
    trace (pathInitialRow block) column = 0 := by
  have residual := coordinate_residual_zero_of_semantic_rows_vanish
    fields trace vanish (.initial column) (pathInitialRow block)
  rw [atomicSemanticResidual,
    initialResidual_at_pathInitialRow_low trace block column low] at residual
  exact residual

theorem selectedPathRightLow_zero_of_semantic_rows_vanish
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace)
    (level : Fin 20) (output : Bool) (lane : Fin 8) :
    trace (selectedPathRightRow level output) ⟨lane.val, by omega⟩ = 0 := by
  rw [selectedPathRightRow_eq_pathInitialRow]
  let column : Fin 16 := ⟨lane.val, by omega⟩
  have columnLow : column.val < 8 := by
    simp [column]
  exact pathInitialLow_zero_of_semantic_rows_vanish fields trace vanish
    (selectedPathInitialIndex level output) column columnLow

/-- The deployed row-zero plus row-twelve input is exactly the typed node
state.  This closes the subtle last-lane negative-tweak convention. -/
theorem absorbed_selected_path_block_eq_nodeState
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace)
    (level : Fin 20) (output : Bool) :
    absorbedBlockInput trace (selectedPathBlock level output) =
      nodeState NODE_TWEAK
        (selectedPathLeftDigest trace level output)
        (selectedPathRightDigest trace level output) := by
  funext lane
  have rightRow := selectedPathRightRow_eq_block_zero level output
  have leftRow := selectedPathLeftRow_eq_block_twelve level output
  by_cases low : lane.val < 8
  · let lowLane : Fin 8 := ⟨lane.val, low⟩
    have rowZero := selectedPathRightLow_zero_of_semantic_rows_vanish
      fields trace vanish level output lowLane
    have rowZeroLane :
        trace (selectedPathRightRow level output) lane = 0 := by
      have laneEq : lane = (⟨lowLane.val, by omega⟩ : Fin 16) := by
        apply Fin.ext
        simp [lowLane]
      rw [laneEq]
      exact rowZero
    unfold absorbedBlockInput nodeState
    rw [← rightRow, ← leftRow]
    simp [low, selectedPathLeftDigest, lowDigestAt, rowZeroLane]
  · have high : 8 ≤ lane.val := by omega
    unfold absorbedBlockInput nodeState
    rw [← rightRow]
    by_cases last : lane.val = 15
    · have laneEq : lane = (15 : Fin 16) := by
        apply Fin.ext
        exact last
      subst lane
      simp [selectedPathRightDigest, add_assoc,
        right_offset_cancels_node_tweak]
    · have notSeven : lane.val - 8 ≠ 7 := by omega
      simp [low, last, selectedPathRightDigest, notSeven]
      congr 1
      apply Fin.ext
      simp
      omega

theorem current_match_left_digest
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0)) :
    pathDigestAt (extractedPhysicalTrace extraction)
        (selectedPathCurrentRow level output) =
      selectedPathLeftDigest (extractedPhysicalTrace extraction) level output := by
  funext limb
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs
      ⟨1 + limb.val, by omega⟩) tupleEqual
  rw [deployedProducerTuple_pathSelect_current_limb,
    deployedConsumerTuple_pathSelect_left_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  have active : limb.val + 1 < 9 := by omega
  simpa [active, extractedSelectedTrace, pathDigestAt, selectedPathLeftDigest,
    lowDigestAt, Nat.add_comm] using baseEqual

theorem current_match_right_digest
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1)) :
    pathDigestAt (extractedPhysicalTrace extraction)
        (selectedPathCurrentRow level output) =
      selectedPathRightDigest (extractedPhysicalTrace extraction) level output := by
  funext limb
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs
      ⟨1 + limb.val, by omega⟩) tupleEqual
  rw [deployedProducerTuple_pathSelect_current_limb,
    deployedConsumerTuple_pathSelect_right_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  have offsetBase : ((1051521018 : QM31Exact).re.re) =
      (1051521018 : F) := rfl
  have offsetIfBase :
      ((if limb.val = 7 then (1051521018 : QM31Exact) else 0).re.re) =
        (if limb.val = 7 then (1051521018 : F) else 0) := by
    by_cases last : limb.val = 7 <;> simp [last, offsetBase]
  have active : limb.val + 1 < 9 := by omega
  simpa [active, extractedSelectedTrace, pathDigestAt, selectedPathRightDigest,
    offsetIfBase, Nat.add_assoc, Nat.add_comm] using baseEqual

theorem sibling_match_left_digest
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 0)) :
    pathDigestAt (extractedPhysicalTrace extraction) (siblingPathRow level) =
      selectedPathLeftDigest (extractedPhysicalTrace extraction) level output := by
  funext limb
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs
      ⟨1 + limb.val, by omega⟩) tupleEqual
  rw [deployedProducerTuple_pathSelect_sibling_limb,
    deployedConsumerTuple_pathSelect_left_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  have active : limb.val + 1 < 9 := by omega
  simpa [active, extractedSelectedTrace, pathDigestAt, selectedPathLeftDigest,
    lowDigestAt, Nat.add_comm] using baseEqual

theorem sibling_match_right_digest
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (level : Fin 20) (output : Bool)
    (tupleEqual :
      deployedProducerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1) =
        deployedConsumerTuple (extractedSelectedTrace extraction)
          (.pathSelect level output 1)) :
    pathDigestAt (extractedPhysicalTrace extraction) (siblingPathRow level) =
      selectedPathRightDigest (extractedPhysicalTrace extraction) level output := by
  funext limb
  have limbEqual := congrArg
    (fun tuple : TaggedCopyTuple QM31Exact => tuple.limbs
      ⟨1 + limb.val, by omega⟩) tupleEqual
  rw [deployedProducerTuple_pathSelect_sibling_limb,
    deployedConsumerTuple_pathSelect_right_limb] at limbEqual
  have baseEqual := congrArg (fun value : QM31Exact => value.re.re) limbEqual
  have offsetBase : ((1051521018 : QM31Exact).re.re) =
      (1051521018 : F) := rfl
  have offsetIfBase :
      ((if limb.val = 7 then (1051521018 : QM31Exact) else 0).re.re) =
        (if limb.val = 7 then (1051521018 : F) else 0) := by
    by_cases last : limb.val = 7 <;> simp [last, offsetBase]
  have active : limb.val + 1 < 9 := by omega
  simpa [active, extractedSelectedTrace, pathDigestAt, selectedPathRightDigest,
    offsetIfBase, Nat.add_assoc, Nat.add_comm] using baseEqual

/-- The exact deployed selection tuples imply both typed Merkle child
residuals for either input or output path. -/
theorem selected_path_child_residuals
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
    (binary : PathBitsAreBinary
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)))
    (level : Fin 20) (output : Bool) (lane : Fin 8) :
    selectedPathLeftDigest (extractedPhysicalTrace extraction) level output lane -
        (pathDigestAt (extractedPhysicalTrace extraction)
              (selectedPathCurrentRow level output) lane +
          (rawOpenedColumnsFromTrace
              (extractedPhysicalTrace extraction)).inputPathBits level *
            (pathDigestAt (extractedPhysicalTrace extraction)
                  (siblingPathRow level) lane -
              pathDigestAt (extractedPhysicalTrace extraction)
                (selectedPathCurrentRow level output) lane)) = 0 ∧
      selectedPathRightDigest (extractedPhysicalTrace extraction) level output lane -
        (pathDigestAt (extractedPhysicalTrace extraction)
              (siblingPathRow level) lane +
          (rawOpenedColumnsFromTrace
              (extractedPhysicalTrace extraction)).inputPathBits level *
            (pathDigestAt (extractedPhysicalTrace extraction)
                  (selectedPathCurrentRow level output) lane -
              pathDigestAt (extractedPhysicalTrace extraction)
                (siblingPathRow level) lane)) = 0 := by
  rcases pathSelect_pair_exact_of_binary_and_tagged_multisets_equal
      extraction taggedEqual binary level output with
    ⟨bitZero, currentToLeft, siblingToRight⟩ |
    ⟨bitOne, currentToRight, siblingToLeft⟩
  · have currentDigest := current_match_left_digest extraction
      level output currentToLeft
    have siblingDigest := sibling_match_right_digest extraction
      level output siblingToRight
    constructor
    · rw [bitZero]
      simp only [zero_mul, add_zero, sub_eq_zero]
      exact (congrFun currentDigest lane).symm
    · rw [bitZero]
      simp only [zero_mul, add_zero, sub_eq_zero]
      exact (congrFun siblingDigest lane).symm
  · have currentDigest := current_match_right_digest extraction
      level output currentToRight
    have siblingDigest := sibling_match_left_digest extraction
      level output siblingToLeft
    constructor
    · rw [bitOne]
      simp only [one_mul]
      apply sub_eq_zero.mpr
      calc
        selectedPathLeftDigest (extractedPhysicalTrace extraction)
            level output lane =
            pathDigestAt (extractedPhysicalTrace extraction)
              (siblingPathRow level) lane :=
          (congrFun siblingDigest lane).symm
        _ = pathDigestAt (extractedPhysicalTrace extraction)
                (selectedPathCurrentRow level output) lane +
              (pathDigestAt (extractedPhysicalTrace extraction)
                  (siblingPathRow level) lane -
                pathDigestAt (extractedPhysicalTrace extraction)
                  (selectedPathCurrentRow level output) lane) := by ring
    · rw [bitOne]
      simp only [one_mul]
      apply sub_eq_zero.mpr
      calc
        selectedPathRightDigest (extractedPhysicalTrace extraction)
            level output lane =
            pathDigestAt (extractedPhysicalTrace extraction)
              (selectedPathCurrentRow level output) lane :=
          (congrFun currentDigest lane).symm
        _ = pathDigestAt (extractedPhysicalTrace extraction)
                (siblingPathRow level) lane +
              (pathDigestAt (extractedPhysicalTrace extraction)
                  (selectedPathCurrentRow level output) lane -
                pathDigestAt (extractedPhysicalTrace extraction)
                  (siblingPathRow level) lane) := by ring

/-- One physical path block, with its Copy LogUp consequences, is exactly the
typed Merkle-level residual object consumed by the spend-relation proof. -/
def extractedMerkleLevelOfTrace
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (rc : RoundConstants)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (fee : BoundedFee)
    (fields : TerminalSpendFields)
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
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)))
    (level : Fin 20) (output : Bool) :
    ExtractedMerkleLevel rc
      ((openedColumnsFromTrace (extractedPhysicalTrace extraction) fee).bits level)
      (pathDigestAt (extractedPhysicalTrace extraction)
        (selectedPathCurrentRow level output))
      ((rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).siblings level)
      (truncate8 (blockFinalState (extractedPhysicalTrace extraction)
        (selectedPathBlock level output))) := by
  let trace := extractedPhysicalTrace extraction
  have childResidual := selected_path_child_residuals extraction taggedEqual
    binary level output
  have nodeInput := absorbed_selected_path_block_eq_nodeState
    fields trace semanticVanish level output
  have gate := twoRoundPermutationRowsOfVanish rc trace poseidonVanish
    (selectedPathBlock level output)
  rw [nodeInput] at gate
  have projects :=
    (openedColumnsFromTrace_projects_iff_path_bits_binary trace fee).2 binary
  refine {
    bit := (rawOpenedColumnsFromTrace trace).inputPathBits level
    bitCopyResidual := ?_
    left := selectedPathLeftDigest trace level output
    right := selectedPathRightDigest trace level output
    leftResidual := fun lane => (childResidual lane).1
    rightResidual := fun lane => (childResidual lane).2
    parentState := blockFinalState trace (selectedPathBlock level output)
    nodeGate := gate
    nextResidual := sub_self _
  }
  apply sub_eq_zero.mpr
  have bitExact := (projects.pathBitExact level).symm
  cases direction : (openedColumnsFromTrace trace fee).bits level <;>
    simpa [boolToField, direction] using bitExact

#print axioms current_match_left_digest
#print axioms current_match_right_digest
#print axioms sibling_match_left_digest
#print axioms sibling_match_right_digest
#print axioms selected_path_child_residuals
#print axioms right_offset_cancels_node_tweak
#print axioms pathInitialLow_zero_of_semantic_rows_vanish
#print axioms absorbed_selected_path_block_eq_nodeState
#print axioms extractedMerkleLevelOfTrace

end AspisPool.V7MerkleLevelFromTrace
