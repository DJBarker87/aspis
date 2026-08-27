import AspisFormal.Pool.V7PairLeafOccupancy

/-!
# Exact V7 pair-tree trace geometry and degree headroom

This is the arithmetic gate for the proposed one-transaction pair-tree
relation.  It keeps the frozen 1,024-row / sixteen-column trace and allocates:

* 54 Poseidon blocks (864 rows), including historical pair membership and one
  live pair append;
* six auxiliary blocks for the exact four-level-per-block path layout used by
  the existing Pool trace, extended from 20 to 21 private directions;
* one value/conservation/occupancy auxiliary block;
* exactly 48 untouched rows.

The append path uses its Poseidon absorption/final rows directly.  Its cursor
bits and frontier/result values are public late-bound data, so it does not
consume a second private-path auxiliary region.

The degree inventory separately records that the new occupancy zero test,
empty-slot and child-selection residuals are at most quadratic.  The existing
two-round Poseidon residual remains the degree-25 maximum; the frozen selector
and outer zerocheck factors therefore retain the degree-27 cap.
-/

set_option autoImplicit false

namespace AspisPool.V7PairTreeTraceGeometry

def traceRows : Nat := 1024
def traceColumns : Nat := 16
def blockRows : Nat := 16
def twoRoundRowsPerPoseidonBlock : Nat := 11

def inputTreeDepth : Nat := 20
def pairMembershipHashBlocks : Nat := 1
def appendTreeDepth : Nat := 20
def appendPairHashBlocks : Nat := 1

def ownerBlocks : Nat := 1
def inputNoteBlocks : Nat := 3
def nullifierBlocks : Nat := 2
def recipientNoteBlocks : Nat := 3
def changeNoteBlocks : Nat := 3

def stableSpendPoseidonBlocks : Nat :=
  ownerBlocks + inputNoteBlocks + pairMembershipHashBlocks + inputTreeDepth +
    nullifierBlocks + recipientNoteBlocks + changeNoteBlocks +
    appendPairHashBlocks

def lateAppendPoseidonBlocks : Nat :=
  appendTreeDepth

def poseidonBlocks : Nat :=
  stableSpendPoseidonBlocks + lateAppendPoseidonBlocks

def privateMembershipDirections : Nat :=
  pairMembershipHashBlocks + inputTreeDepth

def directionsPerAuxBlock : Nat := 4
def membershipAuxBlocks : Nat :=
  (privateMembershipDirections + directionsPerAuxBlock - 1) /
    directionsPerAuxBlock
def valueAuxBlocks : Nat := 1
def auxiliaryBlocks : Nat := membershipAuxBlocks + valueAuxBlocks
def allocatedBlocks : Nat := poseidonBlocks + auxiliaryBlocks
def allocatedRows : Nat := allocatedBlocks * blockRows
def remainingRows : Nat := traceRows - allocatedRows

def pathAuxBlockStart : Nat := poseidonBlocks
def valueAuxBlock : Nat := pathAuxBlockStart + membershipAuxBlocks
def auxRowEnd : Nat := (valueAuxBlock + valueAuxBlocks) * blockRows

theorem exact_stable_and_late_poseidon_counts :
    stableSpendPoseidonBlocks = 34 ∧
      lateAppendPoseidonBlocks = 20 ∧
      poseidonBlocks = 54 := by
  decide

theorem exact_auxiliary_count :
    privateMembershipDirections = 21 ∧
      membershipAuxBlocks = 6 ∧
      auxiliaryBlocks = 7 := by
  decide

theorem exact_48_row_headroom :
    allocatedBlocks = 61 ∧
      allocatedRows = 976 ∧
      remainingRows = 48 := by
  decide

theorem exact_source_layout_block_boundaries :
    pathAuxBlockStart = 54 ∧
      membershipAuxBlocks = 6 ∧
      valueAuxBlock = 60 ∧
      auxRowEnd = 976 := by
  decide

theorem allocation_strictly_inside_frozen_trace : allocatedRows < traceRows := by
  decide

/-- Exact semantic role of each of the 54 one-permutation blocks. -/
inductive PoseidonBlockRole where
  | ownerKey
  | inputNote (permutation : Fin 3)
  | inputPair
  | inputTreePath (level : Fin 20)
  | nullifier (permutation : Fin 2)
  | recipientNote (permutation : Fin 3)
  | changeNote (permutation : Fin 3)
  | appendPair
  | appendTreePath (level : Fin 20)
  deriving DecidableEq

def poseidonBlockRole (block : Fin 54) : PoseidonBlockRole :=
  if h0 : block.val = 0 then .ownerKey
  else if h1 : block.val < 4 then .inputNote ⟨block.val - 1, by omega⟩
  else if h2 : block.val = 4 then .inputPair
  else if h3 : block.val < 25 then .inputTreePath ⟨block.val - 5, by omega⟩
  else if h4 : block.val < 27 then .nullifier ⟨block.val - 25, by omega⟩
  else if h5 : block.val < 30 then .recipientNote ⟨block.val - 27, by omega⟩
  else if h6 : block.val < 33 then .changeNote ⟨block.val - 30, by omega⟩
  else if h7 : block.val = 33 then .appendPair
  else .appendTreePath ⟨block.val - 34, by omega⟩

theorem first_late_append_block_exact :
    poseidonBlockRole ⟨33, by decide⟩ = .appendPair := by
  simp [poseidonBlockRole]

theorem final_poseidon_block_exact :
    poseidonBlockRole ⟨53, by decide⟩ = .appendTreePath ⟨19, by decide⟩ := by
  simp [poseidonBlockRole]

/-- Stage A can commit every expensive spend/output computation, including
the output-pair compression, before the live append snapshot is selected.
Only the twenty upper append nodes occupy the late Stage-B row interval. -/
def stableStagePoseidonRowEnd : Nat := stableSpendPoseidonBlocks * blockRows
def lateStagePoseidonRowStart : Nat := stableStagePoseidonRowEnd
def lateStagePoseidonRowEnd : Nat := poseidonBlocks * blockRows

theorem exact_staged_poseidon_row_boundary :
    stableStagePoseidonRowEnd = 544 ∧
      lateStagePoseidonRowStart = 544 ∧
      lateStagePoseidonRowEnd = 864 ∧
      lateStagePoseidonRowEnd - lateStagePoseidonRowStart = 320 := by
  decide

def poseidonRowStart : Nat := 0
def poseidonRowEnd : Nat := poseidonBlocks * blockRows
def membershipAuxRowStart : Nat := poseidonRowEnd
def membershipAuxRowEnd : Nat :=
  membershipAuxRowStart + membershipAuxBlocks * blockRows
def valueAuxRowStart : Nat := membershipAuxRowEnd
def valueAuxRowEnd : Nat := valueAuxRowStart + valueAuxBlocks * blockRows
def untouchedRowStart : Nat := valueAuxRowEnd

theorem exact_row_boundaries :
    poseidonRowEnd = 864 ∧
      membershipAuxRowStart = 864 ∧
      membershipAuxRowEnd = 960 ∧
      valueAuxRowStart = 960 ∧
      valueAuxRowEnd = 976 ∧
      untouchedRowStart = 976 := by
  decide

theorem regions_are_ordered_and_disjoint :
    poseidonRowStart ≤ poseidonRowEnd ∧
      poseidonRowEnd = membershipAuxRowStart ∧
      membershipAuxRowStart ≤ membershipAuxRowEnd ∧
      membershipAuxRowEnd = valueAuxRowStart ∧
      valueAuxRowStart ≤ valueAuxRowEnd ∧
      valueAuxRowEnd = untouchedRowStart ∧
      untouchedRowStart < traceRows := by
  decide

theorem untouched_rows_have_exact_cardinality :
    (Finset.Icc untouchedRowStart (traceRows - 1)).card = 48 := by
  decide

/-! ## Exact auxiliary placement

This mirrors the existing Pool V1 source layout rather than merely rounding a
row count.  Four path levels share each sixteen-row block.  Their base rows are
local rows `0,2,4,6`; ordered children use the successor row and the sibling
digest uses the existing `xor 12` view.  Extending 20 directions to the pair
side plus twenty upper levels therefore consumes exactly one additional path
block. -/

structure TraceCell where
  row : Nat
  column : Nat
  deriving DecidableEq

def pathBaseRow (level : Fin 21) : Nat :=
  (pathAuxBlockStart + level.val / directionsPerAuxBlock) * blockRows +
    2 * (level.val % directionsPerAuxBlock)

def pathSuccessorRow (level : Fin 21) : Nat := pathBaseRow level + 1
def pathSiblingRow (level : Fin 21) : Nat := Nat.xor (pathBaseRow level) 12

def pathBitCell (level : Fin 21) : TraceCell :=
  ⟨pathBaseRow level, 0⟩

def pathCurrentCell (level : Fin 21) (lane : Fin 8) : TraceCell :=
  ⟨pathBaseRow level, 1 + lane.val⟩

def pathLeftCell (level : Fin 21) (lane : Fin 8) : TraceCell :=
  ⟨pathSuccessorRow level, lane.val⟩

def pathRightCell (level : Fin 21) (lane : Fin 8) : TraceCell :=
  ⟨pathSuccessorRow level, 8 + lane.val⟩

def pathSiblingCell (level : Fin 21) (lane : Fin 8) : TraceCell :=
  ⟨pathSiblingRow level, lane.val⟩

theorem every_path_aux_row_is_exactly_inside_six_block_region :
    ∀ level : Fin 21,
      membershipAuxRowStart ≤ pathBaseRow level ∧
      pathBaseRow level < membershipAuxRowEnd ∧
      membershipAuxRowStart ≤ pathSuccessorRow level ∧
      pathSuccessorRow level < membershipAuxRowEnd ∧
      membershipAuxRowStart ≤ pathSiblingRow level ∧
      pathSiblingRow level < membershipAuxRowEnd := by
  decide

theorem every_path_aux_cell_is_inside_sixteen_columns :
    (∀ level : Fin 21, (pathBitCell level).column < traceColumns) ∧
      (∀ level : Fin 21, ∀ lane : Fin 8,
        (pathCurrentCell level lane).column < traceColumns ∧
        (pathLeftCell level lane).column < traceColumns ∧
        (pathRightCell level lane).column < traceColumns ∧
        (pathSiblingCell level lane).column < traceColumns) := by
  decide

def valueBaseRow (value : Fin 3) : Nat :=
  valueAuxRowStart + 2 * value.val

def valueSuccessorRow (value : Fin 3) : Nat := valueBaseRow value + 1
def valueSiblingRow (value : Fin 3) : Nat := Nat.xor (valueBaseRow value) 12
def conservationBaseRow : Nat := valueAuxRowStart + 6

/-- Input membership and output append need separate occupancy certificates.
Each row contains `(occupied, inverse, secondCommitment[0..8])`, making the
zero test and all eight empty-slot constraints row-local. -/
def inputOccupancyAuxRow : Nat := valueAuxRowStart + 9
def outputOccupancyAuxRow : Nat := valueAuxRowStart + 10

def inputOccupancyBitCell : TraceCell := ⟨inputOccupancyAuxRow, 0⟩
def inputOccupancyInverseCell : TraceCell := ⟨inputOccupancyAuxRow, 1⟩
def inputSecondCommitmentCell (lane : Fin 8) : TraceCell :=
  ⟨inputOccupancyAuxRow, 2 + lane.val⟩

def outputOccupancyBitCell : TraceCell := ⟨outputOccupancyAuxRow, 0⟩
def outputOccupancyInverseCell : TraceCell := ⟨outputOccupancyAuxRow, 1⟩
def outputSecondCommitmentCell (lane : Fin 8) : TraceCell :=
  ⟨outputOccupancyAuxRow, 2 + lane.val⟩

def existingValueAndConservationRows : Finset Nat :=
  ((Finset.univ.image valueBaseRow ∪
      Finset.univ.image valueSuccessorRow) ∪
      Finset.univ.image valueSiblingRow) ∪
    {conservationBaseRow, conservationBaseRow + 1}

theorem exact_value_and_occupancy_rows_inside_final_aux_block :
    (∀ value : Fin 3,
      valueAuxRowStart ≤ valueBaseRow value ∧
      valueBaseRow value < valueAuxRowEnd ∧
      valueAuxRowStart ≤ valueSuccessorRow value ∧
      valueSuccessorRow value < valueAuxRowEnd ∧
      valueAuxRowStart ≤ valueSiblingRow value ∧
      valueSiblingRow value < valueAuxRowEnd) ∧
    valueAuxRowStart ≤ inputOccupancyAuxRow ∧
      inputOccupancyAuxRow < valueAuxRowEnd ∧
      valueAuxRowStart ≤ outputOccupancyAuxRow ∧
      outputOccupancyAuxRow < valueAuxRowEnd := by
  decide

theorem occupancy_auxiliaries_are_distinct_and_do_not_alias_existing_value_rows :
    inputOccupancyAuxRow ≠ outputOccupancyAuxRow ∧
      inputOccupancyAuxRow ∉ existingValueAndConservationRows ∧
      outputOccupancyAuxRow ∉ existingValueAndConservationRows := by
  decide

theorem occupancy_commitment_cells_are_inside_sixteen_columns :
    (∀ lane : Fin 8, (inputSecondCommitmentCell lane).column < traceColumns) ∧
      (∀ lane : Fin 8, (outputSecondCommitmentCell lane).column < traceColumns) := by
  decide

/-! ## Literal polynomial degree of the new constraints -/

inductive PairResidualVariable where
  | occupied
  | sentinel
  | inverse
  | commitment (lane : Fin 8)
  | direction
  | current
  | sibling
  | ordered
  deriving DecidableEq

abbrev PairResidualPolynomial (K : Type) [CommSemiring K] :=
  MvPolynomial PairResidualVariable K

open MvPolynomial

noncomputable def occupancyBooleanityPolynomial
    (K : Type) [CommRing K] : PairResidualPolynomial K :=
  X .occupied * (X .occupied - 1)

noncomputable def occupancySentinelInversePolynomial
    (K : Type) [CommRing K] : PairResidualPolynomial K :=
  X .sentinel * X .inverse - X .occupied

noncomputable def emptySlotCanonicalityPolynomial
    (K : Type) [CommRing K] (lane : Fin 8) : PairResidualPolynomial K :=
  (1 - X .occupied) * X (.commitment lane)

noncomputable def selectedChildOrderingPolynomial
    (K : Type) [CommRing K] : PairResidualPolynomial K :=
  X .ordered -
    ((1 - X .direction) * X .current + X .direction * X .sibling)

theorem occupancyBooleanityPolynomial_totalDegree_le_two
    (K : Type) [CommRing K] [Nontrivial K] :
    (occupancyBooleanityPolynomial K).totalDegree ≤ 2 := by
  unfold occupancyBooleanityPolynomial
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have occupiedDegree :
      (X PairResidualVariable.occupied : PairResidualPolynomial K).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree_X]
  have shiftedDegree :
      ((X PairResidualVariable.occupied - 1 : PairResidualPolynomial K).totalDegree) ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    simp
  exact Nat.add_le_add occupiedDegree shiftedDegree

theorem occupancySentinelInversePolynomial_totalDegree_le_two
    (K : Type) [CommRing K] [Nontrivial K] :
    (occupancySentinelInversePolynomial K).totalDegree ≤ 2 := by
  unfold occupancySentinelInversePolynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  refine max_le ?_ ?_
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp
  · simp

theorem emptySlotCanonicalityPolynomial_totalDegree_le_two
    (K : Type) [CommRing K] [Nontrivial K] (lane : Fin 8) :
    (emptySlotCanonicalityPolynomial K lane).totalDegree ≤ 2 := by
  unfold emptySlotCanonicalityPolynomial
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have firstDegree :
      ((1 - X PairResidualVariable.occupied : PairResidualPolynomial K).totalDegree) ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    simp
  have commitmentDegree :
      (X (PairResidualVariable.commitment lane) : PairResidualPolynomial K).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree_X]
  exact Nat.add_le_add firstDegree commitmentDegree

theorem selectedChildOrderingPolynomial_totalDegree_le_two
    (K : Type) [CommRing K] [Nontrivial K] :
    (selectedChildOrderingPolynomial K).totalDegree ≤ 2 := by
  unfold selectedChildOrderingPolynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  refine max_le (by simp) ?_
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  refine max_le ?_ ?_
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have selectorDegree :
        ((1 - X PairResidualVariable.direction : PairResidualPolynomial K).totalDegree) ≤ 1 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans ?_
      simp
    have currentDegree :
        (X PairResidualVariable.current : PairResidualPolynomial K).totalDegree ≤ 1 := by
      rw [MvPolynomial.totalDegree_X]
    exact Nat.add_le_add selectorDegree currentDegree
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

theorem every_literal_new_pair_residual_totalDegree_le_two
    (K : Type) [CommRing K] [Nontrivial K] :
    (occupancyBooleanityPolynomial K).totalDegree ≤ 2 ∧
      (occupancySentinelInversePolynomial K).totalDegree ≤ 2 ∧
      (∀ lane, (emptySlotCanonicalityPolynomial K lane).totalDegree ≤ 2) ∧
      (selectedChildOrderingPolynomial K).totalDegree ≤ 2 := by
  exact ⟨occupancyBooleanityPolynomial_totalDegree_le_two K,
    occupancySentinelInversePolynomial_totalDegree_le_two K,
    emptySlotCanonicalityPolynomial_totalDegree_le_two K,
    selectedChildOrderingPolynomial_totalDegree_le_two K⟩

/-! ## Degree inventory -/

inductive ResidualClass where
  | twoRoundPoseidon
  | occupancyBooleanity
  | occupancySentinelInverse
  | emptySlotCanonicality
  | selectedChildOrdering
  | cursorBitBinding
  | frontierBinding
  | outputFrontierBinding
  deriving DecidableEq, Fintype

def intrinsicDegree : ResidualClass → Nat
  | .twoRoundPoseidon => 25
  | .occupancyBooleanity => 2
  | .occupancySentinelInverse => 2
  | .emptySlotCanonicality => 2
  | .selectedChildOrdering => 2
  | .cursorBitBinding => 1
  | .frontierBinding => 1
  | .outputFrontierBinding => 2

theorem every_new_pair_tree_residual_degree_le_two
    (residual : ResidualClass) (notPoseidon : residual ≠ .twoRoundPoseidon) :
    intrinsicDegree residual ≤ 2 := by
  cases residual <;> simp_all [intrinsicDegree]

theorem every_residual_intrinsic_degree_le_25 (residual : ResidualClass) :
    intrinsicDegree residual ≤ 25 := by
  cases residual <;> decide

def selectorDegreeOverhead : Nat := 1
def outerZerocheckDegreeOverhead : Nat := 1
def deployedDegree (residual : ResidualClass) : Nat :=
  intrinsicDegree residual + selectorDegreeOverhead + outerZerocheckDegreeOverhead

theorem every_deployed_residual_degree_le_27 (residual : ResidualClass) :
    deployedDegree residual ≤ 27 := by
  have intrinsic := every_residual_intrinsic_degree_le_25 residual
  simp only [deployedDegree, selectorDegreeOverhead,
    outerZerocheckDegreeOverhead]
  omega

theorem poseidon_still_attains_degree_27 :
    deployedDegree .twoRoundPoseidon = 27 := by
  decide

theorem pair_tree_constraints_do_not_raise_degree_cap :
    (Finset.univ.sup intrinsicDegree) = 25 ∧
      ∀ residual, deployedDegree residual ≤ 27 := by
  constructor
  · decide
  · exact every_deployed_residual_degree_le_27

#print axioms exact_48_row_headroom
#print axioms exact_source_layout_block_boundaries
#print axioms exact_staged_poseidon_row_boundary
#print axioms exact_row_boundaries
#print axioms regions_are_ordered_and_disjoint
#print axioms untouched_rows_have_exact_cardinality
#print axioms every_path_aux_row_is_exactly_inside_six_block_region
#print axioms every_path_aux_cell_is_inside_sixteen_columns
#print axioms exact_value_and_occupancy_rows_inside_final_aux_block
#print axioms occupancy_auxiliary_does_not_alias_existing_value_rows
#print axioms every_literal_new_pair_residual_totalDegree_le_two
#print axioms every_new_pair_tree_residual_degree_le_two
#print axioms every_deployed_residual_degree_le_27
#print axioms pair_tree_constraints_do_not_raise_degree_cap

end AspisPool.V7PairTreeTraceGeometry
