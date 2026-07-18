import Mathlib
import AspisFormal.CircleTensorBinding
import AspisFormal.CircleDiscreteAvailability

/-!
# Rectangular masking at the q18 spend schedule

One spend proof authenticates 18 disjoint arity-four fibres, hence 72 distinct
layer-zero positions.  This changes the linear-algebra target for component A.
The deployed view cannot supply the 96 rows used by the old square diagnostic.
It can, however, be hidden by a 72-by-96 mask map provided that map has full row
rank.  Equivalently, it is enough to exhibit one nonsingular 72-column minor.

The first 36 ordinary pure-x monomials and first 36 ordinary y-block
monomials give exactly such a candidate minor.  Under the triangular
ordinary-to-natural conversion used by the candidate encoder, their subspace
is supported on the first 36 natural indices of each block.  Those natural
indices use the aligned message offsets

```
  0, 2, ..., 70       and       1, 3, ..., 71
```

inside rows `896..967`.  The minor below is written in ordinary monomial
coordinates as the `m = 36` block-form circle matrix.  This file does not
prove that the Rust conversion matrix carries it to those natural-basis rows;
that identification remains part of the encoder correspondence obligation.

This file proves the dimension cap and two versions of the full-rank bridge.
The generic rational-parameter version remains conditional on its determinant
hypothesis.  The deployed-coordinate version below reindexes the exact
four-sign-fibre minor from `CircleDiscreteAvailability.lean` into the first 36
columns of each 48-column block and proves its rank unconditionally for every
injective q18 fibre schedule over M31.

That stronger result removes the schedule-specific determinant obligation; it
does not by itself identify the Rust transcript's bit-reversed stored indices
and slot order with the Lean representatives, identify the Rust natural-basis
conversion and row-896 weights with this monomial-coordinate map, or transport
the M31 rank certificate into the QM31 verifier field.  Those are still exact
cross-language binding obligations rather than determinant hypotheses.

The result concerns only the 72 layer-zero point values.  It does not show that
OOD, fold, terminal, or any other released functionals are in their span, nor
does it replace the required joint-rank theorem for the complete v5 view.
-/

open Matrix

namespace AspisCircleRectangularMasking

open AspisCircleTensorBinding
open AspisCircleDiscreteAvailability

def openedWidth : ℕ := 72
def rectangularHalf : ℕ := 36
def rectangularWidth : ℕ := 72
def originalHalf : ℕ := 48
def originalWidth : ℕ := 96

theorem concrete_widths :
    queryCount * fibreSlots = openedWidth ∧
      openedWidth = rectangularWidth ∧
      rectangularWidth = 2 * rectangularHalf ∧
      originalWidth = 2 * originalHalf := by
  norm_num [openedWidth, rectangularWidth, rectangularHalf, originalWidth, originalHalf,
    queryCount, fibreSlots]

/-! ## The rank cap imposed by the released rows -/

/-- No matrix with only the 72 released rows can have more than 72 linearly
independent columns.  Thus 72 is the maximum *effective* mask dimension visible
in this part of the transcript.  This does not forbid sampling 96 coefficients;
the extra 24 then lie in fibres of a surjective map. -/
theorem independent_column_count_le_openedWidth
    {K : Type*} [Field K] {k : ℕ}
    (M : Matrix (Fin openedWidth) (Fin k) K)
    (hcols : LinearIndependent K M.col) : k ≤ openedWidth := by
  have hrank : M.rank = k := by
    rw [← Matrix.rank_transpose]
    simpa only [Matrix.row_transpose, Fintype.card_fin] using hcols.rank_matrix
  rw [← hrank]
  exact Matrix.rank_le_height M

theorem no_96_independent_columns
    {K : Type*} [Field K]
    (M : Matrix (Fin openedWidth) (Fin originalWidth) K) :
    ¬ LinearIndependent K M.col := by
  intro hcols
  have hle := independent_column_count_le_openedWidth M hcols
  norm_num [openedWidth, originalWidth, originalHalf, queryCount, fibreSlots] at hle

/-! ## The aligned 72-column choice -/

/-- Column inclusion selecting `p_0..p_35, q_0..q_35` from coefficient order
`p_0..p_47, q_0..q_47`. -/
def selectedColumn (j : Fin rectangularWidth) : Fin originalWidth :=
  if h : (j : ℕ) < rectangularHalf then
    ⟨j, by
      have hj := j.isLt
      simp only [rectangularWidth, rectangularHalf, originalWidth] at hj h ⊢
      omega⟩
  else
    ⟨originalHalf + ((j : ℕ) - rectangularHalf), by
      have hj := j.isLt
      simp only [rectangularWidth, rectangularHalf, originalWidth, originalHalf] at hj h ⊢
      omega⟩

/-- Message offset of the natural-basis index with the same block/degree
label as a selected ordinary monomial.  The candidate circle encoder
interleaves the pure-x and y natural bases in bit-zero order.  Equality of the
ordinary-coordinate map with the converted Rust rows is not asserted here. -/
def selectedMessageOffset (j : Fin rectangularWidth) : ℕ :=
  if (j : ℕ) < rectangularHalf then 2 * (j : ℕ)
  else 2 * ((j : ℕ) - rectangularHalf) + 1

theorem selectedMessageOffset_lt (j : Fin rectangularWidth) :
    selectedMessageOffset j < rectangularWidth := by
  have hj := j.isLt
  simp only [selectedMessageOffset, rectangularWidth, rectangularHalf] at hj ⊢
  split_ifs with h <;> omega

/-- All 72 corresponding natural-basis indices stay inside the aligned
reserve block, indeed inside rows `896..967`. -/
theorem selected_reserve_row_geometry (j : Fin rectangularWidth) :
    reserveStart + selectedMessageOffset j < reserveStart + rectangularWidth ∧
    reserveStart + selectedMessageOffset j < traceRows := by
  have hoff := selectedMessageOffset_lt j
  constructor
  · omega
  · norm_num [reserveStart, rectangularWidth, rectangularHalf, traceRows] at hoff ⊢
    omega

/-- The existing aligned tensor factorisation applies to every corresponding
natural-basis row.  A separate triangular conversion is needed before using
this fact for the ordinary-monomial minor. -/
theorem selected_tensor_factorisation
    {K : Type*} [CommRing K] (factor : Fin 10 → K) (j : Fin rectangularWidth) :
    tensorBasis10 factor (reserveStart + selectedMessageOffset j) =
      tensorBasis10 factor reserveStart *
        tensorBasis10 factor (selectedMessageOffset j) := by
  apply tensorBasis10_reserve_add
  have h := selectedMessageOffset_lt j
  norm_num [rectangularWidth, rectangularHalf, reserveWidth] at h ⊢
  omega

/-! ## A 72-column minor of the 72-by-96 evaluation map -/

section Evaluation

variable {K : Type*} [Field K]

/-- Rectangular block-form circle evaluation.  It has `r` schedule rows and
`2m` coefficient columns. -/
def rectangularBlockEvalMatrix (m r : ℕ) (sched : Fin r → K) :
    Matrix (Fin r) (Fin (2 * m)) K :=
  fun i j =>
    if (j : ℕ) < m then
      rationalCircleX (sched i) ^ (j : ℕ)
    else
      rationalCircleY (sched i) *
        rationalCircleX (sched i) ^ ((j : ℕ) - m)

/-- Selecting the first 36 columns of each block from the 72-by-96 matrix is
entrywise the square `m = 36` block-form circle matrix. -/
theorem selected_minor_eq_circleBlock
    (sched : Fin rectangularWidth → K) :
    (rectangularBlockEvalMatrix originalHalf rectangularWidth sched).submatrix
        id selectedColumn =
      circleBlockEvalMatrix rectangularHalf sched := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq]
  by_cases h : (j : ℕ) < 36
  · simp [rectangularBlockEvalMatrix, circleBlockEvalMatrix, selectedColumn,
      rectangularHalf, originalHalf, h]
    omega
  · have hj := j.isLt
    simp only [rectangularWidth] at hj
    simp [rectangularBlockEvalMatrix, circleBlockEvalMatrix, selectedColumn,
      rectangularHalf, originalHalf, h]

/-- The square 72-column block, given a type whose row and column indices are
definitionally identical. -/
def squareBlockEval (sched : Fin rectangularWidth → K) :
    Matrix (Fin rectangularWidth) (Fin rectangularWidth) K :=
  fun i j =>
    if (j : ℕ) < rectangularHalf then
      rationalCircleX (sched i) ^ (j : ℕ)
    else
      rationalCircleY (sched i) *
        rationalCircleX (sched i) ^ ((j : ℕ) - rectangularHalf)

theorem squareBlockEval_eq_circleBlock (sched : Fin rectangularWidth → K) :
    squareBlockEval sched = circleBlockEvalMatrix rectangularHalf sched := by
  ext i j
  rfl

theorem selected_minor_eq_squareBlock
    (sched : Fin rectangularWidth → K) :
    (rectangularBlockEvalMatrix originalHalf rectangularWidth sched).submatrix
        id selectedColumn = squareBlockEval sched := by
  rw [selected_minor_eq_circleBlock, squareBlockEval_eq_circleBlock]

/-- Aligned row rescaling of the complete 72-by-96 point-evaluation map. -/
def alignedRectangularEval (sched : Fin rectangularWidth → K)
    (weight : Fin rectangularWidth → K) :
    Matrix (Fin rectangularWidth) (Fin originalWidth) K :=
  Matrix.diagonal weight *
    rectangularBlockEvalMatrix originalHalf rectangularWidth sched

/-- The selected minor commutes with the aligned diagonal row rescaling. -/
theorem aligned_selected_minor_eq
    (sched : Fin rectangularWidth → K)
    (weight : Fin rectangularWidth → K) :
    (alignedRectangularEval sched weight).submatrix id selectedColumn =
      Matrix.diagonal weight * squareBlockEval sched := by
  ext i j
  simp only [alignedRectangularEval, Matrix.submatrix_apply, id_eq,
    Matrix.diagonal_mul]
  exact congrArg (weight i * ·)
    (congrFun (congrFun (selected_minor_eq_squareBlock sched) i) j)

/-- The candidate 72-column minor is nonsingular under the exact three
hypotheses exposed by the existing circle-tensor bridge: no rational pole,
nonzero aligned row factors, and nonsingularity of the cleared `circleTMatrix`
at this schedule. -/
theorem aligned_minor_det_ne_zero
    (sched : Fin rectangularWidth → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0)
    (weight : Fin rectangularWidth → K) (hweight : ∀ i, weight i ≠ 0)
    (hcircle :
      ((AspisCircleLiveness.circleTMatrix K 36).map
        (MvPolynomial.eval sched)).det ≠ 0) :
    (Matrix.diagonal weight *
      squareBlockEval sched).det ≠ 0 := by
  rw [squareBlockEval_eq_circleBlock]
  exact weightedBlock_det_ne_zero 36 sched hQ weight hweight hcircle

/-- Consequently, those 72 selected columns have full column rank. -/
theorem aligned_minor_linearIndependent_columns
    (sched : Fin rectangularWidth → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0)
    (weight : Fin rectangularWidth → K) (hweight : ∀ i, weight i ≠ 0)
    (hcircle :
      ((AspisCircleLiveness.circleTMatrix K 36).map
        (MvPolynomial.eval sched)).det ≠ 0) :
    LinearIndependent K
      (Matrix.diagonal weight *
        squareBlockEval sched).col := by
  apply Matrix.linearIndependent_cols_of_det_ne_zero
  exact aligned_minor_det_ne_zero sched hQ weight hweight hcircle

/-- The full 72-by-96 map then has rank exactly 72.  This is the correct
surjectivity-shaped certificate for hiding all 72 layer-zero values while
retaining the original 96 random coefficients. -/
theorem alignedRectangularEval_rank_eq_openedWidth
    (sched : Fin rectangularWidth → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0)
    (weight : Fin rectangularWidth → K) (hweight : ∀ i, weight i ≠ 0)
    (hcircle :
      ((AspisCircleLiveness.circleTMatrix K 36).map
        (MvPolynomial.eval sched)).det ≠ 0) :
    (alignedRectangularEval sched weight).rank = openedWidth := by
  have hdet := aligned_minor_det_ne_zero sched hQ weight hweight hcircle
  have hminorRank :
      (Matrix.diagonal weight *
        squareBlockEval sched).rank = rectangularWidth := by
    simpa only [Fintype.card_fin] using
      (Matrix.linearIndependent_rows_of_det_ne_zero hdet).rank_matrix
  have hle : rectangularWidth ≤ (alignedRectangularEval sched weight).rank := by
    calc
      rectangularWidth =
          (Matrix.diagonal weight * squareBlockEval sched).rank := hminorRank.symm
      _ = ((alignedRectangularEval sched weight).submatrix id selectedColumn).rank :=
        congrArg Matrix.rank (aligned_selected_minor_eq sched weight).symm
      _ ≤ (alignedRectangularEval sched weight).rank :=
        Matrix.rank_submatrix_le (alignedRectangularEval sched weight) id selectedColumn
  have hu := Matrix.rank_le_height (alignedRectangularEval sched weight)
  have heq : (alignedRectangularEval sched weight).rank = rectangularWidth := by omega
  simpa [openedWidth, rectangularWidth] using heq

/-- Full rank of the 72-by-96 map is equivalent here to the operational fact
needed by the point-evaluation hiding argument: every 72-coordinate view has a
mask preimage. -/
theorem alignedRectangularEval_mulVec_surjective
    (sched : Fin rectangularWidth → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0)
    (weight : Fin rectangularWidth → K) (hweight : ∀ i, weight i ≠ 0)
    (hcircle :
      ((AspisCircleLiveness.circleTMatrix K 36).map
        (MvPolynomial.eval sched)).det ≠ 0) :
    Function.Surjective (alignedRectangularEval sched weight).mulVec := by
  change Function.Surjective
    ⇑(alignedRectangularEval sched weight).mulVecLin
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  change (alignedRectangularEval sched weight).rank =
    Module.finrank K (Fin rectangularWidth → K)
  rw [alignedRectangularEval_rank_eq_openedWidth sched hQ weight hweight hcircle]
  rw [Module.finrank_pi]
  rw [Fintype.card_fin]
  rfl

/-- The m=36 determinant is not the zero polynomial.  This establishes that
the 72-column candidate is algebraically viable in the independent-parameter
model; it is not the missing discrete-fibre availability theorem. -/
theorem circle72_polynomial_det_ne_zero
    (τ : Fin 36 → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0)
    (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2))
    (h2 : (2 : K) ≠ 0) :
    (AspisCircleLiveness.circleTMatrix K 36).det ≠ 0 :=
  AspisCircleLiveness.circleTMatrix_det_ne_zero K 36 τ hQ hτ0 hτsq h2

end Evaluation

/-! ## The deployed four-sign-fibre minor

The generic matrix above uses a rational parameter `t` and a flat `Fin 72`
row index.  The discrete theorem uses the deployed M31 circle coordinates
directly, with rows and columns indexed by `Fin 18 × (Fin 2 × Fin 2)`.  The
following definitions make the column permutation explicit.  They avoid
silently treating those two matrix presentations as definitionally equal.
-/

section DeployedFibre

abbrev DeployedField := ZMod AspisCircleGroupOrder.P
abbrev FibreIndex := Fin queryCount × FibreSign

/-- The x exponent selected by a degree and the x-sign character.  For q18 it
runs from 0 through 35. -/
def fibreXDegree (column : FibreIndex) : ℕ :=
  2 * (column.1 : ℕ) + (column.2.1 : ℕ)

theorem fibreXDegree_lt_rectangularHalf (column : FibreIndex) :
    fibreXDegree column < rectangularHalf := by
  have hd := column.1.isLt
  have hp := column.2.1.isLt
  norm_num [fibreXDegree, queryCount, rectangularHalf] at hd hp ⊢
  omega

/-- Column permutation from the four character blocks to conventional
`p_0..p_47, q_0..q_47` order.  Character bit zero chooses the pure-x block;
character bit one chooses the y block. -/
def selectedFibreColumn (column : FibreIndex) : Fin originalWidth :=
  if h : column.2.2 = 0 then
    ⟨fibreXDegree column, by
      have hd := fibreXDegree_lt_rectangularHalf column
      norm_num [rectangularHalf, originalWidth] at hd ⊢
      omega⟩
  else
    ⟨originalHalf + fibreXDegree column, by
      have hd := fibreXDegree_lt_rectangularHalf column
      norm_num [rectangularHalf, originalHalf, originalWidth] at hd ⊢
      omega⟩

/-- The direct M31 coordinate form of the complete 72-by-96 point-evaluation
map.  `weight` isolates the aligned row-896 factor. -/
def deployedFibreRectangularEval
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    Matrix FibreIndex (Fin originalWidth) DeployedField :=
  fun row column =>
    weight row *
      if (column : ℕ) < originalHalf then
        signedCoordinate row.2.1 (representativeX (queries row.1)) ^ (column : ℕ)
      else
        signedCoordinate row.2.2 (representativeY (queries row.1)) *
          signedCoordinate row.2.1 (representativeX (queries row.1)) ^
            ((column : ℕ) - originalHalf)

/-- After the explicit column permutation, the deployed rectangular map is a
nonzero row diagonal times the discrete four-fibre minor. -/
theorem deployedFibre_selected_minor_eq
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    (deployedFibreRectangularEval queries weight).submatrix id selectedFibreColumn =
      Matrix.diagonal weight *
        fibreEvaluationMinor
          (fun i ↦ representativeX (queries i))
          (fun i ↦ representativeY (queries i)) := by
  ext row column
  rcases row with ⟨i, sign⟩
  rcases column with ⟨degree, character⟩
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_mul,
    deployedFibreRectangularEval]
  rw [fibreEvaluationMinor_is_block_eval]
  congr 1
  have hsmall : fibreXDegree (degree, character) < originalHalf := by
    have h := fibreXDegree_lt_rectangularHalf (degree, character)
    norm_num [rectangularHalf, originalHalf] at h ⊢
    omega
  have hc : character.2 = 0 ∨ character.2 = 1 := by omega
  rcases hc with hc | hc
  · have hsmall' : 2 * (degree : ℕ) + (character.1 : ℕ) < 48 := by
      simpa [fibreXDegree, originalHalf] using hsmall
    simp [selectedFibreColumn, fibreXDegree, originalHalf, hc, pow_add]
    omega
  · simp [selectedFibreColumn, fibreXDegree, originalHalf, hc, pow_add]
    ring

/-- The selected deployed minor is nonsingular for every q18 schedule sampled
without replacement and every nonzero aligned row factor. -/
theorem deployedFibre_selected_minor_det_ne_zero
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    ((deployedFibreRectangularEval queries weight).submatrix
      id selectedFibreColumn).det ≠ 0 := by
  rw [deployedFibre_selected_minor_eq, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun row _ ↦ hweight row))
    (spend_fibre_minor_det_ne_zero queries hqueries)

/-- Hence the direct deployed-coordinate 72-by-96 map has full row rank.  This
is the schedule-specific determinant conclusion that the earlier abstract
rational presentation could only assume. -/
theorem deployedFibreRectangularEval_rank_eq_openedWidth
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    (deployedFibreRectangularEval queries weight).rank = openedWidth := by
  have hdet := deployedFibre_selected_minor_det_ne_zero queries hqueries weight hweight
  let minor : Matrix FibreIndex FibreIndex DeployedField :=
    (deployedFibreRectangularEval queries weight).submatrix id selectedFibreColumn
  have hdetMinor : minor.det ≠ 0 := by simpa [minor] using hdet
  have hminorRank :
      minor.rank = Fintype.card FibreIndex :=
    (Matrix.linearIndependent_rows_of_det_ne_zero hdetMinor).rank_matrix
  have hle : Fintype.card FibreIndex ≤
      (deployedFibreRectangularEval queries weight).rank := by
    rw [← hminorRank]
    change ((deployedFibreRectangularEval queries weight).submatrix
      id selectedFibreColumn).rank ≤ _
    exact Matrix.rank_submatrix_le
      (deployedFibreRectangularEval queries weight) id selectedFibreColumn
  have hu := Matrix.rank_le_card_height (deployedFibreRectangularEval queries weight)
  have heq :
      (deployedFibreRectangularEval queries weight).rank = Fintype.card FibreIndex := by
    omega
  have hcard : Fintype.card FibreIndex = openedWidth := by
    norm_num [FibreIndex, FibreSign, queryCount, openedWidth]
  exact heq.trans hcard

end DeployedFibre

/-! ## What the discrete availability result does and does not close -/

/-- The current q18 theorem supplies the 72 distinct row indices needed to
form the rectangular matrix. -/
theorem q18_supplies_distinct_rows
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries) :
    Function.Injective (expandedPosition queries) :=
  spend_opened_positions_injective queries hqueries

/-- This proposition names the determinant hypothesis of the generic
rational-parameter presentation.  `spend_fibre_minor_det_ne_zero` and
`deployedFibreRectangularEval_rank_eq_openedWidth` discharge the corresponding
fact for the direct deployed M31 coordinates.  An explicit rational-parameter
and row-reindexing bridge would be required to construct this proposition
itself; no later theorem should silently treat the two presentations as
definitionally equal. -/
def ActualScheduleMinorNonsingular
    {K : Type*} [Field K] (sched : Fin rectangularWidth → K) : Prop :=
  ((AspisCircleLiveness.circleTMatrix K rectangularHalf).map
    (MvPolynomial.eval sched)).det ≠ 0

/-!
The deployed rank theorem still closes only the layer-zero submatrix.  The
complete-view PCS obligation must append every OOD, fold and terminal mask
functional and prove surjectivity of that joint map.  It must also bind the
Rust index/slot order, natural-basis conversion, aligned weights and QM31 field
embedding to the objects used here.
-/

#print axioms independent_column_count_le_openedWidth
#print axioms no_96_independent_columns
#print axioms selected_tensor_factorisation
#print axioms selected_minor_eq_circleBlock
#print axioms aligned_minor_det_ne_zero
#print axioms aligned_minor_linearIndependent_columns
#print axioms alignedRectangularEval_rank_eq_openedWidth
#print axioms alignedRectangularEval_mulVec_surjective
#print axioms circle72_polynomial_det_ne_zero
#print axioms deployedFibre_selected_minor_eq
#print axioms deployedFibre_selected_minor_det_ne_zero
#print axioms deployedFibreRectangularEval_rank_eq_openedWidth
#print axioms q18_supplies_distinct_rows

end AspisCircleRectangularMasking
