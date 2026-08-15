import AspisFormal.SumcheckMasking
import AspisFormal.V5ComponentADeployedTerminalApplicability
import AspisFormal.V5ProductionPublicResidualBinding

/-!
# From the accepted masked sumcheck to production residuals

This file isolates the algebra between the verifier's ten-round masked
sumcheck and the public residuals used by the spend statement.

The production verifier does the following in this order.

1. It samples `theta`, a ten-coordinate equality point, and `mu` after the
   trace roots have been absorbed.
2. It samples a nonzero `eta` and verifies ten degree-27 sumcheck messages.
3. It checks the final sumcheck claim against
   `mask(point) + eta * real(point)`.
4. The real terminal is the equality weight times the twenty-five-lane
   constraint batch, plus `mu` times the copy-helper value.

Acceptance alone is not enough to conclude that the committed table satisfies
all constraints.  The commitment/FRI and sumcheck argument must first connect
the accepted messages and authenticated point openings to one fixed table.
That remaining implication is represented below by
`AcceptedTraceAndSumcheckEvidence`.  It is deliberately not assigned a
probability here.

Once that evidence is available, this file proves the rest of the deterministic
argument.  A false public statement must fall into one of three separate
algebraic events:

* cancellation against the helper at `mu`;
* a nonzero Boolean table evaluating to zero at the equality point; or
* a nonzero twenty-five-lane row polynomial evaluating to zero at `theta`.

The events are kept separate because they have different degree bounds and
different transcript-ordering requirements.
-/

namespace AspisV5AcceptedTerminalResidualExtraction

open scoped BigOperators
open AspisFormal.ArithmetizationCore
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ConstraintLaneBatching
open AspisV5FriConcreteEncoderApplicability
open AspisV5ProductionPublicResidualBinding
open AspisV5TowerPackedResidualExtraction
open Module Polynomial

variable {K : Type*} [Field K] [Algebra F K]

/-- Ten-coordinate Boolean point for a physical trace row.  Coordinate zero
is row bit nine, matching `AtomicSemanticSelectors::at_point`. -/
def booleanTracePoint (row : Fin 1024) : Fin 10 → K := fun coordinate =>
  if bigEndianBit row coordinate then 1 else 0

/-- Ten big-endian bits determine a row in the 1,024-row trace. -/
theorem bigEndianBits_injective :
    Function.Injective
      (fun row : Fin 1024 => fun coordinate : Fin 10 =>
        bigEndianBit row coordinate) := by
  intro left right equalBits
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases within : bit < 10
  · let coordinate : Fin 10 := ⟨9 - bit, by omega⟩
    have equalAtCoordinate := congrFun equalBits coordinate
    change Nat.testBit left.val (9 - coordinate.val) =
      Nat.testBit right.val (9 - coordinate.val) at equalAtCoordinate
    have coordinateBit : 9 - coordinate.val = bit := by
      simp only [coordinate]
      omega
    simpa [coordinateBit] using equalAtCoordinate
  · have tenLe : 10 ≤ bit := by omega
    have powLe : 2 ^ 10 ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide) tenLe
    have leftBelow : left.val < 2 ^ bit := by
      have leftLt := left.isLt
      norm_num at leftLt
      omega
    have rightBelow : right.val < 2 ^ bit := by
      have rightLt := right.isLt
      norm_num at rightLt
      omega
    rw [Nat.testBit_eq_false_of_lt leftBelow,
      Nat.testBit_eq_false_of_lt rightBelow]

/-- The Boolean point for a selected row gives a Kronecker-delta MLE
selector on all physical rows. -/
theorem mleRowWeight_booleanTracePoint
    (selected row : Fin 1024) :
    mleRowWeight (booleanTracePoint selected : Fin 10 → K) row =
      if row = selected then 1 else 0 := by
  classical
  by_cases same : row = selected
  · subst row
    simp only [mleRowWeight]
    apply Finset.prod_eq_one
    intro coordinate _
    by_cases bit : bigEndianBit selected coordinate <;>
      simp [booleanTracePoint, bit]
  · have bitFunctionsDiffer :
        (fun coordinate : Fin 10 => bigEndianBit row coordinate) ≠
          (fun coordinate : Fin 10 => bigEndianBit selected coordinate) := by
      intro equalBits
      exact same (bigEndianBits_injective equalBits)
    obtain ⟨coordinate, bitDiffers⟩ := Function.ne_iff.mp bitFunctionsDiffer
    rw [if_neg same]
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    by_cases rowBit : bigEndianBit row coordinate
    · have selectedBit : bigEndianBit selected coordinate = false := by
        cases selectedValue : bigEndianBit selected coordinate
        · rfl
        · exact False.elim (bitDiffers (by simp [rowBit, selectedValue]))
      simp [booleanTracePoint, rowBit, selectedBit]
    · have selectedBit : bigEndianBit selected coordinate = true := by
        cases selectedValue : bigEndianBit selected coordinate
        · exact False.elim (bitDiffers (by simp [rowBit, selectedValue]))
        · rfl
      simp [booleanTracePoint, rowBit, selectedBit]

/-- Field spelling of `atomic_equality_value`. -/
def sourceEqualityValue (left right : Fin 10 → K) : K :=
  Finset.univ.prod (fun coordinate : Fin 10 =>
    1 - left coordinate - right coordinate +
      left coordinate * right coordinate +
      left coordinate * right coordinate)

/-- On a Boolean row, the source equality polynomial is exactly the
big-endian multilinear row selector used elsewhere in the release model. -/
theorem sourceEqualityValue_booleanTracePoint
    (point : Fin 10 → K) (row : Fin 1024) :
    sourceEqualityValue point (booleanTracePoint row) =
      mleRowWeight point row := by
  classical
  simp only [sourceEqualityValue, mleRowWeight]
  apply Finset.prod_congr rfl
  intro coordinate _
  by_cases bit : bigEndianBit row coordinate
  · simp [booleanTracePoint, bit]
  · simp [booleanTracePoint, bit]

/-- The degree-at-most-24 lane polynomial at one physical Boolean row. -/
noncomputable def rowConstraintPolynomial
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (row : Fin 1024) : K[X] :=
  monomialPolynomial ((constraintRows row).laneVector basis)

/-- The fixed Boolean constraint table after evaluating the row polynomials
at the transcript challenge `theta`. -/
noncomputable def thetaConstraintTable
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) : Fin 1024 → K := fun row =>
  (rowConstraintPolynomial basis constraintRows row).eval theta

/-- Literal big-endian multilinear evaluation of a 1,024-entry table.  The
explicit row type avoids relying on reducibility of the shared `traceRows`
abbreviation when this file is replayed across Lean toolchains. -/
noncomputable def tableMLEValue
    (point : Fin 10 → K) (table : Fin 1024 → K) : K :=
  ∑ row : Fin 1024, mleRowWeight point row * table row

/-- The big-endian multilinear evaluation of the theta-batched Boolean table
at the ten-coordinate equality point. -/
noncomputable def constraintMLE
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (point : Fin 10 → K) : K :=
  tableMLEValue point
    (thetaConstraintTable basis constraintRows theta)

/-! ## Exact degree-ten equality-point polynomial -/

/-- One big-endian Boolean-row basis polynomial in ten variables. -/
noncomputable def mleRowPolynomial (row : Fin 1024) :
    MvPolynomial (Fin 10) K :=
  ∏ coordinate : Fin 10,
    if bigEndianBit row coordinate then MvPolynomial.X coordinate
    else 1 - MvPolynomial.X coordinate

/-- Unique multilinear extension of a 1,024-entry Boolean table. -/
noncomputable def tableMLEPolynomial (table : Fin 1024 → K) :
    MvPolynomial (Fin 10) K :=
  ∑ row, MvPolynomial.C (table row) * mleRowPolynomial row

@[simp]
theorem eval_mleRowPolynomial (point : Fin 10 → K) (row : Fin 1024) :
    MvPolynomial.eval point (mleRowPolynomial row) =
      mleRowWeight point row := by
  classical
  rw [mleRowPolynomial, map_prod]
  simp only [mleRowWeight]
  apply Finset.prod_congr rfl
  intro coordinate _
  by_cases bit : bigEndianBit row coordinate <;> simp [bit]

@[simp]
theorem eval_tableMLEPolynomial
    (point : Fin 10 → K) (table : Fin 1024 → K) :
    MvPolynomial.eval point (tableMLEPolynomial table) =
      tableMLEValue point table := by
  classical
  simp [tableMLEPolynomial, tableMLEValue, map_sum, mul_comm]

/-- Evaluating the multilinear extension at a Boolean trace point returns
the selected physical row exactly. -/
theorem tableMLEValue_booleanTracePoint
    (table : Fin 1024 → K) (selected : Fin 1024) :
    tableMLEValue (booleanTracePoint selected) table = table selected := by
  classical
  unfold tableMLEValue
  simp_rw [mleRowWeight_booleanTracePoint]
  rw [Finset.sum_eq_single selected]
  · simp
  · intro row _ rowNe
    simp [rowNe]
  · simp

/-- A nonzero Boolean table has a nonzero multilinear-extension polynomial. -/
theorem tableMLEPolynomial_ne_zero
    (table : Fin 1024 → K) (tableNonzero : table ≠ 0) :
    tableMLEPolynomial table ≠ 0 := by
  classical
  have existsNonzero : ∃ row, table row ≠ 0 := by
    by_contra noNonzero
    apply tableNonzero
    funext row
    by_contra rowNonzero
    exact noNonzero ⟨row, rowNonzero⟩
  obtain ⟨row, rowNonzero⟩ := existsNonzero
  intro polynomialZero
  have evaluatedZero := congrArg
    (MvPolynomial.eval (booleanTracePoint row)) polynomialZero
  rw [map_zero, eval_tableMLEPolynomial,
    tableMLEValue_booleanTracePoint] at evaluatedZero
  exact rowNonzero evaluatedZero

/-- Every Boolean-row basis polynomial has total degree at most ten. -/
theorem mleRowPolynomial_totalDegree_le (row : Fin 1024) :
    (mleRowPolynomial (K := K) row).totalDegree ≤ 10 := by
  classical
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ coordinate : Fin 10,
        (if bigEndianBit row coordinate then MvPolynomial.X coordinate
          else 1 - MvPolynomial.X coordinate :
            MvPolynomial (Fin 10) K).totalDegree
      ≤ ∑ _coordinate : Fin 10, 1 := by
        apply Finset.sum_le_sum
        intro coordinate _
        by_cases bit : bigEndianBit row coordinate
        · simp [bit]
        · simp only [bit]
          refine (MvPolynomial.totalDegree_sub _ _).trans ?_
          simp
    _ = 10 := by simp

/-- The multilinear extension of any 1,024-entry table has total degree at
most ten. -/
theorem tableMLEPolynomial_totalDegree_le (table : Fin 1024 → K) :
    (tableMLEPolynomial table).totalDegree ≤ 10 := by
  classical
  unfold tableMLEPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro row _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  calc
    (MvPolynomial.C (table row) : MvPolynomial (Fin 10) K).totalDegree +
        (mleRowPolynomial row).totalDegree
      ≤ 0 + 10 := Nat.add_le_add
        (by simp) (mleRowPolynomial_totalDegree_le row)
    _ = 10 := by omega

section FiniteFieldBounds

variable [Fintype K] [DecidableEq K]

/-- Equality points where a fixed Boolean table's multilinear extension
vanishes. -/
noncomputable def zerocheckCollisionSet
    (table : Fin 1024 → K) : Finset (Fin 10 → K) :=
  Finset.univ.filter fun point => tableMLEValue point table = 0

/-- A fixed nonzero Boolean table vanishes at at most a `10 / |K|` fraction
of uniformly sampled ten-coordinate equality points. -/
theorem uniform_zerocheck_collision_fraction_le_ten
    (table : Fin 1024 → K) (tableNonzero : table ≠ 0) :
    ((zerocheckCollisionSet table).card : ℚ≥0) /
        (Fintype.card K ^ 10) ≤
      (10 : ℚ≥0) / Fintype.card K := by
  have bound := MvPolynomial.schwartz_zippel_totalDegree
    (tableMLEPolynomial_ne_zero table tableNonzero)
    (Finset.univ : Finset K)
  simp only [Fintype.piFinset_univ, Finset.card_univ,
    eval_tableMLEPolynomial] at bound
  change ((zerocheckCollisionSet table).card : ℚ≥0) /
      (Fintype.card K ^ 10) ≤ (10 : ℚ≥0) / Fintype.card K
  refine bound.trans ?_
  gcongr
  exact_mod_cast tableMLEPolynomial_totalDegree_le table

/-- Challenges `mu` that cancel one fixed nonzero constraint value against
one fixed helper sum. -/
def helperCancellationSet (constraintValue helperSum : K) : Finset K :=
  Finset.univ.filter fun mu => constraintValue + mu * helperSum = 0

/-- At most one field element can cancel a fixed nonzero constraint value
against a fixed helper sum. -/
theorem helperCancellationSet_card_le_one
    (constraintValue helperSum : K) (constraintNonzero : constraintValue ≠ 0) :
    (helperCancellationSet constraintValue helperSum).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro left right leftMember rightMember
  have leftEquation := (Finset.mem_filter.mp leftMember).2
  have rightEquation := (Finset.mem_filter.mp rightMember).2
  by_cases helperZero : helperSum = 0
  · exfalso
    apply constraintNonzero
    simpa [helperZero] using leftEquation
  · apply sub_eq_zero.mp
    have productZero : (left - right) * helperSum = 0 := by
      linear_combination leftEquation - rightEquation
    exact (mul_eq_zero.mp productZero).resolve_right helperZero

/-- The corresponding uniform-field helper-cancellation fraction is at most
`1 / |K|`. -/
theorem uniform_helper_cancellation_fraction_le_one
    (constraintValue helperSum : K) (constraintNonzero : constraintValue ≠ 0) :
    ((helperCancellationSet constraintValue helperSum).card : ℚ≥0) /
        Fintype.card K ≤
      (1 : ℚ≥0) / Fintype.card K := by
  gcongr
  exact_mod_cast helperCancellationSet_card_le_one
    constraintValue helperSum constraintNonzero

end FiniteFieldBounds

/-- Boolean restriction of the real, unmasked oracle evaluated by
`atomic_state_only_selected_unmasked_terminal_value_compiled_v3`. -/
noncomputable def sourceUnmaskedZerocheckTable
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mu : K) (helper : Fin 1024 → K) : Fin 1024 → K := fun row =>
  sourceEqualityValue zerocheckPoint (booleanTracePoint row) *
      thetaConstraintTable basis constraintRows theta row +
    mu * helper row

/-- Summing the source-shaped Boolean oracle gives the constraint MLE plus
`mu` times the helper sum. -/
theorem tableSum_sourceUnmaskedZerocheckTable
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mu : K) (helper : Fin 1024 → K) :
    tableSum (sourceUnmaskedZerocheckTable basis constraintRows theta
      zerocheckPoint mu helper) =
      constraintMLE basis constraintRows theta zerocheckPoint +
        mu * tableSum helper := by
  classical
  simp only [tableSum, sourceUnmaskedZerocheckTable,
    sourceEqualityValue_booleanTracePoint, constraintMLE,
    tableMLEValue, Finset.sum_add_distrib]
  rw [Finset.mul_sum]

/-- Exact equation needed from the accepted degree-27 sumcheck after the
point openings have been authenticated.  The nonzero `eta` check is performed
by the production rejection sampler. -/
structure ExtractedMaskedSumcheckBoundary
    (eta : K) (real mask : Fin 1024 → K) : Prop where
  etaNonzero : eta ≠ 0
  boundary : tableSum (maskedOracle eta real mask) = tableSum mask

/-- The accepted masked equation forces the unmasked Boolean oracle to sum to
zero. -/
theorem unmasked_sum_zero_of_extracted_boundary
    (eta : K) (real mask : Fin 1024 → K)
    (extracted : ExtractedMaskedSumcheckBoundary eta real mask) :
    tableSum real = 0 :=
  original_sum_eq_zero_of_mixed_sum eta real mask
    extracted.etaNonzero extracted.boundary

/-- A nonzero constraint MLE can be hidden by the helper term at the sampled
`mu`.  This is a separate one-variable cancellation event. -/
def HelperCancellation
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mu : K) (helper : Fin 1024 → K) : Prop :=
  constraintMLE basis constraintRows theta zerocheckPoint ≠ 0 ∧
    constraintMLE basis constraintRows theta zerocheckPoint +
      mu * tableSum helper = 0

/-- Outside helper cancellation, a zero sum of the source-shaped unmasked
oracle forces the theta-batched constraint MLE to be zero. -/
theorem constraintMLE_zero_outside_helper_cancellation
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mu : K) (helper : Fin 1024 → K)
    (sumZero : tableSum (sourceUnmaskedZerocheckTable basis constraintRows
      theta zerocheckPoint mu helper) = 0)
    (outside : ¬ HelperCancellation basis constraintRows theta
      zerocheckPoint mu helper) :
    constraintMLE basis constraintRows theta zerocheckPoint = 0 := by
  have equation :
      constraintMLE basis constraintRows theta zerocheckPoint +
        mu * tableSum helper = 0 := by
    rw [← tableSum_sourceUnmaskedZerocheckTable]
    exact sumZero
  by_contra nonzero
  exact outside ⟨nonzero, equation⟩

/-- A nonzero theta-batched Boolean table happens to evaluate to zero at the
sampled ten-coordinate equality point. -/
def ZerocheckEvaluationCollision
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K) : Prop :=
  thetaConstraintTable basis constraintRows theta ≠ 0 ∧
    constraintMLE basis constraintRows theta zerocheckPoint = 0

/-- Outside the equality-point collision, a zero constraint MLE means every
Boolean-row theta batch is zero. -/
theorem thetaConstraintTable_zero_outside_zerocheck_collision
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mleZero : constraintMLE basis constraintRows theta zerocheckPoint = 0)
    (outside : ¬ ZerocheckEvaluationCollision basis constraintRows theta
      zerocheckPoint) :
    thetaConstraintTable basis constraintRows theta = 0 := by
  by_contra tableNonzero
  exact outside ⟨tableNonzero, mleZero⟩

/-- One fixed nonzero row, chosen only from the constraint table and therefore
independently of `theta`.  The default row is used only when every row
polynomial is already zero. -/
noncomputable def selectedNonzeroPolynomialRow
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K)) : Fin 1024 := by
  classical
  exact if existsNonzero : ∃ row,
        rowConstraintPolynomial basis constraintRows row ≠ 0 then
      Classical.choose existsNonzero
    else 0

theorem selectedNonzeroPolynomialRow_spec
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (existsNonzero : ∃ row,
      rowConstraintPolynomial basis constraintRows row ≠ 0) :
    rowConstraintPolynomial basis constraintRows
      (selectedNonzeroPolynomialRow basis constraintRows) ≠ 0 := by
  rw [selectedNonzeroPolynomialRow, dif_pos existsNonzero]
  exact Classical.choose_spec existsNonzero

/-- A nonzero selected row polynomial has a nonzero twenty-five-lane
coefficient vector. -/
theorem selectedNonzeroPolynomialRow_laneVector_ne_zero
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (existsNonzero : ∃ row,
      rowConstraintPolynomial basis constraintRows row ≠ 0) :
    (constraintRows
      (selectedNonzeroPolynomialRow basis constraintRows)).laneVector basis ≠ 0 := by
  intro lanesZero
  have polynomialNonzero := selectedNonzeroPolynomialRow_spec basis
    constraintRows existsNonzero
  apply polynomialNonzero
  rw [rowConstraintPolynomial, lanesZero]
  unfold monomialPolynomial
  simp

/-- The fixed nonzero row polynomial is hidden by the sampled `theta`.
Because the selected row does not depend on `theta`, this event has the
ordinary degree-24 root bound once `theta` is modeled as uniform. -/
def ThetaLaneCollision
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K) : Prop :=
  rowConstraintPolynomial basis constraintRows
      (selectedNonzeroPolynomialRow basis constraintRows) ≠ 0 ∧
    (rowConstraintPolynomial basis constraintRows
      (selectedNonzeroPolynomialRow basis constraintRows)).eval theta = 0

section ThetaFiniteFieldBound

variable [Fintype K] [DecidableEq K]

/-- For a fixed constraint table with at least one nonzero row polynomial,
the concrete `ThetaLaneCollision` event is exactly membership in the
degree-24 root set for the selected row. -/
theorem thetaLaneCollision_iff_mem_width25CollisionSet
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (existsNonzero : ∃ row,
      rowConstraintPolynomial basis constraintRows row ≠ 0)
    (theta : K) :
    ThetaLaneCollision basis constraintRows theta ↔
      theta ∈ width25CollisionSet
        ((constraintRows
          (selectedNonzeroPolynomialRow basis constraintRows)).laneVector basis) := by
  have selectedNonzero := selectedNonzeroPolynomialRow_spec basis
    constraintRows existsNonzero
  constructor
  · intro collision
    rw [width25CollisionSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ theta, ?_⟩
    rw [← eval_monomialPolynomial_width25]
    exact collision.2
  · intro member
    refine ⟨selectedNonzero, ?_⟩
    have batchZero := (Finset.mem_filter.mp member).2
    rw [rowConstraintPolynomial, eval_monomialPolynomial_width25]
    exact batchZero

/-- The fixed-table `theta` event contains at most twenty-four field
challenges. -/
theorem thetaLaneCollision_card_le_twenty_four
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (existsNonzero : ∃ row,
      rowConstraintPolynomial basis constraintRows row ≠ 0) :
    (width25CollisionSet
      ((constraintRows
        (selectedNonzeroPolynomialRow basis constraintRows)).laneVector basis)).card ≤ 24 :=
  width25_collision_card_le_twenty_four _
    (selectedNonzeroPolynomialRow_laneVector_ne_zero basis constraintRows
      existsNonzero)

/-- Under a uniform full-field `theta`, the fixed selected-row collision
probability is at most `24 / |K|`. -/
theorem uniform_thetaLaneCollision_probability_le
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (existsNonzero : ∃ row,
      rowConstraintPolynomial basis constraintRows row ≠ 0) :
    uniformWidth25CollisionProbability
        ((constraintRows
          (selectedNonzeroPolynomialRow basis constraintRows)).laneVector basis) ≤
      (24 : Rat) / Fintype.card K :=
  uniform_width25_collision_probability_le _
    (selectedNonzeroPolynomialRow_laneVector_ne_zero basis constraintRows
      existsNonzero)

end ThetaFiniteFieldBound

/-- If every row evaluates to zero and `theta` did not hide a nonzero row
polynomial, all twenty-five-lane row polynomials are identically zero. -/
theorem row_polynomials_zero_outside_theta_collision
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 →
      ConstraintRowResiduals (F := F) (K := K))
    (theta : K)
    (tableZero : thetaConstraintTable basis constraintRows theta = 0)
    (outside : ¬ ThetaLaneCollision basis constraintRows theta) :
    ∀ row, rowConstraintPolynomial basis constraintRows row = 0 := by
  intro row
  by_contra polynomialNonzero
  apply outside
  have existsNonzero : ∃ row,
      rowConstraintPolynomial basis constraintRows row ≠ 0 :=
    ⟨row, polynomialNonzero⟩
  refine ⟨selectedNonzeroPolynomialRow_spec basis constraintRows
    existsNonzero, ?_⟩
  have rowZero := congrFun tableZero
    (selectedNonzeroPolynomialRow basis constraintRows)
  exact rowZero

/-! ## One fixed accepted-run view -/

/-- All mathematical objects that must be recovered from one accepted
production run.  The extraction function supplying this view must be fixed;
the theorem below does not choose a convenient trace after seeing `theta`. -/
structure AcceptedTerminalRunView (K : Type*) [Field K] [Algebra F K] where
  trace : Fin 1024 → Fin 16 → F
  opened : OpenedColumns
  constraintRows : Fin 1024 →
    ConstraintRowResiduals (F := F) (K := K)
  theta : K
  zerocheckPoint : Fin 10 → K
  mu : K
  eta : K
  helper : Fin 1024 → K
  mask : Fin 1024 → K

/-- The remaining exact evidence expected from source correspondence,
commitment/FRI extraction, and sumcheck soundness.  Its three fields are kept
separate so later work can discharge them independently. -/
structure AcceptedTraceAndSumcheckEvidence
    (statement : V5PublicStatement)
    (basis : Basis (Fin 4) F K)
    (view : AcceptedTerminalRunView K) : Prop where
  publicRowsProject : ProductionPublicRowsProjectToOpenedColumns
    (productionPublicRowsFromTrace view.trace) view.opened
  publicResidualsMatch : ProductionPublicResidualsMatchConstraintRows
    (terminalSpendFields statement)
    (productionPublicRowsFromTrace view.trace) view.constraintRows
  maskedBoundary : ExtractedMaskedSumcheckBoundary view.eta
    (sourceUnmaskedZerocheckTable basis view.constraintRows view.theta
      view.zerocheckPoint view.mu view.helper)
    view.mask

/-- Exact failure of the still-missing accepted-Rust-to-fixed-table and
sumcheck/commitment implication.  No numerical bound is claimed here. -/
def AcceptedTraceOrSumcheckExtractionFailure
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (viewOf : Run → AcceptedTerminalRunView K)
    (basis : Basis (Fin 4) F K)
    (statement : V5PublicStatement) (run : Run) : Prop :=
  accepts statement run ∧
    ¬ AcceptedTraceAndSumcheckEvidence statement basis (viewOf run)

/-- With the fixed trace and accepted masked-boundary equation, the three
named algebraic events are the only remaining reasons this step can fail to
produce identically zero row polynomials. -/
theorem extracted_row_polynomials_or_algebraic_failure
    (statement : V5PublicStatement)
    (basis : Basis (Fin 4) F K)
    (view : AcceptedTerminalRunView K)
    (evidence : AcceptedTraceAndSumcheckEvidence statement basis view) :
    (∀ row, rowConstraintPolynomial basis view.constraintRows row = 0) ∨
      HelperCancellation basis view.constraintRows view.theta
          view.zerocheckPoint view.mu view.helper ∨
      ZerocheckEvaluationCollision basis view.constraintRows view.theta
          view.zerocheckPoint ∨
      ThetaLaneCollision basis view.constraintRows view.theta := by
  by_cases helperFailure : HelperCancellation basis view.constraintRows
      view.theta view.zerocheckPoint view.mu view.helper
  · exact Or.inr (Or.inl helperFailure)
  have realSumZero :
      tableSum (sourceUnmaskedZerocheckTable basis view.constraintRows
        view.theta view.zerocheckPoint view.mu view.helper) = 0 :=
    unmasked_sum_zero_of_extracted_boundary view.eta _ view.mask
      evidence.maskedBoundary
  have mleZero := constraintMLE_zero_outside_helper_cancellation basis
    view.constraintRows view.theta view.zerocheckPoint view.mu view.helper
    realSumZero helperFailure
  by_cases zerocheckFailure : ZerocheckEvaluationCollision basis
      view.constraintRows view.theta view.zerocheckPoint
  · exact Or.inr (Or.inr (Or.inl zerocheckFailure))
  have tableZero := thetaConstraintTable_zero_outside_zerocheck_collision basis
    view.constraintRows view.theta view.zerocheckPoint mleZero zerocheckFailure
  by_cases thetaFailure : ThetaLaneCollision basis view.constraintRows view.theta
  · exact Or.inr (Or.inr (Or.inr thetaFailure))
  exact Or.inl (row_polynomials_zero_outside_theta_collision basis
    view.constraintRows view.theta tableZero thetaFailure)

/-- Outside the three named algebraic events, the fixed accepted-run evidence
has exactly the shape required by the production public-residual theorem. -/
theorem extracted_production_theta_residuals_outside_algebraic_failures
    (statement : V5PublicStatement)
    (basis : Basis (Fin 4) F K)
    (view : AcceptedTerminalRunView K)
    (evidence : AcceptedTraceAndSumcheckEvidence statement basis view)
    (noHelper : ¬ HelperCancellation basis view.constraintRows view.theta
      view.zerocheckPoint view.mu view.helper)
    (noZerocheck : ¬ ZerocheckEvaluationCollision basis view.constraintRows
      view.theta view.zerocheckPoint)
    (noTheta : ¬ ThetaLaneCollision basis view.constraintRows view.theta) :
    ExtractedProductionThetaPublicResiduals
      (terminalSpendFields statement) view.opened
      (productionPublicRowsFromTrace view.trace) basis view.constraintRows := by
  refine {
    projects := evidence.publicRowsProject
    residualsMatch := evidence.publicResidualsMatch
    polynomialZero := ?_
  }
  have realSumZero :
      tableSum (sourceUnmaskedZerocheckTable basis view.constraintRows
        view.theta view.zerocheckPoint view.mu view.helper) = 0 :=
    unmasked_sum_zero_of_extracted_boundary view.eta _ view.mask
      evidence.maskedBoundary
  have mleZero := constraintMLE_zero_outside_helper_cancellation basis
    view.constraintRows view.theta view.zerocheckPoint view.mu view.helper
    realSumZero noHelper
  have tableZero := thetaConstraintTable_zero_outside_zerocheck_collision basis
    view.constraintRows view.theta view.zerocheckPoint mleZero noZerocheck
  exact row_polynomials_zero_outside_theta_collision basis view.constraintRows
    view.theta tableZero noTheta

/-- Accepted production verification either binds all six spend fields or
falls into the exact unproved extraction condition or one of the three named
algebraic events.  The theorem assigns no probability to any branch. -/
theorem accepted_run_binds_statement_or_named_failure
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (viewOf : Run → AcceptedTerminalRunView K)
    (basis : Basis (Fin 4) F K)
    (statement : V5PublicStatement) (run : Run)
    (constraints : ConstraintsSatisfied (viewOf run).opened)
    (accepted : accepts statement run) :
    OpenedColumnsMatchStatement statement (viewOf run).opened ∨
      AcceptedTraceOrSumcheckExtractionFailure accepts viewOf basis statement run ∨
      HelperCancellation basis (viewOf run).constraintRows (viewOf run).theta
          (viewOf run).zerocheckPoint (viewOf run).mu (viewOf run).helper ∨
      ZerocheckEvaluationCollision basis (viewOf run).constraintRows
          (viewOf run).theta (viewOf run).zerocheckPoint ∨
      ThetaLaneCollision basis (viewOf run).constraintRows (viewOf run).theta := by
  by_cases extractionFailure : AcceptedTraceOrSumcheckExtractionFailure
      accepts viewOf basis statement run
  · exact Or.inr (Or.inl extractionFailure)
  have evidence : AcceptedTraceAndSumcheckEvidence statement basis (viewOf run) := by
    by_contra missing
    exact extractionFailure ⟨accepted, missing⟩
  rcases extracted_row_polynomials_or_algebraic_failure statement basis
      (viewOf run) evidence with polynomialZero | failure
  · left
    apply extracted_theta_public_residuals_bind_statement statement
      (viewOf run).opened constraints
      (productionPublicRowsFromTrace (viewOf run).trace) basis
      (viewOf run).constraintRows
    exact {
      projects := evidence.publicRowsProject
      residualsMatch := evidence.publicResidualsMatch
      polynomialZero := polynomialZero
    }
  · rcases failure with helper | zerocheck | theta
    · exact Or.inr (Or.inr (Or.inl helper))
    · exact Or.inr (Or.inr (Or.inr (Or.inl zerocheck)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr theta)))

#print axioms sourceEqualityValue_booleanTracePoint
#print axioms bigEndianBits_injective
#print axioms mleRowWeight_booleanTracePoint
#print axioms eval_tableMLEPolynomial
#print axioms tableMLEValue_booleanTracePoint
#print axioms tableMLEPolynomial_ne_zero
#print axioms tableMLEPolynomial_totalDegree_le
#print axioms uniform_zerocheck_collision_fraction_le_ten
#print axioms helperCancellationSet_card_le_one
#print axioms uniform_helper_cancellation_fraction_le_one
#print axioms tableSum_sourceUnmaskedZerocheckTable
#print axioms unmasked_sum_zero_of_extracted_boundary
#print axioms constraintMLE_zero_outside_helper_cancellation
#print axioms thetaConstraintTable_zero_outside_zerocheck_collision
#print axioms selectedNonzeroPolynomialRow_spec
#print axioms selectedNonzeroPolynomialRow_laneVector_ne_zero
#print axioms thetaLaneCollision_iff_mem_width25CollisionSet
#print axioms thetaLaneCollision_card_le_twenty_four
#print axioms uniform_thetaLaneCollision_probability_le
#print axioms row_polynomials_zero_outside_theta_collision
#print axioms extracted_row_polynomials_or_algebraic_failure
#print axioms extracted_production_theta_residuals_outside_algebraic_failures
#print axioms accepted_run_binds_statement_or_named_failure

end AspisV5AcceptedTerminalResidualExtraction
