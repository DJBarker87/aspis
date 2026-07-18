import Mathlib
import AspisFormal.V5SumcheckCommitment

/-!
# The compact component-B terminal covector

This module identifies the sparse 1,024-row coefficient layout used by the
component-B CU prototype with the ten-round terminal functional proved in
`V5SumcheckCommitment`.

Round blocks start at selectors `0,1,2,3,4,5,6,28,29,30`.  Each aligned
32-row block stores the derived constant coefficient followed by the 27 free
tail coefficients; its last four rows are zero.  The initial state occupies
row 992.  The main layout theorem proves that the dot product with the public
geometric covector is exactly the scaled `terminalCovector`, and hence the
scaled `tenRoundTerminal`.

The final section defines the exact arity-four dual fold used by the Rust
relation accumulator and its four-fold/final-four-value evaluator.  It proves
that applying the compact evaluator to this sparse covector is definitionally
the same operation as four dense dual folds.  It deliberately does not claim
that the final dot alone equals the initial dot: that equality is established
by the intervening sumcheck messages and checks, not by a linear-algebra
identity of the two vectors.
-/

open scoped BigOperators

namespace AspisV5CompactTerminal

open AspisV5SumcheckCommitment

section Layout

variable {K : Type*} [Field K]

abbrev Row := Fin 1024
abbrev Round := Fin roundCount
abbrev StoredDegree := Fin 28
abbrev TailDegree := Fin tailCount
abbrev CoefficientIndex := Round × StoredDegree

/-- The Rust block-selector table, written as its two affine pieces. -/
def blockSelector (round : Round) : ℕ :=
  if (round : ℕ) < 7 then round else (round : ℕ) + 21

theorem blockSelector_values :
    List.ofFn blockSelector = [0, 1, 2, 3, 4, 5, 6, 28, 29, 30] := by
  decide

theorem blockSelector_le_thirty (round : Round) : blockSelector round ≤ 30 := by
  have hround : (round : ℕ) < 10 := by
    simpa [roundCount] using round.isLt
  simp only [blockSelector]
  split <;> omega

theorem blockSelector_injective : Function.Injective blockSelector := by
  intro left right equal
  apply Fin.ext
  simp only [blockSelector] at equal
  split at equal <;> split at equal <;> omega

/-- Physical row of stored coefficient `degree` in a round block. -/
def coefficientRow (index : CoefficientIndex) : Row :=
  ⟨32 * blockSelector index.1 + index.2,
    by have := blockSelector_le_thirty index.1; omega⟩

theorem coefficientRow_val (index : CoefficientIndex) :
    (coefficientRow index : ℕ) = 32 * blockSelector index.1 + index.2 := rfl

theorem coefficientRow_injective : Function.Injective coefficientRow := by
  intro left right equal
  have hval : 32 * blockSelector left.1 + (left.2 : ℕ) =
      32 * blockSelector right.1 + (right.2 : ℕ) := by
    exact congrArg Fin.val equal
  have hdegree : (left.2 : ℕ) = (right.2 : ℕ) := by
    have hmod := congrArg (fun value : ℕ ↦ value % 32) hval
    have hleft : (left.2 : ℕ) < 32 := by omega
    have hright : (right.2 : ℕ) < 32 := by omega
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hleft,
      Nat.mod_eq_of_lt hright] using hmod
  have hselector : blockSelector left.1 = blockSelector right.1 := by
    omega
  have hround : left.1 = right.1 := blockSelector_injective hselector
  apply Prod.ext hround
  exact Fin.ext hdegree

/-- Row 992 stores the initial mask claim. -/
def initialRow : Row := ⟨992, by omega⟩

theorem coefficientRow_lt_initial (index : CoefficientIndex) :
    (coefficientRow index : ℕ) < (initialRow : ℕ) := by
  rw [coefficientRow_val]
  change 32 * blockSelector index.1 + (index.2 : ℕ) < 992
  have := blockSelector_le_thirty index.1
  omega

theorem coefficientRow_ne_initial (index : CoefficientIndex) :
    coefficientRow index ≠ initialRow := by
  intro equal
  have := congrArg Fin.val equal
  have := coefficientRow_lt_initial index
  omega

/-- One of the four physically reserved zero rows at offsets 28 through 31
of a round's aligned block. -/
def zeroTailRow (round : Round) (offset : Fin 4) : Row :=
  ⟨32 * blockSelector round + 28 + offset,
    by have := blockSelector_le_thirty round; omega⟩

theorem zeroTailRow_lt_initial (round : Round) (offset : Fin 4) :
    (zeroTailRow round offset : ℕ) < (initialRow : ℕ) := by
  change 32 * blockSelector round + 28 + (offset : ℕ) < 992
  have := blockSelector_le_thirty round
  omega

theorem coefficientRow_ne_zeroTailRow (index : CoefficientIndex)
    (round : Round) (offset : Fin 4) :
    coefficientRow index ≠ zeroTailRow round offset := by
  intro equal
  have hval :
      32 * blockSelector index.1 + (index.2 : ℕ) =
        32 * blockSelector round + 28 + (offset : ℕ) := congrArg Fin.val equal
  have hmod := congrArg (fun value : ℕ ↦ value % 32) hval
  have hdegree : (index.2 : ℕ) < 32 := by omega
  have hoffsetOnly : (offset : ℕ) < 32 := by omega
  have hoffset : 28 + (offset : ℕ) < 32 := by omega
  have : (index.2 : ℕ) = 28 + (offset : ℕ) := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hdegree,
      Nat.mod_eq_of_lt hoffsetOnly, Nat.mod_eq_of_lt hoffset] using hmod
  omega

/-- A one-coordinate row vector. -/
def basis (row : Row) (value : K) : Row → K :=
  fun query ↦ if query = row then value else 0

/-- Dense dot product in row order. -/
def dot (left right : Row → K) : K := ∑ row, left row * right row

theorem dot_basis_right (left : Row → K) (row : Row) (value : K) :
    dot left (basis row value) = left row * value := by
  simp [dot, basis]

private theorem sum_basis_at_of_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (location : I → Row) (hlocation : Function.Injective location)
    (values : I → K) (target : I) :
    (∑ index, basis (location index) (values index)) (location target) = values target := by
  classical
  simp only [Finset.sum_apply, basis]
  rw [Finset.sum_eq_single target]
  · simp
  · intro other _ hne
    rw [if_neg]
    intro equal
    exact hne (hlocation equal.symm)
  · simp

/-- Stored coefficient zero is derived; stored coefficients 1 through 27 are
the freely sampled tail. -/
def storedCoefficient (tails : Round → TailDegree → K)
    (index : CoefficientIndex) : K :=
  Fin.cases (-(∑ degree, tails index.1 degree) * half)
    (fun degree ↦ tails index.1 degree) index.2

theorem storedCoefficient_zero (tails : Round → TailDegree → K)
    (round : Round) :
    storedCoefficient tails (round, 0) = -(∑ degree, tails round degree) * half := by
  simp [storedCoefficient]

theorem storedCoefficient_succ (tails : Round → TailDegree → K)
    (round : Round) (degree : TailDegree) :
    storedCoefficient tails (round, degree.succ) = tails round degree := by
  simp [storedCoefficient, tailCount]

/-- Exact 1,024-row component-B message.  Rows outside the ten coefficient
blocks and row 992 are zero by construction. -/
def rowMessage (initial : K) (tails : Round → TailDegree → K) : Row → K :=
  basis initialRow initial +
    ∑ index : CoefficientIndex,
      basis (coefficientRow index) (storedCoefficient tails index)

theorem rowMessage_at_initial (initial : K) (tails : Round → TailDegree → K) :
    rowMessage initial tails initialRow = initial := by
  classical
  simp only [rowMessage, Pi.add_apply, basis, if_pos, Finset.sum_apply]
  have hzero :
      (∑ index : CoefficientIndex,
        if initialRow = coefficientRow index then storedCoefficient tails index else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [if_neg]
    exact (coefficientRow_ne_initial index).symm
  rw [hzero]
  simp

theorem rowMessage_at_coefficient (initial : K) (tails : Round → TailDegree → K)
    (index : CoefficientIndex) :
    rowMessage initial tails (coefficientRow index) = storedCoefficient tails index := by
  classical
  simp only [rowMessage, Pi.add_apply, basis]
  rw [if_neg (coefficientRow_ne_initial index)]
  simp only [zero_add]
  exact sum_basis_at_of_injective coefficientRow coefficientRow_injective
    (storedCoefficient tails) index

/-- Offsets 28 through 31 of every component-B block are exactly zero. -/
theorem rowMessage_at_zeroTailRow (initial : K) (tails : Round → TailDegree → K)
    (round : Round) (offset : Fin 4) :
    rowMessage initial tails (zeroTailRow round offset) = 0 := by
  classical
  simp only [rowMessage, Pi.add_apply, basis, Finset.sum_apply]
  rw [if_neg]
  · simp only [zero_add]
    apply Finset.sum_eq_zero
    intro index _
    rw [if_neg]
    exact (coefficientRow_ne_zeroTailRow index round offset).symm
  · intro equal
    have := congrArg Fin.val equal
    have := zeroTailRow_lt_initial round offset
    omega

/-- Public geometric covector before any relation fold. -/
def terminalWeights (point : Round → K) (scale : K) : Row → K :=
  basis initialRow (scale * half ^ 10) +
    ∑ index : CoefficientIndex,
      basis (coefficientRow index)
        (scale * half ^ (9 - (index.1 : ℕ)) * point index.1 ^ (index.2 : ℕ))

theorem terminalWeights_at_initial (point : Round → K) (scale : K) :
    terminalWeights point scale initialRow = scale * half ^ 10 := by
  classical
  simp only [terminalWeights, Pi.add_apply, basis, if_pos, Finset.sum_apply]
  have hzero :
      (∑ index : CoefficientIndex,
        if initialRow = coefficientRow index then
          scale * half ^ (9 - (index.1 : ℕ)) * point index.1 ^ (index.2 : ℕ)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    simp [coefficientRow_ne_initial index |>.symm]
  rw [hzero]
  simp

theorem terminalWeights_at_coefficient (point : Round → K) (scale : K)
    (index : CoefficientIndex) :
    terminalWeights point scale (coefficientRow index) =
      scale * half ^ (9 - (index.1 : ℕ)) * point index.1 ^ (index.2 : ℕ) := by
  classical
  simp only [terminalWeights, Pi.add_apply, basis]
  rw [if_neg (coefficientRow_ne_initial index)]
  simp only [zero_add]
  exact sum_basis_at_of_injective coefficientRow coefficientRow_injective
    (fun index ↦
      scale * half ^ (9 - (index.1 : ℕ)) * point index.1 ^ (index.2 : ℕ)) index

theorem dot_rowMessage (weights : Row → K) (initial : K)
    (tails : Round → TailDegree → K) :
    dot weights (rowMessage initial tails) =
      weights initialRow * initial +
        ∑ index : CoefficientIndex,
          weights (coefficientRow index) * storedCoefficient tails index := by
  classical
  simp only [rowMessage, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    Finset.sum_apply, Finset.mul_sum]
  simp only [basis]
  rw [Finset.sum_comm]
  simp

/-- Evaluation of one stored 28-coefficient block is exactly the
zero-boundary tail evaluation used by the chained recurrence. -/
theorem storedCoefficient_evaluation
    (tail : TailDegree → K) (x : K) :
    ∑ degree : StoredDegree,
        x ^ (degree : ℕ) *
          Fin.cases (-(∑ k, tail k) * half) tail degree =
      tailEvaluation tail x := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.cases_zero, Fin.val_succ,
    Fin.cases_succ, tailEvaluation]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring_nf
  rfl

/-- The exact sparse layout computes the already-proved terminal covector. -/
theorem dot_terminalWeights_rowMessage (point : Round → K) (scale initial : K)
    (tails : Round → TailDegree → K) :
    dot (terminalWeights point scale) (rowMessage initial tails) =
      scale * terminalCovector point initial tails := by
  rw [dot_rowMessage, terminalWeights_at_initial]
  simp_rw [terminalWeights_at_coefficient]
  rw [Fintype.sum_prod_type]
  have heval (round : Round) :
      (∑ degree : StoredDegree,
        scale * half ^ (9 - (round : ℕ)) * point round ^ (degree : ℕ) *
          storedCoefficient tails (round, degree)) =
        scale * half ^ (9 - (round : ℕ)) * tailEvaluation (tails round) (point round) := by
    have hstored :
        (∑ degree : StoredDegree,
          point round ^ (degree : ℕ) * storedCoefficient tails (round, degree)) =
          tailEvaluation (tails round) (point round) := by
      simpa only [storedCoefficient] using
        (storedCoefficient_evaluation (tail := tails round) (x := point round))
    calc
      _ = ∑ degree : StoredDegree,
          (scale * half ^ (9 - (round : ℕ))) *
            (point round ^ (degree : ℕ) * storedCoefficient tails (round, degree)) := by
            apply Finset.sum_congr rfl
            intro degree _
            ring
      _ = (scale * half ^ (9 - (round : ℕ))) *
          ∑ degree : StoredDegree,
            point round ^ (degree : ℕ) * storedCoefficient tails (round, degree) := by
            rw [Finset.mul_sum]
      _ = _ := by rw [hstored]
  simp_rw [heval]
  change
    scale * half ^ 10 * initial +
        ∑ round : Round,
          scale * half ^ (9 - (round : ℕ)) * tailEvaluation (tails round) (point round) =
      scale *
        (half ^ 10 * initial +
          ∑ round : Round,
            half ^ (9 - (round : ℕ)) * tailEvaluation (tails round) (point round))
  rw [mul_add, Finset.mul_sum]
  simp only [mul_assoc]

/-- Consequently the sparse row layout authenticates the literal ten-round
recurrence, not a multilinear endpoint surrogate. -/
theorem dot_terminalWeights_rowMessage_eq_tenRoundTerminal
    (point : Round → K) (scale initial : K)
    (tails : Round → TailDegree → K) :
    dot (terminalWeights point scale) (rowMessage initial tails) =
      scale * tenRoundTerminal initial tails point := by
  rw [dot_terminalWeights_rowMessage, tenRoundTerminal_eq_terminalCovector]

end Layout

section DualFold

variable {K : Type*} [Field K]

/-- One quarter, expressed as the same two halvings used by Rust. -/
def quarter : K := half * half

/-- The dual of the arity-four monomial fold.  A chunk `(b0,b1,b2,b3)`
becomes `(b0 + alpha^3*b1 + alpha^2*b2 + alpha*b3)/4`. -/
def dualFold4 {n : ℕ} (alpha : K) (weights : Fin (4 * n) → K) : Fin n → K :=
  fun chunk ↦ quarter *
    (weights ⟨4 * chunk, by omega⟩ +
      alpha ^ 3 * weights ⟨4 * chunk + 1, by omega⟩ +
      alpha ^ 2 * weights ⟨4 * chunk + 2, by omega⟩ +
      alpha * weights ⟨4 * chunk + 3, by omega⟩)

/-- Four exact dual folds from 1,024 weights to four final weights. -/
def fourDualFolds (alphas : Fin 4 → K) (weights : Fin 1024 → K) : Fin 4 → K :=
  dualFold4 (n := 4) (alphas 3)
    (dualFold4 (n := 16) (alphas 2)
      (dualFold4 (n := 64) (alphas 1)
        (dualFold4 (n := 256) (alphas 0) weights)))

/-- The terminal operation performed by the compact Rust relation component:
four dual folds followed by a four-value dot. -/
def compactFinalDot (alphas : Fin 4 → K) (weights : Fin 1024 → K)
    (finalValues : Fin 4 → K) : K :=
  ∑ index, fourDualFolds alphas weights index * finalValues index

/-- Exact q10 instantiation of the compact component-B terminal evaluator. -/
def compactComponentBFinalDot (point : Fin 10 → K) (scale : K)
    (alphas : Fin 4 → K) (finalValues : Fin 4 → K) : K :=
  compactFinalDot alphas (terminalWeights point scale) finalValues

theorem compactComponentBFinalDot_eq_four_dense_dual_folds
    (point : Fin 10 → K) (scale : K)
    (alphas : Fin 4 → K) (finalValues : Fin 4 → K) :
    compactComponentBFinalDot point scale alphas finalValues =
      ∑ index,
        dualFold4 (n := 4) (alphas 3)
          (dualFold4 (n := 16) (alphas 2)
            (dualFold4 (n := 64) (alphas 1)
              (dualFold4 (n := 256) (alphas 0)
                (terminalWeights point scale)))) index * finalValues index := by
  rfl

/-- Once the ordinary relation sumcheck has carried the initial row-dot claim
to the final four values, the compact terminal check authenticates exactly the
ten-round component-B recurrence.  The hypothesis is intentionally explicit:
without those intervening sumcheck checks, a four-value dot is not equal to
the original 1,024-value dot for arbitrary final values. -/
theorem compactComponentBFinalDot_eq_tenRoundTerminal_of_relation
    (point : Fin 10 → K) (scale initial : K)
    (tails : Fin 10 → Fin 27 → K)
    (alphas : Fin 4 → K) (finalValues : Fin 4 → K)
    (relation_carried :
      compactComponentBFinalDot point scale alphas finalValues =
        dot (terminalWeights point scale) (rowMessage initial tails)) :
    compactComponentBFinalDot point scale alphas finalValues =
      scale * tenRoundTerminal initial tails point := by
  rw [relation_carried]
  exact dot_terminalWeights_rowMessage_eq_tenRoundTerminal point scale initial tails

end DualFold

end AspisV5CompactTerminal

#print axioms AspisV5CompactTerminal.blockSelector_values
#print axioms AspisV5CompactTerminal.coefficientRow_injective
#print axioms AspisV5CompactTerminal.storedCoefficient_evaluation
#print axioms AspisV5CompactTerminal.rowMessage_at_zeroTailRow
#print axioms AspisV5CompactTerminal.dot_terminalWeights_rowMessage
#print axioms AspisV5CompactTerminal.dot_terminalWeights_rowMessage_eq_tenRoundTerminal
#print axioms AspisV5CompactTerminal.compactComponentBFinalDot_eq_four_dense_dual_folds
#print axioms AspisV5CompactTerminal.compactComponentBFinalDot_eq_tenRoundTerminal_of_relation
