import Mathlib
import AspisFormal.CircleNaturalBasisEval

/-!
# Natural line basis used by the circle encoder

This lightweight module contains the natural-basis definitions and algebra
that were originally declared inside `CircleTensorBinding`.  Keeping this
section independent lets source-extracted Rust evaluator proofs import the
exact maintained definitions without also loading the unrelated circle-matrix
hiding corpus.  The declarations remain in the same namespace with identical
statements.
-/

open Matrix

namespace AspisCircleTensorBinding

section NaturalBasis

open Polynomial Polynomial.Chebyshev

variable {K : Type*} [Field K]

variable [NeZero (2 : K)]

theorem naturalLinePoly_ne_zero (index : ℕ) : naturalLinePoly K index ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro bit hbit
  exact T_ne_zero K (2 ^ bit : ℕ)

/-- The natural basis is degree-triangular: basis element `i` has degree
exactly `i`. -/
theorem naturalLinePoly_natDegree (index : ℕ) :
    (naturalLinePoly K index).natDegree = index := by
  rw [naturalLinePoly, Polynomial.natDegree_prod]
  · simp
  · intro bit hbit
    exact T_ne_zero K (2 ^ bit : ℕ)

/-- Coefficients of natural basis polynomials, with monomial degree as the row
and natural basis index as the column. -/
noncomputable def naturalCoeffMatrix (K : Type*) [Field K] (m : ℕ) :
    Matrix (Fin m) (Fin m) K :=
  fun degree basis => (naturalLinePoly K basis).coeff degree

/-- The natural-to-monomial coefficient matrix is nonsingular in every width.
Its matrix is triangular and every diagonal entry is a nonzero leading
coefficient. -/
theorem naturalCoeffMatrix_det_ne_zero (m : ℕ) :
    (naturalCoeffMatrix K m).det ≠ 0 := by
  have htri : (naturalCoeffMatrix K m).BlockTriangular id := by
    intro i j hij
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simpa [naturalCoeffMatrix, naturalLinePoly_natDegree] using hij
  rw [Matrix.det_of_upperTriangular htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  change (naturalLinePoly K i).coeff i ≠ 0
  have hlead : (naturalLinePoly K i).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (naturalLinePoly_ne_zero (K := K) i)
  simpa only [Polynomial.leadingCoeff, naturalLinePoly_natDegree] using hlead

/-- The canonical conversion from ordinary monomial coefficients to natural
line-basis coefficients. -/
noncomputable def monomialToNatural (K : Type*) [Field K] (m : ℕ) :
    Matrix (Fin m) (Fin m) K :=
  (naturalCoeffMatrix K m)⁻¹

theorem naturalCoeff_mul_monomialToNatural (m : ℕ) :
    naturalCoeffMatrix K m * monomialToNatural K m = 1 := by
  apply Matrix.mul_nonsing_inv
  exact (isUnit_iff_ne_zero.mpr (naturalCoeffMatrix_det_ne_zero (K := K) m))

/-- Evaluation of the first `m` natural line-basis polynomials at `r` points. -/
noncomputable def naturalEvalMatrix (K : Type*) [Field K] (m : ℕ) {r : ℕ}
    (points : Fin r → K) : Matrix (Fin r) (Fin m) K :=
  fun i j => (naturalLinePoly K j).eval (points i)

/-- Ordinary monomial evaluation at the same rectangular point schedule. -/
def monomialEvalMatrix (m : ℕ) {r : ℕ} (points : Fin r → K) : Matrix (Fin r) (Fin m) K :=
  fun i j => (points i) ^ (j : ℕ)

/-- Evaluating the natural basis equals ordinary Vandermonde evaluation after
the natural-to-monomial coefficient matrix. -/
theorem naturalEvalMatrix_eq_monomial_mul_coeff {r m : ℕ} (points : Fin r → K) :
    naturalEvalMatrix K m points = monomialEvalMatrix m points * naturalCoeffMatrix K m := by
  ext i j
  rw [Matrix.mul_apply]
  change (naturalLinePoly K j).eval (points i) = _
  rw [Polynomial.eval_eq_sum_range'
    (n := m) (by simp [naturalLinePoly_natDegree, j.isLt]) (points i)]
  simp only [monomialEvalMatrix, naturalCoeffMatrix]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro degree hdegree
  rw [mul_comm]

/-- After the canonical conversion, natural-basis evaluation is exactly the
ordinary monomial Vandermonde map. -/
theorem naturalEval_mul_monomialToNatural {m : ℕ} (points : Fin m → K) :
    naturalEvalMatrix K m points * monomialToNatural K m = monomialEvalMatrix m points := by
  rw [naturalEvalMatrix_eq_monomial_mul_coeff, Matrix.mul_assoc,
    naturalCoeff_mul_monomialToNatural, Matrix.mul_one]

/-- The same conversion identity for any rectangular point schedule. -/
theorem naturalEval_mul_monomialToNatural_rect {r m : ℕ} (points : Fin r → K) :
    naturalEvalMatrix K m points * monomialToNatural K m = monomialEvalMatrix m points := by
  rw [naturalEvalMatrix_eq_monomial_mul_coeff, Matrix.mul_assoc,
    naturalCoeff_mul_monomialToNatural, Matrix.mul_one]

/-- A pointwise row factor, including the circle `y` block or the aligned
`B_896` factor, commutes with the coefficient conversion. -/
theorem weightedNaturalEval_mul_monomialToNatural {r m : ℕ}
    (points weights : Fin r → K) :
    (Matrix.diagonal weights * naturalEvalMatrix K m points) * monomialToNatural K m =
      Matrix.diagonal weights * monomialEvalMatrix m points := by
  rw [Matrix.mul_assoc, naturalEval_mul_monomialToNatural_rect]

end NaturalBasis

end AspisCircleTensorBinding
