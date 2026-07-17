import Mathlib
import AspisFormal.CircleTMatrixHiding

/-!
# Aligned circle-tensor binding for the v5 reserve block

The circle encoder treats its 1024 message coordinates as coefficients in a
ten-factor tensor basis. A consecutive mask block has the claimed
`diagonal · circleTMatrix` form only when its start is aligned beyond every
varying low bit. The original draft used rows `928..1023`; those rows cross
three different high-bit prefixes and do not have one common factor.

The corrected block is `896..991 = 896 + (0..95)`. Since `896 = 7 * 128`, its
low seven bits are zero and every `j < 96` occupies only those low bits. Thus
the tensor basis at coordinate `896+j` is the fixed high factor at 896 times
the low tensor basis at `j`.

This file kernel-checks that alignment statement and the general linear-algebra
bridge showing that an invertible coefficient conversion on the right, like
the monomial-to-natural conversion used by the Rust encoder adapter, preserves
nonsingularity and hiding. The exact Rust conversion table remains a separate
cross-language binding obligation.
-/

open Matrix

namespace AspisCircleTensorBinding

/-! ## Concrete reserve geometry -/

def activeRows : ℕ := 879
def reserveStart : ℕ := 896
def reserveWidth : ℕ := 96
def reserveAlignment : ℕ := 128
def traceRows : ℕ := 1024

theorem reserve_geometry :
    activeRows ≤ reserveStart ∧
    reserveStart % reserveAlignment = 0 ∧
    reserveWidth ≤ reserveAlignment ∧
    reserveStart + reserveWidth = 992 ∧
    reserveStart + reserveWidth ≤ traceRows := by
  norm_num [activeRows, reserveStart, reserveWidth, reserveAlignment, traceRows]

/-! ## Ten-factor tensor basis -/

section Tensor

variable {K : Type*} [CommRing K]

/-- Evaluation of the ten-factor binary tensor basis at numeric coordinate
`index`. Factor `k` is present exactly when bit `k` of `index` is set. -/
def tensorBasis10 (factor : Fin 10 → K) (index : ℕ) : K :=
  ∏ k : Fin 10, if index.testBit k then factor k else 1

/-- The fixed high factor selected by the aligned start `896`, whose only set
bits are 7, 8 and 9. -/
def reserveHighFactor (factor : Fin 10 → K) : K := factor 7 * factor 8 * factor 9

private theorem aligned_bit (j : ℕ) (hj : j < reserveWidth) (k : Fin 10) :
    (reserveStart + j).testBit k =
      (if k.1 < 7 then j.testBit k else (7 : ℕ).testBit (k.1 - 7)) := by
  have hwidth : reserveWidth < 2 ^ 7 := by norm_num [reserveWidth]
  have hj128 : j < 2 ^ 7 := lt_trans hj hwidth
  rw [show reserveStart + j = 2 ^ 7 * 7 + j by norm_num [reserveStart]]
  exact Nat.testBit_two_pow_mul_add 7 hj128 k

private theorem start_bit (k : Fin 10) :
    reserveStart.testBit k =
      (if k.1 < 7 then false else (7 : ℕ).testBit (k.1 - 7)) := by
  rw [show reserveStart = 2 ^ 7 * 7 + 0 by norm_num [reserveStart]]
  simpa using Nat.testBit_two_pow_mul_add 7 (b := 0) (by norm_num : 0 < 2 ^ 7) k

private theorem low_high_bit (j : ℕ) (hj : j < reserveWidth) (k : Fin 10)
    (hk : ¬ k.1 < 7) : j.testBit k = false := by
  fin_cases k <;> simp_all only [not_true_eq_false, Nat.reduceLT]
  all_goals
    apply Nat.testBit_lt_two_pow
    norm_num [reserveWidth] at hj ⊢
    omega

/-- **Exact aligned-block factorisation.** For every one of the 96 reserved
coordinates, the ten-factor encoder basis splits into the fixed basis image at
row 896 and the lower basis image at row `j`. -/
theorem tensorBasis10_reserve_add (factor : Fin 10 → K) (j : ℕ) (hj : j < reserveWidth) :
    tensorBasis10 factor (reserveStart + j) =
      tensorBasis10 factor reserveStart * tensorBasis10 factor j := by
  classical
  simp only [tensorBasis10, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [aligned_bit j hj k, start_bit]
  by_cases hk : k.1 < 7
  · simp [hk]
  · have hjk := low_high_bit j hj k hk
    simp [hk, hjk]

end Tensor

/-! ## The natural line basis and its coefficient conversion -/

section NaturalBasis

open Polynomial Polynomial.Chebyshev

variable {K : Type*} [Field K]

/-- The repeated doubling factor used by the Rust natural-basis evaluator. -/
def doubledFactor (x : K) : ℕ → K
  | 0 => x
  | bit + 1 => 2 * (doubledFactor x bit) ^ 2 - 1

/-- Repeated `2x²-1` is evaluation of the power-of-two Chebyshev factor. -/
theorem doubledFactor_eq_chebyshev (x : K) : ∀ bit : ℕ,
    doubledFactor x bit = (T K (2 ^ bit : ℕ)).eval x
  | 0 => by simp [doubledFactor]
  | bit + 1 => by
      rw [doubledFactor, doubledFactor_eq_chebyshev]
      rw [show (2 ^ (bit + 1) : ℕ) = 2 * 2 ^ bit by omega]
      change 2 * (T K (2 ^ bit : ℕ)).eval x ^ 2 - 1 =
        (T K ((2 : ℤ) * (2 ^ bit : ℕ))).eval x
      rw [T_mul, T_two, Polynomial.eval_comp]
      simp

/-- The real encoder's natural line basis polynomial. Its set bits select the
Chebyshev factors `T_(2^k)`, exactly matching the repeated `2x²-1` factors in
the circle FFT. -/
noncomputable def naturalLinePoly (K : Type*) [Field K] (index : ℕ) : K[X] :=
  ∏ bit ∈ index.bitIndices.toFinset, T K (2 ^ bit : ℕ)

/-- The product evaluator used by Rust is evaluation of `naturalLinePoly`. -/
def naturalLineValue (x : K) (index : ℕ) : K :=
  ∏ bit ∈ index.bitIndices.toFinset, doubledFactor x bit

theorem naturalLineValue_eq_eval (x : K) (index : ℕ) :
    naturalLineValue x index = (naturalLinePoly K index).eval x := by
  rw [naturalLineValue, naturalLinePoly, Polynomial.eval_prod]
  simp only [doubledFactor_eq_chebyshev]

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

/-! ## Exact bridge from the rational circle matrix to the encoder leakage -/

section RationalCircleBridge

open MvPolynomial AspisCircleLiveness

variable {K : Type*} [Field K]

/-- The standard rational parametrisation's `x` coordinate. -/
def rationalCircleX (t : K) : K := (1 - t ^ 2) / (1 + t ^ 2)

/-- The standard rational parametrisation's `y` coordinate. -/
def rationalCircleY (t : K) : K := 2 * t / (1 + t ^ 2)

/-- Ordinary block-form circle evaluation, before denominator clearing. -/
def circleBlockEvalMatrix (m : ℕ) (sched : Fin (2 * m) → K) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) K :=
  fun i j =>
    if (j : ℕ) < m then
      rationalCircleX (sched i) ^ (j : ℕ)
    else
      rationalCircleY (sched i) * rationalCircleX (sched i) ^ ((j : ℕ) - m)

/-- Per-row factor already incorporated by `circleTMatrix`. -/
def circleClearingFactor (m : ℕ) (sched : Fin (2 * m) → K) (i : Fin (2 * m)) : K :=
  (1 + (sched i) ^ 2) ^ m

private lemma clear_x (m s : ℕ) (t : K) (hQ : 1 + t ^ 2 ≠ 0) (hs : s ≤ m) :
    (1 - t ^ 2) ^ s * (1 + t ^ 2) ^ (m - s) =
      (1 + t ^ 2) ^ m * rationalCircleX t ^ s := by
  have hpow : (1 + t ^ 2) ^ m = (1 + t ^ 2) ^ s * (1 + t ^ 2) ^ (m - s) := by
    rw [← pow_add]
    congr 1
    omega
  rw [rationalCircleX, div_pow, hpow]
  field_simp

private lemma clear_y (m k : ℕ) (t : K) (hQ : 1 + t ^ 2 ≠ 0) (hk : k < m) :
    2 * t * (1 - t ^ 2) ^ k * (1 + t ^ 2) ^ (m - 1 - k) =
      (1 + t ^ 2) ^ m * (rationalCircleY t * rationalCircleX t ^ k) := by
  have hpow : (1 + t ^ 2) ^ m =
      (1 + t ^ 2) ^ (k + 1) * (1 + t ^ 2) ^ (m - 1 - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [rationalCircleX, rationalCircleY, div_pow, hpow]
  field_simp
  ring

/-- The denominator-cleared matrix is exactly a nonzero row rescaling of the
ordinary block-form evaluation matrix. -/
theorem circleTMatrix_eval_eq_clearing_mul_block (m : ℕ) (sched : Fin (2 * m) → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0) :
    (circleTMatrix K m).map (MvPolynomial.eval sched) =
      Matrix.diagonal (circleClearingFactor m sched) * circleBlockEvalMatrix m sched := by
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_mul, circleClearingFactor,
    circleBlockEvalMatrix]
  by_cases hj : (j : ℕ) < m
  · simp only [circleTMatrix, hj, if_true, map_mul, map_pow, map_sub, map_one,
      map_add, eval_X]
    exact clear_x m j (sched i) (hQ i) (le_of_lt hj)
  · simp only [circleTMatrix, hj, if_false, map_mul, map_pow, map_sub, map_one,
      map_add, eval_X, map_ofNat]
    exact clear_y m ((j : ℕ) - m) (sched i) (hQ i) (by omega)

/-- A leakage matrix with row factor `weight` is the cleared rational-circle
matrix rescaled by `weight / (1+t²)^m`. This fixes the direction of the
denominator factor: `circleTMatrix` already contains it. -/
theorem weightedBlock_eq_rescaled_circleT (m : ℕ) (sched : Fin (2 * m) → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0) (weight : Fin (2 * m) → K) :
    Matrix.diagonal weight * circleBlockEvalMatrix m sched =
      Matrix.diagonal (fun i => weight i / circleClearingFactor m sched i) *
        (circleTMatrix K m).map (MvPolynomial.eval sched) := by
  rw [circleTMatrix_eval_eq_clearing_mul_block m sched hQ]
  ext i j
  simp only [Matrix.diagonal_mul]
  field_simp [circleClearingFactor, hQ i]

/-- Consequently, nonzero encoder factors and a nonsingular cleared circle
matrix imply that the actual weighted block-form leakage matrix is
nonsingular. -/
theorem weightedBlock_det_ne_zero (m : ℕ) (sched : Fin (2 * m) → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0)
    (weight : Fin (2 * m) → K) (hweight : ∀ i, weight i ≠ 0)
    (hcircle : ((circleTMatrix K m).map (MvPolynomial.eval sched)).det ≠ 0) :
    (Matrix.diagonal weight * circleBlockEvalMatrix m sched).det ≠ 0 := by
  rw [weightedBlock_eq_rescaled_circleT m sched hQ weight]
  apply AspisCircleTMatrixHiding.det_diagonal_mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact div_ne_zero (hweight i) (pow_ne_zero m (hQ i))
  · exact hcircle

/-- Under the same explicit non-pole, nonzero-factor and nonsingularity
hypotheses, the ordinary-coefficient leakage view has witness-independent
fibres. -/
theorem weightedBlock_view_indep (m : ℕ) (sched : Fin (2 * m) → K)
    (hQ : ∀ i, 1 + (sched i) ^ 2 ≠ 0)
    (weight : Fin (2 * m) → K) (hweight : ∀ i, weight i ≠ 0)
    (hcircle : ((circleTMatrix K m).map (MvPolynomial.eval sched)).det ≠ 0)
    (w₁ w₂ y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K //
        w₁ + Matrix.mulVecLin
          (Matrix.diagonal weight * circleBlockEvalMatrix m sched) R = y}
      = Nat.card {R : Fin (2 * m) → K //
        w₂ + Matrix.mulVecLin
          (Matrix.diagonal weight * circleBlockEvalMatrix m sched) R = y} :=
  view_indep_of_det_ne_zero
    (Matrix.diagonal weight * circleBlockEvalMatrix m sched)
    (weightedBlock_det_ne_zero m sched hQ weight hweight hcircle) w₁ w₂ y

end RationalCircleBridge

/-! ## Invertible right conversions preserve the hiding matrix -/

section LinearAlgebra

variable {K : Type*} [CommRing K] [NoZeroDivisors K] {n : ℕ}

/-- Right multiplication by a nonsingular coefficient conversion preserves
`det ≠ 0`. -/
theorem det_mul_conversion_ne_zero {A C : Matrix (Fin n) (Fin n) K}
    (hA : A.det ≠ 0) (hC : C.det ≠ 0) : (A * C).det ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero hA hC

end LinearAlgebra

section Hiding

variable {K : Type*} [Field K] {n : ℕ}

/-- A nonzero diagonal on the left and an invertible coefficient conversion on
the right preserve the witness-independent view conclusion. -/
theorem converted_diag_view_indep
    {d : Fin n → K} (hd : (∏ i, d i) ≠ 0)
    {A C : Matrix (Fin n) (Fin n) K}
    (hA : A.det ≠ 0) (hC : C.det ≠ 0)
    (w₁ w₂ y : Fin n → K) :
    Nat.card {R : Fin n → K //
        w₁ + Matrix.mulVecLin (Matrix.diagonal d * A * C) R = y}
      = Nat.card {R : Fin n → K //
        w₂ + Matrix.mulVecLin (Matrix.diagonal d * A * C) R = y} := by
  simpa only [Matrix.mul_assoc] using
    AspisCircleTMatrixHiding.diag_rescale_view_indep hd
      (det_mul_conversion_ne_zero hA hC) w₁ w₂ y

end Hiding

end AspisCircleTensorBinding

#print axioms AspisCircleTensorBinding.reserve_geometry
#print axioms AspisCircleTensorBinding.tensorBasis10_reserve_add
#print axioms AspisCircleTensorBinding.doubledFactor_eq_chebyshev
#print axioms AspisCircleTensorBinding.naturalLineValue_eq_eval
#print axioms AspisCircleTensorBinding.naturalLinePoly_natDegree
#print axioms AspisCircleTensorBinding.naturalCoeffMatrix_det_ne_zero
#print axioms AspisCircleTensorBinding.naturalEval_mul_monomialToNatural
#print axioms AspisCircleTensorBinding.weightedNaturalEval_mul_monomialToNatural
#print axioms AspisCircleTensorBinding.circleTMatrix_eval_eq_clearing_mul_block
#print axioms AspisCircleTensorBinding.weightedBlock_eq_rescaled_circleT
#print axioms AspisCircleTensorBinding.weightedBlock_det_ne_zero
#print axioms AspisCircleTensorBinding.weightedBlock_view_indep
#print axioms AspisCircleTensorBinding.det_mul_conversion_ne_zero
#print axioms AspisCircleTensorBinding.converted_diag_view_indep
