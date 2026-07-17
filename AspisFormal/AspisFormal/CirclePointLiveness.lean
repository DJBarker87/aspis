import Mathlib
import AspisFormal.CircleVandermonde
import AspisFormal.CircleVandermondeGeneral

/-!
# Layer 2b over independently parametrised circle points

`CircleVandermondeGeneral` proves the `b = 2m` mask-evaluation liveness bound treating
each schedule point's coordinates `(x_i, y_i)` as *independent free variables* ranging
over `K^(2b)`. Circle query points do not range freely: they lie on the unit
circle `x_i^2 + y_i^2 = 1`, a one-dimensional variety. This file closes that
geometric gap by proving the bound for a distribution where each point `i` is
drawn independently from a free parameter `t_i ∈ K` via the rational
parametrisation

```
x(t) = (1 - t^2)/(1 + t^2),   y(t) = 2t/(1 + t^2),   1 + t^2 ≠ 0.
```

This is not yet the production distribution: the current wire derives
structured circle points from discrete query indices and their fibres. A
separate availability theorem is required for that schedule.

## Clearing denominators

Substituting `x = x(t)`, `y = y(t)` into the block-form basis entry for row `i` and
multiplying that row by `(1 + t_i^2)^m` clears all denominators, giving a matrix
`circleTMatrix m` over `MvPolynomial (Fin (2m)) K` in the `b = 2m` parameters `t_1..t_b`
(one per point, matching the circle's dimension 1).  Row scaling by the nonzero factor
`(1 + t_i^2)^m` does not change whether the determinant vanishes.

## The circle grid witness

The free-coordinate witness of `CircleVandermondeGeneral` puts `y = 0` at `m` distinct
`x`-nodes.  That is **impossible on the circle** (`y = 0 ⇒ x = ±1`, only two points), which
is exactly why the circle constraint is a genuine restriction.  The honest circle witness
instead takes `m` distinct nodes `x_r = x(τ_r)` and pairs each with the *two* circle points
`(x_r, ±y_r)` — parameters `±τ_r`.  The evaluated matrix reindexes to
`fromBlocks (R·V) (R·W·V) (R·V) (R·(-W·V))`, whose determinant is
`(∏ Q_r^m)^2 · (-2)^m · (∏ y_r) · (det V)^2 ≠ 0` when the nodes are distinct,
the parameters are nonzero, and `char K ≠ 2`. (Characteristic `≠ 2` is
intrinsic to circle-FFT STARKs; the deployed field `QM31` has characteristic
`2^31 − 1`.)

## Deliverables

* `circleTMatrix K m` — the denominator-cleared matrix over the `b = 2m` parameters.
* `circleTMatrix_det_ne_zero` — `det ≠ 0` for any circle witness `τ` (distinct squares,
  nonzero, non-pole) with `2 ≠ 0`.
* `circleTMatrix_totalDegree_le` — `det.totalDegree ≤ 4·m·m` (the `≈ 2×` cost of clearing
  denominators versus the free `2m^2`).
* `circle_point_schedule_fail_le` — singular fraction `≤ 4·m·m / |K|` over circle points.
* `circle_pole_fraction_le` — the excluded pole set `{∃ i, 1 + t_i^2 = 0}` has fraction
  `≤ 2·(2m) / |K|`.
* `circle_point_liveness` — combined: `Pr[singular ∨ pole] ≤ (4·m·m + 2·(2m)) / |K|`.
* reference `b = 128` (`m = 64`): `16384 / |K|`, pole `256 / |K|`, combined
  `16640 / |K|`;
* v5 algebraic block `b = 96` (`m = 48`): `9216 / |K|`, pole `192 / |K|`,
  combined `9408 / |K|`, for this independent-parameter model only.

Everything is `sorry`-free; the witness hypotheses (`τ` with distinct nonzero squares, all
`1 + τ^2 ≠ 0`, and `2 ≠ 0`) are the circle analogue of the "enough distinct nodes"
requirement, satisfied for `K = QM31`.
-/

open Finset MvPolynomial Matrix AspisLiveness AspisLivenessGeneral

namespace AspisCircleLiveness

variable {K : Type*} [Field K]

/-! ### The two denominator-clearing identities -/

/-- Clearing the `x`-block: `(1 - t^2)^s (1 + t^2)^(m-s) = (1 + t^2)^m · x(t)^s`. -/
private lemma xblock_id (m s : ℕ) (t : K) (hQ : (1 + t ^ 2) ≠ 0) (hs : s ≤ m) :
    (1 - t ^ 2) ^ s * (1 + t ^ 2) ^ (m - s)
      = (1 + t ^ 2) ^ m * ((1 - t ^ 2) / (1 + t ^ 2)) ^ s := by
  have hpow : (1 + t ^ 2) ^ m = (1 + t ^ 2) ^ s * (1 + t ^ 2) ^ (m - s) := by
    rw [← pow_add]; congr 1; omega
  rw [div_pow, hpow]
  field_simp

/-- Clearing the `y`-block:
`2 t (1 - t^2)^k (1 + t^2)^(m-1-k) = (1 + t^2)^m · (y(t) · x(t)^k)`. -/
private lemma yblock_id (m k : ℕ) (t : K) (hQ : (1 + t ^ 2) ≠ 0) (hk : k < m) :
    2 * t * (1 - t ^ 2) ^ k * (1 + t ^ 2) ^ (m - 1 - k)
      = (1 + t ^ 2) ^ m *
          (2 * t / (1 + t ^ 2) * ((1 - t ^ 2) / (1 + t ^ 2)) ^ k) := by
  have hpow : (1 + t ^ 2) ^ m = (1 + t ^ 2) ^ (k + 1) * (1 + t ^ 2) ^ (m - 1 - k) := by
    rw [← pow_add]; congr 1; omega
  rw [div_pow, hpow]
  field_simp
  ring

/-! ### The denominator-cleared circle mask-evaluation matrix -/

/-- The circle mask-evaluation matrix for `b = 2m`, in the `b = 2m` circle parameters
`t_1 .. t_b` (variables `Fin (2m)`, one per point).  Row `i` uses the single variable `X i`.
Column `j < m` is the cleared `x^j`; column `m ≤ j < 2m` is the cleared `x^{j-m}·y`, where
each row has been multiplied by `(1 + t_i^2)^m` to remove denominators. -/
noncomputable def circleTMatrix (K : Type*) [Field K] (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) (MvPolynomial (Fin (2 * m)) K) :=
  fun i j =>
    if (j : ℕ) < m then
      (1 - (X i) ^ 2) ^ (j : ℕ) * (1 + (X i) ^ 2) ^ (m - (j : ℕ))
    else
      C 2 * X i * (1 - (X i) ^ 2) ^ ((j : ℕ) - m) *
        (1 + (X i) ^ 2) ^ (m - 1 - ((j : ℕ) - m))

/-- Evaluation of an entry at a parameter assignment `g`. -/
private lemma circleTMatrix_eval (m : ℕ) (g : Fin (2 * m) → K) (i j : Fin (2 * m)) :
    MvPolynomial.eval g (circleTMatrix K m i j)
      = if (j : ℕ) < m then
          (1 - (g i) ^ 2) ^ (j : ℕ) * (1 + (g i) ^ 2) ^ (m - (j : ℕ))
        else
          2 * (g i) * (1 - (g i) ^ 2) ^ ((j : ℕ) - m) *
            (1 + (g i) ^ 2) ^ (m - 1 - ((j : ℕ) - m)) := by
  simp only [circleTMatrix]
  split_ifs with h
  · simp [map_mul, map_pow, map_sub, map_add, map_one]
  · simp [map_mul, map_pow, map_sub, map_add, map_one, MvPolynomial.eval_C]

/-! ### Total-degree bound -/

/-- **Determinant total-degree bound.**  `deg(det M) ≤ 4·m·m`.

Each entry involves only its row variable `X i` to total degree `≤ 2m` (the `x`-block entry
has degree `2j + 2(m-j) = 2m`; the `y`-block entry `1 + 2k + 2(m-1-k) = 2m-1`).  Summing the
uniform column bound `2m` over the `2m` columns gives `4m^2`.  This is `≈ 2×` the free
coordinate bound `2m^2`, the honest cost of clearing the `(1+t^2)` denominators. -/
theorem circleTMatrix_totalDegree_le (K : Type*) [Field K] (m : ℕ) :
    (circleTMatrix K m).det.totalDegree ≤ 4 * m * m := by
  refine (AspisLiveness.totalDegree_det_le (circleTMatrix K m) (fun _ => 2 * m) ?_).trans ?_
  · intro i j
    have hb1 : ((1 - (X i) ^ 2 : MvPolynomial (Fin (2 * m)) K)).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans ?_
      rw [totalDegree_one]
      refine max_le (Nat.zero_le _) ?_
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      rw [totalDegree_X]
    have hb2 : ((1 + (X i) ^ 2 : MvPolynomial (Fin (2 * m)) K)).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_add _ _).trans ?_
      rw [totalDegree_one]
      refine max_le (Nat.zero_le _) ?_
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      rw [totalDegree_X]
    simp only [circleTMatrix]
    split_ifs with h
    · have ha : (((1 - (X i) ^ 2) ^ (j : ℕ) : MvPolynomial (Fin (2 * m)) K)).totalDegree
          ≤ (j : ℕ) * 2 :=
        (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul (le_refl _) hb1)
      have hb : (((1 + (X i) ^ 2) ^ (m - (j : ℕ)) : MvPolynomial (Fin (2 * m)) K)).totalDegree
          ≤ (m - (j : ℕ)) * 2 :=
        (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul (le_refl _) hb2)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have := add_le_add ha hb
      have hjm : (j : ℕ) ≤ m := le_of_lt h
      omega
    · have ha : (((1 - (X i) ^ 2) ^ ((j : ℕ) - m) : MvPolynomial (Fin (2 * m)) K)).totalDegree
          ≤ ((j : ℕ) - m) * 2 :=
        (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul (le_refl _) hb1)
      have hb : (((1 + (X i) ^ 2) ^ (m - 1 - ((j : ℕ) - m)) :
          MvPolynomial (Fin (2 * m)) K)).totalDegree ≤ (m - 1 - ((j : ℕ) - m)) * 2 :=
        (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul (le_refl _) hb2)
      have hCX : ((C 2 * X i : MvPolynomial (Fin (2 * m)) K)).totalDegree ≤ 1 := by
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, totalDegree_X]
      have h1 : ((C 2 * X i * (1 - (X i) ^ 2) ^ ((j : ℕ) - m) :
          MvPolynomial (Fin (2 * m)) K)).totalDegree ≤ 1 + ((j : ℕ) - m) * 2 :=
        (MvPolynomial.totalDegree_mul _ _).trans (add_le_add hCX ha)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have := add_le_add h1 hb
      have hj2 : (j : ℕ) < 2 * m := j.2
      have hjm : m ≤ (j : ℕ) := not_lt.mp h
      omega
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have : 2 * m * (2 * m) = 4 * m * m := by ring
    omega

/-! ### The circle grid witness and `det ≠ 0` -/

/-- The parameter-witness assignment: point `blockEquiv (inl r)` gets `τ r`, point
`blockEquiv (inr r)` gets `-τ r`, so the two circle points `(x_r, ±y_r)` are covered. -/
noncomputable def tWitness (K : Type*) [Field K] (m : ℕ) (τ : Fin m → K) :
    Fin (2 * m) → K :=
  Sum.elim τ (fun r => - τ r) ∘ (blockEquiv m).symm

@[simp] lemma tWitness_inl (m : ℕ) (τ : Fin m → K) (r : Fin m) :
    tWitness K m τ (blockEquiv m (Sum.inl r)) = τ r := by
  simp [tWitness]

@[simp] lemma tWitness_inr (m : ℕ) (τ : Fin m → K) (r : Fin m) :
    tWitness K m τ (blockEquiv m (Sum.inr r)) = - τ r := by
  simp [tWitness]

/-- **Determinant is a nonzero polynomial over the circle parameters.**

For any circle witness family `τ` (distinct squares, nonzero, non-pole) over a field with
`2 ≠ 0`, the denominator-cleared circle mask-evaluation determinant is not identically zero.
At the `±τ` witness the evaluated matrix factors as
`diag(Q^m ⊕ Q^m) · fromBlocks V (WV) V (-(WV))`, whose determinant is
`(∏ Q_r^m)^2 · (∏ (-y_r - y_r)) · (det V)^2 ≠ 0`. -/
theorem circleTMatrix_det_ne_zero (K : Type*) [Field K] (m : ℕ) (τ : Fin m → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0)
    (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2))
    (h2 : (2 : K) ≠ 0) :
    (circleTMatrix K m).det ≠ 0 := by
  set x : Fin m → K := fun r => (1 - (τ r) ^ 2) / (1 + (τ r) ^ 2) with hx
  set y : Fin m → K := fun r => 2 * (τ r) / (1 + (τ r) ^ 2) with hy
  set Qm : Fin m → K := fun r => (1 + (τ r) ^ 2) ^ m with hQm
  -- circle-point data facts
  have hyne : ∀ r, y r ≠ 0 := by
    intro r; rw [hy]; exact div_ne_zero (mul_ne_zero h2 (hτ0 r)) (hQ r)
  have hxinj : Function.Injective x := by
    intro a b hab
    apply hτsq
    simp only [hx] at hab
    rw [div_eq_div_iff (hQ a) (hQ b)] at hab
    have h2ab : (2 : K) * ((τ a) ^ 2 - (τ b) ^ 2) = 0 := by linear_combination -hab
    have hab' : (τ a) ^ 2 - (τ b) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2ab with h | h
      · exact absurd h h2
      · exact h
    exact sub_eq_zero.mp hab'
  -- the two evaluated block matrices
  set Mdiag : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    Matrix.fromBlocks (Matrix.diagonal Qm) 0 0 (Matrix.diagonal Qm) with hMdiagDef
  set Mcore : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    Matrix.fromBlocks (Matrix.vandermonde x) (Matrix.diagonal y * Matrix.vandermonde x)
      (Matrix.vandermonde x) (-(Matrix.diagonal y * Matrix.vandermonde x)) with hMcoreDef
  refine AspisLiveness.det_ne_zero_of_eval (circleTMatrix K m) (tWitness K m τ) ?_
  set E := (circleTMatrix K m).map (MvPolynomial.eval (tWitness K m τ)) with hE
  -- block factorisation of the reindexed evaluated matrix
  have hEP : E.submatrix (blockEquiv m) (blockEquiv m) = Mdiag * Mcore := by
    rw [hMdiagDef, hMcoreDef, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, add_zero, zero_add]
    ext a b
    rcases a with r | r <;> rcases b with s | s
    · -- (inl r, inl s): top-left = diag Qm * V
      rw [Matrix.submatrix_apply, hE, Matrix.map_apply, circleTMatrix_eval,
        Matrix.fromBlocks_apply₁₁, Matrix.diagonal_mul, Matrix.vandermonde_apply]
      simp only [blockEquiv_inl_val, tWitness_inl]
      rw [if_pos s.isLt]
      simp only [hQm, hx]
      exact xblock_id m s (τ r) (hQ r) (le_of_lt s.isLt)
    · -- (inl r, inr s): top-right = diag Qm * (diag y * V)
      rw [Matrix.submatrix_apply, hE, Matrix.map_apply, circleTMatrix_eval,
        Matrix.fromBlocks_apply₁₂]
      simp only [blockEquiv_inr_val, tWitness_inl, Nat.add_sub_cancel_left]
      rw [if_neg (show ¬ ((m : ℕ) + (s : ℕ) < m) by omega)]
      rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.vandermonde_apply]
      simp only [hQm, hx, hy]
      exact yblock_id m s (τ r) (hQ r) s.isLt
    · -- (inr r, inl s): bottom-left = diag Qm * V
      rw [Matrix.submatrix_apply, hE, Matrix.map_apply, circleTMatrix_eval,
        Matrix.fromBlocks_apply₂₁, Matrix.diagonal_mul, Matrix.vandermonde_apply]
      simp only [blockEquiv_inl_val, tWitness_inr, neg_sq]
      rw [if_pos s.isLt]
      simp only [hQm, hx]
      exact xblock_id m s (τ r) (hQ r) (le_of_lt s.isLt)
    · -- (inr r, inr s): bottom-right = diag Qm * (-(diag y * V))
      rw [Matrix.submatrix_apply, hE, Matrix.map_apply, circleTMatrix_eval,
        Matrix.fromBlocks_apply₂₂]
      simp only [blockEquiv_inr_val, tWitness_inr, neg_sq, Nat.add_sub_cancel_left]
      rw [if_neg (show ¬ ((m : ℕ) + (s : ℕ) < m) by omega)]
      rw [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.diagonal_mul, Matrix.vandermonde_apply]
      simp only [hQm, hx, hy]
      linear_combination -yblock_id m s (τ r) (hQ r) s.isLt
  -- determinant of the factorisation
  have hMcoreFact : Mcore = Matrix.fromBlocks 1 (Matrix.diagonal y) 1 (-(Matrix.diagonal y))
      * Matrix.fromBlocks (Matrix.vandermonde x) 0 0 (Matrix.vandermonde x) := by
    rw [hMcoreDef, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul]
  have hMid : (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) K) (Matrix.diagonal y) 1
      (-(Matrix.diagonal y))).det = ∏ r, (- y r - y r) := by
    rw [Matrix.det_fromBlocks_one₁₁, Matrix.one_mul]
    simp only [Matrix.diagonal_neg, Matrix.diagonal_sub, Matrix.det_diagonal]
  have hdetE : E.det = ((∏ r, Qm r) * (∏ r, Qm r))
      * ((∏ r, (- y r - y r)) * ((Matrix.vandermonde x).det * (Matrix.vandermonde x).det)) := by
    rw [← Matrix.det_submatrix_equiv_self (blockEquiv m) E, hEP, Matrix.det_mul,
      hMdiagDef, Matrix.det_fromBlocks_zero₁₂]
    simp only [Matrix.det_diagonal]
    rw [hMcoreFact, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, hMid]
  -- each factor is nonzero
  have hQmne : (∏ r, Qm r) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro r _; rw [hQm]; exact pow_ne_zero _ (hQ r)
  have hyyne : (∏ r, (- y r - y r)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro r _ h
    apply hyne r
    have : (2 : K) * y r = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h2
    · exact h'
  have hVne : (Matrix.vandermonde x).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff).mpr hxinj
  rw [hdetE]
  exact mul_ne_zero (mul_ne_zero hQmne hQmne) (mul_ne_zero hyyne (mul_ne_zero hVne hVne))

/-! ### The liveness bound over circle points -/

/-- **Layer 2b over independent rational circle parameters.**

Over any finite field `K` with a circle witness `τ` (distinct nonzero squares, all
non-pole) and `2 ≠ 0`, the fraction of parameter tuples `t ∈ K^(2m)` on which the circle
mask-evaluation matrix is singular is at most `4·m·m / |K|`.  Each point is drawn by its
single circle parameter `t_i`, so this is a bound over independent points on
the one-dimensional circle rather than free `K^(2b)` coordinates. It does not
describe the wire's discrete query-index distribution. -/
theorem circle_point_schedule_fail_le (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (τ : Fin m → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0) (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2)) (h2 : (2 : K) ≠ 0) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * m) → K)) |
          ((circleTMatrix K m).map (MvPolynomial.eval f)).det = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * m))
      ≤ (4 * m * m) / Fintype.card K := by
  refine (schedule_fail_fraction_le_univ (circleTMatrix K m)
      (circleTMatrix_det_ne_zero K m τ hQ hτ0 hτsq h2)).trans ?_
  gcongr
  exact_mod_cast circleTMatrix_totalDegree_le K m

/-- **The excluded pole set.**  The parameterization misses the point `(-1, 0)` and is
undefined where `1 + t_i^2 = 0` (the two "poles" `t = ±i`, when they exist in `K`).
The fraction of independent parameter tuples with some coordinate a pole is at
most `2·(2m) / |K|` (degree of `∏_i (1 + t_i^2)`). -/
theorem circle_pole_fraction_le (K : Type*) [Field K] [Fintype K] [DecidableEq K] (m : ℕ) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * m) → K)) | ∃ i, (1 : K) + (f i) ^ 2 = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * m))
      ≤ (2 * (2 * m)) / Fintype.card K := by
  have hQne : (∏ i : Fin (2 * m), (1 + (X i) ^ 2) : MvPolynomial (Fin (2 * m)) K) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _ h
    have := congrArg (MvPolynomial.eval (fun _ => (0 : K))) h
    simp at this
  have hdeg : (∏ i : Fin (2 * m), (1 + (X i) ^ 2) :
      MvPolynomial (Fin (2 * m)) K).totalDegree ≤ 2 * (2 * m) := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (2 * m))),
        (1 + (X i) ^ 2 : MvPolynomial (Fin (2 * m)) K).totalDegree ≤ 2 := by
      intro i _
      refine (MvPolynomial.totalDegree_add _ _).trans ?_
      rw [totalDegree_one]
      refine max_le (Nat.zero_le _) ?_
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      rw [totalDegree_X]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hset : {f ∈ (Finset.univ : Finset (Fin (2 * m) → K)) | ∃ i, (1 : K) + (f i) ^ 2 = 0}
      = {f ∈ (Finset.univ : Finset (Fin (2 * m) → K)) |
          MvPolynomial.eval f (∏ i, (1 + (X i) ^ 2)) = 0} := by
    apply Finset.filter_congr
    intro f _
    rw [map_prod]
    simp only [map_add, map_one, map_pow, MvPolynomial.eval_X, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and]
  have h := MvPolynomial.schwartz_zippel_totalDegree hQne (Finset.univ : Finset K)
  simp only [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [hset]
  refine h.trans ?_
  gcongr
  exact_mod_cast hdeg

/-- **Combined liveness over circle sampling.**  Drawing each point's parameter `t_i`
uniformly, the probability that the sample is either invalid (a pole) or gives a singular
mask matrix is at most `(4·m·m + 2·(2m)) / |K|`.  Proved by applying Schwartz–Zippel to the
product `det · ∏_i (1 + t_i^2)`, whose zero set is exactly `{singular} ∪ {pole}`. -/
theorem circle_point_liveness (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (τ : Fin m → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0) (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2)) (h2 : (2 : K) ≠ 0) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * m) → K)) |
          ((circleTMatrix K m).map (MvPolynomial.eval f)).det = 0 ∨
            ∃ i, (1 : K) + (f i) ^ 2 = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * m))
      ≤ (4 * m * m + 2 * (2 * m)) / Fintype.card K := by
  set BAD : MvPolynomial (Fin (2 * m)) K :=
    (circleTMatrix K m).det * ∏ i, (1 + (X i) ^ 2) with hBAD
  have hdet := circleTMatrix_det_ne_zero K m τ hQ hτ0 hτsq h2
  have hQne : (∏ i : Fin (2 * m), (1 + (X i) ^ 2) : MvPolynomial (Fin (2 * m)) K) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _ h
    have := congrArg (MvPolynomial.eval (fun _ => (0 : K))) h
    simp at this
  have hBADne : BAD ≠ 0 := by rw [hBAD]; exact mul_ne_zero hdet hQne
  have hBADdeg : BAD.totalDegree ≤ 4 * m * m + 2 * (2 * m) := by
    rw [hBAD]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    refine add_le_add (circleTMatrix_totalDegree_le K m) ?_
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (2 * m))),
        (1 + (X i) ^ 2 : MvPolynomial (Fin (2 * m)) K).totalDegree ≤ 2 := by
      intro i _
      refine (MvPolynomial.totalDegree_add _ _).trans ?_
      rw [totalDegree_one]
      refine max_le (Nat.zero_le _) ?_
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      rw [totalDegree_X]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hset : {f ∈ (Finset.univ : Finset (Fin (2 * m) → K)) |
        ((circleTMatrix K m).map (MvPolynomial.eval f)).det = 0 ∨
          ∃ i, (1 : K) + (f i) ^ 2 = 0}
      = {f ∈ (Finset.univ : Finset (Fin (2 * m) → K)) | MvPolynomial.eval f BAD = 0} := by
    apply Finset.filter_congr
    intro f _
    rw [hBAD, map_mul,
      show MvPolynomial.eval f (circleTMatrix K m).det
        = ((circleTMatrix K m).map (MvPolynomial.eval f)).det from by
          rw [RingHom.map_det, RingHom.mapMatrix_apply],
      map_prod]
    simp only [map_add, map_one, map_pow, MvPolynomial.eval_X, mul_eq_zero,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  have h := MvPolynomial.schwartz_zippel_totalDegree hBADne (Finset.univ : Finset K)
  simp only [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [hset]
  refine h.trans ?_
  gcongr
  exact_mod_cast hBADdeg

/-! ### Numerical specialisations -/

/-- **Reference circle-point liveness, `b = 128` (`m = 64`).**  `4·64·64 = 16384` and
`2·(2·64) = 256`; the combined bad-or-pole fraction over the 128 circle parameters is
`≤ (16384 + 256) / |K| = 16640 / |K|`. For `K = QM31`
(`|K| = (2³¹−1)⁴ ≈ 2¹²⁴`) this is
`≈ 2⁻¹¹⁰` in the independent-parameter model. -/
theorem circle_point_liveness_b128 (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (τ : Fin 64 → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0) (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2)) (h2 : (2 : K) ≠ 0) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * 64) → K)) |
          ((circleTMatrix K 64).map (MvPolynomial.eval f)).det = 0 ∨
            ∃ i, (1 : K) + (f i) ^ 2 = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * 64))
      ≤ (4 * 64 * 64 + 2 * (2 * 64)) / Fintype.card K :=
  circle_point_liveness K 64 τ hQ hτ0 hτsq h2

/-- Reference singular-only bound: `≤ 16384 / |K|` over 128 independent
circle parameters. -/
theorem circle_point_schedule_fail_le_b128 (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (τ : Fin 64 → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0) (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2)) (h2 : (2 : K) ≠ 0) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * 64) → K)) |
          ((circleTMatrix K 64).map (MvPolynomial.eval f)).det = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * 64))
      ≤ (4 * 64 * 64) / Fintype.card K :=
  circle_point_schedule_fail_le K 64 τ hQ hτ0 hτsq h2

/-- **V5 algebraic-block liveness, `b = 96` (`m = 48`).** The combined
bad-or-pole fraction over 96 independent circle parameters is
`≤ (9216 + 192) / |K| = 9408 / |K|`. This is not a production-wire
availability theorem. -/
theorem circle_point_liveness_b96 (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (τ : Fin 48 → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0) (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2)) (h2 : (2 : K) ≠ 0) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * 48) → K)) |
          ((circleTMatrix K 48).map (MvPolynomial.eval f)).det = 0 ∨
            ∃ i, (1 : K) + (f i) ^ 2 = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * 48))
      ≤ (4 * 48 * 48 + 2 * (2 * 48)) / Fintype.card K :=
  circle_point_liveness K 48 τ hQ hτ0 hτsq h2

/-- V5 algebraic-block singular-only bound: `≤ 9216 / |K|` over 96
independent circle parameters. -/
theorem circle_point_schedule_fail_le_b96
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (τ : Fin 48 → K)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0) (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2)) (h2 : (2 : K) ≠ 0) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * 48) → K)) |
          ((circleTMatrix K 48).map (MvPolynomial.eval f)).det = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * 48))
      ≤ (4 * 48 * 48) / Fintype.card K :=
  circle_point_schedule_fail_le K 48 τ hQ hτ0 hτsq h2

end AspisCircleLiveness

/-- Numeric sanity for the two reference widths. -/
example : (4 * 64 * 64 : ℕ) = 16384 := by norm_num
example : (2 * (2 * 64) : ℕ) = 256 := by norm_num
example : (4 * 64 * 64 + 2 * (2 * 64) : ℕ) = 16640 := by norm_num
example : (4 * 48 * 48 : ℕ) = 9216 := by norm_num
example : (2 * (2 * 48) : ℕ) = 192 := by norm_num
example : (4 * 48 * 48 + 2 * (2 * 48) : ℕ) = 9408 := by norm_num

#print axioms AspisCircleLiveness.circleTMatrix_det_ne_zero
#print axioms AspisCircleLiveness.circleTMatrix_totalDegree_le
#print axioms AspisCircleLiveness.circle_point_schedule_fail_le
#print axioms AspisCircleLiveness.circle_pole_fraction_le
#print axioms AspisCircleLiveness.circle_point_liveness
#print axioms AspisCircleLiveness.circle_point_liveness_b128
#print axioms AspisCircleLiveness.circle_point_liveness_b96
