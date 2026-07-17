import Mathlib
import AspisFormal.CircleVandermonde

/-!
# Layer 2b, general `b`: circle mask-evaluation liveness for arbitrary leakage budget

`CircleVandermonde` proves the Schwartz–Zippel liveness bridge and works out the
concrete cases `b = 2` and `b = 4`, the latter with a matrix *literal* `!![…]`.
Literals do not scale: reducing `det` and the degree count of a `b × b` literal
blows up in `whnf`.

Here we redo the argument **functionally** for arbitrary even `b = 2 m`, so that
`det` and the degree bound are discharged by *general* lemmas, never by reducing
literal entries.

## Matrix representation

We use the **explicit block form** of the circle-FFT mask space
`V_{2m} = { p(x) + y q(x) : deg p, deg q ≤ m − 1 }`, with monomial basis

```
1, x, x², …, x^{m-1},  y, y·x, y·x², …, y·x^{m-1}      (2m functions)
```

For `2m` schedule points `pᵢ = (x_i, y_i)` (coordinates the `2·(2m)` variables
`X 0 … X (4m-1)`, point `i` using `X (2i)` and `X (2i+1)`), the mask-evaluation
matrix is `M i j = Bⱼ(pᵢ)`.  Column `j < m` is `x^j`; column `m ≤ j < 2m` is
`x^{j-m}·y`.

Why the block form (rather than the Chebyshev/`φ_k` recursion): at a **grid**
witness (`m` distinct `x`-nodes `ν 0 … ν (m-1)`, each taken once with `y = 0` and
once with `y = 1`) the evaluated matrix reindexes to `fromBlocks V 0 V V` with `V`
the ordinary Vandermonde on the nodes, so its determinant is `(det V)²`, nonzero
exactly when the nodes are distinct — a one-line consequence of
`Matrix.det_vandermonde_ne_zero_iff`, with no exceptional-set casework.

## Deliverables

* `circleMatrixGen K m` — the functional matrix (`b = 2m`, variables `Fin (2·(2m))`).
* `circleMatrixGen_det_ne_zero` — `det ≠ 0` for **any** injective node family
  `ν : Fin m → K` (the block-triangular grid witness).
* `circleMatrixGen_totalDegree_le` — `det.totalDegree ≤ 2·m·m` (uniform
  column-degree bound `m`; the honest column-degree *sum* is `m²`, we prove the
  clean `2m²`).
* `circle_schedule_fail_le` — bad-schedule fraction `≤ 2·m·m / |K|` for any `b = 2m`.
* `circle_schedule_fail_le_deployed` — the representative deployed budget
  `b = 128` (`m = 64`): fraction `≤ 8192 / |K|` (over `256` coordinate variables).

Everything is `sorry`-free; the only "hypothesis" is the existence of `m` distinct
field elements (`ν` injective), which for the deployed field `QM31`
(`|K| = (2³¹−1)⁴ ≫ 64`) is immediate.
-/

open Finset MvPolynomial Matrix AspisLiveness

namespace AspisLivenessGeneral

variable {K : Type*} [Field K]

/-! ### The functional circle mask-evaluation matrix -/

/-- `x`-coordinate variable index of schedule point `i` (the even index `2i`). -/
def xIdx {m : ℕ} (i : Fin (2 * m)) : Fin (2 * (2 * m)) :=
  ⟨2 * i.1, by have := i.2; omega⟩

/-- `y`-coordinate variable index of schedule point `i` (the odd index `2i+1`). -/
def yIdx {m : ℕ} (i : Fin (2 * m)) : Fin (2 * (2 * m)) :=
  ⟨2 * i.1 + 1, by have := i.2; omega⟩

@[simp] lemma xIdx_val {m : ℕ} (i : Fin (2 * m)) : (xIdx i).1 = 2 * i.1 := rfl
@[simp] lemma yIdx_val {m : ℕ} (i : Fin (2 * m)) : (yIdx i).1 = 2 * i.1 + 1 := rfl

/-- The circle mask-evaluation matrix for `b = 2m`, entries in
`MvPolynomial (Fin (2·(2m))) K`.  Column `j < m` is the basis function `x^j`
evaluated at each point; column `m ≤ j < 2m` is `x^{j-m}·y`. -/
noncomputable def circleMatrixGen (K : Type*) [Field K] (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) (MvPolynomial (Fin (2 * (2 * m))) K) :=
  fun i j =>
    if (j : ℕ) < m then (X (xIdx i)) ^ (j : ℕ)
    else (X (xIdx i)) ^ ((j : ℕ) - m) * X (yIdx i)

/-! ### Total-degree bound -/

/-- **Determinant total-degree bound.** `deg(det M) ≤ 2·m·m`.

Each entry of column `j` has total degree `≤ m` (a power `x^{≤m-1}`, or such a
power times `y`, both of degree `≤ m`), so by `totalDegree_det_le` the determinant
has total degree `≤ ∑_{j} m = (2m)·m`.  (The tight column-degree sum is `m²`; the
uniform bound `2m²` we prove here is what the deployed estimate needs.) -/
theorem circleMatrixGen_totalDegree_le (K : Type*) [Field K] (m : ℕ) :
    (circleMatrixGen K m).det.totalDegree ≤ 2 * m * m := by
  refine (totalDegree_det_le (circleMatrixGen K m) (fun _ => m) ?_).trans ?_
  · intro i j
    simp only [circleMatrixGen]
    split_ifs with h
    · refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      rw [totalDegree_X]
      omega
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have h1 : ((X (xIdx i) : MvPolynomial (Fin (2 * (2 * m))) K) ^ ((j : ℕ) - m)).totalDegree
          ≤ (j : ℕ) - m := by
        refine (MvPolynomial.totalDegree_pow _ _).trans ?_
        rw [totalDegree_X]; omega
      have h2 : (X (yIdx i) : MvPolynomial (Fin (2 * (2 * m))) K).totalDegree ≤ 1 := by
        rw [totalDegree_X]
      have hj := j.2
      have := add_le_add h1 h2
      omega
  · simp [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-! ### The grid witness and `det ≠ 0` -/

/-- Index equivalence `Fin m ⊕ Fin m ≃ Fin (2m)` used to expose the block form. -/
def blockEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (two_mul m).symm)

@[simp] lemma blockEquiv_inl_val (m : ℕ) (k : Fin m) :
    ((blockEquiv m) (Sum.inl k) : ℕ) = k.1 := by
  simp only [blockEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply_coe,
    Fin.val_castAdd]

@[simp] lemma blockEquiv_inr_val (m : ℕ) (k : Fin m) :
    ((blockEquiv m) (Sum.inr k) : ℕ) = m + k.1 := by
  simp only [blockEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply_coe,
    Fin.val_natAdd]

/-- The grid witness assignment: point `i` gets `x`-coordinate `ν (i mod m)` and
`y`-coordinate `0` if `i < m`, else `1`. -/
noncomputable def circleWitness (K : Type*) [Field K] (m : ℕ) (hm : 0 < m) (ν : Fin m → K) :
    Fin (2 * (2 * m)) → K :=
  fun v =>
    if v.1 % 2 = 0 then ν ⟨(v.1 / 2) % m, Nat.mod_lt _ hm⟩
    else (if (v.1 / 2) < m then 0 else 1)

lemma witness_x {m : ℕ} (hm : 0 < m) (ν : Fin m → K) (i : Fin (2 * m)) :
    circleWitness K m hm ν (xIdx i) = ν ⟨i.1 % m, Nat.mod_lt _ hm⟩ := by
  unfold circleWitness
  simp only [xIdx_val]
  rw [if_pos (by omega : (2 * i.1) % 2 = 0)]
  congr 1
  simp only [Fin.mk.injEq]
  rw [show 2 * i.1 / 2 = i.1 from by omega]

lemma witness_y {m : ℕ} (hm : 0 < m) (ν : Fin m → K) (i : Fin (2 * m)) :
    circleWitness K m hm ν (yIdx i) = (if i.1 < m then (0 : K) else 1) := by
  have hmod : ¬ (2 * i.1 + 1) % 2 = 0 := by omega
  have hdiv : (2 * i.1 + 1) / 2 = i.1 := by omega
  unfold circleWitness
  simp only [yIdx_val]
  rw [if_neg hmod]
  simp only [hdiv]

/-- Entrywise value of the evaluated matrix at the grid witness: `eval` pushed
through the `if`, `pow`, `mul`, and `X`. -/
lemma eval_entry {m : ℕ} (hm : 0 < m) (ν : Fin m → K) (i j : Fin (2 * m)) :
    ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))) i j
      = if (j : ℕ) < m then (ν ⟨i.1 % m, Nat.mod_lt _ hm⟩) ^ (j : ℕ)
        else (ν ⟨i.1 % m, Nat.mod_lt _ hm⟩) ^ ((j : ℕ) - m) * (if i.1 < m then (0 : K) else 1) := by
  rw [Matrix.map_apply]
  simp only [circleMatrixGen, apply_ite (eval (circleWitness K m hm ν)), map_pow, map_mul,
    MvPolynomial.eval_X, witness_x hm ν i, witness_y hm ν i]

/-- **Determinant is a nonzero polynomial (general `b = 2m`).**

For any injective family of `m` field elements `ν`, the circle mask-evaluation
determinant is not identically zero: at the grid witness the evaluated matrix
reindexes to `fromBlocks V 0 V V` with `V = vandermonde ν`, so its determinant is
`(det V)² ≠ 0` (nodes distinct ⇒ Vandermonde nonsingular).  Then
`det_ne_zero_of_eval`. -/
theorem circleMatrixGen_det_ne_zero (K : Type*) [Field K] (m : ℕ)
    (ν : Fin m → K) (hν : Function.Injective ν) :
    (circleMatrixGen K m).det ≠ 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [Matrix.det_isEmpty]
  -- The Vandermonde block.
  set A : Matrix (Fin m) (Fin m) K := Matrix.vandermonde ν with hA
  refine det_ne_zero_of_eval (circleMatrixGen K m) (circleWitness K m hm ν) ?_
  -- Reindex the evaluated matrix into block form.
  have hsub : ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))).submatrix
      (blockEquiv m) (blockEquiv m) = fromBlocks A 0 A A := by
    ext r c
    rcases r with k | k <;> rcases c with l | l
    · -- (inl k, inl l): top-left block = V
      rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₁₁]
      rw [blockEquiv_inl_val, blockEquiv_inl_val]
      rw [if_pos l.2, hA, Matrix.vandermonde_apply]
      rw [show (⟨k.1 % m, Nat.mod_lt _ hm⟩ : Fin m) = k from Fin.ext (Nat.mod_eq_of_lt k.2)]
    · -- (inl k, inr l): top-right block = 0
      rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [blockEquiv_inl_val, blockEquiv_inr_val]
      rw [if_neg (by omega : ¬ m + l.1 < m), if_pos k.2, mul_zero]
    · -- (inr k, inl l): bottom-left block = V
      have hmodk : (m + k.1) % m = k.1 := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt k.2
      rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₂₁]
      rw [blockEquiv_inr_val, blockEquiv_inl_val]
      rw [if_pos l.2, hA, Matrix.vandermonde_apply]
      rw [show (⟨(m + k.1) % m, Nat.mod_lt _ hm⟩ : Fin m) = k from Fin.ext hmodk]
    · -- (inr k, inr l): bottom-right block = V
      have hmodk : (m + k.1) % m = k.1 := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt k.2
      rw [Matrix.submatrix_apply, eval_entry, Matrix.fromBlocks_apply₂₂]
      rw [blockEquiv_inr_val, blockEquiv_inr_val]
      rw [if_neg (by omega : ¬ m + l.1 < m), if_neg (by omega : ¬ m + k.1 < m), mul_one,
        hA, Matrix.vandermonde_apply,
        show (⟨(m + k.1) % m, Nat.mod_lt _ hm⟩ : Fin m) = k from Fin.ext hmodk,
        show m + l.1 - m = l.1 from by omega]
  -- det of the evaluated matrix = (det V)².
  have hdet : ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))).det = A.det * A.det := by
    rw [← Matrix.det_submatrix_equiv_self (blockEquiv m)
        ((circleMatrixGen K m).map (eval (circleWitness K m hm ν))),
      hsub, Matrix.det_fromBlocks_zero₁₂]
  rw [hdet]
  have hV : A.det ≠ 0 := by rw [hA]; exact (Matrix.det_vandermonde_ne_zero_iff).mpr hν
  exact mul_ne_zero hV hV

/-! ### The liveness bound for arbitrary `b = 2m` -/

/-- **Layer 2b for arbitrary even `b = 2m`.**

Over any finite field `K` with at least `m` elements (encoded by an injective
`ν : Fin m → K`), the fraction of schedules on which the `b = 2m` circle
mask-evaluation matrix is singular is at most `2·m·m / |K|`. -/
theorem circle_schedule_fail_le (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (ν : Fin m → K) (hν : Function.Injective ν) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * (2 * m)) → K)) |
          ((circleMatrixGen K m).map (MvPolynomial.eval f)).det = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * (2 * m)))
      ≤ (2 * m * m) / Fintype.card K := by
  refine (schedule_fail_fraction_le_univ (circleMatrixGen K m)
      (circleMatrixGen_det_ne_zero K m ν hν)).trans ?_
  gcongr
  exact_mod_cast circleMatrixGen_totalDegree_le K m

/-- **Deployed budget `b = 128` (`m = 64`).**

`2·64·64 = 8192` and `2·(2·64) = 256` coordinate variables: the bad-schedule
fraction is `≤ 8192 / |K|`.  For `K = QM31` (`|K| = (2³¹−1)⁴ ≈ 2¹²⁴`) this is
`≈ 2⁻¹¹¹`, so the resample loop succeeds essentially immediately.  Any injective
`ν : Fin 64 → K` witnesses the (trivially satisfied) "enough distinct nodes"
requirement. -/
theorem circle_schedule_fail_le_deployed (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (ν : Fin 64 → K) (hν : Function.Injective ν) :
    (#{f ∈ (Finset.univ : Finset (Fin (2 * (2 * 64)) → K)) |
          ((circleMatrixGen K 64).map (MvPolynomial.eval f)).det = 0} : ℚ≥0)
        / (Fintype.card K ^ (2 * (2 * 64)))
      ≤ (2 * 64 * 64) / Fintype.card K :=
  circle_schedule_fail_le K 64 ν hν

end AspisLivenessGeneral

/-- Numeric sanity: the deployed constants. -/
example : (2 * 64 * 64 : ℕ) = 8192 := by norm_num
example : (2 * (2 * 64) : ℕ) = 256 := by norm_num



#print axioms AspisLivenessGeneral.circleMatrixGen_det_ne_zero
#print axioms AspisLivenessGeneral.circleMatrixGen_totalDegree_le
#print axioms AspisLivenessGeneral.circle_schedule_fail_le
#print axioms AspisLivenessGeneral.circle_schedule_fail_le_deployed
