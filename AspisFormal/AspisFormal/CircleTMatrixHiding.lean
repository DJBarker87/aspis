import Mathlib
import AspisFormal.CirclePointLiveness
import AspisFormal.CircleVandermondeGeneral
import AspisFormal.MaskingHiding

/-!
# Correcting the `circleMatrixGen` → `circleTMatrix` seam: hiding through a row-rescaled mask

## The seam this file corrects

`ViewModel.lean` binds obligation (a) to `circleMatrixGen` — the **free-coordinate**
block-form mask-evaluation matrix, whose entries treat each point's `(x_i, y_i)` as two
*independent* variables ranging over `K^(2·(2m))`.  But `circleMatrixGen` is **not** the
matrix the deployment can certify honest.  The only circle-**honest** liveness / `det ≠ 0`
proof is `CirclePointLiveness.lean`'s `circleTMatrix` (points constrained to the unit circle
`x² + y² = 1`, each drawn by a single parameter `t_i ∈ K`, each row scaled by the
denominator-clearing factor `(1 + t_i²)^m`). That liveness theorem concerns
independent field parameters, not the wire's discrete query-index distribution.
Free coordinates are *not* what Fiat–Shamir
samples; circle points are.  So binding hiding to `circleMatrixGen` claims `det ≠ 0` over a
distribution the prover never uses, while the matrix that is actually proved live —
`circleTMatrix` — is a different matrix.

After rational parametrisation, the candidate leakage matrix is not
`circleTMatrix` bare either: it has the form

```
    Lcandidate  =  D · circleTMatrix(sched),      D = diagonal(d),  d_i ≠ 0,
```

For the aligned Rust reserve block, after rational circle parametrisation, the
exact rescale is `d_i = B_896(p_i) / (1 + t_i²)^m`. The denominator appears
because `circleTMatrix` already contains the denominator-clearing factor. Left-multiplying
by a nonzero diagonal is a *row rescale*: it multiplies the determinant by `∏ d_i`
and therefore **cannot** change whether the determinant vanishes.

## What is corrected here

This file routes the matrix model through `circleTMatrix` with a nonzero-diagonal rescale,
rather than through `circleMatrixGen`. Concretely:

* the candidate matrix is `D · circleTMatrix`, a nonzero-diagonal rescale of the
  circle-**honest** matrix, so `det ≠ 0` (and hence hiding) is **preserved**;
* a concrete field-valued binding must therefore use
  `leakageMap = D · circleTMatrix`, **not** `= circleMatrixGen`.

`det ≠ 0` for the rescaled matrix follows from `circleTMatrix_det_ne_zero` (already proved in
`CirclePointLiveness`) together with `∏ d_i ≠ 0`, via the diagonal-rescale determinant
identity `det (diagonal d · A) = (∏ d_i) · det A`.  Nothing about the diagonal rescale weakens
hiding: a nonzero-diagonal left factor is an invertible row operation.

Everything here is `sorry`-free with axioms `[propext, Classical.choice, Quot.sound]`.
-/

open MvPolynomial Matrix AspisCircleLiveness

namespace AspisCircleTMatrixHiding

/-! ## Part 1 — the diagonal-rescale determinant lemma

Over any commutative ring, left-multiplying by a diagonal matrix multiplies the determinant
by the product of the diagonal.  Over a domain (in particular a field, or `MvPolynomial` over
a field), the rescaled determinant is nonzero **iff** the original is, provided the diagonal
entries are nonzero.  This is the algebraic core of "a nonzero-diagonal rescale preserves
`det ≠ 0`". -/

section DiagRescale

variable {R : Type*} [CommRing R]

/-- **Diagonal-rescale determinant identity.**  `det (diagonal d · A) = (∏ d_i) · det A`. -/
theorem det_diagonal_mul {n : ℕ} (d : Fin n → R) (A : Matrix (Fin n) (Fin n) R) :
    (Matrix.diagonal d * A).det = (∏ i, d i) * A.det := by
  rw [Matrix.det_mul, Matrix.det_diagonal]

variable [NoZeroDivisors R]

/-- **Nonzero-diagonal rescale preserves `det ≠ 0` (the consumer form).**  If `∏ d_i ≠ 0` and
`det A ≠ 0` then `det (diagonal d · A) ≠ 0`.  Over a domain this is `mul_ne_zero` applied to
the identity `det (diagonal d · A) = (∏ d_i) · det A`. -/
theorem det_diagonal_mul_ne_zero {n : ℕ} {d : Fin n → R} (hd : (∏ i, d i) ≠ 0)
    {A : Matrix (Fin n) (Fin n) R} (hA : A.det ≠ 0) :
    (Matrix.diagonal d * A).det ≠ 0 := by
  rw [det_diagonal_mul]
  exact mul_ne_zero hd hA

/-- **`det ≠ 0` is invariant under a nonzero-diagonal rescale (the `↔` form).**  With every
`d_i ≠ 0`, `det (diagonal d · A) ≠ 0 ↔ det A ≠ 0`.  So routing through `D · circleTMatrix`
neither creates nor destroys nonsingularity relative to `circleTMatrix`. -/
theorem det_diagonal_mul_ne_zero_iff {n : ℕ} [Nontrivial R] {d : Fin n → R}
    (hd : ∀ i, d i ≠ 0) (A : Matrix (Fin n) (Fin n) R) :
    (Matrix.diagonal d * A).det ≠ 0 ↔ A.det ≠ 0 := by
  have hp : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  rw [det_diagonal_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun hA => ⟨hp, hA⟩⟩

end DiagRescale

/-! ## Part 2 — non-vacuity of a symbolic row rescale

`circleTMatrix_det_ne_zero` (from `CirclePointLiveness`) proves the circle-honest matrix has a
nonzero symbolic determinant for any circle witness `τ`.  The diagonal-rescale lemma lifts
this immediately to any polynomial row rescale `D · circleTMatrix`: its symbolic
determinant is nonzero whenever the per-row factors have nonzero product. This is a
generic algebraic result, not a claim that the concrete Rust map is itself a
polynomial matrix in the rational parameters. -/

/-- **The row-rescaled leakage matrix has nonzero symbolic determinant.**  For any circle witness
`τ` (distinct nonzero squares, non-pole) over a field with `2 ≠ 0`, and any per-row factor
family `D : Fin (2m) → MvPolynomial …` with nonzero product, the rescaled matrix
`D · circleTMatrix K m` has `det ≠ 0` as a polynomial.  `det ≠ 0` is preserved under the
nonzero-diagonal rescale. -/
theorem rescaledTMatrix_det_ne_zero {K : Type*} [Field K] (m : ℕ) (τ : Fin m → K)
    (D : Fin (2 * m) → MvPolynomial (Fin (2 * m)) K)
    (hD : (∏ i, D i) ≠ 0)
    (hQ : ∀ r, (1 + (τ r) ^ 2 : K) ≠ 0) (hτ0 : ∀ r, τ r ≠ 0)
    (hτsq : Function.Injective (fun r => (τ r) ^ 2)) (h2 : (2 : K) ≠ 0) :
    (Matrix.diagonal D * circleTMatrix K m).det ≠ 0 :=
  det_diagonal_mul_ne_zero hD (circleTMatrix_det_ne_zero K m τ hQ hτ0 hτsq h2)

/-! ## Part 3 — hiding through a field-valued `D · circleTMatrix`

The analogue of `MaskingHiding.view_indep_of_det_ne_zero` / `ViewModel`'s hiding result, but
with the mask matrix `M = D · circleTMatrix(sched)` for a nonzero diagonal `D`. A view's
mask map `mulVecLin (D · circleTMatrix(sched))` is witness-independent given
`det (circleTMatrix(sched)) ≠ 0` and `∏ d_i ≠ 0`.  This replaces the `circleMatrixGen`
routing. -/

section Hiding

variable {K : Type*} [Field K]

/-- **General nonzero-diagonal-rescale hiding.**  For any `K`-matrix `A` with `det A ≠ 0` and
any nonzero-product diagonal `d`, the released view through `mulVecLin (diagonal d · A)` has
witness-independent mask-fibre cardinalities.  `view_indep_of_det_ne_zero` at the rescaled
matrix, whose determinant is nonzero by `det_diagonal_mul_ne_zero`. -/
theorem diag_rescale_view_indep {n : ℕ} {d : Fin n → K} (hd : (∏ i, d i) ≠ 0)
    {A : Matrix (Fin n) (Fin n) K} (hA : A.det ≠ 0)
    (w₁ w₂ y : Fin n → K) :
    Nat.card {R : Fin n → K // w₁ + Matrix.mulVecLin (Matrix.diagonal d * A) R = y}
      = Nat.card {R : Fin n → K // w₂ + Matrix.mulVecLin (Matrix.diagonal d * A) R = y} :=
  view_indep_of_det_ne_zero (Matrix.diagonal d * A)
    (det_diagonal_mul_ne_zero hd hA) w₁ w₂ y

/-- **Row-rescaled circle-mask hiding.** The leakage matrix
`D · circleTMatrix(sched)` — a nonzero-diagonal rescale of the circle-**honest**
matrix — hides the witness whenever `circleTMatrix` at the schedule is nonsingular and the
per-row factors have nonzero product. A concrete use still has to prove the
entrywise map identity and every factor's non-vanishing. -/
theorem circleTMask_hides_witness {m : ℕ} (sched : Fin (2 * m) → K)
    (hsched : ((circleTMatrix K m).map (eval sched)).det ≠ 0)
    {d : Fin (2 * m) → K} (hd : (∏ i, d i) ≠ 0)
    (w₁ w₂ y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K //
        w₁ + Matrix.mulVecLin
          (Matrix.diagonal d * (circleTMatrix K m).map (eval sched)) R = y}
      = Nat.card {R : Fin (2 * m) → K //
        w₂ + Matrix.mulVecLin
          (Matrix.diagonal d * (circleTMatrix K m).map (eval sched)) R = y} :=
  diag_rescale_view_indep hd hsched w₁ w₂ y

end Hiding

/-! ## Part 4 — a generic symbolic rescale binding

`ClosesObligationA_T` is a generic specification for a symbolic map already
known to have the form `D · circleTMatrix`. Its bridge theorems show that this
identity and `∏ d_i ≠ 0` supply the hiding hypothesis. It is not the concrete
v5 binding: the latter is field-valued after rational parametrisation and is
handled in `CircleTensorBinding.lean`. -/

section ObligationA

variable {K : Type*} [Field K]

/-- **Generic symbolic rescale binding.** Entrywise equality of a symbolic map
to the nonzero-diagonal rescale `D · circleTMatrix` of the circle-**honest** matrix.
`D` carries the per-row rescale. This specification does not assert
that the actual v5 leakage map is polynomial in the rational parameters. The
field-valued identity for that map instead uses
`B_896(p_i) / (1 + t_i²)^m` and is proved in `CircleTensorBinding.lean`. -/
def ClosesObligationA_T {m : ℕ}
    (deployedMap : Matrix (Fin (2 * m)) (Fin (2 * m)) (MvPolynomial (Fin (2 * m)) K))
    (D : Fin (2 * m) → MvPolynomial (Fin (2 * m)) K) : Prop :=
  ∀ i j, deployedMap i j = (Matrix.diagonal D * circleTMatrix K m) i j

/-- **Bridge, step 1: the symbolic identity survives evaluation at the schedule.**  If the
deployed map is `D · circleTMatrix` symbolically, then evaluated at any schedule it is the
`K`-matrix `diagonal (eval sched ∘ D) · (circleTMatrix at sched)`.  This is the
`circleTMatrix` analogue of `ViewModel.ClosesObligationA.deployed_map_eq`, carrying the
diagonal factor through. -/
theorem ClosesObligationA_T.deployed_map_eq {m : ℕ}
    {deployedMap : Matrix (Fin (2 * m)) (Fin (2 * m)) (MvPolynomial (Fin (2 * m)) K)}
    {D : Fin (2 * m) → MvPolynomial (Fin (2 * m)) K}
    (h : ClosesObligationA_T deployedMap D) (sched : Fin (2 * m) → K) :
    deployedMap.map (eval sched)
      = Matrix.diagonal (fun i => eval sched (D i)) * (circleTMatrix K m).map (eval sched) := by
  have hEq : deployedMap = Matrix.diagonal D * circleTMatrix K m := Matrix.ext h
  have hmul : (Matrix.diagonal D * circleTMatrix K m).map (eval sched)
      = (Matrix.diagonal D).map (eval sched) * (circleTMatrix K m).map (eval sched) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.mapMatrix_apply, map_mul]
  rw [hEq, hmul, Matrix.diagonal_map (map_zero (eval sched))]

/-- **Bridge, step 2: the restated obligation (a) supplies the hiding hypothesis.**  Given the
entrywise identity `deployedMap = D · circleTMatrix`, a schedule at which `circleTMatrix` is
nonsingular, and per-row factors whose evaluated product is nonzero, the deployed released
view (through `mulVecLin (deployedMap at sched)`) hides the witness.  This is the corrected
replacement for the `circleMatrixGen`-routed hiding: no `= circleMatrixGen` binding is used. -/
theorem ClosesObligationA_T.hides_witness {m : ℕ}
    {deployedMap : Matrix (Fin (2 * m)) (Fin (2 * m)) (MvPolynomial (Fin (2 * m)) K)}
    {D : Fin (2 * m) → MvPolynomial (Fin (2 * m)) K}
    (h : ClosesObligationA_T deployedMap D) (sched : Fin (2 * m) → K)
    (hD : (∏ i, eval sched (D i)) ≠ 0)
    (hsched : ((circleTMatrix K m).map (eval sched)).det ≠ 0)
    (w₁ w₂ y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K //
        w₁ + Matrix.mulVecLin (deployedMap.map (eval sched)) R = y}
      = Nat.card {R : Fin (2 * m) → K //
        w₂ + Matrix.mulVecLin (deployedMap.map (eval sched)) R = y} := by
  rw [h.deployed_map_eq sched]
  exact circleTMask_hides_witness sched hsched hD w₁ w₂ y

end ObligationA

/-! ## Summary — what this file establishes over `ViewModel`

**The seam correction.** Hiding can be routed through `circleTMatrix` (the
circle-**honest** matrix with a `det ≠ 0` / liveness proof) after an explicitly
nonzero row rescale. `CircleTensorBinding.lean` proves the exact field-valued
rescale direction for the aligned candidate map.

**`det ≠ 0` (hence hiding) is preserved under the rescale.**  `det (diagonal d · A) =
(∏ d_i) · det A` (`det_diagonal_mul`), so `det ≠ 0 ↔ det A ≠ 0` when the
diagonal is nonzero
(`det_diagonal_mul_ne_zero_iff`). Lifting `circleTMatrix_det_ne_zero` gives the
generic symbolic non-vacuity `rescaledTMatrix_det_ne_zero`.

**Proved in-kernel (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`):**

* `det_diagonal_mul`, `det_diagonal_mul_ne_zero`, `det_diagonal_mul_ne_zero_iff` — the
  diagonal-rescale determinant lemma;
* `rescaledTMatrix_det_ne_zero` — a polynomial rescale of `circleTMatrix` is nonsingular;
* `diag_rescale_view_indep`, `circleTMask_hides_witness` — hiding through `D · circleTMatrix`;
* `ClosesObligationA_T` and its bridges `deployed_map_eq`, `hides_witness` — a
  generic symbolic identity supplies the corresponding hiding hypothesis.
-/

end AspisCircleTMatrixHiding

#print axioms AspisCircleTMatrixHiding.det_diagonal_mul
#print axioms AspisCircleTMatrixHiding.det_diagonal_mul_ne_zero
#print axioms AspisCircleTMatrixHiding.det_diagonal_mul_ne_zero_iff
#print axioms AspisCircleTMatrixHiding.rescaledTMatrix_det_ne_zero
#print axioms AspisCircleTMatrixHiding.diag_rescale_view_indep
#print axioms AspisCircleTMatrixHiding.circleTMask_hides_witness
#print axioms AspisCircleTMatrixHiding.ClosesObligationA_T.deployed_map_eq
#print axioms AspisCircleTMatrixHiding.ClosesObligationA_T.hides_witness
