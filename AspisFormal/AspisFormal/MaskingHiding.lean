import Mathlib
import AspisFormal.CoreHiding

/-!
# Layer 2a: hiding from a per-proof determinant check

Layer 1 (`CoreHiding`) proved: a **surjective** mask map hides the witness.
Here we discharge the surjectivity hypothesis from a concrete, per-proof,
computable condition: the square mask matrix `M` (mask coefficients → the `b`
field coordinates the verifier opens) has **nonzero determinant**.

Consequence: the entire hiding property reduces, *in the kernel*, to
`det M ≠ 0` at the emitted schedule — a `Good_spend`-style check the prover
performs per proof, not a theorem anyone has to trust.  What remains (Layer 2b)
is only that a random schedule satisfies `det M ≠ 0` except with negligible
probability (the circle-Vandermonde Schwartz–Zippel bound).
-/

variable {K : Type*} [Field K] {b : ℕ}

/-- **Layer 2a.** A square mask matrix with nonzero determinant induces a
surjective mask map (`det ≠ 0 → IsUnit → bijective` over a field). -/
theorem mulVecLin_surjective_of_det_ne_zero
    (M : Matrix (Fin b) (Fin b) K) (hM : M.det ≠ 0) :
    Function.Surjective (Matrix.mulVecLin M) := by
  intro y
  refine ⟨M⁻¹.mulVec y, ?_⟩
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu,
      Matrix.one_mulVec]

/-- **Hiding from a per-proof determinant check.**
If the mask matrix at the emitted schedule has nonzero determinant, the released
field view is witness-free: for any two witnesses and any fixed view, the mask
fibre cardinalities agree.  Kernel-checked; the only remaining obligation is the
availability fact that `det M ≠ 0` at a random schedule (Layer 2b). -/
theorem view_indep_of_det_ne_zero
    (M : Matrix (Fin b) (Fin b) K) (hM : M.det ≠ 0)
    (w₁ w₂ y : Fin b → K) :
    Nat.card {R : Fin b → K // w₁ + Matrix.mulVecLin M R = y}
      = Nat.card {R : Fin b → K // w₂ + Matrix.mulVecLin M R = y} :=
  view_card_indep_of_witness (Matrix.mulVecLin M)
    (mulVecLin_surjective_of_det_ne_zero M hM) w₁ w₂ y

#print axioms view_indep_of_det_ne_zero
