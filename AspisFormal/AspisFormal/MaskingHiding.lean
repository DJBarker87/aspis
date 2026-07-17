import Mathlib
import AspisFormal.CoreHiding

/-!
# Layer 2a: hiding from a per-proof determinant check

Layer 1 (`CoreHiding`) proved: a **surjective** mask map gives witness-independent
fibre counts.  Here we discharge the surjectivity hypothesis from a concrete
condition: the square mask matrix `M` has **nonzero determinant**.

**Scope — what this does NOT yet establish.**  `M` here is an *arbitrary*
square matrix; this is a general linear-algebra building block.  It does not
prove that `M` is the matrix Aspis's circle mask actually produces, that it
captures the *complete* released view, that it matches the deployed fold/DEEP
schedule and extension-field coordinates, or that it corresponds to the Rust
implementation.  It also proves equality of fibre *cardinalities*, not equality
of probability distributions (`CoreHiding` uses only `[Field K]`, with no
`Fintype`/`PMF`; over a finite field equal counts give the uniform-distribution
claim, but that upgrade is not yet formalized).  Those obligations — defining
the real released-view type, defining `M` from the real schedule, and proving
`M` models the Rust transcript — are what would make this lemma load-bearing
*for Aspis* rather than merely a correct algebra fact.  They are not done.

Conditional statement, honestly scoped: **given** a finite field and a matrix
`M` that faithfully represents the complete released affine view, `det M ≠ 0`
implies witness-independent fibre counts.  Layer 2b bounds how often a random
schedule fails `det M ≠ 0`.
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
