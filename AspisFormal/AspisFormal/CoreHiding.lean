import Mathlib

/-!
# Bounded-independence hiding: the kernel-checked core

The masking argument's core building block: if the linear mask map `A` (mask
coefficients → the field coordinates the verifier sees) is **surjective** onto
the view space, then for any fixed released view `y`, the number of masks
producing it is the *same* whether the witness shift is `w₁` or `w₂`.

**Exactly what is and isn't proved.**  This is an equality of fibre
*cardinalities* (`Nat.card`), field-agnostic (`[Field K]` only).  Over a finite
field, equal fibre counts give equal uniform-sampling probabilities and hence a
witness-free view distribution — but that finite-field / `PMF`-level statement
is NOT formalized here (no `[Fintype K]`, no `PMF`, no simulator is constructed).
And `A` is an *arbitrary* linear map: this file says nothing about whether `A`
is Aspis's actual circle mask, nor whether the view coordinates are the complete
released view.  Those are the load-bearing obligations, handled (or flagged as
open) elsewhere.

What this file does buy: the kernel — not an AI — checks that surjectivity
implies witness-independent fibre counts.  Surjectivity of the specific circle
mask map is the separate instantiation (Layer 2).
-/

variable {K : Type*} [Field K] {m b : ℕ}

/-- **Core hiding lemma (Layer 1).**
If the mask map `A : Kᵐ → Kᵇ` is surjective, the count of masks `R` that yield a
fixed view `y = wᵢ + A R` does not depend on the witness shift `wᵢ`.  Hence the
view distribution is independent of the witness. -/
theorem view_card_indep_of_witness
    (A : (Fin m → K) →ₗ[K] (Fin b → K)) (hA : Function.Surjective A)
    (w₁ w₂ y : Fin b → K) :
    Nat.card {R : Fin m → K // w₁ + A R = y}
      = Nat.card {R : Fin m → K // w₂ + A R = y} := by
  obtain ⟨R₀, hR₀⟩ := hA (w₁ - w₂)          -- A R₀ = w₁ - w₂, by surjectivity
  apply Nat.card_congr
  exact {
    toFun := fun R => ⟨R.1 + R₀, by
      have h := R.2; rw [map_add, hR₀]; linear_combination h⟩
    invFun := fun R => ⟨R.1 - R₀, by
      have h := R.2; rw [map_sub, hR₀]; linear_combination h⟩
    left_inv := fun R => by apply Subtype.ext; simp
    right_inv := fun R => by apply Subtype.ext; simp }

/-- **Perfect hiding at the view (corollary).**
Two distinct witnesses induce identically-distributed views: for every view `y`
the fibre cardinalities agree.  This is exactly the statement a perfect-ZK
simulator needs — the released field view can be sampled without the witness. -/
theorem view_distribution_witness_free
    (A : (Fin m → K) →ₗ[K] (Fin b → K)) (hA : Function.Surjective A)
    (w₁ w₂ : Fin b → K) :
    (fun y => Nat.card {R : Fin m → K // w₁ + A R = y})
      = (fun y => Nat.card {R : Fin m → K // w₂ + A R = y}) := by
  funext y
  exact view_card_indep_of_witness A hA w₁ w₂ y

#print axioms view_card_indep_of_witness
