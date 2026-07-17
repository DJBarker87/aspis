import Mathlib

/-!
# Bounded-independence hiding: the kernel-checked core

The masking argument's heart is this: if the linear mask map `A` (mask
coefficients → the field coordinates the verifier sees) is **surjective** onto
the view space, then the released view is uniform and carries **no** information
about the witness.  We state the witness-independence as a counting identity:
for any fixed released view `y`, the number of masks producing it is the *same*
whether the witness shift is `w₁` or `w₂`.  A perfect (honest-verifier)
simulator that samples the view uniformly is therefore witness-free.

Nothing here is trusted because "an AI derived it": the Lean kernel checks the
proof term.  Surjectivity of the specific circle mask map is the separate
instantiation lemma (Layer 2); this file is the field-agnostic core (Layer 1).
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
