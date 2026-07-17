import Mathlib
import AspisFormal.CoreHiding

/-!
# Bounded-independence hiding: the finite-field *distribution* statement

`CoreHiding.lean` proves, for an arbitrary `[Field K]`, that the number of masks
`R` producing a fixed view `y = wᵢ + A R` is the *same* for any two witness
shifts `w₁`, `w₂` (an equality of fibre *cardinalities*, `Nat.card`).

A reviewer rightly points out that a counting fact is not yet a probability
statement.  This file closes that gap.  Adding `[Fintype K] [DecidableEq K]`
(so the mask space `Fin m → K` is a finite probability space) we upgrade the
cardinality equality to a genuine **distribution equality**: the pushforward of
the *uniform* distribution on the mask space under `R ↦ w + A R` is literally the
same `PMF` for every witness shift `w`.  This is the "the released view
distribution is independent of the witness" statement in its honest form — an
equality of `PMF`s, obtained by `PMF.ext` from the CoreHiding fibre count.

The core input is `view_card_indep_of_witness` from `CoreHiding.lean`; nothing
about the argument is re-proved, only lifted from counting to measure.
-/

open scoped ENNReal

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m b : ℕ}

/-- The mask space `Fin m → K` is nonempty (it contains `0`), so the uniform
distribution `PMF.uniformOfFintype` on it is defined. -/
instance : Nonempty (Fin m → K) := ⟨0⟩

/-- **The mass the pushed-forward uniform distribution assigns to a view `y`.**
Sampling a mask `R` uniformly and releasing `w + A R`, the probability of seeing
`y` is `(#{R : w + A R = y}) / |Fin m → K|` — exactly the fibre count over the
mask-space size.  This is the bridge from `Nat.card` counting to `PMF` mass. -/
theorem map_uniform_apply
    (A : (Fin m → K) →ₗ[K] (Fin b → K)) (w y : Fin b → K) :
    ((PMF.uniformOfFintype (Fin m → K)).map (fun R => w + A R)) y
      = (Nat.card {R : Fin m → K // w + A R = y} : ℝ≥0∞)
          / (Fintype.card (Fin m → K) : ℝ≥0∞) := by
  classical
  haveI : Fintype ((fun R => w + A R) ⁻¹' ({y} : Set (Fin b → K))) :=
    Fintype.ofFinite _
  have hc : Fintype.card ((fun R => w + A R) ⁻¹' ({y} : Set (Fin b → K)))
      = Nat.card {R : Fin m → K // w + A R = y} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun R => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff])
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_uniformOfFintype_apply, hc]

/-- **Perfect hiding as a distribution equality (finite field).**
For a surjective linear mask map `A`, the pushforward of the *uniform*
distribution on the mask space under `R ↦ w + A R` is the **same `PMF`** for
every witness shift `w`.  Equivalently: an honest party masking with a uniform
`R` produces a released-view distribution that carries no information about the
witness.  This is `view_card_indep_of_witness` lifted from equal fibre counts to
equal probability mass, one point at a time via `PMF.ext`. -/
theorem view_pmf_indep_of_witness
    (A : (Fin m → K) →ₗ[K] (Fin b → K)) (hA : Function.Surjective A)
    (w₁ w₂ : Fin b → K) :
    (PMF.uniformOfFintype (Fin m → K)).map (fun R => w₁ + A R)
      = (PMF.uniformOfFintype (Fin m → K)).map (fun R => w₂ + A R) := by
  apply PMF.ext
  intro y
  rw [map_uniform_apply A w₁ y, map_uniform_apply A w₂ y,
      view_card_indep_of_witness A hA w₁ w₂ y]

omit [DecidableEq K] in
/-- **Pointwise probability form (equivalent restatement).**
Spelled out as an equality of rational probabilities point by point, in case a
reader prefers the ratio form to the `PMF` equality above. -/
theorem view_prob_indep_of_witness
    (A : (Fin m → K) →ₗ[K] (Fin b → K)) (hA : Function.Surjective A)
    (w₁ w₂ : Fin b → K) (y : Fin b → K) :
    (Nat.card {R : Fin m → K // w₁ + A R = y} : ℚ) / (Fintype.card (Fin m → K) : ℚ)
      = (Nat.card {R : Fin m → K // w₂ + A R = y} : ℚ) / (Fintype.card (Fin m → K) : ℚ) := by
  rw [view_card_indep_of_witness A hA w₁ w₂ y]

/-- **The `[Fintype K]` hypothesis is inhabited.**
Specializing the field to `ZMod p` for a prime `p` (a genuine finite field)
gives the distribution-hiding statement for a concrete instance, confirming the
hypotheses of `view_pmf_indep_of_witness` are satisfiable. -/
theorem view_pmf_indep_of_witness_zmod
    (p : ℕ) [Fact p.Prime] {m b : ℕ}
    (A : (Fin m → ZMod p) →ₗ[ZMod p] (Fin b → ZMod p))
    (hA : Function.Surjective A) (w₁ w₂ : Fin b → ZMod p) :
    (PMF.uniformOfFintype (Fin m → ZMod p)).map (fun R => w₁ + A R)
      = (PMF.uniformOfFintype (Fin m → ZMod p)).map (fun R => w₂ + A R) :=
  view_pmf_indep_of_witness A hA w₁ w₂

#print axioms view_pmf_indep_of_witness
#print axioms view_pmf_indep_of_witness_zmod
