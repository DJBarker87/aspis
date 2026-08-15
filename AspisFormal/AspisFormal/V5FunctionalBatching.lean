import Mathlib
import AspisFormal.SoundnessLedger

/-!
# Four-functional batching

This file checks the algebra behind batching four already-fixed discrepancies
with the scalar powers `1, κ, κ², κ³`.  A nonzero discrepancy vector defines a
nonzero cubic, so at most three field elements make the batch vanish.

The ordering hypothesis is essential.  `FixedBeforeKappa` states that the
discrepancy vector is determined by the transcript prefix and cannot depend on
the subsequently sampled `κ`.  Without that hypothesis, an adaptive prover can
choose a different polynomial for each challenge and the cubic root bound does
not apply.
-/

namespace AspisV5FunctionalBatching

open Polynomial

variable {K : Type*}

/-- The four scalar-power batch `δ₀ + κ δ₁ + κ² δ₂ + κ³ δ₃`. -/
def batchedDiscrepancy [Semiring K] (δ : Fin 4 → K) (κ : K) : K :=
  δ 0 + δ 1 * κ + δ 2 * κ ^ 2 + δ 3 * κ ^ 3

/-- The cubic whose value at `κ` is the four-functional batch. -/
noncomputable def discrepancyPolynomial [Semiring K] (δ : Fin 4 → K) : K[X] :=
  C (δ 3) * X ^ 3 + C (δ 2) * X ^ 2 + C (δ 1) * X + C (δ 0)

@[simp]
theorem eval_discrepancyPolynomial [Semiring K] (δ : Fin 4 → K) (κ : K) :
    (discrepancyPolynomial δ).eval κ = batchedDiscrepancy δ κ := by
  simp [discrepancyPolynomial, batchedDiscrepancy]
  ac_rfl

@[simp]
theorem coeff_discrepancyPolynomial [Semiring K] (δ : Fin 4 → K) (i : Fin 4) :
    (discrepancyPolynomial δ).coeff i = δ i := by
  fin_cases i <;> simp [discrepancyPolynomial]

/-- A discrepancy vector that is not identically zero gives a nonzero cubic. -/
theorem discrepancyPolynomial_ne_zero [Semiring K] [Nontrivial K]
    (δ : Fin 4 → K) (hδ : δ ≠ 0) : discrepancyPolynomial δ ≠ 0 := by
  intro hp
  apply hδ
  funext i
  have hi := congrArg (fun p : K[X] => p.coeff i) hp
  simpa using hi

/-- The batching polynomial has degree at most three, including degenerate
lower-degree cases. -/
theorem natDegree_discrepancyPolynomial_le [Semiring K] (δ : Fin 4 → K) :
    (discrepancyPolynomial δ).natDegree ≤ 3 := by
  exact Polynomial.natDegree_cubic_le

section Roots

variable [Field K] [Fintype K] [DecidableEq K]

/-- Challenges for which a fixed discrepancy vector collides under batching. -/
def collisionSet (δ : Fin 4 → K) : Finset K :=
  Finset.univ.filter fun κ => batchedDiscrepancy δ κ = 0

/-- A nonzero four-functional discrepancy collides for at most three choices
of the scalar-power batching challenge. -/
theorem collision_card_le_three (δ : Fin 4 → K) (hδ : δ ≠ 0) :
    (collisionSet δ).card ≤ 3 := by
  let p := discrepancyPolynomial δ
  have hp : p ≠ 0 := discrepancyPolynomial_ne_zero δ hδ
  have hsubset : (collisionSet δ).val ⊆ p.roots := by
    intro κ hκ
    have hbatch : batchedDiscrepancy δ κ = 0 := by
      simpa [collisionSet] using hκ
    rw [Polynomial.mem_roots hp]
    simpa [Polynomial.IsRoot, p] using hbatch
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    (natDegree_discrepancyPolynomial_le δ)

/-- The exact rational mass of the collision event under uniform `κ` over
the complete field. -/
def uniformCollisionProbability (δ : Fin 4 → K) : ℚ :=
  (collisionSet δ).card / Fintype.card K

/-- Uniform collision probability is at most `3 / |K|`. -/
theorem uniformCollisionProbability_le (δ : Fin 4 → K) (hδ : δ ≠ 0) :
    uniformCollisionProbability δ ≤ (3 : ℚ) / Fintype.card K := by
  have hcardNat : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard : (0 : ℚ) < Fintype.card K := by exact_mod_cast hcardNat
  rw [uniformCollisionProbability, div_le_div_iff_of_pos_right hcard]
  exact_mod_cast collision_card_le_three δ hδ

/-- Collision challenges after restricting the sampler to nonzero field
elements, as the released V5 transcript does. -/
def nonzeroCollisionSet (δ : Fin 4 → K) : Finset K :=
  (collisionSet δ).erase 0

/-- Exact rational mass under a uniform nonzero batching challenge. -/
def uniformNonzeroCollisionProbability (δ : Fin 4 → K) : ℚ :=
  (nonzeroCollisionSet δ).card /
    ((Fintype.card K - 1 : Nat) : ℚ)

/-- A fixed nonzero discrepancy collides with probability at most
`3 / (|K| - 1)` under the released nonzero sampler. -/
theorem uniformNonzeroCollisionProbability_le
    (δ : Fin 4 → K) (hδ : δ ≠ 0) :
    uniformNonzeroCollisionProbability δ ≤
      (3 : ℚ) / ((Fintype.card K - 1 : Nat) : ℚ) := by
  have hfieldNat : 0 < Fintype.card K - 1 := Nat.sub_pos_iff_lt.mpr
    (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance)
  have hfield : (0 : ℚ) < ((Fintype.card K - 1 : Nat) : ℚ) := by
    exact_mod_cast hfieldNat
  rw [uniformNonzeroCollisionProbability,
    div_le_div_iff_of_pos_right hfield]
  exact_mod_cast (Finset.card_erase_le.trans (collision_card_le_three δ hδ))

/-! ## Transcript-ordering precondition

`δ prefix κ` is written with a `κ` argument solely to model a possibly
adaptive implementation.  `FixedBeforeKappa δ` says that argument is ignored:
once the prefix is fixed, the discrepancy vector is the same for every future
challenge.
-/

/-- The discrepancy vector is fixed by the transcript prefix before `κ` is
sampled. -/
def FixedBeforeKappa {Prefix : Type*} (δ : Prefix → K → Fin 4 → K) : Prop :=
  ∀ transcriptPrefix κ₁ κ₂,
    δ transcriptPrefix κ₁ = δ transcriptPrefix κ₂

/-- Collision set of an implementation that is syntactically allowed to inspect
`κ`; the theorem below reduces it to a single frozen cubic only under
`FixedBeforeKappa`. -/
def adaptiveCollisionSet {Prefix : Type*} (δ : Prefix → K → Fin 4 → K)
    (transcriptPrefix : Prefix) : Finset K :=
  Finset.univ.filter fun κ => batchedDiscrepancy (δ transcriptPrefix κ) κ = 0

theorem adaptiveCollisionSet_eq_collisionSet {Prefix : Type*}
    (δ : Prefix → K → Fin 4 → K) (hfixed : FixedBeforeKappa δ)
    (transcriptPrefix : Prefix) (κ₀ : K) :
    adaptiveCollisionSet δ transcriptPrefix = collisionSet (δ transcriptPrefix κ₀) := by
  ext κ
  simp only [adaptiveCollisionSet, collisionSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [hfixed transcriptPrefix κ κ₀]

/-- The root bound for the transcript-shaped statement.  Both the fixed-before-
`κ` hypothesis and nonzeroness of the frozen vector are explicit. -/
theorem adaptive_collision_card_le_three {Prefix : Type*}
    (δ : Prefix → K → Fin 4 → K) (hfixed : FixedBeforeKappa δ)
    (transcriptPrefix : Prefix) (κ₀ : K) (hδ : δ transcriptPrefix κ₀ ≠ 0) :
    (adaptiveCollisionSet δ transcriptPrefix).card ≤ 3 := by
  rw [adaptiveCollisionSet_eq_collisionSet δ hfixed transcriptPrefix κ₀]
  exact collision_card_le_three (δ transcriptPrefix κ₀) hδ

end Roots

/-! ## Concrete QM31 ledger arithmetic -/

/-- For the deployed QM31 cardinality `(2³¹ - 1)⁴` and its nonzero
sampler, the cubic collision term is at most `2⁻¹²²`. -/
theorem qm31_four_functional_collision :
    (3 : ℝ) / (AspisSoundnessLedger.FIELD - 1) ≤ 1 / 2 ^ 122 := by
  unfold AspisSoundnessLedger.FIELD
  norm_num

#print axioms discrepancyPolynomial_ne_zero
#print axioms collision_card_le_three
#print axioms uniformCollisionProbability_le
#print axioms uniformNonzeroCollisionProbability_le
#print axioms adaptive_collision_card_le_three
#print axioms qm31_four_functional_collision

end AspisV5FunctionalBatching
