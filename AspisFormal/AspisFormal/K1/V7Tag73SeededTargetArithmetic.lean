import AspisFormal.K1.V7Tag73AtomicForkUniformScheduler

/-!
# Exact arithmetic for the dummy-seeded Tag-73 causal tree

The deployed verifier has one public, non-oracle initial digest: the all-zero
dummy state.  Seeding that digest makes the first causal exposure start at
step one.  Hence the exact per-exposure cap list is

`[1 + G, 2 + G, ..., F + G]`,

which is the existing global forward-reference list with constant `G + 1`.
Its exact sum is `F + choose(F,2) + F*G`.

This leaf is arithmetic only.  It does not assert failure-event inclusion or
a compiler theorem.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SeededTargetArithmetic

open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73GlobalForwardReferenceBound

/-! ## Shifting the initial seen-cardinality step -/

theorem operational_caps_from_step_succ
    (step remaining G : Nat) :
    operationalCapsFrom (step + 1) remaining G =
      operationalCapsFrom step remaining (G + 1) := by
  induction remaining generalizing step with
  | zero => rfl
  | succ remaining ih =>
      rw [operational_caps_from_succ, operational_caps_from_succ]
      congr 1
      · omega
      · exact ih (step + 1)

/-- Starting with the singleton dummy digest is exactly the old cap family
with one extra target at every exposure. -/
theorem operational_caps_from_one_eq_seeded_global_caps (F G : Nat) :
    operationalCapsFrom 1 F G =
      tag73GlobalForwardReferenceCaps F (G + 1) := by
  calc
    operationalCapsFrom 1 F G =
        operationalCapsFrom 0 F (G + 1) := by
      simpa using operational_caps_from_step_succ 0 F G
    _ = tag73GlobalForwardReferenceCaps F (G + 1) := by
      rw [operational_caps_from_eq_range_map]
      rfl

theorem operational_caps_from_one_length (F G : Nat) :
    (operationalCapsFrom 1 F G).length = F := by
  rw [operational_caps_from_one_eq_seeded_global_caps]
  exact tag73_global_forward_reference_caps_length F (G + 1)

def seededTargetCoefficient (F G : Nat) : Nat :=
  F + F.choose 2 + F * G

theorem seeded_global_coefficient_equivalence (F G : Nat) :
    tag73GlobalForwardReferenceCoefficient F (G + 1) =
      seededTargetCoefficient F G := by
  unfold tag73GlobalForwardReferenceCoefficient seededTargetCoefficient
  simp only [Nat.mul_add, Nat.mul_one]
  ac_rfl

theorem operational_caps_from_one_sum_exact (F G : Nat) :
    (operationalCapsFrom 1 F G).sum = seededTargetCoefficient F G := by
  rw [operational_caps_from_one_eq_seeded_global_caps,
    tag73_global_forward_reference_caps_sum_exact,
    seeded_global_coefficient_equivalence]

theorem seeded_target_coefficient_expansion (F G : Nat) :
    seededTargetCoefficient F G = F + F.choose 2 + F * G := by
  rfl

#print axioms operational_caps_from_step_succ
#print axioms operational_caps_from_one_eq_seeded_global_caps
#print axioms operational_caps_from_one_length
#print axioms seeded_global_coefficient_equivalence
#print axioms operational_caps_from_one_sum_exact
#print axioms seeded_target_coefficient_expansion

end AspisK1.V7Tag73SeededTargetArithmetic
