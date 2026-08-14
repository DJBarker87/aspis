import AspisFormal.CircleNaturalBasisEval

/-!
# Radix-four decomposition of the natural line basis

The recursive V5 line encoders split coefficient indices into four adjacent
lanes.  This file proves that this is exactly the corresponding split of the
natural Chebyshev-product basis.  It is a polynomial identity; it contains no
coding-theory or distance premise.
-/

namespace AspisV5FriNaturalBasisRadix4

open AspisCircleTensorBinding

variable {K : Type*} [CommRing K]

/-- Repeated doubling factors compose by addition of their indices. -/
theorem doubledFactor_add (x : K) (a b : Nat) :
    doubledFactor x (a + b) = doubledFactor (doubledFactor x a) b := by
  induction b with
  | zero => simp [doubledFactor]
  | succ b ih =>
      rw [Nat.add_succ, doubledFactor, ih, doubledFactor]

theorem doubledFactor_add_two (x : K) (bit : Nat) :
    doubledFactor x (bit + 2) =
      doubledFactor (doubledFactor x 2) bit := by
  rw [Nat.add_comm bit 2, doubledFactor_add]

private theorem list_toFinset_map_add (values : List Nat) (shift : Nat) :
    (values.map fun value => value + shift).toFinset =
      values.toFinset.image fun value => value + shift := by
  ext value
  simp

/-- Splitting off one zero low bit changes the evaluation point from `x` to
`T₂(x)`. -/
theorem naturalLineValue_two_mul (x : K) (q : Nat) :
    naturalLineValue x (2 * q) =
      naturalLineValue (doubledFactor x 1) q := by
  unfold naturalLineValue
  rw [Nat.bitIndices_two_mul, list_toFinset_map_add]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro bit _hbit
    rw [show bit + 1 = 1 + bit by omega, doubledFactor_add]
  · intro left _hleft right _hright heq
    exact Nat.add_right_cancel heq

/-- Splitting off one set low bit contributes the factor `x`. -/
theorem naturalLineValue_two_mul_add_one (x : K) (q : Nat) :
    naturalLineValue x (2 * q + 1) =
      x * naturalLineValue (doubledFactor x 1) q := by
  unfold naturalLineValue
  rw [Nat.bitIndices_two_mul_add_one, List.toFinset_cons,
    list_toFinset_map_add]
  have hzero : 0 ∉ q.bitIndices.toFinset.image (fun value => value + 1) := by
    simp
  rw [Finset.prod_insert hzero, Finset.prod_image]
  · change x *
      (∏ bit ∈ q.bitIndices.toFinset,
        doubledFactor x (bit + 1)) =
        x * (∏ bit ∈ q.bitIndices.toFinset,
          doubledFactor (doubledFactor x 1) bit)
    congr 1
    apply Finset.prod_congr rfl
    intro bit _hbit
    rw [show bit + 1 = 1 + bit by omega, doubledFactor_add]
  · intro left _hleft right _hright heq
    exact Nat.add_right_cancel heq

/-- The high binary digits of a natural-basis index are evaluated at the
twice-doubled point. -/
theorem naturalLineValue_four_mul (x : K) (q : Nat) :
    naturalLineValue x (4 * q) =
      naturalLineValue (doubledFactor x 2) q := by
  rw [show 4 * q = 2 * (2 * q) by omega,
    naturalLineValue_two_mul, naturalLineValue_two_mul]
  congr 1

/-- Full four-lane decomposition.  The low two bits select
`[1, x, T₂(x), x*T₂(x)]`; all higher bits are evaluated at `T₄(x)`. -/
theorem naturalLineValue_four_mul_add (x : K) (q : Nat) (slot : Fin 4) :
    naturalLineValue x (4 * q + slot) =
      naturalLineValue (doubledFactor x 2) q *
        ![1, x, doubledFactor x 1, x * doubledFactor x 1] slot := by
  fin_cases slot
  · simpa using naturalLineValue_four_mul x q
  · rw [show 4 * q + 1 = 2 * (2 * q) + 1 by omega,
      naturalLineValue_two_mul_add_one, naturalLineValue_two_mul]
    rw [show doubledFactor (doubledFactor x 1) 1 = doubledFactor x 2 by
      rw [← doubledFactor_add]]
    simp
    ring
  · rw [show 4 * q + 2 = 2 * (2 * q + 1) by omega,
      naturalLineValue_two_mul, naturalLineValue_two_mul_add_one]
    rw [show doubledFactor (doubledFactor x 1) 1 = doubledFactor x 2 by
      rw [← doubledFactor_add]]
    simp
    ring
  · rw [show 4 * q + 3 = 2 * (2 * q + 1) + 1 by omega,
      naturalLineValue_two_mul_add_one,
      naturalLineValue_two_mul_add_one]
    rw [show doubledFactor (doubledFactor x 1) 1 = doubledFactor x 2 by
      rw [← doubledFactor_add]]
    simp
    ring

/-! ## Audit -/

#print axioms naturalLineValue_four_mul_add

end AspisV5FriNaturalBasisRadix4
