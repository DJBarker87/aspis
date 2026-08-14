import Mathlib

/-!
# Fixed-width bit reversal used by the V5 circle and line domains

The Rust domains are stored in bit-reversed order.  This file gives the small
arithmetic fact needed by the radix-four encoder proof: after appending a
two-bit fibre slot, reversal moves that slot to the high end and leaves the
parent reversal at the low end.
-/

namespace AspisV5FriBitReverse

/-- Reverse the low `width` bits of `value`.  Bits above `width` are ignored. -/
def reverseBits : Nat -> Nat -> Nat
  | 0, _ => 0
  | width + 1, value =>
      (value % 2) * 2 ^ width + reverseBits width (value / 2)

theorem reverseBits_lt_two_pow (width value : Nat) :
    reverseBits width value < 2 ^ width := by
  induction width generalizing value with
  | zero => simp [reverseBits]
  | succ width ih =>
      rw [reverseBits, pow_succ]
      have hmod : value % 2 < 2 := Nat.mod_lt _ (by decide)
      have htail := ih (value / 2)
      interval_cases h : value % 2
      · simp only [h, zero_mul, zero_add]
        omega
      · simp only [h, one_mul]
        omega

/-- Fixed-width reversal is injective on values that fit in the width. -/
theorem reverseBits_injective_on_width (width : Nat) :
    Set.InjOn (reverseBits width) (Set.Iio (2 ^ width)) := by
  induction width with
  | zero =>
      intro left hleft right hright _heq
      simp only [Set.mem_Iio] at hleft hright
      omega
  | succ width ih =>
      intro left hleft right hright heq
      simp only [Set.mem_Iio] at hleft hright
      rw [reverseBits, reverseBits] at heq
      have hleftTail := reverseBits_lt_two_pow width (left / 2)
      have hrightTail := reverseBits_lt_two_pow width (right / 2)
      have htail : reverseBits width (left / 2) =
          reverseBits width (right / 2) := by
        calc
          reverseBits width (left / 2) =
              ((left % 2) * 2 ^ width +
                reverseBits width (left / 2)) % 2 ^ width := by
                rw [Nat.add_comm, Nat.mul_comm,
                  Nat.add_mul_mod_self_left,
                  Nat.mod_eq_of_lt hleftTail]
          _ = ((right % 2) * 2 ^ width +
                reverseBits width (right / 2)) % 2 ^ width :=
              congrArg (fun value => value % (2 ^ width)) heq
          _ = reverseBits width (right / 2) := by
                rw [Nat.add_comm, Nat.mul_comm,
                  Nat.add_mul_mod_self_left,
                  Nat.mod_eq_of_lt hrightTail]
      have hlow : left % 2 = right % 2 := by
        rw [htail] at heq
        exact Nat.mul_right_cancel (pow_pos (by decide) _)
          (Nat.add_right_cancel heq)
      have hleftDiv : left / 2 < 2 ^ width := by
        rw [pow_succ] at hleft
        omega
      have hrightDiv : right / 2 < 2 ^ width := by
        rw [pow_succ] at hright
        omega
      have hdiv : left / 2 = right / 2 :=
        ih hleftDiv hrightDiv htail
      omega

/-- Bit reversal as an injective map on the exact finite domain. -/
def reverseFin (width : Nat) : Fin (2 ^ width) -> Fin (2 ^ width) :=
  fun value => ⟨reverseBits width value,
    reverseBits_lt_two_pow width value⟩

theorem reverseFin_injective (width : Nat) :
    Function.Injective (reverseFin width) := by
  intro left right heq
  apply Fin.ext
  apply reverseBits_injective_on_width width left.isLt right.isLt
  exact congrArg Fin.val heq

/-- Reversing `4 * parent + slot` moves the reversed two-bit slot to the high
end and preserves the reversed parent below it. -/
theorem reverseBits_radix4_fibre
    (width parent slot : Nat) (hslot : slot < 4) :
    reverseBits (width + 2) (4 * parent + slot) =
      reverseBits width parent + 2 ^ width * reverseBits 2 slot := by
  simp only [reverseBits]
  have hpow : 2 ^ (width + 1) = 2 * 2 ^ width := by
    rw [pow_succ]
    omega
  rw [hpow]
  have hslotDiv : slot / 2 < 2 := by omega
  have hdiv : (4 * parent + slot) / 2 / 2 = parent := by omega
  have hmod : (4 * parent + slot) % 2 = slot % 2 := by omega
  have hdivmod : ((4 * parent + slot) / 2) % 2 = (slot / 2) % 2 := by
    omega
  rw [hdiv, hmod, hdivmod]
  ring

/-- Finite-index spelling used by `childIndex`. -/
theorem reverseBits_childIndex
    (width : Nat) (parent : Nat) (slot : Fin 4) :
    reverseBits (width + 2) (4 * parent + slot) =
      reverseBits width parent + 2 ^ width * reverseBits 2 slot :=
  reverseBits_radix4_fibre width parent slot slot.isLt

/-- Appending one zero bit before reversal leaves the reversed parent value
unchanged.  This is the index relation for the intermediate domain used by
the two binary folds inside one radix-four fold. -/
theorem reverseBits_two_mul (width value : Nat) :
    reverseBits (width + 1) (2 * value) = reverseBits width value := by
  simp [reverseBits]

/-! ## Audit -/

#print axioms reverseBits_injective_on_width
#print axioms reverseFin_injective
#print axioms reverseBits_radix4_fibre
#print axioms reverseBits_two_mul

end AspisV5FriBitReverse
