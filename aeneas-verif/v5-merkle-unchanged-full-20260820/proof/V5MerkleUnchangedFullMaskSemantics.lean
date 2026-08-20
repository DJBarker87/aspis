import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullGroupTraceLists
import V5MerkleUnchangedFullConstructorSemantics

/-! Exact interpretation of each generated radix mask bit. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace AspisV5MerkleUnchangedFullMaskSemantics

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullOrderedChildPositions

private def slotScalar (slot : Nat) (slotBound : slot < 4) : Std.Usize :=
  Std.Usize.ofNatCore slot (by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with bits | bits <;>
      rw [bits] <;> norm_num at slotBound ⊢ <;> omega)

@[simp] private theorem slotScalar_val (slot : Nat) (slotBound : slot < 4) :
    (slotScalar slot slotBound).val = slot := by
  exact Std.Usize.ofNatCore_val_eq _

private theorem one_shift_u32_val (value : Std.U32) (bound : value.val < 4) :
    (Std.U8.wrapping_shl 1#u8 value).val = 2 ^ value.val := by
  unfold Std.U8.wrapping_shl UScalar.wrapping_shl
  norm_num
  unfold UScalar.val
  simp [Nat.shiftLeft_eq]
  change value.bv.toNat < 4 at bound
  change 2 ^ (value.bv.toNat % 8) % 256 = 2 ^ value.bv.toNat
  interval_cases current : value.bv.toNat <;> norm_num [current] at *

@[simp] private theorem one_shift_slotScalar_val
    (slot : Nat) (slotBound : slot < 4) :
    (Std.U8.wrapping_shl 1#u8
      (UScalar.cast .U32 (slotScalar slot slotBound))).val = 2 ^ slot := by
  have castValue :
      (UScalar.cast .U32 (slotScalar slot slotBound)).val = slot := by
    simp [UScalar.cast_val_eq, slotScalar_val]
    omega
  have castBound :
      (UScalar.cast .U32 (slotScalar slot slotBound)).val < 4 := by
    rw [castValue]
    exact slotBound
  rw [one_shift_u32_val _ castBound, castValue]

private theorem childPresent_iff_canonical_bit
    (present : Std.U8) (slot : Nat) (slotBound : slot < 4) :
    ChildPresent present slot ↔
      present &&& Std.U8.wrapping_shl 1#u8
        (UScalar.cast .U32 (slotScalar slot slotBound)) != 0#u8 := by
  constructor
  · rintro ⟨scalar, scalarValue, bit⟩
    have scalarEq : scalar = slotScalar slot slotBound :=
      UScalar.eq_of_val_eq (scalarValue.trans (slotScalar_val slot slotBound).symm)
    simpa only [scalarEq] using bit
  · intro bit
    exact ⟨slotScalar slot slotBound, slotScalar_val slot slotBound, bit⟩

/-- For a released four-child group mask, the generated Rust bit test is
true exactly for the slots held in the maintained active-child set. -/
theorem childPresent_iff_mem_slots
    (present : Std.U8) (slots : Finset (Fin 4))
    (presentValue : present.val = slotMask slots)
    (slot : Fin 4) :
    ChildPresent present slot.val ↔ slot ∈ slots := by
  rw [childPresent_iff_canonical_bit present slot.val slot.isLt]
  by_cases member : slot ∈ slots
  · simp only [member, iff_true, bne_iff_ne]
    apply UScalar.ne_of_val_ne
    simp only [UScalar.val_and]
    fin_cases slot <;>
      by_cases h0 : (0 : Fin 4) ∈ slots <;>
      by_cases h1 : (1 : Fin 4) ∈ slots <;>
      by_cases h2 : (2 : Fin 4) ∈ slots <;>
      by_cases h3 : (3 : Fin 4) ∈ slots <;>
      simp [h0, h1, h2, h3] at member <;>
      rw [presentValue, slotMask_four] <;>
      simp [h0, h1, h2, h3, one_shift_slotScalar_val] <;>
      norm_num
  · simp only [member, iff_false, bne_iff_ne, not_not]
    apply UScalar.eq_of_val_eq
    simp only [UScalar.val_and]
    fin_cases slot <;>
      by_cases h0 : (0 : Fin 4) ∈ slots <;>
      by_cases h1 : (1 : Fin 4) ∈ slots <;>
      by_cases h2 : (2 : Fin 4) ∈ slots <;>
      by_cases h3 : (3 : Fin 4) ∈ slots <;>
      simp [h0, h1, h2, h3] at member <;>
      rw [presentValue, slotMask_four] <;>
      simp [h0, h1, h2, h3, one_shift_slotScalar_val] <;>
      norm_num

#print axioms childPresent_iff_mem_slots

end AspisV5MerkleUnchangedFullMaskSemantics
