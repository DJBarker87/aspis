import AspisCoreFieldSub
import Mathlib.Data.ZMod.Basic

/-!
# Extracted Rust M31 subtraction correspondence

This proof applies directly to the Aeneas definition extracted from the
production `aspis-core/src/field.rs` implementation. Canonical inputs make all
three generated `u32` wrapping operations ordinary natural arithmetic.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasM31Sub

open aspis_core

abbrev m31Modulus : Nat := 2147483647
abbrev u32Cardinality : Nat := 2 ^ 32
def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus
abbrev M31Exact := ZMod m31Modulus

def rawM31Sub (x y : Nat) : Nat :=
  if y ≤ x then x - y else x + m31Modulus - y

@[simp] theorem extracted_P_val : field.P.val = m31Modulus := by
  unfold field.P
  rfl

theorem u32_size_eq : UScalar.size .U32 = u32Cardinality := by
  rw [UScalar.size_def, UScalarTy.U32_numBits_eq]

theorem extracted_m31_sub_eq_conditional (a b : field.M31) :
    field.M31.sub a b =
      let sum := Std.U32.wrapping_add a field.P
      let shifted := Std.U32.wrapping_sub sum b
      if m31Modulus ≤ shifted.val then
        ok (Std.U32.wrapping_sub shifted field.P)
      else ok shifted := by
  simp [field.M31.sub, Std.lift]

theorem add_P_lt_u32
    (a : field.M31) (ha : CanonicalRawM31 a.val) :
    a.val + m31Modulus < u32Cardinality := by
  unfold CanonicalRawM31 at ha
  norm_num [m31Modulus, u32Cardinality] at ha ⊢
  omega

theorem wrapping_add_P_val
    (a : field.M31) (ha : CanonicalRawM31 a.val) :
    (Std.U32.wrapping_add a field.P).val = a.val + m31Modulus := by
  rw [Std.U32.wrapping_add_val_eq, u32_size_eq, extracted_P_val,
    Nat.mod_eq_of_lt (add_P_lt_u32 a ha)]

theorem shifted_sub_val
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    (Std.U32.wrapping_sub (Std.U32.wrapping_add a field.P) b).val =
      a.val + m31Modulus - b.val := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq,
    wrapping_add_P_val a ha]
  have hb_le : b.val ≤ a.val + m31Modulus := by
    unfold CanonicalRawM31 at hb
    omega
  have hdiff : a.val + m31Modulus - b.val < u32Cardinality := by
    have := add_P_lt_u32 a ha
    omega
  have hrewrite :
      a.val + m31Modulus + (u32Cardinality - b.val) =
        (a.val + m31Modulus - b.val) + u32Cardinality := by
    have hb_u32 : b.val ≤ u32Cardinality := by
      unfold CanonicalRawM31 at hb
      norm_num [m31Modulus, u32Cardinality] at hb ⊢
      omega
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hdiff]

theorem shifted_high_iff
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    m31Modulus ≤
        (Std.U32.wrapping_sub (Std.U32.wrapping_add a field.P) b).val ↔
      b.val ≤ a.val := by
  rw [shifted_sub_val a b ha hb]
  unfold CanonicalRawM31 at hb
  omega

theorem high_sub_P_val
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val)
    (hhigh : b.val ≤ a.val) :
    (Std.U32.wrapping_sub
        (Std.U32.wrapping_sub (Std.U32.wrapping_add a field.P) b)
        field.P).val = a.val - b.val := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, extracted_P_val,
    shifted_sub_val a b ha hb]
  have hshift : a.val + m31Modulus - b.val = a.val - b.val + m31Modulus := by
    omega
  rw [hshift]
  have hsmall : a.val - b.val < u32Cardinality := by
    unfold CanonicalRawM31 at ha
    norm_num [m31Modulus, u32Cardinality] at ha ⊢
    omega
  have hp_le_u32 : m31Modulus ≤ u32Cardinality := by
    norm_num [m31Modulus, u32Cardinality]
  have hrewrite :
      a.val - b.val + m31Modulus + (u32Cardinality - m31Modulus) =
        (a.val - b.val) + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]

theorem rawM31Sub_canonical
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    CanonicalRawM31 (rawM31Sub x y) := by
  by_cases h : y ≤ x
  · rw [rawM31Sub, if_pos h]
    unfold CanonicalRawM31 at hx ⊢
    omega
  · have hxy : x < y := Nat.lt_of_not_ge h
    rw [rawM31Sub, if_neg h]
    unfold CanonicalRawM31 at hy ⊢
    omega

theorem residue_rawM31Sub
    {x y : Nat} (_hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    ((rawM31Sub x y : Nat) : M31Exact) =
      (x : M31Exact) - (y : M31Exact) := by
  by_cases h : y ≤ x
  · rw [rawM31Sub, if_pos h, Nat.cast_sub h]
  · have hy_le : y ≤ x + m31Modulus := by
      unfold CanonicalRawM31 at hy
      omega
    rw [rawM31Sub, if_neg h, Nat.cast_sub hy_le, Nat.cast_add,
      ZMod.natCast_self, add_zero]

theorem extracted_m31_sub_corresponds
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : field.M31,
      field.M31.sub a b = ok out ∧
      out.val = rawM31Sub a.val b.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) - (b.val : M31Exact) := by
  let shifted := Std.U32.wrapping_sub (Std.U32.wrapping_add a field.P) b
  by_cases hhigh : b.val ≤ a.val
  · let out := Std.U32.wrapping_sub shifted field.P
    have hbranch : m31Modulus ≤ shifted.val := by
      exact (shifted_high_iff a b ha hb).2 hhigh
    have hout : out.val = a.val - b.val :=
      high_sub_P_val a b ha hb hhigh
    have hraw : out.val = rawM31Sub a.val b.val := by
      rw [hout, rawM31Sub, if_pos hhigh]
    refine ⟨out, ?_, hraw, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_pos hbranch]
    · rw [hraw]
      exact rawM31Sub_canonical ha hb
    · rw [hraw]
      exact residue_rawM31Sub ha hb
  · let out := shifted
    have hbranch : ¬m31Modulus ≤ shifted.val := by
      intro h
      exact hhigh ((shifted_high_iff a b ha hb).1 h)
    have hout : out.val = a.val + m31Modulus - b.val :=
      shifted_sub_val a b ha hb
    have hraw : out.val = rawM31Sub a.val b.val := by
      rw [hout, rawM31Sub, if_neg hhigh]
    refine ⟨out, ?_, hraw, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_neg hbranch]
    · rw [hraw]
      exact rawM31Sub_canonical ha hb
    · rw [hraw]
      exact residue_rawM31Sub ha hb

#print axioms shifted_sub_val
#print axioms high_sub_P_val
#print axioms residue_rawM31Sub
#print axioms extracted_m31_sub_corresponds

end AspisAeneasM31Sub
