import AspisCoreCm31Multiplicative
import Mathlib.Data.ZMod.Basic

open Aeneas Aeneas.Std Result

namespace GoodMatricesCurrent.SourceExtractedAuthenticM31Sub

abbrev RustM31 := AspisCoreCM31Multiplicative.field.M31
abbrev m31Modulus : Nat := 2147483647
abbrev u32Cardinality : Nat := 2 ^ 32
abbrev M31Exact := ZMod m31Modulus

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

@[simp] theorem extracted_P_val :
    AspisCoreCM31Multiplicative.field.P.val = m31Modulus := by
  unfold AspisCoreCM31Multiplicative.field.P
  rfl

theorem u32_size_eq : UScalar.size .U32 = u32Cardinality := by
  rw [UScalar.size_def, UScalarTy.U32_numBits_eq]

theorem extracted_m31_sub_eq_conditional (a b : RustM31) :
    AspisCoreCM31Multiplicative.field.M31.sub a b =
      let sum := Std.U32.wrapping_add
        a AspisCoreCM31Multiplicative.field.P
      let shifted := Std.U32.wrapping_sub sum b
      if m31Modulus ≤ shifted.val then
        ok (Std.U32.wrapping_sub
          shifted AspisCoreCM31Multiplicative.field.P)
      else ok shifted := by
  simp [AspisCoreCM31Multiplicative.field.M31.sub, Std.lift]

theorem add_P_lt_u32
    (a : RustM31) (ha : CanonicalRawM31 a.val) :
    a.val + m31Modulus < u32Cardinality := by
  unfold CanonicalRawM31 at ha
  norm_num [m31Modulus, u32Cardinality] at ha ⊢
  omega

theorem wrapping_add_P_val
    (a : RustM31) (ha : CanonicalRawM31 a.val) :
    (Std.U32.wrapping_add
      a AspisCoreCM31Multiplicative.field.P).val =
      a.val + m31Modulus := by
  rw [Std.U32.wrapping_add_val_eq, u32_size_eq, extracted_P_val,
    Nat.mod_eq_of_lt (add_P_lt_u32 a ha)]

theorem shifted_sub_val
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    (Std.U32.wrapping_sub
      (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P)
      b).val = a.val + m31Modulus - b.val := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq,
    wrapping_add_P_val a ha]
  have hdiff : a.val + m31Modulus - b.val < u32Cardinality := by
    have := add_P_lt_u32 a ha
    omega
  have hb_u32 : b.val ≤ u32Cardinality := by
    unfold CanonicalRawM31 at hb
    norm_num [m31Modulus, u32Cardinality] at hb ⊢
    omega
  have hrewrite :
      a.val + m31Modulus + (u32Cardinality - b.val) =
        (a.val + m31Modulus - b.val) + u32Cardinality := by
    unfold CanonicalRawM31 at hb
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hdiff]

theorem shifted_high_iff
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    m31Modulus ≤
        (Std.U32.wrapping_sub
          (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P)
          b).val ↔
      b.val ≤ a.val := by
  rw [shifted_sub_val a b ha hb]
  unfold CanonicalRawM31 at hb
  omega

theorem high_sub_P_val
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val)
    (hhigh : b.val ≤ a.val) :
    (Std.U32.wrapping_sub
      (Std.U32.wrapping_sub
        (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P)
        b)
      AspisCoreCM31Multiplicative.field.P).val = a.val - b.val := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, extracted_P_val,
    shifted_sub_val a b ha hb]
  have hshift :
      a.val + m31Modulus - b.val = a.val - b.val + m31Modulus := by
    omega
  rw [hshift]
  have hsmall : a.val - b.val < u32Cardinality := by
    unfold CanonicalRawM31 at ha
    norm_num [m31Modulus, u32Cardinality] at ha ⊢
    omega
  have hp_le_u32 : m31Modulus ≤ u32Cardinality := by
    norm_num [m31Modulus, u32Cardinality]
  have hrewrite :
      a.val - b.val + m31Modulus +
          (u32Cardinality - m31Modulus) =
        a.val - b.val + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]

/-- Authentic generated M31 subtraction, isolated from the multiplicative
module's unrelated reducer dependencies. -/
theorem extracted_m31_sub_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisCoreCM31Multiplicative.field.M31.sub a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) - (b.val : M31Exact) := by
  let shifted := Std.U32.wrapping_sub
    (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P) b
  by_cases hhigh : b.val ≤ a.val
  · let out := Std.U32.wrapping_sub
      shifted AspisCoreCM31Multiplicative.field.P
    have hbranch : m31Modulus ≤ shifted.val :=
      (shifted_high_iff a b ha hb).2 hhigh
    have hout : out.val = a.val - b.val :=
      high_sub_P_val a b ha hb hhigh
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_pos hbranch]
    · rw [hout]
      unfold CanonicalRawM31 at ha ⊢
      omega
    · rw [hout, Nat.cast_sub hhigh]
  · let out := shifted
    have hbranch : ¬ m31Modulus ≤ shifted.val := by
      intro h
      exact hhigh ((shifted_high_iff a b ha hb).1 h)
    have hout : out.val = a.val + m31Modulus - b.val :=
      shifted_sub_val a b ha hb
    have hb_le : b.val ≤ a.val + m31Modulus := by
      unfold CanonicalRawM31 at hb
      omega
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_neg hbranch]
    · rw [hout]
      unfold CanonicalRawM31 at hb ⊢
      omega
    · rw [hout, Nat.cast_sub hb_le, Nat.cast_add,
        ZMod.natCast_self, add_zero]

end GoodMatricesCurrent.SourceExtractedAuthenticM31Sub
