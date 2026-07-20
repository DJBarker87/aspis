import AspisCoreFieldNeg
import Mathlib.Data.ZMod.Basic

/-!
# Extracted Rust M31 negation correspondence

This proof applies directly to the Aeneas definition extracted from the
production `aspis-core/src/field.rs` implementation.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasM31Neg

open aspis_core

abbrev m31Modulus : Nat := 2147483647
abbrev u32Cardinality : Nat := 2 ^ 32
def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus
abbrev M31Exact := ZMod m31Modulus

def rawM31Neg (x : Nat) : Nat :=
  if x = 0 then 0 else m31Modulus - x

@[simp] theorem extracted_P_val : field.P.val = m31Modulus := by
  unfold field.P
  rfl

theorem u32_size_eq : UScalar.size .U32 = u32Cardinality := by
  rw [UScalar.size_def, UScalarTy.U32_numBits_eq]

theorem extracted_m31_neg_eq_conditional (a : field.M31) :
    field.M31.neg a =
      if a = 0#u32 then ok 0#u32
      else ok (Std.U32.wrapping_sub field.P a) := by
  simp [field.M31.neg, Std.lift]

theorem scalar_eq_zero_iff (a : field.M31) :
    a = 0#u32 ↔ a.val = 0 := by
  constructor
  · intro h
    simp [h]
  · intro h
    apply UScalar.eq_of_val_eq
    simpa using h

theorem wrapping_P_sub_val
    (a : field.M31) (ha : CanonicalRawM31 a.val) :
    (Std.U32.wrapping_sub field.P a).val = m31Modulus - a.val := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, extracted_P_val]
  have ha_le_P : a.val ≤ m31Modulus := by
    unfold CanonicalRawM31 at ha
    omega
  have ha_le_u32 : a.val ≤ u32Cardinality := by
    unfold CanonicalRawM31 at ha
    norm_num [m31Modulus, u32Cardinality] at ha ⊢
    omega
  have hsmall : m31Modulus - a.val < u32Cardinality := by
    norm_num [m31Modulus, u32Cardinality]
    omega
  have hrewrite :
      m31Modulus + (u32Cardinality - a.val) =
        (m31Modulus - a.val) + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]

theorem rawM31Neg_canonical
    {x : Nat} (hx : CanonicalRawM31 x) :
    CanonicalRawM31 (rawM31Neg x) := by
  by_cases hzero : x = 0
  · simp [rawM31Neg, hzero, CanonicalRawM31, m31Modulus]
  · rw [rawM31Neg, if_neg hzero]
    unfold CanonicalRawM31 at hx ⊢
    omega

theorem residue_rawM31Neg
    {x : Nat} (hx : CanonicalRawM31 x) :
    ((rawM31Neg x : Nat) : M31Exact) = -(x : M31Exact) := by
  by_cases hzero : x = 0
  · simp [rawM31Neg, hzero]
  · have hx_le : x ≤ m31Modulus := by
      unfold CanonicalRawM31 at hx
      omega
    rw [rawM31Neg, if_neg hzero, Nat.cast_sub hx_le,
      ZMod.natCast_self, zero_sub]

theorem extracted_m31_neg_corresponds
    (a : field.M31) (ha : CanonicalRawM31 a.val) :
    ∃ out : field.M31,
      field.M31.neg a = ok out ∧
      out.val = rawM31Neg a.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = -(a.val : M31Exact) := by
  by_cases hzero : a.val = 0
  · let out : field.M31 := 0#u32
    have hascalar : a = 0#u32 := (scalar_eq_zero_iff a).2 hzero
    have hraw : out.val = rawM31Neg a.val := by
      simp [out, rawM31Neg, hzero]
    refine ⟨out, ?_, hraw, ?_, ?_⟩
    · rw [extracted_m31_neg_eq_conditional, if_pos hascalar]
    · rw [hraw]
      exact rawM31Neg_canonical ha
    · rw [hraw]
      exact residue_rawM31Neg ha
  · let out := Std.U32.wrapping_sub field.P a
    have hascalar : a ≠ 0#u32 := by
      intro h
      exact hzero ((scalar_eq_zero_iff a).1 h)
    have hout : out.val = m31Modulus - a.val := wrapping_P_sub_val a ha
    have hraw : out.val = rawM31Neg a.val := by
      rw [hout, rawM31Neg, if_neg hzero]
    refine ⟨out, ?_, hraw, ?_, ?_⟩
    · rw [extracted_m31_neg_eq_conditional, if_neg hascalar]
    · rw [hraw]
      exact rawM31Neg_canonical ha
    · rw [hraw]
      exact residue_rawM31Neg ha

#print axioms wrapping_P_sub_val
#print axioms residue_rawM31Neg
#print axioms extracted_m31_neg_corresponds

end AspisAeneasM31Neg
