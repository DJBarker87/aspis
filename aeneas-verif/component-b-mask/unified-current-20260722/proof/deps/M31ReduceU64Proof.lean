import AspisCoreFieldReduceU64
import Mathlib.Data.ZMod.Basic

/-!
# Extracted full-u64 M31 reduction correspondence

This file proves the Aeneas model extracted from production `reduce_u64`
canonicalizes every Rust `u64`, not only products of canonical M31 values.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasM31ReduceU64

open aspis_core

abbrev m31Modulus : Nat := 2147483647
abbrev u32Cardinality : Nat := 2 ^ 32
abbrev u64Cardinality : Nat := 2 ^ 64
def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus
abbrev M31Exact := ZMod m31Modulus

def mersenneFold31 (x : Nat) : Nat :=
  x % (2 ^ 31) + x / (2 ^ 31)

def rawM31ReduceU64 (x : Nat) : Nat :=
  let folded := mersenneFold31 (mersenneFold31 x)
  if m31Modulus ≤ folded then folded - m31Modulus else folded

@[simp] theorem extracted_P_val : field.P.val = m31Modulus := by
  unfold field.P
  rfl

theorem u32_size_eq : UScalar.size .U32 = u32Cardinality := by
  rw [UScalar.size_def, UScalarTy.U32_numBits_eq]

theorem u64_size_eq : UScalar.size .U64 = u64Cardinality := by
  rw [UScalar.size_def, UScalarTy.U64_numBits_eq]

theorem m31Modulus_eq_two31_sub_one : m31Modulus = 2 ^ 31 - 1 := by
  norm_num [m31Modulus]

theorem shift31_val (x : Std.U64) :
    (Std.U64.wrapping_shr x 31#u32).val = x.val / 2 ^ 31 := by
  change (Std.U64.wrapping_shr x 31#u32).bv.toNat =
    x.bv.toNat / 2 ^ 31
  rw [Std.U64.wrapping_shr_bv_eq, BitVec.ushiftRight_eq,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  norm_num

theorem masked31_val (x : Std.U64) :
    (x &&& UScalar.cast .U64 field.P).val = x.val % 2 ^ 31 := by
  rw [UScalar.val_and, U32.cast_U64_val_eq, extracted_P_val,
    m31Modulus_eq_two31_sub_one, Nat.and_two_pow_sub_one_eq_mod]

theorem mersenneFold31_lt_two34
    {x : Nat} (hx : x < 2 ^ 64) :
    mersenneFold31 x < 2 ^ 34 := by
  have hmod : x % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  have hdiv : x / 2 ^ 31 < 2 ^ 33 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num at hx ⊢
    exact hx
  unfold mersenneFold31
  omega

theorem secondFold_lt_modulus_add_eight
    {x : Nat} (hx : x < 2 ^ 64) :
    mersenneFold31 (mersenneFold31 x) < m31Modulus + 8 := by
  have hfirst := mersenneFold31_lt_two34 hx
  have hmod : mersenneFold31 x % 2 ^ 31 < 2 ^ 31 :=
    Nat.mod_lt _ (by positivity)
  have hdiv : mersenneFold31 x / 2 ^ 31 < 8 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num at hfirst ⊢
    exact hfirst
  unfold mersenneFold31
  norm_num [m31Modulus] at hmod hdiv ⊢
  omega

theorem secondFold_lt_u32
    {x : Nat} (hx : x < 2 ^ 64) :
    mersenneFold31 (mersenneFold31 x) < u32Cardinality := by
  have h := secondFold_lt_modulus_add_eight hx
  norm_num [m31Modulus, u32Cardinality] at h ⊢
  omega

theorem rawM31ReduceU64_canonical
    {x : Nat} (hx : x < 2 ^ 64) :
    CanonicalRawM31 (rawM31ReduceU64 x) := by
  have hbound := secondFold_lt_modulus_add_eight hx
  by_cases hhigh :
      m31Modulus ≤ mersenneFold31 (mersenneFold31 x)
  · rw [rawM31ReduceU64, if_pos hhigh]
    unfold CanonicalRawM31
    norm_num [m31Modulus] at hbound ⊢
    omega
  · have hlow : mersenneFold31 (mersenneFold31 x) < m31Modulus :=
      Nat.lt_of_not_ge hhigh
    rw [rawM31ReduceU64, if_neg hhigh]
    exact hlow

theorem cast_two31_eq_one :
    ((2 ^ 31 : Nat) : M31Exact) = 1 := by
  have h : 2 ^ 31 = m31Modulus + 1 := by
    norm_num [m31Modulus]
  rw [h, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

theorem residue_mersenneFold31 (x : Nat) :
    ((mersenneFold31 x : Nat) : M31Exact) = (x : M31Exact) := by
  rw [mersenneFold31, Nat.cast_add]
  calc
    ((x % 2 ^ 31 : Nat) : M31Exact) +
          ((x / 2 ^ 31 : Nat) : M31Exact) =
        ((x % 2 ^ 31 : Nat) : M31Exact) +
          ((x / 2 ^ 31 : Nat) : M31Exact) *
            ((2 ^ 31 : Nat) : M31Exact) := by
              rw [cast_two31_eq_one, mul_one]
    _ = ((x % 2 ^ 31 + (x / 2 ^ 31) * 2 ^ 31 : Nat) : M31Exact) := by
          rw [Nat.cast_add, Nat.cast_mul]
    _ = (x : M31Exact) := by rw [Nat.mod_add_div']

theorem residue_rawM31ReduceU64 (x : Nat) :
    ((rawM31ReduceU64 x : Nat) : M31Exact) = (x : M31Exact) := by
  by_cases hhigh :
      m31Modulus ≤ mersenneFold31 (mersenneFold31 x)
  · rw [rawM31ReduceU64, if_pos hhigh, Nat.cast_sub hhigh,
      ZMod.natCast_self, sub_zero, residue_mersenneFold31,
      residue_mersenneFold31]
  · rw [rawM31ReduceU64, if_neg hhigh, residue_mersenneFold31,
      residue_mersenneFold31]

def extractedFold31 (x : Std.U64) : Std.U64 :=
  Std.U64.wrapping_add
    (x &&& UScalar.cast .U64 field.P)
    (Std.U64.wrapping_shr x 31#u32)

def extractedReduceOut (x : Std.U64) : Std.U32 :=
  let folded := extractedFold31 (extractedFold31 x)
  let narrowed := UScalar.cast .U32 folded
  if narrowed >= field.P then Std.U32.wrapping_sub narrowed field.P
  else narrowed

theorem extractedFold31_val
    (x : Std.U64) (hx : x.val < 2 ^ 64) :
    (extractedFold31 x).val = mersenneFold31 x.val := by
  rw [extractedFold31, Std.U64.wrapping_add_val_eq, u64_size_eq,
    masked31_val, shift31_val]
  apply Nat.mod_eq_of_lt
  change mersenneFold31 x.val < u64Cardinality
  have h := mersenneFold31_lt_two34 hx
  norm_num [u64Cardinality] at h ⊢
  omega

theorem extractedSecondFold_val (x : Std.U64) :
    (extractedFold31 (extractedFold31 x)).val =
      mersenneFold31 (mersenneFold31 x.val) := by
  have hx : x.val < 2 ^ 64 := by
    simpa [UScalarTy.U64_numBits_eq] using x.hmax
  have hfirst : (extractedFold31 x).val < 2 ^ 64 := by
    simpa [UScalarTy.U64_numBits_eq] using (extractedFold31 x).hmax
  rw [extractedFold31_val _ hfirst, extractedFold31_val x hx]

theorem narrowedSecondFold_val (x : Std.U64) :
    (UScalar.cast .U32 (extractedFold31 (extractedFold31 x))).val =
      mersenneFold31 (mersenneFold31 x.val) := by
  rw [UScalar.cast_val_eq, extractedSecondFold_val,
    UScalarTy.U32_numBits_eq]
  have hx : x.val < 2 ^ 64 := by
    simpa [UScalarTy.U64_numBits_eq] using x.hmax
  rw [Nat.mod_eq_of_lt (secondFold_lt_u32 hx)]

theorem extracted_reduce_u64_eq_out (x : Std.U64) :
    field.reduce_u64 x = ok (extractedReduceOut x) := by
  unfold field.reduce_u64 extractedReduceOut extractedFold31
  simp only [Std.lift, bind_tc_ok]
  split <;> rfl

theorem wrapping_sub_P_val
    (narrowed : Std.U32) (hhigh : m31Modulus ≤ narrowed.val) :
    (Std.U32.wrapping_sub narrowed field.P).val =
      narrowed.val - m31Modulus := by
  change (UScalar.overflowing_sub narrowed field.P).fst.val =
    narrowed.val - m31Modulus
  have hnot : ¬narrowed.val < field.P.val := by
    rw [extracted_P_val]
    omega
  have hspec := UScalar.overflowing_sub_eq narrowed field.P
  simp only [hnot, ↓reduceIte] at hspec
  simpa [extracted_P_val] using hspec.1

theorem extractedReduceOut_val (x : Std.U64) :
    (extractedReduceOut x).val = rawM31ReduceU64 x.val := by
  let narrowed := UScalar.cast .U32 (extractedFold31 (extractedFold31 x))
  have hnarrow : narrowed.val = mersenneFold31 (mersenneFold31 x.val) :=
    narrowedSecondFold_val x
  change
    (if narrowed >= field.P then Std.U32.wrapping_sub narrowed field.P
      else narrowed).val = rawM31ReduceU64 x.val
  by_cases hhigh : m31Modulus ≤ mersenneFold31 (mersenneFold31 x.val)
  · have hscalar : narrowed >= field.P := by
      change field.P.val ≤ narrowed.val
      rw [extracted_P_val, hnarrow]
      exact hhigh
    rw [if_pos hscalar, rawM31ReduceU64, if_pos hhigh,
      wrapping_sub_P_val narrowed (by simpa [hnarrow] using hhigh), hnarrow]
  · have hscalar : ¬narrowed >= field.P := by
      intro h
      apply hhigh
      change field.P.val ≤ narrowed.val at h
      rw [extracted_P_val, hnarrow] at h
      exact h
    rw [if_neg hscalar, rawM31ReduceU64, if_neg hhigh, hnarrow]

theorem extracted_reduce_u64_corresponds (x : Std.U64) :
    ∃ out : Std.U32,
      field.reduce_u64 x = ok out ∧
      out.val = rawM31ReduceU64 x.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = (x.val : M31Exact) := by
  let out := extractedReduceOut x
  have hx : x.val < 2 ^ 64 := by
    simpa [UScalarTy.U64_numBits_eq] using x.hmax
  have hout : out.val = rawM31ReduceU64 x.val := extractedReduceOut_val x
  refine ⟨out, extracted_reduce_u64_eq_out x, hout, ?_, ?_⟩
  · rw [hout]
    exact rawM31ReduceU64_canonical hx
  · rw [hout]
    exact residue_rawM31ReduceU64 x.val

#print axioms shift31_val
#print axioms rawM31ReduceU64_canonical
#print axioms residue_rawM31ReduceU64
#print axioms extracted_reduce_u64_corresponds

end AspisAeneasM31ReduceU64
