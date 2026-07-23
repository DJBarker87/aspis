import AspisCoreFieldAddSubNeg
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Source-authentic QM31 additive correspondence

This file imports one Aeneas module generated directly from the tracked
`aspis-core/src/field.rs` add/sub/neg methods.  One combined extraction is
necessary: independently generated operation modules each redeclare the same
Rust types and cannot be imported together in Lean.

The proof proceeds through the generated call graph itself:

* generated M31 add/sub/neg to canonical residues;
* generated CM31 add/sub/neg to the exact quadratic pair;
* generated QM31 add/sub/neg to the exact four-limb tower.

The Aeneas project is pinned to Lean 4.31 while AspisFormal currently uses
Lean 4.32.  The explicit four-coordinate tower map is therefore a named
two-kernel compatibility boundary, not yet a single imported theorem chain.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasQM31Additive

open AspisCoreAdditive

/-! ## Canonical base model -/

abbrev m31Modulus : Nat := 2147483647
abbrev u32Cardinality : Nat := 2 ^ 32
abbrev M31Exact := ZMod m31Modulus

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

def rawM31Add (x y : Nat) : Nat :=
  if m31Modulus ≤ x + y then x + y - m31Modulus else x + y

def rawM31Sub (x y : Nat) : Nat :=
  if y ≤ x then x - y else x + m31Modulus - y

def rawM31Neg (x : Nat) : Nat :=
  if x = 0 then 0 else m31Modulus - x

@[simp] theorem extracted_P_val : field.P.val = m31Modulus := by
  unfold field.P
  rfl

theorem u32_size_eq : UScalar.size .U32 = u32Cardinality := by
  rw [UScalar.size_def, UScalarTy.U32_numBits_eq]

/-! ### M31 addition -/

theorem extracted_m31_add_eq_conditional (a b : field.M31) :
    field.M31.add a b =
      if m31Modulus ≤ (Std.U32.wrapping_add a b).val then
        ok (Std.U32.wrapping_sub (Std.U32.wrapping_add a b) field.P)
      else ok (Std.U32.wrapping_add a b) := by
  simp [field.M31.add, Std.lift]

theorem canonical_sum_lt_u32
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    a.val + b.val < u32Cardinality := by
  unfold CanonicalRawM31 at ha hb
  norm_num [m31Modulus, u32Cardinality] at ha hb ⊢
  omega

theorem wrapping_add_val_of_canonical
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    (Std.U32.wrapping_add a b).val = a.val + b.val := by
  rw [Std.U32.wrapping_add_val_eq, u32_size_eq,
    Nat.mod_eq_of_lt (canonical_sum_lt_u32 a b ha hb)]

theorem wrapping_add_sub_P_val
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val)
    (hhigh : m31Modulus ≤ a.val + b.val) :
    (Std.U32.wrapping_sub (Std.U32.wrapping_add a b) field.P).val =
      a.val + b.val - m31Modulus := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, extracted_P_val,
    wrapping_add_val_of_canonical a b ha hb]
  have hsum := canonical_sum_lt_u32 a b ha hb
  have hreduced : a.val + b.val - m31Modulus < u32Cardinality := by
    omega
  have hrewrite :
      a.val + b.val + (u32Cardinality - m31Modulus) =
        (a.val + b.val - m31Modulus) + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hreduced]

theorem rawM31Add_canonical
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    CanonicalRawM31 (rawM31Add x y) := by
  by_cases hhigh : m31Modulus ≤ x + y
  · rw [rawM31Add, if_pos hhigh]
    unfold CanonicalRawM31 at hx hy ⊢
    omega
  · rw [rawM31Add, if_neg hhigh]
    exact Nat.lt_of_not_ge hhigh

theorem residue_rawM31Add
    {x y : Nat} (_hx : CanonicalRawM31 x) (_hy : CanonicalRawM31 y) :
    ((rawM31Add x y : Nat) : M31Exact) =
      (x : M31Exact) + (y : M31Exact) := by
  by_cases hhigh : m31Modulus ≤ x + y
  · rw [rawM31Add, if_pos hhigh, Nat.cast_sub hhigh, Nat.cast_add,
      ZMod.natCast_self, sub_zero]
  · rw [rawM31Add, if_neg hhigh, Nat.cast_add]

theorem extracted_m31_add_corresponds
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : field.M31,
      field.M31.add a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (b.val : M31Exact) := by
  have hadd := wrapping_add_val_of_canonical a b ha hb
  by_cases hhigh : m31Modulus ≤ a.val + b.val
  · let out := Std.U32.wrapping_sub (Std.U32.wrapping_add a b) field.P
    have hbranch : m31Modulus ≤ (Std.U32.wrapping_add a b).val := by
      simpa [hadd] using hhigh
    have hout : out.val = a.val + b.val - m31Modulus :=
      wrapping_add_sub_P_val a b ha hb hhigh
    have hraw : out.val = rawM31Add a.val b.val := by
      rw [hout]
      simp [rawM31Add, hhigh]
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_add_eq_conditional, if_pos hbranch]
    · rw [hraw]
      exact rawM31Add_canonical ha hb
    · rw [hraw]
      exact residue_rawM31Add ha hb
  · let out := Std.U32.wrapping_add a b
    have hbranch : ¬ m31Modulus ≤ (Std.U32.wrapping_add a b).val := by
      simpa [hadd] using hhigh
    have hraw : out.val = rawM31Add a.val b.val := by
      rw [show out.val = a.val + b.val from hadd]
      simp [rawM31Add, hhigh]
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_add_eq_conditional, if_neg hbranch]
    · rw [hraw]
      exact rawM31Add_canonical ha hb
    · rw [hraw]
      exact residue_rawM31Add ha hb

/-! ### M31 subtraction -/

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
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, wrapping_add_P_val a ha]
  have hb_le : b.val ≤ a.val + m31Modulus := by
    unfold CanonicalRawM31 at hb
    omega
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
  have hshift : a.val + m31Modulus - b.val =
      a.val - b.val + m31Modulus := by
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
        a.val - b.val + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]

theorem rawM31Sub_canonical
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    CanonicalRawM31 (rawM31Sub x y) := by
  by_cases h : y ≤ x
  · rw [rawM31Sub, if_pos h]
    unfold CanonicalRawM31 at hx ⊢
    omega
  · rw [rawM31Sub, if_neg h]
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
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) - (b.val : M31Exact) := by
  let shifted := Std.U32.wrapping_sub (Std.U32.wrapping_add a field.P) b
  by_cases hhigh : b.val ≤ a.val
  · let out := Std.U32.wrapping_sub shifted field.P
    have hbranch : m31Modulus ≤ shifted.val :=
      (shifted_high_iff a b ha hb).2 hhigh
    have hout : out.val = a.val - b.val :=
      high_sub_P_val a b ha hb hhigh
    have hraw : out.val = rawM31Sub a.val b.val := by
      rw [hout, rawM31Sub, if_pos hhigh]
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_pos hbranch]
    · rw [hraw]
      exact rawM31Sub_canonical ha hb
    · rw [hraw]
      exact residue_rawM31Sub ha hb
  · let out := shifted
    have hbranch : ¬ m31Modulus ≤ shifted.val := by
      intro h
      exact hhigh ((shifted_high_iff a b ha hb).1 h)
    have hout : out.val = a.val + m31Modulus - b.val :=
      shifted_sub_val a b ha hb
    have hraw : out.val = rawM31Sub a.val b.val := by
      rw [hout, rawM31Sub, if_neg hhigh]
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_neg hbranch]
    · rw [hraw]
      exact rawM31Sub_canonical ha hb
    · rw [hraw]
      exact residue_rawM31Sub ha hb

/-! ### M31 negation -/

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
  have ha_le : a.val ≤ m31Modulus := by
    unfold CanonicalRawM31 at ha
    omega
  have ha_u32 : a.val ≤ u32Cardinality := by
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
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = -(a.val : M31Exact) := by
  by_cases hzero : a.val = 0
  · let out : field.M31 := 0#u32
    have hascalar : a = 0#u32 := (scalar_eq_zero_iff a).2 hzero
    have hraw : out.val = rawM31Neg a.val := by
      simp [out, rawM31Neg, hzero]
    refine ⟨out, ?_, ?_, ?_⟩
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
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_neg_eq_conditional, if_neg hascalar]
    · rw [hraw]
      exact rawM31Neg_canonical ha
    · rw [hraw]
      exact residue_rawM31Neg ha

/-! ## Exact CM31 and QM31 tower -/

abbrev CM31Exact := QuadraticAlgebra M31Exact (-1) 0

def qm31R : CM31Exact := ⟨2, 1⟩

abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0

def cm31ToExact (x : field.CM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def qm31ToExact (x : field.QM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

def CanonicalCM31 (x : field.CM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def CanonicalQM31 (x : field.QM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

/-! ### CM31 composition -/

theorem extracted_cm31_add_corresponds
    (x y : field.CM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : field.CM31,
      field.CM31.add x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x + cm31ToExact y := by
  rcases extracted_m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases extracted_m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  let out : field.CM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [field.CM31.add, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem extracted_cm31_sub_corresponds
    (x y : field.CM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : field.CM31,
      field.CM31.sub x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x - cm31ToExact y := by
  rcases extracted_m31_sub_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases extracted_m31_sub_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  let out : field.CM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [field.CM31.sub, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem extracted_cm31_neg_corresponds
    (x : field.CM31) (hx : CanonicalCM31 x) :
    ∃ out : field.CM31,
      field.CM31.neg x = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = -cm31ToExact x := by
  rcases extracted_m31_neg_corresponds x.a hx.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases extracted_m31_neg_corresponds x.b hx.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  let out : field.CM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [field.CM31.neg, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

/-! ### QM31 composition -/

theorem extracted_qm31_add_corresponds
    (x y : field.QM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out : field.QM31,
      field.QM31.add x y = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x + qm31ToExact y := by
  rcases extracted_cm31_add_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨o0, hcall0, hcan0, hexact0⟩
  rcases extracted_cm31_add_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨o1, hcall1, hcan1, hexact1⟩
  let out : field.QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [field.QM31.add, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem extracted_qm31_sub_corresponds
    (x y : field.QM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out : field.QM31,
      field.QM31.sub x y = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x - qm31ToExact y := by
  rcases extracted_cm31_sub_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨o0, hcall0, hcan0, hexact0⟩
  rcases extracted_cm31_sub_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨o1, hcall1, hcan1, hexact1⟩
  let out : field.QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [field.QM31.sub, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

theorem extracted_qm31_neg_corresponds
    (x : field.QM31) (hx : CanonicalQM31 x) :
    ∃ out : field.QM31,
      field.QM31.neg x = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = -qm31ToExact x := by
  rcases extracted_cm31_neg_corresponds x.c0 hx.1 with
    ⟨o0, hcall0, hcan0, hexact0⟩
  rcases extracted_cm31_neg_corresponds x.c1 hx.2 with
    ⟨o1, hcall1, hcan1, hexact1⟩
  let out : field.QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_⟩
  · simp [field.QM31.neg, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

/-! ## Concrete coordinate-order teeth -/

def orderTooth : field.QM31 :=
  ⟨⟨1#u32, 2#u32⟩, ⟨3#u32, 4#u32⟩⟩

def swapFirstPair (x : field.QM31) : field.QM31 :=
  ⟨⟨x.c0.b, x.c0.a⟩, x.c1⟩

def swapTowerBlocks (x : field.QM31) : field.QM31 :=
  ⟨x.c1, x.c0⟩

theorem orderTooth_canonical : CanonicalQM31 orderTooth := by
  norm_num [CanonicalQM31, CanonicalCM31, CanonicalRawM31,
    orderTooth, m31Modulus]

/-- Swapping the first two M31 limbs changes the exact tower value. -/
theorem wrong_first_pair_order_breaks_exact_tower :
    qm31ToExact (swapFirstPair orderTooth) ≠ qm31ToExact orderTooth := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.re.re) h
  norm_num [qm31ToExact, cm31ToExact, swapFirstPair, orderTooth,
    M31Exact, m31Modulus] at hcoord
  exact (by decide : (2 : M31Exact) ≠ 1) hcoord

/-- Swapping the two CM31 tower blocks also changes the exact tower value. -/
theorem wrong_tower_block_swap_breaks_exact_tower :
    qm31ToExact (swapTowerBlocks orderTooth) ≠ qm31ToExact orderTooth := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.re.re) h
  norm_num [qm31ToExact, cm31ToExact, swapTowerBlocks, orderTooth,
    M31Exact, m31Modulus] at hcoord
  exact (by decide : (3 : M31Exact) ≠ 1) hcoord

/-! ## Axiom audit -/

#print axioms extracted_m31_add_corresponds
#print axioms extracted_m31_sub_corresponds
#print axioms extracted_m31_neg_corresponds
#print axioms extracted_cm31_add_corresponds
#print axioms extracted_cm31_sub_corresponds
#print axioms extracted_cm31_neg_corresponds
#print axioms extracted_qm31_add_corresponds
#print axioms extracted_qm31_sub_corresponds
#print axioms extracted_qm31_neg_corresponds
#print axioms wrong_first_pair_order_breaks_exact_tower
#print axioms wrong_tower_block_swap_breaks_exact_tower

end AspisAeneasQM31Additive
