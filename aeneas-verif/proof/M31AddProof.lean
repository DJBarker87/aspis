import AspisCoreFieldAdd
import Mathlib.Data.ZMod.Basic

/-!
# Extracted Rust M31 addition correspondence

This file imports the Aeneas output generated from the production
`aspis-core/src/field.rs` implementation.  It does not restate the Rust
function.  The capstone theorem below applies directly to
`aspis_core.field.M31.add` and exposes the natural-number reduction graph used
by the main AspisFormal arithmetic seam.

The generated release-mode semantics use `wrapping_add` and `wrapping_sub`.
Canonical M31 inputs make both operations non-wrapping; those bounds are
proved explicitly rather than assumed.

This Aeneas project is pinned to Lean 4.31 and the main AspisFormal corpus is
currently on Lean 4.32.  The identical explicit `rawM31Add` graph below is the
named compatibility boundary between the two separately kernel-checked
artifacts until the toolchains align; no theorem here claims that cross-project
import edge is already closed.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasM31Add

open aspis_core

/-- The natural-number value of the deployed Mersenne prime. -/
abbrev m31Modulus : Nat := 2147483647

/-- The cardinality of a Rust `u32`. -/
abbrev u32Cardinality : Nat := 2 ^ 32

/-- Canonicality of a raw Rust M31 word. -/
def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

/-- The literal one-subtraction graph shared with the AspisFormal seam. -/
def rawM31Add (x y : Nat) : Nat :=
  let sum := x + y
  if m31Modulus ≤ sum then sum - m31Modulus else sum

/-- The exact mathematical field targeted by the main arithmetic seam. -/
abbrev M31Exact := ZMod m31Modulus

@[simp] theorem extracted_P_val : field.P.val = m31Modulus := by
  unfold field.P
  rfl

theorem u32_size_eq : UScalar.size .U32 = u32Cardinality := by
  rw [UScalar.size_def, UScalarTy.U32_numBits_eq]

/-- Unfold the exact generated function once, retaining its two literal
wrapping operations and comparison. -/
theorem extracted_m31_add_eq_conditional (a b : field.M31) :
    field.M31.add a b =
      if m31Modulus ≤ (Std.U32.wrapping_add a b).val then
        ok (Std.U32.wrapping_sub (Std.U32.wrapping_add a b) field.P)
      else ok (Std.U32.wrapping_add a b) := by
  simp [field.M31.add, Std.lift]

/-- Canonical inputs cannot overflow the generated `wrapping_add`. -/
theorem canonical_sum_lt_u32
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    a.val + b.val < u32Cardinality := by
  unfold CanonicalRawM31 at ha hb
  norm_num [m31Modulus, u32Cardinality] at ha hb ⊢
  omega

/-- Therefore the generated wrapping addition has the ordinary natural sum
as its stored value. -/
theorem wrapping_add_val_of_canonical
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    (Std.U32.wrapping_add a b).val = a.val + b.val := by
  rw [Std.U32.wrapping_add_val_eq, u32_size_eq,
    Nat.mod_eq_of_lt (canonical_sum_lt_u32 a b ha hb)]

/-- In the high branch the generated wrapping subtraction is also ordinary
subtraction. -/
theorem wrapping_sub_P_val_of_high
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val)
    (hhigh : m31Modulus ≤ a.val + b.val) :
    (Std.U32.wrapping_sub (Std.U32.wrapping_add a b) field.P).val =
      a.val + b.val - m31Modulus := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, extracted_P_val,
    wrapping_add_val_of_canonical a b ha hb]
  have hsum : a.val + b.val < u32Cardinality :=
    canonical_sum_lt_u32 a b ha hb
  have hreduced : a.val + b.val - m31Modulus < u32Cardinality := by
    omega
  have hrewrite :
      a.val + b.val + (u32Cardinality - m31Modulus) =
        (a.val + b.val - m31Modulus) + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hreduced]

/-- One conditional subtraction is the ordinary remainder modulo `P`. -/
theorem rawM31Add_eq_mod
    {x y : Nat} (hx : CanonicalRawM31 x) (hy : CanonicalRawM31 y) :
    rawM31Add x y = (x + y) % m31Modulus := by
  by_cases hhigh : m31Modulus ≤ x + y
  · have hreduced : x + y - m31Modulus < m31Modulus := by
      unfold CanonicalRawM31 at hx hy
      omega
    rw [rawM31Add, if_pos hhigh, Nat.mod_eq_sub_mod hhigh,
      Nat.mod_eq_of_lt hreduced]
  · have hlow : x + y < m31Modulus := Nat.lt_of_not_ge hhigh
    rw [rawM31Add, if_neg hhigh, Nat.mod_eq_of_lt hlow]

/-- The shared natural-number graph commutes with exact M31 addition. -/
theorem residue_rawM31Add
    {x y : Nat} (_hx : CanonicalRawM31 x) (_hy : CanonicalRawM31 y) :
    ((rawM31Add x y : Nat) : M31Exact) =
      (x : M31Exact) + (y : M31Exact) := by
  by_cases hhigh : m31Modulus ≤ x + y
  · rw [rawM31Add, if_pos hhigh, Nat.cast_sub hhigh, Nat.cast_add,
      ZMod.natCast_self, sub_zero]
  · rw [rawM31Add, if_neg hhigh, Nat.cast_add]

/-- Exact generated-function correspondence.  The result is successful,
canonical, equal to the shared raw reduction graph, and equal to field
addition after mapping into `ZMod (2^31-1)`. -/
theorem extracted_m31_add_corresponds
    (a b : field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : field.M31,
      field.M31.add a b = ok out ∧
      out.val = rawM31Add a.val b.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (b.val : M31Exact) := by
  have hadd := wrapping_add_val_of_canonical a b ha hb
  by_cases hhigh : m31Modulus ≤ a.val + b.val
  · let out := Std.U32.wrapping_sub (Std.U32.wrapping_add a b) field.P
    have hbranch : m31Modulus ≤ (Std.U32.wrapping_add a b).val := by
      rw [hadd]
      exact hhigh
    have hout : out.val = a.val + b.val - m31Modulus :=
      wrapping_sub_P_val_of_high a b ha hb hhigh
    have hcanonical : CanonicalRawM31 out.val := by
      rw [hout]
      unfold CanonicalRawM31 at ha hb ⊢
      omega
    have hraw : out.val = rawM31Add a.val b.val := by
      rw [hout]
      simp [rawM31Add, hhigh]
    refine ⟨out, ?_, hraw, hcanonical, ?_⟩
    · rw [extracted_m31_add_eq_conditional, if_pos hbranch]
    · calc
        ((out.val : Nat) : M31Exact) =
            ((rawM31Add a.val b.val : Nat) : M31Exact) := congrArg _ hraw
        _ = (a.val : M31Exact) + (b.val : M31Exact) :=
          residue_rawM31Add ha hb
  · have hlow : a.val + b.val < m31Modulus := Nat.lt_of_not_ge hhigh
    let out := Std.U32.wrapping_add a b
    have hbranch : ¬ m31Modulus ≤ (Std.U32.wrapping_add a b).val := by
      rw [hadd]
      exact hhigh
    have hcanonical : CanonicalRawM31 out.val := by
      rw [show out.val = a.val + b.val from hadd]
      exact hlow
    have hraw : out.val = rawM31Add a.val b.val := by
      rw [show out.val = a.val + b.val from hadd]
      simp [rawM31Add, hhigh]
    refine ⟨out, ?_, hraw, hcanonical, ?_⟩
    · rw [extracted_m31_add_eq_conditional, if_neg hbranch]
    · calc
        ((out.val : Nat) : M31Exact) =
            ((rawM31Add a.val b.val : Nat) : M31Exact) := congrArg _ hraw
        _ = (a.val : M31Exact) + (b.val : M31Exact) :=
          residue_rawM31Add ha hb

/-! ## Axiom audit -/

#print axioms canonical_sum_lt_u32
#print axioms wrapping_sub_P_val_of_high
#print axioms rawM31Add_eq_mod
#print axioms residue_rawM31Add
#print axioms extracted_m31_add_corresponds

end AspisAeneasM31Add
