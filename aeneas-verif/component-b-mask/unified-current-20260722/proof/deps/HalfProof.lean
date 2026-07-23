import AspisCoreHalf
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Source-authentic M31/CM31/QM31 halving

The capstones below refer directly to the Aeneas definitions generated from
the frozen production `field.rs`.  The exact tower is the same literal nested
quadratic tower used by the existing additive proof.  Halving in each tower
is coordinatewise division by two in exact M31.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasHalf

open AspisCoreHalf

abbrev m31Modulus : Nat := 2147483647
instance m31PrimeFact : Fact m31Modulus.Prime :=
  ⟨by norm_num [m31Modulus]⟩
abbrev M31Exact := ZMod m31Modulus
abbrev CM31Exact := QuadraticAlgebra M31Exact (-1) 0

def qm31R : CM31Exact := ⟨2, 1⟩

abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

def CanonicalCM31 (x : field.CM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def CanonicalQM31 (x : field.QM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def cm31ToExact (x : field.CM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def qm31ToExact (x : field.QM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

def cm31HalfExact (x : CM31Exact) : CM31Exact :=
  ⟨x.re / (2 : M31Exact), x.im / (2 : M31Exact)⟩

def qm31HalfExact (x : QM31Exact) : QM31Exact :=
  ⟨cm31HalfExact x.re, cm31HalfExact x.im⟩

def rawM31Half (x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else (x + m31Modulus) / 2

private theorem u32ShiftOneVal (x : Std.U32) :
    (Std.U32.wrapping_shr x 1#u32).val = x.val / 2 := by
  change (x.bv.ushiftRight (1 % 32)).toNat = x.bv.toNat / 2
  norm_num [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem u64ShiftOneVal (x : Std.U64) :
    (Std.U64.wrapping_shr x 1#u32).val = x.val / 2 := by
  change (x.bv.ushiftRight (1 % 64)).toNat = x.bv.toNat / 2
  norm_num [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bitAndOneVal (x : Std.U32) :
    (x &&& 1#u32).val = x.val % 2 := by
  simp only [UScalar.val_and, UScalar.ofNatCore_val_eq,
    Nat.and_one_is_mod]

private theorem bitAndOneEqZeroIff (x : Std.U32) :
    x &&& 1#u32 = 0#u32 ↔ x.val % 2 = 0 := by
  constructor
  · intro h
    have hv := congrArg UScalar.val h
    simpa [bitAndOneVal] using hv
  · intro h
    apply UScalar.eq_of_val_eq
    simpa [bitAndOneVal] using h

private def oddHalfRaw (x : Std.U32) : Std.U32 :=
  UScalar.cast .U32
    (Std.U64.wrapping_shr
      (Std.U64.wrapping_add (UScalar.cast .U64 x)
        (UScalar.cast .U64 field.P)) 1#u32)

private theorem oddHalfRawVal
    (x : Std.U32) (hx : CanonicalRawM31 x.val) :
    (oddHalfRaw x).val = (x.val + m31Modulus) / 2 := by
  let xu : Std.U64 := UScalar.cast .U64 x
  let pu : Std.U64 := UScalar.cast .U64 field.P
  let sum : Std.U64 := Std.U64.wrapping_add xu pu
  let half64 : Std.U64 := Std.U64.wrapping_shr sum 1#u32
  have hxu : xu.val = x.val := U32.cast_U64_val_eq x
  have hpu : pu.val = m31Modulus := by
    unfold pu field.P m31Modulus
    norm_num
  have hsumBound : x.val + m31Modulus < UScalar.size .U64 := by
    calc
      x.val + m31Modulus < m31Modulus + m31Modulus :=
        Nat.add_lt_add_right hx m31Modulus
      _ < UScalar.size .U64 := by
        norm_num [m31Modulus, U64.size, U64.numBits]
  have hsum : sum.val = x.val + m31Modulus := by
    unfold sum
    rw [U64.wrapping_add_val_eq, Nat.mod_eq_of_lt]
    · rw [hxu, hpu]
    · simpa [hxu, hpu] using hsumBound
  have hhalf : half64.val = (x.val + m31Modulus) / 2 := by
    rw [show half64.val = sum.val / 2 by exact u64ShiftOneVal sum, hsum]
  have hbound : half64.val < 2 ^ UScalarTy.U32.numBits := by
    rw [hhalf]
    unfold CanonicalRawM31 m31Modulus at hx
    norm_num
    omega
  have hcast := UScalar.cast_val_mod_pow_of_inBounds_eq .U32 half64 hbound
  unfold oddHalfRaw
  change (UScalar.cast .U32 half64).val = _
  rw [hcast, hhalf]

private theorem rawM31HalfCanonical
    {x : Nat} (hx : CanonicalRawM31 x) :
    CanonicalRawM31 (rawM31Half x) := by
  by_cases heven : x % 2 = 0
  · rw [rawM31Half, if_pos heven]
    exact lt_of_le_of_lt (Nat.div_le_self x 2) hx
  · rw [rawM31Half, if_neg heven]
    unfold CanonicalRawM31 at hx ⊢
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
    omega

private theorem twoNeZero : (2 : M31Exact) ≠ 0 := by
  decide

private theorem residueRawM31Half
    {x : Nat} (hx : CanonicalRawM31 x) :
    ((rawM31Half x : Nat) : M31Exact) =
      (x : M31Exact) / (2 : M31Exact) := by
  apply (eq_div_iff twoNeZero).2
  by_cases heven : x % 2 = 0
  · have hdecomp := Nat.mod_add_div x 2
    have hdouble : x / 2 * 2 = x := by omega
    rw [rawM31Half, if_pos heven]
    calc
      ((x / 2 : Nat) : M31Exact) * 2 =
          (((x / 2) * 2 : Nat) : M31Exact) := by
            rw [Nat.cast_mul]
            norm_num
      _ = (x : M31Exact) :=
        congrArg (fun n : Nat => (n : M31Exact)) hdouble
  · have hodd : x % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one x with hzero | hone
      · exact False.elim (heven hzero)
      · exact hone
    have hsumMod : (x + m31Modulus) % 2 = 0 := by
      unfold m31Modulus
      omega
    have hdecomp := Nat.mod_add_div (x + m31Modulus) 2
    have hdouble : (x + m31Modulus) / 2 * 2 = x + m31Modulus := by
      omega
    rw [rawM31Half, if_neg heven]
    calc
      (((x + m31Modulus) / 2 : Nat) : M31Exact) * 2 =
          ((((x + m31Modulus) / 2) * 2 : Nat) : M31Exact) := by
            rw [Nat.cast_mul]
            norm_num
      _ = ((x + m31Modulus : Nat) : M31Exact) :=
        congrArg (fun n : Nat => (n : M31Exact)) hdouble
      _ = (x : M31Exact) := by
        rw [Nat.cast_add, ZMod.natCast_self, add_zero]

/-- The generated even branch succeeds, stays canonical, and is exact field
division by two. -/
theorem extracted_m31_half_even_corresponds
    (x : field.M31) (hx : CanonicalRawM31 x.val)
    (heven : x.val % 2 = 0) :
    ∃ out : field.M31,
      field.M31.half x = ok out ∧
      out.val = rawM31Half x.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (x.val : M31Exact) / (2 : M31Exact) := by
  let out : field.M31 := Std.U32.wrapping_shr x 1#u32
  have hcondition : x &&& 1#u32 = 0#u32 :=
    (bitAndOneEqZeroIff x).2 heven
  have hout : out.val = x.val / 2 := u32ShiftOneVal x
  have hraw : out.val = rawM31Half x.val := by
    rw [hout, rawM31Half, if_pos heven]
  refine ⟨out, ?_, hraw, ?_, ?_⟩
  · unfold field.M31.half
    simp only [Std.lift, bind_tc_ok]
    rw [if_pos hcondition, halfShiftCountOne_exact]
  · rw [hraw]
    exact rawM31HalfCanonical hx
  · rw [hraw]
    exact residueRawM31Half hx

/-- The generated odd branch adds `P` before shifting, succeeds, stays
canonical, and is exact field division by two. -/
theorem extracted_m31_half_odd_corresponds
    (x : field.M31) (hx : CanonicalRawM31 x.val)
    (hodd : x.val % 2 = 1) :
    ∃ out : field.M31,
      field.M31.half x = ok out ∧
      out.val = rawM31Half x.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (x.val : M31Exact) / (2 : M31Exact) := by
  let out : field.M31 := oddHalfRaw x
  have hnot : x &&& 1#u32 ≠ 0#u32 := by
    intro h
    have := (bitAndOneEqZeroIff x).1 h
    omega
  have hout : out.val = (x.val + m31Modulus) / 2 := oddHalfRawVal x hx
  have hnotEven : x.val % 2 ≠ 0 := by omega
  have hraw : out.val = rawM31Half x.val := by
    rw [hout, rawM31Half, if_neg hnotEven]
  refine ⟨out, ?_, hraw, ?_, ?_⟩
  · unfold field.M31.half
    simp only [Std.lift, bind_tc_ok]
    rw [if_neg hnot, halfShiftCountOne_exact]
    rfl
  · rw [hraw]
    exact rawM31HalfCanonical hx
  · rw [hraw]
    exact residueRawM31Half hx

/-- Source-authentic generated M31 halving correspondence for every canonical
raw limb, covering both parity branches. -/
theorem extracted_m31_half_corresponds
    (x : field.M31) (hx : CanonicalRawM31 x.val) :
    ∃ out : field.M31,
      field.M31.half x = ok out ∧
      out.val = rawM31Half x.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (x.val : M31Exact) / (2 : M31Exact) := by
  rcases Nat.mod_two_eq_zero_or_one x.val with heven | hodd
  · exact extracted_m31_half_even_corresponds x hx heven
  · exact extracted_m31_half_odd_corresponds x hx hodd

/-- Generated CM31 halving succeeds coordinatewise, preserves canonicality,
and equals exact nested-tower division by two. -/
theorem extracted_cm31_half_corresponds
    (x : field.CM31) (hx : CanonicalCM31 x) :
    ∃ out : field.CM31,
      field.CM31.half x = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31HalfExact (cm31ToExact x) ∧
      cm31ToExact out + cm31ToExact out = cm31ToExact x := by
  rcases extracted_m31_half_corresponds x.a hx.1 with
    ⟨oa, hcallA, _hrawA, hcanA, hexactA⟩
  rcases extracted_m31_half_corresponds x.b hx.2 with
    ⟨ob, hcallB, _hrawB, hcanB, hexactB⟩
  let out : field.CM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_, ?_⟩
  · simp [field.CM31.half, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB
  · apply QuadraticAlgebra.ext
    · change
        (oa.val : M31Exact) + (oa.val : M31Exact) =
          (x.a.val : M31Exact)
      rw [← mul_two]
      exact (eq_div_iff twoNeZero).1 hexactA
    · change
        (ob.val : M31Exact) + (ob.val : M31Exact) =
          (x.b.val : M31Exact)
      rw [← mul_two]
      exact (eq_div_iff twoNeZero).1 hexactB

/-- Generated QM31 halving succeeds on every canonical four-limb input,
preserves every limb's canonicality, and equals exact nested-tower division
by two without swapping either tower block. -/
theorem extracted_qm31_half_corresponds
    (x : field.QM31) (hx : CanonicalQM31 x) :
    ∃ out : field.QM31,
      field.QM31.half x = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31HalfExact (qm31ToExact x) ∧
      qm31ToExact out + qm31ToExact out = qm31ToExact x := by
  rcases extracted_cm31_half_corresponds x.c0 hx.1 with
    ⟨o0, hcall0, hcan0, hexact0, hdouble0⟩
  rcases extracted_cm31_half_corresponds x.c1 hx.2 with
    ⟨o1, hcall1, hcan1, hexact1, hdouble1⟩
  let out : field.QM31 := ⟨o0, o1⟩
  refine ⟨out, ?_, ⟨hcan0, hcan1⟩, ?_, ?_⟩
  · simp [field.QM31.half, hcall0, hcall1, out]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1
  · apply QuadraticAlgebra.ext
    · exact hdouble0
    · exact hdouble1

/-- Concrete odd-input tooth: generated halving of three cannot be replaced
by a plain right shift. -/
theorem odd_plain_right_shift_is_wrong :
    ∃ out : field.M31,
      field.M31.half 3#u32 = ok out ∧
      out.val = 1073741825 ∧
      (Std.U32.wrapping_shr 3#u32 1#u32).val = 1 ∧
      out ≠ Std.U32.wrapping_shr 3#u32 1#u32 := by
  have hx : CanonicalRawM31 (3#u32).val := by
    norm_num [CanonicalRawM31, m31Modulus]
  have hodd : (3#u32).val % 2 = 1 := by norm_num
  rcases extracted_m31_half_odd_corresponds 3#u32 hx hodd with
    ⟨out, hcall, hraw, _hcan, _hexact⟩
  have hout : out.val = 1073741825 := by
    simpa [rawM31Half, m31Modulus] using hraw
  have hshift : (Std.U32.wrapping_shr 3#u32 1#u32).val = 1 := by
    rw [u32ShiftOneVal]
    norm_num
  refine ⟨out, hcall, hout, hshift, ?_⟩
  intro heq
  have hv := congrArg UScalar.val heq
  rw [hout, hshift] at hv
  omega

#print axioms extracted_m31_half_even_corresponds
#print axioms extracted_m31_half_odd_corresponds
#print axioms extracted_m31_half_corresponds
#print axioms extracted_cm31_half_corresponds
#print axioms extracted_qm31_half_corresponds
#print axioms odd_plain_right_shift_is_wrong

end AspisAeneasHalf
