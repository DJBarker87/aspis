import AspisCoreMulPow2
import M31ReduceU64Proof

/-!
# Source-authentic `M31::mul_pow2`

This proof follows the generated `u32 -> u64`, left-shift, and generated
two-fold Mersenne reduction call graph.  The theorem covers every canonical
input and every production-permitted shift through 30.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasMulPow2

open AspisCoreMulPow2
open AspisAeneasM31ReduceU64

abbrev CanonicalRawM31 := AspisAeneasM31ReduceU64.CanonicalRawM31
abbrev M31Exact := AspisAeneasM31ReduceU64.M31Exact

private theorem namespacedReduceU64Eq (x : Std.U64) :
    field.reduce_u64 x = aspis_core.field.reduce_u64 x := by
  have hP : field.P = aspis_core.field.P := by
    apply UScalar.eq_of_val_eq
    unfold field.P aspis_core.field.P
    rfl
  unfold field.reduce_u64 aspis_core.field.reduce_u64
  rw [hP]

private theorem canonicalShiftProductLtU64
    (x : field.M31) (shift : Std.U8)
    (hx : CanonicalRawM31 x.val) (hshift : shift.val ≤ 30) :
    x.val * 2 ^ shift.val < 2 ^ 64 := by
  have hx31 : x.val < 2 ^ 31 := by
    change x.val < m31Modulus at hx
    norm_num [m31Modulus] at hx ⊢
    omega
  have hpow : 2 ^ shift.val ≤ 2 ^ 30 :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hshift
  have hmul : x.val * 2 ^ shift.val < 2 ^ 31 * 2 ^ 30 :=
    Nat.mul_lt_mul_of_lt_of_le hx31 hpow (by positivity)
  norm_num [← pow_add] at hmul ⊢
  omega

private theorem generatedShiftVal
    (x : field.M31) (shift : Std.U8)
    (hx : CanonicalRawM31 x.val) (hshift : shift.val ≤ 30) :
    (Std.U64.wrapping_shl (UScalar.cast .U64 x) shift).val =
      x.val * 2 ^ shift.val := by
  change
    (((UScalar.cast .U64 x).bv <<<
      (((shift : Std.U32).val) % 64)).toNat) =
      x.val * 2 ^ shift.val
  rw [BitVec.toNat_shiftLeft, u8ToU32ZeroExtend_val]
  have hshift64 : shift.val < 64 := by omega
  rw [Nat.mod_eq_of_lt hshift64, Nat.shiftLeft_eq]
  change
    (UScalar.cast .U64 x).val * 2 ^ shift.val % 2 ^ 64 =
      x.val * 2 ^ shift.val
  rw [U32.cast_U64_val_eq,
    Nat.mod_eq_of_lt (canonicalShiftProductLtU64 x shift hx hshift)]

/-- The generated `M31::mul_pow2` succeeds for every canonical input and
every permitted `u8` shift through 30, returns a canonical limb, and maps to
exact multiplication by `2^shift` in M31. -/
theorem extracted_m31_mul_pow2_corresponds
    (x : field.M31) (shift : Std.U8)
    (hx : CanonicalRawM31 x.val) (hshift : shift.val ≤ 30) :
    ∃ out : field.M31,
      field.M31.mul_pow2 x shift = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (x.val : M31Exact) * (2 : M31Exact) ^ shift.val := by
  let shifted := Std.U64.wrapping_shl (UScalar.cast .U64 x) shift
  have hshifted : shifted.val = x.val * 2 ^ shift.val :=
    generatedShiftVal x shift hx hshift
  rcases extracted_reduce_u64_corresponds shifted with
    ⟨out, hreduce, _hraw, hcanonical, hresidue⟩
  refine ⟨out, ?_, hcanonical, ?_⟩
  · unfold field.M31.mul_pow2
    simp only [Std.lift, bind_tc_ok]
    rw [namespacedReduceU64Eq, hreduce]
    rfl
  · calc
      ((out.val : Nat) : M31Exact) = (shifted.val : M31Exact) := hresidue
      _ = ((x.val * 2 ^ shift.val : Nat) : M31Exact) :=
        congrArg (fun n : Nat => (n : M31Exact)) hshifted
      _ = (x.val : M31Exact) * (2 : M31Exact) ^ shift.val := by
        rw [Nat.cast_mul, Nat.cast_pow]
        norm_num

/-- The declared upper bound is genuinely part of the theorem domain: at a
full-word count the generated release semantics wrap the count modulo 64,
which is not multiplication by `2^64` in M31. -/
theorem shift_bound_is_necessary :
    field.M31.mul_pow2 1#u32 64#u8 = ok 1#u32 ∧
    (1 : M31Exact) ≠ (1 : M31Exact) * (2 : M31Exact) ^ 64 := by
  let shifted :=
    Std.U64.wrapping_shl (UScalar.cast .U64 (1#u32 : Std.U32)) (64#u8 : Std.U8)
  have hshifted : shifted = 1#u64 := by decide
  rcases extracted_reduce_u64_corresponds shifted with
    ⟨out, hreduce, hraw, _hcanonical, _hresidue⟩
  have hrawOne : rawM31ReduceU64 shifted.val = 1 := by
    rw [hshifted]
    norm_num [rawM31ReduceU64, mersenneFold31, m31Modulus]
  have houtVal : out.val = 1 := hraw.trans hrawOne
  have hout : out = 1#u32 := by
    apply UScalar.eq_of_val_eq
    simpa using houtVal
  constructor
  · unfold field.M31.mul_pow2
    simp only [Std.lift, bind_tc_ok]
    change (do let out ← field.reduce_u64 shifted; ok out) = ok 1#u32
    rw [namespacedReduceU64Eq, hreduce, hout]
    rfl
  · decide

#print axioms extracted_m31_mul_pow2_corresponds
#print axioms shift_bound_is_necessary

end AspisAeneasMulPow2
