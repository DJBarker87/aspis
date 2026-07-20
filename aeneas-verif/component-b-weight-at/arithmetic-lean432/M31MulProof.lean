import AspisCoreFieldMulNamespaced
import M31ReduceU64Proof

/-!
# Extracted Rust M31 multiplication correspondence

The multiplication extraction is translated under `AspisCoreMul` solely to
avoid declaration-name collisions with the minimal reduction extraction. Both
Lean modules come from checked LLBC extracted from the same production source
blob. The equality of their two generated reduction functions is proved below
inside Lean.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasM31Mul

open AspisAeneasM31ReduceU64

abbrev CanonicalRawM31 := AspisAeneasM31ReduceU64.CanonicalRawM31
abbrev M31Exact := AspisAeneasM31ReduceU64.M31Exact

theorem namespaced_reduce_u64_eq (x : Std.U64) :
    AspisCoreMul.field.reduce_u64 x = aspis_core.field.reduce_u64 x := by
  have hP : AspisCoreMul.field.P = aspis_core.field.P := by
    apply UScalar.eq_of_val_eq
    unfold AspisCoreMul.field.P aspis_core.field.P
    rfl
  unfold AspisCoreMul.field.reduce_u64 aspis_core.field.reduce_u64
  rw [hP]

theorem canonical_product_lt_u64
    (a b : AspisCoreMul.field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    a.val * b.val < 2 ^ 64 := by
  unfold CanonicalRawM31 AspisAeneasM31ReduceU64.CanonicalRawM31 at ha hb
  norm_num [m31Modulus] at ha hb ⊢
  nlinarith

theorem extracted_product_val
    (a b : AspisCoreMul.field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    (Std.U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val =
      a.val * b.val := by
  rw [Std.U64.wrapping_mul_val_eq,
    U32.cast_U64_val_eq, U32.cast_U64_val_eq,
    AspisAeneasM31ReduceU64.u64_size_eq,
    Nat.mod_eq_of_lt (canonical_product_lt_u64 a b ha hb)]

theorem extracted_m31_mul_corresponds
    (a b : AspisCoreMul.field.M31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : AspisCoreMul.field.M31,
      AspisCoreMul.field.M31.mul a b = ok out ∧
      out.val = rawM31ReduceU64 (a.val * b.val) ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) * (b.val : M31Exact) := by
  let product :=
    Std.U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  have hproduct : product.val = a.val * b.val :=
    extracted_product_val a b ha hb
  obtain ⟨out, hreduce, hraw, hcanonical, hresidue⟩ :=
    extracted_reduce_u64_corresponds product
  refine ⟨out, ?_, ?_, hcanonical, ?_⟩
  · unfold AspisCoreMul.field.M31.mul
    simp only [Std.lift, bind_tc_ok]
    rw [namespaced_reduce_u64_eq, hreduce]
    rfl
  · rw [hraw, hproduct]
  · calc
      ((out.val : Nat) : M31Exact) = (product.val : M31Exact) := hresidue
      _ = ((a.val * b.val : Nat) : M31Exact) := congrArg _ hproduct
      _ = (a.val : M31Exact) * (b.val : M31Exact) := by rw [Nat.cast_mul]

#print axioms namespaced_reduce_u64_eq
#print axioms extracted_product_val
#print axioms extracted_m31_mul_corresponds

end AspisAeneasM31Mul
