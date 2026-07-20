import AspisCorePublicReducers
import M31ReduceU64Proof

/-!
# Source-authentic public M31 reducers backed by the generated private reducer

The two public production methods are deliberately proved through their
generated wrapper bodies.  Their shared private call is related to the
already kernel-checked, source-authentic `reduce_u64` capstone.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasPublicU64Reducers

open AspisCorePublicReducers
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

/-- On the complete documented `value < 2^62` domain, the actual generated
`M31::reduce_u62` wrapper succeeds, returns a canonical limb, and denotes the
input residue in M31.  The raw equality pins it to the deployed two-fold
Mersenne reducer rather than merely an extensionally convenient model. -/
theorem extracted_m31_reduce_u62_corresponds
    (value : Std.U64) (_hvalue : value.val < 2 ^ 62) :
    ∃ out : field.M31,
      field.M31.reduce_u62 value = ok out ∧
      out.val = rawM31ReduceU64 value.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = (value.val : M31Exact) := by
  rcases extracted_reduce_u64_corresponds value with
    ⟨out, hreduce, hraw, hcanonical, hresidue⟩
  refine ⟨out, ?_, hraw, hcanonical, hresidue⟩
  unfold field.M31.reduce_u62
  rw [namespacedReduceU64Eq, hreduce]
  rfl

/-- The actual generated public `M31::reduce_u64` wrapper succeeds for every
Rust `u64`, returns a canonical limb, and denotes the input residue in M31. -/
theorem extracted_public_m31_reduce_u64_corresponds
    (value : Std.U64) :
    ∃ out : field.M31,
      field.M31.reduce_u64 value = ok out ∧
      out.val = rawM31ReduceU64 value.val ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = (value.val : M31Exact) := by
  rcases extracted_reduce_u64_corresponds value with
    ⟨out, hreduce, hraw, hcanonical, hresidue⟩
  refine ⟨out, ?_, hraw, hcanonical, hresidue⟩
  unfold field.M31.reduce_u64
  rw [namespacedReduceU64Eq, hreduce]
  rfl

#print axioms extracted_m31_reduce_u62_corresponds
#print axioms extracted_public_m31_reduce_u64_corresponds

end AspisAeneasPublicU64Reducers
