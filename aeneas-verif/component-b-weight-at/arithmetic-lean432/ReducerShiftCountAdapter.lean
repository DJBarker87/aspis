import HalfShiftCountAdapter

/-!
The authenticated extraction preserves the unsuffixed Rust shift literal in
`M31::reduce_u128` as an `i32` literal.  Aeneas's unsigned wrapping-shift
model expects a `u32` count.  This adapter uses the same-width bit-pattern
conversion supplied for `half`; at the deployed positive count it is exactly
31.
-/

open Aeneas Aeneas.Std

theorem reducerShiftCount31_exact :
    ((31#i32 : Std.I32) : Std.U32) = 31#u32 := by
  rfl

#print axioms reducerShiftCount31_exact
