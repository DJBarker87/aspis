import Aeneas.Std

open Aeneas Aeneas.Std

/-!
The pinned Aeneas `wrapping_shl` model accepts a `U32` count, while Charon
preserves the production `mul_pow2` parameter as `U8`.  Zero extension is the
exact coercion for every Rust `u8` shift value and changes no generated body.
-/

instance u8ToU32ZeroExtend : Coe Std.U8 Std.U32 where
  coe x := UScalar.cast .U32 x

theorem u8ToU32ZeroExtend_val (x : Std.U8) :
    (x : Std.U32).val = x.val := by
  exact U8.cast_U32_val_eq x

#print axioms u8ToU32ZeroExtend_val
