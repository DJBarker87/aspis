import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std

/-!
Charon records each unsuffixed Rust shift literal in `M31::half` as `I32`,
while the pinned Aeneas `wrapping_shr` model accepts a `U32` shift count.
This same-width bit-pattern coercion makes the literal one exact.  It changes
no generated function body.
-/

instance i32ToU32SameWidth : Coe Std.I32 Std.U32 where
  coe x := ⟨x.bv⟩

theorem halfShiftCountOne_exact : ((1#i32 : Std.I32) : Std.U32) = 1#u32 := by
  rfl

#print axioms halfShiftCountOne_exact
