import V7LiteralCallerCorePrimitivesExternal

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1

theorem bool_then_some_true_exact {T : Type} (value : T) :
    core.bool.Bool.then_some true value = .ok (some value) := by
  rfl

theorem bool_then_some_false_exact {T : Type} (value : T) :
    core.bool.Bool.then_some false value = .ok none := by
  rfl

theorem option_as_ref_exact {T : Type} (value : Option T) :
    core.option.Option.as_ref value = .ok value := by
  rfl

theorem option_ok_or_some_exact {T E : Type} (value : T) (error : E) :
    core.option.Option.ok_or (some value) error = .ok (.Ok value) := by
  rfl

theorem option_ok_or_none_exact {T E : Type} (error : E) :
    core.option.Option.ok_or (none : Option T) error = .ok (.Err error) := by
  rfl

theorem slice_first_exact {T : Type} (value : Slice T) :
    core.slice.Slice.first value = .ok value.val.head? := by
  rfl

theorem slice_last_exact {T : Type} (value : Slice T) :
    core.slice.Slice.last value = .ok value.val.getLast? := by
  rfl

theorem u32_checked_shl_out_of_range
    (value : Std.U32) (shift : Std.U32) (large : 32 ≤ shift.val) :
    core.num.U32.checked_shl value shift = .ok none := by
  simp [core.num.U32.checked_shl, Nat.not_lt.mpr large]

theorem usize_checked_shl_out_of_range
    (value : Std.Usize) (shift : Std.U32)
    (large : System.Platform.numBits ≤ shift.val) :
    core.num.Usize.checked_shl value shift = .ok none := by
  simp [core.num.Usize.checked_shl, Nat.not_lt.mpr large]

#print axioms bool_then_some_true_exact
#print axioms bool_then_some_false_exact
#print axioms option_as_ref_exact
#print axioms option_ok_or_some_exact
#print axioms option_ok_or_none_exact
#print axioms slice_first_exact
#print axioms slice_last_exact
#print axioms u32_checked_shl_out_of_range
#print axioms usize_checked_shl_out_of_range

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
