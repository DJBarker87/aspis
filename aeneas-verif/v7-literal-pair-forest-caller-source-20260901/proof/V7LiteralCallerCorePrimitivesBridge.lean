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

theorem option_is_some_and_none_exact
    {T T1 : Type} (fnOnce : core.ops.function.FnOnce T1 T Bool)
    (closure : T1) :
    core.option.Option.is_some_and fnOnce none closure = .ok false := by
  rfl

theorem option_eq_none_none_exact
    {T : Type} (partialEq : core.cmp.PartialEq T T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
        partialEq none none = .ok true := by
  rfl

theorem option_eq_none_some_exact
    {T : Type} (partialEq : core.cmp.PartialEq T T) (value : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
        partialEq none (some value) = .ok false := by
  rfl

theorem option_branch_some_exact {T : Type} (value : T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (some value) =
      .ok (.Continue value) := by
  rfl

theorem option_branch_none_exact {T : Type} :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (none : Option T) =
      .ok (.Break none) := by
  rfl

theorem option_from_residual_none_exact (T : Type) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        T none = .ok none := by
  rfl

theorem result_is_ok_and_err_exact
    {T E F : Type} (fnOnce : core.ops.function.FnOnce F T Bool)
    (error : E) (closure : F) :
    core.result.Result.is_ok_and fnOnce (.Err error) closure = .ok false := by
  rfl

theorem result_ok_ok_exact {T E : Type} (value : T) :
    core.result.Result.ok (.Ok value : core.result.Result T E) =
      .ok (some value) := by
  rfl

theorem result_ok_err_exact {T E : Type} (error : E) :
    core.result.Result.ok (.Err error : core.result.Result T E) =
      .ok none := by
  rfl

theorem result_map_err_branch_exact
    {T E U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (error : E) (closure : F) :
    core.result.Result.map fnOnce (.Err error) closure = .ok (.Err error) := by
  rfl

theorem result_map_err_ok_branch_exact
    {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F)
    (value : T) (closure : O) :
    core.result.Result.map_err fnOnce (.Ok value) closure = .ok (.Ok value) := by
  rfl

theorem box_as_ref_exact {T : Type} (allocator : Type) (value : T) :
    Box.Insts.CoreConvertAsRef.as_ref allocator value = .ok value := by
  rfl

theorem vec_into_boxed_slice_exact
    {T : Type} (allocator : Type) (value : alloc.vec.Vec T) :
    ∃ output : Slice T,
      alloc.vec.Vec.into_boxed_slice allocator value = .ok output ∧
      output.val = value.val := by
  refine ⟨_, rfl, rfl⟩

theorem vec_truncate_values_exact
    {T : Type} (allocator : Type) (value : alloc.vec.Vec T)
    (length : Std.Usize) :
    ∃ output : alloc.vec.Vec T,
      alloc.vec.Vec.truncate allocator value length = .ok output ∧
      output.val = value.val.take length.val := by
  refine ⟨_, rfl, rfl⟩

theorem vec_remove_out_of_bounds
    {T : Type} (allocator : Type) (value : alloc.vec.Vec T)
    (index : Std.Usize) (large : value.val.length ≤ index.val) :
    alloc.vec.Vec.remove allocator value index = .fail .arrayOutOfBounds := by
  simp [alloc.vec.Vec.remove, Nat.not_lt.mpr large]

theorem vec_clear_is_empty
    {T : Type} (allocator : Type) (value : alloc.vec.Vec T) :
    ∃ output : alloc.vec.Vec T,
      alloc.vec.Vec.clear allocator value = .ok output ∧
      output.val = [] := by
  refine ⟨_, rfl, rfl⟩

theorem vec_is_empty_exact
    {T : Type} (allocator : Type) (value : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty allocator value = .ok value.val.isEmpty := by
  rfl

#print axioms bool_then_some_true_exact
#print axioms bool_then_some_false_exact
#print axioms option_as_ref_exact
#print axioms option_ok_or_some_exact
#print axioms option_ok_or_none_exact
#print axioms slice_first_exact
#print axioms slice_last_exact
#print axioms u32_checked_shl_out_of_range
#print axioms usize_checked_shl_out_of_range
#print axioms option_is_some_and_none_exact
#print axioms option_eq_none_none_exact
#print axioms option_eq_none_some_exact
#print axioms option_branch_some_exact
#print axioms option_branch_none_exact
#print axioms option_from_residual_none_exact
#print axioms result_is_ok_and_err_exact
#print axioms result_ok_ok_exact
#print axioms result_ok_err_exact
#print axioms result_map_err_branch_exact
#print axioms result_map_err_ok_branch_exact
#print axioms box_as_ref_exact
#print axioms vec_into_boxed_slice_exact
#print axioms vec_truncate_values_exact
#print axioms vec_remove_out_of_bounds
#print axioms vec_clear_is_empty
#print axioms vec_is_empty_exact

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
