import V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1

/-!
Executable interpretations of the deterministic Rust core operations next in
the whole-caller external inventory.  These are ordinary library semantics,
not protocol or cryptographic assumptions.
-/

@[rust_fun "core::bool::{bool}::then_some"]
def core.bool.Bool.then_some {T : Type}
    (condition : Bool) (value : T) : Result (Option T) :=
  if condition then ok (some value) else ok none

@[rust_fun "core::num::{u16}::count_ones"]
def core.num.U16.count_ones (value : Std.U16) : Result Std.U32 :=
  ok ⟨value.bv.cpop.zeroExtend 32⟩

def core.num.trailingZerosNat : Nat → Nat → Nat
  | _, 0 => 0
  | value, fuel + 1 =>
      if value % 2 = 0 then
        1 + core.num.trailingZerosNat (value / 2) fuel
      else
        0

@[rust_fun "core::num::{u16}::trailing_zeros"]
def core.num.U16.trailing_zeros (value : Std.U16) : Result Std.U32 :=
  ok ⟨BitVec.ofNat 32 (core.num.trailingZerosNat value.bv.toNat 16)⟩

def core.num.trailingOnesNat : Nat → Nat → Nat
  | _, 0 => 0
  | value, fuel + 1 =>
      if value % 2 = 1 then
        1 + core.num.trailingOnesNat (value / 2) fuel
      else
        0

@[rust_fun "core::num::{u64}::trailing_ones"]
def core.num.U64.trailing_ones (value : Std.U64) : Result Std.U32 :=
  ok ⟨BitVec.ofNat 32 (core.num.trailingOnesNat value.bv.toNat 64)⟩

@[rust_fun "core::num::{usize}::reverse_bits"]
def core.num.Usize.reverse_bits (value : Std.Usize) : Result Std.Usize :=
  ok ⟨value.bv.reverse⟩

@[rust_fun "core::num::{usize}::checked_shl"]
def core.num.Usize.checked_shl
    (value : Std.Usize) (shift : Std.U32) : Result (Option Std.Usize) :=
  if shift.val < System.Platform.numBits then
    ok (some ⟨value.bv.shiftLeft shift.val⟩)
  else
    ok none

@[rust_fun "core::num::{u32}::checked_shl"]
def core.num.U32.checked_shl
    (value shift : Std.U32) : Result (Option Std.U32) :=
  if shift.val < 32 then
    ok (some ⟨value.bv.shiftLeft shift.val⟩)
  else
    ok none

@[rust_fun "core::num::{u32}::is_power_of_two"]
def core.num.U32.is_power_of_two (value : Std.U32) : Result Bool :=
  ok value.val.isPowerOfTwo

@[rust_fun "core::option::{core::option::Option<@T>}::as_ref"]
def core.option.Option.as_ref {T : Type}
    (value : Option T) : Result (Option T) :=
  ok value

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type}
    (value : Option T) (error : E) :
    Result (core.result.Result T E) :=
  match value with
  | some present => ok (.Ok present)
  | none => ok (.Err error)

@[rust_fun "core::slice::{[@T]}::first"]
def core.slice.Slice.first {T : Type}
    (value : Slice T) : Result (Option T) :=
  ok value.val.head?

@[rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type}
    (value : Slice T) : Result (Option T) :=
  ok value.val.getLast?

@[rust_fun
  "core::ops::range::{core::clone::Clone<core::ops::range::Range<@Idx>>}::clone"]
def core.ops.range.Range.Insts.CoreCloneClone.clone
    {Idx : Type} (cloneInst : core.clone.Clone Idx)
    (range : core.ops.range.Range Idx) :
    Result (core.ops.range.Range Idx) := do
  let start ← cloneInst.clone range.start
  let «end» ← cloneInst.clone range.«end»
  ok { start, «end» }

@[rust_fun "core::option::{core::option::Option<@T>}::is_some_and"]
def core.option.Option.is_some_and
    {T T1 : Type} (fnOnce : core.ops.function.FnOnce T1 T Bool) :
    Option T → T1 → Result Bool
  | none, _ => ok false
  | some value, closure => fnOnce.call_once closure value

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
    {T : Type} (partialEq : core.cmp.PartialEq T T) :
    Option T → Option T → Result Bool
  | none, none => ok true
  | some left, some right => partialEq.eq left right
  | _, _ => ok false

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} :
    Option T → Result
      (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  | some value => ok (.Continue value)
  | none => ok (.Break none)

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible → Result (Option T)
  | none => ok none
  | some impossible => nomatch impossible

@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_ok_and"]
def core.result.Result.is_ok_and
    {T E F : Type} (fnOnce : core.ops.function.FnOnce F T Bool) :
    core.result.Result T E → F → Result Bool
  | .Ok value, closure => fnOnce.call_once closure value
  | .Err _, _ => ok false

@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T E : Type} :
    core.result.Result T E → Result (Option T)
  | .Ok value => .ok (some value)
  | .Err _ => .ok none

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map
    {T E U F : Type} (fnOnce : core.ops.function.FnOnce F T U) :
    core.result.Result T E → F → Result (core.result.Result U E)
  | .Ok value, closure => do
      let mapped ← fnOnce.call_once closure value
      .ok (.Ok mapped)
  | .Err error, _ => .ok (.Err error)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, closure => do
      let mapped ← fnOnce.call_once closure error
      .ok (.Err mapped)

@[rust_fun "alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref"]
def Box.Insts.CoreConvertAsRef.as_ref
    {T : Type} (_allocator : Type) (value : T) : Result T :=
  .ok value

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::into_boxed_slice"]
def alloc.vec.Vec.into_boxed_slice
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T) :
    Result (Slice T) :=
  .ok ⟨value.val, value.property⟩

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::truncate"]
def alloc.vec.Vec.truncate
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T)
    (length : Std.Usize) : Result (alloc.vec.Vec T) :=
  .ok ⟨value.val.take length.val,
    Nat.le_trans (List.length_take_le' ..) value.property⟩

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T)
    (index : Std.Usize) : Result (T × alloc.vec.Vec T) :=
  if h : index.val < value.val.length then
    .ok (value.val[index.val],
      ⟨value.val.eraseIdx index.val,
        Nat.le_trans (List.length_eraseIdx_le ..) value.property⟩)
  else
    .fail .arrayOutOfBounds

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"]
def alloc.vec.Vec.clear
    {T : Type} (_allocator : Type) (_value : alloc.vec.Vec T) :
    Result (alloc.vec.Vec T) :=
  .ok (alloc.vec.Vec.new T)

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def alloc.vec.Vec.is_empty
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T) : Result Bool :=
  .ok value.val.isEmpty

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
