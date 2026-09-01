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

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
