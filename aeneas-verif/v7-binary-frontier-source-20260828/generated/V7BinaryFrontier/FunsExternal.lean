import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7BinaryFrontier.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V7BinaryFrontierSource

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 4096

/-!
Executable interpretations of the four Rust standard-library operations left
external by the focused `binary_frontier_nodes` extraction.  These are generic
library models rather than Aspis protocol assumptions.
-/

@[rust_fun "core::num::{u32}::checked_shl"]
def core.num.U32.checked_shl
    (value shift : Std.U32) : Result (Option Std.U32) :=
  if shift.val < 32 then
    .ok (some ⟨value.bv.shiftLeft shift.val⟩)
  else
    .ok none

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

def core.slice.iter.Windows.windowAt {T : Type}
    (slice : Slice T) (index width : Nat) : Slice T :=
  ⟨(slice.val.drop index).take width, by
    calc
      ((slice.val.drop index).take width).length ≤
          (slice.val.drop index).length := List.length_take_le' _ _
      _ = slice.val.length - index := List.length_drop
      _ ≤ slice.val.length := Nat.sub_le _ _
      _ ≤ Usize.max := slice.property⟩

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Windows<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    {T : Type} (iterator : core.slice.iter.Windows T) :
    Result (Option (Slice T) × core.slice.iter.Windows T) :=
  if iterator.index + iterator.width.val ≤ iterator.slice.val.length then
    .ok (some (core.slice.iter.Windows.windowAt iterator.slice iterator.index
      iterator.width.val), { iterator with index := iterator.index + 1 })
  else
    .ok (none, iterator)

@[rust_fun "core::slice::{[@T]}::windows"]
def core.slice.Slice.windows {T : Type} :
    Slice T → Std.Usize → Result (core.slice.iter.Windows T)
  | slice, width =>
    if width = 0#usize then .fail .panic
    else .ok { slice := slice, width := width, index := 0 }
