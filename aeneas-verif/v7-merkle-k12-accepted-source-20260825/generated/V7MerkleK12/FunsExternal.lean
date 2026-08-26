-- Handwritten executable interpretations of the five Rust-library calls
-- left external by the focused Charon extraction.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7MerkleK12.Types
open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open V7MerkleK12Generated

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def core.iter.traits.iterator.Iterator.any.default
  {Self : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBoolInst : core.ops.function.FnMut F
  Clause0_Item Bool) :
  Self → F → Result (Bool × Self) :=
  fun self predicate => do
    let result : Result (Bool × Self × F) :=
      loop
        (fun (self', predicate') => do
          let (item, self'') ← IteratorInst.next self'
          match item with
          | none => ok (done (false, self'', predicate'))
          | some item' =>
            let (isMatch, predicate'') ←
              opsfunctionFnMutFTupleClause0_ItemBoolInst.call_mut
                predicate' item'
            if isMatch then
              ok (done (true, self'', predicate''))
            else
              ok (cont (self'', predicate'')))
        (self, predicate)
    let (found, self', _) ←
      result
    ok (found, self')

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
    {T : Type} : core.slice.iter.Windows T →
      Result (Option (Slice T) × core.slice.iter.Windows T) :=
  fun self =>
    if self.index + self.width.val ≤ self.slice.val.length then
      ok (some (core.slice.iter.Windows.windowAt
          self.slice self.index self.width.val),
        { self with index := self.index + 1 })
    else
      ok (none, self)

@[rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type} : Slice T → Result (Option T) :=
  fun slice => ok slice.val.getLast?

@[rust_fun "core::slice::{[@T]}::windows"]
def core.slice.Slice.windows {T : Type} :
    Slice T → Std.Usize → Result (core.slice.iter.Windows T) :=
  fun slice width =>
    if width = 0#usize then fail .panic
    else ok { slice, width, index := 0 }

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"]
def alloc.vec.Vec.clear {T : Type} (A : Type) (_ : alloc.vec.Vec T) :
    Result (alloc.vec.Vec T) :=
  let _ := A
  ok (alloc.vec.Vec.new T)
