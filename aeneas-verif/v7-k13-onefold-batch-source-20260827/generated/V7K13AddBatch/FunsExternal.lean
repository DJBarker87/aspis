import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7K13AddBatch.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V7K13AddBatchGenerated

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 4096

/-!
Executable interpretations of the Rust standard-library operations left
external by the focused extraction.  These are generic library models, not
Aspis protocol premises.
-/

@[rust_fun
  "core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter"]
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T : Type} {N : Std.Usize} (array : Array T N) :
    Result (core.array.iter.IntoIter T N) :=
  .ok { array := array }

@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    {T : Type} {N : Std.Usize}
    (iterator : core.array.iter.IntoIter T N) :
    Result (Option T × core.array.iter.IntoIter T N) :=
  if h : iterator.index < iterator.array.val.length then
    .ok (some iterator.array.val[iterator.index],
      { iterator with index := iterator.index + 1 })
  else
    .ok (none, iterator)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def core.iter.traits.iterator.Iterator.any.default
    {Self F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (fnMutInst : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self) :=
  fun iterator closure => do
    let result : Bool × Self × F ← loop
      (fun (iterator, closure) => do
        let (item, iterator) ← iteratorInst.next iterator
        match item with
        | none => .ok (.done (false, iterator, closure))
        | some value => do
          let (found, closure) ← fnMutInst.call_mut closure value
          if found then
            .ok (.done (true, iterator, closure))
          else
            .ok (.cont (iterator, closure)))
      (iterator, closure)
    .ok (result.1, result.2.1)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (fnOnceInst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, state => do
    let mapped ← fnOnceInst.call_once state error
    .ok (.Err mapped)

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

namespace V7K13AddBatchExternal

def insertByOrd {T : Type} (ord : core.cmp.Ord T) (value : T) :
    List T → Result (List T)
  | [] => .ok [value]
  | head :: tail => do
    let ordering ← ord.cmp value head
    match ordering with
    | .lt => .ok (value :: head :: tail)
    | .eq => do
      let rest ← insertByOrd ord value tail
      .ok (head :: rest)
    | .gt => do
      let rest ← insertByOrd ord value tail
      .ok (head :: rest)

def sortList {T : Type} (ord : core.cmp.Ord T) :
    List T → Result (List T)
  | [] => .ok []
  | head :: tail => do
    let sortedTail ← sortList ord tail
    insertByOrd ord head sortedTail

def checkedSlice {T : Type} (values : List T) : Result (Slice T) :=
  if h : values.length ≤ Usize.max then .ok ⟨values, h⟩
  else .fail .panic

end V7K13AddBatchExternal

@[rust_fun "core::slice::{[@T]}::sort_unstable"]
def core.slice.Slice.sort_unstable {T : Type} (ord : core.cmp.Ord T) :
    Slice T → Result (Slice T)
  | slice => do
    let values ← V7K13AddBatchExternal.sortList ord slice.val
    V7K13AddBatchExternal.checkedSlice values
