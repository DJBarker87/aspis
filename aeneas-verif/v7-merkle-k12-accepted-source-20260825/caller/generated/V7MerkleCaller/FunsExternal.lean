-- Executable interpretations of the Rust-library operations left external by
-- the transparent caller extraction.  These are definitions, not semantic
-- axioms.  The array/window/option/result/Vec models are reused from existing
-- source bundles; the exact emitted signatures for from_fn, mutable any, and
-- sort_unstable_by_key are executable adaptations of the same models.
import V7MerkleK12.FunsExternal
import V7MerkleCaller.Types
open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open V7MerkleCallerGenerated

/-- Type-correct shared-trait view of mutable iteration.  Direct translated
uses retain `IteratorIterMut.next` and its write-back function; this view is
used only by Rust's generic `Iterator` trait record. -/
def core.slice.iter.IteratorIterMut.next_without_writeback
    {T : Type} (iter : core.slice.iter.IterMut T) :
    Result (Option T × core.slice.iter.IterMut T) := do
  let (value, next, _) ← core.slice.iter.IteratorIterMut.next iter
  .ok (value, next)

/-- Forward/backward `Enumerate<IterMut<T>>::next`, preserving assignment to
the yielded mutable slot through Aeneas's write-back function. -/
def core.iter.adapters.enumerate.IteratorEnumerateMut.next
    {T : Type}
    (self : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut T)) :
    Result
      (Option (Std.Usize × T) ×
        core.iter.adapters.enumerate.Enumerate
          (core.slice.iter.IterMut T) ×
        (core.iter.adapters.enumerate.Enumerate
            (core.slice.iter.IterMut T) →
          Option (Std.Usize × T) →
          core.iter.adapters.enumerate.Enumerate
            (core.slice.iter.IterMut T))) := do
  let (value, nextIter, writeBack) ←
    core.slice.iter.IteratorIterMut.next self.iter
  let nextSelf := { self with iter := nextIter }
  match value with
  | none =>
      .ok (none, nextSelf,
        fun current replacement =>
          { current with
            iter := writeBack current.iter (replacement.map Prod.snd) })
  | some item => do
      let nextCount ← self.count + 1#usize
      .ok (some (self.count, item), { nextSelf with count := nextCount },
        fun current replacement =>
          { current with
            iter := writeBack current.iter (replacement.map Prod.snd) })

/-- Forward/backward construction of mutable enumeration. -/
def core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate
    {T : Type} (iter : core.slice.iter.IterMut T) :
    Result
      (core.iter.adapters.enumerate.Enumerate
          (core.slice.iter.IterMut T) ×
        (core.iter.adapters.enumerate.Enumerate
            (core.slice.iter.IterMut T) →
          core.slice.iter.IterMut T)) :=
  .ok ({ iter := iter, count := 0#usize }, fun current => current.iter)

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

namespace V7MerkleCallerExternal

/-- Build the values for `array::from_fn`, threading the Rust `FnMut` state.
The final closure state is deliberately discarded because that is the exact
signature emitted for the production call. -/
def fromFnList
    {T F : Type} (fnMut : core.ops.function.FnMut F Std.Usize T) :
    Nat → Std.Usize → F → Result (List T)
  | 0, _, _ => .ok []
  | remaining + 1, index, closure => do
      let (value, closure) ← fnMut.call_mut closure index
      let nextIndex ← index + 1#usize
      let tail ← fromFnList fnMut remaining nextIndex closure
      .ok (value :: tail)

end V7MerkleCallerExternal

@[rust_fun "core::array::from_fn"]
def core.array.from_fn
    {T F : Type} (N : Std.Usize)
    (fnMut : core.ops.function.FnMut F Std.Usize T) :
    F → Result (Array T N)
  | closure => do
      let values ←
        V7MerkleCallerExternal.fromFnList fnMut N.val 0#usize closure
      dite (values.length = N.val)
        (fun h => .ok ⟨values, h⟩)
        (fun _ => .fail .panic)

@[rust_fun
  "core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N], &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"]
def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} {N : Std.Usize} (array : Array T N) :
    Result (core.slice.iter.IterMut T ×
      (core.slice.iter.IterMut T → Array T N)) :=
  .ok ({ slice := Array.to_slice array },
    fun iterator => Array.from_slice array iterator.slice)

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} :
    Option T → Result
      (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  | some value => .ok (.Continue value)
  | none => .ok (.Break none)

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible → Result (Option T)
  | none => .ok none
  | some impossible => nomatch impossible

@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T E : Type} :
    core.result.Result T E → Result (Option T)
  | .Ok value => .ok (some value)
  | .Err _ => .ok none

namespace V7MerkleCallerExternal

/-- Executable mutable-slice `any`, including reinsertion through the Aeneas
mutable-item back function. -/
def iterMutAnyAux
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    Nat → core.slice.iter.IterMut T → F →
      Result (Bool × core.slice.iter.IterMut T × F)
  | 0, iterator, closure => .ok (false, iterator, closure)
  | fuel + 1, iterator, closure => do
      let (item, next, itemBack) ← core.slice.iter.IteratorIterMut.next iterator
      let next := itemBack next item
      match item with
      | none => .ok (false, next, closure)
      | some value =>
          let (isMatch, closure) ← fnMut.call_mut closure value
          if isMatch then
            .ok (true, next, closure)
          else
            iterMutAnyAux fnMut fuel next closure

end V7MerkleCallerExternal

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::any"]
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.IterMut T → F →
      Result (Bool × core.slice.iter.IterMut T ×
        (core.slice.iter.IterMut T → core.slice.iter.IterMut T))
  | iterator, closure => do
      let fuel := iterator.slice.val.length - iterator.i + 1
      let (found, iterator, _) ←
        V7MerkleCallerExternal.iterMutAnyAux fnMut fuel iterator closure
      .ok (found, iterator, fun updated => updated)

namespace V7MerkleCallerExternal

/-- Monadic insertion by the supplied Rust key closure and `Ord` instance. -/
def insertByKey
    {T K F : Type} (fnMut : core.ops.function.FnMut F T K)
    (ord : core.cmp.Ord K) (value : T) :
    List T → F → Result (List T × F)
  | [], closure => .ok ([value], closure)
  | head :: tail, closure => do
      let (valueKey, closure) ← fnMut.call_mut closure value
      let (headKey, closure) ← fnMut.call_mut closure head
      let ordering ← ord.cmp valueKey headKey
      match ordering with
      | .lt => .ok (value :: head :: tail, closure)
      | .eq =>
          let (rest, closure) ← insertByKey fnMut ord value tail closure
          .ok (head :: rest, closure)
      | .gt =>
          let (rest, closure) ← insertByKey fnMut ord value tail closure
          .ok (head :: rest, closure)

/-- Executable unstable sort model.  Its order among equal keys is deliberately
unspecified by the Rust contract; this insertion implementation chooses one
such order while preserving all elements. -/
def sortListByKey
    {T K F : Type} (fnMut : core.ops.function.FnMut F T K)
    (ord : core.cmp.Ord K) : List T → F → Result (List T × F)
  | [], closure => .ok ([], closure)
  | head :: tail, closure => do
      let (sortedTail, closure) ← sortListByKey fnMut ord tail closure
      insertByKey fnMut ord head sortedTail closure

end V7MerkleCallerExternal

@[rust_fun "core::slice::{[@T]}::sort_unstable_by_key"]
def core.slice.Slice.sort_unstable_by_key
    {T K F : Type} (fnMut : core.ops.function.FnMut F T K)
    (ord : core.cmp.Ord K) : Slice T → F → Result (Slice T)
  | slice, closure => do
      let (values, _) ←
        V7MerkleCallerExternal.sortListByKey fnMut ord slice.val closure
      dite (values.length ≤ Usize.max)
        (fun h => .ok ⟨values, h⟩)
        (fun _ => .fail .panic)
