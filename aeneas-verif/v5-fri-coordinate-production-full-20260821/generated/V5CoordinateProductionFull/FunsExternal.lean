import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
import V5CoordinateSelectedProduction.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section

namespace V5CoordinateSelectedProductionSource

/-! Exact models of the standard-library operations reached by the unchanged
production coordinate function.  The source function calls `array::from_fn`
only at length three; its model deliberately rejects every other length. -/

@[rust_type "core::array::iter::IntoIter"]
structure core.array.iter.IntoIter (T : Type) (N : Std.Usize) where
  array : Array T N
  index : Nat := 0

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
    Result ((Option T) × core.array.iter.IntoIter T N) :=
  if h : iterator.index < iterator.array.val.length then
    .ok (some iterator.array.val[iterator.index],
      { iterator with index := iterator.index + 1 })
  else
    .ok (none, iterator)

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>"]
impl_def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
    (T : Type) (N : Std.Usize) :
    core.iter.traits.iterator.Iterator (core.array.iter.IntoIter T N) T := {
  next := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N)
}

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>"]
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
    (T : Type) (N : Std.Usize) :
    core.iter.traits.collect.IntoIterator (Array T N) T
      (core.array.iter.IntoIter T N) := {
  iteratorInst :=
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N
  into_iter := Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
}

@[rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.default
    {Self B F Item : Type}
    (_iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (_fnMutInst : core.ops.function.FnMut F Item B) :
    Self → F → Result (core.iter.adapters.map.Map Self F)
  | iterator, closure => .ok ⟨iterator, closure⟩

@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
    {B I F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator I Item)
    (fnMutInst : core.ops.function.FnMut F Item B)
    (state : core.iter.adapters.map.Map I F) :
    Result ((Option B) × core.iter.adapters.map.Map I F) := do
  let (item, iterator) ← iteratorInst.next state.iter
  match item with
  | none => .ok (none, ⟨iterator, state.f⟩)
  | some value =>
    let (mapped, closure) ← fnMutInst.call_mut state.f value
    .ok (some mapped, ⟨iterator, closure⟩)

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>"]
impl_def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    {B I F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator I Item)
    (fnMutInst : core.ops.function.FnMut F Item B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B := {
  next :=
    core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
      iteratorInst fnMutInst
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
      iteratorInst fnMutInst)
}

@[trait_default, rust_fun
  "core::iter::traits::iterator::Iterator::try_fold"]
def core.iter.traits.iterator.Iterator.try_fold.default
    {Self B F R Item Residual : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (fnMutInst : core.ops.function.FnMut F (B × Item) R)
    (tryInst : core.ops.try_trait.Try R B Residual) :
    Self → B → F → Result (R × Self)
  | iterator, accumulator, closure =>
    loop
      (fun (iterator, accumulator, closure) => do
        let (item, iterator) ← iteratorInst.next iterator
        match item with
        | none =>
          let result ← tryInst.from_output accumulator
          .ok (.done (result, iterator))
        | some value =>
          let (result, closure) ←
            fnMutInst.call_mut closure (accumulator, value)
          let branch ← tryInst.branch result
          match branch with
          | .Continue accumulator =>
            .ok (.cont (iterator, accumulator, closure))
          | .Break residual =>
            let result ← tryInst.FromResidualInst.from_residual residual
            .ok (.done (result, iterator)))
      (iterator, accumulator, closure)

@[rust_fun "core::array::from_fn"]
def core.array.from_fn
    {T F : Type} (N : Std.Usize)
    (fnMutInst : core.ops.function.FnMut F Std.Usize T) :
    F → Result ((Array T N) × F)
  | closure => do
    if hN : N = 3#usize then
      let (v0, closure) ← fnMutInst.call_mut closure 0#usize
      let (v1, closure) ← fnMutInst.call_mut closure 1#usize
      let (v2, closure) ← fnMutInst.call_mut closure 2#usize
      let output : Array T N :=
        hN.symm ▸ (Array.make 3#usize [v0, v1, v2] : Array T 3#usize)
      .ok (output, closure)
    else
      .fail .panic

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T) :
    Result (core.slice.iter.Iter T) :=
  .ok { slice := ⟨value.val, value.property⟩, i := 0 }

end V5CoordinateSelectedProductionSource
