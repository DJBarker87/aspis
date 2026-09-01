import V7Tag73CurrentHelpersOpaque.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error

@[rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.default
    {Self B F Item : Type}
    (_iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (_fnMutInst : core.ops.function.FnMut F Item B) :
    Self → F → Result (core.iter.adapters.map.Map Self F)
  | iterator, closure => .ok ⟨iterator, closure⟩

@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::fold"]
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
    {I Acc F Item : Type}
    (doubleEndedIteratorInst :
      core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (fnMutInst : core.ops.function.FnMut F (Acc × Item) Acc)
    (iterator : core.iter.adapters.rev.Rev I) (accumulator : Acc)
    (closure : F) : Result Acc := do
  let result : Acc × core.iter.adapters.rev.Rev I × F ←
    loop
      (fun (acc, state, closureState) => do
        let (item, innerNext) ←
          doubleEndedIteratorInst.next_back state.iter
        match item with
        | none => .ok (.done (acc, ⟨innerNext⟩, closureState))
        | some value =>
          let (accNext, closureNext) ←
            fnMutInst.call_mut closureState (acc, value)
          .ok (.cont (accNext, ⟨innerNext⟩, closureNext)))
      (accumulator, iterator, closure)
  .ok result.1

@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, @A>}::fold"]
def core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold
    {A Acc F : Type} (stepInst : core.iter.range.Step A)
    (fnMutInst : core.ops.function.FnMut F (Acc × A) Acc)
    (iterator : core.ops.range.RangeInclusive A) (accumulator : Acc)
    (closure : F) : Result Acc := do
  let result : Acc × core.ops.range.RangeInclusive A × F ←
    loop
      (fun (acc, state, closureState) => do
        let (item, stateNext) ←
          core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
            stepInst state
        match item with
        | none => .ok (.done (acc, stateNext, closureState))
        | some value =>
          let (accNext, closureNext) ←
            fnMutInst.call_mut closureState (acc, value)
          .ok (.cont (accNext, stateNext, closureNext)))
      (accumulator, iterator, closure)
  .ok result.1
