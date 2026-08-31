-- Exact transparent interpretations of the Rust core-library operations left
-- outside the focused production ASQ8 reconstruction / ASR8 emission
-- extraction.  The final `set_return_data` interpretation models only
-- successful control transfer to the Solana runtime; the runtime's storage of
-- return bytes remains an explicit Solana boundary in the composition report.
import Aeneas
import V7PairForestProductionCodecs.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open V7PairForestProductionCodecsGenerated

@[rust_fun
  "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq"]
def Slice.Insts.CoreCmpPartialEqArray.eq
    {T U : Type} {N : Std.Usize}
    (partialEq : core.cmp.PartialEq T U) :
    Slice T → Array U N → Result Bool :=
  fun left right =>
    core.slice.cmp.PartialEqSlice.eq partialEq left right.to_slice

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def core.iter.traits.iterator.Iterator.any.default
    {Self F Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (fnMut : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self) :=
  fun self predicate => do
    let outcome ←
      (loop
        (fun (self', predicate') => do
          let (item, self'') ← iterator.next self'
          match item with
          | none => ok (done (false, self'', predicate'))
          | some value =>
              let (accepted, predicate'') ← fnMut.call_mut predicate' value
              if accepted then
                ok (done (true, self'', predicate''))
              else
                ok (cont (self'', predicate'')))
        (self, predicate) : Result (Bool × Self × F))
    ok (outcome.1, outcome.2.1)

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::all"]
def core.iter.traits.iterator.Iterator.all.default
    {Self F Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (fnMut : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self) :=
  fun self predicate => do
    let outcome ←
      (loop
        (fun (self', predicate') => do
          let (item, self'') ← iterator.next self'
          match item with
          | none => ok (done (true, self'', predicate'))
          | some value =>
              let (holds, predicate'') ← fnMut.call_mut predicate' value
              if holds then
                ok (cont (self'', predicate''))
              else
                ok (done (false, self'', predicate'')))
        (self, predicate) : Result (Bool × Self × F))
    ok (outcome.1, outcome.2.1)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F →
      Result (Bool × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.any.default
    (core.iter.traits.iterator.IteratorSliceIter T) fnMut

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::all"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F →
      Result (Bool × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.all.default
    (core.iter.traits.iterator.IteratorSliceIter T) fnMut

@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flatten"]
def core.iter.traits.iterator.Iterator.flatten.default
    {Self OuterItem InnerItem InnerIter : Type}
    (_iterator : core.iter.traits.iterator.Iterator Self OuterItem)
    (_intoIterator :
      core.iter.traits.collect.IntoIterator OuterItem InnerItem InnerIter) :
    Self → Result
      (core.iter.adapters.flatten.Flatten
        Self OuterItem InnerItem InnerIter) :=
  fun outer => ok { outer, inner := none }

@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::Flatten<@I, @Clause0_Item, @Clause2_Item, @U>, @Clause2_Item>}::next"]
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next
    {I U OuterItem Item : Type}
    (outerIterator : core.iter.traits.iterator.Iterator I OuterItem)
    (intoIterator :
      core.iter.traits.collect.IntoIterator OuterItem Item U)
    (innerIterator : core.iter.traits.iterator.Iterator U Item) :
    core.iter.adapters.flatten.Flatten I OuterItem Item U →
      Result
        (Option Item ×
          core.iter.adapters.flatten.Flatten I OuterItem Item U) :=
  fun initial => do
    loop
      (fun (state :
          core.iter.adapters.flatten.Flatten I OuterItem Item U) => do
        match state.inner with
        | some inner =>
            let (item, inner') ← innerIterator.next inner
            match item with
            | some value =>
                ok (done (some value, { state with inner := some inner' }))
            | none =>
                ok (cont { state with inner := none })
        | none =>
            let (outerItem, outer') ← outerIterator.next state.outer
            match outerItem with
            | none => ok (done (none, { state with outer := outer' }))
            | some value =>
                let inner ← intoIterator.into_iter value
                ok (cont { outer := outer', inner := some inner }))
      initial

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def V7PairForestCodecOptionEq
    {T : Type} (partialEq : core.cmp.PartialEq T T) :
    Option T → Option T → Result Bool
  | none, none => ok true
  | some left, some right => partialEq.eq left right
  | _, _ => ok false

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, closure => do
      let mapped ← fnOnce.call_once closure error
      ok (.Err mapped)

@[rust_const "aspis_core::field::P"]
def aspis_core.field.P : Result Std.U32 := ok 2147483647#u32

@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq"]
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
    (left right : aspis_core.field.M31) : Result Bool :=
  ok (left = right)

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::to_le_bytes"]
def aspis_core.field.M31.to_le_bytes
    (value : aspis_core.field.M31) : Result (Array Std.U8 4#usize) :=
  ok (core.num.U32.to_le_bytes value)

/-- Runtime-call projection.  This proves the translated producer reaches the
Solana return-data syscall with successfully encoded bytes; Solana's storage
of those bytes is intentionally not represented as a Lean state mutation. -/
@[rust_fun "solana_program::program::set_return_data"]
def solana_program.program.set_return_data
    (_bytes : Slice Std.U8) : Result Unit := ok ()
