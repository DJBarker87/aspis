import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import AuthorizationReceiptEncoder.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open AuthorizationReceiptEncoderGenerated

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AuthorizationReceiptEncoderGenerated

def core.slice.iter.Iter.allAux
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    Nat → core.slice.iter.Iter T → F →
      Result (Bool × core.slice.iter.Iter T × F)
  | 0, iter, state => ok (true, iter, state)
  | fuel + 1, iter, state => do
      let (item, next) ← core.slice.iter.IteratorSliceIter.next iter
      match item with
      | none => ok (true, next, state)
      | some value =>
          let (accepted, state') ← fnMut.call_mut state value
          if accepted then core.slice.iter.Iter.allAux fnMut fuel next state'
          else ok (false, next, state')

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::all"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T)
  | iter, state => do
      let (accepted, next, _) ←
        core.slice.iter.Iter.allAux fnMut (iter.slice.len - iter.i + 1)
          iter state
      ok (accepted, next)

@[rust_const "aspis_core::field::P"]
def aspis_core.field.P : Result Std.U32 := ok 2147483647#u32

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::to_le_bytes"]
def aspis_core.field.M31.to_le_bytes
    (value : aspis_core.field.M31) : Result (Array Std.U8 4#usize) :=
  ok (core.num.U32.to_le_bytes value)

end AuthorizationReceiptEncoderGenerated
