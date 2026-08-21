-- Combined proof view: reuse the adapter's identical global standard-library
-- semantics and add only the operations required by the direct extraction.
import Coordinates.Funs
import V5CoordinateSelectedProduction.Types
import RelationLinked.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

@[rust_fun "core::num::{usize}::checked_shl"]
def core.num.Usize.checked_shl
    (value : Std.Usize) (shift : Std.U32) : Result (Option Std.Usize) :=
  if shift.val < System.Platform.numBits then
    ok (some ⟨value.bv.shiftLeft shift.val⟩)
  else
    ok none

@[rust_fun "core::option::{core::option::Option<@T>}::and_then"]
def core.option.Option.and_then
    {T U F : Type} (fnOnce : core.ops.function.FnOnce F T (Option U)) :
    Option T → F → Result (Option U)
  | none, _ => ok none
  | some value, closure => fnOnce.call_once closure value

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::from_output"]
def core.option.Option.Insts.CoreOpsTry_traitTry.from_output
    {T : Type} (value : T) : Result (Option T) :=
  ok (some value)
