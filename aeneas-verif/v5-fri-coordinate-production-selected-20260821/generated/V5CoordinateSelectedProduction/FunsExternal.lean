-- Combined proof view: reuse the adapter's identical global standard-library
-- semantics and add only the operations required by the direct extraction.
import Coordinates.Funs
import V5CoordinateSelectedProduction.Types

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

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
    {T E : Type} : Option T → E → Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

@[rust_fun "core::option::{core::option::Option<@T>}::and_then"]
def core.option.Option.and_then
    {T U F : Type} (fnOnce : core.ops.function.FnOnce F T (Option U)) :
    Option T → F → Result (Option U)
  | none, _ => ok none
  | some value, closure => fnOnce.call_once closure value

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible → Result (Option T)
  | none => ok none
  | some impossible => nomatch impossible

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
    {T : Type} : Option T →
      Result (core.ops.control_flow.ControlFlow
        (Option core.convert.Infallible) T)
  | none => ok (.Break none)
  | some value => ok (.Continue value)

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::from_output"]
def core.option.Option.Insts.CoreOpsTry_traitTry.from_output
    {T : Type} (value : T) : Result (Option T) :=
  ok (some value)
