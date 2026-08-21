-- Executable interpretations of the standard-library functions left opaque
-- by the pinned Aeneas extraction.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
import Prepare.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace V5RelationPrepareGenerated

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
    {T : Type} (inst : core.cmp.PartialEq T T) :
    Option T → Option T → Result Bool
  | none, none => ok true
  | some left, some right => inst.eq left right
  | _, _ => ok false

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} :
    Option T → Result (core.ops.control_flow.ControlFlow
      (Option core.convert.Infallible) T)
  | none => ok (.Break none)
  | some value => ok (.Continue value)

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible → Result (Option T)
  | none => ok none
  | some impossible => nomatch impossible

@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T E : Type} :
    core.result.Result T E → Result (Option T)
  | .Ok value => .ok (some value)
  | .Err _ => .ok none

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, closure => do
      let mapped ← inst.call_once closure error
      .ok (.Err mapped)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap_or"]
def core.result.Result.unwrap_or {T E : Type} :
    core.result.Result T E → T → Result T
  | .Ok value, _ => .ok value
  | .Err _, fallback => .ok fallback

end V5RelationPrepareGenerated
