-- Exact transparent interpretations of the Rust core-library functions left
-- external by the V7 deferred-parser Charon extraction.
import Aeneas
import V7DeferredParser.Types

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open V7DeferredParserGenerated

@[rust_fun "core::option::{core::option::Option<@T>}::unwrap_or_default"]
def core.option.Option.unwrap_or_default
    {T : Type} (defaultDefaultInst : core.default.Default T) :
    Option T → Result T
  | some value => ok value
  | none => defaultDefaultInst.default

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
    {T E : Type} : Option T → E → Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

@[rust_fun "core::option::{core::option::Option<&'0 @T>}::copied"]
def core.option.OptionShared0T.copied
    {T : Type} (markerCopyInst : core.marker.Copy T) :
    Option T → Result (Option T) :=
  fun value =>
    let _ := markerCopyInst
    ok value

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (function : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, state => do
      let mapped ← function.call_once state error
      ok (.Err mapped)

@[rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type} : Slice T → Result (Option T) :=
  fun slice => ok slice.val.getLast?
