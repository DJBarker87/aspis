import Aeneas
import PoolV1SourceStateResultImage.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1SourceStateResultImage

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::ne"]
def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Std.Usize} (partialEq : core.cmp.PartialEq T U) :
    Slice T → Array U N → Result Bool :=
  fun slice array =>
    core.slice.cmp.PartialEqSlice.ne partialEq slice (Array.to_slice array)

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (mapper : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, closure => do
      let mapped ← mapper.call_once closure error
      .ok (.Err mapped)

/-!
The canonical digest encoder is independently source-closed by the focused
Pool history codec round-trip bridge.  This literal byte-gate extraction uses
the exact production symbol at that already-audited interface.
-/
@[rust_fun "aspis_statement::atomic_statement::encode_digest_canonical"]
axiom aspis_statement.atomic_statement.encode_digest_canonical :
  Array aspis_core.field.M31 8#usize → Result (Array Std.U8 32#usize)
