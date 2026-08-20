import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V5FriDecoderReference.Types

open Aeneas Aeneas.Std Result ControlFlow Error
namespace V5FriDecoderReference

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
    {T E : Type} : Option T -> E -> Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
    {T : Type} : Option T ->
      Result (core.ops.control_flow.ControlFlow
        (Option core.convert.Infallible) T)
  | none => ok (.Break none)
  | some value => ok (.Continue value)

@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible -> Result (Option T)
  | none => ok none
  | some impossible => nomatch impossible

@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok
    {T E : Type} : core.result.Result T E -> Result (Option T)
  | .Ok value => Aeneas.Std.Result.ok (some value)
  | .Err _ => Aeneas.Std.Result.ok none

@[rust_const "aspis_core::circle_query::CIRCLE_QUERY_QM31_BYTES"]
def aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES :
    Result Std.Usize :=
  ok 16#usize

end V5FriDecoderReference
