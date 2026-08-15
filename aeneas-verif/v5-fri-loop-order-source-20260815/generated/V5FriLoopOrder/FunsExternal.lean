import Aeneas.Std
import V5FriLoopOrder.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V5FriLoopOrderGenerated

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
    {T : Type} {E : Type} : Option T -> E ->
      Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

@[rust_fun "core::option::{core::option::Option<&'0 @T>}::copied"]
def core.option.OptionShared0T.copied
    {T : Type} (_markerCopyInst : core.marker.Copy T) :
      Option T -> Result (Option T)
  | value => ok value

@[rust_fun
  "core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
    {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
      Option T -> Option T -> Result Bool
  | none, none => ok true
  | some left, some right => cmpPartialEqInst.eq left right
  | _, _ => ok false

@[rust_fun
  "core::option::{impl core::ops::try_trait::Try for core::option::Option<T>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
    {T : Type} : Option T ->
      Result (core.ops.control_flow.ControlFlow
        (Option core.convert.Infallible) T)
  | none => ok (.Break none)
  | some value => ok (.Continue value)

@[rust_fun
  "core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<core::convert::Infallible>> for core::option::Option<T>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) : Option core.convert.Infallible -> Result (Option T)
  | none => ok none
  | some impossible => nomatch impossible

@[rust_const
  "aspis_core::state_only_private_merkle::STATE_ONLY_PRIVATE_LEAF_SALT_BYTES"]
def aspis_core.state_only_private_merkle.STATE_ONLY_PRIVATE_LEAF_SALT_BYTES :
    Result Std.Usize :=
  ok 32#usize
