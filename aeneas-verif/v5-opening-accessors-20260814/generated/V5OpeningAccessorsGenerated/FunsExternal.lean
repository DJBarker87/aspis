import Aeneas.Std
import V5OpeningAccessorsGenerated.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_core

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
