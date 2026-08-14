import Aeneas.Std
import V5TopologyReadsGenerated.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_core

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
    {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
    Option T → Option T → Result Bool
  | none, none => ok true
  | some left, some right => cmpPartialEqInst.eq left right
  | _, _ => ok false
