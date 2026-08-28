-- Transparent completion of the sole standard-library interface emitted by
-- Aeneas for this focused extraction.
import Aeneas
import V7ForestLaneInvariant.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

open V7ForestLaneInvariantGenerated

/-- Exact Rust `Option<T>` partial equality. This is standard-library control
flow, not a project or cryptographic assumption. -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
    {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
    Option T → Option T → Result Bool
  | none, none => .ok true
  | some left, some right => cmpPartialEqInst.eq left right
  | _, _ => .ok false
