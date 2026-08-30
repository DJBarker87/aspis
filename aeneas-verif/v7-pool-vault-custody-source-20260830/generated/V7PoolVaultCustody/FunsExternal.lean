import Aeneas
import V7PoolVaultCustody.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V7PoolVaultCustodyGenerated

set_option autoImplicit false

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | .some value, _ => .ok (.Ok value)
  | .none, error => .ok (.Err error)
