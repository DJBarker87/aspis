import Aeneas.Std
import V5OpeningParserGenerated.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_core

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
    {T : Type} {E : Type} : Option T -> E ->
      Result (core.result.Result T E)
  | some value, _ => ok (.Ok value)
  | none, error => ok (.Err error)

/-- Transparent normalization of `Result::unwrap` for the infallible
fixed-width copy-slice conversion.  Rust's debug formatter argument is unused
by `unwrap`; spelling out the two result cases avoids importing that unrelated
formatter model into the proof's trusted assumptions. -/
def state_only_private_openings.unwrap_copy_slice
    {T : Type} : core.result.Result T core.array.TryFromSliceError -> Result T
  | .Ok value => ok value
  | .Err _ => fail .panic
