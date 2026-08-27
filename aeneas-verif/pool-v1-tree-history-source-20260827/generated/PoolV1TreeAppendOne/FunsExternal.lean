import Aeneas
import PoolV1TreeAppendOne.Types

/-!
Transparent standard-library and scalar interpretations for the focused Pool
V1 one-append extraction. Poseidon remains the sole deliberately opaque
cryptographic primitive.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1TreeAppendOneGenerated

set_option autoImplicit false

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map
    {T E U F : Type} (function : core.ops.function.FnOnce F T U) :
    core.result.Result T E → F → Result (core.result.Result U E)
  | .Ok value, state => do
      let mapped ← function.call_once state value
      .ok (.Ok mapped)
  | .Err error, _ => .ok (.Err error)

@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq"]
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
    (self other : aspis_core.field.M31) : Result Bool :=
  .ok (self = other)

@[rust_const "aspis_core::field::{aspis_core::field::M31}::ZERO"]
def aspis_core.field.M31.ZERO : Result aspis_core.field.M31 :=
  .ok 0#u32

@[rust_const "aspis_statement::pool_v1::format::POOL_V1_TREE_DEPTH"]
def aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH : Result Std.Usize :=
  .ok 20#usize

/-- Exact boundary deliberately excluded from this implementation lane: the
deployed Poseidon/M31 parent compression primitive. -/
@[rust_fun "aspis_statement::pool_v1::format::pool_v1_tree_parent"]
opaque aspis_statement.pool_v1.format.pool_v1_tree_parent :
  Array aspis_core.field.M31 8#usize →
    Array aspis_core.field.M31 8#usize →
      Result (Array aspis_core.field.M31 8#usize)
