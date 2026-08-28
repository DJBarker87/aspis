import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7CanonicalDeferredParser.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CanonicalDeferredParserGenerated

set_option autoImplicit false
set_option linter.dupNamespace false

/-! Transparent models of the Rust standard-library calls and frozen source
constants left external by the focused cross-crate extraction. -/

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
    {T E F O : Type} (fnOnceInst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => .ok (.Ok value)
  | .Err error, state => do
    let mapped ← fnOnceInst.call_once state error
    .ok (.Err mapped)

@[rust_const "aspis_core::v6_onefold::V6_FIXED_QM31_VALUES"]
def aspis_core.v6_onefold.V6_FIXED_QM31_VALUES : Result Std.Usize :=
  .ok 641#usize

@[rust_const "aspis_core::v6_onefold::V6_WORK_NONCE_BYTES"]
def aspis_core.v6_onefold.V6_WORK_NONCE_BYTES : Result Std.Usize :=
  .ok 24#usize

@[rust_const "aspis_core::v7_onefold::V7_COMPACT_QUERY_SECTION_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES : Result Std.Usize :=
  .ok 9936#usize

@[rust_const "aspis_core::v7_onefold::V7_COMPACT_DIGEST_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES : Result Std.Usize :=
  .ok 26#usize

@[rust_const "aspis_core::v7_onefold::V7_COMPACT_FRONTIER_CAP_PER_TREE"]
def aspis_core.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE : Result Std.Usize :=
  .ok 209#usize
