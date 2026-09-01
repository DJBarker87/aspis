import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk35

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 220:29-220:35
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>}::call_once"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c :
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 220:29-220:35
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure
  Std.Usize Std.U64 := {
  call_once :=
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 220:29-220:35
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure
  Std.Usize Std.U64 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_statement::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 219:52-219:60
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>}::call_mut"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
  (c : aspis_statement.state_only_poseidon.external_local_packed_raw.closure)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U64 4#usize) ×
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure)
  := do
  let a ←
    core.array.from_fn 4#usize
      aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      (c, tupled_args)
  ok (a, c)

/-- [aspis_statement::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 219:52-219:60
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>}::call_once"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
  (c : aspis_statement.state_only_poseidon.external_local_packed_raw.closure)
  (i : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  let (a, _) ←
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
      c i
  ok a

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 219:52-219:60
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure
  Std.Usize (Array Std.U64 4#usize) := {
  call_once :=
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 219:52-219:60
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure<'0>, (usize), [u64; 4]>"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure
  Std.Usize (Array Std.U64 4#usize) := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  call_mut :=
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
}

/-- [aspis_statement::state_only_poseidon::EXTERNAL_LOCAL_LIMB_MODULUS_BOUND]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 197:0-197:44
    Name pattern: [aspis_statement::state_only_poseidon::EXTERNAL_LOCAL_LIMB_MODULUS_BOUND] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::state_only_poseidon::EXTERNAL_LOCAL_LIMB_MODULUS_BOUND"]
def aspis_statement.state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  : Result Std.U64 := do
  let i ← Aeneas.Std.lift (UScalar.cast .U64 aspis_core.field.P)
  7#u64 * i

/-- [aspis_statement::state_only_poseidon::external_local_packed_raw]: loop body 1:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 238:8-241:9
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw_loop0_loop0.body
  (local1 : Array (Array Std.U64 4#usize) 4#usize) (output : Std.Usize)
  (all_local_limbs_bounded : Bool) (limb : Std.Usize) :
  Result (ControlFlow (Bool × Std.Usize) Bool)
  := do
  if limb < 4#usize
  then
    let a ← Array.index_usize local1 output
    let i ← Array.index_usize a limb
    let i1 ←
      aspis_statement.state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
    let limb1 ← limb + 1#usize
    ok (cont (all_local_limbs_bounded && (i < i1), limb1))
  else ok (done all_local_limbs_bounded)

/-- [aspis_statement::state_only_poseidon::external_local_packed_raw]: loop 1:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 238:8-241:9
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw"]
def aspis_statement.state_only_poseidon.external_local_packed_raw_loop0_loop0
  (local1 : Array (Array Std.U64 4#usize) 4#usize)
  (all_local_limbs_bounded : Bool) (output : Std.Usize) (limb : Std.Usize) :
  Result Bool
  := do
  loop
    (fun (all_local_limbs_bounded1, limb1) =>
      aspis_statement.state_only_poseidon.external_local_packed_raw_loop0_loop0.body
      local1 output all_local_limbs_bounded1 limb1)
    (all_local_limbs_bounded, limb)

/-- [aspis_statement::state_only_poseidon::external_local_packed_raw]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 236:4-243:5
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw"]
def aspis_statement.state_only_poseidon.external_local_packed_raw_loop0.body
  (local1 : Array (Array Std.U64 4#usize) 4#usize)
  (all_local_limbs_bounded : Bool) (output : Std.Usize) :
  Result (ControlFlow (Bool × Std.Usize) Bool)
  := do
  if output < 4#usize
  then
    let all_local_limbs_bounded1 ←
      aspis_statement.state_only_poseidon.external_local_packed_raw_loop0_loop0
        local1 all_local_limbs_bounded output 0#usize
    let output1 ← output + 1#usize
    ok (cont (all_local_limbs_bounded1, output1))
  else ok (done all_local_limbs_bounded)

/-- [aspis_statement::state_only_poseidon::external_local_packed_raw]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 236:4-243:5
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw"]
def aspis_statement.state_only_poseidon.external_local_packed_raw_loop0
  (local1 : Array (Array Std.U64 4#usize) 4#usize)
  (all_local_limbs_bounded : Bool) (output : Std.Usize) :
  Result Bool
  := do
  loop
    (fun (all_local_limbs_bounded1, output1) =>
      aspis_statement.state_only_poseidon.external_local_packed_raw_loop0.body
      local1 all_local_limbs_bounded1 output1)
    (all_local_limbs_bounded, output)


end V7Tag73CurrentHelpersOpaque
