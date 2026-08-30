import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk32

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 320:61-320:67
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>}::call_mut"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1)
  := do
  let (a, a1) := c
  let i ← Array.index_usize a tupled_args
  let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i2 ← i + i1
  let i3 ← Array.index_usize a1 tupled_args
  let i4 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i3)
  let i5 ← i2 - i4
  ok (i5, c)

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 320:61-320:67
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>}::call_once"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 320:61-320:67
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1 Std.Usize
  Std.U64 := {
  call_once :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 320:61-320:67
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#1<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1 Std.Usize
  Std.U64 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 319:29-319:35
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>}::call_mut"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : aspis_statement.state_only_poseidon.internal_linear_lazy.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure)
  := do
  let (a, a1) := c
  let i ← Array.index_usize a tupled_args
  let i1 ← Array.index_usize a1 tupled_args
  let i2 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i1)
  let i3 ← i + i2
  ok (i3, c)

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 319:29-319:35
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>}::call_once"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : aspis_statement.state_only_poseidon.internal_linear_lazy.closure)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 319:29-319:35
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure Std.Usize
  Std.U64 := {
  call_once :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 319:29-319:35
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure Std.Usize
  Std.U64 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_statement::state_only_poseidon::extension_from_raw_limbs]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 135:0-135:52
    Name pattern: [aspis_statement::state_only_poseidon::extension_from_raw_limbs] -/
@[rust_fun "aspis_statement::state_only_poseidon::extension_from_raw_limbs"]
def aspis_statement.state_only_poseidon.extension_from_raw_limbs
  (limbs : Array Std.U64 4#usize) : Result aspis_core.field.QM31 := do
  let i ← Array.index_usize limbs 0#usize
  let m ← aspis_core.field.M31.reduce_u62 i
  let i1 ← Array.index_usize limbs 1#usize
  let m1 ← aspis_core.field.M31.reduce_u62 i1
  let c ← aspis_core.field.CM31.new m m1
  let i2 ← Array.index_usize limbs 2#usize
  let m2 ← aspis_core.field.M31.reduce_u62 i2
  let i3 ← Array.index_usize limbs 3#usize
  let m3 ← aspis_core.field.M31.reduce_u62 i3
  let c1 ← aspis_core.field.CM31.new m2 m3
  ok { c0 := c, c1 }

/-- [aspis_statement::state_only_poseidon::extension_limbs]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 130:0-130:43
    Name pattern: [aspis_statement::state_only_poseidon::extension_limbs] -/
@[rust_fun "aspis_statement::state_only_poseidon::extension_limbs"]
def aspis_statement.state_only_poseidon.extension_limbs
  (value : aspis_core.field.QM31) : Result (Array Std.U32 4#usize) := do
  let i := value.c0.a
  let i1 := value.c0.b
  let i2 := value.c1.a
  let i3 := value.c1.b
  ok (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [aspis_statement::poseidon2::POSEIDON2_WIDTH]
    Source: 'crates/aspis-statement/src/poseidon2.rs', lines 56:0-56:32
    Name pattern: [aspis_statement::poseidon2::POSEIDON2_WIDTH]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_statement::poseidon2::POSEIDON2_WIDTH"]
def aspis_statement.poseidon2.POSEIDON2_WIDTH : Std.Usize := 16#usize

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy]: loop body 1:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 312:8-315:9
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy"]
def aspis_statement.state_only_poseidon.internal_linear_lazy_loop0_loop0.body
  (limbs : Array Std.U32 4#usize) (part_sum : Array Std.U64 4#usize)
  (limb : Std.Usize) :
  Result (ControlFlow ((Array Std.U64 4#usize) × Std.Usize) (Array Std.U64
    4#usize))
  := do
  if limb < 4#usize
  then
    let i ← Array.index_usize limbs limb
    let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i)
    let i2 ← Array.index_usize part_sum limb
    let i3 ← i2 + i1
    let a ← Array.update part_sum limb i3
    let limb1 ← limb + 1#usize
    ok (cont (a, limb1))
  else ok (done part_sum)


end V7Tag73CurrentHelpersOpaque
