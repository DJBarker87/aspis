import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk34

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 524:0-527:28
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair] -/
@[rust_fun "aspis_statement::state_only_poseidon::interpolated_internal_pair"]
def aspis_statement.state_only_poseidon.interpolated_internal_pair
  (state : Array aspis_core.field.QM31 16#usize)
  (local1 : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let weights ←
    core.array.Array.map
      aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      aspis_statement.state_only_poseidon.interpolated_internal_pair.ROWS
      local1
  let even_constants ←
    core.array.Array.map
      aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      aspis_statement.state_only_poseidon.interpolated_internal_pair.ROWS ()
  let odd_constants ←
    core.array.Array.map
      aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      aspis_statement.state_only_poseidon.interpolated_internal_pair.ROWS ()
  let s ← Aeneas.Std.lift (Array.to_slice weights)
  let s1 ← Aeneas.Std.lift (Array.to_slice even_constants)
  let even ← aspis_core.field.qm31_m31_dot s s1
  let s2 ← Aeneas.Std.lift (Array.to_slice weights)
  let s3 ← Aeneas.Std.lift (Array.to_slice odd_constants)
  let odd ← aspis_core.field.qm31_m31_dot s2 s3
  let a ← aspis_statement.state_only_poseidon.internal_round state even
  aspis_statement.state_only_poseidon.internal_round a odd

/-- [aspis_statement::state_only_poseidon::interpolate_three_constant_limb]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 416:0-423:8
    Name pattern: [aspis_statement::state_only_poseidon::interpolate_three_constant_limb] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolate_three_constant_limb"]
def aspis_statement.state_only_poseidon.interpolate_three_constant_limb
  (weight0 : Std.U32) (weight1 : Std.U32) (weight2 : Std.U32)
  (constant0 : Std.U32) (constant1 : Std.U32) (constant2 : Std.U32) :
  Result aspis_core.field.M31
  := do
  let i ← Aeneas.Std.lift (core.convert.num.FromU64U32.from weight0)
  let i1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from constant0)
  let i2 ← i * i1
  let i3 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from weight1)
  let i4 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from constant1)
  let i5 ← i3 * i4
  let i6 ← i2 + i5
  let i7 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from weight2)
  let i8 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from constant2)
  let i9 ← i7 * i8
  let i10 ← i6 + i9
  aspis_core.field.M31.reduce_u64 i10

/-- [aspis_statement::state_only_poseidon::interpolate_three_constant_columns]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 440:4-480:5
    Name pattern: [aspis_statement::state_only_poseidon::interpolate_three_constant_columns] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::interpolate_three_constant_columns"]
def
  aspis_statement.state_only_poseidon.interpolate_three_constant_columns_loop.body
  (weights : Array aspis_core.field.QM31 3#usize)
  (column0 : Array Std.U32 16#usize) (column1 : Array Std.U32 16#usize)
  (column2 : Array Std.U32 16#usize)
  (output : Array aspis_core.field.QM31 16#usize) (lane : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 16#usize) × Std.Usize)
    (Array aspis_core.field.QM31 16#usize))
  := do
  if lane < aspis_statement.poseidon2.POSEIDON2_WIDTH
  then
    let q ← Array.index_usize weights 0#usize
    let i := q.c0.a
    let q1 ← Array.index_usize weights 1#usize
    let i1 := q1.c0.a
    let q2 ← Array.index_usize weights 2#usize
    let i2 := q2.c0.a
    let i3 ← Array.index_usize column0 lane
    let i4 ← Array.index_usize column1 lane
    let i5 ← Array.index_usize column2 lane
    let m ←
      aspis_statement.state_only_poseidon.interpolate_three_constant_limb i i1
        i2 i3 i4 i5
    let i6 := q.c0.b
    let i7 := q1.c0.b
    let i8 := q2.c0.b
    let m1 ←
      aspis_statement.state_only_poseidon.interpolate_three_constant_limb i6 i7
        i8 i3 i4 i5
    let c ← aspis_core.field.CM31.new m m1
    let i9 := q.c1.a
    let i10 := q1.c1.a
    let i11 := q2.c1.a
    let m2 ←
      aspis_statement.state_only_poseidon.interpolate_three_constant_limb i9
        i10 i11 i3 i4 i5
    let i12 := q.c1.b
    let i13 := q1.c1.b
    let i14 := q2.c1.b
    let m3 ←
      aspis_statement.state_only_poseidon.interpolate_three_constant_limb i12
        i13 i14 i3 i4 i5
    let c1 ← aspis_core.field.CM31.new m2 m3
    let a ←
      Array.update output lane ({ c0 := c, c1 } : aspis_core.field.QM31)
    let lane1 ← lane + 1#usize
    ok (cont (a, lane1))
  else ok (done output)

/-- [aspis_statement::state_only_poseidon::interpolate_three_constant_columns]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 440:4-480:5
    Name pattern: [aspis_statement::state_only_poseidon::interpolate_three_constant_columns] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::interpolate_three_constant_columns"]
def aspis_statement.state_only_poseidon.interpolate_three_constant_columns_loop
  (weights : Array aspis_core.field.QM31 3#usize)
  (column0 : Array Std.U32 16#usize) (column1 : Array Std.U32 16#usize)
  (column2 : Array Std.U32 16#usize)
  (output : Array aspis_core.field.QM31 16#usize) (lane : Std.Usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (output1, lane1) =>
      aspis_statement.state_only_poseidon.interpolate_three_constant_columns_loop.body
      weights column0 column1 column2 output1 lane1)
    (output, lane)

/-- [aspis_statement::state_only_poseidon::interpolate_three_constant_columns]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 432:0-437:28
    Name pattern: [aspis_statement::state_only_poseidon::interpolate_three_constant_columns] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolate_three_constant_columns"]
def aspis_statement.state_only_poseidon.interpolate_three_constant_columns
  (weights : Array aspis_core.field.QM31 3#usize)
  (column0 : Array Std.U32 16#usize) (column1 : Array Std.U32 16#usize)
  (column2 : Array Std.U32 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let output := Array.repeat 16#usize aspis_core.field.QM31.ZERO
  aspis_statement.state_only_poseidon.interpolate_three_constant_columns_loop
    weights column0 column1 column2 output 0#usize

/-- [aspis_statement::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnMut<(aspis_core::field::QM31,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::external_linear_packed::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 300:21-300:28
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_packed::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_packed::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
  (c : aspis_statement.state_only_poseidon.external_linear_packed.closure)
  (tupled_args : aspis_core.field.QM31) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.state_only_poseidon.external_linear_packed.closure)
  := do
  let q ← aspis_core.field.QM31.add tupled_args c
  ok (q, c)

/-- [aspis_statement::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnOnce<(aspis_core::field::QM31,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::external_linear_packed::closure<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 300:21-300:28
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_packed::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_packed::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31.call_once
  (c : aspis_statement.state_only_poseidon.external_linear_packed.closure)
  (q : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let (q1, _) ←
    aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
      c q
  ok q1

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnOnce<(aspis_core::field::QM31,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::external_linear_packed::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 300:21-300:28
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.external_linear_packed.closure
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnMut<(aspis_core::field::QM31,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::external_linear_packed::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 300:21-300:28
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_packed::closure<'0>, (aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.external_linear_packed.closure
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31
  call_mut :=
    aspis_statement.state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
}

/-- [aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 220:29-220:35
    Name pattern: [aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_local_packed_raw::closure::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_local_packed_raw::closure::closure<'0, '1>, (usize), u64>}::call_mut"]
def
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c :
  aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    aspis_statement.state_only_poseidon.external_local_packed_raw.closure.closure)
  := do
  let (a, i) := c
  let a1 ← Array.index_usize a 0#usize
  let i1 ← Array.index_usize a1 tupled_args
  let a2 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i1)
  let a3 ← Array.index_usize a 1#usize
  let i2 ← Array.index_usize a3 tupled_args
  let b ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i2)
  let a4 ← Array.index_usize a 2#usize
  let i3 ← Array.index_usize a4 tupled_args
  let c1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i3)
  let a5 ← Array.index_usize a 3#usize
  let i4 ← Array.index_usize a5 tupled_args
  let d ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i4)
  match i.val with
  | 0 =>
    let i5 ← 2#u64 * a2
    let i6 ← 3#u64 * b
    let i7 ← i5 + i6
    let i8 ← i7 + c1
    let i9 ← i8 + d
    ok (i9, c)
  | 1 =>
    let i5 ← 2#u64 * b
    let i6 ← a2 + i5
    let i7 ← 3#u64 * c1
    let i8 ← i6 + i7
    let i9 ← i8 + d
    ok (i9, c)
  | 2 =>
    let i5 ← a2 + b
    let i6 ← 2#u64 * c1
    let i7 ← i5 + i6
    let i8 ← 3#u64 * d
    let i9 ← i7 + i8
    ok (i9, c)
  | 3 =>
    let i5 ← 3#u64 * a2
    let i6 ← i5 + b
    let i7 ← i6 + c1
    let i8 ← 2#u64 * d
    let i9 ← i7 + i8
    ok (i9, c)
  | _ => fail panic


end V7Tag73CurrentHelpersOpaque
