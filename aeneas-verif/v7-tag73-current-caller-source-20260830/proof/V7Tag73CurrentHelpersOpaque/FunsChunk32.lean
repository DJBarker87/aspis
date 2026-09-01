import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk31

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 530:34-530:39
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>}::call_mut"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c :
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1)
  := do
  let i ← tupled_args - 2#usize
  let i1 ← 2#usize * i
  let i2 ← Array.index_usize aspis_statement.poseidon2.INTERNAL i1
  ok (i2, c)

/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 530:34-530:39
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>}::call_once"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c :
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1)
  (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 530:34-530:39
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1
  Std.Usize aspis_core.field.M31 := {
  call_once :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 530:34-530:39
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#1, (usize), aspis_core::field::M31>"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1
  Std.Usize aspis_core.field.M31 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 529:27-529:32
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : aspis_statement.state_only_poseidon.interpolated_internal_pair.closure)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure)
  := do
  let q ← Array.index_usize c tupled_args
  ok (q, c)

/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 529:27-529:32
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : aspis_statement.state_only_poseidon.interpolated_internal_pair.closure)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 529:27-529:32
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 529:27-529:32
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair::ROWS]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 528:4-528:26
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair::ROWS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::state_only_poseidon::interpolated_internal_pair::ROWS"]
def aspis_statement.state_only_poseidon.interpolated_internal_pair.ROWS
  : Array Std.Usize 7#usize :=
  Array.make 7#usize [
    2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize
    ]

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy::SHIFTS]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 305:4-305:26
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy::SHIFTS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::state_only_poseidon::internal_linear_lazy::SHIFTS"]
def aspis_statement.state_only_poseidon.internal_linear_lazy.SHIFTS
  : Array Std.U8 15#usize :=
  Array.make 15#usize [
    0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 10#u8, 12#u8, 13#u8,
    14#u8, 15#u8, 16#u8
    ]

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 325:68-325:74
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_mut"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2)
  := do
  let (a, a1, i) := c
  let i1 ← Array.index_usize a tupled_args
  let i2 ← Array.index_usize a1 tupled_args
  let i3 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i - 1#usize
  let i5 ←
    Array.index_usize
      aspis_statement.state_only_poseidon.internal_linear_lazy.SHIFTS i4
  let i6 ← i3 <<< i5
  let i7 ← i1 + i6
  ok (i7, c)

/-- [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 325:68-325:74
    Name pattern: [aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::internal_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_once"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 325:68-325:74
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2 Std.Usize
  Std.U64 := {
  call_once :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 325:68-325:74
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::internal_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2 Std.Usize
  Std.U64 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    aspis_statement.state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}


end V7Tag73CurrentHelpersOpaque
