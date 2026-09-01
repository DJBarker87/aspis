import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk30

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 600:25-600:32
    Name pattern: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 600:25-600:32
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 600:25-600:32
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 593:53-593:63
    Name pattern: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
  (c :
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1)
  (tupled_args : (aspis_core.field.QM31 × Std.Usize)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1)
  := do
  let (sum, row) := tupled_args
  let q ← Array.index_usize c.«local» row
  let q1 ← aspis_core.field.QM31.add sum q
  ok (q1, c)

/-- [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 593:53-593:63
    Name pattern: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
  (c :
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1)
  (p : (aspis_core.field.QM31 × Std.Usize)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 593:53-593:63
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1
  (aspis_core.field.QM31 × Std.Usize) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 593:53-593:63
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1
  (aspis_core.field.QM31 × Std.Usize) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  call_mut :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
}

/-- [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 592:26-592:36
    Name pattern: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
  (c :
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure)
  (tupled_args : (aspis_core.field.QM31 × Std.Usize)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure)
  := do
  let (sum, row) := tupled_args
  let q ← Array.index_usize c.«local» row
  let q1 ← aspis_core.field.QM31.add sum q
  ok (q1, c)

/-- [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 592:26-592:36
    Name pattern: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
  (c :
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure)
  (p : (aspis_core.field.QM31 × Std.Usize)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 592:26-592:36
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure
  (aspis_core.field.QM31 × Std.Usize) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_core::field::QM31, usize), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 592:26-592:36
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'0>, (aspis_core::field::QM31, usize), aspis_core::field::QM31>"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure
  (aspis_core.field.QM31 × Std.Usize) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  call_mut :=
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
}

/-- [aspis_statement::poseidon2::INTERNAL]
    Source: 'crates/aspis-statement/src/poseidon2.rs', lines 129:0-129:36
    Name pattern: [aspis_statement::poseidon2::INTERNAL] -/
@[global_simps, irreducible, rust_const "aspis_statement::poseidon2::INTERNAL"]
def aspis_statement.poseidon2.INTERNAL : Array Std.U32 14#usize :=
  Array.make 14#usize [
    2139014335#u32, 69309039#u32, 1368974953#u32, 886780232#u32,
    1130937085#u32, 1718115455#u32, 2027103386#u32, 1612216449#u32,
    1994053242#u32, 110146615#u32, 514413329#u32, 1088763546#u32,
    955319292#u32, 488794657#u32
    ]

/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 531:33-531:38
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>}::call_mut"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c :
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2)
  := do
  let i ← tupled_args - 2#usize
  let i1 ← 2#usize * i
  let i2 ← i1 + 1#usize
  let i3 ← Array.index_usize aspis_statement.poseidon2.INTERNAL i2
  ok (i3, c)

/-- [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 531:33-531:38
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolated_internal_pair::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>}::call_once"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c :
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2)
  (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 531:33-531:38
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2
  Std.Usize aspis_core.field.M31 := {
  call_once :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 531:33-531:38
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::interpolated_internal_pair::closure#2, (usize), aspis_core::field::M31>"]
def
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2
  Std.Usize aspis_core.field.M31 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    aspis_statement.state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}


end V7Tag73CurrentHelpersOpaque
