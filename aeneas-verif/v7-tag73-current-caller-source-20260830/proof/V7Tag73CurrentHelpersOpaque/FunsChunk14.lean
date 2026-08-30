import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk13

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 267:12-267:41
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedPairU64U16QM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure)
  (p : (aspis_core.field.QM31 × (Std.U64 × Std.U16))) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedPairU64U16QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 267:12-267:41
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedPairU64U16QM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure
  (aspis_core.field.QM31 × (Std.U64 × Std.U16)) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedPairU64U16QM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 267:12-267:41
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedPairU64U16QM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure
  (aspis_core.field.QM31 × (Std.U64 × Std.U16)) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedPairU64U16QM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedPairU64U16QM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 264:4-264:33
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active"]
def aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active
  (self : aspis_statement.atomic_state_only_terminal.AtomicSelectors) :
  Result aspis_core.field.QM31
  := do
  let s ←
    lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_ACTIVE_FACTORS)
  let i ← core.slice.Slice.iter s
  core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedPairU64U16QM31
    i aspis_core.field.QM31.ZERO self

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 386:30-386:42
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3)
  (tupled_args : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3)
  := do
  let (sum, value) := tupled_args
  let q ← aspis_core.field.QM31.add sum value
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 386:30-386:42
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3)
  (p : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 386:30-386:42
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 386:30-386:42
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#3, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 382:30-382:42
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2)
  (tupled_args : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2)
  := do
  let (sum, value) := tupled_args
  let q ← aspis_core.field.QM31.add sum value
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 382:30-382:42
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2)
  (p : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 382:30-382:42
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 382:30-382:42
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#2, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 370:50-370:57
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1)
  := do
  let q ← Array.index_usize c tupled_args
  let i ← 16#usize + tupled_args
  let q1 ← Array.index_usize c i
  let q2 ← aspis_core.field.QM31.add q q1
  let i1 ← 32#usize + tupled_args
  let q3 ← Array.index_usize c i1
  let q4 ← aspis_core.field.QM31.add q2 q3
  let i2 ← 48#usize + tupled_args
  let q5 ← Array.index_usize c i2
  let q6 ← aspis_core.field.QM31.add q4 q5
  ok (q6, c)

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 370:50-370:57
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 370:50-370:57
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 370:50-370:57
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure#1<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}


end V7Tag73CurrentHelpersOpaque
