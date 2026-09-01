import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk41

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::spend::VALUE_LIMIT]
    Source: 'crates/aspis-statement/src/spend.rs', lines 9:0-9:26
    Name pattern: [aspis_statement::spend::VALUE_LIMIT]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_statement::spend::VALUE_LIMIT"]
def aspis_statement.spend.VALUE_LIMIT : Result Std.U32 := 1#u32 <<< 30#i32

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1438:92-1438:95
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4)
  (tupled_args :
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase) :
  Result (Unit ×
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4)
  := do
  ok ((), c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1438:92-1438:95
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4)
  (sotdp :
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase) :
  Result Unit
  := do
  let _ ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple.call_mut
      c sotdp
  ok ()

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1438:92-1438:95
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit
  := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1438:92-1438:95
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#4, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit
  := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1432:29-1432:37
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3)
  := do
  let i ← aspis_statement.atomic_state_only_terminal.C1_COLUMNS + tupled_args
  let q ←
    aspis_statement.atomic_state_only_terminal.atomic_selected_claim c 0#usize
      i
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1432:29-1432:37
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1432:29-1432:37
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1432:29-1432:37
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#3<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1429:38-1429:46
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2)
  := do
  let q ←
    aspis_statement.atomic_state_only_terminal.atomic_selected_claim c 2#usize
      tupled_args
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1429:38-1429:46
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1429:38-1429:46
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1429:38-1429:46
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#2<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1428:37-1428:45
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1)
  := do
  let q ←
    aspis_statement.atomic_state_only_terminal.atomic_selected_claim c 1#usize
      tupled_args
  ok (q, c)


end V7Tag73CurrentHelpersOpaque
