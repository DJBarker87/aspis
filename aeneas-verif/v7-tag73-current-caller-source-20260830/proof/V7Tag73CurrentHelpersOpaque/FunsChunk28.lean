import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk27

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'_0, '_1, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1242:29-1242:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1242:29-1242:35
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1242:29-1242:35
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'_0, '_1, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1241:29-1241:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3
    S F))
  := do
  let (sopo, apsv) := c
  let q ← Array.index_usize sopo.z tupled_args
  let m ← Array.index_usize apsv.output_anchor tupled_args
  let q1 ← aspis_statement.atomic_state_only_terminal.lift m
  let q2 ← aspis_core.field.QM31.sub q q1
  ok (q2, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'_0, '_1, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1241:29-1241:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1241:29-1241:35
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1241:29-1241:35
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#3<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'_0, '_1, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1240:29-1240:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2
    S F))
  := do
  let (sopo, apsv) := c
  let q ← Array.index_usize sopo.z tupled_args
  let m ← Array.index_usize apsv.spend.anchor tupled_args
  let q1 ← aspis_statement.atomic_state_only_terminal.lift m
  let q2 ← aspis_core.field.QM31.sub q q1
  ok (q2, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'_0, '_1, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1240:29-1240:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1240:29-1240:35
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1240:29-1240:35
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#2<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'_0, '_1, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1208:59-1208:66
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1
    S F))
  := do
  let (sopo, q) := c
  if tupled_args < 30#usize
  then
    let i ← tupled_args / 10#usize
    let view ←
      match i.val with
      | 0 => ok sopo.z
      | 1 => ok sopo.succ_z
      | _ => ok sopo.xor12_z
    let i1 ← tupled_args % 10#usize
    let bit ← Array.index_usize view i1
    let q1 ← aspis_core.field.QM31.square bit
    let q2 ← aspis_core.field.QM31.sub q1 bit
    ok (q2, c)
  else
    if tupled_args < 33#usize
    then
      let i ← tupled_args - 30#usize
      let view ←
        match i.val with
        | 0 => ok sopo.z
        | 1 => ok sopo.succ_z
        | _ => ok sopo.xor12_z
      let s ← Aeneas.Std.lift (Array.to_slice view)
      let reconstructed ←
        aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10 s
      let q1 ← Array.index_usize view 10#usize
      let q2 ← aspis_core.field.QM31.sub q1 reconstructed
      ok (q2, c)
    else
      let q1 ← Array.index_usize sopo.z 11#usize
      let q2 ← aspis_core.field.QM31.sub q1 q
      ok (q2, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'_0, '_1, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1208:59-1208:66
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1208:59-1208:66
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1208:59-1208:66
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#1<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'_0, '_1, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1182:56-1182:62
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure
    S F))
  := do
  let (i, sopo) := c
  let i1 ← 4#usize * i
  let lane ← i1 + tupled_args
  if lane >= 2#usize
  then let q ← Array.index_usize sopo.z lane
       ok (q, c)
  else ok (aspis_core.field.QM31.ZERO, c)


end V7Tag73CurrentHelpersOpaque
