import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk26

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_terminal::constants::INPUT_ASSET_CELL]
    Source: 'crates/aspis-statement/src/state_only_terminal_constants.rs', lines 2459:0-2459:44
    Name pattern: [aspis_statement::state_only_terminal::constants::INPUT_ASSET_CELL] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::state_only_terminal::constants::INPUT_ASSET_CELL"]
def aspis_statement.state_only_terminal.constants.INPUT_ASSET_CELL
  : (Std.U16 × Std.U8) :=
  (795#u16, 1#u8)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'_0, '_1, '_2, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1250:49-1250:55
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7
    S F))
  := do
  let (t, sopo, apsv) := c
  let p ←
    Array.index_usize
      (Array.make 2#usize [
        aspis_statement.state_only_terminal.constants.INPUT_ASSET_CELL,
        aspis_statement.state_only_terminal.constants.OUTPUT_ASSET_CELL
        ]) tupled_args
  let (row, _) := p
  let (_, column) := p
  let i ← Aeneas.Std.lift (core.convert.num.FromUsizeU16.from row)
  let q ← AtomicSemanticSelectorViewInst.row t i
  let i1 ← Aeneas.Std.lift (core.convert.num.FromUsizeU8.from column)
  let q1 ← Array.index_usize sopo.z i1
  let q2 ←
    aspis_statement.atomic_state_only_terminal.lift apsv.spend.asset_id
  let q3 ← aspis_core.field.QM31.sub q1 q2
  let q4 ← aspis_core.field.QM31.mul q q3
  ok (q4, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'_0, '_1, '_2, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1250:49-1250:55
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'_0, '_1, '_2, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1250:49-1250:55
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'_0, '_1, '_2, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1250:49-1250:55
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#7<'0, '1, '2, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_7.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'_0, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1247:53-1247:60
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6
    S F))
  := do
  let i ← tupled_args * 16#usize
  let i1 ← i + 11#usize
  let q ← AtomicSemanticSelectorViewInst.row c i1
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'_0, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1247:53-1247:60
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'_0, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1247:53-1247:60
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'_0, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1247:53-1247:60
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#6<'0, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'_0, '_1, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1243:29-1243:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5
    S F))
  := do
  let (sopo, apsv) := c
  let q ← Array.index_usize sopo.z tupled_args
  let m ← Array.index_usize apsv.spend.output_commitment tupled_args
  let q1 ← aspis_statement.atomic_state_only_terminal.lift m
  let q2 ← aspis_core.field.QM31.sub q q1
  ok (q2, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'_0, '_1, S, F>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1243:29-1243:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5
  S F) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1243:29-1243:35
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5
  S F) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'_0, '_1, S, F>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1243:29-1243:35
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#5<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5
  S F) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'_0, '_1, S, F>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1242:29-1242:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed_impl::closure#4<'0, '1, @S, @F>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} {F : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4
  S F) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl.closure_4
    S F))
  := do
  let (sopo, apsv) := c
  let q ← Array.index_usize sopo.z tupled_args
  let m ← Array.index_usize apsv.spend.nullifier tupled_args
  let q1 ← aspis_statement.atomic_state_only_terminal.lift m
  let q2 ← aspis_core.field.QM31.sub q q1
  ok (q2, c)


end V7Tag73CurrentHelpersOpaque
