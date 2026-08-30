import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk29

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{impl core::ops::function::FnMut<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<S>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1388:64-1388:67
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple.call_mut
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure S)
  (tupled_args :
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase) :
  Result (Unit ×
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure S))
  := do
  ok ((), c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{impl core::ops::function::FnOnce<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<S>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1388:64-1388:67
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple.call_once
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure S)
  (sotdp :
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase) :
  Result Unit
  := do
  let _ ←
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple.call_mut
      AtomicSemanticSelectorViewInst c sotdp
  ok ()

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{impl core::ops::function::FnOnce<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1388:64-1388:67
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure S)
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit
  := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple.call_once
    AtomicSemanticSelectorViewInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::{impl core::ops::function::FnMut<(aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase,), ()> for aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1388:64-1388:67
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_semantic_packed::closure<@S>, (aspis_statement::state_only_terminal::StateOnlyTerminalDiagnosticPhase), ()>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure S)
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit
  := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyTerminalDiagnosticPhaseTuple
    AtomicSemanticSelectorViewInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple.call_mut
    AtomicSemanticSelectorViewInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1383:0-1387:41
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_semantic_packed] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_semantic_packed"]
def aspis_statement.atomic_state_only_terminal.atomic_semantic_packed
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : S) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  aspis_statement.atomic_state_only_terminal.atomic_semantic_packed_impl
    AtomicSemanticSelectorViewInst
    (aspis_statement.atomic_state_only_terminal.atomic_semantic_packed.closure.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple
    AtomicSemanticSelectorViewInst) statement openings selectors ()

/-- [aspis_statement::atomic_state_only_terminal::atomic_equality_value::{impl core::ops::function::Fn<(aspis_core::field::QM31, aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_equality_value::closure}::call]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1392:17-1392:35
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_equality_value::{core::ops::function::Fn<aspis_statement::atomic_state_only_terminal::atomic_equality_value::closure, (aspis_core::field::QM31, aspis_core::field::QM31), aspis_core::field::QM31>}::call] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_equality_value::{core::ops::function::Fn<aspis_statement::atomic_state_only_terminal::atomic_equality_value::closure, (aspis_core::field::QM31, aspis_core::field::QM31), aspis_core::field::QM31>}::call"]
def
  aspis_statement.atomic_state_only_terminal.atomic_equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_equality_value.closure)
  (tupled_args : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result aspis_core.field.QM31
  := do
  let (a, b) := tupled_args
  let ab ← aspis_core.field.QM31.mul a b
  let q ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a
  let q1 ← aspis_core.field.QM31.sub q b
  let q2 ← aspis_core.field.QM31.add q1 ab
  aspis_core.field.QM31.add q2 ab

/-- [aspis_statement::atomic_state_only_terminal::atomic_equality_value]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1397:4-1399:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_equality_value] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_equality_value"]
def aspis_statement.atomic_state_only_terminal.atomic_equality_value_loop.body
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter
  aspis_core.field.QM31) (core.slice.iter.Iter aspis_core.field.QM31))
  (product : aspis_core.field.QM31) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter
    aspis_core.field.QM31) (core.slice.iter.Iter aspis_core.field.QM31)) ×
    aspis_core.field.QM31) aspis_core.field.QM31)
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31)
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31) iter
  match o with
  | none => ok (done product)
  | some p =>
    let q ←
      aspis_statement.atomic_state_only_terminal.atomic_equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
        () p
    let product1 ← aspis_core.field.QM31.mul product q
    ok (cont (iter1, product1))

/-- [aspis_statement::atomic_state_only_terminal::atomic_equality_value]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1397:4-1399:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_equality_value] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_equality_value"]
def aspis_statement.atomic_state_only_terminal.atomic_equality_value_loop
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter
  aspis_core.field.QM31) (core.slice.iter.Iter aspis_core.field.QM31))
  (product : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (iter1, product1) =>
      aspis_statement.atomic_state_only_terminal.atomic_equality_value_loop.body
      iter1 product1)
    (iter, product)

/-- [aspis_statement::atomic_state_only_terminal::atomic_equality_value]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1391:0-1391:71
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_equality_value] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_equality_value"]
def aspis_statement.atomic_state_only_terminal.atomic_equality_value
  (left : Array aspis_core.field.QM31 10#usize)
  (right : Array aspis_core.field.QM31 10#usize) :
  Result aspis_core.field.QM31
  := do
  let q ← Array.index_usize left 0#usize
  let q1 ← Array.index_usize right 0#usize
  let product ←
    aspis_statement.atomic_state_only_terminal.atomic_equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
      () (q, q1)
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice aspis_core.field.QM31))
      left { start := 1#usize }
  let i ← core.slice.Slice.iter s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice aspis_core.field.QM31))
      right { start := 1#usize }
  let iter ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31)
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
      aspis_core.field.QM31) i s1
  aspis_statement.atomic_state_only_terminal.atomic_equality_value_loop iter
    product

/-- [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 600:25-600:32
    Name pattern: [aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'0, '1, '2, '3, '4, '5>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  := do
  let (sopo, a, pqm, a1, a2, a3) := c
  let start ← 4#usize * tupled_args
  let i ← start + 4#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      sopo.succ_z { start, «end» := i }
  let target ← aspis_core.field.qm31_pack_base4 s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31)) a
      { start, «end» := i }
  let internal ← aspis_core.field.qm31_pack_base4 s1
  let q ← Array.index_usize a2 tupled_args
  let q1 ← aspis_core.field.QM31.sub target q
  let q2 ← Array.index_usize a3 tupled_args
  let q3 ← aspis_core.field.QM31.sub target q2
  let q4 ← aspis_core.field.QM31.sub target internal
  let q5 ←
    aspis_core.field.qm31_sum_products3_prepared a1
      (Array.make 3#usize [ q1, q3, q4 ])
  let q6 ← aspis_core.field.PreparedQm31Multiplier.mul pqm q5
  ok (q6, c)


end V7Tag73CurrentHelpersOpaque
