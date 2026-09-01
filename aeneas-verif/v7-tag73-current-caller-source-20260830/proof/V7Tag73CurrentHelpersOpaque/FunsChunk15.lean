import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk14

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 368:34-368:46
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure)
  (tupled_args : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure)
  := do
  let (sum, value) := tupled_args
  let q ← aspis_core.field.QM31.add sum value
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 368:34-368:46
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure)
  (p : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 368:34-368:46
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 368:34-368:46
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 365:48-365:56
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure)
  := do
  let i ← tupled_args * 16#usize
  let i1 ← tupled_args + 1#usize
  let i2 ← i1 * 16#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31)) c
      { start := i, «end» := i2 }
  let i3 ← core.slice.Slice.iter s
  let q ←
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
      aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
      i3 aspis_core.field.QM31.ZERO ()
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 365:48-365:56
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 365:48-365:56
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 365:48-365:56
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point::closure<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 363:4-363:43
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::at_point"]
def aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point
  (point : Array aspis_core.field.QM31 10#usize) :
  Result aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors
  := do
  let copy ←
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.at_point point
  let semantic_mid ←
    core.array.from_fn 4#usize
      aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      copy.high
  let semantic_local ←
    core.array.from_fn 16#usize
      aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      copy.high
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      copy.low { «end» := 12#usize }
  let i ← core.slice.Slice.iter s
  let q ←
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
      aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_2.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
      i aspis_core.field.QM31.ZERO ()
  let q1 ← Array.index_usize copy.low 12#usize
  let q2 ← Array.index_usize semantic_mid 0#usize
  let q3 ← aspis_core.field.QM31.mul q1 q2
  let poseidon_block ← aspis_core.field.QM31.add q q3
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      copy.low { start := 1#usize, «end» := 11#usize }
  let i1 ← core.slice.Slice.iter s1
  let path_block ←
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
      aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point.closure_3.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
      i1 aspis_core.field.QM31.ZERO ()
  ok { copy, semantic_mid, semantic_local, poseidon_block, path_block }

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::boxed_at_point]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 400:4-400:54
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::boxed_at_point] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::boxed_at_point"]
def
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.boxed_at_point
  (point : Array aspis_core.field.QM31 10#usize) :
  Result aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors
  := do
  aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.at_point
    point

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::block]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 405:4-405:41
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::block] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::block"]
def aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.block
  (self : aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors)
  (block : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  massert (block < 64#usize)
  let i ← block >>> 2#i32
  let q ← Array.index_usize self.copy.low i
  let i1 ← lift (block &&& 3#usize)
  let q1 ← Array.index_usize self.semantic_mid i1
  aspis_core.field.QM31.mul q q1

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::row]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 411:4-411:37
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::row] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicCrossSelectors}::row"]
def aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.row
  (self : aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors)
  (row : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.row self.copy row


end V7Tag73CurrentHelpersOpaque
