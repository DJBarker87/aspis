import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk25

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<S>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1107:49-1107:61
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1
  S) (p : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
      AtomicSemanticSelectorViewInst c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1107:49-1107:61
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1
  S) (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31
  := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
    AtomicSemanticSelectorViewInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1107:49-1107:61
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1
  S) (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31
  := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
    AtomicSemanticSelectorViewInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
    AtomicSemanticSelectorViewInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'_0, S>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1103:58-1103:65
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure
  S) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure
    S))
  := do
  let (i, _, _) ←
    Array.index_usize
      aspis_statement.state_only_terminal.constants.INITIAL_BLOCKS tupled_args
  let i1 ← Aeneas.Std.lift (core.convert.num.FromUsizeU16.from i)
  let block ← i1 >>> 4#i32
  let q ← AtomicSemanticSelectorViewInst.block c block
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'_0, S>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1103:58-1103:65
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure
  S) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      AtomicSemanticSelectorViewInst c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'_0, S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1103:58-1103:65
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure
  S) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    AtomicSemanticSelectorViewInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'_0, S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1103:58-1103:65
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure<'0, @S>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure
  S) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    AtomicSemanticSelectorViewInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    AtomicSemanticSelectorViewInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1100:0-1102:23
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums"]
def aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (selectors : S) :
  Result (aspis_core.field.QM31 × aspis_core.field.QM31 ×
    aspis_core.field.QM31)
  := do
  let highs ←
    core.array.Array.map
      (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      AtomicSemanticSelectorViewInst)
      aspis_statement.atomic_state_only_terminal.ATOMIC_RETAINED_INITIAL_BLOCK_INDICES
      selectors
  let s ← Aeneas.Std.lift (Array.to_slice highs)
  let i ← core.slice.Slice.iter s
  let high_sum ←
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
      (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
      AtomicSemanticSelectorViewInst) i aspis_core.field.QM31.ZERO ()
  let domains ←
    core.array.Array.map
      (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      AtomicSemanticSelectorViewInst)
      aspis_statement.atomic_state_only_terminal.ATOMIC_RETAINED_INITIAL_BLOCK_INDICES
      ()
  let lengths ←
    core.array.Array.map
      (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      AtomicSemanticSelectorViewInst)
      aspis_statement.atomic_state_only_terminal.ATOMIC_RETAINED_INITIAL_BLOCK_INDICES
      ()
  let s1 ← Aeneas.Std.lift (Array.to_slice highs)
  let s2 ← Aeneas.Std.lift (Array.to_slice domains)
  let q ← aspis_core.field.qm31_m31_dot s1 s2
  let s3 ← Aeneas.Std.lift (Array.to_slice highs)
  let s4 ← Aeneas.Std.lift (Array.to_slice lengths)
  let q1 ← aspis_core.field.qm31_m31_dot s3 s4
  ok (high_sum, q, q1)

/-- [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1126:23-1126:33
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure)
  (tupled_args : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure)
  := do
  let (acc, bit) := tupled_args
  let q ← aspis_core.field.QM31.add acc acc
  let q1 ← aspis_core.field.QM31.add q bit
  ok (q1, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1126:23-1126:33
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure)
  (p : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1126:23-1126:33
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1126:23-1126:33
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10::closure, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure
  (aspis_core.field.QM31 × aspis_core.field.QM31) aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1121:0-1121:47
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_reconstruct_10"]
def aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10
  (view : Slice aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let i := Slice.len view
  massert (i >= 10#usize)
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      aspis_core.field.QM31) view { «end» := 9#usize }
  let i1 ← core.slice.Slice.iter s
  let r ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31)
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      aspis_core.field.QM31) i1
  let q ← Slice.index_usize view 9#usize
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
    (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
    aspis_core.field.QM31)
    aspis_statement.atomic_state_only_terminal.atomic_reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
    r q ()

/-- [aspis_statement::state_only_terminal::constants::OUTPUT_ASSET_CELL]
    Source: 'crates/aspis-statement/src/state_only_terminal_constants.rs', lines 2460:0-2460:45
    Name pattern: [aspis_statement::state_only_terminal::constants::OUTPUT_ASSET_CELL] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::state_only_terminal::constants::OUTPUT_ASSET_CELL"]
def aspis_statement.state_only_terminal.constants.OUTPUT_ASSET_CELL
  : (Std.U16 × Std.U8) :=
  (799#u16, 1#u8)


end V7Tag73CurrentHelpersOpaque
