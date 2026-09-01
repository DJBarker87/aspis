import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk12

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 233:8-242:9
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand"]
def
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0.body
  {N : Std.Usize} (iter : core.slice.iter.Iter aspis_core.field.QM31)
  (weights : Array aspis_core.field.QM31 N) (len : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.Iter aspis_core.field.QM31) × (Array
    aspis_core.field.QM31 N) × Std.Usize) (Array aspis_core.field.QM31 N))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done weights)
  | some coordinate =>
    let prepared ← aspis_core.field.PreparedQm31Multiplier.new coordinate
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator
        core.iter.range.StepUsize) { start := 0#usize, «end» := len }
    let weights1 ←
      aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0
        iter2 weights prepared
    let len1 ← len * 2#usize
    ok (cont (iter1, weights1, len1))

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 233:8-242:9
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand"]
def aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0
  {N : Std.Usize} (iter : core.slice.iter.Iter aspis_core.field.QM31)
  (weights : Array aspis_core.field.QM31 N) (len : Std.Usize) :
  Result (Array aspis_core.field.QM31 N)
  := do
  loop
    (fun (iter1, weights1, len1) =>
      aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0.body
      iter1 weights1 len1)
    (iter, weights, len)

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 229:4-229:64
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::expand"]
def aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand
  (N : Std.Usize) (coordinates : Slice aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 N)
  := do
  let weights := Array.repeat N aspis_core.field.QM31.ZERO
  let a ← Array.update weights 0#usize aspis_core.field.QM31.ONE
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      coordinates
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand_loop0 iter
    a 1#usize

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::at_point]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 246:4-246:43
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::at_point] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::at_point"]
def aspis_statement.atomic_state_only_terminal.AtomicSelectors.at_point
  (point : Array aspis_core.field.QM31 10#usize) :
  Result aspis_statement.atomic_state_only_terminal.AtomicSelectors
  := do
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice aspis_core.field.QM31))
      point { start := 4#usize }
  let a ←
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand 64#usize
      s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      point { «end» := 4#usize }
  let a1 ←
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.expand 16#usize
      s1
  ok { high := a, low := a1 }

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LOW_ROW_BITS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 5:0-5:54
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LOW_ROW_BITS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LOW_ROW_BITS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LOW_ROW_BITS
  : Std.U16 :=
  960#u16

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::row]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 256:4-256:37
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::row] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::row"]
def aspis_statement.atomic_state_only_terminal.AtomicSelectors.row
  (self : aspis_statement.atomic_state_only_terminal.AtomicSelectors)
  (row : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  massert (row < aspis_statement.atomic_state_only_terminal.TRACE_ROWS)
  let i ←
    lift (~~~
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LOW_ROW_BITS)
  let high_bits ← lift (i &&& 1023#u16)
  let i1 ←
    aspis_statement.atomic_state_only_terminal.projected_row_index row
      high_bits
  let q ← Array.index_usize self.high i1
  let i2 ←
    aspis_statement.atomic_state_only_terminal.projected_row_index row
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LOW_ROW_BITS
  let q1 ← Array.index_usize self.low i2
  aspis_core.field.QM31.mul q q1

/-- [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_ACTIVE_FACTORS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 11:0-11:70
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_ACTIVE_FACTORS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_ACTIVE_FACTORS"]
def
  aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_ACTIVE_FACTORS
  : Array (Std.U64 × Std.U16) 10#usize :=
  Array.make 10#usize [
    (16717053931664965632#u64, 4096#u16), (134217728#u64, 6143#u16),
    (576460752303423488#u64, 7135#u16), (1153229368131059712#u64, 8191#u16),
    (59390#u64, 8192#u16), (17180786688#u64, 12288#u16), (1#u64, 14334#u16),
    (4294967296#u64, 14335#u16), (65536#u64, 16382#u16), (6144#u64, 16383#u16)
    ]

/-- [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 267:12-267:41
    Name pattern: [aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::{aspis_statement::atomic_state_only_terminal::AtomicSelectors}::copy_active::closure<'0>, (aspis_core::field::QM31, &'_ (u64, u16)), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedPairU64U16QM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure)
  (tupled_args : (aspis_core.field.QM31 × (Std.U64 × Std.U16))) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active.closure)
  := do
  let (sum, (high_mask, low_mask)) := tupled_args
  let high ←
    aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_64
      c.high high_mask
  let low ←
    aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_16
      c.low low_mask
  let q ← aspis_core.field.QM31.mul high low
  let q1 ← aspis_core.field.QM31.add sum q
  ok (q1, c)


end V7Tag73CurrentHelpersOpaque
