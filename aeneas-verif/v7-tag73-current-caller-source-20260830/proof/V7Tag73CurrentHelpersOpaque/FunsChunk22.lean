import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk21

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::QM31,), aspis_core::field::PreparedQm31Multiplier> for aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 819:13-819:20
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnOnceTupleSharedQM31PreparedQm31Multiplier.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure)
  (q : aspis_core.field.QM31) :
  Result aspis_core.field.PreparedQm31Multiplier
  := do
  let (pqm, _) ←
    aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnMutTupleSharedQM31PreparedQm31Multiplier.call_mut
      c q
  ok pqm

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::QM31,), aspis_core::field::PreparedQm31Multiplier> for aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 819:13-819:20
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnOnceTupleSharedQM31PreparedQm31Multiplier
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure
  aspis_core.field.QM31 aspis_core.field.PreparedQm31Multiplier := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnOnceTupleSharedQM31PreparedQm31Multiplier.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{impl core::ops::function::FnMut<(&'_ aspis_core::field::QM31,), aspis_core::field::PreparedQm31Multiplier> for aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 819:13-819:20
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnMutTupleSharedQM31PreparedQm31Multiplier
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure
  aspis_core.field.QM31 aspis_core.field.PreparedQm31Multiplier := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnOnceTupleSharedQM31PreparedQm31Multiplier
  call_mut :=
    aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnMutTupleSharedQM31PreparedQm31Multiplier.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 802:0-802:73
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing"]
def aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing
  (selectors : aspis_statement.atomic_state_only_terminal.AtomicSelectors) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  let s ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LEFT_BASIS_FACTORS)
  let s1 ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LEFT_RECONSTRUCTION_FACTORS)
  let s2 ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LEFT_DIRECT_BASIS)
  let s3 ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_ENTRIES)
  let s4 ← Aeneas.Std.lift (Array.to_slice selectors.high)
  let left_values ←
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms
      s s1 s2 s3 s4
  let s5 ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_RIGHT_BASIS_FACTORS)
  let s6 ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_RIGHT_RECONSTRUCTION_FACTORS)
  let s7 ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_RIGHT_DIRECT_BASIS)
  let s8 ←
    Aeneas.Std.lift (Array.to_slice
      aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_ENTRIES)
  let s9 ← Aeneas.Std.lift (Array.to_slice selectors.low)
  let right_values ←
    aspis_statement.atomic_state_only_terminal.evaluate_factorized_routing_linear_forms
      s5 s6 s7 s8 s9
  let s10 := alloc.vec.Vec.deref right_values
  let i ← core.slice.Slice.iter s10
  let m ←
    core.iter.traits.iterator.Iterator.map.default
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31)
      aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnMutTupleSharedQM31PreparedQm31Multiplier
      i ()
  let right_prepared ←
    core.iter.traits.iterator.Iterator.collect.default
      (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31)
      aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnMutTupleSharedQM31PreparedQm31Multiplier)
      (core.iter.traits.collect.FromIteratorVec
      aspis_core.field.PreparedQm31Multiplier) m
  aspis_statement.atomic_state_only_terminal.accumulate_atomic_copy_routing
    left_values right_prepared

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_PATTERN_MASKS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 50:0-50:60
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_PATTERN_MASKS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_PATTERN_MASKS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_PATTERN_MASKS
  : Array Std.U16 4#usize :=
  Array.make 4#usize [ 10731#u16, 8714#u16, 22047#u16, 524#u16 ]

/-- [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl]: loop body 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 888:4-896:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0_loop0.body
  (pattern_values : Array aspis_core.field.QM31 15#usize)
  (routing : alloc.vec.Vec aspis_core.field.QM31)
  (iter : core.ops.range.Range Std.Usize)
  (values : Array aspis_core.field.QM31 4#usize)
  (weights : Array aspis_core.field.QM31 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 4#usize) × (Array aspis_core.field.QM31 4#usize))
    ((Array aspis_core.field.QM31 4#usize) × (Array aspis_core.field.QM31
    4#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (values, weights))
  | some slot =>
    let i ←
      2#usize +
        aspis_statement.atomic_state_only_terminal.ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS
    let base ← slot * i
    let q ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.QM31) routing base
    let a ← Array.update weights slot q
    let i1 ← base + 1#usize
    let q1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.QM31) routing i1
    let i2 ← base + 2#usize
    let s ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice
        aspis_core.field.QM31) routing { start := i2 }
    let i3 ←
      Array.index_usize
        aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_PATTERN_MASKS
        slot
    let q2 ←
      aspis_statement.atomic_state_only_terminal.atomic_pattern_masked_dot s
        pattern_values i3
    let q3 ← aspis_core.field.QM31.add q1 q2
    let a1 ← Array.update values slot q3
    ok (cont (iter1, a1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl]: loop 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 888:4-896:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (pattern_values : Array aspis_core.field.QM31 15#usize)
  (routing : alloc.vec.Vec aspis_core.field.QM31)
  (values : Array aspis_core.field.QM31 4#usize)
  (weights : Array aspis_core.field.QM31 4#usize) :
  Result ((Array aspis_core.field.QM31 4#usize) × (Array aspis_core.field.QM31
    4#usize))
  := do
  loop
    (fun (iter1, values1, weights1) =>
      aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0_loop0.body
      pattern_values routing iter1 values1 weights1)
    (iter, values, weights)

/-- [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 879:4-915:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0.body
  {F : Type}
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31)
  (selectors : aspis_statement.atomic_state_only_terminal.AtomicSelectors)
  (chi : aspis_core.field.QM31) (trace : F)
  (prepared_lambda : aspis_core.field.PreparedQm31Multiplier)
  (iter : core.ops.range.Range Std.Usize)
  (powers : Array aspis_core.field.QM31 9#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 9#usize)) (aspis_core.field.QM31 ×
    aspis_core.field.QM31))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let s ← Aeneas.Std.lift (Array.to_slice powers)
    let pattern_values ←
      aspis_statement.atomic_state_only_terminal.atomic_copy_pattern_values
        openings s
    let (_, trace1) ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.CopyPatterns
    let routing ←
      aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing
        selectors
    let (_, trace2) ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace1
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.CopyRouting
    let values := Array.repeat 4#usize aspis_core.field.QM31.ZERO
    let weights := Array.repeat 4#usize aspis_core.field.QM31.ZERO
    let (values1, weights1) ←
      aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0_loop0
        { start := 0#usize, «end» := 4#usize } pattern_values routing values
        weights
    let q ← Array.index_usize values1 0#usize
    let q1 ← aspis_core.field.QM31.sub chi q
    let q2 ← Array.index_usize values1 1#usize
    let q3 ← aspis_core.field.QM31.sub chi q2
    let q4 ← Array.index_usize values1 2#usize
    let q5 ← aspis_core.field.QM31.sub chi q4
    let q6 ← Array.index_usize values1 3#usize
    let q7 ← aspis_core.field.QM31.sub chi q6
    let q8 ←
      Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 0#usize
    let q9 ←
      Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 1#usize
    let producer_denominator ← aspis_core.field.QM31.mul q8 q9
    let q10 ←
      Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 2#usize
    let q11 ←
      Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 3#usize
    let consumer_denominator ← aspis_core.field.QM31.mul q10 q11
    let q12 ← Array.index_usize weights1 0#usize
    let q13 ← Array.index_usize weights1 1#usize
    let producer ←
      aspis_core.field.qm31_sum_products2 (Array.make 2#usize [ q12, q13 ])
        (Array.make 2#usize [ q9, q8 ])
    let q14 ← Array.index_usize weights1 2#usize
    let q15 ← Array.index_usize weights1 3#usize
    let consumer ←
      aspis_core.field.qm31_sum_products2 (Array.make 2#usize [ q14, q15 ])
        (Array.make 2#usize [ q11, q10 ])
    let q16 ← aspis_core.field.QM31.neg consumer_denominator
    let q17 ← aspis_core.field.QM31.mul h1_z consumer_denominator
    let q18 ← aspis_core.field.QM31.add q17 consumer
    let cleared ←
      aspis_core.field.qm31_sum_products2
        (Array.make 2#usize [ producer_denominator, q16 ])
        (Array.make 2#usize [ q18, producer ])
    let copy_active ←
      aspis_statement.atomic_state_only_terminal.AtomicSelectors.copy_active
        selectors
    let output ← aspis_core.field.QM31.mul copy_active cleared
    let _ ←
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst.call_mut
        trace2
        aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase.Copy
    ok (done (output, copy_active))
  | some index =>
    let i ← index - 1#usize
    let q ← Array.index_usize powers i
    let q1 ← aspis_core.field.PreparedQm31Multiplier.mul prepared_lambda q
    let a ← Array.update powers index q1
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 879:4-915:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0
  {F : Type}
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (iter : core.ops.range.Range Std.Usize)
  (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31)
  (selectors : aspis_statement.atomic_state_only_terminal.AtomicSelectors)
  (chi : aspis_core.field.QM31) (trace : F)
  (powers : Array aspis_core.field.QM31 9#usize)
  (prepared_lambda : aspis_core.field.PreparedQm31Multiplier) :
  Result (aspis_core.field.QM31 × aspis_core.field.QM31)
  := do
  loop
    (fun (iter1, powers1) =>
      aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0.body
      coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
      openings h1_z selectors chi trace prepared_lambda iter1 powers1)
    (iter, powers)

/-- [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 862:0-871:47
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_copy_lane_from_routing_impl"]
def
  aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl
  {F : Type}
  (coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst :
  core.ops.function.FnMut F
  aspis_statement.state_only_terminal.StateOnlyTerminalDiagnosticPhase Unit)
  (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31)
  (selectors : aspis_statement.atomic_state_only_terminal.AtomicSelectors)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) (trace : F) :
  Result (aspis_core.field.QM31 × aspis_core.field.QM31)
  := do
  let powers := Array.repeat 9#usize aspis_core.field.QM31.ZERO
  let powers1 ← Array.update powers 0#usize lambda
  let prepared_lambda ← aspis_core.field.PreparedQm31Multiplier.new lambda
  let s ← Aeneas.Std.lift (Array.to_slice powers1)
  let i := Slice.len s
  aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl_loop0
    coreopsfunctionFnMutFTupleStateOnlyTerminalDiagnosticPhaseTupleInst
    { start := 1#usize, «end» := i } openings h1_z selectors chi trace
    powers1 prepared_lambda


end V7Tag73CurrentHelpersOpaque
