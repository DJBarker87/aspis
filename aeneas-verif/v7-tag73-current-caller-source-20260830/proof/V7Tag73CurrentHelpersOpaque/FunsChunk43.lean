import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk42

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1428:37-1428:45
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1428:37-1428:45
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1428:37-1428:45
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure#1<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1427:32-1427:40
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure)
  := do
  let q ←
    aspis_statement.atomic_state_only_terminal.atomic_selected_claim c 0#usize
      tupled_args
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1427:32-1427:40
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1427:32-1427:40
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'_0>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1427:32-1427:40
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3::closure<'0>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3]: loop body 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1444:4-1446:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0_loop0.body
  (prepared_theta : aspis_core.field.PreparedQm31Multiplier)
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter
  aspis_core.field.QM31 4#usize)) (composition : aspis_core.field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.array.iter.IntoIter
    aspis_core.field.QM31 4#usize)) × aspis_core.field.QM31)
    aspis_core.field.QM31)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      aspis_core.field.QM31 4#usize) iter
  match o with
  | none => ok (done composition)
  | some lane =>
    let q ←
      aspis_core.field.PreparedQm31Multiplier.mul prepared_theta composition
    let composition1 ← aspis_core.field.QM31.add q lane
    ok (cont (iter1, composition1))

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3]: loop 1:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1444:4-1446:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0_loop0
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter
  aspis_core.field.QM31 4#usize))
  (prepared_theta : aspis_core.field.PreparedQm31Multiplier)
  (composition : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (iter1, composition1) =>
      aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0_loop0.body
      prepared_theta iter1 composition1)
    (iter, composition)

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1441:4-1455:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0.body
  (claims : Array aspis_core.field.QM31 84#usize)
  (poseidon : Array aspis_core.field.QM31 4#usize)
  (prepared_theta : aspis_core.field.PreparedQm31Multiplier)
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter
  aspis_core.field.QM31 20#usize)) (composition : aspis_core.field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.array.iter.IntoIter
    aspis_core.field.QM31 20#usize)) × aspis_core.field.QM31)
    (aspis_core.field.QM31 × aspis_core.field.QM31))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      aspis_core.field.QM31 20#usize) iter
  match o with
  | none =>
    let ii ←
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter poseidon
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
        aspis_core.field.QM31 4#usize)
        (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
        aspis_core.field.QM31 4#usize) ii
    let composition1 ←
      aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0_loop0
        iter2 prepared_theta composition
    let i ←
      aspis_statement.atomic_state_only_terminal.ATOMIC_SELECTED_G_COLUMN
    let q ←
      aspis_statement.atomic_state_only_terminal.atomic_selected_claim claims
        0#usize i
    ok (done (composition1, q))
  | some lane =>
    let q ←
      aspis_core.field.PreparedQm31Multiplier.mul prepared_theta composition
    let composition1 ← aspis_core.field.QM31.add q lane
    ok (cont (iter1, composition1))

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1441:4-1455:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter
  aspis_core.field.QM31 20#usize))
  (claims : Array aspis_core.field.QM31 84#usize)
  (poseidon : Array aspis_core.field.QM31 4#usize)
  (prepared_theta : aspis_core.field.PreparedQm31Multiplier)
  (composition : aspis_core.field.QM31) :
  Result (aspis_core.field.QM31 × aspis_core.field.QM31)
  := do
  loop
    (fun (iter1, composition1) =>
      aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0.body
      claims poseidon prepared_theta iter1 composition1)
    (iter, composition)

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1405:0-1422:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_composition_parts_compiled_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (claims : Array aspis_core.field.QM31 84#usize)
  (point : Array aspis_core.field.QM31 10#usize)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (theta : aspis_core.field.QM31) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 16#usize) × (Array aspis_core.field.QM31 10#usize)
    × aspis_core.field.QM31 × aspis_core.field.QM31 × aspis_core.field.QM31)
    aspis_statement.state_only_terminal.StateOnlyTerminalError)
  := do
  let i ← aspis_statement.spend.VALUE_LIMIT
  if statement.spend.fee >= i
  then
    ok (core.result.Result.Err
      aspis_statement.state_only_terminal.StateOnlyTerminalError.PublicFeeOutOfRange)
  else
    let a ←
      core.array.from_fn 16#usize
        aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        claims
    let a1 ←
      core.array.from_fn 16#usize
        aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        claims
    let a2 ←
      core.array.from_fn 16#usize
        aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        claims
    let mask_only ←
      core.array.from_fn 10#usize
        aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        claims
    let selectors ←
      aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.boxed_at_point
        point
    let sops ←
      aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.poseidon
        selectors
    let poseidon ←
      aspis_statement.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
        { z := a, succ_z := a1, xor12_z := a2 } sops
    let acs ← Box.Insts.CoreConvertAsRef.as_ref Global selectors
    let semantic ←
      aspis_statement.atomic_state_only_terminal.atomic_semantic_packed
        aspis_statement.atomic_state_only_terminal.AtomicCrossSelectors.Insts.Aspis_statementAtomic_state_only_terminalAtomicSemanticSelectorView
        statement { z := a, succ_z := a1, xor12_z := a2 } acs
    let i1 ←
      aspis_statement.atomic_state_only_terminal.ATOMIC_SELECTED_H1_COLUMN
    let h1_z ←
      aspis_statement.atomic_state_only_terminal.atomic_selected_claim claims
        0#usize i1
    let (copy, copy_active) ←
      aspis_statement.atomic_state_only_terminal.atomic_copy_lane_from_routing_impl
        aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3.closure_4.Insts.CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple
        a h1_z selectors.copy lambda chi ()
    let prepared_theta ← aspis_core.field.PreparedQm31Multiplier.new theta
    let ii ←
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter semantic
    let iter ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
        aspis_core.field.QM31 20#usize)
        (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
        aspis_core.field.QM31 20#usize) ii
    let (composition, q) ←
      aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3_loop0
        iter claims poseidon prepared_theta copy
    ok (core.result.Result.Ok (composition, a, mask_only, q, h1_z,
      copy_active))


end V7Tag73CurrentHelpersOpaque
