import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk23

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1059:4-1069:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate"]
def aspis_statement.atomic_state_only_terminal.atomic_accumulate_loop.body
  {N : Std.Usize} (start : Std.Usize) (values : Array aspis_core.field.QM31 N)
  (prepared_selector : aspis_core.field.PreparedQm31Multiplier)
  (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Array
    aspis_core.field.QM31 20#usize)) (Array aspis_core.field.QM31 20#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done packed)
  | some group =>
    let lanes ←
      core.array.from_fn 4#usize
        (aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        N) (group, start, values)
    let q ← Array.index_usize packed group
    let s ← Aeneas.Std.lift (Array.to_slice lanes)
    let q1 ← aspis_core.field.qm31_pack_base4 s
    let q2 ← aspis_core.field.PreparedQm31Multiplier.mul prepared_selector q1
    let q3 ← aspis_core.field.QM31.add q q2
    let a ← Array.update packed group q3
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1059:4-1069:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate"]
def aspis_statement.atomic_state_only_terminal.atomic_accumulate_loop
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) (start : Std.Usize)
  (values : Array aspis_core.field.QM31 N)
  (prepared_selector : aspis_core.field.PreparedQm31Multiplier) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  loop
    (fun (iter1, packed1) =>
      aspis_statement.atomic_state_only_terminal.atomic_accumulate_loop.body
      start values prepared_selector iter1 packed1)
    (iter, packed)

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1050:0-1055:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate] -/
@[rust_fun "aspis_statement::atomic_state_only_terminal::atomic_accumulate"]
def aspis_statement.atomic_state_only_terminal.atomic_accumulate
  {N : Std.Usize} (packed : Array aspis_core.field.QM31 20#usize)
  (start : Std.Usize) (values : Array aspis_core.field.QM31 N)
  (selector : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  let first ← start / 4#usize
  let i ← start + N
  let i1 ← i - 1#usize
  let last ← i1 / 4#usize
  let prepared_selector ←
    aspis_core.field.PreparedQm31Multiplier.new selector
  let iter ← core.ops.range.RangeInclusive.new first last
  aspis_statement.atomic_state_only_terminal.atomic_accumulate_loop iter packed
    start values prepared_selector

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'_0, '_1, '_2, '_3, N>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1085:56-1085:62
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {N : Std.Usize}
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure
  N) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure
    N))
  := do
  let (i, i1, a, i2) := c
  let i3 ← 4#usize * i
  let source ← i3 + tupled_args
  if source >= i1
  then
    let i4 ← i1 + N
    if source < i4
    then
      let i5 ← source - i1
      let a1 ← Array.index_usize a i2
      let q ← Array.index_usize a1 i5
      ok (q, c)
    else ok (aspis_core.field.QM31.ZERO, c)
  else ok (aspis_core.field.QM31.ZERO, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'_0, '_1, '_2, '_3, N>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1085:56-1085:62
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {N : Std.Usize}
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure
  N) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'_0, '_1, '_2, '_3, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1085:56-1085:62
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure
  N) Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'_0, '_1, '_2, '_3, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1085:56-1085:62
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure::closure<'0, '1, '2, '3, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure
  N) Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    N
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'_0, '_1, '_2, N>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1084:54-1084:61
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {N : Std.Usize}
  (c : aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure N)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure N))
  := do
  let (i, i1, a) := c
  let lanes ←
    core.array.from_fn 4#usize
      (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      N) (i, i1, a, tupled_args)
  let s ← Aeneas.Std.lift (Array.to_slice lanes)
  let q ← aspis_core.field.qm31_pack_base4 s
  ok (q, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'_0, '_1, '_2, N>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1084:54-1084:61
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {N : Std.Usize}
  (c : aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure N)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'_0, '_1, '_2, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1084:54-1084:61
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure N)
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'_0, '_1, '_2, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1084:54-1084:61
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate4::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure N)
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    N
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate4]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1083:4-1096:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate4"]
def aspis_statement.atomic_state_only_terminal.atomic_accumulate4_loop.body
  {N : Std.Usize} (start : Std.Usize)
  (values : Array (Array aspis_core.field.QM31 N) 4#usize)
  (selectors : Array aspis_core.field.QM31 4#usize)
  (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Array
    aspis_core.field.QM31 20#usize)) (Array aspis_core.field.QM31 20#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done packed)
  | some group =>
    let grouped ←
      core.array.from_fn 4#usize
        (aspis_statement.atomic_state_only_terminal.atomic_accumulate4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        N) (group, start, values)
    let q ← Array.index_usize packed group
    let q1 ← aspis_core.field.qm31_sum_products4 selectors grouped
    let q2 ← aspis_core.field.QM31.add q q1
    let a ← Array.update packed group q2
    ok (cont (iter1, a))


end V7Tag73CurrentHelpersOpaque
