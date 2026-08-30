import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk22

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_selected_claim]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1020:0-1024:9
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_selected_claim] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_selected_claim"]
def aspis_statement.atomic_state_only_terminal.atomic_selected_claim
  (claims : Array aspis_core.field.QM31 84#usize) (point : Std.Usize)
  (column : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let i ←
    aspis_statement.atomic_state_only_terminal.ATOMIC_SELECTED_TERMINAL_COLUMNS
  let i1 ← point * i
  let i2 ← i1 + column
  Array.index_usize claims i2

/-- [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'_0, '_1, '_2, N>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1037:52-1037:58
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {N : Std.Usize}
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure N)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure
    N))
  := do
  let (i, i1, a) := c
  let i2 ← 4#usize * i
  let source ← i2 + tupled_args
  if source >= i1
  then
    let i3 ← i1 + N
    if source < i3
    then let i4 ← source - i1
         let q ← Array.index_usize a i4
         ok (q, c)
    else ok (aspis_core.field.QM31.ZERO, c)
  else ok (aspis_core.field.QM31.ZERO, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'_0, '_1, '_2, N>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1037:52-1037:58
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {N : Std.Usize}
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure N)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'_0, '_1, '_2, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1037:52-1037:58
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure N)
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'_0, '_1, '_2, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1037:52-1037:58
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_add_preweighted::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure N)
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    N
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1036:4-1046:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_add_preweighted"]
def aspis_statement.atomic_state_only_terminal.atomic_add_preweighted_loop.body
  {N : Std.Usize} (start : Std.Usize) (values : Array aspis_core.field.QM31 N)
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
        (aspis_statement.atomic_state_only_terminal.atomic_add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        N) (group, start, values)
    let q ← Array.index_usize packed group
    let s ← Aeneas.Std.lift (Array.to_slice lanes)
    let q1 ← aspis_core.field.qm31_pack_base4 s
    let q2 ← aspis_core.field.QM31.add q q1
    let a ← Array.update packed group q2
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1036:4-1046:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_add_preweighted"]
def aspis_statement.atomic_state_only_terminal.atomic_add_preweighted_loop
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) (start : Std.Usize)
  (values : Array aspis_core.field.QM31 N) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  loop
    (fun (iter1, packed1) =>
      aspis_statement.atomic_state_only_terminal.atomic_add_preweighted_loop.body
      start values iter1 packed1)
    (iter, packed)

/-- [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1029:0-1033:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_add_preweighted] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_add_preweighted"]
def aspis_statement.atomic_state_only_terminal.atomic_add_preweighted
  {N : Std.Usize} (packed : Array aspis_core.field.QM31 20#usize)
  (start : Std.Usize) (values : Array aspis_core.field.QM31 N) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  let first ← start / 4#usize
  let i ← start + N
  let i1 ← i - 1#usize
  let last ← i1 / 4#usize
  let iter ← core.ops.range.RangeInclusive.new first last
  aspis_statement.atomic_state_only_terminal.atomic_add_preweighted_loop iter
    packed start values

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'_0, '_1, '_2, N>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1060:52-1060:58
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {N : Std.Usize}
  (c : aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure N)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure N))
  := do
  let (i, i1, a) := c
  let i2 ← 4#usize * i
  let source ← i2 + tupled_args
  if source >= i1
  then
    let i3 ← i1 + N
    if source < i3
    then let i4 ← source - i1
         let q ← Array.index_usize a i4
         ok (q, c)
    else ok (aspis_core.field.QM31.ZERO, c)
  else ok (aspis_core.field.QM31.ZERO, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'_0, '_1, '_2, N>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1060:52-1060:58
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {N : Std.Usize}
  (c : aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure N)
  (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_accumulate::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'_0, '_1, '_2, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1060:52-1060:58
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure N)
  Std.Usize aspis_core.field.QM31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_accumulate::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'_0, '_1, '_2, N>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1060:52-1060:58
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_accumulate::closure<'0, '1, '2, @N>, (usize), aspis_core::field::QM31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure N)
  Std.Usize aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    N
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_accumulate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}


end V7Tag73CurrentHelpersOpaque
