import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk24

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate4]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1083:4-1096:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_accumulate4"]
def aspis_statement.atomic_state_only_terminal.atomic_accumulate4_loop
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array aspis_core.field.QM31 20#usize) (start : Std.Usize)
  (values : Array (Array aspis_core.field.QM31 N) 4#usize)
  (selectors : Array aspis_core.field.QM31 4#usize) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  loop
    (fun (iter1, packed1) =>
      aspis_statement.atomic_state_only_terminal.atomic_accumulate4_loop.body
      start values selectors iter1 packed1)
    (iter, packed)

/-- [aspis_statement::atomic_state_only_terminal::atomic_accumulate4]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1075:0-1080:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_accumulate4] -/
@[rust_fun "aspis_statement::atomic_state_only_terminal::atomic_accumulate4"]
def aspis_statement.atomic_state_only_terminal.atomic_accumulate4
  {N : Std.Usize} (packed : Array aspis_core.field.QM31 20#usize)
  (start : Std.Usize) (values : Array (Array aspis_core.field.QM31 N) 4#usize)
  (selectors : Array aspis_core.field.QM31 4#usize) :
  Result (Array aspis_core.field.QM31 20#usize)
  := do
  let first ← start / 4#usize
  let i ← start + N
  let i1 ← i - 1#usize
  let last ← i1 / 4#usize
  let iter ← core.ops.range.RangeInclusive.new first last
  aspis_statement.atomic_state_only_terminal.atomic_accumulate4_loop iter
    packed start values selectors

/-- [aspis_statement::state_only_terminal::constants::INITIAL_BLOCKS]
    Source: 'crates/aspis-statement/src/state_only_terminal_constants.rs', lines 2433:0-2433:54
    Name pattern: [aspis_statement::state_only_terminal::constants::INITIAL_BLOCKS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::state_only_terminal::constants::INITIAL_BLOCKS"]
def aspis_statement.state_only_terminal.constants.INITIAL_BLOCKS
  : Array (Std.U16 × Std.U32 × Std.U32) 24#usize :=
  Array.make 24#usize [
    (0#u16, 1095958529#u32, 8#u32), (16#u16, 1095958531#u32, 18#u32), (64#u16,
    1095958533#u32, 16#u32), (96#u16, 1095958533#u32, 16#u32), (128#u16,
    1095958533#u32, 16#u32), (160#u16, 1095958533#u32, 16#u32), (192#u16,
    1095958533#u32, 16#u32), (224#u16, 1095958533#u32, 16#u32), (256#u16,
    1095958533#u32, 16#u32), (288#u16, 1095958533#u32, 16#u32), (320#u16,
    1095958533#u32, 16#u32), (352#u16, 1095958533#u32, 16#u32), (384#u16,
    1095958533#u32, 16#u32), (416#u16, 1095958533#u32, 16#u32), (448#u16,
    1095958533#u32, 16#u32), (480#u16, 1095958533#u32, 16#u32), (512#u16,
    1095958533#u32, 16#u32), (544#u16, 1095958533#u32, 16#u32), (576#u16,
    1095958533#u32, 16#u32), (608#u16, 1095958533#u32, 16#u32), (640#u16,
    1095958533#u32, 16#u32), (672#u16, 1095958533#u32, 16#u32), (704#u16,
    1095958530#u32, 16#u32), (736#u16, 1095958531#u32, 18#u32)
    ]

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<S>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1111:13-1111:20
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3
  S) (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3
    S))
  := do
  let (_, _, i) ←
    Array.index_usize
      aspis_statement.state_only_terminal.constants.INITIAL_BLOCKS tupled_args
  ok (i, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<S>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1111:13-1111:20
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3
  S) (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      AtomicSemanticSelectorViewInst c i
  ok m

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1111:13-1111:20
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3
  S) Std.Usize aspis_core.field.M31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
    AtomicSemanticSelectorViewInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1111:13-1111:20
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#3<@S>, (usize), aspis_core::field::M31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3
  S) Std.Usize aspis_core.field.M31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
    AtomicSemanticSelectorViewInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
    AtomicSemanticSelectorViewInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<S>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1109:13-1109:20
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2
  S) (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2
    S))
  := do
  let (_, i, _) ←
    Array.index_usize
      aspis_statement.state_only_terminal.constants.INITIAL_BLOCKS tupled_args
  ok (i, c)

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<S>}::call_once]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1109:13-1109:20
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>}::call_once] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>}::call_once"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2
  S) (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      AtomicSemanticSelectorViewInst c i
  ok m

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1109:13-1109:20
    Name pattern: [core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnOnce
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2
  S) Std.Usize aspis_core.field.M31 := {
  call_once :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
    AtomicSemanticSelectorViewInst
}

/-- Trait implementation: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<S>}]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1109:13-1109:20
    Name pattern: [core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#2<@S>, (usize), aspis_core::field::M31>"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S) :
  core.ops.function.FnMut
  (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2
  S) Std.Usize aspis_core.field.M31 := {
  FnOnceInst :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
    AtomicSemanticSelectorViewInst
  call_mut :=
    aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
    AtomicSemanticSelectorViewInst
}

/-- [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<S>}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1107:49-1107:61
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::atomic_retained_initial_sums::closure#1<@S>, (aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
  {S : Type} (AtomicSemanticSelectorViewInst :
  aspis_statement.atomic_state_only_terminal.AtomicSemanticSelectorView S)
  (c :
  aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1
  S) (tupled_args : (aspis_core.field.QM31 × aspis_core.field.QM31)) :
  Result (aspis_core.field.QM31 ×
    (aspis_statement.atomic_state_only_terminal.atomic_retained_initial_sums.closure_1
    S))
  := do
  let (sum, value) := tupled_args
  let q ← aspis_core.field.QM31.add sum value
  ok (q, c)


end V7Tag73CurrentHelpersOpaque
