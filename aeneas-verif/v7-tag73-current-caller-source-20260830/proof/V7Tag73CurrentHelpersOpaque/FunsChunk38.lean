import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk37

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'_0, '_1, '_2>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 186:69-186:75
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_mut"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : aspis_statement.state_only_poseidon.external_linear_lazy.closure_2)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_2)
  := do
  let (a, a1, i) := c
  let i1 ← Array.index_usize a tupled_args
  let i2 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i1)
  let i3 ← Aeneas.Std.lift (i &&& 3#usize)
  let a2 ← Array.index_usize a1 i3
  let i4 ← Array.index_usize a2 tupled_args
  let i5 ← i2 + i4
  ok (i5, c)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'_0, '_1, '_2>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 186:69-186:75
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>}::call_once"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : aspis_statement.state_only_poseidon.external_linear_lazy.closure_2)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'_0, '_1, '_2>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 186:69-186:75
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_2 Std.Usize
  Std.U64 := {
  call_once :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'_0, '_1, '_2>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 186:69-186:75
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#2<'0, '1, '2>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_2 Std.Usize
  Std.U64 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 176:29-176:35
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>}::call_mut"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c :
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure)
  := do
  let (a, i) := c
  let q ← Array.index_usize a i
  let a1 ← aspis_statement.state_only_poseidon.extension_limbs q
  let i1 ← Array.index_usize a1 tupled_args
  let i2 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i1)
  let i3 ← 4#usize + i
  let q1 ← Array.index_usize a i3
  let a2 ← aspis_statement.state_only_poseidon.extension_limbs q1
  let i4 ← Array.index_usize a2 tupled_args
  let i5 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i4)
  let i6 ← i2 + i5
  let i7 ← 8#usize + i
  let q2 ← Array.index_usize a i7
  let a3 ← aspis_statement.state_only_poseidon.extension_limbs q2
  let i8 ← Array.index_usize a3 tupled_args
  let i9 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i8)
  let i10 ← i6 + i9
  let i11 ← 12#usize + i
  let q3 ← Array.index_usize a i11
  let a4 ← aspis_statement.state_only_poseidon.extension_limbs q3
  let i12 ← Array.index_usize a4 tupled_args
  let i13 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i12)
  let i14 ← i10 + i13
  ok (i14, c)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 176:29-176:35
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>}::call_once"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c :
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 176:29-176:35
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure
  Std.Usize Std.U64 := {
  call_once :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 176:29-176:35
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure
  Std.Usize Std.U64 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'_0>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 175:51-175:59
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>}::call_mut"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
  (c : aspis_statement.state_only_poseidon.external_linear_lazy.closure_1)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U64 4#usize) ×
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1)
  := do
  let a ←
    core.array.from_fn 4#usize
      aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      (c, tupled_args)
  ok (a, c)

/-- [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'_0>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 175:51-175:59
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>}::call_once"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
  (c : aspis_statement.state_only_poseidon.external_linear_lazy.closure_1)
  (i : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  let (a, _) ←
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
      c i
  ok a

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 175:51-175:59
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1 Std.Usize
  (Array Std.U64 4#usize) := {
  call_once :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'_0>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 175:51-175:59
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure#1<'0>, (usize), [u64; 4]>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.external_linear_lazy.closure_1 Std.Usize
  (Array Std.U64 4#usize) := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  call_mut :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
}

/-- [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 157:43-157:49
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>}::call_mut] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>}::call_mut"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : aspis_statement.state_only_poseidon.external_linear_lazy.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    aspis_statement.state_only_poseidon.external_linear_lazy.closure)
  := do
  let (a, i) := c
  let a1 ← Array.index_usize a 0#usize
  let i1 ← Array.index_usize a1 tupled_args
  let a2 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i1)
  let a3 ← Array.index_usize a 1#usize
  let i2 ← Array.index_usize a3 tupled_args
  let b ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i2)
  let a4 ← Array.index_usize a 2#usize
  let i3 ← Array.index_usize a4 tupled_args
  let c1 ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i3)
  let a5 ← Array.index_usize a 3#usize
  let i4 ← Array.index_usize a5 tupled_args
  let d ← Aeneas.Std.lift (core.convert.num.FromU64U32.from i4)
  match i.val with
  | 0 =>
    let i5 ← 2#u64 * a2
    let i6 ← 3#u64 * b
    let i7 ← i5 + i6
    let i8 ← i7 + c1
    let i9 ← i8 + d
    ok (i9, c)
  | 1 =>
    let i5 ← 2#u64 * b
    let i6 ← a2 + i5
    let i7 ← 3#u64 * c1
    let i8 ← i6 + i7
    let i9 ← i8 + d
    ok (i9, c)
  | 2 =>
    let i5 ← a2 + b
    let i6 ← 2#u64 * c1
    let i7 ← i5 + i6
    let i8 ← 3#u64 * d
    let i9 ← i7 + i8
    ok (i9, c)
  | 3 =>
    let i5 ← 3#u64 * a2
    let i6 ← i5 + b
    let i7 ← i6 + c1
    let i8 ← 2#u64 * d
    let i9 ← i7 + i8
    ok (i9, c)
  | _ => fail panic

/-- [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 157:43-157:49
    Name pattern: [aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>}::call_once] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::external_linear_lazy::{core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>}::call_once"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : aspis_statement.state_only_poseidon.external_linear_lazy.closure)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 157:43-157:49
    Name pattern: [core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  aspis_statement.state_only_poseidon.external_linear_lazy.closure Std.Usize
  Std.U64 := {
  call_once :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_statement::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_statement::state_only_poseidon::external_linear_lazy::closure<'_0, '_1>}]
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 157:43-157:49
    Name pattern: [core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_statement::state_only_poseidon::external_linear_lazy::closure<'0, '1>, (usize), u64>"]
def
  aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  aspis_statement.state_only_poseidon.external_linear_lazy.closure Std.Usize
  Std.U64 := {
  FnOnceInst :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    aspis_statement.state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}


end V7Tag73CurrentHelpersOpaque
