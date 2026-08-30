import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk08

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::query]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 190:4-190:75
    Name pattern: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::query]
    Visibility: public -/
@[rust_fun
  "aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::query"]
def aspis_core.v7_onefold.V7CompactOneFoldWire.query
  (self : aspis_core.v7_onefold.V7CompactOneFoldWire) (ordinal : Std.Usize) :
  Result (Option aspis_core.v7_onefold.V7CompactQueryRecord)
  := do
  if ordinal >= aspis_core.v6_onefold.V6_QUERY_COUNT
  then ok none
  else
    let i ← aspis_core.v7_onefold.V7_COMPACT_QUERY_BYTES
    let start ← ordinal * i
    let i1 ← aspis_core.v7_onefold.V7_COMPACT_C1_BYTES_PER_QUERY
    let c1_end ← start + i1
    let i2 ← aspis_core.v7_onefold.V7_COMPACT_C2_BYTES_PER_QUERY
    let c2_end ← c1_end + i2
    let end1 ← c2_end + aspis_core.v7_onefold.V7_COMPACT_PRIVATE_SALT_BYTES
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) self.query_section { start, «end» := c1_end }
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) self.query_section { start := c1_end, «end» := c2_end }
    let s2 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) self.query_section { start := c2_end, «end» := end1 }
    let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s2
    let o ← core.result.Result.ok r
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (some { c1_packed := s, c2_packed := s1, salt := val })
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        aspis_core.v7_onefold.V7CompactQueryRecord residual

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnMut<(&'_ [(u32, usize)],), bool> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2}::call_mut]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 216:70-216:76
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>}::call_mut] -/
@[rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>}::call_mut"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
  (c : aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2)
  (tupled_args : Slice (Std.U32 × Std.Usize)) :
  Result (Bool ×
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2)
  := do
  let (i, _) ← Slice.index_usize tupled_args 0#usize
  let (i1, _) ← Slice.index_usize tupled_args 1#usize
  ok (i = i1, c)

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnOnce<(&'_ [(u32, usize)],), bool> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 216:70-216:76
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>}::call_once"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedSlicePairU32UsizeBool.call_once
  (c : aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2)
  (s : Slice (Std.U32 × Std.Usize)) :
  Result Bool
  := do
  let (b, _) ←
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
      c s
  ok b

/-- Trait implementation: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnOnce<(&'_ [(u32, usize)],), bool> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 216:70-216:76
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedSlicePairU32UsizeBool
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2 (Slice
  (Std.U32 × Std.Usize)) Bool := {
  call_once :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedSlicePairU32UsizeBool.call_once
}

/-- Trait implementation: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnMut<(&'_ [(u32, usize)],), bool> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 216:70-216:76
    Name pattern: [core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#2, (&'_ [(u32, usize)]), bool>"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool
  : core.ops.function.FnMut
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2 (Slice
  (Std.U32 × Std.Usize)) Bool := {
  FnOnceInst :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedSlicePairU32UsizeBool
  call_mut :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
}

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnMut<(&'_ (u32, usize),), u32> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1}::call_mut]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 215:31-215:38
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>}::call_mut] -/
@[rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>}::call_mut"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32.call_mut
  (c : aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1)
  (tupled_args : (Std.U32 × Std.Usize)) :
  Result (Std.U32 ×
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1)
  := do
  let (i, _) := tupled_args
  ok (i, c)

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnOnce<(&'_ (u32, usize),), u32> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 215:31-215:38
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>}::call_once"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedPairU32UsizeU32.call_once
  (c : aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1)
  (p : (Std.U32 × Std.Usize)) :
  Result Std.U32
  := do
  let (i, _) ←
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32.call_mut
      c p
  ok i

/-- Trait implementation: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnOnce<(&'_ (u32, usize),), u32> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 215:31-215:38
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedPairU32UsizeU32
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1 (Std.U32
  × Std.Usize) Std.U32 := {
  call_once :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedPairU32UsizeU32.call_once
}

/-- Trait implementation: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnMut<(&'_ (u32, usize),), u32> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 215:31-215:38
    Name pattern: [core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure#1, (&'_ (u32, usize)), u32>"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
  : core.ops.function.FnMut
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1 (Std.U32
  × Std.Usize) Std.U32 := {
  FnOnceInst :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedPairU32UsizeU32
  call_mut :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32.call_mut
}

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnMut<(usize,), (u32, usize)> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 214:29-214:38
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>}::call_mut] -/
@[rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>}::call_mut"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnMutTupleUsizePairU32Usize.call_mut
  (c : aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure)
  (tupled_args : Std.Usize) :
  Result ((Std.U32 × Std.Usize) ×
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure)
  := do
  let i ← Array.index_usize c tupled_args
  ok ((i, tupled_args), c)

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnOnce<(usize,), (u32, usize)> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'_0>}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 214:29-214:38
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>}::call_once"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePairU32Usize.call_once
  (c : aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure)
  (i : Std.Usize) :
  Result (Std.U32 × Std.Usize)
  := do
  let (p, _) ←
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnMutTupleUsizePairU32Usize.call_mut
      c i
  ok p

/-- Trait implementation: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnOnce<(usize,), (u32, usize)> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'_0>}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 214:29-214:38
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePairU32Usize
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure Std.Usize
  (Std.U32 × Std.Usize) := {
  call_once :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePairU32Usize.call_once
}

/-- Trait implementation: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::{impl core::ops::function::FnMut<(usize,), (u32, usize)> for aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'_0>}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 214:29-214:38
    Name pattern: [core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings::closure<'0>, (usize), (u32, usize)>"]
def
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnMutTupleUsizePairU32Usize
  : core.ops.function.FnMut
  aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure Std.Usize
  (Std.U32 × Std.Usize) := {
  FnOnceInst :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePairU32Usize
  call_mut :=
    aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnMutTupleUsizePairU32Usize.call_mut
}

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings]: loop body 0:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 223:4-250:1
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings"]
def aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings_loop.body
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
  (iter : core.array.iter.IntoIter (Std.U32 × Std.Usize) 16#usize)
  (combined : Array (Array aspis_core.field.QM31 4#usize) 16#usize)
  (entries : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) :
  Result (ControlFlow ((core.array.iter.IntoIter (Std.U32 × Std.Usize)
    16#usize) × (Array (Array aspis_core.field.QM31 4#usize) 16#usize) ×
    (alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
    26#usize)))) (core.result.Result (Array (Array aspis_core.field.QM31
    4#usize) 16#usize) aspis_core.v6_onefold.V6WireError))
  := do
  let (o, iter1) ←
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter
  match o with
  | none =>
    let level :=
      alloc.vec.Vec.with_capacity (Std.U32 × (Array Std.U8 26#usize) × (Array
        Std.U8 26#usize)) aspis_core.v6_onefold.V6_QUERY_COUNT
    let next :=
      alloc.vec.Vec.with_capacity (Std.U32 × (Array Std.U8 26#usize) × (Array
        Std.U8 26#usize)) aspis_core.v6_onefold.V6_QUERY_COUNT
    let s := alloc.vec.Vec.deref entries
    let (b, _, _) ←
      aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes hash
        (wire.c1_root, wire.c2_root) 18#u32 s (wire.c1_frontier,
        wire.c2_frontier) level next
    if b
    then ok (done (core.result.Result.Ok combined))
    else
      ok (done (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.MerkleMismatch))
  | some p =>
    let (query, ordinal) := p
    let o1 ← aspis_core.v7_onefold.V7CompactOneFoldWire.query wire ordinal
    let r ←
      core.option.Option.ok_or o1
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue vcqr =>
      let r1 ←
        aspis_core.v6_onefold.gamma_combine_v6_packed_layer0 vcqr.c1_packed
          vcqr.c2_packed powers
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let a ← Array.update combined ordinal val
        let a1 ←
          aspis_core.v7_merkle208.private_leaf_hash_v7 hash
            aspis_core.v7_merkle208.V7_C1_TREE_TAG vcqr.c1_packed vcqr.salt
        let a2 ←
          aspis_core.v7_merkle208.private_leaf_hash_v7 hash
            aspis_core.v7_merkle208.V7_C2_TREE_TAG vcqr.c2_packed vcqr.salt
        let entries1 ← alloc.vec.Vec.push entries (query, a1, a2)
        ok (cont (iter1, a, entries1))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let return_capture ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array (Array aspis_core.field.QM31 4#usize) 16#usize)
            (core.convert.FromSame aspis_core.v6_onefold.V6WireError) residual
        ok (done return_capture)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array (Array aspis_core.field.QM31 4#usize) 16#usize)
          (core.convert.FromSame aspis_core.v6_onefold.V6WireError) residual
      ok (done return_capture)

/-- [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings]: loop 0:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 223:4-250:1
    Name pattern: [aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::v7_onefold::verify_and_gamma_combine_v7_openings"]
def aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings_loop
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (iter : core.array.iter.IntoIter (Std.U32 × Std.Usize) 16#usize)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
  (combined : Array (Array aspis_core.field.QM31 4#usize) 16#usize)
  (entries : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) :
  Result (core.result.Result (Array (Array aspis_core.field.QM31 4#usize)
    16#usize) aspis_core.v6_onefold.V6WireError)
  := do
  loop
    (fun (iter1, combined1, entries1) =>
      aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings_loop.body wire
      hash powers iter1 combined1 entries1)
    (iter, combined, entries)


end V7Tag73CurrentHelpersOpaque
