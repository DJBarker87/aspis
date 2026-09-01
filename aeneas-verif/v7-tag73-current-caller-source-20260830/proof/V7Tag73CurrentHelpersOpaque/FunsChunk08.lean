import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk07

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates]: loop body 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 918:4-931:5
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates"]
def aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop.body
  (points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  aspis_core.circle_fri.BaseCirclePoint))
  (denominators : Array aspis_core.field.M31 32#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter aspis_core.circle_fri.BaseCirclePoint)) × (Array
    aspis_core.field.M31 32#usize)) (core.result.Result
    aspis_core.v6_onefold.V6OneFoldCoordinates
    aspis_core.v6_onefold.V6WireError))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter
      aspis_core.circle_fri.BaseCirclePoint) iter
  match o with
  | none =>
    let inverses := Array.repeat 32#usize aspis_core.field.M31.ZERO
    let s ← lift (Array.to_slice denominators)
    let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut inverses)
    let s2 ← aspis_core.field.m31_batch_inverse s s1
    let inverses1 := to_slice_mut_back s2
    let m ← Array.index_usize denominators 0#usize
    let m1 ← Array.index_usize inverses1 0#usize
    let m2 ← aspis_core.field.M31.mul m m1
    let b ←
      core.cmp.PartialEq.ne.trait_default
        aspis_core.field.M31.Insts.CoreCmpPartialEqM31 m2
        aspis_core.field.M31.ONE
    if b
    then
      ok (done (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule))
    else
      let a ←
        core.array.from_fn 16#usize
          aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
          inverses1
      let a1 ←
        core.array.from_fn 16#usize
          aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
          inverses1
      let a2 ←
        core.array.from_fn 16#usize
          aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31
          points
      ok (done (core.result.Result.Ok
        { inv_2x := a, inv_2y := a1, line_x := a2 }))
  | some p =>
    let (ordinal, point) := p
    let x ← aspis_core.field.M31.double point.x
    let y ← aspis_core.field.M31.double point.y
    let b ← aspis_core.field.M31.is_zero x
    if b
    then
      ok (done (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule))
    else
      let b1 ← aspis_core.field.M31.is_zero y
      if b1
      then
        ok (done (core.result.Result.Err
          aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule))
      else
        let i ← 2#usize * ordinal
        let denominators1 ← Array.update denominators i x
        let i1 ← i + 1#usize
        let a ← Array.update denominators1 i1 y
        ok (cont (iter1, a))

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates]: loop 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 918:4-931:5
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::prepare_v6_onefold_coordinates"]
def aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  aspis_core.circle_fri.BaseCirclePoint))
  (points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (denominators : Array aspis_core.field.M31 32#usize) :
  Result (core.result.Result aspis_core.v6_onefold.V6OneFoldCoordinates
    aspis_core.v6_onefold.V6WireError)
  := do
  loop
    (fun (iter1, denominators1) =>
      aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop.body points
      iter1 denominators1)
    (iter, denominators)

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 912:0-914:46
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates]
    Visibility: public -/
@[rust_fun "aspis_core::v6_onefold::prepare_v6_onefold_coordinates"]
def aspis_core.v6_onefold.prepare_v6_onefold_coordinates
  (queries : Array Std.U32 16#usize) :
  Result (core.result.Result aspis_core.v6_onefold.V6OneFoldCoordinates
    aspis_core.v6_onefold.V6WireError)
  := do
  let s ← lift (Array.to_slice queries)
  let r ← aspis_core.circle_fri.selected_circle_fiber_points_shared 20#u32 s
  let r1 ←
    core.result.Result.map_err
      aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure.Insts.CoreOpsFunctionFnOnceTupleCircleFriErrorV6WireError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let denominators := Array.repeat 32#usize aspis_core.field.M31.ZERO
    let s1 := alloc.vec.Vec.deref val
    let i ← core.slice.Slice.iter s1
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter
        aspis_core.circle_fri.BaseCirclePoint) i
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates_loop iter val
      denominators
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.v6_onefold.V6OneFoldCoordinates (core.convert.FromSame
      aspis_core.v6_onefold.V6WireError) residual

/-- [aspis_core::v6_onefold::fold_v6_onefold_queries::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'_0, '_1, '_2>}::call_mut]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 975:25-975:34
    Name pattern: [aspis_core::v6_onefold::fold_v6_onefold_queries::{core::ops::function::FnMut<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>}::call_mut] -/
@[rust_fun
  "aspis_core::v6_onefold::fold_v6_onefold_queries::{core::ops::function::FnMut<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>}::call_mut"]
def
  aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : aspis_core.v6_onefold.fold_v6_onefold_queries.closure)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 ×
    aspis_core.v6_onefold.fold_v6_onefold_queries.closure)
  := do
  let (a, a1, vofc) := c
  let a2 ← Array.index_usize a tupled_args
  let m ← Array.index_usize vofc.inv_2x tupled_args
  let m1 ← Array.index_usize vofc.inv_2y tupled_args
  let q ←
    aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
      a2 a1 m m1
  ok (q, c)

/-- [aspis_core::v6_onefold::fold_v6_onefold_queries::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'_0, '_1, '_2>}::call_once]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 975:25-975:34
    Name pattern: [aspis_core::v6_onefold::fold_v6_onefold_queries::{core::ops::function::FnOnce<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>}::call_once] -/
@[rust_fun
  "aspis_core::v6_onefold::fold_v6_onefold_queries::{core::ops::function::FnOnce<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>}::call_once"]
def
  aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : aspis_core.v6_onefold.fold_v6_onefold_queries.closure) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_core::v6_onefold::fold_v6_onefold_queries::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'_0, '_1, '_2>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 975:25-975:34
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>"]
def
  aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  aspis_core.v6_onefold.fold_v6_onefold_queries.closure Std.Usize
  aspis_core.field.QM31 := {
  call_once :=
    aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_core::v6_onefold::fold_v6_onefold_queries::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'_0, '_1, '_2>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 975:25-975:34
    Name pattern: [core::ops::function::FnMut<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v6_onefold::fold_v6_onefold_queries::closure<'0, '1, '2>, (usize), aspis_core::field::QM31>"]
def
  aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  aspis_core.v6_onefold.fold_v6_onefold_queries.closure Std.Usize
  aspis_core.field.QM31 := {
  FnOnceInst :=
    aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_core::v6_onefold::fold_v6_onefold_queries]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 964:0-968:27
    Name pattern: [aspis_core::v6_onefold::fold_v6_onefold_queries]
    Visibility: public -/
@[rust_fun "aspis_core::v6_onefold::fold_v6_onefold_queries"]
def aspis_core.v6_onefold.fold_v6_onefold_queries
  (combined : Array (Array aspis_core.field.QM31 4#usize) 16#usize)
  (coordinates : aspis_core.v6_onefold.V6OneFoldCoordinates)
  (alpha : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let alpha_squared ← aspis_core.field.QM31.square alpha
  let pqm ← aspis_core.field.PreparedQm31Multiplier.new alpha
  let pqm1 ← aspis_core.field.PreparedQm31Multiplier.new alpha_squared
  let q ← aspis_core.field.QM31.mul alpha_squared alpha
  let pqm2 ← aspis_core.field.PreparedQm31Multiplier.new q
  core.array.from_fn 16#usize
    aspis_core.v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    (combined, Array.make 3#usize [ pqm, pqm1, pqm2 ], coordinates)

/-- [aspis_core::v6_query_batch::V6_QUERY_BATCH_COUNT]
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 11:0-11:37
    Name pattern: [aspis_core::v6_query_batch::V6_QUERY_BATCH_COUNT]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v6_query_batch::V6_QUERY_BATCH_COUNT"]
def aspis_core.v6_query_batch.V6_QUERY_BATCH_COUNT : Std.Usize := 16#usize

/-- [aspis_core::v6_query_batch::V6_QUERY_BATCH_TREE_DEPTH]
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 16:0-16:39
    Name pattern: [aspis_core::v6_query_batch::V6_QUERY_BATCH_TREE_DEPTH]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v6_query_batch::V6_QUERY_BATCH_TREE_DEPTH"]
def aspis_core.v6_query_batch.V6_QUERY_BATCH_TREE_DEPTH : Std.U8 := 18#u8

/-- [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_query_batch::V6QueryBatchError> for aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure#1}::call_once]:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 110:17-110:20
    Name pattern: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure#1, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_query_batch::V6QueryBatchError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure#1, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_query_batch::V6QueryBatchError>}::call_once"]
def
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6QueryBatchError.call_once
  (c :
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1)
  (tupled_args : aspis_core.sumcheck.TensorWeightError) :
  Result aspis_core.v6_query_batch.V6QueryBatchError
  := do
  ok aspis_core.v6_query_batch.V6QueryBatchError.WeightShape

/-- Trait implementation: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_query_batch::V6QueryBatchError> for aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure#1}]
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 110:17-110:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure#1, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_query_batch::V6QueryBatchError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure#1, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_query_batch::V6QueryBatchError>"]
def
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6QueryBatchError
  : core.ops.function.FnOnce
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1
  aspis_core.sumcheck.TensorWeightError
  aspis_core.v6_query_batch.V6QueryBatchError := {
  call_once :=
    aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6QueryBatchError.call_once
}

/-- [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{impl core::ops::function::FnMut<(&'_ [u32],), bool> for aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure}::call_mut]:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 97:33-97:39
    Name pattern: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{core::ops::function::FnMut<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>}::call_mut] -/
@[rust_fun
  "aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{core::ops::function::FnMut<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>}::call_mut"]
def
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut
  (c :
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure)
  (tupled_args : Slice Std.U32) :
  Result (Bool ×
    aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure)
  := do
  let i ← Slice.index_usize tupled_args 0#usize
  let i1 ← Slice.index_usize tupled_args 1#usize
  ok (i = i1, c)

/-- [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{impl core::ops::function::FnOnce<(&'_ [u32],), bool> for aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure}::call_once]:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 97:33-97:39
    Name pattern: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>}::call_once] -/
@[rust_fun
  "aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>}::call_once"]
def
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool.call_once
  (c :
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure)
  (s : Slice Std.U32) :
  Result Bool
  := do
  let (b, _) ←
    aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut
      c s
  ok b

/-- Trait implementation: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{impl core::ops::function::FnOnce<(&'_ [u32],), bool> for aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure}]
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 97:33-97:39
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>"]
def
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool
  : core.ops.function.FnOnce
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure
  (Slice Std.U32) Bool := {
  call_once :=
    aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool.call_once
}

/-- Trait implementation: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::{impl core::ops::function::FnMut<(&'_ [u32],), bool> for aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure}]
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 97:33-97:39
    Name pattern: [core::ops::function::FnMut<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale::closure, (&'_ [u32]), bool>"]
def
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
  : core.ops.function.FnMut
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure
  (Slice Std.U32) Bool := {
  FnOnceInst :=
    aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool
  call_mut :=
    aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut
}

/-- [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale]: loop body 0:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 105:4-114:1
    Name pattern: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale"]
def
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
  (weights : aspis_core.sumcheck.WeightAccumulator)
  (running_claim : aspis_core.field.QM31)
  (authenticated : aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
  (prepared_rho : aspis_core.field.PreparedQm31Multiplier)
  (iter : core.ops.range.Range Std.Usize)
  (scales : Array aspis_core.field.QM31 16#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 16#usize)) ((core.result.Result aspis_core.field.QM31
    aspis_core.v6_query_batch.V6QueryBatchError) ×
    aspis_core.sumcheck.WeightAccumulator × aspis_core.field.QM31))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let s ← lift (Array.to_slice scales)
    let s1 ← lift (Array.to_slice authenticated.line_x)
    let (r, weights1) ←
      aspis_core.sumcheck.WeightAccumulator.add_line_m31_batch weights s s1
    let r1 ←
      core.result.Result.map_err
        aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6QueryBatchError
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s2 ← lift (Array.to_slice scales)
      let s3 ← lift (Array.to_slice authenticated.values)
      let claim_increment ← aspis_core.field.qm31_dot s2 s3
      let running_claim1 ←
        aspis_core.field.QM31.add running_claim claim_increment
      ok (done (core.result.Result.Ok claim_increment, weights1,
        running_claim1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame
          aspis_core.v6_query_batch.V6QueryBatchError) residual
      ok (done (return_capture, weights1, running_claim))
  | some ordinal =>
    let i ← ordinal - 1#usize
    let q ← Array.index_usize scales i
    let q1 ← aspis_core.field.PreparedQm31Multiplier.mul prepared_rho q
    let a ← Array.update scales ordinal q1
    ok (cont (iter1, a))

/-- [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale]: loop 0:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 105:4-114:1
    Name pattern: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale] -/
@[rust_loop, rust_fun
  "aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale"]
def aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale_loop
  (iter : core.ops.range.Range Std.Usize)
  (weights : aspis_core.sumcheck.WeightAccumulator)
  (running_claim : aspis_core.field.QM31)
  (authenticated : aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
  (scales : Array aspis_core.field.QM31 16#usize)
  (prepared_rho : aspis_core.field.PreparedQm31Multiplier) :
  Result ((core.result.Result aspis_core.field.QM31
    aspis_core.v6_query_batch.V6QueryBatchError) ×
    aspis_core.sumcheck.WeightAccumulator × aspis_core.field.QM31)
  := do
  loop
    (fun (iter1, scales1) =>
      aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
      weights running_claim authenticated prepared_rho iter1 scales1)
    (iter, scales)

/-- [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale]:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 86:0-93:36
    Name pattern: [aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale] -/
@[rust_fun
  "aspis_core::v6_query_batch::add_final256_query_batch_with_initial_scale"]
def aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale
  (weights : aspis_core.sumcheck.WeightAccumulator)
  (running_claim : aspis_core.field.QM31) (queries : Array Std.U32 16#usize)
  (authenticated : aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
  (rho : aspis_core.field.QM31) (initial_scale : aspis_core.field.QM31) :
  Result ((core.result.Result aspis_core.field.QM31
    aspis_core.v6_query_batch.V6QueryBatchError) ×
    aspis_core.sumcheck.WeightAccumulator × aspis_core.field.QM31)
  := do
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut queries)
  let s1 ← core.slice.Slice.sort_unstable core.cmp.OrdU32 s
  let queries1 := to_slice_mut_back s1
  let i ← aspis_core.v6_query_batch.V6_QUERY_BATCH_COUNT - 1#usize
  let i1 ← Array.index_usize queries1 i
  let i2 ← 1#u32 <<< aspis_core.v6_query_batch.V6_QUERY_BATCH_TREE_DEPTH
  if i1 >= i2
  then
    ok (core.result.Result.Err
      aspis_core.v6_query_batch.V6QueryBatchError.InvalidQuerySchedule,
      weights, running_claim)
  else
    let s2 ← lift (Array.to_slice queries1)
    let w ← core.slice.Slice.windows s2 2#usize
    let (b, _) ←
      core.iter.traits.iterator.Iterator.any.default
        (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
        Std.U32)
        aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
        w ()
    if b
    then
      ok (core.result.Result.Err
        aspis_core.v6_query_batch.V6QueryBatchError.InvalidQuerySchedule,
        weights, running_claim)
    else
      let scales := Array.repeat 16#usize aspis_core.field.QM31.ZERO
      let a ← Array.update scales 0#usize initial_scale
      let prepared_rho ← aspis_core.field.PreparedQm31Multiplier.new rho
      aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale_loop
        {
          start := 1#usize,
          «end» := aspis_core.v6_query_batch.V6_QUERY_BATCH_COUNT
        } weights running_claim authenticated a prepared_rho

/-- [aspis_core::v6_query_batch::add_v6_final256_query_batch]:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 44:0-50:36
    Name pattern: [aspis_core::v6_query_batch::add_v6_final256_query_batch]
    Visibility: public -/
@[rust_fun "aspis_core::v6_query_batch::add_v6_final256_query_batch"]
def aspis_core.v6_query_batch.add_v6_final256_query_batch
  (weights : aspis_core.sumcheck.WeightAccumulator)
  (running_claim : aspis_core.field.QM31) (queries : Array Std.U32 16#usize)
  (authenticated : aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
  (rho : aspis_core.field.QM31) :
  Result ((core.result.Result aspis_core.field.QM31
    aspis_core.v6_query_batch.V6QueryBatchError) ×
    aspis_core.sumcheck.WeightAccumulator × aspis_core.field.QM31)
  := do
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale weights
    running_claim queries authenticated rho aspis_core.field.QM31.ONE

/-- [aspis_core::v6_query_batch::add_v7_final256_query_batch_shifted]:
    Source: 'crates/aspis-core/src/v6_query_batch.rs', lines 69:0-75:36
    Name pattern: [aspis_core::v6_query_batch::add_v7_final256_query_batch_shifted]
    Visibility: public -/
@[rust_fun "aspis_core::v6_query_batch::add_v7_final256_query_batch_shifted"]
def aspis_core.v6_query_batch.add_v7_final256_query_batch_shifted
  (weights : aspis_core.sumcheck.WeightAccumulator)
  (running_claim : aspis_core.field.QM31) (queries : Array Std.U32 16#usize)
  (authenticated : aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
  (rho : aspis_core.field.QM31) :
  Result ((core.result.Result aspis_core.field.QM31
    aspis_core.v6_query_batch.V6QueryBatchError) ×
    aspis_core.sumcheck.WeightAccumulator × aspis_core.field.QM31)
  := do
  aspis_core.v6_query_batch.add_final256_query_batch_with_initial_scale weights
    running_claim queries authenticated rho rho

/-- [aspis_core::v6_transcript::V7_ROOT_SALT_DOMAIN]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 67:0-67:32
    Name pattern: [aspis_core::v6_transcript::V7_ROOT_SALT_DOMAIN] -/
@[global_simps, irreducible, rust_const
  "aspis_core::v6_transcript::V7_ROOT_SALT_DOMAIN"]
def aspis_core.v6_transcript.V7_ROOT_SALT_DOMAIN : Slice Std.U8 :=
  Array.to_slice
    (Array.make 28#usize [
      97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 118#u8, 55#u8, 45#u8,
      112#u8, 117#u8, 98#u8, 108#u8, 105#u8, 99#u8, 45#u8, 114#u8, 111#u8,
      111#u8, 116#u8, 45#u8, 115#u8, 97#u8, 108#u8, 116#u8, 45#u8, 118#u8,
      49#u8
      ])

/-- [aspis_core::v6_transcript::V6TranscriptError::Wire]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 129:4-129:8
    Name pattern: [aspis_core::v6_transcript::V6TranscriptError::Wire] -/
@[rust_fun "aspis_core::v6_transcript::V6TranscriptError::Wire"]
def aspis_core.v6_transcript.V6TranscriptError.Wire_fn
  (vwe : aspis_core.v6_onefold.V6WireError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok (aspis_core.v6_transcript.V6TranscriptError.Wire vwe)

/-- [aspis_core::v6_transcript::{impl core::convert::From<aspis_core::v6_onefold::V6WireError> for aspis_core::v6_transcript::V6TranscriptError}::from]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 154:4-154:39
    Name pattern: [aspis_core::v6_transcript::{core::convert::From<aspis_core::v6_transcript::V6TranscriptError, aspis_core::v6_onefold::V6WireError>}::from]
    Visibility: public -/
@[rust_fun
  "aspis_core::v6_transcript::{core::convert::From<aspis_core::v6_transcript::V6TranscriptError, aspis_core::v6_onefold::V6WireError>}::from"]
def
  aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
  (error : aspis_core.v6_onefold.V6WireError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok (aspis_core.v6_transcript.V6TranscriptError.Wire error)

/-- Trait implementation: [aspis_core::v6_transcript::{impl core::convert::From<aspis_core::v6_onefold::V6WireError> for aspis_core::v6_transcript::V6TranscriptError}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 153:0-153:44
    Name pattern: [core::convert::From<aspis_core::v6_transcript::V6TranscriptError, aspis_core::v6_onefold::V6WireError>] -/
@[reducible, rust_trait_impl
  "core::convert::From<aspis_core::v6_transcript::V6TranscriptError, aspis_core::v6_onefold::V6WireError>"]
def aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
  : core.convert.From aspis_core.v6_transcript.V6TranscriptError
  aspis_core.v6_onefold.V6WireError := {
  «from» :=
    aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from
}

/-- [aspis_core::v6_transcript::profile_root_salt]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 204:0-210:13
    Name pattern: [aspis_core::v6_transcript::profile_root_salt] -/
@[rust_fun "aspis_core::v6_transcript::profile_root_salt"]
def aspis_core.v6_transcript.profile_root_salt
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (domain : Slice Std.U8) (profile_binding : Array Std.U8 32#usize)
  (context : aspis_core.v6_transcript.V6TranscriptContext) (tree_tag : Std.U8)
  :
  Result (Array Std.U8 32#usize)
  := do
  let s ← lift (Array.to_slice profile_binding)
  let s1 ← lift (Array.to_slice context.program_id)
  let s2 ← lift (Array.to_slice context.release_binding)
  let s3 ← lift (Array.to_slice context.statement_digest)
  let s4 ← lift (Array.to_slice context.attempt_id)
  let s5 ← lift (Array.to_slice (Array.make 1#usize [ tree_tag ]))
  let s6 ←
    lift (Array.to_slice
      (Array.make 7#usize [ domain, s, s1, s2, s3, s4, s5 ]))
  hash s6

/-- [aspis_core::v7_onefold::V7_COMPACT_PROFILE_BINDING]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 38:0-38:46
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_PROFILE_BINDING]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_PROFILE_BINDING"]
def aspis_core.v7_onefold.V7_COMPACT_PROFILE_BINDING : Array Std.U8 32#usize :=
  Array.make 32#usize [
    65#u8, 86#u8, 55#u8, 79#u8, 70#u8, 48#u8, 48#u8, 49#u8, 26#u8, 3#u8, 10#u8,
    16#u8, 203#u8, 0#u8, 26#u8, 32#u8, 27#u8, 4#u8, 6#u8, 35#u8, 31#u8, 34#u8,
    113#u8, 241#u8, 129#u8, 2#u8, 8#u8, 20#u8, 18#u8, 1#u8, 64#u8, 1#u8
    ]

/-- [aspis_core::v6_transcript::v7_public_root_salt]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 232:0-232:93
    Name pattern: [aspis_core::v6_transcript::v7_public_root_salt] -/
@[rust_fun "aspis_core::v6_transcript::v7_public_root_salt"]
def aspis_core.v6_transcript.v7_public_root_salt
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.v6_transcript.V6TranscriptContext) (tree_tag : Std.U8)
  :
  Result (Array Std.U8 32#usize)
  := do
  aspis_core.v6_transcript.profile_root_salt hash
    aspis_core.v6_transcript.V7_ROOT_SALT_DOMAIN
    aspis_core.v7_onefold.V7_COMPACT_PROFILE_BINDING context tree_tag

/-- [aspis_core::v7_merkle208::V7_MERKLE_DIGEST_BYTES]
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 14:0-14:39
    Name pattern: [aspis_core::v7_merkle208::V7_MERKLE_DIGEST_BYTES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_merkle208::V7_MERKLE_DIGEST_BYTES"]
def aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES : Std.Usize := 26#usize

/-- [aspis_core::v6_transcript::absorb_v7_c1_root]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 257:0-261:1
    Name pattern: [aspis_core::v6_transcript::absorb_v7_c1_root] -/
@[rust_fun "aspis_core::v6_transcript::absorb_v7_c1_root"]
def aspis_core.v6_transcript.absorb_v7_c1_root
  (transcript : aspis_core.transcript.Transcript)
  (root : Array Std.U8 26#usize) (salt : Array Std.U8 32#usize) :
  Result aspis_core.transcript.Transcript
  := do
  let record1 := Array.repeat 59#usize 0#u8
  let record2 ← Array.update record1 0#usize 0#u8
  let i ← 1#usize + aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) record2
      { start := 1#usize, «end» := i }
  let s1 ← lift (Array.to_slice root)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let record3 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) record3
      { start := i }
  let s4 ← lift (Array.to_slice salt)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let record4 := index_mut_back1 s5
  let s6 ← lift (Array.to_slice record4)
  aspis_core.transcript.Transcript.absorb transcript
    aspis_core.transcript.label.M31_CIRCLE_ROUND_ROOT s6

/-- [aspis_core::v6_transcript::absorb_v7_c2_root]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 269:0-273:1
    Name pattern: [aspis_core::v6_transcript::absorb_v7_c2_root] -/
@[rust_fun "aspis_core::v6_transcript::absorb_v7_c2_root"]
def aspis_core.v6_transcript.absorb_v7_c2_root
  (transcript : aspis_core.transcript.Transcript)
  (root : Array Std.U8 26#usize) (salt : Array Std.U8 32#usize) :
  Result aspis_core.transcript.Transcript
  := do
  let record1 := Array.repeat 58#usize 0#u8
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) record1
      { «end» := aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES }
  let s1 ← lift (Array.to_slice root)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let record2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) record2
      { start := aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES }
  let s4 ← lift (Array.to_slice salt)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let record3 := index_mut_back1 s5
  let s6 ← lift (Array.to_slice record3)
  aspis_core.transcript.Transcript.absorb transcript
    aspis_core.transcript.label.M31_CIRCLE_C2_ROOT s6

/-- [aspis_core::v7_merkle208::V7_C2_TREE_TAG]
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 17:0-17:28
    Name pattern: [aspis_core::v7_merkle208::V7_C2_TREE_TAG]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_merkle208::V7_C2_TREE_TAG"]
def aspis_core.v7_merkle208.V7_C2_TREE_TAG : Std.U8 := 241#u8

/-- [aspis_core::v7_merkle208::V7_C1_TREE_TAG]
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 16:0-16:28
    Name pattern: [aspis_core::v7_merkle208::V7_C1_TREE_TAG]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_merkle208::V7_C1_TREE_TAG"]
def aspis_core.v7_merkle208.V7_C1_TREE_TAG : Std.U8 := 113#u8

/-- [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#3}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 351:17-351:20
    Name pattern: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#3, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#3, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_3.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  (c :
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_3)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#3}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 351:17-351:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#3, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#3, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_3.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  : core.ops.function.FnOnce
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_3
  aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_3.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
}

/-- [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#2}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 346:17-346:20
    Name pattern: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#2, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#2, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_2.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  (c :
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_2)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#2}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 346:17-346:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#2, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#2, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_2.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  : core.ops.function.FnOnce
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_2
  aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_2.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
}

/-- [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#1}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 343:17-343:20
    Name pattern: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#1, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#1, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  (c :
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_1)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#1}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 343:17-343:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#1, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure#1, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  : core.ops.function.FnOnce
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_1
  aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
}

/-- [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::state_only_hiding::StateOnlyHidingScheduleError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 337:17-337:20
    Name pattern: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError.call_once
  (c :
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure)
  (tupled_args : aspis_core.state_only_hiding.StateOnlyHidingScheduleError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.HidingContext

/-- Trait implementation: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::state_only_hiding::StateOnlyHidingScheduleError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 337:17-337:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context::closure, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError
  : core.ops.function.FnOnce
  aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure
  aspis_core.state_only_hiding.StateOnlyHidingScheduleError
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError.call_once
}

/-- [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 317:0-322:85
    Name pattern: [aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context] -/
@[rust_fun
  "aspis_core::v6_transcript::begin_v7_compact_transcript_with_hiding_context"]
def aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.v6_transcript.V6TranscriptContext)
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (hiding_context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  Result (core.result.Result (aspis_core.transcript.Transcript ×
    aspis_core.field.QM31 × aspis_core.field.QM31 ×
    aspis_core.statement_sumcheck.PaymentConstraintChallenges)
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  let b ←
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      hiding_context.statement_digest context.statement_digest
  if b
  then
    ok (core.result.Result.Err
      aspis_core.v6_transcript.V6TranscriptError.HidingContext)
  else
    let b1 ←
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        hiding_context.mask_nonce context.attempt_id
    if b1
    then
      ok (core.result.Result.Err
        aspis_core.v6_transcript.V6TranscriptError.HidingContext)
    else
      let transcript ← aspis_core.transcript.Transcript.new hash
      let s ←
        lift (Array.to_slice aspis_core.v7_onefold.V7_COMPACT_PROFILE_BINDING)
      let transcript1 ←
        aspis_core.transcript.Transcript.absorb transcript
          aspis_core.transcript.label.PROFILE s
      let s1 ←
        lift (Array.to_slice aspis_core.proof.M31_CIRCLE_BASIS_DISCRIMINATOR)
      let transcript2 ←
        aspis_core.transcript.Transcript.absorb transcript1
          aspis_core.transcript.label.M31_CIRCLE_BASIS s1
      let deployment := Array.repeat 64#usize 0#u8
      let (s2, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) deployment
          { «end» := 32#usize }
      let s3 ← lift (Array.to_slice context.program_id)
      let s4 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s2 s3
      let deployment1 := index_mut_back s4
      let (s5, index_mut_back1) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) deployment1
          { start := 32#usize }
      let s6 ← lift (Array.to_slice context.release_binding)
      let s7 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s5 s6
      let deployment2 := index_mut_back1 s7
      let s8 ← lift (Array.to_slice deployment2)
      let transcript3 ←
        aspis_core.transcript.Transcript.absorb transcript2
          aspis_core.transcript.label.V7_DEPLOYMENT_CONTEXT s8
      let s9 ← lift (Array.to_slice context.statement_digest)
      let transcript4 ←
        aspis_core.transcript.Transcript.absorb transcript3
          aspis_core.transcript.label.STATEMENT s9
      let (r, transcript5) ←
        aspis_core.state_only_hiding.begin_state_only_hiding_precommit
          transcript4 hiding_context
      let r1 ←
        core.result.Result.map_err
          aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError
          r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let c1_salt ←
          aspis_core.v6_transcript.v7_public_root_salt hash context
            aspis_core.v7_merkle208.V7_C1_TREE_TAG
        let transcript6 ←
          aspis_core.v6_transcript.absorb_v7_c1_root transcript5 wire.c1_root
            c1_salt
        let (r2, transcript7) ←
          aspis_core.transcript.Transcript.challenge_qm31 transcript6
        let r3 ←
          core.result.Result.map_err
            aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
            r2 ()
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let (r4, transcript8) ←
            aspis_core.transcript.Transcript.challenge_qm31 transcript7
          let r5 ←
            core.result.Result.map_err
              aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_2.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
              r4 ()
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            let c2_salt ←
              aspis_core.v6_transcript.v7_public_root_salt hash context
                aspis_core.v7_merkle208.V7_C2_TREE_TAG
            let transcript9 ←
              aspis_core.v6_transcript.absorb_v7_c2_root transcript8
                wire.c2_root c2_salt
            let (r6, transcript10) ←
              aspis_core.state_only_sumcheck.begin_state_only_zerocheck
                transcript9
            let r7 ←
              core.result.Result.map_err
                aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context.closure_3.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
                r6 ()
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r7
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              ok (core.result.Result.Ok (transcript10, val, val1, val2))
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (aspis_core.transcript.Transcript × aspis_core.field.QM31 ×
                aspis_core.field.QM31 ×
                aspis_core.statement_sumcheck.PaymentConstraintChallenges)
                (core.convert.FromSame
                aspis_core.v6_transcript.V6TranscriptError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (aspis_core.transcript.Transcript × aspis_core.field.QM31 ×
              aspis_core.field.QM31 ×
              aspis_core.statement_sumcheck.PaymentConstraintChallenges)
              (core.convert.FromSame
              aspis_core.v6_transcript.V6TranscriptError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (aspis_core.transcript.Transcript × aspis_core.field.QM31 ×
            aspis_core.field.QM31 ×
            aspis_core.statement_sumcheck.PaymentConstraintChallenges)
            (core.convert.FromSame aspis_core.v6_transcript.V6TranscriptError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_core.transcript.Transcript × aspis_core.field.QM31 ×
          aspis_core.field.QM31 ×
          aspis_core.statement_sumcheck.PaymentConstraintChallenges)
          (core.convert.FromSame aspis_core.v6_transcript.V6TranscriptError)
          residual

/-- [aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure#1<Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 454:21-454:24
    Name pattern: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure#1<@Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure#1<@Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (c : aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure_1
  Fields) (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure#1<Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 454:21-454:24
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure#1<@Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure#1<@Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure_1 Fields)
  aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{impl core::ops::function::FnOnce<(aspis_core::state_only_hiding::StateOnlyHidingScheduleError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure<Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 405:17-405:20
    Name pattern: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure<@Fields>, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure<@Fields>, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError.call_once
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (c : aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure
  Fields)
  (tupled_args : aspis_core.state_only_hiding.StateOnlyHidingScheduleError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck::{impl core::ops::function::FnOnce<(aspis_core::state_only_hiding::StateOnlyHidingScheduleError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure<Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 405:17-405:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure<@Fields>, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::verify_compact_semantic_sumcheck::closure<@Fields>, (aspis_core::state_only_hiding::StateOnlyHidingScheduleError), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure Fields)
  aspis_core.state_only_hiding.StateOnlyHidingScheduleError
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError.call_once
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::verify_compact_semantic_sumcheck]: loop body 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 422:8-457:5
    Name pattern: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::verify_compact_semantic_sumcheck"]
def aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (transcript : aspis_core.transcript.Transcript)
  (point : Array aspis_core.field.QM31 10#usize)
  (running_claim : aspis_core.field.QM31) (round : Std.Usize)
  (pending_return : Option (core.result.Result (aspis_core.field.QM31 × (Array
  aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
  aspis_core.v6_transcript.V6TranscriptError))
  (iter : core.ops.range.Range Std.Usize) (fields : Fields)
  (polynomial : Array aspis_core.field.QM31 28#usize)
  (framed : Array Std.U8 433#usize) (tail_limbs : Array Std.U64 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Fields × (Array
    aspis_core.field.QM31 28#usize) × (Array Std.U8 433#usize) × (Array
    Std.U64 4#usize)) (aspis_core.transcript.Transcript × Fields × (Array
    aspis_core.field.QM31 10#usize) × aspis_core.field.QM31 × (Option
    (core.result.Result (aspis_core.field.QM31 × (Array aspis_core.field.QM31
    10#usize) × aspis_core.field.QM31)
    aspis_core.v6_transcript.V6TranscriptError)) × Std.U32))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let i ← Array.index_usize tail_limbs 0#usize
    let m ← aspis_core.field.M31.reduce_u64 i
    let i1 ← Array.index_usize tail_limbs 1#usize
    let m1 ← aspis_core.field.M31.reduce_u64 i1
    let c ← aspis_core.field.CM31.new m m1
    let i2 ← Array.index_usize tail_limbs 2#usize
    let m2 ← aspis_core.field.M31.reduce_u64 i2
    let i3 ← Array.index_usize tail_limbs 3#usize
    let m3 ← aspis_core.field.M31.reduce_u64 i3
    let c1 ← aspis_core.field.CM31.new m2 m3
    let q ← aspis_core.field.QM31.sub running_claim { c0 := c, c1 }
    let polynomial1 ← Array.update polynomial 1#usize q
    let left_val ←
      aspis_core.state_only_sumcheck.state_only_boundary_sum polynomial1
    let b ←
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq left_val
        running_claim
    massert b
    let s ← lift (Array.to_slice framed)
    let transcript1 ←
      aspis_core.transcript.Transcript.absorb transcript
        aspis_core.transcript.label.V6_COMPACT_SEMANTIC_ROUND s
    let (r, transcript2) ←
      aspis_core.transcript.Transcript.challenge_qm31 transcript1
    let r1 ←
      core.result.Result.map_err
        (aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
        v6_onefoldV6FixedFieldStreamInst) r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let running_claim1 ←
        aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
          polynomial1 val
      let a ← Array.update point round val
      ok (done (transcript2, fields, a, running_claim1, pending_return, 1#u32))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
          aspis_core.field.QM31) (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
      ok (done (transcript2, fields, point, running_claim, some return_capture,
        0#u32))
  | some sent =>
    let coefficient ← sent + 1#usize
    let (r, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let a ←
        Array.update polynomial coefficient
          ({
             c0 := { a := val.c0.a, b := val.c0.b },
             c1 := { a := val.c1.a, b := val.c1.b }
           } : aspis_core.field.QM31)
      let i ← sent * 16#usize
      let i1 ← 1#usize + i
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) framed
          { start := i1 }
      let (s1, index_mut_back1) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s
          { «end» := 16#usize }
      let s2 ← aspis_core.field.QM31.write_le_bytes val s1
      let s3 := index_mut_back1 s2
      let framed1 := index_mut_back s3
      let i2 := val.c0.a
      let i3 ← lift (core.convert.num.FromU64U32.from i2)
      let i4 ← Array.index_usize tail_limbs 0#usize
      let i5 ← i4 + i3
      let tail_limbs1 ← Array.update tail_limbs 0#usize i5
      let i6 := val.c0.b
      let i7 ← lift (core.convert.num.FromU64U32.from i6)
      let i8 ← Array.index_usize tail_limbs1 1#usize
      let i9 ← i8 + i7
      let tail_limbs2 ← Array.update tail_limbs1 1#usize i9
      let i10 := val.c1.a
      let i11 ← lift (core.convert.num.FromU64U32.from i10)
      let i12 ← Array.index_usize tail_limbs2 2#usize
      let i13 ← i12 + i11
      let tail_limbs3 ← Array.update tail_limbs2 2#usize i13
      let i14 := val.c1.b
      let i15 ← lift (core.convert.num.FromU64U32.from i14)
      let i16 ← Array.index_usize tail_limbs3 3#usize
      let i17 ← i16 + i15
      let a1 ← Array.update tail_limbs3 3#usize i17
      ok (cont (iter1, fields1, a, framed1, a1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
          aspis_core.field.QM31)
          aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
          residual
      ok (done (transcript, fields1, point, running_claim, some return_capture,
        0#u32))

/-- [aspis_core::v6_transcript::verify_compact_semantic_sumcheck]: loop 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 422:8-457:5
    Name pattern: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck] -/
@[rust_loop, rust_fun
  "aspis_core::v6_transcript::verify_compact_semantic_sumcheck"]
def aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.ops.range.Range Std.Usize)
  (transcript : aspis_core.transcript.Transcript) (fields : Fields)
  (point : Array aspis_core.field.QM31 10#usize)
  (running_claim : aspis_core.field.QM31) (round : Std.Usize)
  (polynomial : Array aspis_core.field.QM31 28#usize)
  (framed : Array Std.U8 433#usize) (tail_limbs : Array Std.U64 4#usize)
  (pending_return : Option (core.result.Result (aspis_core.field.QM31 × (Array
  aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
  aspis_core.v6_transcript.V6TranscriptError)) :
  Result (aspis_core.transcript.Transcript × Fields × (Array
    aspis_core.field.QM31 10#usize) × aspis_core.field.QM31 × (Option
    (core.result.Result (aspis_core.field.QM31 × (Array aspis_core.field.QM31
    10#usize) × aspis_core.field.QM31)
    aspis_core.v6_transcript.V6TranscriptError)) × Std.U32)
  := do
  loop
    (fun (iter1, fields1, polynomial1, framed1, tail_limbs1) =>
      aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
      v6_onefoldV6FixedFieldStreamInst transcript point running_claim round
      pending_return iter1 fields1 polynomial1 framed1 tail_limbs1)
    (iter, fields, polynomial, framed, tail_limbs)

/-- [aspis_core::v6_transcript::verify_compact_semantic_sumcheck]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 409:4-459:1
    Name pattern: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::verify_compact_semantic_sumcheck"]
def aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (eta : aspis_core.field.QM31) (iter : core.ops.range.Range Std.Usize)
  (transcript : aspis_core.transcript.Transcript) (fields : Fields)
  (point : Array aspis_core.field.QM31 10#usize)
  (running_claim : aspis_core.field.QM31)
  (pending_return : Option (core.result.Result (aspis_core.field.QM31 × (Array
  aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
  aspis_core.v6_transcript.V6TranscriptError)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.transcript.Transcript × Fields × (Array aspis_core.field.QM31
    10#usize) × aspis_core.field.QM31 × (Option (core.result.Result
    (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) aspis_core.v6_transcript.V6TranscriptError)))
    ((core.result.Result (aspis_core.field.QM31 × (Array aspis_core.field.QM31
    10#usize) × aspis_core.field.QM31)
    aspis_core.v6_transcript.V6TranscriptError) ×
    aspis_core.transcript.Transcript × Fields))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    ok (done (core.result.Result.Ok (eta, point, running_claim), transcript,
      fields))
  | some round =>
    let polynomial := Array.repeat 28#usize aspis_core.field.QM31.ZERO
    let framed := Array.repeat 433#usize 0#u8
    let (_, index_mut_back) ← Array.index_mut_usize framed 0#usize
    let i ← lift (UScalar.cast .U8 round)
    let (r, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let polynomial1 ← Array.update polynomial 0#usize val
      let q ← Array.index_usize polynomial1 0#usize
      let framed1 := index_mut_back i
      let (s, index_mut_back1) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) framed1
          { start := 1#usize, «end» := 17#usize }
      let s1 ← aspis_core.field.QM31.write_le_bytes q s
      let framed2 := index_mut_back1 s1
      let i1 := q.c0.a
      let i2 ← lift (core.convert.num.FromU64U32.from i1)
      let i3 ← 2#u64 * i2
      let i4 := q.c0.b
      let i5 ← lift (core.convert.num.FromU64U32.from i4)
      let i6 ← 2#u64 * i5
      let i7 := q.c1.a
      let i8 ← lift (core.convert.num.FromU64U32.from i7)
      let i9 ← 2#u64 * i8
      let i10 := q.c1.b
      let i11 ← lift (core.convert.num.FromU64U32.from i10)
      let i12 ← 2#u64 * i11
      let (transcript1, fields2, point1, running_claim1, pending_return1, i13)
        ←
        aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
          v6_onefoldV6FixedFieldStreamInst
          {
            start := 1#usize,
            «end» := aspis_core.v6_onefold.V6_SEMANTIC_SENT_VALUES
          } transcript fields1 point running_claim round polynomial1 framed2
          (Array.make 4#usize [ i3, i6, i9, i12 ]) pending_return
      match i13 with
      | 1#uscalar =>
        ok (cont (iter1, transcript1, fields2, point1, running_claim1,
          pending_return1))
      | _ =>
        match pending_return1 with
        | none => fail panic
        | some r1 => ok (done (r1, transcript1, fields2))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
          aspis_core.field.QM31)
          aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
          residual
      ok (done (return_capture, transcript, fields1))

/-- [aspis_core::v6_transcript::verify_compact_semantic_sumcheck]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 409:4-459:1
    Name pattern: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck] -/
@[rust_loop, rust_fun
  "aspis_core::v6_transcript::verify_compact_semantic_sumcheck"]
def aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.ops.range.Range Std.Usize)
  (transcript : aspis_core.transcript.Transcript) (fields : Fields)
  (eta : aspis_core.field.QM31) (point : Array aspis_core.field.QM31 10#usize)
  (running_claim : aspis_core.field.QM31)
  (pending_return : Option (core.result.Result (aspis_core.field.QM31 × (Array
  aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
  aspis_core.v6_transcript.V6TranscriptError)) :
  Result ((core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
    aspis_core.v6_transcript.V6TranscriptError) ×
    aspis_core.transcript.Transcript × Fields)
  := do
  loop
    (fun (iter1, transcript1, fields1, point1, running_claim1, pending_return1)
      => aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
      v6_onefoldV6FixedFieldStreamInst eta iter1 transcript1 fields1 point1
      running_claim1 pending_return1)
    (iter, transcript, fields, point, running_claim, pending_return)

/-- [aspis_core::v6_transcript::verify_compact_semantic_sumcheck]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 399:0-402:72
    Name pattern: [aspis_core::v6_transcript::verify_compact_semantic_sumcheck] -/
@[rust_fun "aspis_core::v6_transcript::verify_compact_semantic_sumcheck"]
def aspis_core.v6_transcript.verify_compact_semantic_sumcheck
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (transcript : aspis_core.transcript.Transcript) (fields : Fields) :
  Result ((core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
    aspis_core.v6_transcript.V6TranscriptError) ×
    aspis_core.transcript.Transcript × Fields)
  := do
  let (r, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, transcript1) ←
      aspis_core.state_only_hiding.begin_state_only_masked_sumcheck transcript
        val
    let r2 ←
      core.result.Result.map_err
        (aspis_core.v6_transcript.verify_compact_semantic_sumcheck.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError
        v6_onefoldV6FixedFieldStreamInst) r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let point := Array.repeat 10#usize aspis_core.field.QM31.ZERO
      aspis_core.v6_transcript.verify_compact_semantic_sumcheck_loop0
        v6_onefoldV6FixedFieldStreamInst
        { start := 0#usize, «end» := aspis_core.v6_onefold.V6_SEMANTIC_ROUNDS
        } transcript1 fields1 val1 point val none
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
          aspis_core.field.QM31) (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
      ok (r3, transcript1, fields1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
        aspis_core.field.QM31)
        aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
        residual
    ok (r1, transcript, fields1)

/-- [aspis_core::v6_transcript::decode_and_absorb_point_claims]: loop body 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 469:8-478:1
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_point_claims] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::decode_and_absorb_point_claims"]
def aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields) (i : Std.Usize)
  (row : Std.Usize) (iter : core.ops.range.Range Std.Usize) (fields : Fields)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (encoded : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Fields × (Array
    (Array aspis_core.field.QM31 29#usize) 3#usize) × (alloc.vec.Vec Std.U8))
    (Fields × (Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
    (alloc.vec.Vec Std.U8) × (Option (core.result.Result (Array (Array
    aspis_core.field.QM31 29#usize) 3#usize)
    aspis_core.v6_transcript.V6TranscriptError))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (fields, claims, encoded, none))
  | some column =>
    let i1 ← row * i
    let ordinal ← i1 + column
    let (r, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (a, index_mut_back) ← Array.index_mut_usize claims row
      let a1 ← Array.update a column val
      let i2 ← ordinal * 16#usize
      let (s, index_mut_back1) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice
          Std.U8) encoded { start := i2 }
      let (s1, index_mut_back2) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s
          { «end» := 16#usize }
      let s2 ← aspis_core.field.QM31.write_le_bytes val s1
      let s3 := index_mut_back2 s2
      let encoded1 := index_mut_back1 s3
      let a2 := index_mut_back a1
      ok (cont (iter1, fields1, a2, encoded1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array (Array aspis_core.field.QM31 29#usize) 3#usize)
          aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
          residual
      ok (done (fields1, claims, encoded, some return_capture))

/-- [aspis_core::v6_transcript::decode_and_absorb_point_claims]: loop 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 469:8-478:1
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_point_claims] -/
@[rust_loop, rust_fun
  "aspis_core::v6_transcript::decode_and_absorb_point_claims"]
def aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0_loop0
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields) (i : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (fields : Fields)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (encoded : alloc.vec.Vec Std.U8) (row : Std.Usize) :
  Result (Fields × (Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
    (alloc.vec.Vec Std.U8) × (Option (core.result.Result (Array (Array
    aspis_core.field.QM31 29#usize) 3#usize)
    aspis_core.v6_transcript.V6TranscriptError)))
  := do
  loop
    (fun (iter1, fields1, claims1, encoded1) =>
      aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0_loop0.body
      v6_onefoldV6FixedFieldStreamInst i row iter1 fields1 claims1 encoded1)
    (iter, fields, claims, encoded)

/-- [aspis_core::v6_transcript::decode_and_absorb_point_claims]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 468:4-478:1
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_point_claims] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::decode_and_absorb_point_claims"]
def aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0.body
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields) (i : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (fields : Fields)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (encoded : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Fields × (Array
    (Array aspis_core.field.QM31 29#usize) 3#usize) × (alloc.vec.Vec Std.U8))
    (Fields × (Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
    (alloc.vec.Vec Std.U8) × (Option (core.result.Result (Array (Array
    aspis_core.field.QM31 29#usize) 3#usize)
    aspis_core.v6_transcript.V6TranscriptError))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (fields, claims, encoded, none))
  | some row =>
    let (fields1, claims1, encoded1, pending_return) ←
      aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0_loop0
        v6_onefoldV6FixedFieldStreamInst i { start := 0#usize, «end» := i }
        fields claims encoded row
    match pending_return with
    | none => ok (cont (iter1, fields1, claims1, encoded1))
    | some _ => ok (done (fields1, claims1, encoded1, pending_return))

/-- [aspis_core::v6_transcript::decode_and_absorb_point_claims]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 468:4-478:1
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_point_claims] -/
@[rust_loop, rust_fun
  "aspis_core::v6_transcript::decode_and_absorb_point_claims"]
def aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields) (i : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (fields : Fields)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (encoded : alloc.vec.Vec Std.U8) :
  Result (Fields × (Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
    (alloc.vec.Vec Std.U8) × (Option (core.result.Result (Array (Array
    aspis_core.field.QM31 29#usize) 3#usize)
    aspis_core.v6_transcript.V6TranscriptError)))
  := do
  loop
    (fun (iter1, fields1, claims1, encoded1) =>
      aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0.body
      v6_onefoldV6FixedFieldStreamInst i iter1 fields1 claims1 encoded1)
    (iter, fields, claims, encoded)

/-- [aspis_core::v6_transcript::decode_and_absorb_point_claims]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 462:0-465:84
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_point_claims] -/
@[rust_fun "aspis_core::v6_transcript::decode_and_absorb_point_claims"]
def aspis_core.v6_transcript.decode_and_absorb_point_claims
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (transcript : aspis_core.transcript.Transcript) (fields : Fields) :
  Result ((core.result.Result (Array (Array aspis_core.field.QM31 29#usize)
    3#usize) aspis_core.v6_transcript.V6TranscriptError) ×
    aspis_core.transcript.Transcript × Fields)
  := do
  let a := Array.repeat 29#usize aspis_core.field.QM31.ZERO
  let a1 := Array.repeat 3#usize a
  let i ← aspis_core.v6_onefold.V6_TOTAL_COLUMNS
  let i1 ← aspis_core.v6_onefold.V6_POINT_CLAIM_ROWS * i
  let i2 ← i1 * 16#usize
  let encoded ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i2
  let (fields1, claims, encoded1, pending_return) ←
    aspis_core.v6_transcript.decode_and_absorb_point_claims_loop0
      v6_onefoldV6FixedFieldStreamInst i
      { start := 0#usize, «end» := aspis_core.v6_onefold.V6_POINT_CLAIM_ROWS
      } fields a1 encoded
  match pending_return with
  | none =>
    let s := alloc.vec.Vec.deref encoded1
    let transcript1 ←
      aspis_core.transcript.Transcript.absorb transcript
        aspis_core.transcript.label.V6_POINT_CLAIMS s
    ok (core.result.Result.Ok claims, transcript1, fields1)
  | some r => ok (r, transcript, fields1)

/-- [aspis_core::v6_transcript::work_nonce_bytes]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 480:0-480:70
    Name pattern: [aspis_core::v6_transcript::work_nonce_bytes] -/
@[rust_fun "aspis_core::v6_transcript::work_nonce_bytes"]
def aspis_core.v6_transcript.work_nonce_bytes
  (work_nonces : Array Std.U8 24#usize)
  (stage : aspis_core.v6_transcript.V6WorkStage) :
  Result Std.U64
  := do
  let offset ←
    match stage with
    | aspis_core.v6_transcript.V6WorkStage.Batch => ok 0#usize
    | aspis_core.v6_transcript.V6WorkStage.Fold => ok 8#usize
    | aspis_core.v6_transcript.V6WorkStage.Final => ok 16#usize
  let i ← offset + 8#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) work_nonces
      { start := offset, «end» := i }
  let r ←
    core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s
  let a ←
      match r with
      | core.result.Result.Ok value => ok value
      | core.result.Result.Err _ => fail .panic
  ok (core.num.U64.from_le_bytes a)

/-- [aspis_core::v6_transcript::check_and_absorb_work]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 489:0-495:34
    Name pattern: [aspis_core::v6_transcript::check_and_absorb_work] -/
@[rust_fun "aspis_core::v6_transcript::check_and_absorb_work"]
def aspis_core.v6_transcript.check_and_absorb_work
  (transcript : aspis_core.transcript.Transcript) (nonce : Std.U64)
  (bits : Std.U8) (stage : aspis_core.v6_transcript.V6WorkStage)
  (check_pow : Bool) :
  Result ((core.result.Result Unit aspis_core.v6_transcript.V6TranscriptError)
    × aspis_core.transcript.Transcript)
  := do
  if check_pow
  then
    let b ←
      aspis_core.transcript.Transcript.grinding_ok transcript nonce bits
    if b
    then
      match stage with
      | aspis_core.v6_transcript.V6WorkStage.Batch =>
        let a ← lift (core.num.U64.to_le_bytes nonce)
        let s ← lift (Array.to_slice a)
        let transcript1 ←
          aspis_core.transcript.Transcript.absorb transcript
            aspis_core.transcript.label.M31_PAYMENT_BATCH_POW_NONCE s
        ok (core.result.Result.Ok (), transcript1)
      | aspis_core.v6_transcript.V6WorkStage.Fold =>
        let record1 := Array.repeat 9#usize 0#u8
        let record2 ← Array.update record1 0#usize 0#u8
        let (s, index_mut_back) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) record2
            { start := 1#usize }
        let a ← lift (core.num.U64.to_le_bytes nonce)
        let s1 ← lift (Array.to_slice a)
        let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
        let record3 := index_mut_back s2
        let s3 ← lift (Array.to_slice record3)
        let transcript1 ←
          aspis_core.transcript.Transcript.absorb transcript
            aspis_core.transcript.label.M31_CIRCLE_FOLD_POW_NONCE s3
        ok (core.result.Result.Ok (), transcript1)
      | aspis_core.v6_transcript.V6WorkStage.Final =>
        let a ← lift (core.num.U64.to_le_bytes nonce)
        let s ← lift (Array.to_slice a)
        let transcript1 ←
          aspis_core.transcript.Transcript.absorb transcript
            aspis_core.transcript.label.GRIND_NONCE s
        ok (core.result.Result.Ok (), transcript1)
    else
      ok (core.result.Result.Err
        (aspis_core.v6_transcript.V6TranscriptError.WorkRejected stage),
        transcript)
  else
    match stage with
    | aspis_core.v6_transcript.V6WorkStage.Batch =>
      let a ← lift (core.num.U64.to_le_bytes nonce)
      let s ← lift (Array.to_slice a)
      let transcript1 ←
        aspis_core.transcript.Transcript.absorb transcript
          aspis_core.transcript.label.M31_PAYMENT_BATCH_POW_NONCE s
      ok (core.result.Result.Ok (), transcript1)
    | aspis_core.v6_transcript.V6WorkStage.Fold =>
      let record1 := Array.repeat 9#usize 0#u8
      let record2 ← Array.update record1 0#usize 0#u8
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) record2
          { start := 1#usize }
      let a ← lift (core.num.U64.to_le_bytes nonce)
      let s1 ← lift (Array.to_slice a)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let record3 := index_mut_back s2
      let s3 ← lift (Array.to_slice record3)
      let transcript1 ←
        aspis_core.transcript.Transcript.absorb transcript
          aspis_core.transcript.label.M31_CIRCLE_FOLD_POW_NONCE s3
      ok (core.result.Result.Ok (), transcript1)
    | aspis_core.v6_transcript.V6WorkStage.Final =>
      let a ← lift (core.num.U64.to_le_bytes nonce)
      let s ← lift (Array.to_slice a)
      let transcript1 ←
        aspis_core.transcript.Transcript.absorb transcript
          aspis_core.transcript.label.GRIND_NONCE s
      ok (core.result.Result.Ok (), transcript1)

/-- [aspis_core::v6_transcript::gamma_point_claims_and_query_powers]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 514:0-517:67
    Name pattern: [aspis_core::v6_transcript::gamma_point_claims_and_query_powers] -/
@[rust_fun "aspis_core::v6_transcript::gamma_point_claims_and_query_powers"]
def aspis_core.v6_transcript.gamma_point_claims_and_query_powers
  (gamma : aspis_core.field.QM31)
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize) :
  Result ((Array aspis_core.field.QM31 3#usize) ×
    aspis_core.state_only_spend_query.StateOnlySpendQueryPowers ×
    aspis_core.field.QM31)
  := do
  let right_val ← aspis_core.state_only_spend_query.SPEND_TOTAL_COLUMNS
  let left_val ← aspis_core.v6_onefold.V6_TOTAL_COLUMNS
  massert (left_val = right_val)
  let powers ← aspis_core.field.qm31_power_table 29#usize gamma
  let s ← lift (Array.to_slice powers)
  let a ← Array.index_usize claims 0#usize
  let s1 ← lift (Array.to_slice a)
  let a1 ← Array.index_usize claims 1#usize
  let s2 ← lift (Array.to_slice a1)
  let a2 ← Array.index_usize claims 2#usize
  let s3 ← lift (Array.to_slice a2)
  let a3 ← aspis_core.field.qm31_dot3 s (Array.make 3#usize [ s1, s2, s3 ])
  let sosqp ←
    aspis_core.state_only_spend_query.StateOnlySpendQueryPowers.from_full_table
      powers
  let i ← aspis_core.state_only_spend_query.SPEND_D_GENERATOR_INDEX
  let q ← Array.index_usize powers i
  ok (a3, sosqp, q)

/-- [aspis_core::v6_transcript::v6_statement_points]: loop body 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 541:4-543:5
    Name pattern: [aspis_core::v6_transcript::v6_statement_points]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::v6_transcript::v6_statement_points"]
def aspis_core.v6_transcript.v6_statement_points_loop0_loop0.body
  (iter : core.array.iter.IntoIter Std.Usize 2#usize)
  (xor12 : Array aspis_core.field.QM31 10#usize) :
  Result (ControlFlow ((core.array.iter.IntoIter Std.Usize 2#usize) × (Array
    aspis_core.field.QM31 10#usize)) (Array aspis_core.field.QM31 10#usize))
  := do
  let (o, iter1) ←
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter
  match o with
  | none => ok (done xor12)
  | some coordinate =>
    let q ← Array.index_usize xor12 coordinate
    let q1 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE q
    let a ← Array.update xor12 coordinate q1
    ok (cont (iter1, a))

/-- [aspis_core::v6_transcript::v6_statement_points]: loop 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 541:4-543:5
    Name pattern: [aspis_core::v6_transcript::v6_statement_points]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_transcript::v6_statement_points"]
def aspis_core.v6_transcript.v6_statement_points_loop0_loop0
  (iter : core.array.iter.IntoIter Std.Usize 2#usize)
  (xor12 : Array aspis_core.field.QM31 10#usize) :
  Result (Array aspis_core.field.QM31 10#usize)
  := do
  loop
    (fun (iter1, xor121) =>
      aspis_core.v6_transcript.v6_statement_points_loop0_loop0.body iter1
      xor121)
    (iter, xor12)

/-- [aspis_core::v6_transcript::v6_statement_points]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 534:4-545:1
    Name pattern: [aspis_core::v6_transcript::v6_statement_points]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::v6_transcript::v6_statement_points"]
def aspis_core.v6_transcript.v6_statement_points_loop0.body
  (z : Array aspis_core.field.QM31 10#usize)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (successor : Array aspis_core.field.QM31 10#usize)
  (carry : aspis_core.field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) (Array (Array aspis_core.field.QM31 10#usize)
    3#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none =>
    let iter2 ←
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
        (Array.make 2#usize [ 7#usize, 6#usize ])
    let xor12 ←
      aspis_core.v6_transcript.v6_statement_points_loop0_loop0 iter2 z
    ok (done (Array.make 3#usize [ z, successor, xor12 ]))
  | some coordinate =>
    let bit ← Array.index_usize z coordinate
    let bit_and_carry ← aspis_core.field.QM31.mul bit carry
    let q ← aspis_core.field.QM31.add bit carry
    let q1 ← aspis_core.field.QM31.add bit_and_carry bit_and_carry
    let q2 ← aspis_core.field.QM31.sub q q1
    let a ← Array.update successor coordinate q2
    ok (cont (iter1, a, bit_and_carry))

/-- [aspis_core::v6_transcript::v6_statement_points]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 534:4-545:1
    Name pattern: [aspis_core::v6_transcript::v6_statement_points]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_transcript::v6_statement_points"]
def aspis_core.v6_transcript.v6_statement_points_loop0
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (z : Array aspis_core.field.QM31 10#usize)
  (successor : Array aspis_core.field.QM31 10#usize)
  (carry : aspis_core.field.QM31) :
  Result (Array (Array aspis_core.field.QM31 10#usize) 3#usize)
  := do
  loop
    (fun (iter1, successor1, carry1) =>
      aspis_core.v6_transcript.v6_statement_points_loop0.body z iter1
      successor1 carry1)
    (iter, successor, carry)

/-- [aspis_core::v6_transcript::v6_statement_points]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 529:0-529:77
    Name pattern: [aspis_core::v6_transcript::v6_statement_points]
    Visibility: public -/
@[rust_fun "aspis_core::v6_transcript::v6_statement_points"]
def aspis_core.v6_transcript.v6_statement_points
  (z : Array aspis_core.field.QM31 10#usize) :
  Result (Array (Array aspis_core.field.QM31 10#usize) 3#usize)
  := do
  let s ← lift (Array.to_slice z)
  let i := Slice.len s
  let last ← i - 1#usize
  let q ← Array.index_usize z last
  let q1 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE q
  let a ← Array.update z last q1
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) { start := 0#usize, «end» := last }
  aspis_core.v6_transcript.v6_statement_points_loop0 iter z a q

/-- [aspis_core::v6_transcript::decode_compact_relation_polynomial]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 547:0-550:23
    Name pattern: [aspis_core::v6_transcript::decode_compact_relation_polynomial] -/
@[rust_fun "aspis_core::v6_transcript::decode_compact_relation_polynomial"]
def aspis_core.v6_transcript.decode_compact_relation_polynomial
  (sent : Array aspis_core.field.QM31 6#usize)
  (running_claim : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 7#usize)
  := do
  let polynomial := Array.repeat 7#usize aspis_core.field.QM31.ZERO
  let q ← Array.index_usize sent 0#usize
  let polynomial1 ← Array.update polynomial 0#usize q
  let q1 ← Array.index_usize sent 1#usize
  let polynomial2 ← Array.update polynomial1 1#usize q1
  let q2 ← Array.index_usize sent 2#usize
  let polynomial3 ← Array.update polynomial2 2#usize q2
  let q3 ← Array.index_usize sent 3#usize
  let polynomial4 ← Array.update polynomial3 3#usize q3
  let q4 ← Array.index_usize sent 4#usize
  let polynomial5 ← Array.update polynomial4 5#usize q4
  let q5 ← Array.index_usize sent 5#usize
  let polynomial6 ← Array.update polynomial5 6#usize q5
  let q6 ←
    aspis_core.field.QM31.mul_m31 running_claim aspis_core.field.M31_QUARTER
  let q7 ← Array.index_usize polynomial6 0#usize
  let q8 ← aspis_core.field.QM31.sub q6 q7
  let polynomial7 ← Array.update polynomial6 4#usize q8
  let left_val ← aspis_core.sumcheck.boundary_sum polynomial7
  let b ←
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq left_val running_claim
  massert b
  ok polynomial7

/-- [aspis_core::v6_transcript::decode_compact_relation_fields]: loop body 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 571:8-576:1
    Name pattern: [aspis_core::v6_transcript::decode_compact_relation_fields] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::decode_compact_relation_fields"]
def aspis_core.v6_transcript.decode_compact_relation_fields_loop0_loop0.body
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (fields : Fields) :
  Result (ControlFlow ((core.slice.iter.IterMut aspis_core.field.QM31) ×
    (core.slice.iter.IterMut aspis_core.field.QM31 → core.slice.iter.IterMut
    aspis_core.field.QM31) × Fields) (Fields × (Option (core.result.Result
    (Array (Array aspis_core.field.QM31 6#usize) 4#usize)
    aspis_core.v6_transcript.V6TranscriptError)) × (core.slice.iter.IterMut
    aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (fields, none, let im := next_back iter1 none
                                    back im))
  | some _ =>
    let (r, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (cont (iter1, fun im => let im1 := next_back im (some val)
                                 back im1, fields1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array (Array aspis_core.field.QM31 6#usize) 4#usize)
          aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
          residual
      ok (done (fields1, some return_capture,
        let im := next_back iter1 o
        back im))

/-- [aspis_core::v6_transcript::decode_compact_relation_fields]: loop 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 571:8-576:1
    Name pattern: [aspis_core::v6_transcript::decode_compact_relation_fields] -/
@[rust_loop, rust_fun
  "aspis_core::v6_transcript::decode_compact_relation_fields"]
def aspis_core.v6_transcript.decode_compact_relation_fields_loop0_loop0
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (fields : Fields) :
  Result (Fields × (Option (core.result.Result (Array (Array
    aspis_core.field.QM31 6#usize) 4#usize)
    aspis_core.v6_transcript.V6TranscriptError)) × (core.slice.iter.IterMut
    aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1, fields1) =>
      aspis_core.v6_transcript.decode_compact_relation_fields_loop0_loop0.body
      v6_onefoldV6FixedFieldStreamInst iter1 back1 fields1)
    (iter, back, fields)

/-- [aspis_core::v6_transcript::decode_compact_relation_fields]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 570:4-576:1
    Name pattern: [aspis_core::v6_transcript::decode_compact_relation_fields] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::decode_compact_relation_fields"]
def aspis_core.v6_transcript.decode_compact_relation_fields_loop0.body
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize))
  (back : core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize) →
  core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize))
  (fields : Fields) :
  Result (ControlFlow ((core.slice.iter.IterMut (Array aspis_core.field.QM31
    6#usize)) × (core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize)
    → core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize)) ×
    Fields) (Fields × (Option (core.result.Result (Array (Array
    aspis_core.field.QM31 6#usize) 4#usize)
    aspis_core.v6_transcript.V6TranscriptError)) × (core.slice.iter.IterMut
    (Array aspis_core.field.QM31 6#usize))))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (fields, none, let im := next_back iter1 none
                                    back im))
  | some round =>
    let (iter2, into_iter_back) ←
      MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        round
    let (fields1, pending_return, back1) ←
      aspis_core.v6_transcript.decode_compact_relation_fields_loop0_loop0
        v6_onefoldV6FixedFieldStreamInst iter2 (fun im => im) fields
    match pending_return with
    | none =>
      ok (cont (iter1,
        fun im =>
          let a := into_iter_back back1
          let im1 := next_back im (some a)
          back im1, fields1))
    | some _ =>
      ok (done (fields1, pending_return,
        let a := into_iter_back back1
        let im := next_back iter1 (some a)
        back im))

/-- [aspis_core::v6_transcript::decode_compact_relation_fields]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 570:4-576:1
    Name pattern: [aspis_core::v6_transcript::decode_compact_relation_fields] -/
@[rust_loop, rust_fun
  "aspis_core::v6_transcript::decode_compact_relation_fields"]
def aspis_core.v6_transcript.decode_compact_relation_fields_loop0
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize))
  (back : core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize) →
  core.slice.iter.IterMut (Array aspis_core.field.QM31 6#usize))
  (fields : Fields) :
  Result (Fields × (Option (core.result.Result (Array (Array
    aspis_core.field.QM31 6#usize) 4#usize)
    aspis_core.v6_transcript.V6TranscriptError)) × (core.slice.iter.IterMut
    (Array aspis_core.field.QM31 6#usize)))
  := do
  loop
    (fun (iter1, back1, fields1) =>
      aspis_core.v6_transcript.decode_compact_relation_fields_loop0.body
      v6_onefoldV6FixedFieldStreamInst iter1 back1 fields1)
    (iter, back, fields)

/-- [aspis_core::v6_transcript::decode_compact_relation_fields]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 566:0-568:90
    Name pattern: [aspis_core::v6_transcript::decode_compact_relation_fields] -/
@[rust_fun "aspis_core::v6_transcript::decode_compact_relation_fields"]
def aspis_core.v6_transcript.decode_compact_relation_fields
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields) (fields : Fields) :
  Result ((core.result.Result (Array (Array aspis_core.field.QM31 6#usize)
    4#usize) aspis_core.v6_transcript.V6TranscriptError) × Fields)
  := do
  let a := Array.repeat 6#usize aspis_core.field.QM31.ZERO
  let a1 := Array.repeat 4#usize a
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut a1)
  let (iter, iter_mut_back) ← core.slice.Slice.iter_mut s
  let (fields1, pending_return, back) ←
    aspis_core.v6_transcript.decode_compact_relation_fields_loop0
      v6_onefoldV6FixedFieldStreamInst iter (fun im => im) fields
  match pending_return with
  | none =>
    let s1 := iter_mut_back back
    let decoded := to_slice_mut_back s1
    ok (core.result.Result.Ok decoded, fields1)
  | some r => ok (r, fields1)

/-- [aspis_core::v6_transcript::absorb_compact_relation_polynomial]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 585:4-587:5
    Name pattern: [aspis_core::v6_transcript::absorb_compact_relation_polynomial] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::absorb_compact_relation_polynomial"]
def aspis_core.v6_transcript.absorb_compact_relation_polynomial_loop.body
  (polynomial : Array aspis_core.field.QM31 7#usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.array.iter.IntoIter
  Std.Usize 6#usize)) (framed : Array Std.U8 97#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.array.iter.IntoIter Std.Usize 6#usize)) × (Array Std.U8 97#usize))
    (Array Std.U8 97#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator Std.Usize
      6#usize) iter
  match o with
  | none => ok (done framed)
  | some p =>
    let (sent, coefficient) := p
    let q ← Array.index_usize polynomial coefficient
    let i ← sent * 16#usize
    let i1 ← 1#usize + i
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) framed
        { start := i1 }
    let (s1, index_mut_back1) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s
        { «end» := 16#usize }
    let s2 ← aspis_core.field.QM31.write_le_bytes q s1
    let s3 := index_mut_back1 s2
    let framed1 := index_mut_back s3
    ok (cont (iter1, framed1))

/-- [aspis_core::v6_transcript::absorb_compact_relation_polynomial]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 585:4-587:5
    Name pattern: [aspis_core::v6_transcript::absorb_compact_relation_polynomial] -/
@[rust_loop, rust_fun
  "aspis_core::v6_transcript::absorb_compact_relation_polynomial"]
def aspis_core.v6_transcript.absorb_compact_relation_polynomial_loop
  (iter : core.iter.adapters.enumerate.Enumerate (core.array.iter.IntoIter
  Std.Usize 6#usize)) (polynomial : Array aspis_core.field.QM31 7#usize)
  (framed : Array Std.U8 97#usize) :
  Result (Array Std.U8 97#usize)
  := do
  loop
    (fun (iter1, framed1) =>
      aspis_core.v6_transcript.absorb_compact_relation_polynomial_loop.body
      polynomial iter1 framed1)
    (iter, framed)

/-- [aspis_core::v6_transcript::absorb_compact_relation_polynomial]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 578:0-582:1
    Name pattern: [aspis_core::v6_transcript::absorb_compact_relation_polynomial] -/
@[rust_fun "aspis_core::v6_transcript::absorb_compact_relation_polynomial"]
def aspis_core.v6_transcript.absorb_compact_relation_polynomial
  (transcript : aspis_core.transcript.Transcript) (round : Std.Usize)
  (polynomial : Array aspis_core.field.QM31 7#usize) :
  Result aspis_core.transcript.Transcript
  := do
  let framed := Array.repeat 97#usize 0#u8
  let i ← lift (UScalar.cast .U8 round)
  let a ← Array.update framed 0#usize i
  let ii ←
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      (Array.make 6#usize [
        0#usize, 1#usize, 2#usize, 3#usize, 5#usize, 6#usize
        ])
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator Std.Usize
      6#usize) ii
  let framed1 ←
    aspis_core.v6_transcript.absorb_compact_relation_polynomial_loop iter
      polynomial a
  let s ← lift (Array.to_slice framed1)
  aspis_core.transcript.Transcript.absorb transcript
    aspis_core.transcript.label.V6_COMPACT_RELATION_ROUND s

/-- [aspis_core::v6_transcript::fold_values_prefix]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 601:4-608:5
    Name pattern: [aspis_core::v6_transcript::fold_values_prefix] -/
@[rust_loop_body, rust_fun "aspis_core::v6_transcript::fold_values_prefix"]
def aspis_core.v6_transcript.fold_values_prefix_loop.body
  (prepared : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
  (iter : core.ops.range.Range Std.Usize)
  (values : Array aspis_core.field.QM31 256#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 256#usize)) (Array aspis_core.field.QM31 256#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done values)
  | some index =>
    let offset ← 4#usize * index
    let q ← Array.index_usize values offset
    let i ← offset + 1#usize
    let q1 ← Array.index_usize values i
    let i1 ← offset + 2#usize
    let q2 ← Array.index_usize values i1
    let i2 ← offset + 3#usize
    let q3 ← Array.index_usize values i2
    let q4 ←
      aspis_core.field.qm31_add_sum_products3_prepared q prepared
        (Array.make 3#usize [ q1, q2, q3 ])
    let a ← Array.update values index q4
    ok (cont (iter1, a))

/-- [aspis_core::v6_transcript::fold_values_prefix]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 601:4-608:5
    Name pattern: [aspis_core::v6_transcript::fold_values_prefix] -/
@[rust_loop, rust_fun "aspis_core::v6_transcript::fold_values_prefix"]
def aspis_core.v6_transcript.fold_values_prefix_loop
  (iter : core.ops.range.Range Std.Usize)
  (values : Array aspis_core.field.QM31 256#usize)
  (prepared : Array aspis_core.field.PreparedQm31Multiplier 3#usize) :
  Result (Array aspis_core.field.QM31 256#usize)
  := do
  loop
    (fun (iter1, values1) =>
      aspis_core.v6_transcript.fold_values_prefix_loop.body prepared iter1
      values1)
    (iter, values)

/-- [aspis_core::v6_transcript::fold_values_prefix]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 591:0-591:97
    Name pattern: [aspis_core::v6_transcript::fold_values_prefix] -/
@[rust_fun "aspis_core::v6_transcript::fold_values_prefix"]
def aspis_core.v6_transcript.fold_values_prefix
  (INPUT : Std.Usize) (values : Array aspis_core.field.QM31 256#usize)
  (alpha : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 256#usize)
  := do
  massert (INPUT <= aspis_core.v6_onefold.V6_FINAL_QM31_VALUES)
  let i ← INPUT % 4#usize
  massert (i = 0#usize)
  let alpha2 ← aspis_core.field.QM31.square alpha
  let alpha3 ← aspis_core.field.QM31.mul alpha2 alpha
  let pqm ← aspis_core.field.PreparedQm31Multiplier.new alpha
  let pqm1 ← aspis_core.field.PreparedQm31Multiplier.new alpha2
  let pqm2 ← aspis_core.field.PreparedQm31Multiplier.new alpha3
  let next_len ← INPUT / 4#usize
  aspis_core.v6_transcript.fold_values_prefix_loop
    { start := 0#usize, «end» := next_len } values
    (Array.make 3#usize [ pqm, pqm1, pqm2 ])

/-- [aspis_core::v6_transcript::decode_and_absorb_final256]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 618:4-628:1
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_final256] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::decode_and_absorb_final256"]
def aspis_core.v6_transcript.decode_and_absorb_final256_loop.body
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.ops.range.Range Std.Usize) (fields : Fields)
  (decoded : alloc.vec.Vec aspis_core.field.QM31)
  (encoded : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Fields ×
    (alloc.vec.Vec aspis_core.field.QM31) × (alloc.vec.Vec Std.U8)) (Fields ×
    (alloc.vec.Vec aspis_core.field.QM31) × (alloc.vec.Vec Std.U8) × (Option
    (core.result.Result (Array aspis_core.field.QM31 256#usize)
    aspis_core.v6_transcript.V6TranscriptError))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (fields, decoded, encoded, none))
  | some index =>
    let (r, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let decoded1 ← alloc.vec.Vec.push decoded val
      let i ← index * 16#usize
      let (s, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice
          Std.U8) encoded { start := i }
      let (s1, index_mut_back1) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s
          { «end» := 16#usize }
      let s2 ← aspis_core.field.QM31.write_le_bytes val s1
      let s3 := index_mut_back1 s2
      let encoded1 := index_mut_back s3
      ok (cont (iter1, fields1, decoded1, encoded1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array aspis_core.field.QM31 256#usize)
          aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
          residual
      ok (done (fields1, decoded, encoded, some return_capture))

/-- [aspis_core::v6_transcript::decode_and_absorb_final256]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 618:4-628:1
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_final256] -/
@[rust_loop, rust_fun "aspis_core::v6_transcript::decode_and_absorb_final256"]
def aspis_core.v6_transcript.decode_and_absorb_final256_loop
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (iter : core.ops.range.Range Std.Usize) (fields : Fields)
  (decoded : alloc.vec.Vec aspis_core.field.QM31)
  (encoded : alloc.vec.Vec Std.U8) :
  Result (Fields × (alloc.vec.Vec aspis_core.field.QM31) × (alloc.vec.Vec
    Std.U8) × (Option (core.result.Result (Array aspis_core.field.QM31
    256#usize) aspis_core.v6_transcript.V6TranscriptError)))
  := do
  loop
    (fun (iter1, fields1, decoded1, encoded1) =>
      aspis_core.v6_transcript.decode_and_absorb_final256_loop.body
      v6_onefoldV6FixedFieldStreamInst iter1 fields1 decoded1 encoded1)
    (iter, fields, decoded, encoded)

/-- [aspis_core::v6_transcript::decode_and_absorb_final256]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 612:0-615:65
    Name pattern: [aspis_core::v6_transcript::decode_and_absorb_final256] -/
@[rust_fun "aspis_core::v6_transcript::decode_and_absorb_final256"]
def aspis_core.v6_transcript.decode_and_absorb_final256
  {Fields : Type} (v6_onefoldV6FixedFieldStreamInst :
  aspis_core.v6_onefold.V6FixedFieldStream Fields)
  (transcript : aspis_core.transcript.Transcript) (fields : Fields) :
  Result ((core.result.Result (Array aspis_core.field.QM31 256#usize)
    aspis_core.v6_transcript.V6TranscriptError) ×
    aspis_core.transcript.Transcript × Fields)
  := do
  let decoded :=
    alloc.vec.Vec.with_capacity aspis_core.field.QM31
      aspis_core.v6_onefold.V6_FINAL_QM31_VALUES
  let i ← aspis_core.v6_onefold.V6_FINAL_QM31_VALUES * 16#usize
  let encoded ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i
  let (fields1, decoded1, encoded1, pending_return) ←
    aspis_core.v6_transcript.decode_and_absorb_final256_loop
      v6_onefoldV6FixedFieldStreamInst
      { start := 0#usize, «end» := aspis_core.v6_onefold.V6_FINAL_QM31_VALUES
      } fields decoded encoded
  match pending_return with
  | none =>
    let s := alloc.vec.Vec.deref encoded1
    let transcript1 ←
      aspis_core.transcript.Transcript.absorb transcript
        aspis_core.transcript.label.V6_FINAL256 s
    let s1 ← alloc.vec.Vec.into_boxed_slice Global decoded1
    let r ←
      BoxArray.Insts.CoreConvertTryFromBoxSliceBoxSlice.try_from 256#usize s1
    let a ←
      match r with
      | core.result.Result.Ok value => ok value
      | core.result.Result.Err _ => fail .panic
    ok (core.result.Result.Ok a, transcript1, fields1)
  | some r => ok (r, transcript, fields1)

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#10<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 863:21-863:24
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#10<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#10<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_10.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_10 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#10<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 863:21-863:24
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#10<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#10<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_10.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_10 QueryFold
  DeriveQueries Trace Fields) aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_10.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::v6_query_batch::V6QueryBatchError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#9<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 852:13-852:16
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#9<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::v6_query_batch::V6QueryBatchError), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#9<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::v6_query_batch::V6QueryBatchError), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_9.Insts.CoreOpsFunctionFnOnceTupleV6QueryBatchErrorV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_9 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.v6_query_batch.V6QueryBatchError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.RelationShape

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::v6_query_batch::V6QueryBatchError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#9<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 852:13-852:16
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#9<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::v6_query_batch::V6QueryBatchError), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#9<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::v6_query_batch::V6QueryBatchError), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_9.Insts.CoreOpsFunctionFnOnceTupleV6QueryBatchErrorV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_9 QueryFold
  DeriveQueries Trace Fields) aspis_core.v6_query_batch.V6QueryBatchError
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_9.Insts.CoreOpsFunctionFnOnceTupleV6QueryBatchErrorV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#8<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 815:17-815:20
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#8<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#8<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_8.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_8 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#8<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 815:17-815:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#8<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#8<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_8.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_8 QueryFold
  DeriveQueries Trace Fields) aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_8.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#7<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 773:17-773:20
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#7<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#7<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_7.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_7 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#7<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 773:17-773:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#7<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#7<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_7.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_7 QueryFold
  DeriveQueries Trace Fields) aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_7.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#6<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 749:21-749:24
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#6<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#6<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_6.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_6 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.sumcheck.TensorWeightError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.RelationShape

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#6<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 749:21-749:24
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#6<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#6<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_6.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_6 QueryFold
  DeriveQueries Trace Fields) aspis_core.sumcheck.TensorWeightError
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_6.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#5<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 746:21-746:24
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#5<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#5<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_5.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_5 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#5<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 746:21-746:24
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#5<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#5<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_5.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_5 QueryFold
  DeriveQueries Trace Fields) aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_5.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::CirclePointSampleError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#4<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 738:21-738:24
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#4<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::CirclePointSampleError), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#4<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::CirclePointSampleError), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_4.Insts.CoreOpsFunctionFnOnceTupleCirclePointSampleErrorV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_4 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.transcript.CirclePointSampleError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::CirclePointSampleError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#4<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 738:21-738:24
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#4<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::CirclePointSampleError), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#4<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::CirclePointSampleError), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_4.Insts.CoreOpsFunctionFnOnceTupleCirclePointSampleErrorV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_4 QueryFold
  DeriveQueries Trace Fields) aspis_core.transcript.CirclePointSampleError
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_4.Insts.CoreOpsFunctionFnOnceTupleCirclePointSampleErrorV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#3<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 732:17-732:20
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#3<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#3<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_3.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_3 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.sumcheck.TensorWeightError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.RelationShape

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#3<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 732:17-732:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#3<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#3<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_3.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_3 QueryFold
  DeriveQueries Trace Fields) aspis_core.sumcheck.TensorWeightError
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_3.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#2<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 728:21-728:24
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#2<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#2<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_2.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_2 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.sumcheck.TensorWeightError) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.RelationShape

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::sumcheck::TensorWeightError,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#2<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 728:21-728:24
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#2<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#2<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::sumcheck::TensorWeightError), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_2.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_2 QueryFold
  DeriveQueries Trace Fields) aspis_core.sumcheck.TensorWeightError
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_2.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#1<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 716:17-716:20
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#1<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#1<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure_1 QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure#1<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 716:17-716:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#1<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure#1<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure_1 QueryFold
  DeriveQueries Trace Fields) aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure<QueryFold, DeriveQueries, Trace, Fields>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 709:17-709:20
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>}::call_once"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields)
  (c : aspis_core.v6_transcript.finish_onefold_relation.closure QueryFold
  DeriveQueries Trace Fields)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result aspis_core.v6_transcript.V6TranscriptError
  := do
  ok aspis_core.v6_transcript.V6TranscriptError.ChallengeSampling

/-- Trait implementation: [aspis_core::v6_transcript::finish_onefold_relation::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_core::v6_transcript::V6TranscriptError> for aspis_core::v6_transcript::finish_onefold_relation::closure<QueryFold, DeriveQueries, Trace, Fields>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 709:17-709:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_onefold_relation::closure<@QueryFold, @DeriveQueries, @Trace, @Fields>, (aspis_core::transcript::ChallengeSampleExhausted), aspis_core::v6_transcript::V6TranscriptError>"]
def
  aspis_core.v6_transcript.finish_onefold_relation.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_onefold_relation.closure QueryFold
  DeriveQueries Trace Fields) aspis_core.transcript.ChallengeSampleExhausted
  aspis_core.v6_transcript.V6TranscriptError := {
  call_once :=
    aspis_core.v6_transcript.finish_onefold_relation.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    v6_onefoldV6FixedFieldStreamInst
}

/-- [aspis_core::v6_transcript::finish_onefold_relation]: loop body 2:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 858:4-917:1
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation"]
def aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0_loop0.body
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) (selector : Std.U8)
  (semantic_point : Array aspis_core.field.QM31 10#usize)
  (gamma : aspis_core.field.QM31) (kappa : aspis_core.field.QM31)
  (relation_fields : Array (Array aspis_core.field.QM31 6#usize) 4#usize)
  (folded_values : Array aspis_core.field.QM31 256#usize)
  (queries : Array Std.U32 16#usize) (compact_counter : Std.U8)
  (frontier_nodes : Std.Usize)
  (transcript_state_after_queries : Array Std.U8 32#usize)
  (query_batch_challenge : aspis_core.field.QM31)
  (authenticated_queries : aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
  (iter : core.ops.range.Range Std.Usize)
  (transcript : aspis_core.transcript.Transcript) (trace : Trace)
  (running_claim : aspis_core.field.QM31)
  (weights : aspis_core.sumcheck.WeightAccumulator)
  (alpha : Array aspis_core.field.QM31 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.transcript.Transcript × Trace × aspis_core.field.QM31 ×
    aspis_core.sumcheck.WeightAccumulator × (Array aspis_core.field.QM31
    4#usize)) (aspis_core.transcript.Transcript × Trace ×
    aspis_core.field.QM31 × aspis_core.sumcheck.WeightAccumulator ×
    (core.result.Result aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
        folded_values { «end» := 4#usize }
    let q ← aspis_core.sumcheck.WeightAccumulator.dot weights s
    let b ←
      core.cmp.PartialEq.ne.trait_default
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q running_claim
    if b
    then
      ok (done (transcript, trace, running_claim, weights,
        core.result.Result.Err
        aspis_core.v6_transcript.V6TranscriptError.RelationTerminal))
    else
      let (_, trace1) ←
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
          trace aspis_core.v6_transcript.V6RelationDiagnosticPhase.Terminal
      let ii ←
        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
          authenticated_queries.values
      let folded_query_sum ←
        core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
          (BuiltinFnMut (aspis_core.field.QM31 × aspis_core.field.QM31)
          aspis_core.field.QM31) ii aspis_core.field.QM31.ZERO
          (fun p => aspis_core.field.QM31.add p.1 p.2)
      ok (done (transcript, trace1, running_claim, weights,
        core.result.Result.Ok
        {
          gamma,
          kappa,
          alpha,
          queries,
          selector,
          compact_counter,
          frontier_nodes,
          semantic_point,
          query_batch_challenge,
          folded_query_sum,
          transcript_state_after_queries
        }))
  | some round =>
    let a ← Array.index_usize relation_fields round
    let polynomial ←
      aspis_core.v6_transcript.decode_compact_relation_polynomial a
        running_claim
    let transcript1 ←
      aspis_core.v6_transcript.absorb_compact_relation_polynomial transcript
        round polynomial
    let (r, transcript2) ←
      aspis_core.transcript.Transcript.challenge_qm31 transcript1
    let r1 ←
      core.result.Result.map_err
        (aspis_core.v6_transcript.finish_onefold_relation.closure_10.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
        coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
        coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
        v6_onefoldV6FixedFieldStreamInst) r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let alpha1 ← Array.update alpha round val
      let q ← Array.index_usize alpha1 round
      let running_claim1 ← aspis_core.sumcheck.evaluate polynomial q
      let vrdp ←
        match round.val with
        | 1 =>
          ok
            aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundOnePolynomial
        | 2 =>
          ok
            aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundTwoPolynomial
        | _ =>
          ok
            aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundThreePolynomial
      let (_, trace1) ←
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
          trace vrdp
      let i ← aspis_core.v6_onefold.V6_RELATION_ROUNDS - 1#usize
      if round = i
      then
        let q1 ← Array.index_usize alpha1 1#usize
        let q2 ← Array.index_usize alpha1 2#usize
        let q3 ← Array.index_usize alpha1 3#usize
        let (b, weights1) ←
          aspis_core.sumcheck.WeightAccumulator.fold_tag73_relation_tail_arity4
            weights (Array.make 3#usize [ q1, q2, q3 ])
        if b
        then
          let vrdp1 ←
            match round.val with
            | 1 =>
              ok
                aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundOneWeights
            | 2 =>
              ok
                aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundTwoWeights
            | _ =>
              ok
                aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundThreeWeights
          let (_, trace2) ←
            coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
              trace1 vrdp1
          match round.val with
          | 1 =>
            do
            let _ ←
              aspis_core.v6_transcript.fold_values_prefix 256#usize
                folded_values q1
            ok ()
          | 2 =>
            do
            let _ ←
              aspis_core.v6_transcript.fold_values_prefix 64#usize
                folded_values q2
            ok ()
          | _ =>
            do
            let q4 ← Array.index_usize alpha1 round
            let _ ←
              aspis_core.v6_transcript.fold_values_prefix 16#usize
                folded_values q4
            ok ()
          let vrdp2 ←
            match round.val with
            | 1 =>
              ok aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundOne
            | 2 =>
              ok aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundTwo
            | _ =>
              ok aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundThree
          let (_, trace3) ←
            coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
              trace2 vrdp2
          ok (cont (iter1, transcript2, trace3, running_claim1, weights1,
            alpha1))
        else
          ok (done (transcript2, trace1, running_claim1, weights1,
            core.result.Result.Err
            aspis_core.v6_transcript.V6TranscriptError.RelationShape))
      else
        let vrdp1 ←
          match round.val with
          | 1 =>
            ok
              aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundOneWeights
          | 2 =>
            ok
              aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundTwoWeights
          | _ =>
            ok
              aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundThreeWeights
        let (_, trace2) ←
          coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
            trace1 vrdp1
        match round.val with
        | 1 =>
          do
          let q1 ← Array.index_usize alpha1 1#usize
          let _ ←
            aspis_core.v6_transcript.fold_values_prefix 256#usize folded_values
              q1
          ok ()
        | 2 =>
          do
          let q1 ← Array.index_usize alpha1 2#usize
          let _ ←
            aspis_core.v6_transcript.fold_values_prefix 64#usize folded_values
              q1
          ok ()
        | _ =>
          do
          let q1 ← Array.index_usize alpha1 round
          let _ ←
            aspis_core.v6_transcript.fold_values_prefix 16#usize folded_values
              q1
          ok ()
        let vrdp2 ←
          match round.val with
          | 1 => ok aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundOne
          | 2 => ok aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundTwo
          | _ =>
            ok aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundThree
        let (_, trace3) ←
          coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
            trace2 vrdp2
        ok (cont (iter1, transcript2, trace3, running_claim1, weights, alpha1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
      ok (done (transcript2, trace, running_claim, weights, return_capture))

/-- [aspis_core::v6_transcript::finish_onefold_relation]: loop 2:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 858:4-917:1
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation] -/
@[rust_loop, rust_fun "aspis_core::v6_transcript::finish_onefold_relation"]
def aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0_loop0
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) (iter : core.ops.range.Range Std.Usize)
  (transcript : aspis_core.transcript.Transcript) (selector : Std.U8)
  (semantic_point : Array aspis_core.field.QM31 10#usize) (trace : Trace)
  (gamma : aspis_core.field.QM31) (kappa : aspis_core.field.QM31)
  (running_claim : aspis_core.field.QM31)
  (weights : aspis_core.sumcheck.WeightAccumulator)
  (relation_fields : Array (Array aspis_core.field.QM31 6#usize) 4#usize)
  (alpha : Array aspis_core.field.QM31 4#usize)
  (folded_values : Array aspis_core.field.QM31 256#usize)
  (queries : Array Std.U32 16#usize) (compact_counter : Std.U8)
  (frontier_nodes : Std.Usize)
  (transcript_state_after_queries : Array Std.U8 32#usize)
  (query_batch_challenge : aspis_core.field.QM31)
  (authenticated_queries : aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
  :
  Result (aspis_core.transcript.Transcript × Trace × aspis_core.field.QM31 ×
    aspis_core.sumcheck.WeightAccumulator × (core.result.Result
    aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError))
  := do
  loop
    (fun (iter1, transcript1, trace1, running_claim1, weights1, alpha1) =>
      aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0_loop0.body
      coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
      coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
      coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
      v6_onefoldV6FixedFieldStreamInst selector semantic_point gamma kappa
      relation_fields folded_values queries compact_counter frontier_nodes
      transcript_state_after_queries query_batch_challenge
      authenticated_queries iter1 transcript1 trace1 running_claim1 weights1
      alpha1)
    (iter, transcript, trace, running_claim, weights, alpha)

/-- [aspis_core::v6_transcript::finish_onefold_relation]: loop body 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 735:4-917:1
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation"]
def aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0.body
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) (work_nonces : Array Std.U8 24#usize) (c1_frontier : Slice Std.U8)
  (c2_frontier : Slice Std.U8) (work_bits : Array Std.U8 3#usize)
  (selector : Std.U8) (frontier_node_bytes : Std.Usize)
  (query_batch_labels : (Std.U8 × Std.U8))
  (shift_query_batch_for_tag73 : Bool) (expose_final256_to_query_fold : Bool)
  (derive_queries : DeriveQueries) (check_pow : Bool)
  (semantic_point : Array aspis_core.field.QM31 10#usize)
  (query_fold : QueryFold) (trace : Trace) (gamma : aspis_core.field.QM31)
  (kappa : aspis_core.field.QM31) (d_power : aspis_core.field.QM31)
  (gamma_powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
  (iter : core.ops.range.Range Std.I32)
  (transcript : aspis_core.transcript.Transcript) (fields : Fields)
  (running_claim : aspis_core.field.QM31)
  (weights : aspis_core.sumcheck.WeightAccumulator) :
  Result (ControlFlow ((core.ops.range.Range Std.I32) ×
    aspis_core.transcript.Transcript × Fields × aspis_core.field.QM31 ×
    aspis_core.sumcheck.WeightAccumulator) (core.result.Result
    aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepI32 iter
  match o with
  | none =>
    let (_, trace1) ←
      coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
        trace aspis_core.v6_transcript.V6RelationDiagnosticPhase.CircleSamples
    let (r, fields1) ←
      aspis_core.v6_transcript.decode_compact_relation_fields
        v6_onefoldV6FixedFieldStreamInst fields
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (_, trace2) ←
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
          trace1
          aspis_core.v6_transcript.V6RelationDiagnosticPhase.RelationFields
      let alpha := Array.repeat 4#usize aspis_core.field.QM31.ZERO
      let a ← Array.index_usize val 0#usize
      let first ←
        aspis_core.v6_transcript.decode_compact_relation_polynomial a
          running_claim
      let transcript1 ←
        aspis_core.v6_transcript.absorb_compact_relation_polynomial transcript
          0#usize first
      let i ←
        aspis_core.v6_transcript.work_nonce_bytes work_nonces
          aspis_core.v6_transcript.V6WorkStage.Fold
      let i1 ← Array.index_usize work_bits 1#usize
      let (r1, transcript2) ←
        aspis_core.v6_transcript.check_and_absorb_work transcript1 i i1
          aspis_core.v6_transcript.V6WorkStage.Fold check_pow
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let (r2, transcript3) ←
          aspis_core.transcript.Transcript.challenge_qm31 transcript2
        let r3 ←
          core.result.Result.map_err
            (aspis_core.v6_transcript.finish_onefold_relation.closure_7.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
            coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
            coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
            coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
            v6_onefoldV6FixedFieldStreamInst) r2 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let alpha1 ← Array.update alpha 0#usize val1
          let q ← Array.index_usize alpha1 0#usize
          let running_claim1 ← aspis_core.sumcheck.evaluate first q
          let weights1 ←
            aspis_core.sumcheck.WeightAccumulator.fold_deferred_relation_arity4
              weights q
          let (_, trace3) ←
            coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
              trace2
              aspis_core.v6_transcript.V6RelationDiagnosticPhase.RoundZero
          let (r4, transcript4, fields2) ←
            aspis_core.v6_transcript.decode_and_absorb_final256
              v6_onefoldV6FixedFieldStreamInst transcript3 fields1
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let r5 ← v6_onefoldV6FixedFieldStreamInst.finish fields2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let (_, trace4) ←
                coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
                  trace3
                  aspis_core.v6_transcript.V6RelationDiagnosticPhase.Final256
              let i2 ←
                aspis_core.v6_transcript.work_nonce_bytes work_nonces
                  aspis_core.v6_transcript.V6WorkStage.Final
              let i3 ← Array.index_usize work_bits 2#usize
              let (r6, transcript5) ←
                aspis_core.v6_transcript.check_and_absorb_work transcript4 i2
                  i3 aspis_core.v6_transcript.V6WorkStage.Final check_pow
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r7 ←
                  coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst.call_once
                    derive_queries transcript5
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let (queries, compact_counter, frontier_nodes,
                    transcript_state_after_queries, accepted_query_transcript)
                    :=
                    val3
                  if frontier_node_bytes = 0#usize
                  then
                    ok (done (core.result.Result.Err
                      (aspis_core.v6_transcript.V6TranscriptError.Wire
                      aspis_core.v6_onefold.V6WireError.WrongLength)))
                  else
                    let i4 := Slice.len c1_frontier
                    let i5 ← i4 % frontier_node_bytes
                    if i5 != 0#usize
                    then
                      ok (done (core.result.Result.Err
                        (aspis_core.v6_transcript.V6TranscriptError.Wire
                        aspis_core.v6_onefold.V6WireError.WrongLength)))
                    else
                      let i6 := Slice.len c2_frontier
                      let i7 ← i6 % frontier_node_bytes
                      if i7 != 0#usize
                      then
                        ok (done (core.result.Result.Err
                          (aspis_core.v6_transcript.V6TranscriptError.Wire
                          aspis_core.v6_onefold.V6WireError.WrongLength)))
                      else
                        let i8 := Slice.len c1_frontier
                        let c1_nodes ← i8 / frontier_node_bytes
                        let i9 := Slice.len c2_frontier
                        let c2_nodes ← i9 / frontier_node_bytes
                        if c1_nodes != frontier_nodes
                        then
                          ok (done (core.result.Result.Err
                            (aspis_core.v6_transcript.V6TranscriptError.FrontierCountMismatch
                            frontier_nodes c1_nodes c2_nodes)))
                        else
                          if c2_nodes != frontier_nodes
                          then
                            ok (done (core.result.Result.Err
                              (aspis_core.v6_transcript.V6TranscriptError.FrontierCountMismatch
                              frontier_nodes c1_nodes c2_nodes)))
                          else
                            let (i10, i11) := query_batch_labels
                            let s ←
                              lift (Array.to_slice (Std.Array.empty Std.U8))
                            let accepted_query_transcript1 ←
                              aspis_core.transcript.Transcript.absorb
                                accepted_query_transcript i10 s
                            let (r8, accepted_query_transcript2) ←
                              aspis_core.transcript.Transcript.challenge_nonzero_qm31
                                accepted_query_transcript1
                            let r9 ←
                              core.result.Result.map_err
                                (aspis_core.v6_transcript.finish_onefold_relation.closure_8.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
                                coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
                                coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
                                coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
                                v6_onefoldV6FixedFieldStreamInst) r8 ()
                            let cf7 ←
                              core.result.Result.Insts.CoreOpsTry.branch r9
                            match cf7 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let (_, trace5) ←
                                coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
                                  trace4
                                  aspis_core.v6_transcript.V6RelationDiagnosticPhase.Queries
                              let o1 ←
                                if expose_final256_to_query_fold
                                then
                                  do
                                  let a1 ←
                                    Box.Insts.CoreConvertAsRef.as_ref Global
                                      val2
                                  ok (some a1)
                                else ok none
                              let r10 ←
                                coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst.call_once
                                  query_fold
                                  ({
                                     gamma,
                                     gamma_powers,
                                     d_power,
                                     alpha0 := q,
                                     final256_coefficients := o1,
                                     queries,
                                     selector,
                                     compact_counter,
                                     frontier_nodes
                                   } :
                                  aspis_core.v6_transcript.V6QueryBatchView)
                              let r11 ←
                                core.result.Result.map_err (BuiltinFnOnce
                                  aspis_core.v6_onefold.V6WireError
                                  aspis_core.v6_transcript.V6TranscriptError)
                                  r10
                                  (aspis_core.v6_transcript.V6TranscriptError.Wire_fn)
                              let cf8 ←
                                core.result.Result.Insts.CoreOpsTry.branch r11
                              match cf8 with
                              | core.ops.control_flow.ControlFlow.Continue val5
                                =>
                                let (running_claim2, weights2, r12) ←
                                  if shift_query_batch_for_tag73
                                  then
                                    do
                                    let (r13, weights3, running_claim3) ←
                                      aspis_core.v6_query_batch.add_v7_final256_query_batch_shifted
                                        weights1 running_claim1 queries val5
                                        val4
                                    ok (running_claim3, weights3, r13)
                                  else
                                    do
                                    let (r13, weights3, running_claim3) ←
                                      aspis_core.v6_query_batch.add_v6_final256_query_batch
                                        weights1 running_claim1 queries val5
                                        val4
                                    ok (running_claim3, weights3, r13)
                                let r13 ←
                                  core.result.Result.map_err
                                    (aspis_core.v6_transcript.finish_onefold_relation.closure_9.Insts.CoreOpsFunctionFnOnceTupleV6QueryBatchErrorV6TranscriptError
                                    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
                                    coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
                                    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
                                    v6_onefoldV6FixedFieldStreamInst) r12 ()
                                let cf9 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r13
                                match cf9 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val6 =>
                                  let query_claim_bytes :=
                                    Array.repeat 16#usize 0#u8
                                  let (s1, to_slice_mut_back) ←
                                    lift (Array.to_slice_mut query_claim_bytes)
                                  let s2 ←
                                    aspis_core.field.QM31.write_le_bytes val6
                                      s1
                                  let query_claim_bytes1 :=
                                    to_slice_mut_back s2
                                  let s3 ←
                                    lift (Array.to_slice query_claim_bytes1)
                                  let accepted_query_transcript3 ←
                                    aspis_core.transcript.Transcript.absorb
                                      accepted_query_transcript2 i11 s3
                                  let (_, trace6) ←
                                    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
                                      trace5
                                      aspis_core.v6_transcript.V6RelationDiagnosticPhase.QueryBatch
                                  let (_, _, _, _, r14) ←
                                    aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0_loop0
                                      coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
                                      coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
                                      coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
                                      v6_onefoldV6FixedFieldStreamInst
                                      {
                                        start := 1#usize,
                                        «end» :=
                                          aspis_core.v6_onefold.V6_RELATION_ROUNDS
                                      } accepted_query_transcript3 selector
                                      semantic_point trace6 gamma kappa
                                      running_claim2 weights2 val alpha1 val2
                                      queries compact_counter frontier_nodes
                                      transcript_state_after_queries val4 val5
                                  ok (done r14)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let return_capture ←
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      aspis_core.v6_transcript.V6VerifiedTranscript
                                      (core.convert.FromSame
                                      aspis_core.v6_transcript.V6TranscriptError)
                                      residual
                                  ok (done return_capture)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let return_capture ←
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    aspis_core.v6_transcript.V6VerifiedTranscript
                                    (core.convert.FromSame
                                    aspis_core.v6_transcript.V6TranscriptError)
                                    residual
                                ok (done return_capture)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let return_capture ←
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  aspis_core.v6_transcript.V6VerifiedTranscript
                                  (core.convert.FromSame
                                  aspis_core.v6_transcript.V6TranscriptError)
                                  residual
                              ok (done return_capture)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let return_capture ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      aspis_core.v6_transcript.V6VerifiedTranscript
                      (core.convert.FromSame
                      aspis_core.v6_transcript.V6TranscriptError) residual
                  ok (done return_capture)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let return_capture ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    aspis_core.v6_transcript.V6VerifiedTranscript
                    (core.convert.FromSame
                    aspis_core.v6_transcript.V6TranscriptError) residual
                ok (done return_capture)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let return_capture ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  aspis_core.v6_transcript.V6VerifiedTranscript
                  aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
                  residual
              ok (done return_capture)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let return_capture ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                aspis_core.v6_transcript.V6VerifiedTranscript
                (core.convert.FromSame
                aspis_core.v6_transcript.V6TranscriptError) residual
            ok (done return_capture)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let return_capture ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_core.v6_transcript.V6VerifiedTranscript
              (core.convert.FromSame
              aspis_core.v6_transcript.V6TranscriptError) residual
          ok (done return_capture)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let return_capture ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.v6_transcript.V6VerifiedTranscript
            (core.convert.FromSame aspis_core.v6_transcript.V6TranscriptError)
            residual
        ok (done return_capture)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
      ok (done return_capture)
  | some sample =>
    let (r, transcript1) ←
      aspis_core.transcript.Transcript.challenge_secure_circle_point transcript
    let r1 ←
      core.result.Result.map_err
        (aspis_core.v6_transcript.finish_onefold_relation.closure_4.Insts.CoreOpsFunctionFnOnceTupleCirclePointSampleErrorV6TranscriptError
        coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
        coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
        v6_onefoldV6FixedFieldStreamInst) r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r2, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let record1 := Array.repeat 17#usize 0#u8
        let i ← lift (IScalar.hcast .U8 sample)
        let record2 ← Array.update record1 0#usize i
        let (s, index_mut_back) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) record2
            { start := 1#usize }
        let s1 ← aspis_core.field.QM31.write_le_bytes val1 s
        let record3 := index_mut_back s1
        let s2 ← lift (Array.to_slice record3)
        let transcript2 ←
          aspis_core.transcript.Transcript.absorb transcript1
            aspis_core.transcript.label.V6_CIRCLE_OOD_VALUE s2
        let (r3, transcript3) ←
          aspis_core.transcript.Transcript.challenge_qm31 transcript2
        let r4 ←
          core.result.Result.map_err
            (aspis_core.v6_transcript.finish_onefold_relation.closure_5.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
            coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
            coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
            coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
            v6_onefoldV6FixedFieldStreamInst) r3 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let (r5, weights1) ←
            aspis_core.sumcheck.WeightAccumulator.add_circle_tensor weights
              val2 val
          let r6 ←
            core.result.Result.map_err
              (aspis_core.v6_transcript.finish_onefold_relation.closure_6.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError
              coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
              coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
              coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
              v6_onefoldV6FixedFieldStreamInst) r5 ()
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let q ← aspis_core.field.QM31.mul val2 val1
            let running_claim1 ← aspis_core.field.QM31.add running_claim q
            ok (cont (iter1, transcript3, fields1, running_claim1, weights1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let return_capture ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                aspis_core.v6_transcript.V6VerifiedTranscript
                (core.convert.FromSame
                aspis_core.v6_transcript.V6TranscriptError) residual
            ok (done return_capture)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let return_capture ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_core.v6_transcript.V6VerifiedTranscript
              (core.convert.FromSame
              aspis_core.v6_transcript.V6TranscriptError) residual
          ok (done return_capture)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let return_capture ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.v6_transcript.V6VerifiedTranscript
            aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
            residual
        ok (done return_capture)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
      ok (done return_capture)

/-- [aspis_core::v6_transcript::finish_onefold_relation]: loop 1:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 735:4-917:1
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation] -/
@[rust_loop, rust_fun "aspis_core::v6_transcript::finish_onefold_relation"]
def aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) (iter : core.ops.range.Range Std.I32)
  (transcript : aspis_core.transcript.Transcript)
  (work_nonces : Array Std.U8 24#usize) (c1_frontier : Slice Std.U8)
  (c2_frontier : Slice Std.U8) (work_bits : Array Std.U8 3#usize)
  (selector : Std.U8) (frontier_node_bytes : Std.Usize)
  (query_batch_labels : (Std.U8 × Std.U8))
  (shift_query_batch_for_tag73 : Bool) (expose_final256_to_query_fold : Bool)
  (derive_queries : DeriveQueries) (fields : Fields) (check_pow : Bool)
  (semantic_point : Array aspis_core.field.QM31 10#usize)
  (query_fold : QueryFold) (trace : Trace) (gamma : aspis_core.field.QM31)
  (kappa : aspis_core.field.QM31) (d_power : aspis_core.field.QM31)
  (gamma_powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
  (running_claim : aspis_core.field.QM31)
  (weights : aspis_core.sumcheck.WeightAccumulator) :
  Result (core.result.Result aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  loop
    (fun (iter1, transcript1, fields1, running_claim1, weights1) =>
      aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0.body
      coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
      coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
      coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
      v6_onefoldV6FixedFieldStreamInst work_nonces c1_frontier c2_frontier
      work_bits selector frontier_node_bytes query_batch_labels
      shift_query_batch_for_tag73 expose_final256_to_query_fold derive_queries
      check_pow semantic_point query_fold trace gamma kappa d_power
      gamma_powers iter1 transcript1 fields1 running_claim1 weights1)
    (iter, transcript, fields, running_claim, weights)

/-- [aspis_core::v6_transcript::finish_onefold_relation]: loop body 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 725:4-917:1
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_transcript::finish_onefold_relation"]
def aspis_core.v6_transcript.finish_onefold_relation_loop0.body
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) (transcript : aspis_core.transcript.Transcript)
  (work_nonces : Array Std.U8 24#usize) (c1_frontier : Slice Std.U8)
  (c2_frontier : Slice Std.U8) (work_bits : Array Std.U8 3#usize)
  (selector : Std.U8) (frontier_node_bytes : Std.Usize)
  (query_batch_labels : (Std.U8 × Std.U8))
  (shift_query_batch_for_tag73 : Bool) (expose_final256_to_query_fold : Bool)
  (derive_queries : DeriveQueries) (fields : Fields)
  (inactive_row_groups : Array Std.U8 64#usize)
  (inactive_group_masks : Slice Std.U16) (check_pow : Bool)
  (semantic_point : Array aspis_core.field.QM31 10#usize)
  (query_fold : QueryFold) (trace : Trace) (gamma : aspis_core.field.QM31)
  (kappa : aspis_core.field.QM31)
  (points : Array (Array aspis_core.field.QM31 10#usize) 3#usize)
  (point_scales : Array aspis_core.field.QM31 3#usize)
  (d_power : aspis_core.field.QM31)
  (gamma_powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
  (running_claim : aspis_core.field.QM31)
  (iter : core.ops.range.Range Std.Usize)
  (weights : aspis_core.sumcheck.WeightAccumulator) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.sumcheck.WeightAccumulator) (core.result.Result
    aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let (r, weights1) ←
      aspis_core.sumcheck.WeightAccumulator.add_grouped_64x16_binary_masks_deferred_prepared
        weights inactive_row_groups inactive_group_masks
    let r1 ←
      core.result.Result.map_err
        (aspis_core.v6_transcript.finish_onefold_relation.closure_3.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError
        coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
        coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
        v6_onefoldV6FixedFieldStreamInst) r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (_, trace1) ←
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
          trace
          aspis_core.v6_transcript.V6RelationDiagnosticPhase.PreparedWeights
      let r2 ←
        aspis_core.v6_transcript.finish_onefold_relation_loop0_loop0
          coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
          coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
          coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
          v6_onefoldV6FixedFieldStreamInst { start := 0#i32, «end» := 2#i32 }
          transcript work_nonces c1_frontier c2_frontier work_bits selector
          frontier_node_bytes query_batch_labels shift_query_batch_for_tag73
          expose_final256_to_query_fold derive_queries fields check_pow
          semantic_point query_fold trace1 gamma kappa d_power gamma_powers
          running_claim weights1
      ok (done r2)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
      ok (done return_capture)
  | some row =>
    let q ← Array.index_usize point_scales row
    let a ← Array.index_usize points row
    let s ← lift (Array.to_slice a)
    let v ←
      alloc.slice.Slice.to_vec aspis_core.field.QM31.Insts.CoreCloneClone s
    let (r, weights1) ←
      aspis_core.sumcheck.WeightAccumulator.add_multilinear weights q v
    let r1 ←
      core.result.Result.map_err
        (aspis_core.v6_transcript.finish_onefold_relation.closure_2.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6TranscriptError
        coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
        coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
        v6_onefoldV6FixedFieldStreamInst) r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ok (cont (iter1, weights1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
      ok (done return_capture)

/-- [aspis_core::v6_transcript::finish_onefold_relation]: loop 0:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 725:4-917:1
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation] -/
@[rust_loop, rust_fun "aspis_core::v6_transcript::finish_onefold_relation"]
def aspis_core.v6_transcript.finish_onefold_relation_loop0
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) (iter : core.ops.range.Range Std.Usize)
  (transcript : aspis_core.transcript.Transcript)
  (work_nonces : Array Std.U8 24#usize) (c1_frontier : Slice Std.U8)
  (c2_frontier : Slice Std.U8) (work_bits : Array Std.U8 3#usize)
  (selector : Std.U8) (frontier_node_bytes : Std.Usize)
  (query_batch_labels : (Std.U8 × Std.U8))
  (shift_query_batch_for_tag73 : Bool) (expose_final256_to_query_fold : Bool)
  (derive_queries : DeriveQueries) (fields : Fields)
  (inactive_row_groups : Array Std.U8 64#usize)
  (inactive_group_masks : Slice Std.U16) (check_pow : Bool)
  (semantic_point : Array aspis_core.field.QM31 10#usize)
  (query_fold : QueryFold) (trace : Trace) (gamma : aspis_core.field.QM31)
  (kappa : aspis_core.field.QM31)
  (points : Array (Array aspis_core.field.QM31 10#usize) 3#usize)
  (point_scales : Array aspis_core.field.QM31 3#usize)
  (d_power : aspis_core.field.QM31)
  (gamma_powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers)
  (running_claim : aspis_core.field.QM31)
  (weights : aspis_core.sumcheck.WeightAccumulator) :
  Result (core.result.Result aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  loop
    (fun (iter1, weights1) =>
      aspis_core.v6_transcript.finish_onefold_relation_loop0.body
      coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
      coreopsfunctionFnOnceDeriveQueriesTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
      coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
      v6_onefoldV6FixedFieldStreamInst transcript work_nonces c1_frontier
      c2_frontier work_bits selector frontier_node_bytes query_batch_labels
      shift_query_batch_for_tag73 expose_final256_to_query_fold derive_queries
      fields inactive_row_groups inactive_group_masks check_pow semantic_point
      query_fold trace gamma kappa points point_scales d_power gamma_powers
      running_claim iter1 weights1)
    (iter, weights)

/-- [aspis_core::v6_transcript::finish_onefold_relation]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 667:0-697:31
    Name pattern: [aspis_core::v6_transcript::finish_onefold_relation] -/
@[rust_fun "aspis_core::v6_transcript::finish_onefold_relation"]
def aspis_core.v6_transcript.finish_onefold_relation
  {QueryFold : Type} {DeriveQueries : Type} {Trace : Type} {Fields : Type}
  (coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnOnceDeriveQueriesTupleShared0TranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
  : core.ops.function.FnOnce DeriveQueries aspis_core.transcript.Transcript
  (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize ×
  (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
  aspis_core.v6_transcript.V6TranscriptError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (v6_onefoldV6FixedFieldStreamInst : aspis_core.v6_onefold.V6FixedFieldStream
  Fields) (transcript : aspis_core.transcript.Transcript)
  (work_nonces : Array Std.U8 24#usize) (c1_frontier : Slice Std.U8)
  (c2_frontier : Slice Std.U8) (work_bits : Array Std.U8 3#usize)
  (selector : Std.U8) (frontier_node_bytes : Std.Usize)
  (query_batch_labels : (Std.U8 × Std.U8))
  (shift_query_batch_for_tag73 : Bool) (expose_final256_to_query_fold : Bool)
  (derive_queries : DeriveQueries) (fields : Fields)
  (inactive_row_groups : Array Std.U8 64#usize)
  (inactive_group_masks : Slice Std.U16) (check_pow : Bool)
  (semantic_point : Array aspis_core.field.QM31 10#usize)
  (point_claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (query_fold : QueryFold) (trace : Trace) :
  Result (core.result.Result aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  let (_, trace1) ←
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst.call_mut
      trace aspis_core.v6_transcript.V6RelationDiagnosticPhase.Start
  let i ←
    aspis_core.v6_transcript.work_nonce_bytes work_nonces
      aspis_core.v6_transcript.V6WorkStage.Batch
  let i1 ← Array.index_usize work_bits 0#usize
  let (r, transcript1) ←
    aspis_core.v6_transcript.check_and_absorb_work transcript i i1
      aspis_core.v6_transcript.V6WorkStage.Batch check_pow
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (r1, transcript2) ←
      aspis_core.transcript.Transcript.challenge_nonzero_qm31 transcript1
    let r2 ←
      core.result.Result.map_err
        (aspis_core.v6_transcript.finish_onefold_relation.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
        coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
        coreopsfunctionFnOnceDeriveQueriesTupleShared0TranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
        coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
        v6_onefoldV6FixedFieldStreamInst) r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r3, fields1) ← v6_onefoldV6FixedFieldStreamInst.next_qm31 fields
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let inactive_bytes := Array.repeat 16#usize 0#u8
        let (s, to_slice_mut_back) ← lift (Array.to_slice_mut inactive_bytes)
        let s1 ← aspis_core.field.QM31.write_le_bytes val1 s
        let inactive_bytes1 := to_slice_mut_back s1
        let s2 ← lift (Array.to_slice inactive_bytes1)
        let transcript3 ←
          aspis_core.transcript.Transcript.absorb transcript2
            aspis_core.transcript.label.V6_INACTIVE_CLAIM s2
        let (r4, transcript4) ←
          aspis_core.transcript.Transcript.challenge_nonzero_qm31 transcript3
        let r5 ←
          core.result.Result.map_err
            (aspis_core.v6_transcript.finish_onefold_relation.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
            coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
            coreopsfunctionFnOnceDeriveQueriesTupleShared0TranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
            coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
            v6_onefoldV6FixedFieldStreamInst) r4 ()
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let points ←
            aspis_core.v6_transcript.v6_statement_points semantic_point
          let q ← aspis_core.field.QM31.square val2
          let (combined_claims, gamma_powers, d_power) ←
            aspis_core.v6_transcript.gamma_point_claims_and_query_powers val
              point_claims
          let q1 ←
            aspis_core.field.qm31_sum_products3
              (Array.make 3#usize [ aspis_core.field.QM31.ONE, val2, q ])
              combined_claims
          let running_claim ← aspis_core.field.QM31.add val1 q1
          let weights ← aspis_core.sumcheck.WeightAccumulator.empty 10#u32
          aspis_core.v6_transcript.finish_onefold_relation_loop0
            coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
            coreopsfunctionFnOnceDeriveQueriesTupleShared0TranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptErrorInst
            coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
            v6_onefoldV6FixedFieldStreamInst
            {
              start := 0#usize,
              «end» := aspis_core.v6_onefold.V6_POINT_CLAIM_ROWS
            } transcript4 work_nonces c1_frontier c2_frontier work_bits
            selector frontier_node_bytes query_batch_labels
            shift_query_batch_for_tag73 expose_final256_to_query_fold
            derive_queries fields1 inactive_row_groups inactive_group_masks
            check_pow semantic_point query_fold trace1 val val2 points
            (Array.make 3#usize [ aspis_core.field.QM31.ONE, val2, q ]) d_power
            gamma_powers running_claim weights
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.v6_transcript.V6VerifiedTranscript
            (core.convert.FromSame aspis_core.v6_transcript.V6TranscriptError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v6_transcript.V6VerifiedTranscript
          aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
        aspis_core.v6_transcript.V6TranscriptError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
      aspis_core.v6_transcript.V6TranscriptError) residual

/-- [aspis_core::v7_onefold::V7_COMPACT_FINAL_WORK_BITS]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 34:0-34:40
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_FINAL_WORK_BITS]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_FINAL_WORK_BITS"]
def aspis_core.v7_onefold.V7_COMPACT_FINAL_WORK_BITS : Std.U8 := 34#u8

/-- [aspis_core::v7_onefold::V7_COMPACT_FOLD_WORK_BITS]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 33:0-33:39
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_FOLD_WORK_BITS]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_FOLD_WORK_BITS"]
def aspis_core.v7_onefold.V7_COMPACT_FOLD_WORK_BITS : Std.U8 := 31#u8

/-- [aspis_core::v7_onefold::V7_COMPACT_BATCH_WORK_BITS]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 32:0-32:40
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_BATCH_WORK_BITS]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_BATCH_WORK_BITS"]
def aspis_core.v7_onefold.V7_COMPACT_BATCH_WORK_BITS : Std.U8 := 35#u8

/-- [aspis_core::v7_onefold::derive_v7_compact_candidate::{impl core::ops::function::FnOnce<(alloc::vec::Vec<u32>,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::derive_v7_compact_candidate::closure#1}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 85:17-85:20
    Name pattern: [aspis_core::v7_onefold::derive_v7_compact_candidate::{core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure#1, (alloc::vec::Vec<u32>), aspis_core::v6_onefold::V6WireError>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::derive_v7_compact_candidate::{core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure#1, (alloc::vec::Vec<u32>), aspis_core::v6_onefold::V6WireError>}::call_once"]
def
  aspis_core.v7_onefold.derive_v7_compact_candidate.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32V6WireError.call_once
  (c : aspis_core.v7_onefold.derive_v7_compact_candidate.closure_1)
  (tupled_args : alloc.vec.Vec Std.U32) :
  Result aspis_core.v6_onefold.V6WireError
  := do
  ok aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule

/-- Trait implementation: [aspis_core::v7_onefold::derive_v7_compact_candidate::{impl core::ops::function::FnOnce<(alloc::vec::Vec<u32>,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::derive_v7_compact_candidate::closure#1}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 85:17-85:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure#1, (alloc::vec::Vec<u32>), aspis_core::v6_onefold::V6WireError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure#1, (alloc::vec::Vec<u32>), aspis_core::v6_onefold::V6WireError>"]
def
  aspis_core.v7_onefold.derive_v7_compact_candidate.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32V6WireError
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.derive_v7_compact_candidate.closure_1 (alloc.vec.Vec
  Std.U32) aspis_core.v6_onefold.V6WireError := {
  call_once :=
    aspis_core.v7_onefold.derive_v7_compact_candidate.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32V6WireError.call_once
}

/-- [aspis_core::v7_onefold::derive_v7_compact_candidate::{impl core::ops::function::FnOnce<(aspis_core::transcript::QuerySampleError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::derive_v7_compact_candidate::closure}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 82:17-82:20
    Name pattern: [aspis_core::v7_onefold::derive_v7_compact_candidate::{core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure, (aspis_core::transcript::QuerySampleError), aspis_core::v6_onefold::V6WireError>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::derive_v7_compact_candidate::{core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure, (aspis_core::transcript::QuerySampleError), aspis_core::v6_onefold::V6WireError>}::call_once"]
def
  aspis_core.v7_onefold.derive_v7_compact_candidate.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorV6WireError.call_once
  (c : aspis_core.v7_onefold.derive_v7_compact_candidate.closure)
  (tupled_args : aspis_core.transcript.QuerySampleError) :
  Result aspis_core.v6_onefold.V6WireError
  := do
  ok aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule

/-- Trait implementation: [aspis_core::v7_onefold::derive_v7_compact_candidate::{impl core::ops::function::FnOnce<(aspis_core::transcript::QuerySampleError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::derive_v7_compact_candidate::closure}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 82:17-82:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure, (aspis_core::transcript::QuerySampleError), aspis_core::v6_onefold::V6WireError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::derive_v7_compact_candidate::closure, (aspis_core::transcript::QuerySampleError), aspis_core::v6_onefold::V6WireError>"]
def
  aspis_core.v7_onefold.derive_v7_compact_candidate.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorV6WireError
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.derive_v7_compact_candidate.closure
  aspis_core.transcript.QuerySampleError aspis_core.v6_onefold.V6WireError := {
  call_once :=
    aspis_core.v7_onefold.derive_v7_compact_candidate.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorV6WireError.call_once
}

/-- [aspis_core::v7_onefold::V7_COMPACT_FRONTIER_CAP_PER_TREE]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 29:0-29:49
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_FRONTIER_CAP_PER_TREE]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_FRONTIER_CAP_PER_TREE"]
def aspis_core.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE : Std.Usize :=
  203#usize

/-- [aspis_core::v7_onefold::derive_v7_compact_candidate]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 74:0-77:56
    Name pattern: [aspis_core::v7_onefold::derive_v7_compact_candidate] -/
@[rust_fun "aspis_core::v7_onefold::derive_v7_compact_candidate"]
def aspis_core.v7_onefold.derive_v7_compact_candidate
  (transcript : aspis_core.transcript.Transcript) (counter : Std.U8) :
  Result (core.result.Result (Option
    aspis_core.v7_onefold.V7CompactQuerySchedule)
    aspis_core.v6_onefold.V6WireError)
  := do
  let candidate_transcript ←
    aspis_core.transcript.Transcript.Insts.CoreCloneClone.clone transcript
  let s ← lift (Array.to_slice (Array.make 1#usize [ counter ]))
  let candidate_transcript1 ←
    aspis_core.transcript.Transcript.absorb candidate_transcript
      aspis_core.transcript.label.V7_QUERY_CANDIDATE s
  let i ← 1#u32 <<< 18#i32
  let (r, candidate_transcript2) ←
    aspis_core.transcript.Transcript.challenge_queries_without_replacement
      candidate_transcript1 aspis_core.v6_onefold.V6_QUERY_COUNT i 64#usize
  let r1 ←
    core.result.Result.map_err
      aspis_core.v7_onefold.derive_v7_compact_candidate.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorV6WireError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r2 ←
      Array.Insts.CoreConvertTryFromVecVec.try_from Global 16#usize val
    let r3 ←
      core.result.Result.map_err
        aspis_core.v7_onefold.derive_v7_compact_candidate.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32V6WireError
        r2 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r4 ← aspis_core.v6_onefold.binary_frontier_nodes val1 18#u8
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        if val2 <= aspis_core.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE
        then
          let a ←
            aspis_core.transcript.Transcript.diagnostic_state
              candidate_transcript2
          ok (core.result.Result.Ok (some
            {
              queries := val1,
              counter,
              frontier_nodes := val2,
              transcript_state := a,
              accepted_transcript := candidate_transcript2
            }))
        else ok (core.result.Result.Ok none)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Option aspis_core.v7_onefold.V7CompactQuerySchedule)
          (core.convert.FromSame aspis_core.v6_onefold.V6WireError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Option aspis_core.v7_onefold.V7CompactQuerySchedule)
        (core.convert.FromSame aspis_core.v6_onefold.V6WireError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Option aspis_core.v7_onefold.V7CompactQuerySchedule)
      (core.convert.FromSame aspis_core.v6_onefold.V6WireError) residual

/-- [aspis_core::v7_onefold::V7_COMPACT_QUERY_CANDIDATES]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 30:0-30:44
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_QUERY_CANDIDATES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_QUERY_CANDIDATES"]
def aspis_core.v7_onefold.V7_COMPACT_QUERY_CANDIDATES : Std.Usize := 64#usize

/-- [aspis_core::v7_onefold::derive_first_v7_compact_queries]: loop body 0:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 108:4-118:1
    Name pattern: [aspis_core::v7_onefold::derive_first_v7_compact_queries]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v7_onefold::derive_first_v7_compact_queries"]
def aspis_core.v7_onefold.derive_first_v7_compact_queries_loop.body
  (transcript : aspis_core.transcript.Transcript)
  (iter : core.ops.range.Range Std.U8) :
  Result (ControlFlow (core.ops.range.Range Std.U8) ((Option
    aspis_core.v7_onefold.V7CompactQuerySchedule) × (Option
    (core.result.Result aspis_core.v7_onefold.V7CompactQuerySchedule
    aspis_core.v6_onefold.V6WireError))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU8 iter
  match o with
  | none => ok (done (none, none))
  | some counter =>
    let r ←
      aspis_core.v7_onefold.derive_v7_compact_candidate transcript counter
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      match val with
      | none => ok (cont iter1)
      | some _ => ok (done (val, none))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let return_capture ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v7_onefold.V7CompactQuerySchedule (core.convert.FromSame
          aspis_core.v6_onefold.V6WireError) residual
      ok (done (none, some return_capture))

/-- [aspis_core::v7_onefold::derive_first_v7_compact_queries]: loop 0:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 108:4-118:1
    Name pattern: [aspis_core::v7_onefold::derive_first_v7_compact_queries]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::v7_onefold::derive_first_v7_compact_queries"]
def aspis_core.v7_onefold.derive_first_v7_compact_queries_loop
  (iter : core.ops.range.Range Std.U8)
  (transcript : aspis_core.transcript.Transcript) :
  Result ((Option aspis_core.v7_onefold.V7CompactQuerySchedule) × (Option
    (core.result.Result aspis_core.v7_onefold.V7CompactQuerySchedule
    aspis_core.v6_onefold.V6WireError)))
  := do
  loop
    (fun iter1 =>
      aspis_core.v7_onefold.derive_first_v7_compact_queries_loop.body
      transcript iter1)
    iter

/-- [aspis_core::v7_onefold::derive_first_v7_compact_queries]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 101:0-103:48
    Name pattern: [aspis_core::v7_onefold::derive_first_v7_compact_queries]
    Visibility: public -/
@[rust_fun "aspis_core::v7_onefold::derive_first_v7_compact_queries"]
def aspis_core.v7_onefold.derive_first_v7_compact_queries
  (transcript : aspis_core.transcript.Transcript) :
  Result (core.result.Result aspis_core.v7_onefold.V7CompactQuerySchedule
    aspis_core.v6_onefold.V6WireError)
  := do
  let i ←
    lift (UScalar.cast .U8 aspis_core.v7_onefold.V7_COMPACT_QUERY_CANDIDATES)
  let (accepted, pending_return) ←
    aspis_core.v7_onefold.derive_first_v7_compact_queries_loop
      { start := 0#u8, «end» := i } transcript
  match pending_return with
  | none =>
    match accepted with
    | none =>
      ok (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule)
    | some schedule => ok (core.result.Result.Ok schedule)
  | some r => ok r

/-- [aspis_core::v6_transcript::finish_v7_compact_relation::{impl core::ops::function::FnOnce<(&'_ aspis_core::transcript::Transcript,), core::result::Result<([u32; 16usize], u8, usize, [u8; 32usize], aspis_core::transcript::Transcript), aspis_core::v6_transcript::V6TranscriptError>> for aspis_core::v6_transcript::finish_v7_compact_relation::closure<QueryFold, Trace>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 994:8-994:30
    Name pattern: [aspis_core::v6_transcript::finish_v7_compact_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_v7_compact_relation::closure<@QueryFold, @Trace>, (&'_ aspis_core::transcript::Transcript), core::result::Result<([u32; 16], u8, usize, [u8; 32], aspis_core::transcript::Transcript), aspis_core::v6_transcript::V6TranscriptError>>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::finish_v7_compact_relation::{core::ops::function::FnOnce<aspis_core::v6_transcript::finish_v7_compact_relation::closure<@QueryFold, @Trace>, (&'_ aspis_core::transcript::Transcript), core::result::Result<([u32; 16], u8, usize, [u8; 32], aspis_core::transcript::Transcript), aspis_core::v6_transcript::V6TranscriptError>>}::call_once"]
def
  aspis_core.v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError.call_once
  {QueryFold : Type} {Trace : Type}
  (coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (c : aspis_core.v6_transcript.finish_v7_compact_relation.closure QueryFold
  Trace) (tupled_args : aspis_core.transcript.Transcript) :
  Result (core.result.Result ((Array Std.U32 16#usize) × Std.U8 × Std.Usize
    × (Array Std.U8 32#usize) × aspis_core.transcript.Transcript)
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  let r ← aspis_core.v7_onefold.derive_first_v7_compact_queries tupled_args
  let r1 ←
    core.result.Result.map_err (BuiltinFnOnce aspis_core.v6_onefold.V6WireError
      aspis_core.v6_transcript.V6TranscriptError) r
      (aspis_core.v6_transcript.V6TranscriptError.Wire_fn)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok (val.queries, val.counter, val.frontier_nodes,
      val.transcript_state, val.accepted_transcript))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Array Std.U32 16#usize) × Std.U8 × Std.Usize × (Array Std.U8
      32#usize) × aspis_core.transcript.Transcript) (core.convert.FromSame
      aspis_core.v6_transcript.V6TranscriptError) residual

/-- Trait implementation: [aspis_core::v6_transcript::finish_v7_compact_relation::{impl core::ops::function::FnOnce<(&'_ aspis_core::transcript::Transcript,), core::result::Result<([u32; 16usize], u8, usize, [u8; 32usize], aspis_core::transcript::Transcript), aspis_core::v6_transcript::V6TranscriptError>> for aspis_core::v6_transcript::finish_v7_compact_relation::closure<QueryFold, Trace>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 994:8-994:30
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::finish_v7_compact_relation::closure<@QueryFold, @Trace>, (&'_ aspis_core::transcript::Transcript), core::result::Result<([u32; 16], u8, usize, [u8; 32], aspis_core::transcript::Transcript), aspis_core::v6_transcript::V6TranscriptError>>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::finish_v7_compact_relation::closure<@QueryFold, @Trace>, (&'_ aspis_core::transcript::Transcript), core::result::Result<([u32; 16], u8, usize, [u8; 32], aspis_core::transcript::Transcript), aspis_core::v6_transcript::V6TranscriptError>>"]
def
  aspis_core.v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError
  {QueryFold : Type} {Trace : Type}
  (coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit) :
  core.ops.function.FnOnce
  (aspis_core.v6_transcript.finish_v7_compact_relation.closure QueryFold Trace)
  aspis_core.transcript.Transcript (core.result.Result ((Array Std.U32
  16#usize) × Std.U8 × Std.Usize × (Array Std.U8 32#usize) ×
  aspis_core.transcript.Transcript) aspis_core.v6_transcript.V6TranscriptError)
  := {
  call_once :=
    aspis_core.v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError.call_once
    coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
}

/-- [aspis_core::v6_transcript::finish_v7_compact_relation]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 963:0-977:44
    Name pattern: [aspis_core::v6_transcript::finish_v7_compact_relation] -/
@[rust_fun "aspis_core::v6_transcript::finish_v7_compact_relation"]
def aspis_core.v6_transcript.finish_v7_compact_relation
  {QueryFold : Type} {Trace : Type}
  (coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst :
  core.ops.function.FnMut Trace
  aspis_core.v6_transcript.V6RelationDiagnosticPhase Unit)
  (transcript : aspis_core.transcript.Transcript)
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (fields : aspis_core.v6_onefold.V6FixedFieldReader)
  (inactive_row_groups : Array Std.U8 64#usize)
  (inactive_group_masks : Slice Std.U16) (check_pow : Bool)
  (semantic_point : Array aspis_core.field.QM31 10#usize)
  (point_claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (query_fold : QueryFold) (trace : Trace) :
  Result (core.result.Result aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  aspis_core.v6_transcript.finish_onefold_relation
    coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    (aspis_core.v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError
    coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst)
    coreopsfunctionFnMutTraceTupleV6RelationDiagnosticPhaseTupleInst
    aspis_core.v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    transcript wire.work_nonces wire.c1_frontier wire.c2_frontier
    (Array.make 3#usize [
      aspis_core.v7_onefold.V7_COMPACT_BATCH_WORK_BITS,
      aspis_core.v7_onefold.V7_COMPACT_FOLD_WORK_BITS,
      aspis_core.v7_onefold.V7_COMPACT_FINAL_WORK_BITS
      ]) 0#u8 aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
    (aspis_core.transcript.label.V7_QUERY_BATCH_CHALLENGE,
    aspis_core.transcript.label.V7_QUERY_BATCH_CLAIM) true false () fields
    inactive_row_groups inactive_group_masks check_pow semantic_point
    point_claims query_fold trace

/-- [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{impl core::ops::function::FnMut<(aspis_core::v6_transcript::V6RelationDiagnosticPhase,), ()> for aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<TerminalCheck, QueryFold>}::call_mut]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 1207:8-1207:11
    Name pattern: [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{core::ops::function::FnMut<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>}::call_mut] -/
@[rust_fun
  "aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{core::ops::function::FnMut<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>}::call_mut"]
def
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple.call_mut
  {TerminalCheck : Type} {QueryFold : Type}
  (coreopsfunctionFnOnceTerminalCheckTupleShared0V6SemanticViewBoolInst :
  core.ops.function.FnOnce TerminalCheck
  aspis_core.v6_transcript.V6SemanticView Bool)
  (coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (c :
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure
  TerminalCheck QueryFold)
  (tupled_args : aspis_core.v6_transcript.V6RelationDiagnosticPhase) :
  Result
    (Unit ×
      aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure
      TerminalCheck QueryFold)
  := do
  ok ((), c)

/-- [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::v6_transcript::V6RelationDiagnosticPhase,), ()> for aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<TerminalCheck, QueryFold>}::call_once]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 1207:8-1207:11
    Name pattern: [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>}::call_once] -/
@[rust_fun
  "aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{core::ops::function::FnOnce<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>}::call_once"]
def
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleV6RelationDiagnosticPhaseTuple.call_once
  {TerminalCheck : Type} {QueryFold : Type}
  (coreopsfunctionFnOnceTerminalCheckTupleSharedV6SemanticViewBoolInst :
  core.ops.function.FnOnce TerminalCheck
  aspis_core.v6_transcript.V6SemanticView Bool)
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (c :
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure
  TerminalCheck QueryFold)
  (vrdp : aspis_core.v6_transcript.V6RelationDiagnosticPhase) :
  Result Unit
  := do
  let _ ←
    aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple.call_mut
      coreopsfunctionFnOnceTerminalCheckTupleSharedV6SemanticViewBoolInst
      coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
      c vrdp
  ok ()

/-- Trait implementation: [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{impl core::ops::function::FnOnce<(aspis_core::v6_transcript::V6RelationDiagnosticPhase,), ()> for aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<TerminalCheck, QueryFold>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 1207:8-1207:11
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>"]
def
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleV6RelationDiagnosticPhaseTuple
  {TerminalCheck : Type} {QueryFold : Type}
  (coreopsfunctionFnOnceTerminalCheckTupleSharedV6SemanticViewBoolInst :
  core.ops.function.FnOnce TerminalCheck
  aspis_core.v6_transcript.V6SemanticView Bool)
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError)) : core.ops.function.FnOnce
  (aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure
  TerminalCheck QueryFold) aspis_core.v6_transcript.V6RelationDiagnosticPhase
  Unit := {
  call_once :=
    aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleV6RelationDiagnosticPhaseTuple.call_once
    coreopsfunctionFnOnceTerminalCheckTupleSharedV6SemanticViewBoolInst
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
}

/-- Trait implementation: [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::{impl core::ops::function::FnMut<(aspis_core::v6_transcript::V6RelationDiagnosticPhase,), ()> for aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<TerminalCheck, QueryFold>}]
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 1207:8-1207:11
    Name pattern: [core::ops::function::FnMut<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context::closure<@TerminalCheck, @QueryFold>, (aspis_core::v6_transcript::V6RelationDiagnosticPhase), ()>"]
def
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
  {TerminalCheck : Type} {QueryFold : Type}
  (coreopsfunctionFnOnceTerminalCheckTupleSharedV6SemanticViewBoolInst :
  core.ops.function.FnOnce TerminalCheck
  aspis_core.v6_transcript.V6SemanticView Bool)
  (coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError)) : core.ops.function.FnMut
  (aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure
  TerminalCheck QueryFold) aspis_core.v6_transcript.V6RelationDiagnosticPhase
  Unit := {
  FnOnceInst :=
    aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnOnceTupleV6RelationDiagnosticPhaseTuple
    coreopsfunctionFnOnceTerminalCheckTupleSharedV6SemanticViewBoolInst
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  call_mut :=
    aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple.call_mut
    coreopsfunctionFnOnceTerminalCheckTupleSharedV6SemanticViewBoolInst
    coreopsfunctionFnOnceQueryFoldTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
}

/-- [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 1160:0-1176:95
    Name pattern: [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context]
    Visibility: public -/
@[rust_fun
  "aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context"]
def
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context
  {TerminalCheck : Type} {QueryFold : Type}
  (coreopsfunctionFnOnceTerminalCheckTupleShared0V6SemanticViewBoolInst :
  core.ops.function.FnOnce TerminalCheck
  aspis_core.v6_transcript.V6SemanticView Bool)
  (coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (context : aspis_core.v6_transcript.V6TranscriptContext)
  (hiding_context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (inactive_row_groups : Array Std.U8 64#usize)
  (inactive_group_masks : Slice Std.U16) (check_pow : Bool)
  (terminal_check : TerminalCheck) (query_fold : QueryFold) :
  Result (core.result.Result aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  let r ←
    aspis_core.v6_onefold.V6FixedFieldReader.new wire.fixed_fields_packed
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vffr =>
    let r1 ←
      aspis_core.v6_transcript.begin_v7_compact_transcript_with_hiding_context
        hash context wire hiding_context
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (transcript, lambda, chi, batching) := val
      let (r2, transcript1, vffr1) ←
        aspis_core.v6_transcript.verify_compact_semantic_sumcheck
          aspis_core.v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          transcript vffr
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (eta, semantic_point, semantic_terminal) := val1
        let (r3, transcript2, vffr2) ←
          aspis_core.v6_transcript.decode_and_absorb_point_claims
            aspis_core.v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
            transcript1 vffr1
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let b ←
            coreopsfunctionFnOnceTerminalCheckTupleShared0V6SemanticViewBoolInst.call_once
              terminal_check
              ({
                 lambda,
                 chi,
                 batching,
                 eta,
                 point := semantic_point,
                 terminal_claim := semantic_terminal,
                 point_claims := val2
               } : aspis_core.v6_transcript.V6SemanticView)
          if b
          then
            aspis_core.v6_transcript.finish_v7_compact_relation
              coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
              (aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
              coreopsfunctionFnOnceTerminalCheckTupleShared0V6SemanticViewBoolInst
              coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst)
              transcript2 wire vffr2 inactive_row_groups inactive_group_masks
              check_pow semantic_point val2 query_fold ()
          else
            ok (core.result.Result.Err
              aspis_core.v6_transcript.V6TranscriptError.TerminalRejected)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.v6_transcript.V6VerifiedTranscript
            (core.convert.FromSame aspis_core.v6_transcript.V6TranscriptError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
          aspis_core.v6_transcript.V6TranscriptError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.v6_transcript.V6VerifiedTranscript (core.convert.FromSame
        aspis_core.v6_transcript.V6TranscriptError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.v6_transcript.V6VerifiedTranscript
      aspis_core.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError
      residual

/-- [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared]:
    Source: 'crates/aspis-core/src/v6_transcript.rs', lines 1127:0-1139:95
    Name pattern: [aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared]
    Visibility: public -/
@[rust_fun
  "aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared"]
def aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared
  {TerminalCheck : Type} {QueryFold : Type}
  (coreopsfunctionFnOnceTerminalCheckTupleShared0V6SemanticViewBoolInst :
  core.ops.function.FnOnce TerminalCheck
  aspis_core.v6_transcript.V6SemanticView Bool)
  (coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
  : core.ops.function.FnOnce QueryFold
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError))
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (context : aspis_core.v6_transcript.V6TranscriptContext)
  (inactive_row_groups : Array Std.U8 64#usize)
  (inactive_group_masks : Slice Std.U16) (check_pow : Bool)
  (terminal_check : TerminalCheck) (query_fold : QueryFold) :
  Result (core.result.Result aspis_core.v6_transcript.V6VerifiedTranscript
    aspis_core.v6_transcript.V6TranscriptError)
  := do
  let sohc ←
    aspis_core.state_only_hiding.StateOnlyHidingContext.atomic_spend_v3
      context.statement_digest context.attempt_id
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context
    coreopsfunctionFnOnceTerminalCheckTupleShared0V6SemanticViewBoolInst
    coreopsfunctionFnOnceQueryFoldTupleShared0V6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireErrorInst
    hash wire context sohc inactive_row_groups inactive_group_masks check_pow
    terminal_check query_fold

/-- [aspis_core::v7_merkle208::DOM_NODE]
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 19:0-19:18
    Name pattern: [aspis_core::v7_merkle208::DOM_NODE] -/
@[global_simps, irreducible, rust_const "aspis_core::v7_merkle208::DOM_NODE"]
def aspis_core.v7_merkle208.DOM_NODE : Std.U8 := 17#u8

/-- [aspis_core::v7_merkle208::truncate_sha256_v7]:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 24:0-24:55
    Name pattern: [aspis_core::v7_merkle208::truncate_sha256_v7]
    Visibility: public -/
@[rust_fun "aspis_core::v7_merkle208::truncate_sha256_v7"]
def aspis_core.v7_merkle208.truncate_sha256_v7
  (digest : Array Std.U8 32#usize) : Result (Array Std.U8 26#usize) := do
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) digest
      { «end» := aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES }
  let r ←
    core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8 s
  match r with
  | core.result.Result.Ok value => ok value
  | core.result.Result.Err _ => fail .panic

/-- [aspis_core::v7_merkle208::private_leaf_hash_v7]:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 31:0-31:98
    Name pattern: [aspis_core::v7_merkle208::private_leaf_hash_v7]
    Visibility: public -/
@[rust_fun "aspis_core::v7_merkle208::private_leaf_hash_v7"]
def aspis_core.v7_merkle208.private_leaf_hash_v7
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tree_tag : Std.U8) (value : Slice Std.U8) (salt : Array Std.U8 32#usize) :
  Result (Array Std.U8 26#usize)
  := do
  let a ←
    aspis_core.state_only_private_merkle.private_leaf_hash hash tree_tag value
      salt
  aspis_core.v7_merkle208.truncate_sha256_v7 a

/-- [aspis_core::v7_merkle208::node_hash_v7]:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 36:0-36:80
    Name pattern: [aspis_core::v7_merkle208::node_hash_v7]
    Visibility: public -/
@[rust_fun "aspis_core::v7_merkle208::node_hash_v7"]
def aspis_core.v7_merkle208.node_hash_v7
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (left : Array Std.U8 26#usize) (right : Array Std.U8 26#usize) :
  Result (Array Std.U8 26#usize)
  := do
  let input := Array.repeat 53#usize 0#u8
  let input1 ← Array.update input 0#usize aspis_core.v7_merkle208.DOM_NODE
  let i ← 1#usize + aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input1
      { start := 1#usize, «end» := i }
  let s1 ← lift (Array.to_slice left)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let input2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) input2
      { start := i }
  let s4 ← lift (Array.to_slice right)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let input3 := index_mut_back1 s5
  let s6 ← lift (Array.to_slice input3)
  let s7 ← lift (Array.to_slice (Array.make 1#usize [ s6 ]))
  let a ← hash s7
  aspis_core.v7_merkle208.truncate_sha256_v7 a

/-- [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{impl core::ops::function::FnMut<(&'_ [(u32, [u8; 26usize], [u8; 26usize])],), bool> for aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure}::call_mut]:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 63:30-63:36
    Name pattern: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{core::ops::function::FnMut<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>}::call_mut] -/
@[rust_fun
  "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{core::ops::function::FnMut<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>}::call_mut"]
def
  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_mut
  (c : aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure)
  (tupled_args : Slice (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) :
  Result (Bool ×
    aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure)
  := do
  let (i, _, _) ← Slice.index_usize tupled_args 0#usize
  let (i1, _, _) ← Slice.index_usize tupled_args 1#usize
  ok (i >= i1, c)

/-- [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{impl core::ops::function::FnOnce<(&'_ [(u32, [u8; 26usize], [u8; 26usize])],), bool> for aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure}::call_once]:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 63:30-63:36
    Name pattern: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{core::ops::function::FnOnce<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>}::call_once] -/
@[rust_fun
  "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{core::ops::function::FnOnce<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>}::call_once"]
def
  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_once
  (c : aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure)
  (s : Slice (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) :
  Result Bool
  := do
  let (b, _) ←
    aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_mut
      c s
  ok b

/-- Trait implementation: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{impl core::ops::function::FnOnce<(&'_ [(u32, [u8; 26usize], [u8; 26usize])],), bool> for aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure}]
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 63:30-63:36
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>"]
def
  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
  : core.ops.function.FnOnce
  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure (Slice
  (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) Bool := {
  call_once :=
    aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_once
}

/-- Trait implementation: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::{impl core::ops::function::FnMut<(&'_ [(u32, [u8; 26usize], [u8; 26usize])],), bool> for aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure}]
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 63:30-63:36
    Name pattern: [core::ops::function::FnMut<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes::closure, (&'_ [(u32, [u8; 26], [u8; 26])]), bool>"]
def
  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
  : core.ops.function.FnMut
  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure (Slice
  (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) Bool := {
  FnOnceInst :=
    aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
  call_mut :=
    aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_mut
}

/-- [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]: loop body 1:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 75:8-123:1
    Name pattern: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes"]
def
  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (s : Slice Std.U8) (s1 : Slice Std.U8)
  (level : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize)))
  (next : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) (node_pos : Std.Usize) (index : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) ×
    (Array Std.U8 26#usize))) × Std.Usize × Std.Usize) ((alloc.vec.Vec
    (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) ×
    Std.Usize × (Option Bool)))
  := do
  let i := alloc.vec.Vec.len level
  if index < i
  then
    let (position, c1, c2) ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Std.U32 ×
        (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) level index
    let i1 ← lift (position &&& 1#u32)
    if i1 = 0#u32
    then
      let i2 ← index + 1#usize
      let i3 := alloc.vec.Vec.len level
      if i2 < i3
      then
        let (i4, _, _) ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Std.U32
            × (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) level i2
        let i5 ← position + 1#u32
        if i4 = i5
        then
          let (_, c1_right, c2_right) ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Std.U32
              × (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) level i2
          let index1 ← index + 2#usize
          let a ← aspis_core.v7_merkle208.node_hash_v7 hash c1 c1_right
          let a1 ← aspis_core.v7_merkle208.node_hash_v7 hash c2 c2_right
          let i6 ← position >>> 1#i32
          let next1 ← alloc.vec.Vec.push next (i6, a, a1)
          ok (cont (next1, node_pos, index1))
        else
          let i6 ← node_pos + aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
          let i7 := Slice.len s
          if i6 > i7
          then ok (done (next, node_pos, some false))
          else
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
                { start := node_pos, «end» := i6 }
            let r ←
              core.array.TryFromArrayCopySlice.try_from 26#usize
                core.marker.CopyU8 s2
            let c1_sibling ←
              match r with
              | core.result.Result.Ok value => ok value
              | core.result.Result.Err _ => fail .panic
            let s3 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s1
                { start := node_pos, «end» := i6 }
            let r1 ←
              core.array.TryFromArrayCopySlice.try_from 26#usize
                core.marker.CopyU8 s3
            let c2_sibling ←
              match r1 with
              | core.result.Result.Ok value => ok value
              | core.result.Result.Err _ => fail .panic
            let i8 ← lift (position &&& 1#u32)
            let (a, a1) ←
              if i8 = 0#u32
              then
                do
                let a2 ←
                  aspis_core.v7_merkle208.node_hash_v7 hash c1 c1_sibling
                let a3 ←
                  aspis_core.v7_merkle208.node_hash_v7 hash c2 c2_sibling
                ok (a2, a3)
              else
                do
                let a2 ←
                  aspis_core.v7_merkle208.node_hash_v7 hash c1_sibling c1
                let a3 ←
                  aspis_core.v7_merkle208.node_hash_v7 hash c2_sibling c2
                ok (a2, a3)
            let i9 ← position >>> 1#i32
            let next1 ← alloc.vec.Vec.push next (i9, a, a1)
            ok (cont (next1, i6, i2))
      else
        let i4 ← node_pos + aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
        let i5 := Slice.len s
        if i4 > i5
        then ok (done (next, node_pos, some false))
        else
          let s2 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
              { start := node_pos, «end» := i4 }
          let r ←
            core.array.TryFromArrayCopySlice.try_from 26#usize
              core.marker.CopyU8 s2
          let c1_sibling ←
            match r with
            | core.result.Result.Ok value => ok value
            | core.result.Result.Err _ => fail .panic
          let s3 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s1
              { start := node_pos, «end» := i4 }
          let r1 ←
            core.array.TryFromArrayCopySlice.try_from 26#usize
              core.marker.CopyU8 s3
          let c2_sibling ←
            match r1 with
            | core.result.Result.Ok value => ok value
            | core.result.Result.Err _ => fail .panic
          let i6 ← lift (position &&& 1#u32)
          let (a, a1) ←
            if i6 = 0#u32
            then
              do
              let a2 ←
                aspis_core.v7_merkle208.node_hash_v7 hash c1 c1_sibling
              let a3 ←
                aspis_core.v7_merkle208.node_hash_v7 hash c2 c2_sibling
              ok (a2, a3)
            else
              do
              let a2 ←
                aspis_core.v7_merkle208.node_hash_v7 hash c1_sibling c1
              let a3 ←
                aspis_core.v7_merkle208.node_hash_v7 hash c2_sibling c2
              ok (a2, a3)
          let i7 ← position >>> 1#i32
          let next1 ← alloc.vec.Vec.push next (i7, a, a1)
          ok (cont (next1, i4, i2))
    else
      let i2 ← node_pos + aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
      let i3 := Slice.len s
      if i2 > i3
      then ok (done (next, node_pos, some false))
      else
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
            { start := node_pos, «end» := i2 }
        let r ←
          core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
            s2
        let c1_sibling ←
          match r with
          | core.result.Result.Ok value => ok value
          | core.result.Result.Err _ => fail .panic
        let s3 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s1
            { start := node_pos, «end» := i2 }
        let r1 ←
          core.array.TryFromArrayCopySlice.try_from 26#usize core.marker.CopyU8
            s3
        let c2_sibling ←
          match r1 with
          | core.result.Result.Ok value => ok value
          | core.result.Result.Err _ => fail .panic
        let index1 ← index + 1#usize
        let i4 ← lift (position &&& 1#u32)
        let (a, a1) ←
          if i4 = 0#u32
          then
            do
            let a2 ← aspis_core.v7_merkle208.node_hash_v7 hash c1 c1_sibling
            let a3 ← aspis_core.v7_merkle208.node_hash_v7 hash c2 c2_sibling
            ok (a2, a3)
          else
            do
            let a2 ← aspis_core.v7_merkle208.node_hash_v7 hash c1_sibling c1
            let a3 ← aspis_core.v7_merkle208.node_hash_v7 hash c2_sibling c2
            ok (a2, a3)
        let i5 ← position >>> 1#i32
        let next1 ← alloc.vec.Vec.push next (i5, a, a1)
        ok (cont (next1, i2, index1))
  else ok (done (next, node_pos, none))

/-- [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]: loop 1:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 75:8-123:1
    Name pattern: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes"]
def aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (s : Slice Std.U8) (s1 : Slice Std.U8)
  (level : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize)))
  (next : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) (node_pos : Std.Usize) (index : Std.Usize) :
  Result ((alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
    26#usize))) × Std.Usize × (Option Bool))
  := do
  loop
    (fun (next1, node_pos1, index1) =>
      aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
      hash s s1 level next1 node_pos1 index1)
    (next, node_pos, index)

/-- [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]: loop body 0:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 72:4-123:1
    Name pattern: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes"]
def aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (s : Slice Std.U8) (s1 : Slice Std.U8) (iter : core.ops.range.Range Std.U32)
  (level : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize)))
  (next : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) (node_pos : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) ×
    (alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
    26#usize))) × Std.Usize) ((alloc.vec.Vec (Std.U32 × (Array Std.U8
    26#usize) × (Array Std.U8 26#usize))) × (alloc.vec.Vec (Std.U32 × (Array
    Std.U8 26#usize) × (Array Std.U8 26#usize))) × Std.Usize × (Option
    Bool)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done (level, next, node_pos, none))
  | some _ =>
    let next1 ← alloc.vec.Vec.clear Global next
    let (next2, node_pos1, pending_return) ←
      aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
        hash s s1 level next1 node_pos 0#usize
    match pending_return with
    | none =>
      let (level1, next3) := core.mem.swap level next2
      ok (cont (iter1, level1, next3, node_pos1))
    | some _ => ok (done (level, next2, node_pos1, pending_return))

/-- [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]: loop 0:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 72:4-123:1
    Name pattern: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes"]
def aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
  (iter : core.ops.range.Range Std.U32)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (s : Slice Std.U8) (s1 : Slice Std.U8)
  (level : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize)))
  (next : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) (node_pos : Std.Usize) :
  Result ((alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
    26#usize))) × (alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array
    Std.U8 26#usize))) × Std.Usize × (Option Bool))
  := do
  loop
    (fun (iter1, level1, next1, node_pos1) =>
      aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
      hash s s1 iter1 level1 next1 node_pos1)
    (iter, level, next, node_pos)

/-- [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]:
    Source: 'crates/aspis-core/src/v7_merkle208.rs', lines 46:0-54:9
    Name pattern: [aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes]
    Visibility: public -/
@[rust_fun "aspis_core::v7_merkle208::verify_two_minimal_subtrees_v7_bytes"]
def aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (roots : ((Array Std.U8 26#usize) × (Array Std.U8 26#usize)))
  (depth : Std.U32)
  (entries : Slice (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) (node_bytes : ((Slice Std.U8) × (Slice Std.U8)))
  (level : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize)))
  (next : alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
  26#usize))) :
  Result (Bool × (alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) × (Array
    Std.U8 26#usize))) × (alloc.vec.Vec (Std.U32 × (Array Std.U8 26#usize) ×
    (Array Std.U8 26#usize))))
  := do
  let (a, a1) := roots
  let (s, s1) := node_bytes
  let b ← core.slice.Slice.is_empty entries
  if b
  then ok (false, level, next)
  else
    if depth >= 32#u32
    then ok (false, level, next)
    else
      let i := Slice.len s
      let i1 ← i % aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
      if i1 != 0#usize
      then ok (false, level, next)
      else
        let i2 := Slice.len s1
        let i3 ← i2 % aspis_core.v7_merkle208.V7_MERKLE_DIGEST_BYTES
        if i3 != 0#usize
        then ok (false, level, next)
        else
          let i4 := Slice.len s
          let i5 := Slice.len s1
          if i4 != i5
          then ok (false, level, next)
          else
            let w ← core.slice.Slice.windows entries 2#usize
            let (b1, _) ←
              core.iter.traits.iterator.Iterator.any.default
                (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
                (Std.U32 × (Array Std.U8 26#usize) × (Array Std.U8
                26#usize)))
                aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
                w ()
            if b1
            then ok (false, level, next)
            else
              let o ← core.slice.Slice.last entries
              let (i6, _, _) ← core.option.Option.unwrap o
              let i7 ← 1#u32 <<< depth
              if i6 >= i7
              then ok (false, level, next)
              else
                let level1 ← alloc.vec.Vec.clear Global level
                let level2 ←
                  alloc.vec.Vec.extend_from_slice (BuiltinClone (Std.U32 ×
                    (Array Std.U8 26#usize) × (Array Std.U8 26#usize))) level1
                    entries
                let (level3, next1, node_pos, pending_return) ←
                  aspis_core.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
                    { start := 0#u32, «end» := depth } hash s s1 level2 next
                    0#usize
                match pending_return with
                | none =>
                  let i8 := Slice.len s
                  if node_pos = i8
                  then
                    let i9 := alloc.vec.Vec.len level3
                    if i9 = 1#usize
                    then
                      let (i10, a2, a3) ←
                        alloc.vec.Vec.index
                          (core.slice.index.SliceIndexUsizeSlice (Std.U32 ×
                          (Array Std.U8 26#usize) × (Array Std.U8 26#usize)))
                          level3 0#usize
                      if i10 = 0#u32
                      then
                        let b2 ←
                          core.array.equality.PartialEqArray.eq
                            core.cmp.PartialEqU8 a2 a
                        if b2
                        then
                          let b3 ←
                            core.array.equality.PartialEqArray.eq
                              core.cmp.PartialEqU8 a3 a1
                          ok (b3, level3, next1)
                        else ok (false, level3, next1)
                      else ok (false, level3, next1)
                    else ok (false, level3, next1)
                  else ok (false, level3, next1)
                | some b2 => ok (b2, level3, next1)

/-- [aspis_core::v7_onefold::V7_COMPACT_DIGEST_BYTES]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 26:0-26:40
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_DIGEST_BYTES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_DIGEST_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES : Std.Usize := 26#usize

/-- [aspis_core::v7_onefold::V7_COMPACT_PRIVATE_SALT_BYTES]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 47:0-47:46
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_PRIVATE_SALT_BYTES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_PRIVATE_SALT_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_PRIVATE_SALT_BYTES : Std.Usize := 32#usize

/-- [aspis_core::v7_onefold::V7_COMPACT_PRODUCTION_LIMIT_BYTES]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 48:0-48:50
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_PRODUCTION_LIMIT_BYTES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_PRODUCTION_LIMIT_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_PRODUCTION_LIMIT_BYTES
  : Result Std.Usize :=
  30#usize * 1024#usize

/-- [aspis_core::v7_onefold::V7_COMPACT_C1_BYTES_PER_QUERY]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 49:0-49:46
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_C1_BYTES_PER_QUERY]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_C1_BYTES_PER_QUERY"]
def aspis_core.v7_onefold.V7_COMPACT_C1_BYTES_PER_QUERY : Result Std.Usize :=
  aspis_core.v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY

/-- [aspis_core::v7_onefold::V7_COMPACT_C2_BYTES_PER_QUERY]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 50:0-50:46
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_C2_BYTES_PER_QUERY]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_C2_BYTES_PER_QUERY"]
def aspis_core.v7_onefold.V7_COMPACT_C2_BYTES_PER_QUERY : Result Std.Usize :=
  aspis_core.v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY

/-- [aspis_core::v7_onefold::V7_COMPACT_QUERY_BYTES]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 51:0-51:39
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_QUERY_BYTES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_QUERY_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_QUERY_BYTES : Result Std.Usize := do
  let i ← aspis_core.v7_onefold.V7_COMPACT_C1_BYTES_PER_QUERY
  let i1 ← aspis_core.v7_onefold.V7_COMPACT_C2_BYTES_PER_QUERY
  let i2 ← i + i1
  i2 + aspis_core.v7_onefold.V7_COMPACT_PRIVATE_SALT_BYTES

/-- [aspis_core::v7_onefold::V7_COMPACT_QUERY_SECTION_BYTES]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 53:0-53:47
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_QUERY_SECTION_BYTES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_QUERY_SECTION_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES
  : Result Std.Usize := do
  let i ← aspis_core.v7_onefold.V7_COMPACT_QUERY_BYTES
  aspis_core.v6_onefold.V6_QUERY_COUNT * i

/-- [aspis_core::v7_onefold::V7_COMPACT_ROOT_BYTES]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 54:0-54:38
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_ROOT_BYTES]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_ROOT_BYTES"]
def aspis_core.v7_onefold.V7_COMPACT_ROOT_BYTES : Result Std.Usize :=
  2#usize * aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES

/-- [aspis_core::v7_onefold::V7_COMPACT_BODY_WITHOUT_FRONTIERS]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 55:0-55:50
    Name pattern: [aspis_core::v7_onefold::V7_COMPACT_BODY_WITHOUT_FRONTIERS]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::v7_onefold::V7_COMPACT_BODY_WITHOUT_FRONTIERS"]
def aspis_core.v7_onefold.V7_COMPACT_BODY_WITHOUT_FRONTIERS
  : Result Std.Usize := do
  let i ← aspis_core.v6_onefold.V6_FIXED_PACKED_FIELD_BYTES
  let i1 ← aspis_core.v7_onefold.V7_COMPACT_ROOT_BYTES
  let i2 ← i + i1
  let i3 ← aspis_core.v6_onefold.V6_WORK_NONCE_BYTES
  let i4 ← i2 + i3
  let i5 ← aspis_core.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES
  i4 + i5

/-- [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#2<'a>}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 183:25-183:28
    Name pattern: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#2<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#2<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>}::call_once"]
def
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError.call_once
  (c :
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_2)
  (tupled_args : core.array.TryFromSliceError) :
  Result aspis_core.v6_onefold.V6WireError
  := do
  ok aspis_core.v6_onefold.V6WireError.WrongLength

/-- Trait implementation: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#2<'a>}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 183:25-183:28
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#2<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#2<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>"]
def
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_2
  core.array.TryFromSliceError aspis_core.v6_onefold.V6WireError := {
  call_once :=
    aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError.call_once
}

/-- [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#1<'a>}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 180:48-180:51
    Name pattern: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#1<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#1<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>}::call_once"]
def
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError.call_once
  (c :
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_1)
  (tupled_args : core.array.TryFromSliceError) :
  Result aspis_core.v6_onefold.V6WireError
  := do
  ok aspis_core.v6_onefold.V6WireError.WrongLength

/-- Trait implementation: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#1<'a>}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 180:48-180:51
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#1<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure#1<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>"]
def
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_1
  core.array.TryFromSliceError aspis_core.v6_onefold.V6WireError := {
  call_once :=
    aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError.call_once
}

/-- [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure<'a>}::call_once]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 179:48-179:51
    Name pattern: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>}::call_once] -/
@[rust_fun
  "aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>}::call_once"]
def
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError.call_once
  (c :
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure)
  (tupled_args : core.array.TryFromSliceError) :
  Result aspis_core.v6_onefold.V6WireError
  := do
  ok aspis_core.v6_onefold.V6WireError.WrongLength

/-- Trait implementation: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure<'a>}]
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 179:48-179:51
    Name pattern: [core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality::closure<'a>, (core::array::TryFromSliceError), aspis_core::v6_onefold::V6WireError>"]
def
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError
  : core.ops.function.FnOnce
  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure
  core.array.TryFromSliceError aspis_core.v6_onefold.V6WireError := {
  call_once :=
    aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError.call_once
}

/-- [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality]:
    Source: 'crates/aspis-core/src/v7_onefold.rs', lines 152:4-155:34
    Name pattern: [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality]
    Visibility: public -/
@[rust_fun
  "aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::parse_deferred_canonicality"]
def aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
  (bytes : Slice Std.U8) (frontier_nodes : Std.Usize) :
  Result (core.result.Result aspis_core.v7_onefold.V7CompactOneFoldWire
    aspis_core.v6_onefold.V6WireError)
  := do
  if frontier_nodes > aspis_core.v7_onefold.V7_COMPACT_FRONTIER_CAP_PER_TREE
  then
    ok (core.result.Result.Err
      aspis_core.v6_onefold.V6WireError.FrontierTooLarge)
  else
    let o ←
      lift (Usize.checked_mul frontier_nodes
        aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES)
    let r ←
      core.option.Option.ok_or o aspis_core.v6_onefold.V6WireError.WrongLength
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← 2#usize * val
      let i1 ← aspis_core.v7_onefold.V7_COMPACT_BODY_WITHOUT_FRONTIERS
      let o1 ← lift (Usize.checked_add i1 i)
      let r1 ←
        core.option.Option.ok_or o1
          aspis_core.v6_onefold.V6WireError.WrongLength
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i2 := Slice.len bytes
        if i2 != val1
        then
          ok (core.result.Result.Err
            aspis_core.v6_onefold.V6WireError.WrongLength)
        else
          let i3 := Slice.len bytes
          let i4 ← aspis_core.v7_onefold.V7_COMPACT_PRODUCTION_LIMIT_BYTES
          if i3 > i4
          then
            ok (core.result.Result.Err
              aspis_core.v6_onefold.V6WireError.WrongLength)
          else
            let i5 ← aspis_core.v6_onefold.V6_FIXED_PACKED_FIELD_BYTES
            let (fixed_fields_packed, rest) ←
              core.slice.Slice.split_at bytes i5
            let o2 ← core.slice.Slice.last fixed_fields_packed
            let o3 ← core.option.OptionShared0T.copied core.marker.CopyU8 o2
            let i6 ←
              core.option.Option.unwrap_or_default core.default.DefaultU8 o3
            let i7 ← lift (i6 &&& 240#u8)
            if i7 != 0#u8
            then
              ok (core.result.Result.Err
                aspis_core.v6_onefold.V6WireError.NonCanonicalM31)
            else
              let (c1_root, rest1) ←
                core.slice.Slice.split_at rest
                  aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES
              let (c2_root, rest2) ←
                core.slice.Slice.split_at rest1
                  aspis_core.v7_onefold.V7_COMPACT_DIGEST_BYTES
              let i8 ← aspis_core.v6_onefold.V6_WORK_NONCE_BYTES
              let (work_nonces, rest3) ← core.slice.Slice.split_at rest2 i8
              let i9 ← aspis_core.v7_onefold.V7_COMPACT_QUERY_SECTION_BYTES
              let (query_section, rest4) ← core.slice.Slice.split_at rest3 i9
              let (c1_frontier, c2_frontier) ←
                core.slice.Slice.split_at rest4 val
              let r2 ←
                core.array.TryFromSharedArraySlice.try_from 26#usize c1_root
              let r3 ←
                core.result.Result.map_err
                  aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError
                  r2 ()
              let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf2 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let r4 ←
                  core.array.TryFromSharedArraySlice.try_from 26#usize c2_root
                let r5 ←
                  core.result.Result.map_err
                    aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError
                    r4 ()
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf3 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let r6 ←
                    core.array.TryFromSharedArraySlice.try_from 24#usize
                      work_nonces
                  let r7 ←
                    core.result.Result.map_err
                      aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorV6WireError
                      r6 ()
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    ok (core.result.Result.Ok
                      {
                        fixed_fields_packed,
                        c1_root := val2,
                        c2_root := val3,
                        work_nonces := val4,
                        query_section,
                        c1_frontier,
                        c2_frontier
                      })
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      aspis_core.v7_onefold.V7CompactOneFoldWire
                      (core.convert.FromSame aspis_core.v6_onefold.V6WireError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    aspis_core.v7_onefold.V7CompactOneFoldWire
                    (core.convert.FromSame aspis_core.v6_onefold.V6WireError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  aspis_core.v7_onefold.V7CompactOneFoldWire
                  (core.convert.FromSame aspis_core.v6_onefold.V6WireError)
                  residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.v7_onefold.V7CompactOneFoldWire (core.convert.FromSame
          aspis_core.v6_onefold.V6WireError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.v7_onefold.V7CompactOneFoldWire (core.convert.FromSame
        aspis_core.v6_onefold.V6WireError) residual


end V7Tag73CurrentHelpersOpaque
