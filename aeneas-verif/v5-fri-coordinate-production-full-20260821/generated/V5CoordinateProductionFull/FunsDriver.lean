-- Deterministic low-memory proof view of the recorded Aeneas output.
-- The prefix through `selected_circle_fiber_points_shared` is byte-for-byte
-- the previously checked direct extraction, so reuse that module and append
-- only the remaining declarations from this complete extraction.
import V5CoordinateSelectedProduction.FunsSelected
import V5CoordinateProductionFull.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section
namespace V5CoordinateSelectedProductionSource

/-- [aspis_core_parent_helper_extraction::circle_fri::double_point]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 308:0-316:1 -/
def circle_fri.double_point
  (point : circle_fri.BaseCirclePoint) :
  Result circle_fri.BaseCirclePoint
  := do
  let m ← field.M31.add point.x point.y
  let m1 ← field.M31.sub point.x point.y
  let m2 ← field.M31.mul m m1
  let m3 ← field.M31.mul point.x point.y
  let m4 ← field.M31.double m3
  ok { x := m2, y := m4 }

/-- [aspis_core_parent_helper_extraction::field::{aspis_core_parent_helper_extraction::field::M31}::neg]:
    Source: '../../../crates/aspis-core/src/field.rs', lines 68:4-74:5
    Visibility: public -/
def field.M31.neg (self : field.M31) : Result field.M31 := do
  if self = 0#u32
  then ok 0#u32
  else let i ← field.P - self
       ok i

/-- [aspis_core_parent_helper_extraction::circle_fri::remove_line_slot_rotation]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 322:0-339:1 -/
def circle_fri.remove_line_slot_rotation
  (point : circle_fri.BaseCirclePoint) (slot : Std.U32) :
  Result circle_fri.BaseCirclePoint
  := do
  match slot with
  | 0#uscalar => ok point
  | 1#uscalar =>
    let m ← field.M31.neg point.x
    let m1 ← field.M31.neg point.y
    ok { x := m, y := m1 }
  | 2#uscalar => let m ← field.M31.neg point.y
                 ok { x := m, y := point.x }
  | 3#uscalar => let m ← field.M31.neg point.x
                 ok { x := point.y, y := m }
  | _ => fail panic

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points]: loop body 1:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 358:8-360:9 -/
@[rust_loop_body]
def circle_fri.derive_parent_line_points_loop0_loop0.body
  (child_indices : Slice Std.U32) (parent : Std.U32)
  (child_ordinal : Std.Usize) :
  Result (ControlFlow Std.Usize Std.Usize)
  := do
  let i := Slice.len child_indices
  if child_ordinal < i
  then
    let i1 ← Slice.index_usize child_indices child_ordinal
    let i2 ← i1 >>> 2#i32
    if i2 < parent
    then
      let child_ordinal1 ← child_ordinal + 1#usize
      ok (cont child_ordinal1)
    else ok (done child_ordinal)
  else ok (done child_ordinal)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points]: loop 1:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 358:8-360:9 -/
@[rust_loop]
def circle_fri.derive_parent_line_points_loop0_loop0
  (child_indices : Slice Std.U32) (child_ordinal : Std.Usize)
  (parent : Std.U32) :
  Result Std.Usize
  := do
  loop
    (fun child_ordinal1 =>
      circle_fri.derive_parent_line_points_loop0_loop0.body child_indices
      parent child_ordinal1)
    child_ordinal

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points]: loop body 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 357:4-375:1 -/
@[rust_loop_body]
def circle_fri.derive_parent_line_points_loop0.body
  (child_indices : Slice Std.U32)
  (child_points : Slice circle_fri.BaseCirclePoint) (doublings : Std.U8)
  (iter : core.slice.iter.Iter Std.U32)
  (parents : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (child_ordinal : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × (alloc.vec.Vec
    circle_fri.BaseCirclePoint) × Std.Usize) (core.result.Result
    (alloc.vec.Vec circle_fri.BaseCirclePoint) circle_fri.CircleFriError))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (core.result.Result.Ok parents))
  | some parent =>
    let child_ordinal1 ←
      circle_fri.derive_parent_line_points_loop0_loop0 child_indices
        child_ordinal parent
    let o1 ←
      core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice Std.U32)
        child_indices child_ordinal1
    let r ←
      core.option.Option.ok_or o1 circle_fri.CircleFriError.QueryOutOfRange
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← val >>> 2#i32
      if i != parent
      then
        ok (done (core.result.Result.Err
          circle_fri.CircleFriError.QueryOutOfRange))
      else
        if doublings = 1#u8
        then ok ()
        else massert (doublings = 2#u8)
        let bcp ← Slice.index_usize child_points child_ordinal1
        let point ← circle_fri.double_point bcp
        let point1 ←
          if doublings = 2#u8
          then circle_fri.double_point point
          else ok point
        let i1 ← lift (val &&& 3#u32)
        let bcp1 ← circle_fri.remove_line_slot_rotation point1 i1
        let parents1 ← alloc.vec.Vec.push parents bcp1
        ok (cont (iter1, parents1, child_ordinal1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec circle_fri.BaseCirclePoint) (core.convert.FromSame
          circle_fri.CircleFriError) residual
      ok (done r1)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points]: loop 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 357:4-375:1 -/
@[rust_loop]
def circle_fri.derive_parent_line_points_loop0
  (iter : core.slice.iter.Iter Std.U32) (child_indices : Slice Std.U32)
  (child_points : Slice circle_fri.BaseCirclePoint) (doublings : Std.U8)
  (parents : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (child_ordinal : Std.Usize) :
  Result (core.result.Result (alloc.vec.Vec circle_fri.BaseCirclePoint)
    circle_fri.CircleFriError)
  := do
  loop
    (fun (iter1, parents1, child_ordinal1) =>
      circle_fri.derive_parent_line_points_loop0.body child_indices
      child_points doublings iter1 parents1 child_ordinal1)
    (iter, parents, child_ordinal)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 346:0-375:1 -/
def circle_fri.derive_parent_line_points
  (child_indices : Slice Std.U32)
  (child_points : Slice circle_fri.BaseCirclePoint)
  (parent_indices : Slice Std.U32) (doublings : Std.U8) :
  Result (core.result.Result (alloc.vec.Vec circle_fri.BaseCirclePoint)
    circle_fri.CircleFriError)
  := do
  let i := Slice.len child_indices
  let i1 := Slice.len child_points
  if i != i1
  then ok (core.result.Result.Err circle_fri.CircleFriError.QueryOutOfRange)
  else
    let i2 := Slice.len parent_indices
    let parents := alloc.vec.Vec.with_capacity circle_fri.BaseCirclePoint i2
    let iter ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
        parent_indices
    circle_fri.derive_parent_line_points_loop0 iter child_indices child_points
      doublings parents 0#usize

/-- [aspis_core_parent_helper_extraction::field::{aspis_core_parent_helper_extraction::field::M31}::ONE]
    Source: '../../../crates/aspis-core/src/field.rs', lines 53:4-53:32
    Visibility: public -/
@[global_simps, irreducible] def field.M31.ONE : field.M31 := 1#u32

/-- [aspis_core_parent_helper_extraction::field::m31_batch_inverse_with]: loop body 0:
    Source: '../../../crates/aspis-core/src/field.rs', lines 1876:4-1879:5
    Visibility: public -/
@[rust_loop_body]
def field.m31_batch_inverse_with_loop0.body
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  field.M31)) (out : Slice field.M31) (accumulator : field.M31) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter field.M31)) × (Slice field.M31) × field.M31)
    ((Slice field.M31) × field.M31))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter field.M31) iter
  match o with
  | none => ok (done (out, accumulator))
  | some p =>
    let (index, value) := p
    let s ← Slice.update out index accumulator
    let accumulator1 ← field.M31.mul accumulator value
    ok (cont (iter1, s, accumulator1))

/-- [aspis_core_parent_helper_extraction::field::m31_batch_inverse_with]: loop 0:
    Source: '../../../crates/aspis-core/src/field.rs', lines 1876:4-1879:5
    Visibility: public -/
@[rust_loop]
def field.m31_batch_inverse_with_loop0
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  field.M31)) (out : Slice field.M31) (accumulator : field.M31) :
  Result ((Slice field.M31) × field.M31)
  := do
  loop
    (fun (iter1, out1, accumulator1) => field.m31_batch_inverse_with_loop0.body
      iter1 out1 accumulator1)
    (iter, out, accumulator)

/-- [aspis_core_parent_helper_extraction::field::m31_batch_inverse_with]: loop body 1:
    Source: '../../../crates/aspis-core/src/field.rs', lines 1881:4-1885:5
    Visibility: public -/
@[rust_loop_body]
def field.m31_batch_inverse_with_loop1.body
  (values : Slice field.M31)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (out : Slice field.M31) (inverse : field.M31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Slice field.M31) × field.M31) (Slice field.M31))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done out)
  | some index =>
    let prefix1 ← Slice.index_usize out index
    let m ← field.M31.mul prefix1 inverse
    let s ← Slice.update out index m
    let m1 ← Slice.index_usize values index
    let inverse1 ← field.M31.mul inverse m1
    ok (cont (iter1, s, inverse1))

/-- [aspis_core_parent_helper_extraction::field::m31_batch_inverse_with]: loop 1:
    Source: '../../../crates/aspis-core/src/field.rs', lines 1881:4-1885:5
    Visibility: public -/
@[rust_loop]
def field.m31_batch_inverse_with_loop1
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (values : Slice field.M31) (out : Slice field.M31) (inverse : field.M31) :
  Result (Slice field.M31)
  := do
  loop
    (fun (iter1, out1, inverse1) => field.m31_batch_inverse_with_loop1.body
      values iter1 out1 inverse1)
    (iter, out, inverse)

/-- [aspis_core_parent_helper_extraction::field::m31_batch_inverse_with]:
    Source: '../../../crates/aspis-core/src/field.rs', lines 1870:0-1886:1
    Visibility: public -/
def field.m31_batch_inverse_with
  (values : Slice field.M31) (out : Slice field.M31)
  (inverse : field.M31 → field.M31) :
  Result (Slice field.M31)
  := do
  let left_val := Slice.len values
  let right_val := Slice.len out
  massert (left_val = right_val)
  let b ← core.slice.Slice.is_empty values
  if b
  then ok out
  else
    let i ← core.slice.Slice.iter values
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter field.M31) i
    let (out1, accumulator) ←
      field.m31_batch_inverse_with_loop0 iter out field.M31.ONE
    let inverse1 := inverse accumulator
    let i1 := Slice.len values
    let iter1 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator
        core.iter.range.StepUsize) { start := 0#usize, «end» := i1 }
    field.m31_batch_inverse_with_loop1 iter1 values out1 inverse1

/-- [aspis_core_parent_helper_extraction::field::{aspis_core_parent_helper_extraction::field::M31}::is_zero]:
    Source: '../../../crates/aspis-core/src/field.rs', lines 173:4-175:5
    Visibility: public -/
def field.M31.is_zero (self : field.M31) : Result Bool := do
  ok (self = 0#u32)

/-- [aspis_core_parent_helper_extraction::field::{aspis_core_parent_helper_extraction::field::M31}::ZERO]
    Source: '../../../crates/aspis-core/src/field.rs', lines 52:4-52:33
    Visibility: public -/
@[global_simps, irreducible] def field.M31.ZERO : field.M31 := 0#u32

/-- [aspis_core_parent_helper_extraction::field::{impl core::cmp::PartialEq<aspis_core_parent_helper_extraction::field::M31> for aspis_core_parent_helper_extraction::field::M31}::eq]:
    Source: '../../../crates/aspis-core/src/field.rs', lines 19:22-19:31
    Visibility: public -/
def field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : field.M31) (other : field.M31) : Result Bool := do
  ok (self = other)

/-- Trait implementation: [aspis_core_parent_helper_extraction::field::{impl core::cmp::PartialEq<aspis_core_parent_helper_extraction::field::M31> for aspis_core_parent_helper_extraction::field::M31}]
    Source: '../../../crates/aspis-core/src/field.rs', lines 19:22-19:31 -/
@[reducible]
impl_def field.M31.Insts.CoreCmpPartialEqM31 : core.cmp.PartialEq field.M31
  field.M31 := {
  eq := field.M31.Insts.CoreCmpPartialEqM31.eq
  ne := core.cmp.PartialEq.ne.trait_default field.M31.Insts.CoreCmpPartialEqM31
}

/-- [aspis_core_parent_helper_extraction::field::{impl core::clone::Clone for aspis_core_parent_helper_extraction::field::M31}::clone]:
    Source: '../../../crates/aspis-core/src/field.rs', lines 19:9-19:14
    Visibility: public -/
def field.M31.Insts.CoreCloneClone.clone
  (self : field.M31) : Result field.M31 := do
  ok self

/-- Trait implementation: [aspis_core_parent_helper_extraction::field::{impl core::clone::Clone for aspis_core_parent_helper_extraction::field::M31}]
    Source: '../../../crates/aspis-core/src/field.rs', lines 19:9-19:14 -/
@[reducible]
def field.M31.Insts.CoreCloneClone : core.clone.Clone field.M31 := {
  clone := field.M31.Insts.CoreCloneClone.clone
}

/-- [aspis_core_parent_helper_extraction::circle_fri::double_x]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 1031:0-1033:1 -/
def circle_fri.double_x (x : field.M31) : Result field.M31 := do
  let m ← field.M31.mul x x
  let m1 ← field.M31.double m
  field.M31.sub m1 field.M31.ONE

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#2]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 487:13-487:48 -/
@[reducible]
def circle_fri.derive_query_fold_inverses_for_circle.closure_2 := Unit

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnMut<(&'_ aspis_core_parent_helper_extraction::circle_fri::BaseCirclePoint,), aspis_core_parent_helper_extraction::field::M31> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#2}::call_mut]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 487:13-487:48 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31.call_mut
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure_2)
  (tupled_args : circle_fri.BaseCirclePoint) :
  Result (field.M31 ×
    circle_fri.derive_query_fold_inverses_for_circle.closure_2)
  := do
  let m ← circle_fri.double_x tupled_args.x
  let m1 ← circle_fri.double_x m
  ok (m1, c)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnOnce<(&'_ aspis_core_parent_helper_extraction::circle_fri::BaseCirclePoint,), aspis_core_parent_helper_extraction::field::M31> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#2}::call_once]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 487:13-487:48 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedBaseCirclePointM31.call_once
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure_2)
  (bcp : circle_fri.BaseCirclePoint) :
  Result field.M31
  := do
  let (m, _) ←
    circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31.call_mut
      c bcp
  ok m

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnOnce<(&'_ aspis_core_parent_helper_extraction::circle_fri::BaseCirclePoint,), aspis_core_parent_helper_extraction::field::M31> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#2}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 487:13-487:48 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedBaseCirclePointM31
  : core.ops.function.FnOnce
  circle_fri.derive_query_fold_inverses_for_circle.closure_2
  circle_fri.BaseCirclePoint field.M31 := {
  call_once :=
    circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedBaseCirclePointM31.call_once
}

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnMut<(&'_ aspis_core_parent_helper_extraction::circle_fri::BaseCirclePoint,), aspis_core_parent_helper_extraction::field::M31> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#2}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 487:13-487:48 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31
  : core.ops.function.FnMut
  circle_fri.derive_query_fold_inverses_for_circle.closure_2
  circle_fri.BaseCirclePoint field.M31 := {
  FnOnceInst :=
    circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedBaseCirclePointM31
  call_mut :=
    circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31.call_mut
}

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#1]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 471:66-482:5 -/
def circle_fri.derive_query_fold_inverses_for_circle.closure_1 :=
  Array (Slice Std.U32) 3#usize × alloc.vec.Vec field.M31 × Std.Usize

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnMut<(usize,), alloc::vec::Vec<[aspis_core_parent_helper_extraction::field::M31; 3usize]>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#1<'_0, '_1, '_2, '_3>}::call_mut]: loop body 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 473:8-480:9 -/
@[rust_loop_body]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop.body
  (v : alloc.vec.Vec field.M31) (iter : core.slice.iter.Iter Std.U32)
  (i : Std.Usize) (values : alloc.vec.Vec (Array field.M31 3#usize)) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × Std.Usize ×
    (alloc.vec.Vec (Array field.M31 3#usize))) (Std.Usize × (alloc.vec.Vec
    (Array field.M31 3#usize))))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (i, values))
  | some _ =>
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31) v i
    let i1 ← i + 1#usize
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31) v
        i1
    let i2 ← i + 2#usize
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31) v
        i2
    let values1 ←
      alloc.vec.Vec.push values (Array.make 3#usize [ m, m1, m2 ] : Array
        field.M31 3#usize)
    let i3 ← i + 3#usize
    ok (cont (iter1, i3, values1))

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnMut<(usize,), alloc::vec::Vec<[aspis_core_parent_helper_extraction::field::M31; 3usize]>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#1<'_0, '_1, '_2, '_3>}::call_mut]: loop 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 473:8-480:9 -/
@[rust_loop]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop
  (iter : core.slice.iter.Iter Std.U32) (v : alloc.vec.Vec field.M31)
  (i : Std.Usize) (values : alloc.vec.Vec (Array field.M31 3#usize)) :
  Result (Std.Usize × (alloc.vec.Vec (Array field.M31 3#usize)))
  := do
  loop
    (fun (iter1, i1, values1) =>
      circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop.body
      v iter1 i1 values1)
    (iter, i, values)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnMut<(usize,), alloc::vec::Vec<[aspis_core_parent_helper_extraction::field::M31; 3usize]>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#1<'_0, '_1, '_2, '_3>}::call_mut]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 471:66-482:5 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure_1)
  (tupled_args : Std.Usize) :
  Result ((alloc.vec.Vec (Array field.M31 3#usize)) ×
    circle_fri.derive_query_fold_inverses_for_circle.closure_1 ×
    (circle_fri.derive_query_fold_inverses_for_circle.closure_1 →
    circle_fri.derive_query_fold_inverses_for_circle.closure_1))
  := do
  let (a, v, i) := c
  let s ← Array.index_usize a tupled_args
  let i1 := Slice.len s
  let values := alloc.vec.Vec.with_capacity (Array field.M31 3#usize) i1
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
  let (i2, values1) ←
    circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop
      iter v i values
  let back := fun c1 => let (_, _, i3) := c1
                        (a, v, i3)
  ok (values1, (a, v, i2), back)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnOnce<(usize,), alloc::vec::Vec<[aspis_core_parent_helper_extraction::field::M31; 3usize]>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#1<'_0, '_1, '_2, '_3>}::call_once]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 471:66-482:5 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeVecArrayM313.call_once
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure_1)
  (i : Std.Usize) :
  Result ((alloc.vec.Vec (Array field.M31 3#usize)) ×
    circle_fri.derive_query_fold_inverses_for_circle.closure_1)
  := do
  let (a, v, _) := c
  let (v1, c1, call_mut_back) ←
    circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut
      c i
  let (_, _, i1) := call_mut_back c1
  ok (v1, (a, v, i1))

/-- Trait-shaped view of the generated consuming call.  The raw translation
returns its final captured cursor for borrow synthesis; Rust consumes the
closure here, so the `FnOnce` result is only the produced vector. -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeVecArrayM313.call_once_trait
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure_1)
  (i : Std.Usize) :
  Result (alloc.vec.Vec (Array field.M31 3#usize)) := do
  let (values, _) ←
    circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeVecArrayM313.call_once
      c i
  ok values

/-- Trait-shaped view of the generated mutable call.  Applying the generated
hand-back function to the returned closure state is exactly Aeneas's model of
writing the new cursor through the captured mutable reference. -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_trait
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure_1)
  (i : Std.Usize) :
  Result ((alloc.vec.Vec (Array field.M31 3#usize)) ×
    circle_fri.derive_query_fold_inverses_for_circle.closure_1) := do
  let (values, updated, handBack) ←
    circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut
      c i
  ok (values, handBack updated)

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnOnce<(usize,), alloc::vec::Vec<[aspis_core_parent_helper_extraction::field::M31; 3usize]>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#1<'_0, '_1, '_2, '_3>}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 471:66-482:5 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeVecArrayM313
  : core.ops.function.FnOnce
  circle_fri.derive_query_fold_inverses_for_circle.closure_1 Std.Usize
  (alloc.vec.Vec (Array field.M31 3#usize)) := {
  call_once :=
    circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeVecArrayM313.call_once_trait
}

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnMut<(usize,), alloc::vec::Vec<[aspis_core_parent_helper_extraction::field::M31; 3usize]>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure#1<'_0, '_1, '_2, '_3>}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 471:66-482:5 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313
  : core.ops.function.FnMut
  circle_fri.derive_query_fold_inverses_for_circle.closure_1 Std.Usize
  (alloc.vec.Vec (Array field.M31 3#usize)) := {
  FnOnceInst :=
    circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeVecArrayM313
  call_mut :=
    circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_trait
}

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure::{impl core::ops::function::FnOnce<(usize,), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure::closure<'_0>}::call_once]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 410:30-410:62 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once
  (c :
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.closure)
  (tupled_args : Std.Usize) :
  Result (Option Std.Usize)
  := do
  ok (Usize.checked_add c tupled_args)

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure::{impl core::ops::function::FnOnce<(usize,), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure::closure<'_0>}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 410:30-410:62 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
  : core.ops.function.FnOnce
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.closure
  Std.Usize (Option Std.Usize) := {
  call_once :=
    circle_fri.derive_query_fold_inverses_for_circle.closure.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once
}

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::{impl core::ops::function::FnMut<(usize, &'_ &'_ [u32]), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure}::call_mut]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 406:41-411:13 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedSharedSliceU32OptionUsize.call_mut
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure.closure)
  (tupled_args : (Std.Usize × (Slice Std.U32))) :
  Result ((Option Std.Usize) ×
    circle_fri.derive_query_fold_inverses_for_circle.closure.closure)
  := do
  let (count, indices) := tupled_args
  let i := Slice.len indices
  let o ← lift (Usize.checked_mul i 3#usize)
  let o1 ←
    core.option.Option.and_then
      circle_fri.derive_query_fold_inverses_for_circle.closure.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
      o count
  ok (o1, c)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::{impl core::ops::function::FnOnce<(usize, &'_ &'_ [u32]), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure}::call_once]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 406:41-411:13 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnOncePairUsizeSharedSharedSliceU32OptionUsize.call_once
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure.closure)
  (p : (Std.Usize × (Slice Std.U32))) :
  Result (Option Std.Usize)
  := do
  let (o, _) ←
    circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedSharedSliceU32OptionUsize.call_mut
      c p
  ok o

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::{impl core::ops::function::FnOnce<(usize, &'_ &'_ [u32]), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 406:41-411:13 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnOncePairUsizeSharedSharedSliceU32OptionUsize
  : core.ops.function.FnOnce
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure (Std.Usize
  × (Slice Std.U32)) (Option Std.Usize) := {
  call_once :=
    circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnOncePairUsizeSharedSharedSliceU32OptionUsize.call_once
}

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::{impl core::ops::function::FnMut<(usize, &'_ &'_ [u32]), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure::closure}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 406:41-411:13 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedSharedSliceU32OptionUsize
  : core.ops.function.FnMut
  circle_fri.derive_query_fold_inverses_for_circle.closure.closure (Std.Usize
  × (Slice Std.U32)) (Option Std.Usize) := {
  FnOnceInst :=
    circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnOncePairUsizeSharedSharedSliceU32OptionUsize
  call_mut :=
    circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedSharedSliceU32OptionUsize.call_mut
}

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnOnce<(usize,), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure<'_0, '_1>}::call_once]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 405:18-412:9 -/
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once
  (c : circle_fri.derive_query_fold_inverses_for_circle.closure)
  (tupled_args : Std.Usize) :
  Result (Option Std.Usize)
  := do
  let s ← lift (Array.to_slice c)
  let i ← core.slice.Slice.iter s
  let (o, _) ←
    core.iter.traits.iterator.Iterator.try_fold.default
      (core.iter.traits.iterator.IteratorSliceIter (Slice Std.U32))
      circle_fri.derive_query_fold_inverses_for_circle.closure.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedSharedSliceU32OptionUsize
      (core.option.Option.Insts.CoreOpsTry_traitTry Std.Usize) i tupled_args ()
  ok o

/-- Trait implementation: [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::{impl core::ops::function::FnOnce<(usize,), core::option::Option<usize>> for aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle::closure<'_0, '_1>}]
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 405:18-412:9 -/
@[reducible]
def
  circle_fri.derive_query_fold_inverses_for_circle.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
  : core.ops.function.FnOnce
  circle_fri.derive_query_fold_inverses_for_circle.closure Std.Usize (Option
  Std.Usize) := {
  call_once :=
    circle_fri.derive_query_fold_inverses_for_circle.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once
}

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop body 2:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 467:4-470:5
    Visibility: public -/
@[rust_loop_body]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop0.body
  (flat_inverses : alloc.vec.Vec field.M31)
  (iter : core.slice.iter.Iter Std.U32) (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array field.M31 2#usize)) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × Std.Usize ×
    (alloc.vec.Vec (Array field.M31 2#usize))) (Std.Usize × (alloc.vec.Vec
    (Array field.M31 2#usize))))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (cursor, circle))
  | some _ =>
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
        flat_inverses cursor
    let i ← cursor + 1#usize
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
        flat_inverses i
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array field.M31
        2#usize)
    let cursor1 ← cursor + 2#usize
    ok (cont (iter1, cursor1, circle1))

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop 2:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 467:4-470:5
    Visibility: public -/
@[rust_loop]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop0
  (iter : core.slice.iter.Iter Std.U32)
  (flat_inverses : alloc.vec.Vec field.M31) (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array field.M31 2#usize)) :
  Result (Std.Usize × (alloc.vec.Vec (Array field.M31 2#usize)))
  := do
  loop
    (fun (iter1, cursor1, circle1) =>
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop0.body
      flat_inverses iter1 cursor1 circle1)
    (iter, cursor, circle)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop body 3:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 467:4-470:5
    Visibility: public -/
@[rust_loop_body]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop1.body
  (flat_inverses : alloc.vec.Vec field.M31)
  (iter : core.slice.iter.Iter Std.U32) (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array field.M31 2#usize)) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × Std.Usize ×
    (alloc.vec.Vec (Array field.M31 2#usize))) (Std.Usize × (alloc.vec.Vec
    (Array field.M31 2#usize))))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (cursor, circle))
  | some _ =>
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
        flat_inverses cursor
    let i ← cursor + 1#usize
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
        flat_inverses i
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array field.M31
        2#usize)
    let cursor1 ← cursor + 2#usize
    ok (cont (iter1, cursor1, circle1))

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop 3:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 467:4-470:5
    Visibility: public -/
@[rust_loop]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop1
  (iter : core.slice.iter.Iter Std.U32)
  (flat_inverses : alloc.vec.Vec field.M31) (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array field.M31 2#usize)) :
  Result (Std.Usize × (alloc.vec.Vec (Array field.M31 2#usize)))
  := do
  loop
    (fun (iter1, cursor1, circle1) =>
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop1.body
      flat_inverses iter1 cursor1 circle1)
    (iter, cursor, circle)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop body 4:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 467:4-470:5
    Visibility: public -/
@[rust_loop_body]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2.body
  (flat_inverses : alloc.vec.Vec field.M31)
  (iter : core.slice.iter.Iter Std.U32) (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array field.M31 2#usize)) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × Std.Usize ×
    (alloc.vec.Vec (Array field.M31 2#usize))) (Std.Usize × (alloc.vec.Vec
    (Array field.M31 2#usize))))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (cursor, circle))
  | some _ =>
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
        flat_inverses cursor
    let i ← cursor + 1#usize
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
        flat_inverses i
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array field.M31
        2#usize)
    let cursor1 ← cursor + 2#usize
    ok (cont (iter1, cursor1, circle1))

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop 4:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 467:4-470:5
    Visibility: public -/
@[rust_loop]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2
  (iter : core.slice.iter.Iter Std.U32)
  (flat_inverses : alloc.vec.Vec field.M31) (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array field.M31 2#usize)) :
  Result (Std.Usize × (alloc.vec.Vec (Array field.M31 2#usize)))
  := do
  loop
    (fun (iter1, cursor1, circle1) =>
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2.body
      flat_inverses iter1 cursor1 circle1)
    (iter, cursor, circle)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop body 6:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 437:12-448:5
    Visibility: public -/
@[rust_loop_body]
def
  circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0.body
  (iter : core.iter.adapters.zip.Zip (core.array.iter.IntoIter field.M31
  3#usize) (core.array.iter.IntoIter circle_fri.FoldDenominator 3#usize))
  (denominators : alloc.vec.Vec field.M31) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.array.iter.IntoIter
    field.M31 3#usize) (core.array.iter.IntoIter circle_fri.FoldDenominator
    3#usize)) × (alloc.vec.Vec field.M31)) ((alloc.vec.Vec field.M31) ×
    (Option (core.result.Result circle_fri.DerivedCircleQueryFoldInverses
    circle_fri.CircleFriError))))
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator field.M31
      3#usize) (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
      circle_fri.FoldDenominator 3#usize) iter
  match o with
  | none => ok (done (denominators, none))
  | some p =>
    let (coordinate, kind) := p
    let b ← field.M31.is_zero coordinate
    if b
    then
      ok (done (denominators, some (core.result.Result.Err
        (circle_fri.CircleFriError.ZeroDenominator kind))))
    else
      let denominators1 ← alloc.vec.Vec.push denominators coordinate
      ok (cont (iter1, denominators1))

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop 6:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 437:12-448:5
    Visibility: public -/
@[rust_loop]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0
  (iter : core.iter.adapters.zip.Zip (core.array.iter.IntoIter field.M31
  3#usize) (core.array.iter.IntoIter circle_fri.FoldDenominator 3#usize))
  (denominators : alloc.vec.Vec field.M31) :
  Result ((alloc.vec.Vec field.M31) × (Option (core.result.Result
    circle_fri.DerivedCircleQueryFoldInverses circle_fri.CircleFriError)))
  := do
  loop
    (fun (iter1, denominators1) =>
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0.body
      iter1 denominators1)
    (iter, denominators)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop body 5:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 427:8-448:5
    Visibility: public -/
@[rust_loop_body]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3.body
  (iter : core.slice.iter.Iter circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec field.M31) :
  Result (ControlFlow ((core.slice.iter.Iter circle_fri.BaseCirclePoint) ×
    (alloc.vec.Vec field.M31)) ((alloc.vec.Vec field.M31) × (Option
    (core.result.Result circle_fri.DerivedCircleQueryFoldInverses
    circle_fri.CircleFriError))))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (denominators, none))
  | some point =>
    let m ← field.M31.double point.x
    let m1 ← field.M31.double point.y
    let m2 ← circle_fri.double_x point.x
    let m3 ← field.M31.double m2
    let ii ←
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
        (Array.make 3#usize [ m, m1, m3 ])
    let iter2 ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
        field.M31 3#usize)
        (Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
        circle_fri.FoldDenominator 3#usize) ii
        (Array.make 3#usize [
          circle_fri.FoldDenominator.LineFirstPairX,
          circle_fri.FoldDenominator.LineSecondPairX,
          circle_fri.FoldDenominator.LineSecondFoldX
          ])
    let (denominators1, pending_return) ←
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0
        iter2 denominators
    match pending_return with
    | none => ok (cont (iter1, denominators1))
    | some _ => ok (done (denominators1, pending_return))

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop 5:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 427:8-448:5
    Visibility: public -/
@[rust_loop]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
  (iter : core.slice.iter.Iter circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec field.M31) :
  Result ((alloc.vec.Vec field.M31) × (Option (core.result.Result
    circle_fri.DerivedCircleQueryFoldInverses circle_fri.CircleFriError)))
  := do
  loop
    (fun (iter1, denominators1) =>
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3.body
      iter1 denominators1)
    (iter, denominators)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop body 1:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 426:4-448:5
    Visibility: public -/
@[rust_loop_body]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
  (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
  (inverse : field.M31 → field.M31)
  (line3_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (denominator_count : Std.Usize)
  (iter : core.array.iter.IntoIter (alloc.vec.Vec circle_fri.BaseCirclePoint)
  3#usize) (denominators : alloc.vec.Vec field.M31) :
  Result (ControlFlow ((core.array.iter.IntoIter (alloc.vec.Vec
    circle_fri.BaseCirclePoint) 3#usize) × (alloc.vec.Vec field.M31))
    (core.result.Result circle_fri.DerivedCircleQueryFoldInverses
    circle_fri.CircleFriError))
  := do
  let (o, iter1) ←
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter
  match o with
  | none =>
    let left_val := alloc.vec.Vec.len denominators
    massert (left_val = denominator_count)
    let i := alloc.vec.Vec.len denominators
    let flat_inverses ←
      alloc.vec.from_elem field.M31.Insts.CoreCloneClone field.M31.ZERO i
    let s := alloc.vec.Vec.deref denominators
    let (s1, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut flat_inverses)
    let s2 ← field.m31_batch_inverse_with s s1 inverse
    let flat_inverses1 := deref_mut_back s2
    let b ← alloc.vec.Vec.is_empty Global denominators
    if b
    then
      let i1 := Slice.len layer0
      let circle := alloc.vec.Vec.with_capacity (Array field.M31 2#usize) i1
      let iter2 ←
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          layer0
      let (cursor, circle1) ←
        circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop0
          iter2 flat_inverses1 0#usize circle
      let (later_inverses, c) ←
        core.array.from_fn 3#usize
          circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313
          (later, flat_inverses1, cursor)
      let (_, _, cursor1) := c
      let right_val := alloc.vec.Vec.len flat_inverses1
      massert (cursor1 = right_val)
      let s3 := alloc.vec.Vec.deref line3_points
      let i2 ← core.slice.Slice.iter s3
      let m ←
        core.iter.traits.iterator.Iterator.map.default
          (core.iter.traits.iterator.IteratorSliceIter
          circle_fri.BaseCirclePoint)
          circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31
          i2 ()
      let final_x ←
        core.iter.traits.iterator.Iterator.collect.default
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          (core.iter.traits.iterator.IteratorSliceIter
          circle_fri.BaseCirclePoint)
          circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31)
          (core.iter.traits.collect.FromIteratorVec field.M31) m
      ok (done (core.result.Result.Ok
        { circle := circle1, later := later_inverses, final_x }))
    else
      let b1 ← alloc.vec.Vec.is_empty Global flat_inverses1
      if b1
      then
        let i1 := Slice.len layer0
        let circle := alloc.vec.Vec.with_capacity (Array field.M31 2#usize) i1
        let iter2 ←
          SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
            layer0
        let (cursor, circle1) ←
          circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop1
            iter2 flat_inverses1 0#usize circle
        let (later_inverses, c) ←
          core.array.from_fn 3#usize
            circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313
            (later, flat_inverses1, cursor)
        let (_, _, cursor1) := c
        let right_val := alloc.vec.Vec.len flat_inverses1
        massert (cursor1 = right_val)
        let s3 := alloc.vec.Vec.deref line3_points
        let i2 ← core.slice.Slice.iter s3
        let m ←
          core.iter.traits.iterator.Iterator.map.default
            (core.iter.traits.iterator.IteratorSliceIter
            circle_fri.BaseCirclePoint)
            circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31
            i2 ()
        let final_x ←
          core.iter.traits.iterator.Iterator.collect.default
            (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter
            circle_fri.BaseCirclePoint)
            circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31)
            (core.iter.traits.collect.FromIteratorVec field.M31) m
        ok (done (core.result.Result.Ok
          { circle := circle1, later := later_inverses, final_x }))
      else
        let denominator ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
            denominators 0#usize
        let inverse1 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.M31)
            flat_inverses1 0#usize
        let m ← field.M31.mul denominator inverse1
        let b2 ←
          core.cmp.PartialEq.ne.trait_default
            field.M31.Insts.CoreCmpPartialEqM31 m field.M31.ONE
        if b2
        then
          ok (done (core.result.Result.Err
            circle_fri.CircleFriError.InvalidInverseBackend))
        else
          let i1 := Slice.len layer0
          let circle :=
            alloc.vec.Vec.with_capacity (Array field.M31 2#usize) i1
          let iter2 ←
            SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
              layer0
          let (cursor, circle1) ←
            circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2
              iter2 flat_inverses1 0#usize circle
          let (later_inverses, c) ←
            core.array.from_fn 3#usize
              circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313
              (later, flat_inverses1, cursor)
          let (_, _, cursor1) := c
          let right_val := alloc.vec.Vec.len flat_inverses1
          massert (cursor1 = right_val)
          let s3 := alloc.vec.Vec.deref line3_points
          let i2 ← core.slice.Slice.iter s3
          let m1 ←
            core.iter.traits.iterator.Iterator.map.default
              (core.iter.traits.iterator.IteratorSliceIter
              circle_fri.BaseCirclePoint)
              circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31
              i2 ()
          let final_x ←
            core.iter.traits.iterator.Iterator.collect.default
              (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
              (core.iter.traits.iterator.IteratorSliceIter
              circle_fri.BaseCirclePoint)
              circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31)
              (core.iter.traits.collect.FromIteratorVec field.M31) m1
          ok (done (core.result.Result.Ok
            { circle := circle1, later := later_inverses, final_x }))
  | some points =>
    let iter2 ←
      SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        Global points
    let (denominators1, pending_return) ←
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3 iter2
        denominators
    match pending_return with
    | none => ok (cont (iter1, denominators1))
    | some r => ok (done r)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop 1:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 426:4-448:5
    Visibility: public -/
@[rust_loop]
def circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
  (iter : core.array.iter.IntoIter (alloc.vec.Vec circle_fri.BaseCirclePoint)
  3#usize) (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
  (inverse : field.M31 → field.M31)
  (line3_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (denominator_count : Std.Usize) (denominators : alloc.vec.Vec field.M31) :
  Result (core.result.Result circle_fri.DerivedCircleQueryFoldInverses
    circle_fri.CircleFriError)
  := do
  loop
    (fun (iter1, denominators1) =>
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body layer0
      later inverse line3_points denominator_count iter1 denominators1)
    (iter, denominators)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop body 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 415:4-448:5
    Visibility: public -/
@[rust_loop_body]
def circle_fri.derive_query_fold_inverses_for_circle_loop0.body
  (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
  (inverse : field.M31 → field.M31)
  (line1_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (line2_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (line3_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (denominator_count : Std.Usize)
  (iter : core.slice.iter.Iter circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec field.M31) :
  Result (ControlFlow ((core.slice.iter.Iter circle_fri.BaseCirclePoint) ×
    (alloc.vec.Vec field.M31)) (core.result.Result
    circle_fri.DerivedCircleQueryFoldInverses circle_fri.CircleFriError))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none =>
    let iter2 ←
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
        (Array.make 3#usize [ line1_points, line2_points, line3_points ])
    let r ←
      circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0 iter2 layer0
        later inverse line3_points denominator_count denominators
    ok (done r)
  | some point =>
    let x ← field.M31.double point.x
    let y ← field.M31.double point.y
    let b ← field.M31.is_zero x
    if b
    then
      ok (done (core.result.Result.Err
        (circle_fri.CircleFriError.ZeroDenominator
        circle_fri.FoldDenominator.CircleX)))
    else
      let b1 ← field.M31.is_zero y
      if b1
      then
        ok (done (core.result.Result.Err
          (circle_fri.CircleFriError.ZeroDenominator
          circle_fri.FoldDenominator.CircleY)))
      else
        let s ← lift (Array.to_slice (Array.make 2#usize [ x, y ]))
        let denominators1 ←
          alloc.vec.Vec.extend_from_slice field.M31.Insts.CoreCloneClone
            denominators s
        ok (cont (iter1, denominators1))

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]: loop 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 415:4-448:5
    Visibility: public -/
@[rust_loop]
def circle_fri.derive_query_fold_inverses_for_circle_loop0
  (iter : core.slice.iter.Iter circle_fri.BaseCirclePoint)
  (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
  (inverse : field.M31 → field.M31)
  (line1_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (line2_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (line3_points : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (denominator_count : Std.Usize) (denominators : alloc.vec.Vec field.M31) :
  Result (core.result.Result circle_fri.DerivedCircleQueryFoldInverses
    circle_fri.CircleFriError)
  := do
  loop
    (fun (iter1, denominators1) =>
      circle_fri.derive_query_fold_inverses_for_circle_loop0.body layer0 later
      inverse line1_points line2_points line3_points denominator_count iter1
      denominators1)
    (iter, denominators)

/-- [aspis_core_parent_helper_extraction::circle_fri::derive_query_fold_inverses_for_circle]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 385:0-494:1
    Visibility: public -/
def circle_fri.derive_query_fold_inverses_for_circle
  (domain_log_size : Std.U32) (layer0 : Slice Std.U32)
  (later : Array (Slice Std.U32) 3#usize) (inverse : field.M31 → field.M31) :
  Result (core.result.Result circle_fri.DerivedCircleQueryFoldInverses
    circle_fri.CircleFriError)
  := do
  if domain_log_size < 8#u32
  then
    ok (core.result.Result.Err
      circle_fri.CircleFriError.InvalidBitReverseLength)
  else
    let i ← params.CIRCLE_LOG_ORDER - 1#u32
    if domain_log_size > i
    then
      ok (core.result.Result.Err
        circle_fri.CircleFriError.InvalidBitReverseLength)
    else
      let r ←
        circle_fri.selected_circle_fiber_points_shared domain_log_size layer0
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s := alloc.vec.Vec.deref val
        let s1 ← Array.index_usize later 0#usize
        let r1 ← circle_fri.derive_parent_line_points layer0 s s1 1#u8
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let s2 := alloc.vec.Vec.deref val1
          let s3 ← Array.index_usize later 1#usize
          let r2 ← circle_fri.derive_parent_line_points s1 s2 s3 2#u8
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s4 := alloc.vec.Vec.deref val2
            let s5 ← Array.index_usize later 2#usize
            let r3 ← circle_fri.derive_parent_line_points s3 s4 s5 2#u8
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let i1 := Slice.len layer0
              let o ← lift (Usize.checked_mul i1 2#usize)
              let o1 ←
                core.option.Option.and_then
                  circle_fri.derive_query_fold_inverses_for_circle.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
                  o later
              let r4 ←
                core.option.Option.ok_or o1
                  circle_fri.CircleFriError.QueryOutOfRange
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let denominators := alloc.vec.Vec.with_capacity field.M31 val4
                let iter ←
                  SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
                    Global val
                circle_fri.derive_query_fold_inverses_for_circle_loop0 iter
                  layer0 later inverse val1 val2 val3 val4 denominators
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  circle_fri.DerivedCircleQueryFoldInverses
                  (core.convert.FromSame circle_fri.CircleFriError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                circle_fri.DerivedCircleQueryFoldInverses
                (core.convert.FromSame circle_fri.CircleFriError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              circle_fri.DerivedCircleQueryFoldInverses (core.convert.FromSame
              circle_fri.CircleFriError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            circle_fri.DerivedCircleQueryFoldInverses (core.convert.FromSame
            circle_fri.CircleFriError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          circle_fri.DerivedCircleQueryFoldInverses (core.convert.FromSame
          circle_fri.CircleFriError) residual

end V5CoordinateSelectedProductionSource
