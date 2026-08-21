-- Deterministic low-memory split of the recorded Aeneas output.
import V5CoordinateSelectedProduction.FunsLowWindow
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace V5CoordinateSelectedProductionSource

/-- [aspis_core_parent_helper_extraction::circle_fri::bit_reverse_index]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 723:0-735:1
    Visibility: public -/
def circle_fri.bit_reverse_index
  (index : Std.Usize) (log_size : Std.U32) :
  Result (core.result.Result Std.Usize circle_fri.CircleFriError)
  := do
  let o ← core.num.Usize.checked_shl 1#usize log_size
  let r ←
    core.option.Option.ok_or o
      circle_fri.CircleFriError.InvalidBitReverseLength
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    if index >= val
    then
      ok (core.result.Result.Err
        circle_fri.CircleFriError.BitReverseIndexOutOfRange)
    else
      if log_size = 0#u32
      then ok (core.result.Result.Ok 0#usize)
      else
        let i ← core.num.Usize.reverse_bits index
        let i1 ← core.num.Usize.BITS - log_size
        let i2 ← i >>> i1
        ok (core.result.Result.Ok i2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Std.Usize (core.convert.FromSame circle_fri.CircleFriError) residual

/-- [aspis_core_parent_helper_extraction::circle_fri::half_odds_step_index]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 560:0-562:1 -/
def circle_fri.half_odds_step_index (log_size : Std.U32) : Result Std.U64 := do
  let i ← params.CIRCLE_LOG_ORDER - log_size
  1#u64 <<< i

/-- [aspis_core_parent_helper_extraction::circle_fri::half_odds_initial_index]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 555:0-557:1 -/
def circle_fri.half_odds_initial_index
  (log_size : Std.U32) : Result Std.U64 := do
  let i ← log_size + 2#u32
  let i1 ← params.CIRCLE_LOG_ORDER - i
  1#u64 <<< i1

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop body 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 257:8-279:25
    Visibility: public -/
@[rust_loop_body]
def circle_fri.selected_circle_fiber_points_shared_loop0.body
  (fiber_count : Std.Usize) (iter : core.slice.iter.Iter Std.U32)
  (points : alloc.vec.Vec circle_fri.BaseCirclePoint) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × (alloc.vec.Vec
    circle_fri.BaseCirclePoint)) (core.result.Result (alloc.vec.Vec
    circle_fri.BaseCirclePoint) circle_fri.CircleFriError))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (core.result.Result.Ok points))
  | some fiber =>
    let i ← lift (UScalar.cast .Usize fiber)
    if i >= fiber_count
    then
      ok (done (core.result.Result.Err
        circle_fri.CircleFriError.CircleFiberOutOfRange))
    else
      let i1 ← lift (UScalar.cast .Usize fiber)
      let i2 ← core.num.Usize.reverse_bits i1
      let i3 ← core.num.Usize.BITS - 17#u32
      let natural ← i2 >>> i3
      let i4 ← lift (natural &&& 255#usize)
      let a ← Array.index_usize circle_fri.RATE512_CIRCLE_LOW8_WINDOW i4
      let low_x ← Array.index_usize a 0#usize
      let low_y ← Array.index_usize a 1#usize
      let high_index ← natural >>> 8#i32
      let point ←
        if high_index != 0#usize
        then
          do
          let a1 ←
            Array.index_usize circle_fri.RATE512_CIRCLE_HIGH9_WINDOW high_index
          let high_x ← Array.index_usize a1 0#usize
          let high_y ← Array.index_usize a1 1#usize
          circle_fri.BaseCirclePoint.add { x := low_x, y := low_y }
            { x := high_x, y := high_y }
        else ok ({ x := low_x, y := low_y } : circle_fri.BaseCirclePoint)
      let points1 ← alloc.vec.Vec.push points point
      ok (cont (iter1, points1))

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop 0:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 257:8-279:25
    Visibility: public -/
@[rust_loop]
def circle_fri.selected_circle_fiber_points_shared_loop0
  (iter : core.slice.iter.Iter Std.U32) (fiber_count : Std.Usize)
  (points : alloc.vec.Vec circle_fri.BaseCirclePoint) :
  Result (core.result.Result (alloc.vec.Vec circle_fri.BaseCirclePoint)
    circle_fri.CircleFriError)
  := do
  loop
    (fun (iter1, points1) =>
      circle_fri.selected_circle_fiber_points_shared_loop0.body fiber_count
      iter1 points1)
    (iter, points)

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop body 1:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 285:4-288:5
    Visibility: public -/
@[rust_loop_body]
def circle_fri.selected_circle_fiber_points_shared_loop1.body
  (iter : core.ops.range.Range Std.U32)
  (step_power : circle_fri.BaseCirclePoint)
  (step_powers : alloc.vec.Vec circle_fri.BaseCirclePoint) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) ×
    circle_fri.BaseCirclePoint × (alloc.vec.Vec circle_fri.BaseCirclePoint))
    (alloc.vec.Vec circle_fri.BaseCirclePoint))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done step_powers)
  | some _ =>
    let step_powers1 ← alloc.vec.Vec.push step_powers step_power
    let step_power1 ← circle_fri.BaseCirclePoint.add step_power step_power
    ok (cont (iter1, step_power1, step_powers1))

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop 1:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 285:4-288:5
    Visibility: public -/
@[rust_loop]
def circle_fri.selected_circle_fiber_points_shared_loop1
  (iter : core.ops.range.Range Std.U32)
  (step_power : circle_fri.BaseCirclePoint)
  (step_powers : alloc.vec.Vec circle_fri.BaseCirclePoint) :
  Result (alloc.vec.Vec circle_fri.BaseCirclePoint)
  := do
  loop
    (fun (iter1, step_power1, step_powers1) =>
      circle_fri.selected_circle_fiber_points_shared_loop1.body iter1
      step_power1 step_powers1)
    (iter, step_power, step_powers)

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop body 3:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 297:8-301:9
    Visibility: public -/
@[rust_loop_body]
def circle_fri.selected_circle_fiber_points_shared_loop2_loop0.body
  (natural : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  circle_fri.BaseCirclePoint)) (point : circle_fri.BaseCirclePoint) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter circle_fri.BaseCirclePoint)) ×
    circle_fri.BaseCirclePoint) circle_fri.BaseCirclePoint)
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter circle_fri.BaseCirclePoint)
      iter
  match o with
  | none => ok (done point)
  | some p =>
    let (bit, power) := p
    let i ← 1#usize <<< bit
    let i1 ← lift (natural &&& i)
    if i1 != 0#usize
    then
      let point1 ← circle_fri.BaseCirclePoint.add point power
      ok (cont (iter1, point1))
    else ok (cont (iter1, point))

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop 3:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 297:8-301:9
    Visibility: public -/
@[rust_loop]
def circle_fri.selected_circle_fiber_points_shared_loop2_loop0
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  circle_fri.BaseCirclePoint)) (natural : Std.Usize)
  (point : circle_fri.BaseCirclePoint) :
  Result circle_fri.BaseCirclePoint
  := do
  loop
    (fun (iter1, point1) =>
      circle_fri.selected_circle_fiber_points_shared_loop2_loop0.body natural
      iter1 point1)
    (iter, point)

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop body 2:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 291:4-305:1
    Visibility: public -/
@[rust_loop_body]
def circle_fri.selected_circle_fiber_points_shared_loop2.body
  (query_log_size : Std.U32) (fiber_count : Std.Usize)
  (initial : circle_fri.BaseCirclePoint)
  (step_powers : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (iter : core.slice.iter.Iter Std.U32)
  (points : alloc.vec.Vec circle_fri.BaseCirclePoint) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × (alloc.vec.Vec
    circle_fri.BaseCirclePoint)) (core.result.Result (alloc.vec.Vec
    circle_fri.BaseCirclePoint) circle_fri.CircleFriError))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (core.result.Result.Ok points))
  | some fiber =>
    let i ← lift (UScalar.cast .Usize fiber)
    if i >= fiber_count
    then
      ok (done (core.result.Result.Err
        circle_fri.CircleFriError.CircleFiberOutOfRange))
    else
      let i1 ← lift (UScalar.cast .Usize fiber)
      let r ← circle_fri.bit_reverse_index i1 query_log_size
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s := alloc.vec.Vec.deref step_powers
        let i2 ← core.slice.Slice.iter s
        let iter2 ←
          core.iter.traits.iterator.Iterator.enumerate.trait_default
            (core.iter.traits.iterator.IteratorSliceIter
            circle_fri.BaseCirclePoint) i2
        let point ←
          circle_fri.selected_circle_fiber_points_shared_loop2_loop0 iter2 val
            initial
        let points1 ← alloc.vec.Vec.push points point
        ok (cont (iter1, points1))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec circle_fri.BaseCirclePoint) (core.convert.FromSame
            circle_fri.CircleFriError) residual
        ok (done r1)

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]: loop 2:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 291:4-305:1
    Visibility: public -/
@[rust_loop]
def circle_fri.selected_circle_fiber_points_shared_loop2
  (iter : core.slice.iter.Iter Std.U32) (query_log_size : Std.U32)
  (fiber_count : Std.Usize) (initial : circle_fri.BaseCirclePoint)
  (step_powers : alloc.vec.Vec circle_fri.BaseCirclePoint)
  (points : alloc.vec.Vec circle_fri.BaseCirclePoint) :
  Result (core.result.Result (alloc.vec.Vec circle_fri.BaseCirclePoint)
    circle_fri.CircleFriError)
  := do
  loop
    (fun (iter1, points1) =>
      circle_fri.selected_circle_fiber_points_shared_loop2.body query_log_size
      fiber_count initial step_powers iter1 points1)
    (iter, points)

/-- [aspis_core_parent_helper_extraction::circle_fri::selected_circle_fiber_points_shared]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 241:0-305:1
    Visibility: public -/
def circle_fri.selected_circle_fiber_points_shared
  (domain_log_size : Std.U32) (fibers : Slice Std.U32) :
  Result (core.result.Result (alloc.vec.Vec circle_fri.BaseCirclePoint)
    circle_fri.CircleFriError)
  := do
  let o ← lift (U32.checked_sub domain_log_size 2#u32)
  let r ←
    core.option.Option.ok_or o
      circle_fri.CircleFriError.InvalidBitReverseLength
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    if domain_log_size = 0#u32
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
        let o1 ← core.num.Usize.checked_shl 1#usize val
        let r1 ←
          core.option.Option.ok_or o1
            circle_fri.CircleFriError.InvalidBitReverseLength
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          if domain_log_size = 19#u32
          then
            let i1 := Slice.len fibers
            let points :=
              alloc.vec.Vec.with_capacity circle_fri.BaseCirclePoint i1
            let iter ←
              SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
                fibers
            circle_fri.selected_circle_fiber_points_shared_loop0 iter val1
              points
          else
            let i1 ← domain_log_size - 1#u32
            let i2 ← circle_fri.half_odds_initial_index i1
            let initial ← circle_fri.point_from_group_index i2
            let i3 ← circle_fri.half_odds_step_index i1
            let step_power ← circle_fri.point_from_group_index i3
            let i4 ← lift (UScalar.cast .Usize val)
            let step_powers :=
              alloc.vec.Vec.with_capacity circle_fri.BaseCirclePoint i4
            let step_powers1 ←
              circle_fri.selected_circle_fiber_points_shared_loop1
                { start := 0#u32, «end» := val } step_power step_powers
            let i5 := Slice.len fibers
            let points :=
              alloc.vec.Vec.with_capacity circle_fri.BaseCirclePoint i5
            let iter ←
              SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
                fibers
            circle_fri.selected_circle_fiber_points_shared_loop2 iter val val1
              initial step_powers1 points
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec circle_fri.BaseCirclePoint) (core.convert.FromSame
            circle_fri.CircleFriError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec circle_fri.BaseCirclePoint) (core.convert.FromSame
      circle_fri.CircleFriError) residual

end V5CoordinateSelectedProductionSource
