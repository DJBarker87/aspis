-- Deterministic split of recorded Aeneas output.
import Coordinates.FunsLowWindow
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace V5FriCoordinateAdapter

/-- [aspis_core::circle_fri::selected_circle_fiber_points_shared]: loop body 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 248:4-253:5
    Name pattern: [aspis_core::circle_fri::selected_circle_fiber_points_shared]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::selected_circle_fiber_points_shared"]
def aspis_core.circle_fri.selected_circle_fiber_points_shared_loop0.body
  (fibers : Slice Std.U32) (fiber_count : Std.Usize) (valid : Bool)
  (validation_ordinal : Std.Usize) :
  Result (ControlFlow (Bool × Std.Usize) Bool)
  := do
  let i := Slice.len fibers
  if validation_ordinal < i
  then
    let i1 ← Slice.index_usize fibers validation_ordinal
    let i2 ← lift (UScalar.cast .Usize i1)
    let valid1 ← if i2 >= fiber_count
                   then ok false
                   else ok valid
    let validation_ordinal1 ←
      lift (Std.Usize.wrapping_add validation_ordinal 1#usize)
    ok (cont (valid1, validation_ordinal1))
  else ok (done valid)

/-- [aspis_core::circle_fri::selected_circle_fiber_points_shared]: loop 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 248:4-253:5
    Name pattern: [aspis_core::circle_fri::selected_circle_fiber_points_shared]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::selected_circle_fiber_points_shared"]
def aspis_core.circle_fri.selected_circle_fiber_points_shared_loop0
  (fibers : Slice Std.U32) (fiber_count : Std.Usize) (valid : Bool)
  (validation_ordinal : Std.Usize) :
  Result Bool
  := do
  loop
    (fun (valid1, validation_ordinal1) =>
      aspis_core.circle_fri.selected_circle_fiber_points_shared_loop0.body
      fibers fiber_count valid1 validation_ordinal1)
    (valid, validation_ordinal)

/-- [aspis_core::circle_fri::selected_circle_fiber_points_shared]: loop body 1:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 256:4-274:5
    Name pattern: [aspis_core::circle_fri::selected_circle_fiber_points_shared]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::selected_circle_fiber_points_shared"]
def aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1.body
  (fibers : Slice Std.U32)
  (points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (fiber_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint) ×
    Std.Usize) (alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint))
  := do
  let i := Slice.len fibers
  if fiber_ordinal < i
  then
    let fiber ← Slice.index_usize fibers fiber_ordinal
    let i1 ← lift (UScalar.cast .Usize fiber)
    let i2 ← core.num.Usize.reverse_bits i1
    let i3 ← lift (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32)
    let natural ← lift (Std.Usize.wrapping_shr i2 i3)
    let i4 ← lift (natural &&& 255#usize)
    let a ←
      Array.index_usize aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW i4
    let low_x ← Array.index_usize a 0#usize
    let low_y ← Array.index_usize a 1#usize
    let high_index ← lift (Std.Usize.wrapping_shr natural 8#i32)
    let point ←
      if high_index != 0#usize
      then
        do
        let a1 ←
          Array.index_usize aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
            high_index
        let high_x ← Array.index_usize a1 0#usize
        let high_y ← Array.index_usize a1 1#usize
        aspis_core.circle_fri.BaseCirclePoint.add { x := low_x, y := low_y }
          { x := high_x, y := high_y }
      else
        ok ({ x := low_x, y := low_y } : aspis_core.circle_fri.BaseCirclePoint)
    let points1 ← alloc.vec.Vec.push points point
    let fiber_ordinal1 ← lift (Std.Usize.wrapping_add fiber_ordinal 1#usize)
    ok (cont (points1, fiber_ordinal1))
  else ok (done points)

/-- [aspis_core::circle_fri::selected_circle_fiber_points_shared]: loop 1:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 256:4-274:5
    Name pattern: [aspis_core::circle_fri::selected_circle_fiber_points_shared]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::selected_circle_fiber_points_shared"]
def aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1
  (fibers : Slice Std.U32)
  (points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (fiber_ordinal : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  := do
  loop
    (fun (points1, fiber_ordinal1) =>
      aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1.body
      fibers points1 fiber_ordinal1)
    (points, fiber_ordinal)

/-- [aspis_core::circle_fri::selected_circle_fiber_points_shared]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 241:0-244:33
    Name pattern: [aspis_core::circle_fri::selected_circle_fiber_points_shared]
    Visibility: public -/
@[rust_fun "aspis_core::circle_fri::selected_circle_fiber_points_shared"]
def aspis_core.circle_fri.selected_circle_fiber_points_shared
  (domain_log_size : Std.U32) (fibers : Slice Std.U32) :
  Result ((alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint) × Bool)
  := do
  let fiber_count ← lift (Std.Usize.wrapping_shl 1#usize 17#i32)
  let valid ←
    aspis_core.circle_fri.selected_circle_fiber_points_shared_loop0 fibers
      fiber_count (domain_log_size = 19#u32) 0#usize
  let i := Slice.len fibers
  let points :=
    alloc.vec.Vec.with_capacity aspis_core.circle_fri.BaseCirclePoint i
  let points1 ←
    aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1 fibers
      points 0#usize
  ok (points1, valid)

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 123:4-123:30
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::double]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::double"]
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  aspis_core.field.M31.add self self

/-- [aspis_core::circle_fri::double_point]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 279:0-279:58
    Name pattern: [aspis_core::circle_fri::double_point] -/
@[rust_fun "aspis_core::circle_fri::double_point"]
def aspis_core.circle_fri.double_point
  (point : aspis_core.circle_fri.BaseCirclePoint) :
  Result aspis_core.circle_fri.BaseCirclePoint
  := do
  let m ← aspis_core.field.M31.add point.x point.y
  let m1 ← aspis_core.field.M31.sub point.x point.y
  let m2 ← aspis_core.field.M31.mul m m1
  let m3 ← aspis_core.field.M31.mul point.x point.y
  let m4 ← aspis_core.field.M31.double m3
  ok { x := m2, y := m4 }

/-- [aspis_core::field::{aspis_core::field::M31}::neg]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 68:4-68:27
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::neg]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::neg"]
def aspis_core.field.M31.neg
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  if self = 0#u32
  then ok 0#u32
  else let i ← lift (Std.U32.wrapping_sub aspis_core.field.P self)
       ok i

/-- [aspis_core::circle_fri::remove_line_slot_rotation]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 293:0-293:82
    Name pattern: [aspis_core::circle_fri::remove_line_slot_rotation] -/
@[rust_fun "aspis_core::circle_fri::remove_line_slot_rotation"]
def aspis_core.circle_fri.remove_line_slot_rotation
  (point : aspis_core.circle_fri.BaseCirclePoint) (slot : Std.U32) :
  Result aspis_core.circle_fri.BaseCirclePoint
  := do
  match slot with
  | 0#uscalar => ok point
  | 1#uscalar =>
    let m ← aspis_core.field.M31.neg point.x
    let m1 ← aspis_core.field.M31.neg point.y
    ok { x := m, y := m1 }
  | 2#uscalar =>
    let m ← aspis_core.field.M31.neg point.y
    ok { x := m, y := point.x }
  | 3#uscalar =>
    let m ← aspis_core.field.M31.neg point.x
    ok { x := point.y, y := m }
  | _ => fail panic

/-- [aspis_core::circle_fri::derive_parent_line_points]: loop body 1:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 329:8-331:9
    Name pattern: [aspis_core::circle_fri::derive_parent_line_points] -/
@[rust_loop_body, rust_fun "aspis_core::circle_fri::derive_parent_line_points"]
def aspis_core.circle_fri.derive_parent_line_points_loop0_loop0.body
  (child_indices : Slice Std.U32) (parent : Std.U32)
  (child_ordinal : Std.Usize) :
  Result (ControlFlow Std.Usize Std.Usize)
  := do
  let i := Slice.len child_indices
  if child_ordinal < i
  then
    let i1 ← Slice.index_usize child_indices child_ordinal
    let i2 ← lift (Std.U32.wrapping_shr i1 2#i32)
    if i2 < parent
    then
      let child_ordinal1 ←
        lift (Std.Usize.wrapping_add child_ordinal 1#usize)
      ok (cont child_ordinal1)
    else ok (done child_ordinal)
  else ok (done child_ordinal)

/-- [aspis_core::circle_fri::derive_parent_line_points]: loop 1:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 329:8-331:9
    Name pattern: [aspis_core::circle_fri::derive_parent_line_points] -/
@[rust_loop, rust_fun "aspis_core::circle_fri::derive_parent_line_points"]
def aspis_core.circle_fri.derive_parent_line_points_loop0_loop0
  (child_indices : Slice Std.U32) (child_ordinal : Std.Usize)
  (parent : Std.U32) :
  Result Std.Usize
  := do
  loop
    (fun child_ordinal1 =>
      aspis_core.circle_fri.derive_parent_line_points_loop0_loop0.body
      child_indices parent child_ordinal1)
    child_ordinal

/-- [aspis_core::circle_fri::derive_parent_line_points]: loop body 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 327:4-348:5
    Name pattern: [aspis_core::circle_fri::derive_parent_line_points] -/
@[rust_loop_body, rust_fun "aspis_core::circle_fri::derive_parent_line_points"]
def aspis_core.circle_fri.derive_parent_line_points_loop0.body
  (child_indices : Slice Std.U32)
  (child_points : Slice aspis_core.circle_fri.BaseCirclePoint)
  (parent_indices : Slice Std.U32) (doublings : Std.U8)
  (parents : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (child_ordinal : Std.Usize) (parent_ordinal : Std.Usize) (valid : Bool) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint) ×
    Std.Usize × Std.Usize × Bool) ((alloc.vec.Vec
    aspis_core.circle_fri.BaseCirclePoint) × Bool))
  := do
  let i := Slice.len parent_indices
  if parent_ordinal < i
  then
    if valid
    then
      let parent ← Slice.index_usize parent_indices parent_ordinal
      let child_ordinal1 ←
        aspis_core.circle_fri.derive_parent_line_points_loop0_loop0
          child_indices child_ordinal parent
      let i1 := Slice.len child_indices
      if child_ordinal1 >= i1
      then ok (cont (parents, child_ordinal1, parent_ordinal, false))
      else
        let child_index ← Slice.index_usize child_indices child_ordinal1
        let i2 ← lift (Std.U32.wrapping_shr child_index 2#i32)
        if i2 != parent
        then ok (cont (parents, child_ordinal1, parent_ordinal, false))
        else
          let bcp ← Slice.index_usize child_points child_ordinal1
          let point ← aspis_core.circle_fri.double_point bcp
          let point1 ←
            if doublings = 2#u8
            then aspis_core.circle_fri.double_point point
            else ok point
          let i3 ← lift (child_index &&& 3#u32)
          let bcp1 ←
            aspis_core.circle_fri.remove_line_slot_rotation point1 i3
          let parents1 ← alloc.vec.Vec.push parents bcp1
          let parent_ordinal1 ←
            lift (Std.Usize.wrapping_add parent_ordinal 1#usize)
          ok (cont (parents1, child_ordinal1, parent_ordinal1, true))
    else ok (done (parents, false))
  else ok (done (parents, valid))

/-- [aspis_core::circle_fri::derive_parent_line_points]: loop 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 327:4-348:5
    Name pattern: [aspis_core::circle_fri::derive_parent_line_points] -/
@[rust_loop, rust_fun "aspis_core::circle_fri::derive_parent_line_points"]
def aspis_core.circle_fri.derive_parent_line_points_loop0
  (child_indices : Slice Std.U32)
  (child_points : Slice aspis_core.circle_fri.BaseCirclePoint)
  (parent_indices : Slice Std.U32) (doublings : Std.U8)
  (parents : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (child_ordinal : Std.Usize) (parent_ordinal : Std.Usize) (valid : Bool) :
  Result ((alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint) × Bool)
  := do
  loop
    (fun (parents1, child_ordinal1, parent_ordinal1, valid1) =>
      aspis_core.circle_fri.derive_parent_line_points_loop0.body child_indices
      child_points parent_indices doublings parents1 child_ordinal1
      parent_ordinal1 valid1)
    (parents, child_ordinal, parent_ordinal, valid)

/-- [aspis_core::circle_fri::derive_parent_line_points]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 317:0-322:33
    Name pattern: [aspis_core::circle_fri::derive_parent_line_points] -/
@[rust_fun "aspis_core::circle_fri::derive_parent_line_points"]
def aspis_core.circle_fri.derive_parent_line_points
  (child_indices : Slice Std.U32)
  (child_points : Slice aspis_core.circle_fri.BaseCirclePoint)
  (parent_indices : Slice Std.U32) (doublings : Std.U8) :
  Result ((alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint) × Bool)
  := do
  let i := Slice.len parent_indices
  let parents :=
    alloc.vec.Vec.with_capacity aspis_core.circle_fri.BaseCirclePoint i
  let i1 := Slice.len child_indices
  let i2 := Slice.len child_points
  aspis_core.circle_fri.derive_parent_line_points_loop0 child_indices
    child_points parent_indices doublings parents 0#usize 0#usize (i1 = i2)

/-- [aspis_core::field::{aspis_core::field::M31}::is_zero]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 173:4-173:32
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::is_zero]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::is_zero"]
def aspis_core.field.M31.is_zero
  (self : aspis_core.field.M31) : Result Bool := do
  ok (self = 0#u32)

/-- [aspis_core::field::square_n]: loop body 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 45:4-47:5
    Name pattern: [aspis_core::field::square_n] -/
@[rust_loop_body, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n_loop.body
  (iter : core.ops.range.Range Std.Usize) (value : aspis_core.field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.field.M31) aspis_core.field.M31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done value)
  | some _ =>
    let value1 ← aspis_core.field.M31.mul value value
    ok (cont (iter1, value1))

/-- [aspis_core::field::square_n]: loop 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 45:4-47:5
    Name pattern: [aspis_core::field::square_n] -/
@[rust_loop, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n_loop
  (iter : core.ops.range.Range Std.Usize) (value : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  loop
    (fun (iter1, value1) => aspis_core.field.square_n_loop.body iter1 value1)
    (iter, value)

/-- [aspis_core::field::square_n]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 44:0-44:48
    Name pattern: [aspis_core::field::square_n] -/
@[reducible, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n
  (value : aspis_core.field.M31) (count : Std.Usize) :
  Result aspis_core.field.M31
  := do
  aspis_core.field.square_n_loop { start := 0#usize, «end» := count } value

/-- [aspis_core::field::{aspis_core::field::M31}::inv]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 154:4-154:27
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::inv]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::inv"]
def aspis_core.field.M31.inv
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  massert (self != 0#u32)
  let m ← aspis_core.field.M31.mul self self
  let t2 ← aspis_core.field.M31.mul m self
  let m1 ← aspis_core.field.square_n t2 2#usize
  let t4 ← aspis_core.field.M31.mul m1 t2
  let m2 ← aspis_core.field.square_n t4 4#usize
  let t8 ← aspis_core.field.M31.mul m2 t4
  let m3 ← aspis_core.field.square_n t8 8#usize
  let t16 ← aspis_core.field.M31.mul m3 t8
  let m4 ← aspis_core.field.square_n t16 8#usize
  let t24 ← aspis_core.field.M31.mul m4 t8
  let m5 ← aspis_core.field.square_n t24 4#usize
  let t28 ← aspis_core.field.M31.mul m5 t4
  let m6 ← aspis_core.field.M31.mul t28 t28
  let t29 ← aspis_core.field.M31.mul m6 self
  let t30 ← aspis_core.field.M31.mul t29 t29
  let m7 ← aspis_core.field.M31.mul t30 t30
  aspis_core.field.M31.mul m7 self

/-- [aspis_core::field::{aspis_core::field::M31}::ONE]
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 53:4-53:22
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::ONE]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::M31}::ONE"]
def aspis_core.field.M31.ONE : aspis_core.field.M31 := 1#u32

/-- [aspis_core::field::{aspis_core::field::M31}::ZERO]
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 52:4-52:23
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::M31}::ZERO"]
def aspis_core.field.M31.ZERO : aspis_core.field.M31 := 0#u32

/-- [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::M31> for aspis_core::field::M31}::eq]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 19:22-19:31
    Name pattern: [aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq"]
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : aspis_core.field.M31) (other : aspis_core.field.M31) :
  Result Bool
  := do
  ok (self = other)

/-- Trait implementation: [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::M31> for aspis_core::field::M31}]
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 19:22-19:31
    Name pattern: [core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>"]
impl_def aspis_core.field.M31.Insts.CoreCmpPartialEqM31 : core.cmp.PartialEq
  aspis_core.field.M31 aspis_core.field.M31 := {
  eq := aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  ne := core.cmp.PartialEq.ne.trait_default
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31
}

/-- [aspis_core::field::{impl core::clone::Clone for aspis_core::field::M31}::clone]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 19:9-19:14
    Name pattern: [aspis_core::field::{core::clone::Clone<aspis_core::field::M31>}::clone]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::clone::Clone<aspis_core::field::M31>}::clone"]
def aspis_core.field.M31.Insts.CoreCloneClone.clone
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  ok self

/-- Trait implementation: [aspis_core::field::{impl core::clone::Clone for aspis_core::field::M31}]
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/field.rs', lines 19:9-19:14
    Name pattern: [core::clone::Clone<aspis_core::field::M31>] -/
@[reducible, rust_trait_impl "core::clone::Clone<aspis_core::field::M31>"]
def aspis_core.field.M31.Insts.CoreCloneClone : core.clone.Clone
  aspis_core.field.M31 := {
  clone := aspis_core.field.M31.Insts.CoreCloneClone.clone
}

/-- [aspis_core::circle_fri::double_x]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 1073:0-1073:26
    Name pattern: [aspis_core::circle_fri::double_x] -/
@[rust_fun "aspis_core::circle_fri::double_x"]
def aspis_core.circle_fri.double_x
  (x : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let m ← aspis_core.field.M31.mul x x
  let m1 ← aspis_core.field.M31.double m
  aspis_core.field.M31.sub m1 aspis_core.field.M31.ONE

end V5FriCoordinateAdapter
