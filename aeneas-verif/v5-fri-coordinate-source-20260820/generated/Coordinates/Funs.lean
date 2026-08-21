-- Deterministic low-memory split of the recorded Aeneas output.
import Coordinates.FunsPoint
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace V5FriCoordinateAdapter

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 399:4-411:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0.body
  (circle_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (circle_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator) × Std.Usize) ((alloc.vec.Vec
    aspis_core.field.M31) × (Option aspis_core.circle_fri.FoldDenominator)))
  := do
  let i := alloc.vec.Vec.len circle_points
  if circle_ordinal < i
  then
    let point ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) circle_points circle_ordinal
    let x ← aspis_core.field.M31.double point.x
    let y ← aspis_core.field.M31.double point.y
    let b ← aspis_core.field.M31.is_zero x
    let zero_denominator1 ←
      if b
      then ok (some aspis_core.circle_fri.FoldDenominator.CircleX)
      else ok zero_denominator
    let b1 ← aspis_core.field.M31.is_zero y
    let zero_denominator2 ←
      if b1
      then ok (some aspis_core.circle_fri.FoldDenominator.CircleY)
      else ok zero_denominator1
    let s ← lift (Array.to_slice (Array.make 2#usize [ x, y ]))
    let denominators1 ←
      alloc.vec.Vec.extend_from_slice aspis_core.field.M31.Insts.CoreCloneClone
        denominators s
    let circle_ordinal1 ←
      lift (Std.Usize.wrapping_add circle_ordinal 1#usize)
    ok (cont (denominators1, zero_denominator2, circle_ordinal1))
  else ok (done (denominators, zero_denominator))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 0:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 399:4-411:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0
  (circle_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (circle_ordinal : Std.Usize) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator))
  := do
  loop
    (fun (denominators1, zero_denominator1, circle_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0.body
      circle_points denominators1 zero_denominator1 circle_ordinal1)
    (denominators, zero_denominator, circle_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 3:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 437:12-445:13
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def
  aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0.body
  (coordinates : Array aspis_core.field.M31 3#usize)
  (kinds : Array aspis_core.circle_fri.FoldDenominator 3#usize)
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (coordinate_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator) × Std.Usize) ((alloc.vec.Vec
    aspis_core.field.M31) × (Option aspis_core.circle_fri.FoldDenominator)))
  := do
  if coordinate_ordinal < 3#usize
  then
    let coordinate ← Array.index_usize coordinates coordinate_ordinal
    let kind ← Array.index_usize kinds coordinate_ordinal
    let b ← aspis_core.field.M31.is_zero coordinate
    let zero_denominator1 ← if b
                              then ok (some kind)
                              else ok zero_denominator
    let denominators1 ← alloc.vec.Vec.push denominators coordinate
    let coordinate_ordinal1 ←
      lift (Std.Usize.wrapping_add coordinate_ordinal 1#usize)
    ok (cont (denominators1, zero_denominator1, coordinate_ordinal1))
  else ok (done (denominators, zero_denominator))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 3:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 437:12-445:13
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def
  aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (coordinates : Array aspis_core.field.M31 3#usize)
  (kinds : Array aspis_core.circle_fri.FoldDenominator 3#usize)
  (coordinate_ordinal : Std.Usize) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator))
  := do
  loop
    (fun (denominators1, zero_denominator1, coordinate_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0.body
      coordinates kinds denominators1 zero_denominator1 coordinate_ordinal1)
    (denominators, zero_denominator, coordinate_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 2:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 420:8-447:9
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def
  aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0.body
  (points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (point_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator) × Std.Usize) ((alloc.vec.Vec
    aspis_core.field.M31) × (Option aspis_core.circle_fri.FoldDenominator)))
  := do
  let i := alloc.vec.Vec.len points
  if point_ordinal < i
  then
    let point ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) points point_ordinal
    let m ← aspis_core.field.M31.double point.x
    let m1 ← aspis_core.field.M31.double point.y
    let m2 ← aspis_core.circle_fri.double_x point.x
    let m3 ← aspis_core.field.M31.double m2
    let (denominators1, zero_denominator1) ←
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0_loop0
        denominators zero_denominator (Array.make 3#usize [ m, m1, m3 ])
        (Array.make 3#usize [
          aspis_core.circle_fri.FoldDenominator.LineFirstPairX,
          aspis_core.circle_fri.FoldDenominator.LineSecondPairX,
          aspis_core.circle_fri.FoldDenominator.LineSecondFoldX
          ]) 0#usize
    let point_ordinal1 ← lift (Std.Usize.wrapping_add point_ordinal 1#usize)
    ok (cont (denominators1, zero_denominator1, point_ordinal1))
  else ok (done (denominators, zero_denominator))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 2:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 420:8-447:9
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (point_ordinal : Std.Usize) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator))
  := do
  loop
    (fun (denominators1, zero_denominator1, point_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0.body
      points denominators1 zero_denominator1 point_ordinal1)
    (denominators, zero_denominator, point_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 1:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 413:4-449:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1.body
  (line1_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (line2_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (line_layer : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator) × Std.Usize) ((alloc.vec.Vec
    aspis_core.field.M31) × (Option aspis_core.circle_fri.FoldDenominator)))
  := do
  if line_layer < 3#usize
  then
    let points ←
      match line_layer.val with
      | 0 => ok line1_points
      | 1 => ok line2_points
      | _ => ok line3_points
    let (denominators1, zero_denominator1) ←
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1_loop0
        denominators zero_denominator points 0#usize
    let line_layer1 ← lift (Std.Usize.wrapping_add line_layer 1#usize)
    ok (cont (denominators1, zero_denominator1, line_layer1))
  else ok (done (denominators, zero_denominator))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 1:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 413:4-449:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1
  (line1_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (line2_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (zero_denominator : Option aspis_core.circle_fri.FoldDenominator)
  (line_layer : Std.Usize) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × (Option
    aspis_core.circle_fri.FoldDenominator))
  := do
  loop
    (fun (denominators1, zero_denominator1, line_layer1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1.body
      line1_points line2_points line3_points denominators1 zero_denominator1
      line_layer1)
    (denominators, zero_denominator, line_layer)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 4:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop2.body
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    2#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 2#usize))))
  := do
  let i := Slice.len layer0
  if circle_output_ordinal < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array
        aspis_core.field.M31 2#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let circle_output_ordinal1 ←
      lift (Std.Usize.wrapping_add circle_output_ordinal 1#usize)
    ok (cont (cursor1, circle1, circle_output_ordinal1))
  else ok (done (cursor, circle))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 4:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop2
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 2#usize)))
  := do
  loop
    (fun (cursor1, circle1, circle_output_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop2.body
      layer0 flat_inverses cursor1 circle1 circle_output_ordinal1)
    (cursor, circle, circle_output_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 5:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop3.body
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line1
  if ordinal0 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later01 ←
      alloc.vec.Vec.push later0 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal01 ← lift (Std.Usize.wrapping_add ordinal0 1#usize)
    ok (cont (cursor1, later01, ordinal01))
  else ok (done (cursor, later0))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 5:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop3
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later01, ordinal01) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop3.body
      line1 flat_inverses cursor1 later01 ordinal01)
    (cursor, later0, ordinal0)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 6:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop4.body
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line2
  if ordinal1 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later11 ←
      alloc.vec.Vec.push later1 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal11 ← lift (Std.Usize.wrapping_add ordinal1 1#usize)
    ok (cont (cursor1, later11, ordinal11))
  else ok (done (cursor, later1))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 6:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop4
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later11, ordinal11) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop4.body
      line2 flat_inverses cursor1 later11 ordinal11)
    (cursor, later1, ordinal1)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 7:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop5.body
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)))
  := do
  let i := Slice.len line3
  if ordinal2 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later21 ←
      alloc.vec.Vec.push later2 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal21 ← lift (Std.Usize.wrapping_add ordinal2 1#usize)
    ok (cont (cursor1, later21, ordinal21))
  else ok (done later2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 7:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop5
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  := do
  loop
    (fun (cursor1, later21, ordinal21) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop5.body
      line3 flat_inverses cursor1 later21 ordinal21)
    (cursor, later2, ordinal2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 8:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop6.body
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.M31))
  := do
  let i := alloc.vec.Vec.len line3_points
  if final_ordinal < i
  then
    let bcp ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) line3_points final_ordinal
    let m ← aspis_core.circle_fri.double_x bcp.x
    let m1 ← aspis_core.circle_fri.double_x m
    let final_x1 ← alloc.vec.Vec.push final_x m1
    let final_ordinal1 ← lift (Std.Usize.wrapping_add final_ordinal 1#usize)
    ok (cont (final_x1, final_ordinal1))
  else ok (done final_x)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 8:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop6
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (final_x1, final_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop6.body
      line3_points final_x1 final_ordinal1)
    (final_x, final_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 9:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop7.body
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    2#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 2#usize))))
  := do
  let i := Slice.len layer0
  if circle_output_ordinal < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array
        aspis_core.field.M31 2#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let circle_output_ordinal1 ←
      lift (Std.Usize.wrapping_add circle_output_ordinal 1#usize)
    ok (cont (cursor1, circle1, circle_output_ordinal1))
  else ok (done (cursor, circle))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 9:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop7
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 2#usize)))
  := do
  loop
    (fun (cursor1, circle1, circle_output_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop7.body
      layer0 flat_inverses cursor1 circle1 circle_output_ordinal1)
    (cursor, circle, circle_output_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 10:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop8.body
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line1
  if ordinal0 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later01 ←
      alloc.vec.Vec.push later0 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal01 ← lift (Std.Usize.wrapping_add ordinal0 1#usize)
    ok (cont (cursor1, later01, ordinal01))
  else ok (done (cursor, later0))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 10:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop8
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later01, ordinal01) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop8.body
      line1 flat_inverses cursor1 later01 ordinal01)
    (cursor, later0, ordinal0)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 11:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop9.body
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line2
  if ordinal1 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later11 ←
      alloc.vec.Vec.push later1 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal11 ← lift (Std.Usize.wrapping_add ordinal1 1#usize)
    ok (cont (cursor1, later11, ordinal11))
  else ok (done (cursor, later1))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 11:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop9
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later11, ordinal11) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop9.body
      line2 flat_inverses cursor1 later11 ordinal11)
    (cursor, later1, ordinal1)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 12:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop10.body
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)))
  := do
  let i := Slice.len line3
  if ordinal2 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later21 ←
      alloc.vec.Vec.push later2 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal21 ← lift (Std.Usize.wrapping_add ordinal2 1#usize)
    ok (cont (cursor1, later21, ordinal21))
  else ok (done later2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 12:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop10
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  := do
  loop
    (fun (cursor1, later21, ordinal21) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop10.body
      line3 flat_inverses cursor1 later21 ordinal21)
    (cursor, later2, ordinal2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 13:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop11.body
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.M31))
  := do
  let i := alloc.vec.Vec.len line3_points
  if final_ordinal < i
  then
    let bcp ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) line3_points final_ordinal
    let m ← aspis_core.circle_fri.double_x bcp.x
    let m1 ← aspis_core.circle_fri.double_x m
    let final_x1 ← alloc.vec.Vec.push final_x m1
    let final_ordinal1 ← lift (Std.Usize.wrapping_add final_ordinal 1#usize)
    ok (cont (final_x1, final_ordinal1))
  else ok (done final_x)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 13:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop11
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (final_x1, final_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop11.body
      line3_points final_x1 final_ordinal1)
    (final_x, final_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 14:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop12.body
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    2#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 2#usize))))
  := do
  let i := Slice.len layer0
  if circle_output_ordinal < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array
        aspis_core.field.M31 2#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let circle_output_ordinal1 ←
      lift (Std.Usize.wrapping_add circle_output_ordinal 1#usize)
    ok (cont (cursor1, circle1, circle_output_ordinal1))
  else ok (done (cursor, circle))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 14:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop12
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 2#usize)))
  := do
  loop
    (fun (cursor1, circle1, circle_output_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop12.body
      layer0 flat_inverses cursor1 circle1 circle_output_ordinal1)
    (cursor, circle, circle_output_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 15:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop13.body
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line1
  if ordinal0 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later01 ←
      alloc.vec.Vec.push later0 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal01 ← lift (Std.Usize.wrapping_add ordinal0 1#usize)
    ok (cont (cursor1, later01, ordinal01))
  else ok (done (cursor, later0))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 15:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop13
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later01, ordinal01) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop13.body
      line1 flat_inverses cursor1 later01 ordinal01)
    (cursor, later0, ordinal0)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 16:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop14.body
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line2
  if ordinal1 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later11 ←
      alloc.vec.Vec.push later1 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal11 ← lift (Std.Usize.wrapping_add ordinal1 1#usize)
    ok (cont (cursor1, later11, ordinal11))
  else ok (done (cursor, later1))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 16:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop14
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later11, ordinal11) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop14.body
      line2 flat_inverses cursor1 later11 ordinal11)
    (cursor, later1, ordinal1)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 17:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop15.body
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)))
  := do
  let i := Slice.len line3
  if ordinal2 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later21 ←
      alloc.vec.Vec.push later2 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal21 ← lift (Std.Usize.wrapping_add ordinal2 1#usize)
    ok (cont (cursor1, later21, ordinal21))
  else ok (done later2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 17:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop15
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  := do
  loop
    (fun (cursor1, later21, ordinal21) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop15.body
      line3 flat_inverses cursor1 later21 ordinal21)
    (cursor, later2, ordinal2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 18:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop16.body
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.M31))
  := do
  let i := alloc.vec.Vec.len line3_points
  if final_ordinal < i
  then
    let bcp ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) line3_points final_ordinal
    let m ← aspis_core.circle_fri.double_x bcp.x
    let m1 ← aspis_core.circle_fri.double_x m
    let final_x1 ← alloc.vec.Vec.push final_x m1
    let final_ordinal1 ← lift (Std.Usize.wrapping_add final_ordinal 1#usize)
    ok (cont (final_x1, final_ordinal1))
  else ok (done final_x)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 18:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop16
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (final_x1, final_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop16.body
      line3_points final_x1 final_ordinal1)
    (final_x, final_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 19:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 459:8-463:9
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop17.body
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (accumulator : aspis_core.field.M31) (index : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) ×
    aspis_core.field.M31 × Std.Usize) ((alloc.vec.Vec aspis_core.field.M31) ×
    aspis_core.field.M31))
  := do
  let i := alloc.vec.Vec.len denominators
  if index < i
  then
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses index
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) denominators index
    let accumulator1 ← aspis_core.field.M31.mul accumulator m
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    let flat_inverses1 := index_mut_back accumulator
    ok (cont (flat_inverses1, accumulator1, index1))
  else ok (done (flat_inverses, accumulator))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 19:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 459:8-463:9
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop17
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (accumulator : aspis_core.field.M31) (index : Std.Usize) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × aspis_core.field.M31)
  := do
  loop
    (fun (flat_inverses1, accumulator1, index1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop17.body
      denominators flat_inverses1 accumulator1 index1)
    (flat_inverses, accumulator, index)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 20:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 466:8-471:9
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop18.body
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (accumulator_inverse : aspis_core.field.M31) (suffix : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) ×
    aspis_core.field.M31 × Std.Usize) (alloc.vec.Vec aspis_core.field.M31))
  := do
  if suffix > 0#usize
  then
    let suffix1 ← lift (Std.Usize.wrapping_sub suffix 1#usize)
    let prefix1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses suffix1
    let m ← aspis_core.field.M31.mul prefix1 accumulator_inverse
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses suffix1
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) denominators suffix1
    let accumulator_inverse1 ←
      aspis_core.field.M31.mul accumulator_inverse m1
    let flat_inverses1 := index_mut_back m
    ok (cont (flat_inverses1, accumulator_inverse1, suffix1))
  else ok (done flat_inverses)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 20:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 466:8-471:9
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop18
  (denominators : alloc.vec.Vec aspis_core.field.M31)
  (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (accumulator_inverse : aspis_core.field.M31) (suffix : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (flat_inverses1, accumulator_inverse1, suffix1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop18.body
      denominators flat_inverses1 accumulator_inverse1 suffix1)
    (flat_inverses, accumulator_inverse, suffix)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 21:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop19.body
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    2#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 2#usize))))
  := do
  let i := Slice.len layer0
  if circle_output_ordinal < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array
        aspis_core.field.M31 2#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let circle_output_ordinal1 ←
      lift (Std.Usize.wrapping_add circle_output_ordinal 1#usize)
    ok (cont (cursor1, circle1, circle_output_ordinal1))
  else ok (done (cursor, circle))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 21:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop19
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 2#usize)))
  := do
  loop
    (fun (cursor1, circle1, circle_output_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop19.body
      layer0 flat_inverses cursor1 circle1 circle_output_ordinal1)
    (cursor, circle, circle_output_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 22:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop20.body
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line1
  if ordinal0 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later01 ←
      alloc.vec.Vec.push later0 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal01 ← lift (Std.Usize.wrapping_add ordinal0 1#usize)
    ok (cont (cursor1, later01, ordinal01))
  else ok (done (cursor, later0))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 22:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop20
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later01, ordinal01) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop20.body
      line1 flat_inverses cursor1 later01 ordinal01)
    (cursor, later0, ordinal0)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 23:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop21.body
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line2
  if ordinal1 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later11 ←
      alloc.vec.Vec.push later1 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal11 ← lift (Std.Usize.wrapping_add ordinal1 1#usize)
    ok (cont (cursor1, later11, ordinal11))
  else ok (done (cursor, later1))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 23:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop21
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later11, ordinal11) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop21.body
      line2 flat_inverses cursor1 later11 ordinal11)
    (cursor, later1, ordinal1)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 24:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop22.body
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)))
  := do
  let i := Slice.len line3
  if ordinal2 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later21 ←
      alloc.vec.Vec.push later2 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal21 ← lift (Std.Usize.wrapping_add ordinal2 1#usize)
    ok (cont (cursor1, later21, ordinal21))
  else ok (done later2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 24:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop22
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  := do
  loop
    (fun (cursor1, later21, ordinal21) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop22.body
      line3 flat_inverses cursor1 later21 ordinal21)
    (cursor, later2, ordinal2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 25:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop23.body
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.M31))
  := do
  let i := alloc.vec.Vec.len line3_points
  if final_ordinal < i
  then
    let bcp ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) line3_points final_ordinal
    let m ← aspis_core.circle_fri.double_x bcp.x
    let m1 ← aspis_core.circle_fri.double_x m
    let final_x1 ← alloc.vec.Vec.push final_x m1
    let final_ordinal1 ← lift (Std.Usize.wrapping_add final_ordinal 1#usize)
    ok (cont (final_x1, final_ordinal1))
  else ok (done final_x)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 25:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop23
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (final_x1, final_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop23.body
      line3_points final_x1 final_ordinal1)
    (final_x, final_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 26:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop24.body
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    2#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 2#usize))))
  := do
  let i := Slice.len layer0
  if circle_output_ordinal < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array
        aspis_core.field.M31 2#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let circle_output_ordinal1 ←
      lift (Std.Usize.wrapping_add circle_output_ordinal 1#usize)
    ok (cont (cursor1, circle1, circle_output_ordinal1))
  else ok (done (cursor, circle))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 26:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop24
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 2#usize)))
  := do
  loop
    (fun (cursor1, circle1, circle_output_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop24.body
      layer0 flat_inverses cursor1 circle1 circle_output_ordinal1)
    (cursor, circle, circle_output_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 27:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop25.body
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line1
  if ordinal0 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later01 ←
      alloc.vec.Vec.push later0 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal01 ← lift (Std.Usize.wrapping_add ordinal0 1#usize)
    ok (cont (cursor1, later01, ordinal01))
  else ok (done (cursor, later0))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 27:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop25
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later01, ordinal01) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop25.body
      line1 flat_inverses cursor1 later01 ordinal01)
    (cursor, later0, ordinal0)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 28:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop26.body
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line2
  if ordinal1 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later11 ←
      alloc.vec.Vec.push later1 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal11 ← lift (Std.Usize.wrapping_add ordinal1 1#usize)
    ok (cont (cursor1, later11, ordinal11))
  else ok (done (cursor, later1))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 28:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop26
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later11, ordinal11) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop26.body
      line2 flat_inverses cursor1 later11 ordinal11)
    (cursor, later1, ordinal1)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 29:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop27.body
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)))
  := do
  let i := Slice.len line3
  if ordinal2 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later21 ←
      alloc.vec.Vec.push later2 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal21 ← lift (Std.Usize.wrapping_add ordinal2 1#usize)
    ok (cont (cursor1, later21, ordinal21))
  else ok (done later2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 29:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop27
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  := do
  loop
    (fun (cursor1, later21, ordinal21) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop27.body
      line3 flat_inverses cursor1 later21 ordinal21)
    (cursor, later2, ordinal2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 30:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop28.body
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.M31))
  := do
  let i := alloc.vec.Vec.len line3_points
  if final_ordinal < i
  then
    let bcp ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) line3_points final_ordinal
    let m ← aspis_core.circle_fri.double_x bcp.x
    let m1 ← aspis_core.circle_fri.double_x m
    let final_x1 ← alloc.vec.Vec.push final_x m1
    let final_ordinal1 ← lift (Std.Usize.wrapping_add final_ordinal 1#usize)
    ok (cont (final_x1, final_ordinal1))
  else ok (done final_x)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 30:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop28
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (final_x1, final_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop28.body
      line3_points final_x1 final_ordinal1)
    (final_x, final_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 31:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29.body
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    2#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 2#usize))))
  := do
  let i := Slice.len layer0
  if circle_output_ordinal < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let circle1 ←
      alloc.vec.Vec.push circle (Array.make 2#usize [ m, m1 ] : Array
        aspis_core.field.M31 2#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let circle_output_ordinal1 ←
      lift (Std.Usize.wrapping_add circle_output_ordinal 1#usize)
    ok (cont (cursor1, circle1, circle_output_ordinal1))
  else ok (done (cursor, circle))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 31:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 484:4-488:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29
  (layer0 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (circle : alloc.vec.Vec (Array aspis_core.field.M31 2#usize))
  (circle_output_ordinal : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 2#usize)))
  := do
  loop
    (fun (cursor1, circle1, circle_output_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29.body
      layer0 flat_inverses cursor1 circle1 circle_output_ordinal1)
    (cursor, circle, circle_output_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 32:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30.body
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line1
  if ordinal0 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later01 ←
      alloc.vec.Vec.push later0 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal01 ← lift (Std.Usize.wrapping_add ordinal0 1#usize)
    ok (cont (cursor1, later01, ordinal01))
  else ok (done (cursor, later0))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 32:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 491:4-499:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30
  (line1 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later0 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal0 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later01, ordinal01) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30.body
      line1 flat_inverses cursor1 later01 ordinal01)
    (cursor, later0, ordinal0)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 33:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31.body
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (Std.Usize × (alloc.vec.Vec (Array
    aspis_core.field.M31 3#usize))))
  := do
  let i := Slice.len line2
  if ordinal1 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later11 ←
      alloc.vec.Vec.push later1 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal11 ← lift (Std.Usize.wrapping_add ordinal1 1#usize)
    ok (cont (cursor1, later11, ordinal11))
  else ok (done (cursor, later1))

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 33:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 502:4-510:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31
  (line2 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later1 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal1 : Std.Usize) :
  Result (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31 3#usize)))
  := do
  loop
    (fun (cursor1, later11, ordinal11) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31.body
      line2 flat_inverses cursor1 later11 ordinal11)
    (cursor, later1, ordinal1)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 34:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32.body
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (ControlFlow (Std.Usize × (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)) × Std.Usize) (alloc.vec.Vec (Array aspis_core.field.M31
    3#usize)))
  := do
  let i := Slice.len line3
  if ordinal2 < i
  then
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses cursor
    let i1 ← lift (Std.Usize.wrapping_add cursor 1#usize)
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i1
    let i2 ← lift (Std.Usize.wrapping_add cursor 2#usize)
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverses i2
    let later21 ←
      alloc.vec.Vec.push later2 (Array.make 3#usize [ m, m1, m2 ] : Array
        aspis_core.field.M31 3#usize)
    let cursor1 ← lift (Std.Usize.wrapping_add cursor 3#usize)
    let ordinal21 ← lift (Std.Usize.wrapping_add ordinal2 1#usize)
    ok (cont (cursor1, later21, ordinal21))
  else ok (done later2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 34:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 513:4-521:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32
  (line3 : Slice Std.U32) (flat_inverses : alloc.vec.Vec aspis_core.field.M31)
  (cursor : Std.Usize)
  (later2 : alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  (ordinal2 : Std.Usize) :
  Result (alloc.vec.Vec (Array aspis_core.field.M31 3#usize))
  := do
  loop
    (fun (cursor1, later21, ordinal21) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32.body
      line3 flat_inverses cursor1 later21 ordinal21)
    (cursor, later2, ordinal2)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop body 35:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33.body
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.M31))
  := do
  let i := alloc.vec.Vec.len line3_points
  if final_ordinal < i
  then
    let bcp ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.circle_fri.BaseCirclePoint) line3_points final_ordinal
    let m ← aspis_core.circle_fri.double_x bcp.x
    let m1 ← aspis_core.circle_fri.double_x m
    let final_x1 ← alloc.vec.Vec.push final_x m1
    let final_ordinal1 ← lift (Std.Usize.wrapping_add final_ordinal 1#usize)
    ok (cont (final_x1, final_ordinal1))
  else ok (done final_x)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]: loop 35:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 527:4-530:5
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33
  (line3_points : alloc.vec.Vec aspis_core.circle_fri.BaseCirclePoint)
  (final_x : alloc.vec.Vec aspis_core.field.M31) (final_ordinal : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (final_x1, final_ordinal1) =>
      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33.body
      line3_points final_x1 final_ordinal1)
    (final_x, final_ordinal)

/-- [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]:
    Source: '/private/tmp/aspis-fri-coordinate-adapter/crates/aspis-core/src/circle_fri.rs', lines 360:0-366:59
    Name pattern: [aspis_core::circle_fri::derive_query_fold_inverses_for_circle]
    Visibility: public -/
@[rust_fun "aspis_core::circle_fri::derive_query_fold_inverses_for_circle"]
def aspis_core.circle_fri.derive_query_fold_inverses_for_circle
  (domain_log_size : Std.U32) (layer0 : Slice Std.U32) (line1 : Slice Std.U32)
  (line2 : Slice Std.U32) (line3 : Slice Std.U32) :
  Result (core.result.Result
    aspis_core.circle_fri.DerivedCircleQueryFoldInverses
    aspis_core.circle_fri.CircleFriError)
  := do
  if domain_log_size < 8#u32
  then
    ok (core.result.Result.Err
      aspis_core.circle_fri.CircleFriError.InvalidBitReverseLength)
  else
    let i ← aspis_core.params.CIRCLE_LOG_ORDER
    let i1 ← lift (Std.U32.wrapping_sub i 1#u32)
    if domain_log_size > i1
    then
      ok (core.result.Result.Err
        aspis_core.circle_fri.CircleFriError.InvalidBitReverseLength)
    else
      let (circle_points, circle_valid) ←
        aspis_core.circle_fri.selected_circle_fiber_points_shared
          domain_log_size layer0
      if circle_valid
      then
        let s := alloc.vec.Vec.deref circle_points
        let (line1_points, line1_valid) ←
          aspis_core.circle_fri.derive_parent_line_points layer0 s line1 1#u8
        if line1_valid
        then
          let s1 := alloc.vec.Vec.deref line1_points
          let (line2_points, line2_valid) ←
            aspis_core.circle_fri.derive_parent_line_points line1 s1 line2 2#u8
          if line2_valid
          then
            let s2 := alloc.vec.Vec.deref line2_points
            let (line3_points, line3_valid) ←
              aspis_core.circle_fri.derive_parent_line_points line2 s2 line3
                2#u8
            if line3_valid
            then
              let i2 := Slice.len layer0
              let i3 ← lift (Std.Usize.wrapping_mul i2 2#usize)
              let i4 := Slice.len line1
              let i5 ← lift (Std.Usize.wrapping_mul i4 3#usize)
              let i6 ← lift (Std.Usize.wrapping_add i3 i5)
              let i7 := Slice.len line2
              let i8 ← lift (Std.Usize.wrapping_mul i7 3#usize)
              let i9 ← lift (Std.Usize.wrapping_add i6 i8)
              let i10 := Slice.len line3
              let i11 ← lift (Std.Usize.wrapping_mul i10 3#usize)
              let denominator_count ← lift (Std.Usize.wrapping_add i9 i11)
              let denominators :=
                alloc.vec.Vec.with_capacity aspis_core.field.M31
                  denominator_count
              let (denominators1, zero_denominator) ←
                aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop0
                  circle_points denominators none 0#usize
              let (denominators2, zero_denominator1) ←
                aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop1
                  line1_points line2_points line3_points denominators1
                  zero_denominator 0#usize
              match zero_denominator1 with
              | none =>
                let i12 := alloc.vec.Vec.len denominators2
                let flat_inverses ←
                  alloc.vec.from_elem aspis_core.field.M31.Insts.CoreCloneClone
                    aspis_core.field.M31.ZERO i12
                let b ← alloc.vec.Vec.is_empty Global denominators2
                if b
                then
                  let s3 := alloc.vec.Vec.deref denominators2
                  let o ← core.slice.Slice.first s3
                  let s4 := alloc.vec.Vec.deref flat_inverses
                  let o1 ← core.slice.Slice.first s4
                  match o with
                  | none =>
                    let i13 := Slice.len layer0
                    let circle :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        2#usize) i13
                    let (cursor, circle1) ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop2
                        layer0 flat_inverses 0#usize circle 0#usize
                    let i14 := Slice.len line1
                    let later0 :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        3#usize) i14
                    let (cursor1, later01) ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop3
                        line1 flat_inverses cursor later0 0#usize
                    let i15 := Slice.len line2
                    let later1 :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        3#usize) i15
                    let (cursor2, later11) ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop4
                        line2 flat_inverses cursor1 later1 0#usize
                    let i16 := Slice.len line3
                    let later2 :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        3#usize) i16
                    let later21 ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop5
                        line3 flat_inverses cursor2 later2 0#usize
                    let i17 := alloc.vec.Vec.len line3_points
                    let final_x :=
                      alloc.vec.Vec.with_capacity aspis_core.field.M31 i17
                    let final_x1 ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop6
                        line3_points final_x 0#usize
                    ok (core.result.Result.Ok
                      {
                        circle := circle1,
                        later :=
                          (Array.make 3#usize [ later01, later11, later21 ]),
                        final_x := final_x1
                      })
                  | some denominator =>
                    match o1 with
                    | none =>
                      let i13 := Slice.len layer0
                      let circle :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          2#usize) i13
                      let (cursor, circle1) ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop7
                          layer0 flat_inverses 0#usize circle 0#usize
                      let i14 := Slice.len line1
                      let later0 :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          3#usize) i14
                      let (cursor1, later01) ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop8
                          line1 flat_inverses cursor later0 0#usize
                      let i15 := Slice.len line2
                      let later1 :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          3#usize) i15
                      let (cursor2, later11) ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop9
                          line2 flat_inverses cursor1 later1 0#usize
                      let i16 := Slice.len line3
                      let later2 :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          3#usize) i16
                      let later21 ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop10
                          line3 flat_inverses cursor2 later2 0#usize
                      let i17 := alloc.vec.Vec.len line3_points
                      let final_x :=
                        alloc.vec.Vec.with_capacity aspis_core.field.M31 i17
                      let final_x1 ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop11
                          line3_points final_x 0#usize
                      ok (core.result.Result.Ok
                        {
                          circle := circle1,
                          later :=
                            (Array.make 3#usize [ later01, later11, later21 ]),
                          final_x := final_x1
                        })
                    | some inverse =>
                      let m ← aspis_core.field.M31.mul denominator inverse
                      let b1 ←
                        core.cmp.PartialEq.ne.trait_default
                          aspis_core.field.M31.Insts.CoreCmpPartialEqM31 m
                          aspis_core.field.M31.ONE
                      if b1
                      then
                        ok (core.result.Result.Err
                          aspis_core.circle_fri.CircleFriError.InvalidInverseBackend)
                      else
                        let i13 := Slice.len layer0
                        let circle :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 2#usize) i13
                        let (cursor, circle1) ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop12
                            layer0 flat_inverses 0#usize circle 0#usize
                        let i14 := Slice.len line1
                        let later0 :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 3#usize) i14
                        let (cursor1, later01) ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop13
                            line1 flat_inverses cursor later0 0#usize
                        let i15 := Slice.len line2
                        let later1 :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 3#usize) i15
                        let (cursor2, later11) ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop14
                            line2 flat_inverses cursor1 later1 0#usize
                        let i16 := Slice.len line3
                        let later2 :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 3#usize) i16
                        let later21 ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop15
                            line3 flat_inverses cursor2 later2 0#usize
                        let i17 := alloc.vec.Vec.len line3_points
                        let final_x :=
                          alloc.vec.Vec.with_capacity aspis_core.field.M31 i17
                        let final_x1 ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop16
                            line3_points final_x 0#usize
                        ok (core.result.Result.Ok
                          {
                            circle := circle1,
                            later :=
                              (Array.make 3#usize [
                                later01, later11, later21
                                ]),
                            final_x := final_x1
                          })
                else
                  let (flat_inverses1, accumulator) ←
                    aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop17
                      denominators2 flat_inverses aspis_core.field.M31.ONE
                      0#usize
                  let accumulator_inverse ←
                    aspis_core.field.M31.inv accumulator
                  let suffix := alloc.vec.Vec.len denominators2
                  let flat_inverses2 ←
                    aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop18
                      denominators2 flat_inverses1 accumulator_inverse suffix
                  let s3 := alloc.vec.Vec.deref denominators2
                  let o ← core.slice.Slice.first s3
                  let s4 := alloc.vec.Vec.deref flat_inverses2
                  let o1 ← core.slice.Slice.first s4
                  match o with
                  | none =>
                    let i13 := Slice.len layer0
                    let circle :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        2#usize) i13
                    let (cursor, circle1) ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop19
                        layer0 flat_inverses2 0#usize circle 0#usize
                    let i14 := Slice.len line1
                    let later0 :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        3#usize) i14
                    let (cursor1, later01) ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop20
                        line1 flat_inverses2 cursor later0 0#usize
                    let i15 := Slice.len line2
                    let later1 :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        3#usize) i15
                    let (cursor2, later11) ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop21
                        line2 flat_inverses2 cursor1 later1 0#usize
                    let i16 := Slice.len line3
                    let later2 :=
                      alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                        3#usize) i16
                    let later21 ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop22
                        line3 flat_inverses2 cursor2 later2 0#usize
                    let i17 := alloc.vec.Vec.len line3_points
                    let final_x :=
                      alloc.vec.Vec.with_capacity aspis_core.field.M31 i17
                    let final_x1 ←
                      aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop23
                        line3_points final_x 0#usize
                    ok (core.result.Result.Ok
                      {
                        circle := circle1,
                        later :=
                          (Array.make 3#usize [ later01, later11, later21 ]),
                        final_x := final_x1
                      })
                  | some denominator =>
                    match o1 with
                    | none =>
                      let i13 := Slice.len layer0
                      let circle :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          2#usize) i13
                      let (cursor, circle1) ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop24
                          layer0 flat_inverses2 0#usize circle 0#usize
                      let i14 := Slice.len line1
                      let later0 :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          3#usize) i14
                      let (cursor1, later01) ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop25
                          line1 flat_inverses2 cursor later0 0#usize
                      let i15 := Slice.len line2
                      let later1 :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          3#usize) i15
                      let (cursor2, later11) ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop26
                          line2 flat_inverses2 cursor1 later1 0#usize
                      let i16 := Slice.len line3
                      let later2 :=
                        alloc.vec.Vec.with_capacity (Array aspis_core.field.M31
                          3#usize) i16
                      let later21 ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop27
                          line3 flat_inverses2 cursor2 later2 0#usize
                      let i17 := alloc.vec.Vec.len line3_points
                      let final_x :=
                        alloc.vec.Vec.with_capacity aspis_core.field.M31 i17
                      let final_x1 ←
                        aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop28
                          line3_points final_x 0#usize
                      ok (core.result.Result.Ok
                        {
                          circle := circle1,
                          later :=
                            (Array.make 3#usize [ later01, later11, later21 ]),
                          final_x := final_x1
                        })
                    | some inverse =>
                      let m ← aspis_core.field.M31.mul denominator inverse
                      let b1 ←
                        core.cmp.PartialEq.ne.trait_default
                          aspis_core.field.M31.Insts.CoreCmpPartialEqM31 m
                          aspis_core.field.M31.ONE
                      if b1
                      then
                        ok (core.result.Result.Err
                          aspis_core.circle_fri.CircleFriError.InvalidInverseBackend)
                      else
                        let i13 := Slice.len layer0
                        let circle :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 2#usize) i13
                        let (cursor, circle1) ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop29
                            layer0 flat_inverses2 0#usize circle 0#usize
                        let i14 := Slice.len line1
                        let later0 :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 3#usize) i14
                        let (cursor1, later01) ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop30
                            line1 flat_inverses2 cursor later0 0#usize
                        let i15 := Slice.len line2
                        let later1 :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 3#usize) i15
                        let (cursor2, later11) ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop31
                            line2 flat_inverses2 cursor1 later1 0#usize
                        let i16 := Slice.len line3
                        let later2 :=
                          alloc.vec.Vec.with_capacity (Array
                            aspis_core.field.M31 3#usize) i16
                        let later21 ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop32
                            line3 flat_inverses2 cursor2 later2 0#usize
                        let i17 := alloc.vec.Vec.len line3_points
                        let final_x :=
                          alloc.vec.Vec.with_capacity aspis_core.field.M31 i17
                        let final_x1 ←
                          aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop33
                            line3_points final_x 0#usize
                        ok (core.result.Result.Ok
                          {
                            circle := circle1,
                            later :=
                              (Array.make 3#usize [
                                later01, later11, later21
                                ]),
                            final_x := final_x1
                          })
              | some kind =>
                ok (core.result.Result.Err
                  (aspis_core.circle_fri.CircleFriError.ZeroDenominator kind))
            else
              ok (core.result.Result.Err
                aspis_core.circle_fri.CircleFriError.QueryOutOfRange)
          else
            ok (core.result.Result.Err
              aspis_core.circle_fri.CircleFriError.QueryOutOfRange)
        else
          ok (core.result.Result.Err
            aspis_core.circle_fri.CircleFriError.QueryOutOfRange)
      else
        ok (core.result.Result.Err
          aspis_core.circle_fri.CircleFriError.CircleFiberOutOfRange)

/-- [v5_fri_coordinate_adapter::derive_released_query_fold_inverses]:
    Source: 'src/lib.rs', lines 6:0-20:1
    Visibility: public -/
def derive_released_query_fold_inverses
  (domain_log_size : Std.U32) (layer0 : Slice Std.U32) (line1 : Slice Std.U32)
  (line2 : Slice Std.U32) (line3 : Slice Std.U32) :
  Result (core.result.Result
    aspis_core.circle_fri.DerivedCircleQueryFoldInverses
    aspis_core.circle_fri.CircleFriError)
  := do
  aspis_core.circle_fri.derive_query_fold_inverses_for_circle domain_log_size
    layer0 line1 line2 line3

end V5FriCoordinateAdapter
