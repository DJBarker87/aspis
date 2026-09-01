import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk06

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::v6_onefold::decode_packed_m31_eight_aligned]: loop body 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 363:4-381:5
    Name pattern: [aspis_core::v6_onefold::decode_packed_m31_eight_aligned] -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_onefold::decode_packed_m31_eight_aligned"]
def aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0.body
  {N : Std.Usize} (i : Std.Usize) (bytes : Slice Std.U8)
  (output : Array Std.U32 N) (invalid : Std.U32) (block : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 N) × Std.U32 × Std.Usize) ((Array
    Std.U32 N) × Std.U32))
  := do
  if block < i
  then
    let byte ← block * 31#usize
    let i1 ← byte + 31#usize
    let chunk ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) bytes { start := byte, «end» := i1 }
    let base ← block * 8#usize
    let i2 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call (N := N)
        chunk 0#usize
    let i3 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i4 ← lift (i2 &&& i3)
    let i5 ← lift (UScalar.cast .U32 i4)
    let output1 ← Array.update output base i5
    let i6 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call (N := N)
        chunk 3#usize
    let i7 ← i6 >>> 7#i32
    let i8 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i9 ← lift (i7 &&& i8)
    let i10 ← base + 1#usize
    let i11 ← lift (UScalar.cast .U32 i9)
    let output2 ← Array.update output1 i10 i11
    let i12 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call (N := N)
        chunk 7#usize
    let i13 ← i12 >>> 6#i32
    let i14 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i15 ← lift (i13 &&& i14)
    let i16 ← base + 2#usize
    let i17 ← lift (UScalar.cast .U32 i15)
    let output3 ← Array.update output2 i16 i17
    let i18 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call (N := N)
        chunk 11#usize
    let i19 ← i18 >>> 5#i32
    let i20 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i21 ← lift (i19 &&& i20)
    let i22 ← base + 3#usize
    let i23 ← lift (UScalar.cast .U32 i21)
    let output4 ← Array.update output3 i22 i23
    let i24 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call (N := N)
        chunk 15#usize
    let i25 ← i24 >>> 4#i32
    let i26 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i27 ← lift (i25 &&& i26)
    let i28 ← base + 4#usize
    let i29 ← lift (UScalar.cast .U32 i27)
    let output5 ← Array.update output4 i28 i29
    let i30 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call (N := N)
        chunk 19#usize
    let i31 ← i30 >>> 3#i32
    let i32 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i33 ← lift (i31 &&& i32)
    let i34 ← base + 5#usize
    let i35 ← lift (UScalar.cast .U32 i33)
    let output6 ← Array.update output5 i34 i35
    let i36 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call (N := N)
        chunk 23#usize
    let i37 ← i36 >>> 2#i32
    let i38 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i39 ← lift (i37 &&& i38)
    let i40 ← base + 6#usize
    let i41 ← lift (UScalar.cast .U32 i39)
    let output7 ← Array.update output6 i40 i41
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) chunk { start := 27#usize, «end» := 31#usize }
    let r ←
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
    let a ←
      match r with
      | core.result.Result.Ok value => ok value
      | core.result.Result.Err _ => fail .panic
    let i42 ← lift (core.num.U32.from_le_bytes a)
    let i43 ← i42 >>> 1#i32
    let i44 ← base + 7#usize
    let i45 ← lift (i43 &&& aspis_core.field.P)
    let output8 ← Array.update output7 i44 i45
    let i46 ← base + 8#usize
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U32)) output8
        { start := base, «end» := i46 }
    let iter ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
        s1
    let invalid1 ←
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0 iter
        invalid
    let block1 ← block + 1#usize
    ok (cont (output8, invalid1, block1))
  else ok (done (output, invalid))

/-- [aspis_core::v6_onefold::decode_packed_m31_eight_aligned]: loop 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 363:4-381:5
    Name pattern: [aspis_core::v6_onefold::decode_packed_m31_eight_aligned] -/
@[rust_loop, rust_fun
  "aspis_core::v6_onefold::decode_packed_m31_eight_aligned"]
def aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0
  {N : Std.Usize} (i : Std.Usize) (bytes : Slice Std.U8)
  (output : Array Std.U32 N) (invalid : Std.U32) (block : Std.Usize) :
  Result ((Array Std.U32 N) × Std.U32)
  := do
  loop
    (fun (output1, invalid1, block1) =>
      aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0.body i bytes
      output1 invalid1 block1)
    (output, invalid, block)

/-- [aspis_core::v6_onefold::decode_packed_m31_eight_aligned]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 356:0-356:97
    Name pattern: [aspis_core::v6_onefold::decode_packed_m31_eight_aligned] -/
@[rust_fun "aspis_core::v6_onefold::decode_packed_m31_eight_aligned"]
def aspis_core.v6_onefold.decode_packed_m31_eight_aligned
  (N : Std.Usize) (bytes : Slice Std.U8) :
  Result (core.result.Result (Array Std.U32 N)
    aspis_core.v6_onefold.V6WireError)
  := do
  if N = 0#usize
  then
    ok (core.result.Result.Err aspis_core.v6_onefold.V6WireError.WrongLength)
  else
    let i ← N % 8#usize
    if i != 0#usize
    then
      ok (core.result.Result.Err aspis_core.v6_onefold.V6WireError.WrongLength)
    else
      let i1 := Slice.len bytes
      let i2 ← N / 8#usize
      let i3 ← i2 * 31#usize
      if i1 != i3
      then
        ok (core.result.Result.Err
          aspis_core.v6_onefold.V6WireError.WrongLength)
      else
        let output := Array.repeat N 0#u32
        let (output1, invalid) ←
          aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0 i2 bytes
            output 0#u32 0#usize
        if invalid = 0#u32
        then ok (core.result.Result.Ok output1)
        else
          ok (core.result.Result.Err
            aspis_core.v6_onefold.V6WireError.NonCanonicalM31)

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop body 2:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 465:8-466:47
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0_loop0.body
  (iter : core.slice.iter.Windows Std.U32) (expanded : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.Windows Std.U32) × Std.Usize)
    Std.Usize)
  := do
  let (o, iter1) ←
    core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done expanded)
  | some pair =>
    let i ← Slice.index_usize pair 0#usize
    let i1 ← Slice.index_usize pair 1#usize
    let differing_bits ← lift (i ^^^ i1)
    massert (differing_bits != 0#u32)
    let i2 ← core.num.U32.BITS - 1#u32
    let i3 ← lift (core.num.U32.leading_zeros differing_bits)
    let i4 ← i2 - i3
    let i5 ← lift (UScalar.cast .Usize i4)
    let expanded1 ← expanded + i5
    ok (cont (iter1, expanded1))

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop 2:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 465:8-466:47
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0_loop0
  (iter : core.slice.iter.Windows Std.U32) (expanded : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, expanded1) =>
      aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0_loop0.body iter1
      expanded1)
    (iter, expanded)

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop body 1:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 458:4-473:1
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0.body
  {Q : Std.Usize} (queries : Array Std.U32 Q) (depth : Std.U8)
  (iter : core.ops.range.Range Std.Usize) :
  Result (ControlFlow (core.ops.range.Range Std.Usize) (core.result.Result
    Std.Usize aspis_core.v6_onefold.V6WireError))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let i ← lift (core.convert.num.FromUsizeU8.from depth)
    let expanded ← i + 1#usize
    let s ← lift (Array.to_slice queries)
    let iter2 ← core.slice.Slice.windows s 2#usize
    let expanded1 ←
      aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0_loop0 iter2
        expanded
    let o1 ← lift (Usize.checked_sub expanded1 Q)
    let return_capture ←
      core.option.Option.ok_or o1
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule
    ok (done return_capture)
  | some index =>
    let i ← index - 1#usize
    let i1 ← Array.index_usize queries i
    let i2 ← Array.index_usize queries index
    if i1 = i2
    then
      ok (done (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule))
    else ok (cont iter1)

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop 1:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 458:4-473:1
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0
  {Q : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (queries : Array Std.U32 Q) (depth : Std.U8) :
  Result (core.result.Result Std.Usize aspis_core.v6_onefold.V6WireError)
  := do
  loop
    (fun iter1 => aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0.body
      queries depth iter1)
    iter

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop body 3:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 449:8-452:9
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop1.body
  {Q : Std.Usize} (value : Std.U32) (queries : Array Std.U32 Q)
  (cursor : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 Q) × Std.Usize) ((Array Std.U32 Q) ×
    Std.Usize))
  := do
  if cursor > 0#usize
  then
    let i ← cursor - 1#usize
    let i1 ← Array.index_usize queries i
    if value < i1
    then
      let i2 ← Array.index_usize queries i
      let a ← Array.update queries cursor i2
      ok (cont (a, i))
    else ok (done (queries, cursor))
  else ok (done (queries, cursor))

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop 3:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 449:8-452:9
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop1
  {Q : Std.Usize} (queries : Array Std.U32 Q) (value : Std.U32)
  (cursor : Std.Usize) :
  Result ((Array Std.U32 Q) × Std.Usize)
  := do
  loop
    (fun (queries1, cursor1) =>
      aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop1.body value
      queries1 cursor1)
    (queries, cursor)

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop body 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 446:4-473:1
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0.body
  {Q : Std.Usize} (depth : Std.U8) (leaf_count : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (queries : Array Std.U32 Q) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32 Q))
    (core.result.Result Std.Usize aspis_core.v6_onefold.V6WireError))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let i ← Q - 1#usize
    let i1 ← Array.index_usize queries i
    if i1 >= leaf_count
    then
      ok (done (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule))
    else
      let r ←
        aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop0
          { start := 1#usize, «end» := Q } queries depth
      ok (done r)
  | some index =>
    let value ← Array.index_usize queries index
    let (queries1, cursor) ←
      aspis_core.v6_onefold.binary_frontier_nodes_loop0_loop1 queries value
        index
    let a ← Array.update queries1 cursor value
    ok (cont (iter1, a))

/-- [aspis_core::v6_onefold::binary_frontier_nodes]: loop 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 446:4-473:1
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes_loop0
  {Q : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (queries : Array Std.U32 Q) (depth : Std.U8) (leaf_count : Std.U32) :
  Result (core.result.Result Std.Usize aspis_core.v6_onefold.V6WireError)
  := do
  loop
    (fun (iter1, queries1) =>
      aspis_core.v6_onefold.binary_frontier_nodes_loop0.body depth leaf_count
      iter1 queries1)
    (iter, queries)

/-- [aspis_core::v6_onefold::binary_frontier_nodes]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 435:0-438:31
    Name pattern: [aspis_core::v6_onefold::binary_frontier_nodes]
    Visibility: public -/
@[rust_fun "aspis_core::v6_onefold::binary_frontier_nodes"]
def aspis_core.v6_onefold.binary_frontier_nodes
  {Q : Std.Usize} (queries : Array Std.U32 Q) (depth : Std.U8) :
  Result (core.result.Result Std.Usize aspis_core.v6_onefold.V6WireError)
  := do
  if Q = 0#usize
  then
    ok (core.result.Result.Err
      aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule)
  else
    if depth >= 32#u8
    then
      ok (core.result.Result.Err
        aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule)
    else
      let i ← lift (core.convert.num.FromU32U8.from depth)
      let o ← core.num.U32.checked_shl 1#u32 i
      let r ←
        core.option.Option.ok_or o
          aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        aspis_core.v6_onefold.binary_frontier_nodes_loop0
          { start := 1#usize, «end» := Q } queries depth val
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Std.Usize (core.convert.FromSame aspis_core.v6_onefold.V6WireError)
          residual

/-- [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]: loop body 1:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 641:4-644:5
    Name pattern: [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_onefold::gamma_combine_v6_packed_layer0"]
def aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0.body
  (helper_powers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
  (helpers : Array (Array aspis_core.field.QM31 4#usize) 3#usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31)) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)))
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.enumerate.IteratorEnumerateMut.next iter
  match o with
  | none => ok (done (let e := next_back iter1 none
                      back e))
  | some p =>
    let (slot, output) := p
    let a ← Array.index_usize helpers 0#usize
    let q ← Array.index_usize a slot
    let a1 ← Array.index_usize helpers 1#usize
    let q1 ← Array.index_usize a1 slot
    let a2 ← Array.index_usize helpers 2#usize
    let q2 ← Array.index_usize a2 slot
    let q3 ←
      aspis_core.field.qm31_sum_products3_prepared helper_powers
        (Array.make 3#usize [ q, q1, q2 ])
    let output1 ← aspis_core.field.QM31.add output q3
    ok (cont (iter1,
      fun e => let e1 := next_back e (some (slot, output1))
               back e1))

/-- [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]: loop 1:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 641:4-644:5
    Name pattern: [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::gamma_combine_v6_packed_layer0"]
def aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31))
  (helper_powers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
  (helpers : Array (Array aspis_core.field.QM31 4#usize) 3#usize) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1) =>
      aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0.body
      helper_powers helpers iter1 back1)
    (iter, back)

/-- [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]: loop body 2:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 633:8-639:9
    Name pattern: [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_onefold::gamma_combine_v6_packed_layer0"]
def aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop1.body
  (c2 : Array Std.U32 48#usize) (helper : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31)) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)))
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.enumerate.IteratorEnumerateMut.next iter
  match o with
  | none => ok (done (let e := next_back iter1 none
                      back e))
  | some p =>
    let (slot, _) := p
    let i ← helper * 4#usize
    let i1 ← i + slot
    let limb ← 4#usize * i1
    let i2 ← Array.index_usize c2 limb
    let i3 ← limb + 1#usize
    let i4 ← Array.index_usize c2 i3
    let c ← aspis_core.field.CM31.new i2 i4
    let i5 ← limb + 2#usize
    let i6 ← Array.index_usize c2 i5
    let i7 ← limb + 3#usize
    let i8 ← Array.index_usize c2 i7
    let c1 ← aspis_core.field.CM31.new i6 i8
    ok (cont (iter1,
      fun e => let e1 := next_back e (some (slot, { c0 := c, c1 }))
               back e1))

/-- [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]: loop 2:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 633:8-639:9
    Name pattern: [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::gamma_combine_v6_packed_layer0"]
def aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop1
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31))
  (c2 : Array Std.U32 48#usize) (helper : Std.Usize) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1) =>
      aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop1.body c2
      helper iter1 back1)
    (iter, back)

/-- [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]: loop body 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 632:4-646:1
    Name pattern: [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_core::v6_onefold::gamma_combine_v6_packed_layer0"]
def aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0.body
  (to_slice_mut_back : Slice (Array aspis_core.field.QM31 4#usize) → Array
  (Array aspis_core.field.QM31 4#usize) 3#usize)
  (iter_mut_back : core.slice.iter.IterMut (Array aspis_core.field.QM31
  4#usize) → Slice (Array aspis_core.field.QM31 4#usize))
  (enumerate_back : core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut (Array aspis_core.field.QM31 4#usize)) →
  core.slice.iter.IterMut (Array aspis_core.field.QM31 4#usize))
  (combined : Array aspis_core.field.QM31 4#usize)
  (helper_powers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
  (c2 : Array Std.U32 48#usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array aspis_core.field.QM31 4#usize)))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array aspis_core.field.QM31 4#usize)) →
  core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut (Array
  aspis_core.field.QM31 4#usize))) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut (Array aspis_core.field.QM31 4#usize))) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut (Array
    aspis_core.field.QM31 4#usize)) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut (Array aspis_core.field.QM31 4#usize)))) (Array
    aspis_core.field.QM31 4#usize))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.enumerate.IteratorEnumerateMut.next iter
  match o with
  | none =>
    let (s, to_slice_mut_back1) ← lift (Array.to_slice_mut combined)
    let (im, iter_mut_back1) ← core.slice.Slice.iter_mut s
    let (iter2, enumerate_back1) ←
      core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im
    let e := next_back iter1 none
    let im1 := enumerate_back (back e)
    let s1 := iter_mut_back im1
    let a := to_slice_mut_back s1
    let back1 ←
      aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop0 iter2
        (fun e1 => e1) helper_powers a
    let im2 := enumerate_back1 back1
    let s2 := iter_mut_back1 im2
    let combined1 := to_slice_mut_back1 s2
    ok (done combined1)
  | some p =>
    let (helper, values) := p
    let (s, to_slice_mut_back1) ← lift (Array.to_slice_mut values)
    let (im, iter_mut_back1) ← core.slice.Slice.iter_mut s
    let (iter2, enumerate_back1) ←
      core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im
    let back1 ←
      aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0_loop1 iter2
        (fun e => e) c2 helper
    ok (cont (iter1,
      fun e =>
        let im1 := enumerate_back1 back1
        let s1 := iter_mut_back1 im1
        let a := to_slice_mut_back1 s1
        let a1 := (fun a2 => a2) a
        let e1 := next_back e (some (helper, a1))
        back e1))

/-- [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]: loop 0:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 632:4-646:1
    Name pattern: [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::v6_onefold::gamma_combine_v6_packed_layer0"]
def aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0
  (to_slice_mut_back : Slice (Array aspis_core.field.QM31 4#usize) → Array
  (Array aspis_core.field.QM31 4#usize) 3#usize)
  (iter_mut_back : core.slice.iter.IterMut (Array aspis_core.field.QM31
  4#usize) → Slice (Array aspis_core.field.QM31 4#usize))
  (enumerate_back : core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut (Array aspis_core.field.QM31 4#usize)) →
  core.slice.iter.IterMut (Array aspis_core.field.QM31 4#usize))
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array aspis_core.field.QM31 4#usize)))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array aspis_core.field.QM31 4#usize)) →
  core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut (Array
  aspis_core.field.QM31 4#usize)))
  (combined : Array aspis_core.field.QM31 4#usize)
  (helper_powers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
  (c2 : Array Std.U32 48#usize) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  loop
    (fun (iter1, back1) =>
      aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0.body
      to_slice_mut_back iter_mut_back enumerate_back combined helper_powers c2
      iter1 back1)
    (iter, back)

/-- [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 612:0-616:35
    Name pattern: [aspis_core::v6_onefold::gamma_combine_v6_packed_layer0]
    Visibility: public -/
@[rust_fun "aspis_core::v6_onefold::gamma_combine_v6_packed_layer0"]
def aspis_core.v6_onefold.gamma_combine_v6_packed_layer0
  (c1_packed : Slice Std.U8) (c2_packed : Slice Std.U8)
  (powers : aspis_core.state_only_spend_query.StateOnlySpendQueryPowers) :
  Result (core.result.Result (Array aspis_core.field.QM31 4#usize)
    aspis_core.v6_onefold.V6WireError)
  := do
  let i := Slice.len c1_packed
  let i1 ← aspis_core.v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY
  if i != i1
  then
    ok (core.result.Result.Err aspis_core.v6_onefold.V6WireError.WrongLength)
  else
    let i2 := Slice.len c2_packed
    let i3 ← aspis_core.v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY
    if i2 != i3
    then
      ok (core.result.Result.Err aspis_core.v6_onefold.V6WireError.WrongLength)
    else
      let r ←
        aspis_core.v6_onefold.decode_packed_m31_eight_aligned 104#usize
          c1_packed
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let combined ←
          aspis_core.v6_onefold.gamma_combine_v6_c1_slot_major val powers
        let pqm ← Array.index_usize powers.base.helpers 0#usize
        let pqm1 ← Array.index_usize powers.base.helpers 1#usize
        let r1 ←
          aspis_core.v6_onefold.decode_packed_m31_eight_aligned 48#usize
            c2_packed
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let a := Array.repeat 4#usize aspis_core.field.QM31.ZERO
          let helpers := Array.repeat 3#usize a
          let (s, to_slice_mut_back) ← lift (Array.to_slice_mut helpers)
          let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
          let (iter, enumerate_back) ←
            core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im
          let combined1 ←
            aspis_core.v6_onefold.gamma_combine_v6_packed_layer0_loop0
              to_slice_mut_back iter_mut_back enumerate_back iter (fun e => e)
              combined (Array.make 3#usize [ pqm, pqm1, powers.d ]) val1
          ok (core.result.Result.Ok combined1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array aspis_core.field.QM31 4#usize) (core.convert.FromSame
            aspis_core.v6_onefold.V6WireError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array aspis_core.field.QM31 4#usize) (core.convert.FromSame
          aspis_core.v6_onefold.V6WireError) residual

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'_0>}::call_mut]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 935:37-935:46
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>}::call_mut] -/
@[rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>}::call_mut"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3)
  := do
  let bcp ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.circle_fri.BaseCirclePoint) c tupled_args
  let m ← aspis_core.field.M31.mul bcp.x bcp.x
  let m1 ← aspis_core.field.M31.double m
  let m2 ← aspis_core.field.M31.sub m1 aspis_core.field.M31.ONE
  ok (m2, c)

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'_0>}::call_once]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 935:37-935:46
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>}::call_once] -/
@[rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>}::call_once"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3)
  (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'_0>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 935:37-935:46
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3 Std.Usize
  aspis_core.field.M31 := {
  call_once :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'_0>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 935:37-935:46
    Name pattern: [core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#3<'0>, (usize), aspis_core::field::M31>"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3 Std.Usize
  aspis_core.field.M31 := {
  FnOnceInst :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'_0>}::call_mut]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 934:37-934:46
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>}::call_mut] -/
@[rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>}::call_mut"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2)
  := do
  let i ← 2#usize * tupled_args
  let i1 ← i + 1#usize
  let m ← Array.index_usize c i1
  ok (m, c)

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'_0>}::call_once]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 934:37-934:46
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>}::call_once] -/
@[rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>}::call_once"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2)
  (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'_0>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 934:37-934:46
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2 Std.Usize
  aspis_core.field.M31 := {
  call_once :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'_0>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 934:37-934:46
    Name pattern: [core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#2<'0>, (usize), aspis_core::field::M31>"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2 Std.Usize
  aspis_core.field.M31 := {
  FnOnceInst :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'_0>}::call_mut]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 933:37-933:46
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>}::call_mut] -/
@[rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>}::call_mut"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1)
  := do
  let i ← 2#usize * tupled_args
  let m ← Array.index_usize c i
  ok (m, c)

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'_0>}::call_once]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 933:37-933:46
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>}::call_once] -/
@[rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>}::call_once"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1)
  (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'_0>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 933:37-933:46
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1 Std.Usize
  aspis_core.field.M31 := {
  call_once :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'_0>}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 933:37-933:46
    Name pattern: [core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnMut<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure#1<'0>, (usize), aspis_core::field::M31>"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1 Std.Usize
  aspis_core.field.M31 := {
  FnOnceInst :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(aspis_core::circle_fri::CircleFriError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure}::call_once]:
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 916:17-916:20
    Name pattern: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure, (aspis_core::circle_fri::CircleFriError), aspis_core::v6_onefold::V6WireError>}::call_once] -/
@[rust_fun
  "aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure, (aspis_core::circle_fri::CircleFriError), aspis_core::v6_onefold::V6WireError>}::call_once"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure.Insts.CoreOpsFunctionFnOnceTupleCircleFriErrorV6WireError.call_once
  (c : aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure)
  (tupled_args : aspis_core.circle_fri.CircleFriError) :
  Result aspis_core.v6_onefold.V6WireError
  := do
  ok aspis_core.v6_onefold.V6WireError.InvalidQuerySchedule

/-- Trait implementation: [aspis_core::v6_onefold::prepare_v6_onefold_coordinates::{impl core::ops::function::FnOnce<(aspis_core::circle_fri::CircleFriError,), aspis_core::v6_onefold::V6WireError> for aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure}]
    Source: 'crates/aspis-core/src/v6_onefold.rs', lines 916:17-916:20
    Name pattern: [core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure, (aspis_core::circle_fri::CircleFriError), aspis_core::v6_onefold::V6WireError>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<aspis_core::v6_onefold::prepare_v6_onefold_coordinates::closure, (aspis_core::circle_fri::CircleFriError), aspis_core::v6_onefold::V6WireError>"]
def
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure.Insts.CoreOpsFunctionFnOnceTupleCircleFriErrorV6WireError
  : core.ops.function.FnOnce
  aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure
  aspis_core.circle_fri.CircleFriError aspis_core.v6_onefold.V6WireError := {
  call_once :=
    aspis_core.v6_onefold.prepare_v6_onefold_coordinates.closure.Insts.CoreOpsFunctionFnOnceTupleCircleFriErrorV6WireError.call_once
}


end V7Tag73CurrentHelpersOpaque
