import V5MerkleUnchangedFull.Funs

/-!
Definitional replay surface for the unchanged production radix verifier.
The production extraction threads a pure hash callback explicitly; the older
audited proof used an equivalent result-shaped call.  This module supplies
that result shape and otherwise repeats the extracted loop equations exactly.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable section

namespace V5MerkleUnchangedCompat

open V5MerkleUnchangedFull

abbrev GeneratedHash :=
  Slice (Slice Std.U8) → Array Std.U8 32#usize

class HashContext where
  hash : GeneratedHash

variable [HashContext]

namespace merkle

abbrev Radix4BinaryCapTopology :=
  V5MerkleUnchangedFull.aspis_core.merkle.Radix4BinaryCapTopology

abbrev MatchedRadix4BinaryCapSuffix :=
  V5MerkleUnchangedFull.aspis_core.merkle.MatchedRadix4BinaryCapSuffix

abbrev DOM_NODE := V5MerkleUnchangedFull.aspis_core.merkle.DOM_NODE
abbrev DOM_NODE4 := V5MerkleUnchangedFull.aspis_core.merkle.DOM_NODE4

def fixed_hashv
    (inputs : Slice (Slice Std.U8)) : Result (Array Std.U8 32#usize) :=
  .ok (HashContext.hash inputs)

end merkle

/-- [v5_merkle_fixed_hash_adapter::merkle::fixed_node_hash]:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 24:0-30:1 -/
def merkle.fixed_node_hash
  (left : Array Std.U8 32#usize) (right : Array Std.U8 32#usize) :
  Result (Array Std.U8 32#usize)
  := do
  let input := Array.repeat 65#usize 0#u8
  let input1 ← Array.update input 0#usize merkle.DOM_NODE
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input1
      { start := 1#usize, «end» := 33#usize }
  let s1 ← lift (Array.to_slice left)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let input2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input2
      { start := 33#usize, «end» := 65#usize }
  let s4 ← lift (Array.to_slice right)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let input3 := index_mut_back1 s5
  let s6 ← lift (Array.to_slice input3)
  let s7 ← lift (Array.to_slice (Array.make 1#usize [ s6 ]))
  merkle.fixed_hashv s7

/-- [v5_merkle_fixed_hash_adapter::merkle::{v5_merkle_fixed_hash_adapter::merkle::Radix4BinaryCapTopology}::level_indices]:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 428:4-434:5 -/
def merkle.Radix4BinaryCapTopology.impl.level_indices
  (self : merkle.Radix4BinaryCapTopology) (level : Std.Usize) :
  Result (Option (Slice Std.U32))
  := do
  if level > self.radix_levels
  then ok none
  else
    let s := alloc.vec.Vec.deref self.level_indices
    let i ← Array.index_usize self.level_offsets level
    let i1 ← lift (Std.Usize.wrapping_add level 1#usize)
    let i2 ← Array.index_usize self.level_offsets i1
    core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice Std.U32) s
      { start := i, «end» := i2 }

/-- [v5_merkle_fixed_hash_adapter::merkle::{v5_merkle_fixed_hash_adapter::merkle::Radix4BinaryCapTopology}::group_masks]:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 436:4-442:5 -/
def merkle.Radix4BinaryCapTopology.impl.group_masks
  (self : merkle.Radix4BinaryCapTopology) (level : Std.Usize) :
  Result (Option (Slice Std.U8))
  := do
  if level >= self.radix_levels
  then ok none
  else
    let s := alloc.vec.Vec.deref self.group_masks
    let i ← Array.index_usize self.group_offsets level
    let i1 ← lift (Std.Usize.wrapping_add level 1#usize)
    let i2 ← Array.index_usize self.group_offsets i1
    core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
      { start := i, «end» := i2 }

/-- [v5_merkle_fixed_hash_adapter::merkle::verify_radix4_binary_cap_with_matched_topology]: loop body 2:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 519:8-542:9 -/
def
  merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0.body
  (node_bytes : Slice Std.U8) (level : alloc.vec.Vec (Array Std.U8 32#usize))
  (next : alloc.vec.Vec (Array Std.U8 32#usize)) (present : Std.U8)
  (pending_return : Option Bool) (iter : core.ops.range.Range Std.Usize)
  (node_pos : Std.Usize) (value_pos : Std.Usize)
  (input : Array Std.U8 129#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize ×
    Std.Usize × (Array Std.U8 129#usize)) ((alloc.vec.Vec (Array Std.U8
    32#usize)) × Std.Usize × Std.Usize × (Option Bool) × Std.U32))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let s ← lift (Array.to_slice input)
    let s1 ← lift (Array.to_slice (Array.make 1#usize [ s ]))
    let a ← merkle.fixed_hashv s1
    let next1 ← alloc.vec.Vec.push next a
    ok (done (next1, node_pos, value_pos, pending_return, 1#u32))
  | some slot =>
    let i ← lift (Std.Usize.wrapping_mul slot 32#usize)
    let i1 ← lift (Std.Usize.wrapping_add 1#usize i)
    let i2 ← lift (Std.Usize.wrapping_add slot 1#usize)
    let i3 ← lift (Std.Usize.wrapping_mul i2 32#usize)
    let i4 ← lift (Std.Usize.wrapping_add 1#usize i3)
    let (child, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input
        { start := i1, «end» := i4 }
    let i5 ← lift (Std.U8.wrapping_shl 1#u8 (UScalar.cast .U32 slot))
    let i6 ← lift (present &&& i5)
    if i6 != 0#u8
    then
      let s := alloc.vec.Vec.deref level
      let o1 : Option (Array Std.U8 32#usize) ←
        core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice (Array
          Std.U8 32#usize)) s value_pos
      Option.elim o1
        (ok (ControlFlow.done
          (next, node_pos, value_pos, some false, 0#u32)))
        (fun value => do
        let s1 ← lift (Array.to_slice value)
        let child1 ←
          core.slice.Slice.copy_from_slice core.marker.CopyU8 child s1
        let value_pos1 ← lift (Std.Usize.wrapping_add value_pos 1#usize)
        let input1 := index_mut_back child1
        ok (cont (iter1, node_pos, value_pos1, input1)))
    else
      let i7 ← lift (Std.Usize.wrapping_add node_pos 32#usize)
      let i8 := Slice.len node_bytes
      if i7 > i8
      then ok (done (next, node_pos, value_pos, some false, 0#u32))
      else
        let i9 ← lift (Std.Usize.wrapping_add node_pos 32#usize)
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) node_bytes
            { start := node_pos, «end» := i9 }
        let child1 ←
          core.slice.Slice.copy_from_slice core.marker.CopyU8 child s
        let node_pos1 ← lift (Std.Usize.wrapping_add node_pos 32#usize)
        let input1 := index_mut_back child1
        ok (cont (iter1, node_pos1, value_pos, input1))

/-- [v5_merkle_fixed_hash_adapter::merkle::verify_radix4_binary_cap_with_matched_topology]: loop 2:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 519:8-542:9 -/
def merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (node_bytes : Slice Std.U8)
  (level : alloc.vec.Vec (Array Std.U8 32#usize))
  (next : alloc.vec.Vec (Array Std.U8 32#usize)) (node_pos : Std.Usize)
  (value_pos : Std.Usize) (present : Std.U8) (input : Array Std.U8 129#usize)
  (pending_return : Option Bool) :
  Result ((alloc.vec.Vec (Array Std.U8 32#usize)) × Std.Usize × Std.Usize ×
    (Option Bool) × Std.U32)
  := do
  loop
    (fun (iter1, node_pos1, value_pos1, input1) =>
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0.body
      node_bytes level next present pending_return iter1 node_pos1 value_pos1
      input1)
    (iter, node_pos, value_pos, input)

/-- [v5_merkle_fixed_hash_adapter::merkle::verify_radix4_binary_cap_with_matched_topology]: loop body 1:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 513:4-547:5 -/
def merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
  (node_bytes : Slice Std.U8) (level : alloc.vec.Vec (Array Std.U8 32#usize))
  (iter : core.slice.iter.Iter Std.U8)
  (next : alloc.vec.Vec (Array Std.U8 32#usize)) (node_pos : Std.Usize)
  (value_pos : Std.Usize) (pending_return : Option Bool) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U8) × (alloc.vec.Vec (Array
    Std.U8 32#usize)) × Std.Usize × Std.Usize × (Option Bool))
    ((alloc.vec.Vec (Array Std.U8 32#usize)) × (alloc.vec.Vec (Array Std.U8
    32#usize)) × Std.Usize × (Option Bool) × Std.U32))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none =>
    let i := alloc.vec.Vec.len level
    if value_pos != i
    then ok (done (level, next, node_pos, some false, 0#u32))
    else
      let (level1, next1) := core.mem.swap level next
      ok (done (level1, next1, node_pos, pending_return, 1#u32))
  | some present =>
    let input := Array.repeat 129#usize 0#u8
    let a ← Array.update input 0#usize merkle.DOM_NODE4
    let (next1, node_pos1, value_pos1, pending_return1, i) ←
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
        { start := 0#usize, «end» := 4#usize } node_bytes level next node_pos
        value_pos present a pending_return
    match i with
    | 1#uscalar =>
      ok (cont (iter1, next1, node_pos1, value_pos1, pending_return1))
    | _ =>
      match pending_return1 with
      | none => ok (done (level, next1, node_pos1, none, 0#u32))
      | some _ => ok (done (level, next1, node_pos1, pending_return1, 0#u32))

/-- [v5_merkle_fixed_hash_adapter::merkle::verify_radix4_binary_cap_with_matched_topology]: loop 1:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 513:4-547:5 -/
def merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0
  (iter : core.slice.iter.Iter Std.U8) (node_bytes : Slice Std.U8)
  (level : alloc.vec.Vec (Array Std.U8 32#usize))
  (next : alloc.vec.Vec (Array Std.U8 32#usize)) (node_pos : Std.Usize)
  (value_pos : Std.Usize) (pending_return : Option Bool) :
  Result ((alloc.vec.Vec (Array Std.U8 32#usize)) × (alloc.vec.Vec (Array
    Std.U8 32#usize)) × Std.Usize × (Option Bool) × Std.U32)
  := do
  loop
    (fun (iter1, next1, node_pos1, value_pos1, pending_return1) =>
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
      node_bytes level iter1 next1 node_pos1 value_pos1 pending_return1)
    (iter, next, node_pos, value_pos, pending_return)

/-- [v5_merkle_fixed_hash_adapter::merkle::verify_radix4_binary_cap_with_matched_topology]: loop body 0:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 513:4-579:1 -/
def merkle.verify_radix4_binary_cap_with_matched_topology_loop0.body
  (root : Array Std.U8 32#usize) (node_bytes : Slice Std.U8) (i : Std.U32)
  (i1 : Std.Usize) (v : alloc.vec.Vec Std.U32) (a : Array Std.Usize 17#usize)
  (v1 : alloc.vec.Vec Std.U8) (a1 : Array Std.Usize 16#usize)
  (binary_depth : Std.U32) (iter : core.ops.range.Range Std.Usize)
  (level : alloc.vec.Vec (Array Std.U8 32#usize))
  (next : alloc.vec.Vec (Array Std.U8 32#usize)) (node_pos : Std.Usize)
  (pending_return : Option Bool) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 32#usize)) × (alloc.vec.Vec (Array Std.U8 32#usize)) ×
    Std.Usize × (Option Bool)) ((alloc.vec.Vec (Array Std.U8 32#usize)) ×
    (alloc.vec.Vec (Array Std.U8 32#usize)) × (Option Bool)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let o1 ←
      merkle.Radix4BinaryCapTopology.impl.level_indices
        {
          binary_depth := i,
          radix_levels := i1,
          level_indices := v,
          level_offsets := a,
          group_masks := v1,
          group_offsets := a1
        } i1
    match o1 with
    | none => ok (done (level, next, pending_return))
    | some indices =>
      let i2 ← lift (binary_depth &&& 1#u32)
      if i2 = 0#u32
      then
        let s ← alloc.vec.Vec.as_slice Global level
        let i3 := Slice.len indices
        if i3 = 1#usize
        then
          let i4 := Slice.len s
          if i4 = 1#usize
          then
            let i5 ← Slice.index_usize indices 0#usize
            match i5 with
            | 0#uscalar =>
              let value ← Slice.index_usize s 0#usize
              let i6 := Slice.len node_bytes
              if node_pos = i6
              then
                let b ←
                  core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
                    value root
                ok (done (level, next, some b))
              else ok (done (level, next, some false))
            | _ => ok (done (level, next, pending_return))
          else ok (done (level, next, pending_return))
        else ok (done (level, next, pending_return))
      else
        let s ← alloc.vec.Vec.as_slice Global level
        let i3 := Slice.len indices
        if i3 = 2#usize
        then
          let i4 := Slice.len s
          if i4 = 2#usize
          then
            let i5 ← Slice.index_usize indices 0#usize
            match i5 with
            | 0#uscalar =>
              let i6 ← Slice.index_usize indices 1#usize
              match i6 with
              | 1#uscalar =>
                let left ← Slice.index_usize s 0#usize
                let right ← Slice.index_usize s 1#usize
                let top ← merkle.fixed_node_hash left right
                let i7 := Slice.len node_bytes
                if node_pos = i7
                then
                  let b ←
                    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
                      top root
                  ok (done (level, next, some b))
                else ok (done (level, next, some false))
              | _ => ok (done (level, next, pending_return))
            | _ => ok (done (level, next, pending_return))
          else ok (done (level, next, pending_return))
        else
          let i4 := Slice.len indices
          if i4 = 1#usize
          then
            let i5 := Slice.len s
            if i5 = 1#usize
            then
              let index ← Slice.index_usize indices 0#usize
              let value ← Slice.index_usize s 0#usize
              let i6 ← lift (Std.Usize.wrapping_add node_pos 32#usize)
              let i7 := Slice.len node_bytes
              if i6 > i7
              then ok (done (level, next, pending_return))
              else
                let i8 ← lift (Std.Usize.wrapping_add node_pos 32#usize)
                let s1 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                    node_bytes { start := node_pos, «end» := i8 }
                let r ←
                  core.array.TryFromArrayCopySlice.try_from 32#usize
                    core.marker.CopyU8 s1
                let sibling ←
                  core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
                let node_pos1 ←
                  lift (Std.Usize.wrapping_add node_pos 32#usize)
                if index = 0#u32
                then
                  let top ← merkle.fixed_node_hash value sibling
                  let i9 := Slice.len node_bytes
                  if node_pos1 = i9
                  then
                    let b ←
                      core.array.equality.PartialEqArray.eq
                        core.cmp.PartialEqU8 top root
                    ok (done (level, next, some b))
                  else ok (done (level, next, some false))
                else
                  if index = 1#u32
                  then
                    let top ← merkle.fixed_node_hash sibling value
                    let i9 := Slice.len node_bytes
                    if node_pos1 = i9
                    then
                      let b ←
                        core.array.equality.PartialEqArray.eq
                          core.cmp.PartialEqU8 top root
                      ok (done (level, next, some b))
                    else ok (done (level, next, some false))
                  else ok (done (level, next, pending_return))
            else ok (done (level, next, pending_return))
          else ok (done (level, next, pending_return))
  | some plan_level =>
    let next1 ← alloc.vec.Vec.clear Global next
    let o1 ←
      merkle.Radix4BinaryCapTopology.impl.group_masks
        {
          binary_depth := i,
          radix_levels := i1,
          level_indices := v,
          level_offsets := a,
          group_masks := v1,
          group_offsets := a1
        } plan_level
    match o1 with
    | none => ok (done (level, next1, some false))
    | some masks =>
      let iter2 ←
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          masks
      let (level1, next2, node_pos1, pending_return1, i2) ←
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0 iter2
          node_bytes level next1 node_pos 0#usize pending_return
      match i2 with
      | 1#uscalar =>
        ok (cont (iter1, level1, next2, node_pos1, pending_return1))
      | _ =>
        match pending_return1 with
        | none => ok (done (level1, next2, none))
        | some _ => ok (done (level1, next2, pending_return1))

/-- [v5_merkle_fixed_hash_adapter::merkle::verify_radix4_binary_cap_with_matched_topology]: loop 0:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 513:4-579:1 -/
def merkle.verify_radix4_binary_cap_with_matched_topology_loop0
  (iter : core.ops.range.Range Std.Usize) (root : Array Std.U8 32#usize)
  (node_bytes : Slice Std.U8) (i : Std.U32) (i1 : Std.Usize)
  (v : alloc.vec.Vec Std.U32) (a : Array Std.Usize 17#usize)
  (v1 : alloc.vec.Vec Std.U8) (a1 : Array Std.Usize 16#usize)
  (binary_depth : Std.U32) (level : alloc.vec.Vec (Array Std.U8 32#usize))
  (next : alloc.vec.Vec (Array Std.U8 32#usize)) (node_pos : Std.Usize)
  (pending_return : Option Bool) :
  Result ((alloc.vec.Vec (Array Std.U8 32#usize)) × (alloc.vec.Vec (Array
    Std.U8 32#usize)) × (Option Bool))
  := do
  loop
    (fun (iter1, level1, next1, node_pos1, pending_return1) =>
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0.body root
      node_bytes i i1 v a v1 a1 binary_depth iter1 level1 next1 node_pos1
      pending_return1)
    (iter, level, next, node_pos, pending_return)

/-- [v5_merkle_fixed_hash_adapter::merkle::verify_radix4_binary_cap_with_matched_topology]:
    Source: 'src/../../../../crates/aspis-core/src/merkle.rs', lines 497:0-579:1 -/
def merkle.verify_radix4_binary_cap_with_matched_topology
  (root : Array Std.U8 32#usize) (node_bytes : Slice Std.U8)
  (matched : merkle.MatchedRadix4BinaryCapSuffix)
  (level : alloc.vec.Vec (Array Std.U8 32#usize))
  (next : alloc.vec.Vec (Array Std.U8 32#usize)) :
  Result (Bool × (alloc.vec.Vec (Array Std.U8 32#usize)) × (alloc.vec.Vec
    (Array Std.U8 32#usize)))
  := do
  let b ← alloc.vec.Vec.is_empty Global level
  if b
  then ok (false, level, next)
  else
    let i := Slice.len node_bytes
    let i1 ← lift (i &&& 31#usize)
    if i1 != 0#usize
    then ok (false, level, next)
    else
      let i2 := alloc.vec.Vec.len level
      if i2 != matched.expected_len
      then ok (false, level, next)
      else
        let (level1, next1, pending_return) ←
          merkle.verify_radix4_binary_cap_with_matched_topology_loop0
            {
              start := matched.radix_level,
              «end» := matched.topology.radix_levels
            } root node_bytes matched.topology.binary_depth
            matched.topology.radix_levels matched.topology.level_indices
            matched.topology.level_offsets matched.topology.group_masks
            matched.topology.group_offsets matched.binary_depth level next
            0#usize none
        match pending_return with
        | none => fail panic
        | some b1 => ok (b1, level1, next1)

/-- The replay surface is definitionally the exact generated outer loop. -/
theorem merkle.compat_level_loop_eq_exact
    (iter : core.ops.range.Range Std.Usize)
    (root : Array Std.U8 32#usize) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology) (binaryDepth : Std.U32)
    (level next : alloc.vec.Vec (Array Std.U8 32#usize))
    (nodePos : Std.Usize) (pending : Option Bool) :
    merkle.verify_radix4_binary_cap_with_matched_topology_loop0 iter root
        nodeBytes topology.binary_depth topology.radix_levels
        topology.level_indices topology.level_offsets topology.group_masks
        topology.group_offsets binaryDepth level next nodePos pending =
      V5MerkleUnchangedFull.aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology_loop0
        iter HashContext.hash root nodeBytes topology.binary_depth
        topology.radix_levels topology.level_indices topology.level_offsets
        topology.group_masks topology.group_offsets binaryDepth level next
        nodePos pending := by
  rfl

/-- The complete replay function is definitionally the exact generated
production function with the context callback inserted. -/
theorem merkle.compat_verify_eq_exact
    (root : Array Std.U8 32#usize) (nodeBytes : Slice Std.U8)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (level next : alloc.vec.Vec (Array Std.U8 32#usize)) :
    merkle.verify_radix4_binary_cap_with_matched_topology root nodeBytes
        matched level next =
      V5MerkleUnchangedFull.aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology
        HashContext.hash root nodeBytes matched level next := by
  rfl

#print axioms merkle.compat_level_loop_eq_exact
#print axioms merkle.compat_verify_eq_exact

end V5MerkleUnchangedCompat
