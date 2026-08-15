import V5MerkleDeployedSource.Funs
import AspisFormal.V5MerkleRustBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedHelperBridge

open V5MerkleDeployedSource
open AspisV5MerkleRustBridge

def generatedU8ToByte (byte : Std.U8) :
    AspisV5MerkleAuthenticationBinding.Byte :=
  ⟨byte.val, by
    have h := UScalar.hBounds byte
    norm_num at h ⊢
    exact h⟩

def generatedArrayToDigest (digest : Array Std.U8 32#usize) : Digest32 :=
  fun index => generatedU8ToByte (digest.val.get ⟨index.val, by
    have hlength := digest.property
    change digest.val.length = 32 at hlength
    omega⟩)

theorem digestBytes_generatedArrayToDigest
    (digest : Array Std.U8 32#usize) :
    digestBytes (generatedArrayToDigest digest) =
      digest.val.map generatedU8ToByte := by
  unfold digestBytes generatedArrayToDigest
  simpa using List.ofFn_getElem_eq_map digest.val generatedU8ToByte

/-- Exact, explicit boundary between the generated opaque `hashv` call and
SHA-256 over the concatenation of its Rust slices. -/
def FixedHashvEqualsSha256
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32) : Prop :=
  ∀ inputs output, merkle.fixed_hashv inputs = .ok output →
    generatedArrayToDigest output =
      sha256 ((inputs.val.flatMap fun input => input.val).map generatedU8ToByte)

/-- The generated leaf helper hashes exactly
`0x10 || tree_tag || value_and_salt`. -/
theorem private_leaf_hash_record_fixed_exact
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (treeTag : Std.U8) (record : Slice Std.U8)
    (output : Array Std.U8 32#usize)
    (hrun : state_only_private_merkle.private_leaf_hash_record_fixed
      treeTag record = .ok output) :
    generatedArrayToDigest output =
      sha256 ([0x10, generatedU8ToByte treeTag] ++
        record.val.map generatedU8ToByte) := by
  unfold state_only_private_merkle.private_leaf_hash_record_fixed at hrun
  simp only [lift] at hrun
  have hexact := hhash _ output hrun
  simpa [Array.make, Array.val_to_slice, generatedU8ToByte,
    state_only_private_merkle.DOM_LEAF] using hexact

/-- The generated binary-cap helper hashes exactly
`0x11 || left || right`. -/
theorem fixed_node_hash_exact
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (left right output : Array Std.U8 32#usize)
    (hrun : merkle.fixed_node_hash left right = .ok output) :
    generatedArrayToDigest output =
      sha256 ([0x11] ++ digestBytes (generatedArrayToDigest left) ++
        digestBytes (generatedArrayToDigest right)) := by
  have hleft := left.property
  have hright := right.property
  change left.val.length = 32 at hleft
  change right.val.length = 32 at hright
  have hleftMap : (left.val.map generatedU8ToByte).length = 32 := by
    simpa using hleft
  have hrightMap : (right.val.map generatedU8ToByte).length = 32 := by
    simpa using hright
  have htakeLeft : List.take 32 (left.val.map generatedU8ToByte) =
      left.val.map generatedU8ToByte := by
    apply List.take_of_length_le
    omega
  have htakeRight : List.take 32 (right.val.map generatedU8ToByte) =
      right.val.map generatedU8ToByte := by
    apply List.take_of_length_le
    omega
  unfold merkle.fixed_node_hash at hrun
  simp [Std.lift, Array.update, core.array.Array.index_mut,
    core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.index_usize, Array.make, Slice.len, Slice.length,
    merkle.DOM_NODE, hleft, hright] at hrun
  simp_lists at hrun
  simp at hrun
  have hexact := hhash _ output hrun
  rw [digestBytes_generatedArrayToDigest,
    digestBytes_generatedArrayToDigest]
  simp [List.setSlice!, hleft, hright] at hexact
  rw [htakeLeft, htakeRight] at hexact
  simpa [Array.make, Array.val_to_slice, generatedU8ToByte,
    merkle.DOM_NODE] using hexact

/-- Once all four slots are filled, the extracted recursive helper returns
the byte preimage and both cursors without another read or hash. -/
theorem fixed_fill_radix_children_done
    (nodeBytes : Slice Std.U8)
    (level : Slice (Array Std.U8 32#usize))
    (present : Std.U8) (slot nodePos valuePos : Std.Usize)
    (input : Array Std.U8 129#usize)
    (hdone : 4 ≤ slot.val) :
    merkle.fixed_fill_radix_children nodeBytes level present slot nodePos
        valuePos input = .ok (some (input, nodePos, valuePos)) := by
  rw [merkle.fixed_fill_radix_children.eq_def]
  have hdone' : slot ≥ 4#usize := by scalar_tac
  rw [if_pos hdone']

/-- Once every mask has been processed, the extracted group helper returns
the accumulated parent vector and both cursors unchanged. -/
theorem fixed_hash_radix_groups_done
    (nodeBytes : Slice Std.U8)
    (level : Slice (Array Std.U8 32#usize))
    (masks : Slice Std.U8) (maskPos nodePos valuePos : Std.Usize)
    (next : alloc.vec.Vec (Array Std.U8 32#usize))
    (hdone : masks.val.length ≤ maskPos.val) :
    merkle.fixed_hash_radix_groups nodeBytes level masks maskPos nodePos
        valuePos next = .ok (some (next, nodePos, valuePos)) := by
  rw [merkle.fixed_hash_radix_groups.eq_def]
  have hdone' : maskPos ≥ Slice.len masks := by scalar_tac
  rw [if_pos hdone']

/-- Once the released topology levels are exhausted, the extracted level
helper returns the final level, scratch vector, and frontier cursor exactly. -/
theorem fixed_hash_radix_levels_done
    (topology : merkle.Radix4BinaryCapTopology)
    (nodeBytes : Slice Std.U8)
    (planLevel nodePos : Std.Usize)
    (level next : alloc.vec.Vec (Array Std.U8 32#usize))
    (hdone : topology.radix_levels.val ≤ planLevel.val) :
    merkle.fixed_hash_radix_levels topology nodeBytes planLevel nodePos level
        next = .ok (some (level, next, nodePos)) := by
  rw [merkle.fixed_hash_radix_levels.eq_def]
  have hdone' : planLevel ≥ topology.radix_levels := by scalar_tac
  rw [if_pos hdone']

#print axioms digestBytes_generatedArrayToDigest
#print axioms private_leaf_hash_record_fixed_exact
#print axioms fixed_node_hash_exact
#print axioms fixed_fill_radix_children_done
#print axioms fixed_hash_radix_groups_done
#print axioms fixed_hash_radix_levels_done

end AspisV5MerkleGeneratedHelperBridge
