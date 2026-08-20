import V5MerkleUnchangedFull.Funs
import AspisFormal.V5MerkleRustBridge

/-! Exact hash framing for the unchanged production helper extraction. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace AspisV5MerkleUnchangedFullHelperBridge

open V5MerkleUnchangedFull
open AspisV5MerkleRustBridge

abbrev GeneratedHash :=
  Slice (Slice Std.U8) → Array Std.U8 32#usize

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

/-- The single executable hash boundary: the callback used by the extracted
Rust is SHA-256 of the concatenated slices supplied by the production code. -/
def HashCallbackEqualsSha256
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash) : Prop :=
  ∀ inputs,
    generatedArrayToDigest (hash inputs) =
      sha256 ((inputs.val.flatMap fun input => input.val).map generatedU8ToByte)

/-- The generated production leaf helper hashes exactly
`0x10 || tree_tag || value_and_salt`. -/
theorem private_leaf_hash_record_exact
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (treeTag : Std.U8) (record : Slice Std.U8)
    (output : Array Std.U8 32#usize)
    (hrun :
      aspis_core.state_only_private_merkle.private_leaf_hash_record
        hash treeTag record = .ok output) :
    generatedArrayToDigest output =
      sha256 ([0x10, generatedU8ToByte treeTag] ++
        record.val.map generatedU8ToByte) := by
  unfold aspis_core.state_only_private_merkle.private_leaf_hash_record at hrun
  simp only [lift] at hrun
  have hout : hash (Array.to_slice (Array.make 2#usize [
      Array.to_slice (Array.make 2#usize [
        aspis_core.state_only_private_merkle.DOM_LEAF, treeTag ]),
      record ])) = output := by
    simpa using Result.ok.inj hrun
  have hexact := hhash (Array.to_slice (Array.make 2#usize [
    Array.to_slice (Array.make 2#usize [
      aspis_core.state_only_private_merkle.DOM_LEAF, treeTag ]), record ]))
  rw [hout] at hexact
  simpa [Array.make, Array.val_to_slice, generatedU8ToByte,
    aspis_core.state_only_private_merkle.DOM_LEAF] using hexact

#print axioms digestBytes_generatedArrayToDigest
#print axioms private_leaf_hash_record_exact

end AspisV5MerkleUnchangedFullHelperBridge
