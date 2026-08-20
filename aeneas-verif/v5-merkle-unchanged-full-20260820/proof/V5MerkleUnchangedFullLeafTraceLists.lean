import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullLeafBridge

/-! Ordered-list consequences of the exact generated leaf-loop trace. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullLeafTraceLists

open V5MerkleUnchangedFull
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleUnchangedFullLeafBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest

/-- The exact relation between one record chunk consumed by the generated
leaf loop and the digest appended for it. -/
def ExactGeneratedLeafPair
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (treeTag : Std.U8) (record : Slice Std.U8)
    (digest : GeneratedDigest) : Prop :=
  generatedArrayToDigest digest =
    (sha256MerkleHashing sha256).privateLeaf
      (generatedU8ToByte treeTag)
      (record.val.map generatedU8ToByte)

/-- A list view of a generated leaf trace.  It exposes, in source order,
the exact record chunks consumed and digests appended by the Rust loop. -/
def GeneratedLeafTraceListView
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (treeTag : Std.U8)
    (iter : core.slice.iter.ChunksExact Std.U8)
    (initialLevel finalLevel : GeneratedDigestVec) : Prop :=
  ∃ digests : List GeneratedDigest,
    finalLevel.val = initialLevel.val ++ digests ∧
    List.Forall₂ (ExactGeneratedLeafPair sha256 treeTag)
      iter.chunks digests

private theorem next_some_exact
    (iter iter' : core.slice.iter.ChunksExact Std.U8)
    (record : Slice Std.U8)
    (hrun : core.slice.iter.IteratorChunksExact.next iter =
      .ok (some record, iter')) :
    iter.chunks = record :: iter'.chunks := by
  cases hchunks : iter.chunks with
  | nil =>
      simp [core.slice.iter.IteratorChunksExact.next, hchunks] at hrun
  | cons head tail =>
      simp [core.slice.iter.IteratorChunksExact.next, hchunks] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      rfl

private theorem push_success_exact
    (level level' : GeneratedDigestVec) (digest : GeneratedDigest)
    (hrun : alloc.vec.Vec.push level digest = .ok level') :
    level'.val = level.val ++ [digest] := by
  unfold alloc.vec.Vec.push at hrun
  dsimp only at hrun
  split at hrun
  · injection hrun with heq
    subst level'
    simp [List.concat_eq_append]
  · simp at hrun

/-- Every successful generated leaf trace is exactly an ordered traversal of
the iterator's chunks.  No chunk is skipped or duplicated, each appended
digest is the maintained private-leaf hash of that same chunk, and the final
generated level is the initial level followed by those digests. -/
theorem generated_leaf_trace_yields_list_view
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash)
    (treeTag : Std.U8)
    (iter : core.slice.iter.ChunksExact Std.U8)
    (initialLevel finalLevel : GeneratedDigestVec)
    (trace : GeneratedLeafTrace sha256 hash treeTag iter initialLevel finalLevel) :
    GeneratedLeafTraceListView sha256 treeTag iter initialLevel finalLevel := by
  induction trace with
  | done iter level empty =>
      refine ⟨[], ?_, ?_⟩
      · simp
      · rw [empty]
        exact List.Forall₂.nil
  | step iter iter' record level level' finalLevel digest next_run hash_run
      push_run digest_eq tail ih =>
      have hchunks := next_some_exact iter iter' record next_run
      have hlevel := push_success_exact level level' digest push_run
      rcases ih with ⟨tailDigests, htailLevel, htailPairs⟩
      refine ⟨digest :: tailDigests, ?_, ?_⟩
      · rw [htailLevel, hlevel]
        simp [List.append_assoc]
      · rw [hchunks]
        exact List.Forall₂.cons digest_eq htailPairs

theorem ordered_leaf_pairs_length_eq
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {treeTag : Std.U8}
    {iter : core.slice.iter.ChunksExact Std.U8}
    {digests : List GeneratedDigest}
    (ordered : List.Forall₂ (ExactGeneratedLeafPair sha256 treeTag)
      iter.chunks digests) :
    iter.chunks.length = digests.length :=
  ordered.length_eq

/-- Position-by-position API for consumers that already identify record
positions with the maintained list of expected indices. -/
theorem ordered_leaf_pair_at
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {treeTag : Std.U8}
    {iter : core.slice.iter.ChunksExact Std.U8}
    {digests : List GeneratedDigest}
    (ordered : List.Forall₂ (ExactGeneratedLeafPair sha256 treeTag)
      iter.chunks digests)
    (index : Nat)
    (hrecord : index < iter.chunks.length)
    (hdigest : index < digests.length) :
    ExactGeneratedLeafPair sha256 treeTag
      (iter.chunks.get ⟨index, hrecord⟩)
      (digests.get ⟨index, hdigest⟩) :=
  ordered.get hrecord hdigest

theorem every_record_has_exact_digest
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {treeTag : Std.U8}
    {iter : core.slice.iter.ChunksExact Std.U8}
    {digests : List GeneratedDigest}
    (ordered : List.Forall₂ (ExactGeneratedLeafPair sha256 treeTag)
      iter.chunks digests)
    (index : Nat) (hrecord : index < iter.chunks.length) :
    ∃ hdigest : index < digests.length,
      generatedArrayToDigest (digests.get ⟨index, hdigest⟩) =
        (sha256MerkleHashing sha256).privateLeaf
          (generatedU8ToByte treeTag)
          ((iter.chunks.get ⟨index, hrecord⟩).val.map generatedU8ToByte) := by
  have hdigest : index < digests.length := by
    rwa [← ordered_leaf_pairs_length_eq ordered]
  exact ⟨hdigest, ordered_leaf_pair_at ordered index hrecord hdigest⟩

#print axioms generated_leaf_trace_yields_list_view
#print axioms ordered_leaf_pairs_length_eq
#print axioms ordered_leaf_pair_at
#print axioms every_record_has_exact_digest

end AspisV5MerkleUnchangedFullLeafTraceLists
