import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullRecordChunks
import V5MerkleUnchangedFullLeafTraceLists

/-! A total level-zero node table recovered from the unchanged helper trace. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullLeafTable

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleUnchangedFullHelperSoundness
open AspisV5MerkleUnchangedFullRecordChunks
open AspisV5MerkleUnchangedFullLeafTraceLists

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest

/-- Distinct names paired with equally long related lists can be extended to
total lookup functions without changing either list's order. -/
theorem exists_total_pair_assignment
    {Index Left Right : Type*} [DecidableEq Index]
    (relation : Left → Right → Prop)
    (defaultLeft : Left) (defaultRight : Right)
    (indices : List Index) (lefts : List Left) (rights : List Right)
    (distinct : indices.Nodup)
    (leftLength : lefts.length = indices.length)
    (rightLength : rights.length = indices.length)
    (related : List.Forall₂ relation lefts rights) :
    ∃ leftAt rightAt,
      indices.map leftAt = lefts ∧
      indices.map rightAt = rights ∧
      ∀ index ∈ indices, relation (leftAt index) (rightAt index) := by
  induction indices generalizing lefts rights with
  | nil =>
      have hleft : lefts = [] := List.eq_nil_of_length_eq_zero (by simpa using leftLength)
      have hright : rights = [] := List.eq_nil_of_length_eq_zero (by simpa using rightLength)
      subst lefts
      subst rights
      exact ⟨fun _ => defaultLeft, fun _ => defaultRight, by simp⟩
  | cons index indices inductionHypothesis =>
      cases lefts with
      | nil => simp at leftLength
      | cons left lefts =>
          cases rights with
          | nil => simp at rightLength
          | cons right rights =>
              have tailDistinct := (List.nodup_cons.mp distinct).2
              have indexFresh := (List.nodup_cons.mp distinct).1
              have tailLeftLength : lefts.length = indices.length := by
                simpa using leftLength
              have tailRightLength : rights.length = indices.length := by
                simpa using rightLength
              have headRelated : relation left right := by
                cases related with
                | cons head _ => exact head
              have tailRelated : List.Forall₂ relation lefts rights := by
                cases related with
                | cons _ tail => exact tail
              obtain ⟨tailLeftAt, tailRightAt, tailLeftMap, tailRightMap,
                tailPointwise⟩ := inductionHypothesis lefts rights tailDistinct
                  tailLeftLength tailRightLength tailRelated
              let leftAt : Index → Left := fun target =>
                if target = index then left else tailLeftAt target
              let rightAt : Index → Right := fun target =>
                if target = index then right else tailRightAt target
              refine ⟨leftAt, rightAt, ?_, ?_, ?_⟩
              · simp only [List.map_cons, leftAt, if_pos]
                congr 1
                calc
                  indices.map (fun target =>
                      if target = index then left else tailLeftAt target) =
                      indices.map tailLeftAt := by
                        apply List.map_congr_left
                        intro target targetMem
                        rw [if_neg]
                        intro targetEq
                        subst target
                        exact indexFresh targetMem
                  _ = lefts := tailLeftMap
              · simp only [List.map_cons, rightAt, if_pos]
                congr 1
                calc
                  indices.map (fun target =>
                      if target = index then right else tailRightAt target) =
                      indices.map tailRightAt := by
                        apply List.map_congr_left
                        intro target targetMem
                        rw [if_neg]
                        intro targetEq
                        subst target
                        exact indexFresh targetMem
                  _ = rights := tailRightMap
              · intro target targetMem
                simp only [List.mem_cons] at targetMem
                rcases targetMem with rfl | targetMem
                · simpa [leftAt, rightAt] using headRelated
                · have targetNe : target ≠ index := by
                    intro targetEq
                    subst target
                    exact indexFresh targetMem
                  simpa [leftAt, rightAt, targetNe] using
                    tailPointwise target targetMem

/-- Exact level-zero records and digests indexed by the maintained active
indices.  The two map equations retain the production order. -/
structure ExactLeafTable
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (treeTag : Std.U8) (valueWidth : Std.Usize)
    (indices : List Nat) (iter : core.slice.iter.ChunksExact Std.U8)
    (leafLevel : GeneratedDigestVec) where
  recordAt : Nat → List AspisV5MerkleAuthenticationBinding.Byte
  leafAt : Nat → Digest32
  records_eq : indices.map recordAt =
    iter.chunks.map fun record => record.val.map generatedU8ToByte
  leaves_eq : indices.map leafAt =
    leafLevel.val.map generatedArrayToDigest
  record_length : ∀ index ∈ indices,
    (recordAt index).length = valueWidth.val + 32
  leaf_eq : ∀ index ∈ indices,
    leafAt index = (sha256MerkleHashing sha256).privateLeaf
      (generatedU8ToByte treeTag) (recordAt index)

/-- The successful unchanged clear/chunk/hash sequence supplies a total exact
leaf table for any distinct list equal to the extracted expected indices. -/
theorem released_helper_yields_exact_leaf_table
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {root : GeneratedDigest} {binaryDepth : Std.U32} {treeTag : Std.U8}
    {valueWidth : Std.Usize} {expectedIndices : Slice Std.U32}
    {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize} {level next : GeneratedDigestVec}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : GeneratedDigestVec}
    (trace : FullExactReleasedHelperTrace sha256 root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext)
    (indices : List Nat)
    (indicesModel : expectedIndices.val.map (fun index => index.val) = indices)
    (distinct : indices.Nodup) (indicesNonempty : indices ≠ []) :
    Nonempty (ExactLeafTable sha256 treeTag valueWidth indices
      trace.execution.recordIter trace.execution.leafLevel) := by
  have expectedPositive : 0 < (Slice.len expectedIndices).val := by
    rw [Slice.len_val]
    change 0 < expectedIndices.val.length
    have hlength : expectedIndices.val.length = indices.length := by
      simpa using congrArg List.length indicesModel
    have hpositive := List.length_pos_iff.mpr indicesNonempty
    omega
  obtain ⟨chunks, recordWidth⟩ :=
    released_helper_record_chunks_exact trace.execution trace.parser
      expectedPositive
  obtain ⟨digests, leafLevelEq, ordered⟩ :=
    generated_leaf_trace_yields_list_view sha256 HashContext.hash treeTag
      trace.execution.recordIter trace.execution.clearedLevel
      trace.execution.leafLevel trace.leaves
  have hcleared : trace.execution.clearedLevel.val = [] := by
    have hrun := trace.execution.clear_run
    unfold alloc.vec.Vec.clear at hrun
    simp only at hrun
    have hclear := Result.ok.inj hrun
    have hclearVal := congrArg (fun value : GeneratedDigestVec => value.val)
      hclear
    simpa [alloc.vec.Vec.new] using hclearVal.symm
  have hleafLevel : trace.execution.leafLevel.val = digests := by
    simpa [hcleared] using leafLevelEq
  have hindicesLength : indices.length =
      (Slice.len expectedIndices).val := by
    rw [Slice.len_val]
    have := congrArg List.length indicesModel
    simpa using this.symm
  have hleftLength : trace.execution.recordIter.chunks.length =
      indices.length := by
    rw [chunks.count_eq, ← hindicesLength]
  have hrightLength : digests.length = indices.length := by
    rw [← ordered.length_eq, hleftLength]
  obtain ⟨recordSliceAt, digestAt, recordMap, digestMap, pairAt⟩ :=
    exists_total_pair_assignment
      (ExactGeneratedLeafPair sha256 treeTag) (Slice.new Std.U8)
      (Array.repeat 32#usize 0#u8) indices
      trace.execution.recordIter.chunks digests distinct hleftLength
      hrightLength ordered
  let recordAt : Nat → List AspisV5MerkleAuthenticationBinding.Byte :=
    fun index => (recordSliceAt index).val.map generatedU8ToByte
  let leafAt : Nat → Digest32 :=
    fun index => generatedArrayToDigest (digestAt index)
  exact ⟨{
    recordAt := recordAt
    leafAt := leafAt
    records_eq := by
      rw [← recordMap]
      simp [recordAt, List.map_map]
    leaves_eq := by
      rw [hleafLevel, ← digestMap]
      simp [leafAt, List.map_map]
    record_length := by
      intro index indexMem
      have chunkMem : recordSliceAt index ∈
          trace.execution.recordIter.chunks := by
        rw [← recordMap]
        exact List.mem_map_of_mem (f := recordSliceAt) indexMem
      simp only [recordAt, List.length_map]
      rw [chunks.chunk_length (recordSliceAt index) chunkMem, recordWidth]
    leaf_eq := by
      intro index indexMem
      exact pairAt index indexMem }⟩

#print axioms exists_total_pair_assignment
#print axioms released_helper_yields_exact_leaf_table

end AspisV5MerkleUnchangedFullLeafTable
