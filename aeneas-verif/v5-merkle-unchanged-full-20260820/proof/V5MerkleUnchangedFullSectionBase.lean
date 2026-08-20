import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullLeafTable
import V5MerkleUnchangedFullWireTable

/-! Everything needed for `ExactSectionTrace` except the internal-node table. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullSectionBase

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullHelperSoundness
open AspisV5MerkleUnchangedFullLeafTable
open AspisV5MerkleUnchangedFullWireTable

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

theorem helper_digest_eq_radix_digest (digest : GeneratedDigest) :
    AspisV5MerkleUnchangedFullHelperBridge.generatedArrayToDigest digest =
      AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest digest := by
  funext index
  apply Fin.ext
  rfl

/-- Parser, record, leaf, and wire facts for one released section.  The only
missing fields of `ExactSectionTrace` are the shared internal nodes, frontier
positions, parent equations, and final root equation. -/
structure ExactSectionBaseData
    (sha256 : List ModelByte → Digest32) (tree : V5PrivateSection)
    (queries : Finset V5Query) where
  wire : List ModelByte
  recordAt : Nat → List ModelByte
  frontier : List Digest32
  leafAt : Nat → Digest32
  records_length : ∀ index, index ∈ activeIndices tree queries 0 →
    (recordAt index).length = valueWidth tree + 32
  wire_eq : wire = encodePrivateSection
    ((orderedActiveIndices tree queries 0).map recordAt) frontier
  leaf_eq : ∀ index, index ∈ activeIndices tree queries 0 →
    leafAt index = (sha256MerkleHashing sha256).privateLeaf
      (treeTag tree) (recordAt index)

/-- Replace the placeholder leaf-level equation with the exact generated
level while retaining a small public base-data type. -/
structure ExactSectionGeneratedBaseData
    (sha256 : List ModelByte → Digest32) (tree : V5PrivateSection)
    (queries : Finset V5Query) (leafLevel : GeneratedDigestVec)
    (frontierBytes : Slice Std.U8) : Type extends
    ExactSectionBaseData sha256 tree queries where
  generated_leaf_level_eq :
    (orderedActiveIndices tree queries 0).map leafAt =
      leafLevel.val.map
        AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest
  generated_frontier_bytes_eq : frontier.flatMap digestBytes =
    frontierBytes.val.map
      AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte

/-- The generated base together with the exact parser prefix/suffix split.
Keeping this equation in the package lets the five unchanged driver calls be
concatenated without introducing a separate serialization premise. -/
structure ExactSectionGeneratedBaseWithSplit
    (sha256 : List ModelByte → Digest32) (tree : V5PrivateSection)
    (queries : Finset V5Query) (leafLevel : GeneratedDigestVec)
    (recordBytes frontierBytes proofBytes remainder : Slice Std.U8) : Type extends
    ExactSectionGeneratedBaseData sha256 tree queries leafLevel frontierBytes where
  generated_records_bytes_eq :
    ((orderedActiveIndices tree queries 0).map recordAt).flatten =
      recordBytes.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte
  generated_proof_split :
    proofBytes.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte =
      wire ++ remainder.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte

/-- One successful unchanged helper supplies all section data except the
internal radix node table. -/
theorem released_helper_yields_exact_section_base_with_split
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {binaryDepth : Std.U32} {generatedTag : Std.U8}
    {generatedWidth : Std.Usize} {expectedIndices : Slice Std.U32}
    {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize} {level next : GeneratedDigestVec}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : GeneratedDigestVec}
    (trace : FullExactReleasedHelperTrace sha256 root binaryDepth generatedTag
      generatedWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext)
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (tagModel : generatedTag.val = (treeTag tree).val)
    (widthModel : generatedWidth.val = valueWidth tree)
    (indicesModel : expectedIndices.val.map (fun index => index.val) =
      orderedActiveIndices tree queries 0)
    (queriesNonempty : queries.Nonempty) :
    Nonempty (ExactSectionGeneratedBaseWithSplit sha256 tree queries
      trace.execution.leafLevel opening.records opening.frontier proofBytes
      remainder) := by
  let indices := orderedActiveIndices tree queries 0
  have indicesNonempty : indices ≠ [] := by
    obtain ⟨query, queryMem⟩ := queriesNonempty
    have activeMem := sectionIndex_mem_active tree queryMem
    have sortedMem : sectionIndex tree query ∈ indices := by
      exact (Finset.mem_sort (fun left right : Nat => left ≤ right)).mpr
        activeMem
    exact fun empty => by simpa [indices, empty] using sortedMem
  let leafTable := Classical.choice
    (released_helper_yields_exact_leaf_table trace indices indicesModel
      (orderedActiveIndices_nodup tree queries 0) indicesNonempty)
  have expectedPositive : 0 < (Slice.len expectedIndices).val := by
    rw [Slice.len_val]
    change 0 < expectedIndices.val.length
    have hlength : expectedIndices.val.length = indices.length := by
      simpa using congrArg List.length indicesModel
    have hpositive := List.length_pos_iff.mpr indicesNonempty
    omega
  let wireTable := Classical.choice
    (released_helper_yields_exact_wire_table trace indices indicesModel
      expectedPositive leafTable)
  have generatedTagEq :
      AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte generatedTag =
        treeTag tree := by
    apply Fin.ext
    exact tagModel
  refine ⟨{
    wire := wireTable.wire
    recordAt := leafTable.recordAt
    frontier := wireTable.frontier
    leafAt := leafTable.leafAt
    records_length := by
      intro index indexMem
      have listMem : index ∈ indices :=
        (Finset.mem_sort (fun left right : Nat => left ≤ right)).mpr indexMem
      rw [leafTable.record_length index listMem, widthModel]
    wire_eq := wireTable.wire_eq
    leaf_eq := by
      intro index indexMem
      have listMem : index ∈ indices :=
        (Finset.mem_sort (fun left right : Nat => left ≤ right)).mpr indexMem
      rw [leafTable.leaf_eq index listMem, generatedTagEq]
    generated_leaf_level_eq := by
      calc
        indices.map leafTable.leafAt =
            trace.execution.leafLevel.val.map
              AspisV5MerkleUnchangedFullHelperBridge.generatedArrayToDigest :=
          leafTable.leaves_eq
        _ = trace.execution.leafLevel.val.map
              AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest := by
          apply List.map_congr_left
          intro digest _
          exact helper_digest_eq_radix_digest digest
    generated_frontier_bytes_eq := wireTable.frontier_bytes
    generated_records_bytes_eq := wireTable.records_bytes
    generated_proof_split := wireTable.proof_split }⟩

/-- Forgetting only the parser split recovers the smaller section-base
package used by the internal-node development. -/
theorem released_helper_yields_exact_section_base
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {binaryDepth : Std.U32} {generatedTag : Std.U8}
    {generatedWidth : Std.Usize} {expectedIndices : Slice Std.U32}
    {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize} {level next : GeneratedDigestVec}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : GeneratedDigestVec}
    (trace : FullExactReleasedHelperTrace sha256 root binaryDepth generatedTag
      generatedWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext)
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (tagModel : generatedTag.val = (treeTag tree).val)
    (widthModel : generatedWidth.val = valueWidth tree)
    (indicesModel : expectedIndices.val.map (fun index => index.val) =
      orderedActiveIndices tree queries 0)
    (queriesNonempty : queries.Nonempty) :
    Nonempty (ExactSectionGeneratedBaseData sha256 tree queries
      trace.execution.leafLevel opening.frontier) := by
  let base := Classical.choice
    (released_helper_yields_exact_section_base_with_split trace tree queries
      tagModel widthModel indicesModel queriesNonempty)
  exact ⟨base.toExactSectionGeneratedBaseData⟩

/-- The exact remaining dynamic obligation: one node table matching the leaf
table, frontier order, every radix-four parent hash, and the binary-cap root. -/
structure ExactSectionNodeData
    (sha256 : List ModelByte → Digest32) (tree : V5PrivateSection)
    (root : Digest32) (queries : Finset V5Query)
    (base : ExactSectionBaseData sha256 tree queries) where
  node : Nat → Nat → Digest32
  leaf_node_eq : ∀ index, index ∈ activeIndices tree queries 0 →
    node 0 index = base.leafAt index
  frontier_eq : base.frontier =
    (frontierPositions tree queries).map fun position =>
      node position.level position.index
  parent_eq : ∀ query, query ∈ queries → ∀ level,
    level < radixLevelCount tree →
    node (level + 1)
        (indexAtRadixLevel (sectionIndex tree query) (level + 1)) =
      (sha256MerkleHashing sha256).radix4Node fun slot =>
        node level
          (4 * indexAtRadixLevel (sectionIndex tree query) (level + 1) + slot)
  root_eq : (sha256MerkleHashing sha256).binaryNode
    (node (radixLevelCount tree) 0)
    (node (radixLevelCount tree) 1) = root

/-- Supplying only the exact internal-node data completes the maintained
section trace; parser, record, and leaf facts are reused verbatim. -/
def base_and_nodes_yield_exact_section_trace
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {root : Digest32} {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (nodes : ExactSectionNodeData sha256 tree root queries base) :
    ExactSectionTrace sha256 tree root queries where
  wire := base.wire
  recordAt := base.recordAt
  frontier := base.frontier
  node := nodes.node
  records_length := base.records_length
  wire_eq := base.wire_eq
  frontier_eq := nodes.frontier_eq
  leaf_eq := by
    intro query queryMem
    have activeMem := sectionIndex_mem_active tree queryMem
    rw [nodes.leaf_node_eq (sectionIndex tree query) activeMem,
      base.leaf_eq (sectionIndex tree query) activeMem]
  parent_eq := nodes.parent_eq
  root_eq := nodes.root_eq

#print axioms released_helper_yields_exact_section_base_with_split
#print axioms released_helper_yields_exact_section_base
#print axioms base_and_nodes_yield_exact_section_trace

end AspisV5MerkleUnchangedFullSectionBase
