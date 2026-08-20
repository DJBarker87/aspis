import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullCanonicalNodeTable
import V5MerkleUnchangedFullGroupChildSources
import V5MerkleUnchangedFullLevelChildSources
import V5MerkleUnchangedFullFrontierChunks

/-! Every extracted radix child is the corresponding canonical model node. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullCanonicalChildSources

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullSectionBase
open AspisV5MerkleUnchangedFullWireTable
open AspisV5MerkleUnchangedFullFrontierChunks
open AspisV5MerkleUnchangedFullGroupTraceLists
open AspisV5MerkleUnchangedFullLevelTraceLists
open AspisV5MerkleUnchangedFullSectionChildOrder
open AspisV5MerkleUnchangedFullMaskCounts
open AspisV5MerkleUnchangedFullGroupParentAlignment
open AspisV5MerkleUnchangedFullGroupChildSources
open AspisV5MerkleUnchangedFullLevelChildSources
open AspisV5MerkleUnchangedFullCanonicalNodeTable

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- Pointwise consequence of the ordered active-level map equation. -/
theorem mapped_level_lookup_exact
    (indices : List Nat) (node : Nat → Digest32)
    (generated : GeneratedDigestVec)
    (map_eq : indices.map node =
      generated.val.map generatedArrayToDigest)
    (ordinal index : Nat) (index_at : indices[ordinal]? = some index) :
    node index = generatedArrayToDigest generated.val[ordinal]! := by
  obtain ⟨ordinal_lt, index_value⟩ :=
    List.getElem?_eq_some_iff.mp index_at
  have lengths := congrArg List.length map_eq
  simp only [List.length_map] at lengths
  have generated_lt : ordinal < generated.val.length := by omega
  have point := List.getElem_of_eq map_eq (by simpa using ordinal_lt)
  simp only [List.getElem_map] at point
  rw [index_value] at point
  simpa [getElem!_pos generated.val ordinal generated_lt] using point

/-- A radix-frontier lookup is the same ordinal in the complete frontier and
therefore returns the canonical node fixed by `core.frontier_eq`. -/
theorem core_radix_frontier_lookup
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (core : ExactSectionNodeCore sha256 tree queries base)
    (ordinal : Nat) (position : FrontierPosition)
    (position_at : (radixFrontierPositions tree queries)[ordinal]? =
      some position) :
    base.frontier[ordinal]? =
      some (core.node position.level position.index) := by
  obtain ⟨ordinal_lt, position_value⟩ :=
    List.getElem?_eq_some_iff.mp position_at
  have full_at : (frontierPositions tree queries)[ordinal]? =
      some position := by
    unfold frontierPositions
    rw [List.getElem?_append_left ordinal_lt]
    exact position_at
  have point := congrArg (fun values => values[ordinal]?) core.frontier_eq
  rw [List.getElem?_map, full_at] at point
  simpa using point

/-- The reified frontier retained by the released base uses the byte map
expected by the unchanged radix proof. -/
theorem generated_base_frontier_flat_exact
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query} {leafLevel : GeneratedDigestVec}
    {frontierBytes : Slice Std.U8}
    (base : ExactSectionGeneratedBaseData sha256 tree queries leafLevel
      frontierBytes) :
    base.frontier.flatMap digestBytes =
      frontierBytes.val.map generatedU8ToByte := by
  calc
    base.frontier.flatMap digestBytes =
        frontierBytes.val.map
          AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte :=
      base.generated_frontier_bytes_eq
    _ = frontierBytes.val.map generatedU8ToByte := by
      apply List.map_congr_left
      intro byte byteMem
      exact (radix_generated_byte_eq byte).symm

/-- For one aligned extracted group, each of its four literal child digests
is exactly the canonical model node selected by that slot. -/
theorem aligned_group_children_match_canonical_nodes
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {frontierBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32} {leafLevel : GeneratedDigestVec}
    (summary : RawLevelStepSummary sha256 root frontierBytes topology
      binaryDepth)
    (base : ExactSectionGeneratedBaseData sha256 tree queries leafLevel
      frontierBytes)
    (core : ExactSectionNodeCore sha256 tree queries
      base.toExactSectionBaseData)
    (ordinal : Nat) (ordinal_lt : ordinal < summary.groupSteps.length)
    (alignment : ExactGroupParentAlignment tree queries level
      summary.groupSteps[ordinal] ordinal)
    (sources : ExactAlignedGroupChildSources tree queries level
      summary.startNodePos summary.groupSteps[ordinal] ordinal alignment)
    (level_lt : level < radixLevelCount tree)
    (level_start_cursor : summary.startNodePos.val =
      32 * sectionFrontierOffset tree queries level)
    (level_values :
      (orderedActiveIndices tree queries level).map (core.node level) =
        summary.levelBefore.val.map generatedArrayToDigest) :
    ∀ slot : Fin 4,
      generatedArrayToDigest
          summary.groupSteps[ordinal].witness.children[slot.val]! =
        core.node level (4 * alignment.parent + slot.val) := by
  intro slot
  by_cases active : 4 * alignment.parent + slot.val ∈
      activeIndices tree queries level
  · have indexAt := sources.live_index slot active
    rw [levelPresentChildIndices_eq_orderedActiveIndices] at indexAt
    have valueAt := mapped_level_lookup_exact
      (orderedActiveIndices tree queries level) (core.node level)
      summary.levelBefore level_values
      (presentLevelOffset tree queries level ordinal +
        liveSlotCount
          (localChildSlots tree queries level alignment.parent) slot.val)
      (4 * alignment.parent + slot.val) indexAt
    rw [sources.live_source slot active]
    exact valueAt.symm
  · let localOrdinal := absentLevelOffset tree queries level ordinal +
      frontierSlotCount
        (localChildSlots tree queries level alignment.parent) slot.val
    let globalOrdinal := sectionFrontierOffset tree queries level +
      localOrdinal
    have localAt : (levelAbsentChildIndices tree queries level)[
        localOrdinal]? = some (4 * alignment.parent + slot.val) := by
      simpa [localOrdinal] using sources.frontier_index slot active
    let childPosition : FrontierPosition :=
      { level := level, index := 4 * alignment.parent + slot.val }
    have globalAt : (radixFrontierPositions tree queries)[globalOrdinal]? =
        some childPosition := by
      simpa [childPosition] using
        level_frontier_rank_to_global tree queries level localOrdinal
          (4 * alignment.parent + slot.val) level_lt localAt
    have coreAt := core_radix_frontier_lookup base.toExactSectionBaseData
      core globalOrdinal childPosition globalAt
    obtain ⟨frontier_lt, frontier_value⟩ :=
      List.getElem?_eq_some_iff.mp coreAt
    have flat := generated_base_frontier_flat_exact base
    apply funext
    intro byte
    have sourceByte := sources.frontier_source slot active byte.val byte.isLt
    have sourceOffset : summary.startNodePos.val +
        32 * localOrdinal + byte.val =
          32 * globalOrdinal + byte.val := by
      simp only [globalOrdinal]
      rw [level_start_cursor]
      omega
    rw [sourceOffset] at sourceByte
    have frontierByte := reified_frontier_byte_exact frontierBytes.val
      base.frontier flat globalOrdinal frontier_lt byte.val byte.isLt
    rw [frontier_value] at frontierByte
    unfold generatedArrayToDigest
    calc
      generatedU8ToByte
          (summary.groupSteps[ordinal].witness.children[slot.val]!.val.get
            ⟨byte.val, by simpa using byte.isLt⟩) =
          generatedU8ToByte
            summary.groupSteps[ordinal].witness.children[slot.val]!.val[
              byte.val]! := by
            congr 1
            symm
            exact getElem!_pos _ _ (by simpa using byte.isLt)
      _ = generatedU8ToByte frontierBytes.val[
          32 * globalOrdinal + byte.val]! := congrArg generatedU8ToByte
            sourceByte
      _ = core.node level (4 * alignment.parent + slot.val) byte :=
        frontierByte.symm

#print axioms mapped_level_lookup_exact
#print axioms core_radix_frontier_lookup
#print axioms generated_base_frontier_flat_exact
#print axioms aligned_group_children_match_canonical_nodes

end AspisV5MerkleUnchangedFullCanonicalChildSources
