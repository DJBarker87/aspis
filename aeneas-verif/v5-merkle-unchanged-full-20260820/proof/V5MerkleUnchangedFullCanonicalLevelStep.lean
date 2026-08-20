import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullCanonicalChildSources

/-! One extracted radix level preserves the canonical active-node table. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullCanonicalLevelStep

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullGroupTraceLists
open AspisV5MerkleUnchangedFullGroupCursorPrefixes
open AspisV5MerkleUnchangedFullLevelTraceLists
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionBase
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullGroupParentAlignment
open AspisV5MerkleUnchangedFullGroupChildSources
open AspisV5MerkleUnchangedFullLevelChildSources
open AspisV5MerkleUnchangedFullCanonicalNodeTable
open AspisV5MerkleUnchangedFullCanonicalChildSources

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- One source-ordered Rust group hashes exactly the four canonical children
of its maintained parent. -/
theorem aligned_group_parent_matches_canonical_node
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
    (fields : FullExactConstructedTopologyFields queries topology)
    (plan_eq : summary.planLevel.val = sectionRadixStart tree + level)
    (level_lt : level < radixLevelCount tree)
    (level_start_cursor : summary.startNodePos.val =
      32 * sectionFrontierOffset tree queries level)
    (level_values :
      (orderedActiveIndices tree queries level).map (core.node level) =
        summary.levelBefore.val.map generatedArrayToDigest)
    (ordinal : Nat) (ordinal_lt : ordinal < summary.groupSteps.length) :
    core.node (level + 1)
        (orderedActiveIndices tree queries (level + 1))[ordinal]! =
      generatedArrayToDigest summary.groupSteps[ordinal].digest := by
  obtain ⟨alignment, sources⟩ := level_group_yields_exact_child_sources
    tree queries level summary fields plan_eq level_lt ordinal ordinal_lt
  have children := aligned_group_children_match_canonical_nodes tree queries
    level summary base core ordinal ordinal_lt alignment sources level_lt
    level_start_cursor level_values
  have parentActive : alignment.parent ∈
      activeIndices tree queries (level + 1) :=
    (Finset.mem_sort (fun left right : Nat => left ≤ right)).mp
      alignment.parent_mem
  obtain ⟨query, queryMem, queryEq⟩ := Finset.mem_image.mp parentActive
  have parentEquation := core.parent_eq query queryMem level level_lt
  have childrenEquation :
      (fun slot : Fin 4 =>
        core.node level (4 * alignment.parent + slot.val)) =
      (fun slot : Fin 4 => generatedArrayToDigest
        summary.groupSteps[ordinal].witness.children[slot.val]!) := by
    funext slot
    exact (children slot).symm
  calc
    core.node (level + 1)
        (orderedActiveIndices tree queries (level + 1))[ordinal]! =
        core.node (level + 1) alignment.parent := by
      rw [alignment.parent_eq]
    _ = (sha256MerkleHashing sha256).radix4Node fun slot =>
          core.node level (4 * alignment.parent + slot.val) := by
      simpa [queryEq] using parentEquation
    _ = (sha256MerkleHashing sha256).radix4Node fun slot =>
          generatedArrayToDigest
            summary.groupSteps[ordinal].witness.children[slot.val]! := by
      rw [childrenEquation]
    _ = generatedArrayToDigest summary.groupSteps[ordinal].digest :=
      sources.parent_digest_exact.symm

/-- The complete extracted group list therefore produces the canonical next
active level, in exactly the maintained parent order. -/
theorem level_step_preserves_canonical_active_values
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
    (fields : FullExactConstructedTopologyFields queries topology)
    (plan_eq : summary.planLevel.val = sectionRadixStart tree + level)
    (level_lt : level < radixLevelCount tree)
    (level_start_cursor : summary.startNodePos.val =
      32 * sectionFrontierOffset tree queries level)
    (level_values :
      (orderedActiveIndices tree queries level).map (core.node level) =
        summary.levelBefore.val.map generatedArrayToDigest) :
    (orderedActiveIndices tree queries (level + 1)).map
        (core.node (level + 1)) =
      summary.levelAfter.val.map generatedArrayToDigest := by
  have counts := level_group_count_lists_exact tree queries level summary
    fields plan_eq level_lt
  have group_length : summary.groupSteps.length =
      (orderedActiveIndices tree queries (level + 1)).length := by
    have lengths := congrArg List.length counts.1
    simpa [groupLiveCounts] using lengths
  rw [summary.parents_exact]
  apply List.ext_getElem
  · simp [groupDigests, group_length]
  · intro ordinal left_lt right_lt
    have ordinal_lt : ordinal < summary.groupSteps.length := by
      rw [group_length]
      simpa [List.length_map] using left_lt
    have parent_lt : ordinal <
        (orderedActiveIndices tree queries (level + 1)).length := by
      simpa [List.length_map] using left_lt
    simp only [List.getElem_map, groupDigests]
    simpa [getElem!_pos
      (orderedActiveIndices tree queries (level + 1)) ordinal parent_lt] using
      aligned_group_parent_matches_canonical_node tree queries level summary
        base core fields plan_eq level_lt level_start_cursor level_values
        ordinal ordinal_lt

#print axioms aligned_group_parent_matches_canonical_node
#print axioms level_step_preserves_canonical_active_values

end AspisV5MerkleUnchangedFullCanonicalLevelStep
