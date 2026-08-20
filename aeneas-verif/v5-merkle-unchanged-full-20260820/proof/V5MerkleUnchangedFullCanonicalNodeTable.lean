import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullSectionBase
import V5MerkleUnchangedFullFrontierPositionUniqueness

/-! A canonical maintained node table from leaves and ordered frontier data. -/

namespace AspisV5MerkleUnchangedFullCanonicalNodeTable

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullLeafTable
open AspisV5MerkleUnchangedFullSectionBase
open AspisV5MerkleUnchangedFullSectionChildOrder
open AspisV5MerkleUnchangedFullFrontierPositionUniqueness

abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- Extend the finite ordered frontier to a total lookup without changing any
listed value.  Position uniqueness makes the extension well-defined. -/
theorem exists_frontier_assignment
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (frontier_length : base.frontier.length =
      (frontierPositions tree queries).length) :
    ∃ frontierAt : FrontierPosition → Digest32,
      (frontierPositions tree queries).map frontierAt = base.frontier := by
  let defaultDigest : Digest32 := fun _ => 0
  have related : List.Forall₂ (fun _ _ : Digest32 => True)
      base.frontier base.frontier := by
    rw [List.forall₂_same]
    simp
  obtain ⟨frontierAt, _unusedAt, assignment, _unusedAssignment,
      _pointwise⟩ := exists_total_pair_assignment
        (fun _ _ : Digest32 => True) defaultDigest defaultDigest
        (frontierPositions tree queries) base.frontier base.frontier
        (frontierPositions_nodup tree queries) frontier_length
        frontier_length related
  exact ⟨frontierAt, assignment⟩

/-- Recursively hash active nodes and use the assigned proof frontier at every
inactive position. -/
noncomputable def canonicalNode
    (sha256 : List ModelByte → Digest32) (tree : V5PrivateSection)
    (queries : Finset V5Query)
    (base : ExactSectionBaseData sha256 tree queries)
    (frontierAt : FrontierPosition → Digest32) : Nat → Nat → Digest32
  | 0, index =>
      if index ∈ activeIndices tree queries 0 then base.leafAt index
      else frontierAt ⟨0, index⟩
  | level + 1, index =>
      if index ∈ activeIndices tree queries (level + 1) then
        (sha256MerkleHashing sha256).radix4Node fun slot =>
          canonicalNode sha256 tree queries base frontierAt level
            (4 * index + slot)
      else frontierAt ⟨level + 1, index⟩

theorem canonicalNode_zero_of_active
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (frontierAt : FrontierPosition → Digest32) (index : Nat)
    (active : index ∈ activeIndices tree queries 0) :
    canonicalNode sha256 tree queries base frontierAt 0 index =
      base.leafAt index := by
  simp [canonicalNode, active]

theorem canonicalNode_succ_of_active
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (frontierAt : FrontierPosition → Digest32) (level index : Nat)
    (active : index ∈ activeIndices tree queries (level + 1)) :
    canonicalNode sha256 tree queries base frontierAt (level + 1) index =
      (sha256MerkleHashing sha256).radix4Node fun slot =>
        canonicalNode sha256 tree queries base frontierAt level
          (4 * index + slot) := by
  simp [canonicalNode, active]

theorem canonicalNode_of_inactive
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (frontierAt : FrontierPosition → Digest32) (level index : Nat)
    (inactive : index ∉ activeIndices tree queries level) :
    canonicalNode sha256 tree queries base frontierAt level index =
      frontierAt ⟨level, index⟩ := by
  cases level with
  | zero => simp [canonicalNode, inactive]
  | succ level => simp [canonicalNode, inactive]

/-- Every maintained frontier position is outside the corresponding active
level, by the literal radix and binary-cap filters that construct it. -/
theorem frontier_position_inactive
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (position : FrontierPosition)
    (member : position ∈ frontierPositions tree queries) :
    position.index ∉ activeIndices tree queries position.level := by
  unfold frontierPositions at member
  rcases List.mem_append.mp member with radixMember | binaryMember
  · rw [radixFrontierPositions_eq_levelAbsentChildIndices] at radixMember
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at radixMember
    obtain ⟨level, levelBound, index, indexMember, positionEq⟩ := radixMember
    subst position
    simp only [levelAbsentChildIndices, List.mem_flatMap] at indexMember
    obtain ⟨parent, parentMember, childMember⟩ := indexMember
    simp only [absentChildIndices, List.mem_map, List.mem_filter,
      List.mem_range] at childMember
    obtain ⟨slot, ⟨slotBound, slotAbsent⟩, indexEq⟩ := childMember
    subst index
    exact of_decide_eq_true slotAbsent
  · unfold binaryCapFrontierPositions at binaryMember
    simp only [List.mem_map, List.mem_filter] at binaryMember
    obtain ⟨index, ⟨indexMember, indexAbsent⟩, positionEq⟩ := binaryMember
    subst position
    exact of_decide_eq_true indexAbsent

/-- Node-table fields that are fixed before checking the final binary root. -/
structure ExactSectionNodeCore
    (sha256 : List ModelByte → Digest32) (tree : V5PrivateSection)
    (queries : Finset V5Query)
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

/-- Equal frontier lengths supply the unique assignment; the canonical
recursive definition then supplies the leaf and every radix-parent equation. -/
theorem frontier_length_yields_exact_node_core
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (frontier_length : base.frontier.length =
      (frontierPositions tree queries).length) :
    Nonempty (ExactSectionNodeCore sha256 tree queries base) := by
  obtain ⟨frontierAt, frontierValues⟩ :=
    exists_frontier_assignment base frontier_length
  let node := canonicalNode sha256 tree queries base frontierAt
  refine ⟨{
    node := node
    leaf_node_eq := by
      intro index active
      exact canonicalNode_zero_of_active base frontierAt index active
    frontier_eq := by
      rw [← frontierValues]
      apply List.map_congr_left
      intro position positionMember
      symm
      exact canonicalNode_of_inactive base frontierAt position.level
        position.index
        (frontier_position_inactive tree queries position positionMember)
    parent_eq := by
      intro query queryMember level levelBound
      have parentActive :
          indexAtRadixLevel (sectionIndex tree query) (level + 1) ∈
            activeIndices tree queries (level + 1) :=
        Finset.mem_image.mpr ⟨query, queryMember, rfl⟩
      exact canonicalNode_succ_of_active base frontierAt level
        (indexAtRadixLevel (sectionIndex tree query) (level + 1))
        parentActive }⟩

#print axioms exists_frontier_assignment
#print axioms canonicalNode_zero_of_active
#print axioms canonicalNode_succ_of_active
#print axioms canonicalNode_of_inactive
#print axioms frontier_position_inactive
#print axioms frontier_length_yields_exact_node_core

end AspisV5MerkleUnchangedFullCanonicalNodeTable
