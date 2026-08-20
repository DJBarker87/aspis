import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullGroupCursorPrefixes
import V5MerkleUnchangedFullGroupParentAlignment
import V5MerkleUnchangedFullSectionChildOrder

/-! Exact maintained child ranks for every source-ordered radix group. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullGroupChildSources

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullOrderedChildPositions
open AspisV5MerkleUnchangedFullGroupTraceLists
open AspisV5MerkleUnchangedFullGroupCursorPrefixes
open AspisV5MerkleUnchangedFullLevelTraceLists
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullGroupParentAlignment
open AspisV5MerkleUnchangedFullMaskCounts
open AspisV5MerkleUnchangedFullSectionChildOrder

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

def presentLevelOffset (tree : V5PrivateSection)
    (queries : Finset V5Query) (level parentOrdinal : Nat) : Nat :=
  (((orderedActiveIndices tree queries (level + 1)).map
    (fun parent =>
      (presentChildIndices tree queries level parent).length)).take
    parentOrdinal).sum

def absentLevelOffset (tree : V5PrivateSection)
    (queries : Finset V5Query) (level parentOrdinal : Nat) : Nat :=
  (((orderedActiveIndices tree queries (level + 1)).map
    (fun parent =>
      (absentChildIndices tree queries level parent).length)).take
    parentOrdinal).sum

/-- Exact source and maintained-list identity of all four children used by
one extracted Rust radix hash. -/
structure ExactAlignedGroupChildSources
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {generatedLevel : GeneratedDigestVec}
    (levelStartNodePos : Std.Usize)
    (group : RawGroupStepSummary sha256 nodeBytes generatedLevel)
    (ordinal : Nat)
    (alignment : ExactGroupParentAlignment tree queries level group ordinal) :
    Prop where
  live_source : ∀ slot : Fin 4,
    4 * alignment.parent + slot.val ∈ activeIndices tree queries level →
      group.witness.children[slot.val]! = generatedLevel.val[
        presentLevelOffset tree queries level ordinal +
          liveSlotCount
            (localChildSlots tree queries level alignment.parent) slot.val]!
  live_index : ∀ slot : Fin 4,
    4 * alignment.parent + slot.val ∈ activeIndices tree queries level →
      (levelPresentChildIndices tree queries level)[
        presentLevelOffset tree queries level ordinal +
          liveSlotCount
            (localChildSlots tree queries level alignment.parent) slot.val]? =
        some (4 * alignment.parent + slot.val)
  frontier_source : ∀ slot : Fin 4,
    4 * alignment.parent + slot.val ∉ activeIndices tree queries level →
      ∀ byte, byte < 32 →
        group.witness.children[slot.val]!.val[byte]! = nodeBytes.val[
          levelStartNodePos.val + 32 *
            (absentLevelOffset tree queries level ordinal +
              frontierSlotCount
                (localChildSlots tree queries level alignment.parent)
                slot.val) + byte]!
  frontier_index : ∀ slot : Fin 4,
    4 * alignment.parent + slot.val ∉ activeIndices tree queries level →
      (levelAbsentChildIndices tree queries level)[
        absentLevelOffset tree queries level ordinal +
          frontierSlotCount
            (localChildSlots tree queries level alignment.parent) slot.val]? =
        some (4 * alignment.parent + slot.val)
  parent_digest_exact :
    AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest group.digest =
      (sha256MerkleHashing sha256).radix4Node fun slot =>
        AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest
          group.witness.children[slot.val]!

/-- One aligned source group consumes exactly the maintained present and
absent child counts of its parent. -/
theorem aligned_group_counts
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {generatedLevel : GeneratedDigestVec}
    (group : RawGroupStepSummary sha256 nodeBytes generatedLevel)
    (ordinal : Nat)
    (alignment : ExactGroupParentAlignment tree queries level group ordinal) :
    liveBefore group.present 4 =
        (presentChildIndices tree queries level alignment.parent).length ∧
      frontierBefore group.present 4 =
        (absentChildIndices tree queries level alignment.parent).length := by
  have localSlots : alignment.slots =
      localChildSlots tree queries level alignment.parent := by
    simpa [localChildSlots] using alignment.slots_eq
  constructor
  · calc
      liveBefore group.present 4 = liveSlotCount alignment.slots 4 :=
        liveBefore_eq_liveSlotCount group.present alignment.slots
          alignment.mask_eq 4 (by omega)
      _ = liveSlotCount
          (localChildSlots tree queries level alignment.parent) 4 := by
        rw [localSlots]
      _ = (presentChildIndices tree queries level
          alignment.parent).length :=
        liveSlotCount_localChildSlots_eq_present_length tree queries level
          alignment.parent
  · calc
      frontierBefore group.present 4 =
          frontierSlotCount alignment.slots 4 :=
        frontierBefore_eq_frontierSlotCount group.present alignment.slots
          alignment.mask_eq 4 (by omega)
      _ = frontierSlotCount
          (localChildSlots tree queries level alignment.parent) 4 := by
        rw [localSlots]
      _ = (absentChildIndices tree queries level
          alignment.parent).length :=
        frontierSlotCount_localChildSlots_eq_absent_length tree queries level
          alignment.parent

/-- Source group totals, in source order, are exactly the maintained child
list lengths for the corresponding ordered parents. -/
theorem level_group_count_lists_exact
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    (summary : RawLevelStepSummary sha256 root nodeBytes topology binaryDepth)
    (fields : FullExactConstructedTopologyFields queries topology)
    (plan_eq : summary.planLevel.val = sectionRadixStart tree + level)
    (level_lt : level < radixLevelCount tree) :
    groupLiveCounts summary.groupSteps =
        (orderedActiveIndices tree queries (level + 1)).map
          (fun parent =>
            (presentChildIndices tree queries level parent).length) ∧
      groupFrontierCounts summary.groupSteps =
        (orderedActiveIndices tree queries (level + 1)).map
          (fun parent =>
            (absentChildIndices tree queries level parent).length) := by
  have lengthEq : summary.groupSteps.length =
      (orderedActiveIndices tree queries (level + 1)).length := by
    have masksLength := congrArg List.length summary.masks_exact
    have plan_lt : summary.planLevel.val < 8 := by
      rw [plan_eq]
      have end_eq := section_start_add_radix_count tree
      omega
    have masksPlan := level_summary_masks_follow_shared_plan queries summary
      fields plan_lt
    have planLength := congrArg List.length masksPlan
    have localMasks := sectionGroupMasks_eq_shared_suffix tree queries level
    have localLength := congrArg List.length localMasks
    simp only [groupMasks, List.length_map] at masksLength
    simp only [List.length_map] at planLength
    rw [plan_eq] at planLength
    have groupsLength : (sectionGroupMasks tree queries level).length =
        (orderedActiveIndices tree queries (level + 1)).length := by
      simp [sectionGroupMasks, sectionGroupSlots]
    omega
  constructor
  · apply List.ext_getElem
    · simpa [groupLiveCounts, lengthEq]
    · intro ordinal source_lt model_lt
      have step_lt : ordinal < summary.groupSteps.length := by
        simpa [groupLiveCounts] using source_lt
      have parent_lt : ordinal <
          (orderedActiveIndices tree queries (level + 1)).length := by
        rw [← lengthEq]
        exact step_lt
      let alignment := Classical.choice
        (level_group_yields_parent_alignment tree queries level summary fields
          plan_eq level_lt ordinal step_lt)
      have counts := aligned_group_counts tree queries level
        (summary.groupSteps.get ⟨ordinal, step_lt⟩) ordinal alignment
      simp only [groupLiveCounts, List.getElem_map]
      rw [← getElem!_pos (orderedActiveIndices tree queries (level + 1))
        ordinal parent_lt, ← alignment.parent_eq]
      exact counts.1
  · apply List.ext_getElem
    · simpa [groupFrontierCounts, lengthEq]
    · intro ordinal source_lt model_lt
      have step_lt : ordinal < summary.groupSteps.length := by
        simpa [groupFrontierCounts] using source_lt
      have parent_lt : ordinal <
          (orderedActiveIndices tree queries (level + 1)).length := by
        rw [← lengthEq]
        exact step_lt
      let alignment := Classical.choice
        (level_group_yields_parent_alignment tree queries level summary fields
          plan_eq level_lt ordinal step_lt)
      have counts := aligned_group_counts tree queries level
        (summary.groupSteps.get ⟨ordinal, step_lt⟩) ordinal alignment
      simp only [groupFrontierCounts, List.getElem_map]
      rw [← getElem!_pos (orderedActiveIndices tree queries (level + 1))
        ordinal parent_lt, ← alignment.parent_eq]
      exact counts.2

/-- The generated cursors at one group are the exact flattened-list offsets
of that group's maintained parent. -/
theorem level_group_start_cursors_exact
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    (summary : RawLevelStepSummary sha256 root nodeBytes topology binaryDepth)
    (fields : FullExactConstructedTopologyFields queries topology)
    (plan_eq : summary.planLevel.val = sectionRadixStart tree + level)
    (level_lt : level < radixLevelCount tree)
    (ordinal : Nat) (ordinal_lt : ordinal < summary.groupSteps.length) :
    summary.groupSteps[ordinal].startValuePos.val =
        (((orderedActiveIndices tree queries (level + 1)).map
          (fun parent =>
            (presentChildIndices tree queries level parent).length)).take
          ordinal).sum ∧
      summary.groupSteps[ordinal].startNodePos.val =
        summary.startNodePos.val + 32 *
          (((orderedActiveIndices tree queries (level + 1)).map
            (fun parent =>
              (absentChildIndices tree queries level parent).length)).take
            ordinal).sum := by
  have cursors :=
    AspisV5MerkleUnchangedFullGroupCursorPrefixes.OrderedGroupStepChain.cursor_prefixes
      summary.group_view.chain ordinal ordinal_lt
  have counts := level_group_count_lists_exact tree queries level summary
    fields plan_eq level_lt
  rcases cursors with ⟨liveCursor, frontierCursor⟩
  rw [counts.1] at liveCursor
  rw [counts.2] at frontierCursor
  constructor
  · simpa using liveCursor
  · exact frontierCursor

/-- Every generated child read in one aligned source group has both its exact
Rust source and its exact maintained live/frontier ordinal. -/
theorem level_group_yields_exact_child_sources
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    (summary : RawLevelStepSummary sha256 root nodeBytes topology binaryDepth)
    (fields : FullExactConstructedTopologyFields queries topology)
    (plan_eq : summary.planLevel.val = sectionRadixStart tree + level)
    (level_lt : level < radixLevelCount tree)
    (ordinal : Nat) (ordinal_lt : ordinal < summary.groupSteps.length) :
    ∃ alignment : ExactGroupParentAlignment tree queries level
        summary.groupSteps[ordinal] ordinal,
      ExactAlignedGroupChildSources tree queries level summary.startNodePos
        summary.groupSteps[ordinal] ordinal alignment := by
  let alignment := Classical.choice
    (level_group_yields_parent_alignment tree queries level summary fields
      plan_eq level_lt ordinal ordinal_lt)
  have countLists := level_group_count_lists_exact tree queries level summary
    fields plan_eq level_lt
  have parentLength : summary.groupSteps.length =
      (orderedActiveIndices tree queries (level + 1)).length := by
    have lengths := congrArg List.length countLists.1
    simpa [groupLiveCounts] using lengths
  have parent_lt : ordinal <
      (orderedActiveIndices tree queries (level + 1)).length := by
    rw [← parentLength]
    exact ordinal_lt
  have parentEqGet :
      (orderedActiveIndices tree queries (level + 1)).get
        ⟨ordinal, parent_lt⟩ = alignment.parent := by
    have parentBang := alignment.parent_eq.symm
    rw [getElem!_pos (orderedActiveIndices tree queries (level + 1))
      ordinal parent_lt] at parentBang
    simpa only [List.get_eq_getElem] using parentBang
  have localSlots : alignment.slots =
      localChildSlots tree queries level alignment.parent := by
    simpa [localChildSlots] using alignment.slots_eq
  have starts := level_group_start_cursors_exact tree queries level summary
    fields plan_eq level_lt ordinal ordinal_lt
  have positions := summary_child_positions_are_exact
    summary.groupSteps[ordinal]
  refine ⟨alignment, {
    live_source := ?_
    live_index := ?_
    frontier_source := ?_
    frontier_index := ?_
    parent_digest_exact := ?_ }⟩
  · intro slot slot_mem
    have generatedPresent : ChildPresent
        summary.groupSteps[ordinal].present slot.val :=
      (alignment.child_present_iff slot).mpr slot_mem
    have rankEq : liveBefore summary.groupSteps[ordinal].present slot.val =
        liveSlotCount
          (localChildSlots tree queries level alignment.parent) slot.val := by
      calc
        liveBefore summary.groupSteps[ordinal].present slot.val =
            liveSlotCount alignment.slots slot.val :=
          liveBefore_eq_liveSlotCount summary.groupSteps[ordinal].present
            alignment.slots alignment.mask_eq slot.val (by omega)
        _ = liveSlotCount
            (localChildSlots tree queries level alignment.parent) slot.val := by
          rw [localSlots]
    have source := positions.live_source slot.val slot.isLt generatedPresent
    rw [starts.1, rankEq] at source
    simpa [presentLevelOffset] using source
  · intro slot slot_mem
    simpa [presentLevelOffset] using
      present_child_level_rank tree queries level ordinal alignment.parent
        slot.val parent_lt parentEqGet slot.isLt slot_mem
  · intro slot slot_absent byte byte_lt
    have generatedAbsent : ¬ ChildPresent
        summary.groupSteps[ordinal].present slot.val := fun present =>
      slot_absent ((alignment.child_present_iff slot).mp present)
    have rankEq :
        frontierBefore summary.groupSteps[ordinal].present slot.val =
          frontierSlotCount
            (localChildSlots tree queries level alignment.parent) slot.val := by
      calc
        frontierBefore summary.groupSteps[ordinal].present slot.val =
            frontierSlotCount alignment.slots slot.val :=
          frontierBefore_eq_frontierSlotCount
            summary.groupSteps[ordinal].present alignment.slots
            alignment.mask_eq slot.val (by omega)
        _ = frontierSlotCount
            (localChildSlots tree queries level alignment.parent) slot.val := by
          rw [localSlots]
    have source := positions.frontier_source slot.val slot.isLt
      generatedAbsent byte byte_lt
    rw [starts.2, rankEq] at source
    simpa [absentLevelOffset, Nat.mul_add, Nat.add_assoc] using source
  · intro slot slot_absent
    simpa [absentLevelOffset] using
      absent_child_level_frontier_rank tree queries level ordinal
        alignment.parent slot.val parent_lt parentEqGet slot.isLt slot_absent
  · simpa [RawGroupStepSummary.digest,
      AspisV5MerkleUnchangedFullRadixSoundness.childrenOfFour] using
      summary.groupSteps[ordinal].witness.digest_exact

#print axioms aligned_group_counts
#print axioms level_group_count_lists_exact
#print axioms level_group_start_cursors_exact
#print axioms level_group_yields_exact_child_sources

end AspisV5MerkleUnchangedFullGroupChildSources
