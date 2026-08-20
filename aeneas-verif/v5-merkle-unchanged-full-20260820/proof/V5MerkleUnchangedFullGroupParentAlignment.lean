import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullMaskSemantics
import V5MerkleUnchangedFullLevelTraceLists
import V5MerkleUnchangedFullSectionTopologyAlignment

/-! Match each generated group summary with its maintained parent index. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullGroupParentAlignment

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullGroupTraceLists
open AspisV5MerkleUnchangedFullMaskSemantics
open AspisV5MerkleUnchangedFullLevelTraceLists
open AspisV5MerkleUnchangedFullSectionTopologyAlignment

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- Exact maintained interpretation of one source-ordered group step. -/
structure ExactGroupParentAlignment
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {generatedLevel : GeneratedDigestVec}
    (group : RawGroupStepSummary sha256 nodeBytes generatedLevel)
    (ordinal : Nat) : Type where
  parent : Nat
  slots : Finset (Fin 4)
  parent_eq : parent =
    (orderedActiveIndices tree queries (level + 1))[ordinal]!
  parent_mem : parent ∈ orderedActiveIndices tree queries (level + 1)
  slots_eq : slots = Finset.univ.filter fun slot =>
    4 * parent + slot.val ∈ activeIndices tree queries level
  mask_eq : group.present.val = slotMask slots
  child_present_iff : ∀ slot : Fin 4,
    AspisV5MerkleUnchangedFullOrderedChildPositions.ChildPresent
        group.present slot.val ↔
      4 * parent + slot.val ∈ activeIndices tree queries level

/-- The `ordinal`th exact Rust group is the `ordinal`th maintained parent;
its byte mask and all four bit tests have the exact model meaning. -/
theorem level_group_yields_parent_alignment
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
    Nonempty (ExactGroupParentAlignment tree queries level
      summary.groupSteps[ordinal] ordinal) := by
  have plan_lt : summary.planLevel.val < 8 := by
    rw [plan_eq]
    have end_eq := section_start_add_radix_count tree
    omega
  have masksPlan := level_summary_masks_follow_shared_plan queries summary
    fields plan_lt
  have stepsMasksLength : summary.groupSteps.length = summary.masks.val.length := by
    have lengths := congrArg List.length summary.masks_exact
    simpa [groupMasks] using lengths
  have mask_lt : ordinal < summary.masks.val.length := by omega
  have planMasksLength : summary.masks.val.length =
      (sharedGroupMasks queries summary.planLevel.val).length := by
    simpa using congrArg List.length masksPlan
  have shared_lt : ordinal <
      (sharedGroupMasks queries summary.planLevel.val).length := by omega
  have localMasksEq : sectionGroupMasks tree queries level =
      sharedGroupMasks queries summary.planLevel.val := by
    rw [plan_eq, sectionGroupMasks_eq_shared_suffix]
  have localMask_lt : ordinal < (sectionGroupMasks tree queries level).length := by
    rw [localMasksEq]
    exact shared_lt
  have groupMaskEq : summary.groupSteps[ordinal].present =
      summary.masks.val[ordinal] := by
    have points := congrArg (fun values => values[ordinal]!) summary.masks_exact
    simpa [groupMasks, ordinal_lt, mask_lt] using points
  have maskPlanEq : summary.masks.val[ordinal].val =
      (sharedGroupMasks queries summary.planLevel.val)[ordinal] := by
    have points := congrArg (fun values => values[ordinal]!) masksPlan
    simpa [mask_lt, shared_lt] using points
  have localMaskEq :
      (sectionGroupMasks tree queries level)[ordinal] =
        (sharedGroupMasks queries summary.planLevel.val)[ordinal] := by
    exact List.getElem_of_eq localMasksEq localMask_lt
  have slotsLength : (sectionGroupSlots tree queries level).length =
      (sectionGroupMasks tree queries level).length := by
    simp [sectionGroupMasks]
  have slot_lt : ordinal < (sectionGroupSlots tree queries level).length := by
    rw [slotsLength]
    exact localMask_lt
  let parents := orderedActiveIndices tree queries (level + 1)
  have parentsLength : parents.length =
      (sectionGroupSlots tree queries level).length := by
    simp [parents, sectionGroupSlots]
  have parent_lt : ordinal < parents.length := by omega
  let parent := parents[ordinal]
  let slots := (sectionGroupSlots tree queries level)[ordinal]
  have slotsAt : slots = Finset.univ.filter fun slot =>
      4 * parent + slot.val ∈ activeIndices tree queries level := by
    simp [slots, sectionGroupSlots, parents, parent, parent_lt]
  have maskAt : summary.groupSteps[ordinal].present.val = slotMask slots := by
    rw [groupMaskEq, maskPlanEq, ← localMaskEq]
    simp [sectionGroupMasks, slots, slot_lt]
  refine ⟨{
    parent := parent
    slots := slots
    parent_eq := by simp [parent, parents, parent_lt]
    parent_mem := by
      exact List.getElem_mem parent_lt
    slots_eq := slotsAt
    mask_eq := maskAt
    child_present_iff := ?_ }⟩
  intro slot
  have bit := childPresent_iff_mem_slots
    summary.groupSteps[ordinal].present slots maskAt slot
  rw [slotsAt] at bit
  simpa using bit

#print axioms level_group_yields_parent_alignment

end AspisV5MerkleUnchangedFullGroupParentAlignment
