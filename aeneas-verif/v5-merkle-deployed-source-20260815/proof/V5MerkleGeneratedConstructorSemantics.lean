import V5MerkleGeneratedConstructorBridge
import V5MerkleGeneratedTopologyBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedConstructorSemantics

open V5MerkleDeployedSource
open AspisV5MerkleTopologyConstructorModel
open AspisV5MerkleGeneratedConstructorBridge
open AspisV5MerkleGeneratedTopologyBridge
open AspisV5TopologyConstruction

private theorem clone_u32_slice_eq (slice : Slice Std.U32) :
    Slice.clone core.clone.CloneU32.clone slice = .ok slice := by
  obtain ⟨cloned, hrun, heq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.clone_spec (clone := core.clone.CloneU32.clone)
      (s := slice) (by simp))
  subst cloned
  exact hrun

private theorem clone_u8_slice_eq (slice : Slice Std.U8) :
    Slice.clone core.clone.CloneU8.clone slice = .ok slice := by
  obtain ⟨cloned, hrun, heq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.clone_spec (clone := core.clone.CloneU8.clone)
      (s := slice) (by simp))
  subst cloned
  exact hrun

private theorem u32_slice_to_vec_value
    (slice : Slice Std.U32) (out : alloc.vec.Vec Std.U32)
    (hrun : alloc.slice.Slice.to_vec core.clone.CloneU32 slice = .ok out) :
    out.val = slice.val := by
  unfold alloc.slice.Slice.to_vec at hrun
  rw [clone_u32_slice_eq] at hrun
  exact congrArg (fun value : Slice Std.U32 => value.val)
    (Result.ok.inj hrun).symm

private theorem u32_extend_value
    (base : alloc.vec.Vec Std.U32) (suffix : Slice Std.U32)
    (out : alloc.vec.Vec Std.U32)
    (hrun : alloc.vec.Vec.extend_from_slice core.clone.CloneU32
      base suffix = .ok out) :
    out.val = base.val ++ suffix.val := by
  unfold alloc.vec.Vec.extend_from_slice at hrun
  split at hrun
  · split at hrun
    · rename_i cloned hclone
      have hsame : cloned = suffix := by
        obtain ⟨witness, hwitness, heq⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Slice.clone_spec (clone := core.clone.CloneU32.clone)
              (s := suffix) (by simp))
        have : witness = cloned := Result.ok.inj (hwitness.symm.trans hclone)
        exact this ▸ heq.symm
      subst cloned
      exact congrArg (fun value : alloc.vec.Vec Std.U32 => value.val)
        (Result.ok.inj hrun).symm
    · simp at hrun
    · simp at hrun
  · simp at hrun

private theorem u8_extend_value
    (base : alloc.vec.Vec Std.U8) (suffix : Slice Std.U8)
    (out : alloc.vec.Vec Std.U8)
    (hrun : alloc.vec.Vec.extend_from_slice core.clone.CloneU8
      base suffix = .ok out) :
    out.val = base.val ++ suffix.val := by
  unfold alloc.vec.Vec.extend_from_slice at hrun
  split at hrun
  · split at hrun
    · rename_i cloned hclone
      have hsame : cloned = suffix := by
        obtain ⟨witness, hwitness, heq⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Slice.clone_spec (clone := core.clone.CloneU8.clone)
              (s := suffix) (by simp))
        have : witness = cloned := Result.ok.inj (hwitness.symm.trans hclone)
        exact this ▸ heq.symm
      subst cloned
      exact congrArg (fun value : alloc.vec.Vec Std.U8 => value.val)
        (Result.ok.inj hrun).symm
    · simp at hrun
    · simp at hrun
  · simp at hrun

private theorem map_slice (values : List α) (start finish : Nat)
    (f : α → β) :
    (List.slice start finish values).map f =
      List.slice start finish (values.map f) := by
  simp [List.slice]

private theorem vec_range_success_value
    (values : alloc.vec.Vec α) (start finish : Std.Usize)
    (slice : Slice α)
    (hrun : alloc.vec.Vec.index
      (core.slice.index.SliceIndexRangeUsizeSlice α)
      values { start := start, «end» := finish } = .ok slice) :
    slice.val = List.slice start.val finish.val values.val := by
  simp [alloc.vec.Vec.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index] at hrun
  split at hrun
  · have heq := Result.ok.inj hrun
    exact (congrArg (fun output : Slice α => output.val) heq).symm
  · simp at hrun

private theorem usize_succ_val_below_nine
    (level : Std.Usize) (hlevel : level.val < 9) :
    (Std.Usize.wrapping_add level 1#usize).val = level.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone]
  apply Nat.mod_eq_of_lt
  have hsize : 11 < UScalar.size .Usize := by
    rw [UScalar.size_def, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      rw [hbits] <;> norm_num
  omega

private theorem array_update_success_eq
    {n : Std.Usize} (values : Array α n) (index : Std.Usize)
    (value : α) (out : Array α n) (hbound : index.val < values.length)
    (hrun : Array.update values index value = .ok out) :
    out = Aeneas.Std.Array.set values index value := by
  have hspec := Array.update_spec values index value hbound
  obtain ⟨witness, hwitness, heq⟩ :=
    Aeneas.Std.WP.spec_imp_exists hspec
  have : witness = out := Result.ok.inj (hwitness.symm.trans hrun)
  simpa [this] using heq

private theorem array_index_success_getElem!
    {n : Std.Usize} [Inhabited α] (values : Array α n)
    (index : Std.Usize) (value : α) (hbound : index.val < values.length)
    (hrun : Array.index_usize values index = .ok value) :
    value = values.val[index.val]! := by
  obtain ⟨witness, hwitness, heq⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec values index hbound)
  have : witness = value := Result.ok.inj (hwitness.symm.trans hrun)
  calc
    value = witness := this.symm
    _ = values.val[index.val] := heq
    _ = values.val[index.val]! := by
      have hopt : values.val[index.val]? =
          some values.val[index.val] := by simp
      exact (List.getElem!_of_getElem? hopt).symm

/-- The remaining source fact about one parent scan, stated independently of
the outer constructor recursion. -/
def GeneratedParentLevelSourceEquality : Prop :=
  ∀ (input : Slice Std.U32)
      (nextIndices : alloc.vec.Vec Std.U32)
      (nextMasks : alloc.vec.Vec Std.U8),
    merkle.topology_parent_level input = .ok (nextIndices, nextMasks) →
      nextIndices.val.map (fun index => index.val) =
          parentIndicesOf (input.val.map fun index => index.val) ∧
        nextMasks.val.map (fun mask => mask.val) =
          parentMasksOf (input.val.map fun index => index.val)

/-- Value-level meaning of one recursive-builder entry. Array offsets are
proved separately because they are writes, not inputs to the parent scan. -/
structure GeneratedBuildValueState
    (initialIndices : List Nat)
    (level currentStart currentEnd : Std.Usize)
    (levelIndices : GeneratedIndexVec)
    (groupMasks : GeneratedMaskVec) : Prop where
  level_lt_nine : level.val < 9
  current_start :
    currentStart.val = (levelPrefix initialIndices level.val).length
  current_end :
    currentEnd.val =
      (levelPrefix initialIndices (level.val + 1)).length
  level_values :
    levelIndices.val.map (fun index => index.val) =
      levelPrefix initialIndices (level.val + 1)
  mask_values :
    groupMasks.val.map (fun mask => mask.val) =
      maskPrefix initialIndices level.val

/-- Prefix offsets already written when the recursive builder enters a
level. The next level offset is written by the step; the current group offset
is written immediately before reading that group. -/
structure GeneratedBuildOffsetState
    (initialIndices : List Nat) (level : Std.Usize)
    (levelOffsets : GeneratedLevelOffsets)
    (groupOffsets : GeneratedGroupOffsets) : Prop where
  level_offsets : ∀ index, index ≤ level.val →
    (levelOffsets.val[index]!).val =
      (levelPrefix initialIndices index).length
  group_offsets : ∀ index, index < level.val →
    (groupOffsets.val[index]!).val =
      (maskPrefix initialIndices index).length

theorem generated_build_step_preserves_values
    (hparent : GeneratedParentLevelSourceEquality)
    (initialIndices : List Nat)
    (radixLevels level currentStart currentEnd : Std.Usize)
    (levelIndices : GeneratedIndexVec)
    (levelOffsets : GeneratedLevelOffsets)
    (groupMasks : GeneratedMaskVec)
    (groupOffsets : GeneratedGroupOffsets)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets)
    (head : GeneratedBuildStep radixLevels level currentStart currentEnd
      levelIndices levelOffsets groupMasks groupOffsets
      finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets)
    (hradix : radixLevels.val ≤ 8)
    (hactive : level.val < radixLevels.val)
    (hstate : GeneratedBuildValueState initialIndices level currentStart
      currentEnd levelIndices groupMasks) :
    GeneratedBuildValueState initialIndices head.nextLevel currentEnd
      head.nextEnd head.levelIndices' head.groupMasks' := by
  have hsliceValue := vec_range_success_value levelIndices currentStart
    currentEnd head.currentSlice head.current_slice_run
  have hcurrentValue := u32_slice_to_vec_value head.currentSlice
    head.currentIndices head.current_indices_run
  have hsliceMapped :
      head.currentIndices.val.map (fun index => index.val) =
        parentLevelFrom initialIndices level.val := by
    rw [hcurrentValue, hsliceValue, map_slice, hstate.level_values,
      hstate.current_start, hstate.current_end, levelPrefix_succ]
    simp [List.slice, List.length_append]
  obtain ⟨hnextIndices, hnextMasks⟩ :=
    hparent (alloc.vec.Vec.deref head.currentIndices) head.nextIndices
      head.nextMasks head.parent_run
  have hnextIndices' :
      head.nextIndices.val.map (fun index => index.val) =
        parentLevelFrom initialIndices (level.val + 1) := by
    rw [hnextIndices, alloc.vec.Vec.deref]
    change parentIndicesOf
      (head.currentIndices.val.map fun index => index.val) = _
    rw [hsliceMapped]
    rfl
  have hnextMasks' :
      head.nextMasks.val.map (fun mask => mask.val) =
        parentMaskLevelFrom initialIndices level.val := by
    rw [hnextMasks, alloc.vec.Vec.deref]
    change parentMasksOf
      (head.currentIndices.val.map fun index => index.val) = _
    rw [hsliceMapped]
    rfl
  have hlevelAppend := u32_extend_value levelIndices
    (alloc.vec.Vec.deref head.nextIndices) head.levelIndices'
    head.indices_append_run
  have hmaskAppend := u8_extend_value groupMasks
    (alloc.vec.Vec.deref head.nextMasks) head.groupMasks'
    head.masks_append_run
  have hnextLevel : head.nextLevel.val = level.val + 1 := by
    rw [head.next_level_eq]
    exact usize_succ_val_below_nine level hstate.level_lt_nine
  refine {
    level_lt_nine := by omega
    current_start := by
      rw [hnextLevel]
      exact hstate.current_end
    current_end := by
      rw [head.next_end_eq, alloc.vec.Vec.len_val]
      change head.levelIndices'.val.length = _
      rw [← List.length_map (fun index => index.val),
        hlevelAppend, List.map_append,
        List.length_append, hstate.level_values,
        alloc.vec.Vec.deref, hnextIndices', hnextLevel]
      simp [levelPrefix_succ, List.length_append, Nat.add_assoc]
    level_values := by
      rw [hlevelAppend, List.map_append, hstate.level_values,
        alloc.vec.Vec.deref, hnextIndices', hnextLevel]
      simp [levelPrefix_succ, List.append_assoc]
    mask_values := by
      rw [hmaskAppend, List.map_append, hstate.mask_values,
        alloc.vec.Vec.deref, hnextMasks', hnextLevel,
        maskPrefix_succ]
  }

theorem generated_build_step_preserves_offsets
    (initialIndices : List Nat)
    (radixLevels level currentStart currentEnd : Std.Usize)
    (levelIndices : GeneratedIndexVec)
    (levelOffsets : GeneratedLevelOffsets)
    (groupMasks : GeneratedMaskVec)
    (groupOffsets : GeneratedGroupOffsets)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets)
    (head : GeneratedBuildStep radixLevels level currentStart currentEnd
      levelIndices levelOffsets groupMasks groupOffsets
      finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets)
    (hradix : radixLevels.val ≤ 8)
    (hactive : level.val < radixLevels.val)
    (hvalues : GeneratedBuildValueState initialIndices level currentStart
      currentEnd levelIndices groupMasks)
    (hoffsets : GeneratedBuildOffsetState initialIndices level levelOffsets
      groupOffsets) :
    GeneratedBuildOffsetState initialIndices head.nextLevel
      head.levelOffsets' head.groupOffsets' := by
  have hnextLevel : head.nextLevel.val = level.val + 1 := by
    rw [head.next_level_eq]
    exact usize_succ_val_below_nine level hvalues.level_lt_nine
  have hgroupBound : level.val < groupOffsets.length := by
    scalar_tac
  have hlevelBound : head.nextLevel.val < levelOffsets.length := by
    scalar_tac
  have hgroupSet : head.groupOffsets' =
      Aeneas.Std.Array.set groupOffsets level head.groupStart :=
    array_update_success_eq groupOffsets level head.groupStart
      head.groupOffsets' hgroupBound head.group_offset_run
  have hlevelSet : head.levelOffsets' =
      Aeneas.Std.Array.set levelOffsets head.nextLevel currentEnd :=
    array_update_success_eq levelOffsets head.nextLevel currentEnd
      head.levelOffsets' hlevelBound head.level_offset_run
  have hgroupStart : head.groupStart.val =
      (maskPrefix initialIndices level.val).length := by
    rw [head.group_start_eq, alloc.vec.Vec.len_val]
    change groupMasks.val.length = _
    rw [← List.length_map (fun mask => mask.val), hvalues.mask_values]
  refine {
    level_offsets := ?_
    group_offsets := ?_
  }
  · intro index hindex
    rw [hnextLevel] at hindex
    by_cases heq : index = level.val + 1
    · subst index
      rw [hlevelSet, Aeneas.Std.Array.set_val_eq]
      have hwithin : level.val + 1 < levelOffsets.val.length := by
        scalar_tac
      rw [List.set_getElem!_eq levelOffsets.val head.nextLevel.val
        (level.val + 1) currentEnd (by constructor <;> scalar_tac)]
      rw [hvalues.current_end]
    · have hold : index ≤ level.val := by omega
      rw [hlevelSet, Aeneas.Std.Array.set_val_eq,
        List.set_getElem!_ne levelOffsets.val head.nextLevel.val index
          currentEnd (Or.inl (by simpa [hnextLevel] using Ne.symm heq))]
      exact hoffsets.level_offsets index hold
  · intro index hindex
    rw [hnextLevel] at hindex
    by_cases heq : index = level.val
    · subst index
      rw [hgroupSet, Aeneas.Std.Array.set_val_eq]
      have hwithin : level.val < groupOffsets.val.length := by scalar_tac
      rw [List.set_getElem!_eq groupOffsets.val level.val level.val
        head.groupStart ⟨hwithin, rfl⟩, hgroupStart]
    · have hold : index < level.val := by omega
      rw [hgroupSet, Aeneas.Std.Array.set_val_eq,
        List.set_getElem!_ne groupOffsets.val level.val index
          head.groupStart (Or.inl (Ne.symm heq))]
      exact hoffsets.group_offsets index hold

theorem generated_build_trace_final_values
    (hparent : GeneratedParentLevelSourceEquality)
    (initialIndices : List Nat)
    (radixLevels level currentStart currentEnd : Std.Usize)
    (levelIndices : GeneratedIndexVec)
    (levelOffsets : GeneratedLevelOffsets)
    (groupMasks : GeneratedMaskVec)
    (groupOffsets : GeneratedGroupOffsets)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets)
    (htrace : GeneratedBuildTrace radixLevels level currentStart currentEnd
      levelIndices levelOffsets groupMasks groupOffsets
      finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets)
    (hradix : radixLevels.val ≤ 8)
    (hlevel : level.val ≤ radixLevels.val)
    (hstate : GeneratedBuildValueState initialIndices level currentStart
      currentEnd levelIndices groupMasks) :
    finalLevelIndices.val.map (fun index => index.val) =
        levelPrefix initialIndices (radixLevels.val + 1) ∧
      finalGroupMasks.val.map (fun mask => mask.val) =
        maskPrefix initialIndices radixLevels.val := by
  induction htrace with
  | done level currentStart currentEnd levelIndices levelOffsets groupMasks
      groupOffsets nextLevel levelOffsets' groupOffsets' hdone
      next_level_eq level_offset_run group_offset_run =>
      have heq : level.val = radixLevels.val := by omega
      constructor
      · simpa [heq] using hstate.level_values
      · simpa [heq] using hstate.mask_values
  | step level currentStart currentEnd levelIndices levelOffsets groupMasks
      groupOffsets finalLevelIndices finalLevelOffsets finalGroupMasks
      finalGroupOffsets hactive head tail ih =>
      have hnextState := generated_build_step_preserves_values hparent
        initialIndices radixLevels level currentStart currentEnd levelIndices
        levelOffsets groupMasks groupOffsets finalLevelIndices
        finalLevelOffsets finalGroupMasks finalGroupOffsets head hradix
        hactive hstate
      have hnextLevel : head.nextLevel.val = level.val + 1 := by
        rw [head.next_level_eq]
        exact usize_succ_val_below_nine level hstate.level_lt_nine
      exact ih (by omega) hnextState

structure GeneratedFinalOffsetState
    (initialIndices : List Nat) (radixLevels : Std.Usize)
    (levelOffsets : GeneratedLevelOffsets)
    (groupOffsets : GeneratedGroupOffsets) : Prop where
  level_offsets : ∀ index, index ≤ radixLevels.val + 1 →
    (levelOffsets.val[index]!).val =
      (levelPrefix initialIndices index).length
  group_offsets : ∀ index, index ≤ radixLevels.val →
    (groupOffsets.val[index]!).val =
      (maskPrefix initialIndices index).length

theorem generated_build_trace_final_offsets
    (hparent : GeneratedParentLevelSourceEquality)
    (initialIndices : List Nat)
    (radixLevels level currentStart currentEnd : Std.Usize)
    (levelIndices : GeneratedIndexVec)
    (levelOffsets : GeneratedLevelOffsets)
    (groupMasks : GeneratedMaskVec)
    (groupOffsets : GeneratedGroupOffsets)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets)
    (htrace : GeneratedBuildTrace radixLevels level currentStart currentEnd
      levelIndices levelOffsets groupMasks groupOffsets
      finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets)
    (hradix : radixLevels.val ≤ 8)
    (hlevel : level.val ≤ radixLevels.val)
    (hvalues : GeneratedBuildValueState initialIndices level currentStart
      currentEnd levelIndices groupMasks)
    (hoffsets : GeneratedBuildOffsetState initialIndices level levelOffsets
      groupOffsets) :
    GeneratedFinalOffsetState initialIndices radixLevels finalLevelOffsets
      finalGroupOffsets := by
  induction htrace with
  | done level currentStart currentEnd levelIndices levelOffsets groupMasks
      groupOffsets nextLevel levelOffsets' groupOffsets' hdone
      next_level_eq level_offset_run group_offset_run =>
      have heq : level.val = radixLevels.val := by omega
      have hnext : nextLevel.val = radixLevels.val + 1 := by
        rw [next_level_eq]
        exact usize_succ_val_below_nine radixLevels (by omega)
      have hlevelBound : nextLevel.val < levelOffsets.length := by scalar_tac
      have hgroupBound : radixLevels.val < groupOffsets.length := by scalar_tac
      have hlevelSet : levelOffsets' =
          Aeneas.Std.Array.set levelOffsets nextLevel currentEnd :=
        array_update_success_eq levelOffsets nextLevel currentEnd levelOffsets'
          hlevelBound level_offset_run
      have hgroupSet : groupOffsets' =
          Aeneas.Std.Array.set groupOffsets radixLevels
            (alloc.vec.Vec.len groupMasks) :=
        array_update_success_eq groupOffsets radixLevels
          (alloc.vec.Vec.len groupMasks) groupOffsets' hgroupBound
          group_offset_run
      have hmaskEnd : (alloc.vec.Vec.len groupMasks).val =
          (maskPrefix initialIndices radixLevels.val).length := by
        rw [alloc.vec.Vec.len_val]
        change groupMasks.val.length = _
        rw [← List.length_map (fun mask => mask.val), hvalues.mask_values,
          heq]
      refine {
        level_offsets := ?_
        group_offsets := ?_
      }
      · intro index hindex
        by_cases hlast : index = radixLevels.val + 1
        · subst index
          rw [hlevelSet, Aeneas.Std.Array.set_val_eq]
          rw [List.set_getElem!_eq levelOffsets.val nextLevel.val
            (radixLevels.val + 1) currentEnd (by constructor <;> scalar_tac)]
          rw [hvalues.current_end, heq]
        · have hold : index ≤ level.val := by omega
          rw [hlevelSet, Aeneas.Std.Array.set_val_eq,
            List.set_getElem!_ne levelOffsets.val nextLevel.val index
              currentEnd (Or.inl (by simpa [hnext] using Ne.symm hlast))]
          exact hoffsets.level_offsets index hold
      · intro index hindex
        by_cases hlast : index = radixLevels.val
        · subst index
          rw [hgroupSet, Aeneas.Std.Array.set_val_eq]
          rw [List.set_getElem!_eq groupOffsets.val radixLevels.val
            radixLevels.val (alloc.vec.Vec.len groupMasks)
            (by constructor <;> scalar_tac), hmaskEnd]
        · have hold : index < level.val := by omega
          rw [hgroupSet, Aeneas.Std.Array.set_val_eq,
            List.set_getElem!_ne groupOffsets.val radixLevels.val index
              (alloc.vec.Vec.len groupMasks) (Or.inl (Ne.symm hlast))]
          exact hoffsets.group_offsets index hold
  | step level currentStart currentEnd levelIndices levelOffsets groupMasks
      groupOffsets finalLevelIndices finalLevelOffsets finalGroupMasks
      finalGroupOffsets hactive head tail ih =>
      have hnextValues := generated_build_step_preserves_values
        hparent initialIndices radixLevels level currentStart currentEnd levelIndices
        levelOffsets groupMasks groupOffsets finalLevelIndices
        finalLevelOffsets finalGroupMasks finalGroupOffsets head hradix
        hactive hvalues
      have hnextOffsets := generated_build_step_preserves_offsets
        initialIndices radixLevels level currentStart currentEnd levelIndices
        levelOffsets groupMasks groupOffsets finalLevelIndices
        finalLevelOffsets finalGroupMasks finalGroupOffsets head hradix
        hactive hvalues hoffsets
      have hnextLevel : head.nextLevel.val = level.val + 1 := by
        rw [head.next_level_eq]
        exact usize_succ_val_below_nine level hvalues.level_lt_nine
      exact ih (by omega) hnextValues hnextOffsets

theorem released_builder_success_values
    (hparent : GeneratedParentLevelSourceEquality)
    (input : GeneratedIndexVec)
    (levelOffsets : GeneratedLevelOffsets)
    (groupOffsets : GeneratedGroupOffsets)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets)
    (hrun : merkle.build_topology_levels 8#usize 0#usize 0#usize
      (alloc.vec.Vec.len input) input levelOffsets (alloc.vec.Vec.new Std.U8)
      groupOffsets = .ok (finalLevelIndices, finalLevelOffsets,
        finalGroupMasks, finalGroupOffsets)) :
    finalLevelIndices.val.map (fun index => index.val) =
        levelPrefix (input.val.map fun index => index.val) 9 ∧
      finalGroupMasks.val.map (fun mask => mask.val) =
        maskPrefix (input.val.map fun index => index.val) 8 := by
  let initialIndices := input.val.map fun index => index.val
  let trace := Classical.choice
    (build_topology_levels_success_yields_trace 8#usize 0#usize 0#usize
      (alloc.vec.Vec.len input) input levelOffsets (alloc.vec.Vec.new Std.U8)
      groupOffsets finalLevelIndices finalLevelOffsets finalGroupMasks
      finalGroupOffsets hrun)
  have hstate : GeneratedBuildValueState initialIndices 0#usize 0#usize
      (alloc.vec.Vec.len input) input (alloc.vec.Vec.new Std.U8) := by
    refine {
      level_lt_nine := by norm_num
      current_start := by simp [initialIndices]
      current_end := by
        rw [alloc.vec.Vec.len_val]
        simp [initialIndices, levelPrefix_succ, parentLevelFrom]
      level_values := by
        simp [initialIndices, levelPrefix_succ, parentLevelFrom]
      mask_values := by simp [initialIndices]
    }
  have hfinal := generated_build_trace_final_values hparent initialIndices
    8#usize 0#usize 0#usize (alloc.vec.Vec.len input) input levelOffsets
    (alloc.vec.Vec.new Std.U8) groupOffsets finalLevelIndices
    finalLevelOffsets finalGroupMasks finalGroupOffsets trace (by norm_num)
    (by norm_num) hstate
  simpa [initialIndices] using hfinal

theorem released_builder_success_semantics
    (hparent : GeneratedParentLevelSourceEquality)
    (input : GeneratedIndexVec)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets)
    (hrun : merkle.build_topology_levels 8#usize 0#usize 0#usize
      (alloc.vec.Vec.len input) input
      (Array.repeat 17#usize 0#usize) (alloc.vec.Vec.new Std.U8)
      (Array.repeat 16#usize 0#usize) =
        .ok (finalLevelIndices, finalLevelOffsets,
          finalGroupMasks, finalGroupOffsets)) :
    (finalLevelIndices.val.map (fun index => index.val) =
        levelPrefix (input.val.map fun index => index.val) 9 ∧
      finalGroupMasks.val.map (fun mask => mask.val) =
        maskPrefix (input.val.map fun index => index.val) 8) ∧
      GeneratedFinalOffsetState (input.val.map fun index => index.val)
        8#usize finalLevelOffsets finalGroupOffsets := by
  let initialIndices := input.val.map fun index => index.val
  let trace := Classical.choice
    (build_topology_levels_success_yields_trace 8#usize 0#usize 0#usize
      (alloc.vec.Vec.len input) input (Array.repeat 17#usize 0#usize)
      (alloc.vec.Vec.new Std.U8) (Array.repeat 16#usize 0#usize)
      finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets
      hrun)
  have hvalues : GeneratedBuildValueState initialIndices 0#usize 0#usize
      (alloc.vec.Vec.len input) input (alloc.vec.Vec.new Std.U8) := by
    refine {
      level_lt_nine := by norm_num
      current_start := by simp [initialIndices]
      current_end := by
        rw [alloc.vec.Vec.len_val]
        simp [initialIndices, levelPrefix_succ, parentLevelFrom]
      level_values := by
        simp [initialIndices, levelPrefix_succ, parentLevelFrom]
      mask_values := by simp [initialIndices]
    }
  have hoffsets : GeneratedBuildOffsetState initialIndices 0#usize
      (Array.repeat 17#usize 0#usize)
      (Array.repeat 16#usize 0#usize) := by
    refine {
      level_offsets := ?_
      group_offsets := ?_
    }
    · intro index hindex
      change index ≤ 0 at hindex
      have : index = 0 := by omega
      subst index
      simp [initialIndices, levelPrefix]
    · intro index hindex
      change index < 0 at hindex
      omega
  constructor
  · have hfinal := generated_build_trace_final_values hparent initialIndices
      8#usize 0#usize 0#usize (alloc.vec.Vec.len input) input
      (Array.repeat 17#usize 0#usize) (alloc.vec.Vec.new Std.U8)
      (Array.repeat 16#usize 0#usize) finalLevelIndices finalLevelOffsets
      finalGroupMasks finalGroupOffsets trace (by norm_num) (by norm_num)
      hvalues
    simpa [initialIndices] using hfinal
  · exact generated_build_trace_final_offsets hparent initialIndices
      8#usize 0#usize 0#usize (alloc.vec.Vec.len input) input
      (Array.repeat 17#usize 0#usize) (alloc.vec.Vec.new Std.U8)
      (Array.repeat 16#usize 0#usize) finalLevelIndices finalLevelOffsets
      finalGroupMasks finalGroupOffsets trace (by norm_num) (by norm_num)
      hvalues hoffsets

private theorem bind_eq_ok_iff {A B : Type} (input : Result A)
    (next : A → Result B) (output : B) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

structure GeneratedNew17Execution
    (indices : Slice Std.U32)
    (topology : merkle.Radix4BinaryCapTopology) where
  initialLevelIndices : GeneratedIndexVec
  finalLevelIndices : GeneratedIndexVec
  finalLevelOffsets : GeneratedLevelOffsets
  finalGroupMasks : GeneratedMaskVec
  finalGroupOffsets : GeneratedGroupOffsets
  initial_values : initialLevelIndices.val = indices.val
  builder_run :
    merkle.build_topology_levels 8#usize 0#usize 0#usize
      (alloc.vec.Vec.len initialLevelIndices) initialLevelIndices
      (Array.repeat 17#usize 0#usize) (alloc.vec.Vec.new Std.U8)
      (Array.repeat 16#usize 0#usize) =
        .ok (finalLevelIndices, finalLevelOffsets,
          finalGroupMasks, finalGroupOffsets)
  topology_eq : topology = {
    binary_depth := 17#u32
    radix_levels := 8#usize
    level_indices := finalLevelIndices
    level_offsets := finalLevelOffsets
    group_masks := finalGroupMasks
    group_offsets := finalGroupOffsets
  }

theorem new_17_success_yields_execution
    (indices : Slice Std.U32)
    (topology : merkle.Radix4BinaryCapTopology)
    (hrun : merkle.Radix4BinaryCapTopology.new 17#u32 indices =
      .ok (some topology)) :
    Nonempty (GeneratedNew17Execution indices topology) := by
  unfold merkle.Radix4BinaryCapTopology.new at hrun
  simp only [lift, Aeneas.Std.bind_tc_ok] at hrun
  rw [bind_eq_ok_iff] at hrun
  rcases hrun with ⟨empty, hempty, hrun⟩
  by_cases hisEmpty : empty = true
  · rw [if_pos hisEmpty] at hrun
    simp at hrun
  · rw [if_neg hisEmpty] at hrun
    norm_num at hrun
    rw [bind_eq_ok_iff] at hrun
    rcases hrun with ⟨increasing, hincreasing, hrun⟩
    by_cases hisIncreasing : increasing = true
    · rw [if_pos hisIncreasing] at hrun
      rw [bind_eq_ok_iff] at hrun
      rcases hrun with ⟨lastIndex, hlastIndex, hrun⟩
      by_cases hlastTooLarge :
          (Std.U32.wrapping_shl 1#u32 17#u32).val ≤ lastIndex.val
      · rw [if_pos hlastTooLarge] at hrun
        simp at hrun
      · rw [if_neg hlastTooLarge] at hrun
        rw [bind_eq_ok_iff] at hrun
        rcases hrun with ⟨radixDepth, hradixDepth, hrun⟩
        obtain ⟨computedDepth, hcomputedDepth, hcomputedDepthValue⟩ :=
          UScalar.div_spec (ty := .U32) 17#u32 (y := 2#u32) (by norm_num)
        have hcomputedEq : computedDepth = radixDepth :=
          Result.ok.inj (hcomputedDepth.symm.trans hradixDepth)
        subst computedDepth
        have hradixValue : radixDepth.val = 8 := by
          norm_num at hcomputedDepthValue ⊢
          exact hcomputedDepthValue
        have hradixEq : radixDepth = 8#u32 :=
          UScalar.eq_of_val_eq (by simpa using hradixValue)
        subst radixDepth
        have hcastEq : UScalar.cast .Usize (8#u32 : Std.U32) = 8#usize := by
          apply UScalar.eq_of_val_eq
          rw [Std.U32.cast_Usize_val_eq]
          norm_num
        rw [hcastEq] at hrun
        simp only [alloc.vec.Vec.with_capacity] at hrun
        rw [bind_eq_ok_iff] at hrun
        rcases hrun with ⟨initialLevelIndices, hinitialLevelIndices, hrun⟩
        rw [bind_eq_ok_iff] at hrun
        rcases hrun with ⟨buildOutput, hbuild, hrun⟩
        rcases buildOutput with
          ⟨finalLevelIndices, finalLevelOffsets, finalGroupMasks,
            finalGroupOffsets⟩
        have hinitialValues := u32_extend_value (alloc.vec.Vec.new Std.U32)
          indices initialLevelIndices hinitialLevelIndices
        have htopology : topology = {
            binary_depth := 17#u32
            radix_levels := 8#usize
            level_indices := finalLevelIndices
            level_offsets := finalLevelOffsets
            group_masks := finalGroupMasks
            group_offsets := finalGroupOffsets
          } := by
          exact (Option.some.inj (Result.ok.inj hrun)).symm
        exact ⟨{
          initialLevelIndices := initialLevelIndices
          finalLevelIndices := finalLevelIndices
          finalLevelOffsets := finalLevelOffsets
          finalGroupMasks := finalGroupMasks
          finalGroupOffsets := finalGroupOffsets
          initial_values := by simpa using hinitialValues
          builder_run := hbuild
          topology_eq := htopology
        }⟩
    · rw [if_neg hisIncreasing] at hrun
      simp at hrun

theorem new_17_success_has_exact_topology_fields
    (hparent : GeneratedParentLevelSourceEquality)
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (indices : Slice Std.U32)
    (topology : merkle.Radix4BinaryCapTopology)
    (hindices : indices.val.map (fun index => index.val) =
      sharedLevelIndices queries 0)
    (hrun : merkle.Radix4BinaryCapTopology.new 17#u32 indices =
      .ok (some topology)) :
    ExactConstructedTopologyFields queries topology := by
  let execution := Classical.choice
    (new_17_success_yields_execution indices topology hrun)
  have hinitialMapped :
      execution.initialLevelIndices.val.map (fun index => index.val) =
        sharedLevelIndices queries 0 := by
    rw [execution.initial_values, hindices]
  have hsemantics := released_builder_success_semantics hparent
    execution.initialLevelIndices execution.finalLevelIndices
    execution.finalLevelOffsets execution.finalGroupMasks
    execution.finalGroupOffsets execution.builder_run
  have hlevelValues :
      execution.finalLevelIndices.val.map (fun index => index.val) =
        (sharedLevelLists queries).flatten := by
    rw [hsemantics.1.1, hinitialMapped]
    unfold levelPrefix
    rw [source_level_lists_are_shared]
  have hgroupValues :
      execution.finalGroupMasks.val.map (fun mask => mask.val) =
        (sharedGroupMaskLists queries).flatten := by
    rw [hsemantics.1.2, hinitialMapped]
    unfold maskPrefix
    rw [source_group_mask_lists_are_shared]
  rw [execution.topology_eq]
  refine {
    binaryDepth := rfl
    radixLevels := rfl
    levelValues := hlevelValues
    groupMaskValues := hgroupValues
    levelOffset := ?_
    groupOffset := ?_
  }
  · intro level offset hlevel hread
    have hbound : level.val < execution.finalLevelOffsets.length := by
      scalar_tac
    have hvalue := array_index_success_getElem!
      execution.finalLevelOffsets level offset hbound hread
    calc
      offset.val =
          (execution.finalLevelOffsets.val[level.val]!).val :=
        congrArg (fun value : Std.Usize => value.val) hvalue
      _ = (levelPrefix
            (execution.initialLevelIndices.val.map fun index => index.val)
            level.val).length :=
        hsemantics.2.level_offsets level.val (by norm_num at hlevel ⊢; omega)
      _ = (levelPrefix (sharedLevelIndices queries 0) level.val).length := by
        rw [hinitialMapped]
      _ = prefixOffset (sharedLevelLists queries) level.val :=
        levelPrefix_shared_length_eq_prefixOffset queries level.val hlevel
  · intro level offset hlevel hread
    have hbound : level.val < execution.finalGroupOffsets.length := by
      scalar_tac
    have hvalue := array_index_success_getElem!
      execution.finalGroupOffsets level offset hbound hread
    calc
      offset.val =
          (execution.finalGroupOffsets.val[level.val]!).val :=
        congrArg (fun value : Std.Usize => value.val) hvalue
      _ = (maskPrefix
            (execution.initialLevelIndices.val.map fun index => index.val)
            level.val).length :=
        hsemantics.2.group_offsets level.val
          (by norm_num at hlevel ⊢; omega)
      _ = (maskPrefix (sharedLevelIndices queries 0) level.val).length := by
        rw [hinitialMapped]
      _ = prefixOffset (sharedGroupMaskLists queries) level.val :=
        maskPrefix_shared_length_eq_prefixOffset queries level.val hlevel

#print axioms u32_slice_to_vec_value
#print axioms u32_extend_value
#print axioms u8_extend_value
#print axioms generated_build_step_preserves_values
#print axioms generated_build_trace_final_values
#print axioms released_builder_success_values
#print axioms generated_build_trace_final_offsets
#print axioms released_builder_success_semantics
#print axioms new_17_success_yields_execution
#print axioms new_17_success_has_exact_topology_fields

end AspisV5MerkleGeneratedConstructorSemantics
