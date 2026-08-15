import V5MerkleDeployedSource.Funs
import V5MerkleTopologyConstructorModel

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedConstructorBridge

open V5MerkleDeployedSource
open AspisV5MerkleTopologyConstructorModel

abbrev GeneratedIndexVec := alloc.vec.Vec Std.U32
abbrev GeneratedMaskVec := alloc.vec.Vec Std.U8
abbrev GeneratedLevelOffsets := Array Std.Usize 17#usize
abbrev GeneratedGroupOffsets := Array Std.Usize 16#usize

private theorem usize_succ_val_before
    (value bound : Std.Usize) (hvalue : value.val < bound.val) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone]
  apply Nat.mod_eq_of_lt
  have hbound := bound.hSize
  have hbound' : bound.val < UScalar.size .Usize := by
    simpa only [UScalar.size_def] using hbound
  omega

/-- One recursive source step of build_topology_levels. All vector slices,
parent construction, appends, offset writes, and the recursive call are
retained exactly. -/
structure GeneratedBuildStep
    (radixLevels level currentStart currentEnd : Std.Usize)
    (levelIndices : GeneratedIndexVec)
    (levelOffsets : GeneratedLevelOffsets)
    (groupMasks : GeneratedMaskVec)
    (groupOffsets : GeneratedGroupOffsets)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets) where
  groupStart : Std.Usize
  groupOffsets' : GeneratedGroupOffsets
  currentSlice : Slice Std.U32
  currentIndices : GeneratedIndexVec
  nextIndices : GeneratedIndexVec
  nextMasks : GeneratedMaskVec
  groupMasks' : GeneratedMaskVec
  levelIndices' : GeneratedIndexVec
  nextLevel : Std.Usize
  levelOffsets' : GeneratedLevelOffsets
  nextEnd : Std.Usize
  group_start_eq : groupStart = alloc.vec.Vec.len groupMasks
  group_offset_run :
    Array.update groupOffsets level groupStart = .ok groupOffsets'
  current_slice_run :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U32)
        levelIndices { start := currentStart, «end» := currentEnd } =
      .ok currentSlice
  current_indices_run :
    alloc.slice.Slice.to_vec core.clone.CloneU32 currentSlice =
      .ok currentIndices
  parent_run :
    merkle.topology_parent_level (alloc.vec.Vec.deref currentIndices) =
      .ok (nextIndices, nextMasks)
  masks_append_run :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 groupMasks
        (alloc.vec.Vec.deref nextMasks) = .ok groupMasks'
  indices_append_run :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU32 levelIndices
        (alloc.vec.Vec.deref nextIndices) = .ok levelIndices'
  next_level_eq : nextLevel = Std.Usize.wrapping_add level 1#usize
  level_offset_run :
    Array.update levelOffsets nextLevel currentEnd = .ok levelOffsets'
  next_end_eq : nextEnd = alloc.vec.Vec.len levelIndices'
  recurse_run :
    merkle.build_topology_levels radixLevels nextLevel currentEnd nextEnd
      levelIndices' levelOffsets' groupMasks' groupOffsets' =
        .ok (finalLevelIndices, finalLevelOffsets,
          finalGroupMasks, finalGroupOffsets)

/-- Exact finite execution of the generated recursive topology builder. -/
inductive GeneratedBuildTrace
    (radixLevels : Std.Usize) :
    Std.Usize -> Std.Usize -> Std.Usize ->
    GeneratedIndexVec -> GeneratedLevelOffsets ->
    GeneratedMaskVec -> GeneratedGroupOffsets ->
    GeneratedIndexVec -> GeneratedLevelOffsets ->
    GeneratedMaskVec -> GeneratedGroupOffsets -> Prop
  | done
      (level currentStart currentEnd : Std.Usize)
      (levelIndices : GeneratedIndexVec)
      (levelOffsets : GeneratedLevelOffsets)
      (groupMasks : GeneratedMaskVec)
      (groupOffsets : GeneratedGroupOffsets)
      (nextLevel : Std.Usize)
      (levelOffsets' : GeneratedLevelOffsets)
      (groupOffsets' : GeneratedGroupOffsets)
      (hdone : radixLevels.val <= level.val)
      (next_level_eq :
        nextLevel = Std.Usize.wrapping_add radixLevels 1#usize)
      (level_offset_run :
        Array.update levelOffsets nextLevel currentEnd = .ok levelOffsets')
      (group_offset_run :
        Array.update groupOffsets radixLevels (alloc.vec.Vec.len groupMasks) =
          .ok groupOffsets') :
      GeneratedBuildTrace radixLevels level currentStart currentEnd
        levelIndices levelOffsets groupMasks groupOffsets
        levelIndices levelOffsets' groupMasks groupOffsets'
  | step
      (level currentStart currentEnd : Std.Usize)
      (levelIndices : GeneratedIndexVec)
      (levelOffsets : GeneratedLevelOffsets)
      (groupMasks : GeneratedMaskVec)
      (groupOffsets : GeneratedGroupOffsets)
      (finalLevelIndices : GeneratedIndexVec)
      (finalLevelOffsets : GeneratedLevelOffsets)
      (finalGroupMasks : GeneratedMaskVec)
      (finalGroupOffsets : GeneratedGroupOffsets)
      (hactive : level.val < radixLevels.val)
      (head : GeneratedBuildStep radixLevels level currentStart currentEnd
        levelIndices levelOffsets groupMasks groupOffsets
        finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets)
      (tail : GeneratedBuildTrace radixLevels head.nextLevel currentEnd
        head.nextEnd head.levelIndices' head.levelOffsets' head.groupMasks'
        head.groupOffsets' finalLevelIndices finalLevelOffsets
        finalGroupMasks finalGroupOffsets) :
      GeneratedBuildTrace radixLevels level currentStart currentEnd
        levelIndices levelOffsets groupMasks groupOffsets
        finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets

/-- A successful generated builder call yields its complete finite source
trace. This theorem assigns no mathematical meaning to the stored arrays. -/
theorem build_topology_levels_success_yields_trace
    (radixLevels level currentStart currentEnd : Std.Usize)
    (levelIndices : GeneratedIndexVec)
    (levelOffsets : GeneratedLevelOffsets)
    (groupMasks : GeneratedMaskVec)
    (groupOffsets : GeneratedGroupOffsets)
    (finalLevelIndices : GeneratedIndexVec)
    (finalLevelOffsets : GeneratedLevelOffsets)
    (finalGroupMasks : GeneratedMaskVec)
    (finalGroupOffsets : GeneratedGroupOffsets)
    (hrun : merkle.build_topology_levels radixLevels level currentStart
      currentEnd levelIndices levelOffsets groupMasks groupOffsets =
        .ok (finalLevelIndices, finalLevelOffsets,
          finalGroupMasks, finalGroupOffsets)) :
    Nonempty (GeneratedBuildTrace radixLevels level currentStart currentEnd
      levelIndices levelOffsets groupMasks groupOffsets
      finalLevelIndices finalLevelOffsets finalGroupMasks finalGroupOffsets) := by
  rw [merkle.build_topology_levels.eq_def] at hrun
  by_cases hdone : level >= radixLevels
  · rw [if_pos hdone] at hrun
    simp only [lift, Aeneas.Std.bind_tc_ok] at hrun
    let nextLevel := Std.Usize.wrapping_add radixLevels 1#usize
    generalize hlevelOffset :
      Array.update levelOffsets nextLevel currentEnd = levelOffsetResult
      at hrun
    cases levelOffsetResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok levelOffsets' =>
      simp only [Aeneas.Std.bind_tc_ok] at hrun
      generalize hgroupOffset :
        Array.update groupOffsets radixLevels (alloc.vec.Vec.len groupMasks) =
          groupOffsetResult at hrun
      cases groupOffsetResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok groupOffsets' =>
        simp only [Aeneas.Std.bind_tc_ok] at hrun
        simp only [Result.ok.injEq, Prod.mk.injEq] at hrun
        rcases hrun with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨GeneratedBuildTrace.done level currentStart currentEnd
          levelIndices levelOffsets groupMasks groupOffsets nextLevel
          levelOffsets' groupOffsets' (by scalar_tac) rfl hlevelOffset
          hgroupOffset⟩
  · rw [if_neg hdone] at hrun
    simp only [lift, Aeneas.Std.bind_tc_ok] at hrun
    let groupStart := alloc.vec.Vec.len groupMasks
    generalize hgroupOffset :
      Array.update groupOffsets level groupStart = groupOffsetResult at hrun
    cases groupOffsetResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok groupOffsets' =>
      simp only [Aeneas.Std.bind_tc_ok] at hrun
      generalize hcurrentSlice :
        alloc.vec.Vec.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U32)
          levelIndices { start := currentStart, «end» := currentEnd } =
            currentSliceResult at hrun
      cases currentSliceResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok currentSlice =>
        simp only [Aeneas.Std.bind_tc_ok] at hrun
        generalize hcurrentIndices :
          alloc.slice.Slice.to_vec core.clone.CloneU32 currentSlice =
            currentIndicesResult at hrun
        cases currentIndicesResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok currentIndices =>
          simp only [Aeneas.Std.bind_tc_ok] at hrun
          generalize hparent :
            merkle.topology_parent_level
              (alloc.vec.Vec.deref currentIndices) = parentResult at hrun
          cases parentResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok parentPair =>
            rcases parentPair with ⟨nextIndices, nextMasks⟩
            simp only [Aeneas.Std.bind_tc_ok] at hrun
            generalize hmasksAppend :
              alloc.vec.Vec.extend_from_slice core.clone.CloneU8 groupMasks
                (alloc.vec.Vec.deref nextMasks) = masksAppendResult at hrun
            cases masksAppendResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok groupMasks' =>
              simp only [Aeneas.Std.bind_tc_ok] at hrun
              generalize hindicesAppend :
                alloc.vec.Vec.extend_from_slice core.clone.CloneU32 levelIndices
                  (alloc.vec.Vec.deref nextIndices) =
                    indicesAppendResult at hrun
              cases indicesAppendResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok levelIndices' =>
                simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
                let nextLevel := Std.Usize.wrapping_add level 1#usize
                generalize hlevelOffset :
                  Array.update levelOffsets nextLevel currentEnd =
                    levelOffsetResult at hrun
                cases levelOffsetResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | ok levelOffsets' =>
                  simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
                  let nextEnd := alloc.vec.Vec.len levelIndices'
                  have hrecurse :
                      merkle.build_topology_levels radixLevels nextLevel
                        currentEnd nextEnd levelIndices' levelOffsets'
                        groupMasks' groupOffsets' =
                        .ok (finalLevelIndices, finalLevelOffsets,
                          finalGroupMasks, finalGroupOffsets) := by
                    exact hrun
                  let tail := Classical.choice
                    (build_topology_levels_success_yields_trace radixLevels
                      nextLevel currentEnd nextEnd levelIndices' levelOffsets'
                      groupMasks' groupOffsets' finalLevelIndices
                      finalLevelOffsets finalGroupMasks finalGroupOffsets
                      hrecurse)
                  exact ⟨GeneratedBuildTrace.step level currentStart currentEnd
                    levelIndices levelOffsets groupMasks groupOffsets
                    finalLevelIndices finalLevelOffsets finalGroupMasks
                    finalGroupOffsets (by scalar_tac)
                    {
                      groupStart := groupStart
                      groupOffsets' := groupOffsets'
                      currentSlice := currentSlice
                      currentIndices := currentIndices
                      nextIndices := nextIndices
                      nextMasks := nextMasks
                      groupMasks' := groupMasks'
                      levelIndices' := levelIndices'
                      nextLevel := nextLevel
                      levelOffsets' := levelOffsets'
                      nextEnd := nextEnd
                      group_start_eq := rfl
                      group_offset_run := hgroupOffset
                      current_slice_run := hcurrentSlice
                      current_indices_run := hcurrentIndices
                      parent_run := hparent
                      masks_append_run := hmasksAppend
                      indices_append_run := hindicesAppend
                      next_level_eq := rfl
                      level_offset_run := hlevelOffset
                      next_end_eq := rfl
                      recurse_run := hrecurse
                    } tail⟩
termination_by radixLevels.val - level.val
decreasing_by
  have hactive : level.val < radixLevels.val := by scalar_tac
  rw [usize_succ_val_before level radixLevels hactive]
  omega

#print axioms build_topology_levels_success_yields_trace

end AspisV5MerkleGeneratedConstructorBridge
