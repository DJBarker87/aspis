import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullConstructorSemantics

/-! Exact reads from the topology produced by the unchanged full extraction. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullTopologyAccessors

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullConstructorSemantics

private theorem usize_succ_val_below_ten (level : Std.Usize)
    (hlevel : level.val ≤ 9) :
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

private theorem map_slice (values : List α) (start finish : Nat)
    (f : α → β) :
    (List.slice start finish values).map f =
      List.slice start finish (values.map f) := by
  simp [List.slice]

/-- Exact offsets and backing-vector slice returned by a successful
`level_indices` call in the unchanged extraction. -/
def ExactLevelIndicesOutput
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (indices : Slice Std.U32) : Prop :=
  ∃ start finish : Std.Usize,
    Array.index_usize topology.level_offsets level = .ok start ∧
    Array.index_usize topology.level_offsets
      (Std.Usize.wrapping_add level 1#usize) = .ok finish ∧
    start.val ≤ finish.val ∧
    finish.val ≤ topology.level_indices.val.length ∧
    indices.val = List.slice start.val finish.val topology.level_indices.val

/-- Exact offsets and backing-vector slice returned by a successful
`group_masks` call in the unchanged extraction. -/
def ExactGroupMasksOutput
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (masks : Slice Std.U8) : Prop :=
  ∃ start finish : Std.Usize,
    Array.index_usize topology.group_offsets level = .ok start ∧
    Array.index_usize topology.group_offsets
      (Std.Usize.wrapping_add level 1#usize) = .ok finish ∧
    start.val ≤ finish.val ∧
    finish.val ≤ topology.group_masks.val.length ∧
    masks.val = List.slice start.val finish.val topology.group_masks.val

/-- Successful `level_indices` is exactly one checked slice between adjacent
stored offsets. -/
theorem level_indices_success_exact
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (indices : Slice Std.U32)
    (hindices : aspis_core.merkle.Radix4BinaryCapTopology.impl.level_indices
      topology level = .ok (some indices)) :
    level.val ≤ topology.radix_levels.val ∧
      ExactLevelIndicesOutput topology level indices := by
  unfold aspis_core.merkle.Radix4BinaryCapTopology.impl.level_indices at hindices
  simp only [lift] at hindices
  split at hindices
  case isTrue htooHigh => simp at hindices
  case isFalse hnotTooHigh =>
    cases hstart : Array.index_usize topology.level_offsets level with
    | fail error => simp [hstart] at hindices
    | div => simp [hstart] at hindices
    | ok start =>
      let nextLevel := Std.Usize.wrapping_add level 1#usize
      cases hfinish : Array.index_usize topology.level_offsets nextLevel with
      | fail error =>
        dsimp [nextLevel] at hfinish
        simp [hstart, hfinish] at hindices
      | div =>
        dsimp [nextLevel] at hfinish
        simp [hstart, hfinish] at hindices
      | ok finish =>
        dsimp [nextLevel] at hfinish
        simp [hstart, hfinish, core.slice.Slice.get,
          core.slice.index.SliceIndexRangeUsizeSlice.get] at hindices
        split at hindices
        · rename_i hbounds
          simp only [Result.ok.injEq, Option.some.injEq] at hindices
          have hvalue := congrArg
            (fun slice : Slice Std.U32 => slice.val) hindices.symm
          have hlevelValue :
              ¬ topology.radix_levels.val < level.val := by
            simpa only [UScalar.lt_equiv] using hnotTooHigh
          exact ⟨Nat.le_of_not_gt hlevelValue, start, finish, hstart,
            hfinish, hbounds.1, hbounds.2, hvalue⟩
        · simp at hindices

/-- Successful `group_masks` is exactly one checked slice between adjacent
stored offsets. -/
theorem group_masks_success_exact
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (masks : Slice Std.U8)
    (hmasks : aspis_core.merkle.Radix4BinaryCapTopology.impl.group_masks
      topology level = .ok (some masks)) :
    level.val < topology.radix_levels.val ∧
      ExactGroupMasksOutput topology level masks := by
  unfold aspis_core.merkle.Radix4BinaryCapTopology.impl.group_masks at hmasks
  simp only [lift] at hmasks
  split at hmasks
  case isTrue htooHigh => simp at hmasks
  case isFalse hnotTooHigh =>
    cases hstart : Array.index_usize topology.group_offsets level with
    | fail error => simp [hstart] at hmasks
    | div => simp [hstart] at hmasks
    | ok start =>
      let nextLevel := Std.Usize.wrapping_add level 1#usize
      cases hfinish : Array.index_usize topology.group_offsets nextLevel with
      | fail error =>
        dsimp [nextLevel] at hfinish
        simp [hstart, hfinish] at hmasks
      | div =>
        dsimp [nextLevel] at hfinish
        simp [hstart, hfinish] at hmasks
      | ok finish =>
        dsimp [nextLevel] at hfinish
        simp [hstart, hfinish, core.slice.Slice.get,
          core.slice.index.SliceIndexRangeUsizeSlice.get] at hmasks
        split at hmasks
        · rename_i hbounds
          simp only [Result.ok.injEq, Option.some.injEq] at hmasks
          have hvalue := congrArg
            (fun slice : Slice Std.U8 => slice.val) hmasks.symm
          have hlevelValue : level.val < topology.radix_levels.val := by
            have hnotLe : ¬ topology.radix_levels.val ≤ level.val := by
              simpa only [UScalar.le_equiv] using hnotTooHigh
            omega
          exact ⟨hlevelValue, start, finish, hstart, hfinish,
            hbounds.1, hbounds.2, hvalue⟩
        · simp at hmasks

/-- A successful full-extraction level read from a constructed topology is
the maintained ordered active-index list at exactly that level. -/
theorem level_indices_follow_shared_plan
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (indices : Slice Std.U32)
    (hfields : FullExactConstructedTopologyFields queries topology)
    (hlevel : level.val < 9)
    (hindices : aspis_core.merkle.Radix4BinaryCapTopology.impl.level_indices
      topology level = .ok (some indices)) :
    indices.val.map (fun index => index.val) =
      sharedLevelIndices queries level.val := by
  obtain ⟨_, start, finish, hstart, hfinish, _, _, hvalue⟩ :=
    level_indices_success_exact topology level indices hindices
  have hstartVal := hfields.levelOffset level start (by omega) hstart
  let nextLevel := Std.Usize.wrapping_add level 1#usize
  have hnextVal : nextLevel.val = level.val + 1 :=
    usize_succ_val_below_ten level (by omega)
  have hfinishVal := hfields.levelOffset nextLevel finish (by omega) hfinish
  have hoffset := sharedLevelPrefixOffset_succ queries level.val hlevel
  rw [hvalue, map_slice]
  change List.slice start.val finish.val
      (indexValues topology.level_indices) = _
  rw [hfields.levelValues, hstartVal, hfinishVal, hnextVal]
  simp only [List.slice, hoffset, Nat.add_sub_cancel_left]
  exact flattened_level_slice_is_exact queries level.val hlevel

/-- A successful full-extraction mask read from a constructed topology is
the maintained ordered group-mask list at exactly that level. -/
theorem group_masks_follow_shared_plan
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (masks : Slice Std.U8)
    (hfields : FullExactConstructedTopologyFields queries topology)
    (hlevel : level.val < 8)
    (hmasks : aspis_core.merkle.Radix4BinaryCapTopology.impl.group_masks
      topology level = .ok (some masks)) :
    masks.val.map (fun mask => mask.val) =
      sharedGroupMasks queries level.val := by
  obtain ⟨_, start, finish, hstart, hfinish, _, _, hvalue⟩ :=
    group_masks_success_exact topology level masks hmasks
  have hstartVal := hfields.groupOffset level start (by omega) hstart
  let nextLevel := Std.Usize.wrapping_add level 1#usize
  have hnextVal : nextLevel.val = level.val + 1 :=
    usize_succ_val_below_ten level (by omega)
  have hfinishVal := hfields.groupOffset nextLevel finish (by omega) hfinish
  have hoffset := sharedGroupMaskPrefixOffset_succ queries level.val hlevel
  rw [hvalue, map_slice]
  change List.slice start.val finish.val
      (maskValues topology.group_masks) = _
  rw [hfields.groupMaskValues, hstartVal, hfinishVal, hnextVal]
  simp only [List.slice, hoffset, Nat.add_sub_cancel_left]
  exact flattened_group_mask_slice_is_exact queries level.val hlevel

#print axioms level_indices_success_exact
#print axioms group_masks_success_exact
#print axioms level_indices_follow_shared_plan
#print axioms group_masks_follow_shared_plan

end AspisV5MerkleUnchangedFullTopologyAccessors
