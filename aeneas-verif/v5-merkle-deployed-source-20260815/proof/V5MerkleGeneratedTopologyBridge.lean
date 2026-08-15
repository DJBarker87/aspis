import V5MerkleDeployedSource.Funs
import AspisFormal.V5TopologyConstruction

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedTopologyBridge

open V5MerkleDeployedSource
open AspisV5TopologyConstruction

/-- Exact structure returned by a successful generated `matched_suffix`
call.  The theorem deliberately states only fields which are needed by the
subsequent hash execution; topology-array contents are handled separately. -/
def ExactMatchedSuffixShape
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix) : Prop :=
  matched = {
    topology := topology
    radix_level := radixLevel
    binary_depth := binaryDepth
    expected_len := Slice.len indices
  }

theorem matched_suffix_success_shape
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (hmatch : merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth indices = .ok (some matched)) :
    ExactMatchedSuffixShape topology radixLevel binaryDepth indices matched := by
  unfold merkle.Radix4BinaryCapTopology.matched_suffix at hmatch
  simp only [lift, Aeneas.Std.bind_tc_ok] at hmatch
  generalize hsub : U32.checked_sub topology.binary_depth
      (Std.U32.wrapping_mul (UScalar.cast .U32 radixLevel) 2#u32) =
    subResult at hmatch
  cases subResult with
  | none =>
    simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
      at hmatch
  | some remainingDepth =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      Aeneas.Std.bind_tc_ok] at hmatch
    generalize hindices :
      merkle.Radix4BinaryCapTopology.impl.level_indices topology radixLevel =
        indicesResult at hmatch
    cases indicesResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hmatch
    | div => simp [Bind.bind, Aeneas.Std.bind] at hmatch
    | ok maybeIndices =>
      simp only [Aeneas.Std.bind_tc_ok] at hmatch
      cases maybeIndices with
      | none =>
        simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
          at hmatch
      | some actualIndices =>
        simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          Aeneas.Std.bind_tc_ok] at hmatch
        by_cases hlevel : radixLevel ≤ topology.radix_levels
        · rw [if_pos hlevel] at hmatch
          by_cases hdepth : remainingDepth = binaryDepth
          · rw [if_pos hdepth] at hmatch
            generalize hequal :
              merkle.u32_slices_equal actualIndices indices 0#usize =
                equalResult at hmatch
            cases equalResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hmatch
            | div => simp [Bind.bind, Aeneas.Std.bind] at hmatch
            | ok equal =>
              simp only [Aeneas.Std.bind_tc_ok] at hmatch
              by_cases hequalTrue : equal = true
              · rw [hequalTrue] at hmatch
                simp at hmatch
                subst matched
                rfl
              · have hequalFalse : equal = false :=
                    Bool.eq_false_of_not_eq_true hequalTrue
                rw [hequalFalse] at hmatch
                simp at hmatch
          · rw [if_neg hdepth] at hmatch
            simp at hmatch
        · rw [if_neg hlevel] at hmatch
          simp at hmatch

/-- Exact values and prefix offsets required of the generated topology
constructor.  This is a data-level statement, independent of hashing. -/
structure ExactConstructedTopologyFields
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (topology : merkle.Radix4BinaryCapTopology) : Prop where
  binaryDepth : topology.binary_depth.val = 17
  radixLevels : topology.radix_levels.val = 8
  levelValues :
    topology.level_indices.val.map (fun index => index.val) =
      (sharedLevelLists queries).flatten
  groupMaskValues :
    topology.group_masks.val.map (fun mask => mask.val) =
      (sharedGroupMaskLists queries).flatten
  levelOffset : ∀ (level offset : Std.Usize), level.val ≤ 9 →
    Array.index_usize topology.level_offsets level = .ok offset →
    offset.val = prefixOffset (sharedLevelLists queries) level.val
  groupOffset : ∀ (level offset : Std.Usize), level.val ≤ 8 →
    Array.index_usize topology.group_offsets level = .ok offset →
    offset.val = prefixOffset (sharedGroupMaskLists queries) level.val

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

/-- A successful generated level-index read returns the exact stored slice. -/
def ExactLevelIndicesOutput
    (topology : merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (indices : Slice Std.U32) : Prop :=
  ∃ start finish : Std.Usize,
    Array.index_usize topology.level_offsets level = .ok start ∧
    Array.index_usize topology.level_offsets
      (Std.Usize.wrapping_add level 1#usize) = .ok finish ∧
    start.val ≤ finish.val ∧
    finish.val ≤ topology.level_indices.val.length ∧
    indices.val = List.slice start.val finish.val topology.level_indices.val

theorem level_indices_success_exact
    (topology : merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (indices : Slice Std.U32)
    (hindices : merkle.Radix4BinaryCapTopology.impl.level_indices
      topology level = .ok (some indices)) :
    level.val ≤ topology.radix_levels.val ∧
      ExactLevelIndicesOutput topology level indices := by
  unfold merkle.Radix4BinaryCapTopology.impl.level_indices at hindices
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

theorem extracted_level_indices_follow_shared_plan
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (topology : merkle.Radix4BinaryCapTopology)
    (level : Std.Usize) (indices : Slice Std.U32)
    (hfields : ExactConstructedTopologyFields queries topology)
    (hlevel : level.val < 9)
    (hindices : merkle.Radix4BinaryCapTopology.impl.level_indices
      topology level = .ok (some indices)) :
    indices.val.map (fun index => index.val) =
      sharedLevelIndices queries level.val := by
  obtain ⟨_, start, finish, hstart, hfinish, _, _, hvalue⟩ :=
    level_indices_success_exact topology level indices hindices
  have hstartVal := hfields.levelOffset level start (by omega) hstart
  let nextLevel := Std.Usize.wrapping_add level 1#usize
  have hnextVal : nextLevel.val = level.val + 1 := by
    exact usize_succ_val_below_ten level (by omega)
  have hfinishVal := hfields.levelOffset nextLevel finish (by omega) hfinish
  have hoffset := sharedLevelPrefixOffset_succ queries level.val hlevel
  rw [hvalue, map_slice, hfields.levelValues, hstartVal, hfinishVal, hnextVal]
  simp only [List.slice, hoffset, Nat.add_sub_cancel_left]
  exact flattened_level_slice_is_exact queries level.val hlevel

/-- The exact mask slice used by one generated level step is the maintained
mask list at that level. -/
theorem extracted_group_mask_slice_follow_shared_plan
    (queries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (topology : merkle.Radix4BinaryCapTopology)
    (level maskStart maskEnd : Std.Usize) (masks : Slice Std.U8)
    (hfields : ExactConstructedTopologyFields queries topology)
    (hlevel : level.val < 8)
    (hstart : Array.index_usize topology.group_offsets level = .ok maskStart)
    (hfinish : Array.index_usize topology.group_offsets
      (Std.Usize.wrapping_add level 1#usize) = .ok maskEnd)
    (hslice : alloc.vec.Vec.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      topology.group_masks { start := maskStart, «end» := maskEnd } =
        .ok masks) :
    masks.val.map (fun mask => mask.val) =
      sharedGroupMasks queries level.val := by
  have hstartVal := hfields.groupOffset level maskStart (by omega) hstart
  have hnextVal : (Std.Usize.wrapping_add level 1#usize).val =
      level.val + 1 := usize_succ_val_below_ten level (by omega)
  have hfinishVal := hfields.groupOffset
    (Std.Usize.wrapping_add level 1#usize) maskEnd (by omega) hfinish
  have hsliceValue : masks.val = List.slice maskStart.val maskEnd.val
      topology.group_masks.val := by
    simp [alloc.vec.Vec.index,
      core.slice.index.SliceIndexRangeUsizeSlice.index] at hslice
    split at hslice
    · have hsliceEq := Result.ok.inj hslice
      exact (congrArg (fun slice : Slice Std.U8 => slice.val) hsliceEq).symm
    · simp at hslice
  have hoffset := sharedGroupMaskPrefixOffset_succ queries level.val hlevel
  rw [hsliceValue, map_slice, hfields.groupMaskValues, hstartVal,
    hfinishVal, hnextVal]
  simp only [List.slice, hoffset, Nat.add_sub_cancel_left]
  exact flattened_group_mask_slice_is_exact queries level.val hlevel

#print axioms matched_suffix_success_shape
#print axioms level_indices_success_exact
#print axioms extracted_level_indices_follow_shared_plan
#print axioms extracted_group_mask_slice_follow_shared_plan

end AspisV5MerkleGeneratedTopologyBridge
